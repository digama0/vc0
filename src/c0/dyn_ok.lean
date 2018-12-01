import c0.dyn

namespace c0

inductive vtype
| int
| bool
| ref : vtype → vtype
| nil
| cons : vtype → vtype → vtype
| arr : vtype → vtype
| struct : ident → vtype

def vtype.arr' (τ : vtype) : ℕ → vtype
| 0 := vtype.nil
| (n+1) := vtype.cons τ (vtype.arr' n)

namespace vtype

open ast.exp.type sum
inductive of_ty : ast.exp.type → vtype → Prop
| void {} : of_ty void nil
| int {} : of_ty (reg type.int) int
| bool {} : of_ty (reg type.bool) bool
| ref {τ vτ} : of_ty (reg τ) vτ →
  of_ty (reg $ type.ref τ) (vtype.ref vτ)
| arr {τ vτ} : of_ty (reg τ) vτ →
  of_ty (reg $ type.arr τ) (vtype.ref $ vtype.arr vτ)
| struct {s} : of_ty (reg $ type.struct s) (struct s)
| nil {} : of_ty (ls []) nil
| cons {τ τs vτ vτs} :
  of_ty (reg τ) vτ → of_ty (ls τs) vτs →
  of_ty (ls (τ :: τs)) (cons vτ vτs)

inductive lookup (i : ident) (τ : vtype) : list ident → vtype → Prop
| one {xs τs} : lookup (i :: xs) (vtype.cons τ τs)
| cons {x τ xs τs} : lookup xs τs →
  lookup (x :: xs) (vtype.cons τ τs)

end vtype

def heap_ty := list vtype
@[reducible] def vars_ty := finmap ident (λ _, vtype)

def vars_ty.ok (Δ : ctx) (σ : vars_ty) : Prop :=
∀ i τ, τ ∈ σ.lookup i → ∃ t ∈ Δ.lookup i, vtype.of_ty (ast.exp.type.reg t) τ

instance heap_ty.empty : has_emptyc heap_ty := ⟨[]⟩

instance : partial_order heap_ty :=
{ le := (<:+),
  le_refl := list.suffix_refl,
  le_trans := @list.is_suffix.trans _,
  le_antisymm := λ l₁ l₂ h₁ h₂, list.sublist_antisymm
    (list.sublist_of_suffix h₁) (list.sublist_of_suffix h₂) }

namespace value

inductive ok (Γ : ast) (E : heap_ty) : value → vtype → Prop
| int {} {n} : ok (int n) vtype.int
| bool {} {b} : ok (bool b) vtype.bool
| null {} {τ} : ok (ref none) (vtype.ref τ)
| ref {} {n τ} : τ ∈ list.nth E n → ok (ref (some n)) (vtype.ref τ)
| nil {} : ok nil vtype.nil
| cons {v₁ v₂ τ₁ τ₂} : ok v₁ τ₁ → ok v₂ τ₂ →
  ok (cons v₁ v₂) (vtype.cons τ₁ τ₂)
| arr {v τ n} : ok v (vtype.arr' τ n) → ok (arr n v) (vtype.arr τ)
| struct {v s} : (∀ sd x τ vτ v',
    Γ.get_sdef s sd →
    τ ∈ sd.lookup x →
    vtype.of_ty (ast.exp.type.reg τ) vτ →
    is_field x v v' → ok v' vτ) →
  ok v (vtype.struct s)

def ok_opt (Γ : ast) (E : heap_ty) (v : value) : option vtype → Prop
| none := nil = v
| (some τ) := ok Γ E v τ

end value

def heap.ok (Γ : ast) (h : heap) (E : heap_ty) : Prop :=
list.forall₂ (value.ok Γ E) h E

def vars.ok (Γ : ast) (E : heap_ty) (η : vars) (σ : vars_ty) : Prop :=
∀ i τ, τ ∈ σ.lookup i → ∃ v ∈ η.lookup i, value.ok Γ E v τ

open ast ast.stmt ast.exp ast.exp.type c0.type cont_ty

def exp.ok_vtype (Γ : ast) (Δ : ctx) (e : exp) (vτ : vtype) : Prop :=
∃ τ, exp.ok Γ Δ e τ ∧ vtype.of_ty τ vτ

def stmt.ok_vtype (Γ : ast) (ret : vtype) (Δ : ctx) (s : stmt) : Prop :=
∃ τ, vtype.of_ty (rego τ) ret ∧ stmt.ok Γ τ Δ s

inductive stmt_list.ok (Γ : ast) (ret : option type) : ctx → finset ident → list stmt → Prop
| nil {} {Δ δ} : ret = none → stmt_list.ok Δ δ []
| one {} {Δ δ δ' s K} :
  stmt.ok Γ ret Δ s →
  s.returns →
  s.init Δ.keys.to_finset δ δ' →
  stmt_list.ok Δ δ (s::K)
| cons {} {Δ δ δ' s K} :
  stmt.ok Γ ret Δ s →
  s.init Δ.keys.to_finset δ δ' →
  stmt_list.ok Δ δ' K →
  stmt_list.ok Δ δ (s::K)
| weak {} {Δ δ x τ h K} :
  stmt_list.ok Δ (finset.erase δ x) K → stmt_list.ok (Δ.cons x τ h) δ K

def stmt_list.ok_vtype (Γ : ast) (ret : vtype)
  (Δ : ctx) (δ : finset ident) (K : list stmt) : Prop :=
∃ τ, vtype.of_ty (rego τ) ret ∧ stmt_list.ok Γ τ Δ δ K

namespace addr
inductive ok (Γ : ast) (E : heap_ty) (σ : vars_ty) : addr → vtype → Prop
| ref {} {n τ} : τ ∈ E.nth n → ok (ref n) τ
| var {} {i τ} : τ ∈ σ.lookup i → ok (var i) τ
| head {a τ τs} : ok a (vtype.cons τ τs) → ok (head a) τ
| tail {a τ τs} : ok a (vtype.cons τ τs) → ok (tail a) τs
| nth {a i v} : ok a (vtype.arr v) → ok (nth a i) v
| field {a s f τ sd vτ} :
  Γ.get_sdef s sd → τ ∈ sd.lookup f →
  vtype.of_ty (ast.exp.type.reg τ) vτ →
  ok a (vtype.struct s) → ok (field a f) vτ
end addr

def addr_opt.ok (Γ : ast) (E : heap_ty) (σ : vars_ty) :
  option addr → vtype → Prop
| none     τ := true
| (some a) τ := addr.ok Γ E σ a τ

def cont_ty.ok (Γ : ast) (E : heap_ty) (σ : vars_ty) :
  ∀ α, cont_ty.ty α → vtype → Prop
| V := value.ok Γ E
| A := addr_opt.ok Γ E σ

inductive cont.ok (Γ : ast) (E : heap_ty) (σ : vars_ty)
  (Δ : ctx) (ret : vtype) : finset ident → ∀ {α}, cont α → vtype → Prop
| If {} {s₁ s₂ δ δ₁ δ₂ K τ} :
  vtype.of_ty (rego τ) ret →
  stmt.ok Γ τ Δ s₁ → s₁.init Δ.keys.to_finset δ δ₁ →
  stmt.ok Γ τ Δ s₂ → s₂.init Δ.keys.to_finset δ δ₂ →
  s₁.returns ∧ s₂.returns ∨ stmt_list.ok Γ τ Δ (δ₁ ∩ δ₂) K →
  cont.ok δ (cont.If s₁ s₂ K) vtype.bool

| asgn₁ {δ e τ K} :
  exp.ok_vtype Γ Δ e τ →
  exp.use e ⊆ δ →
  stmt_list.ok_vtype Γ ret Δ δ K →
  cont.ok δ (cont.asgn₁ e K) τ
| asgn₂ {δ a τ t K} :
  addr_opt.ok Γ E σ a τ →
  vtype.of_ty (rego t) ret →
  stmt_list.ok Γ t Δ δ K →
  cont.ok δ (cont.asgn₂ a K) τ

| asgn_var {} {δ x τ vτ K} :
  τ ∈ Δ.lookup x →
  vtype.of_ty (reg τ) vτ →
  stmt_list.ok_vtype Γ ret Δ (insert x δ) K →
  cont.ok δ (cont.asgn_var x K) vτ

| asnop {δ op e τ vτ K} :
  binop.ok_asnop op τ →
  vtype.of_ty (reg τ) vτ →
  exp.ok Γ Δ e (reg τ) →
  exp.use e ⊆ σ.keys →
  stmt_list.ok_vtype Γ ret Δ δ K →
  cont.ok δ (cont.asnop op e K) vτ

| eval {δ τ K} :
  stmt_list.ok_vtype Γ ret Δ δ K →
  cont.ok δ (cont.eval K) τ

| assert {δ K} :
  stmt_list.ok_vtype Γ ret Δ δ K →
  cont.ok δ (cont.assert K) vtype.bool

| ret {} {δ} : cont.ok δ cont.ret ret

| addr_deref {δ τ K} :
  cont.ok δ K τ → cont.ok δ (cont.addr_deref K) (vtype.ref τ)

| addr_field {δ s f sd t τ K} :
  Γ.get_sdef s sd → t ∈ sd.lookup f →
  vtype.of_ty (reg t) τ →
  cont.ok δ K (vtype.struct s) →
  cont.ok δ (cont.addr_field f K) τ

| addr_index₁ {δ e₂ τ K} :
  exp.ok Γ Δ e₂ (reg int) →
  exp.use e₂ ⊆ δ →
  cont.ok δ K τ →
  cont.ok δ (cont.addr_index₁ e₂ K) (vtype.arr τ)
| addr_index₂ {δ a τ K} :
  addr_opt.ok Γ E σ a (vtype.arr τ) →
  cont.ok δ K τ →
  cont.ok δ (cont.addr_index₂ a K) vtype.int

| binop₁ {δ op e₂ τ₁ τ₂ vτ₁ vτ₂ K} :
  binop.ok op τ₁ τ₂ →
  vtype.of_ty (reg τ₁) vτ₁ →
  vtype.of_ty (reg τ₂) vτ₂ →
  exp.ok Γ Δ e₂ (reg τ₁) →
  exp.use e₂ ⊆ σ.keys →
  cont.ok δ K vτ₂ →
  cont.ok δ (cont.binop₁ op e₂ K) vτ₁
| binop₂ {δ v op τ₁ τ₂ vτ₁ vτ₂ K} :
  binop.ok op τ₁ τ₂ →
  vtype.of_ty (reg τ₁) vτ₁ →
  vtype.of_ty (reg τ₂) vτ₂ →
  value.ok Γ E v vτ₁ →
  cont.ok δ K vτ₂ →
  cont.ok δ (cont.binop₂ v op K) vτ₁

| unop {δ op τ₁ τ₂ vτ₁ vτ₂ K} :
  unop.ok op τ₁ τ₂ →
  vtype.of_ty (reg τ₁) vτ₁ →
  vtype.of_ty (reg τ₂) vτ₂ →
  cont.ok δ K vτ₂ →
  cont.ok δ (cont.unop op K) vτ₁

| cond {δ e₁ e₂ τ K} :
  exp.ok_vtype Γ Δ e₁ τ → exp.use e₁ ⊆ σ.keys →
  exp.ok_vtype Γ Δ e₂ τ → exp.use e₂ ⊆ σ.keys →
  cont.ok δ K τ →
  cont.ok δ (cont.cond e₁ e₂ K) vtype.bool

| cons₁ {δ es τ τs K} :
  exp.ok_vtype Γ Δ es τs →
  exp.use es ⊆ σ.keys →
  cont.ok δ K (vtype.cons τ τs) →
  cont.ok δ (cont.cons₁ es K) τ
| cons₂ {δ v τ τs K} :
  value.ok Γ E v τ →
  cont.ok δ K (vtype.cons τ τs) →
  cont.ok δ (cont.cons₂ v K) τs

| call {δ f τs τ vτs vτ K} :
  Γ.get_fdef f ⟨τs, τ⟩ →
  vtype.of_ty (rego τ) vτ →
  vtype.of_ty (ls τs) vτs →
  cont.ok δ K vτs →
  cont.ok δ (cont.call f K) vτ

| deref {δ τ K} : cont.ok δ K τ → cont.ok δ (cont.deref K) τ

| alloc_arr {δ τ vτ K} :
  vtype.of_ty (reg $ type.arr τ) vτ →
  cont.ok δ K vτ →
  cont.ok δ (cont.alloc_arr τ K) vtype.int

def cont.ok' (Γ : ast) (E : heap_ty) (σ : vars_ty)
  (Δ : ctx) (ret : vtype) {α} : cont α → vtype → Prop :=
cont.ok Γ E σ Δ ret σ.keys

structure env_ty :=
(heap : heap_ty)
(stack : list (ctx × vars_ty))
(vars : vars_ty)
(ctx : ctx)

instance env_ty.empty : has_emptyc env_ty := ⟨⟨∅, [], ∅, ∅⟩⟩

inductive stack.ok (Γ : ast) (E : heap_ty) :
  list (ctx × vars_ty) → list (vars × cont V) → vtype → Prop
| nil {} : stack.ok [] [] vtype.int
| cons {Δ η K S σ σs τ τ'} :
  vars_ty.ok Δ σ →
  vars.ok Γ E η σ →
  cont.ok' Γ E σ Δ τ K τ' →
  stack.ok σs S τ →
  stack.ok ((Δ, σ) :: σs) ((η, K) :: S) τ'

inductive env.ok (Γ : ast) : env_ty → env → vtype → Prop
| mk {E σs σ H η S Δ τ} :
  vars_ty.ok Δ σ →
  heap.ok Γ H E →
  vars.ok Γ E η σ →
  stack.ok Γ E σs S τ →
  env.ok ⟨E, σs, σ, Δ⟩ ⟨H, S, η⟩ τ

-- This is an extra weird state that we have to patch in.
-- It doesn't quite fit the pattern of a regular exp state
-- because `K'` is typechecked in conjunction with the active
-- expression element, in this case a variable.
inductive state.addr_var_ok (Γ : ast) : env → ident → exp → list stmt → Prop
| addr_var₂ {E σs σ Δ ret_τ t τ ret H S η x e K} :
  env.ok Γ ⟨E, σs, σ, Δ⟩ ⟨H, S, η⟩ ret →
  vtype.of_ty (rego ret_τ) ret →
  t ∈ Δ.lookup x →
  exp.ok Γ Δ e (reg t) →
  vtype.of_ty (reg t) τ →
  exp.use e ⊆ σ.keys →
  stmt_list.ok Γ ret_τ Δ (insert x σ.keys) K →
  state.addr_var_ok ⟨H, S, η⟩ x e K

inductive state.ok (Γ : ast) : state → Prop
| stmt {E σs σ Δ C vτ δ s K} (τ) :
  env.ok Γ ⟨E, σs, σ, Δ⟩ C vτ →
  vtype.of_ty (rego τ) vτ →
  stmt.ok Γ τ Δ s →
  stmt.init Δ.keys.to_finset σ.keys s δ →
  s.returns ∨ stmt_list.ok Γ τ Δ δ K →
  state.ok (state.stmt C s K)
| exp {E σs σ H η S Δ ret τ e α K} :
  env.ok Γ ⟨E, σs, σ, Δ⟩ ⟨H, S, η⟩ ret →
  exp.use e ⊆ σ.keys →
  exp.ok_vtype Γ Δ e τ →
  cont.ok' Γ E σ Δ ret K τ →
  state.ok (state.exp α ⟨H, S, η⟩ e K)
| ret {E σs σ H η S Δ ret τ α v K} :
  env.ok Γ ⟨E, σs, σ, Δ⟩ ⟨H, S, η⟩ ret →
  cont_ty.ok Γ E σ α v τ →
  cont.ok' Γ E σ Δ ret K τ →
  state.ok (state.ret α ⟨H, S, η⟩ v K)
| err (err) : state.ok (state.err err)
| done (n) : state.ok (state.done n)

def io.ok (Γ : ast) : io → Prop
| none := true
| (some ((f, H, vs), (H', v))) :=
  ∀ ⦃E τs τ vτ vτs⦄,
    Γ.is_extern f →
    Γ.get_fdef f ⟨τs, τ⟩ →
    vtype.of_ty (rego τ) vτ →
    vtype.of_ty (ls τs) vτs →
    heap.ok Γ H E →
    value.ok Γ E vs vτs →
  ∃ E' ≥ E,
    heap.ok Γ H' E' ∧
    value.ok Γ E' v vτ

end c0
