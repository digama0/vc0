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

inductive field (Γ : ast) (s : ident) (f : ident) : vtype → vtype → Prop
| mk {sd sτ τ} : Γ.get_sdef s sd →
  lookup f τ (prod.fst <$> sd) sτ → field sτ τ

end vtype

def heap_ty := list vtype

structure vars_ty :=
(σ : list (ident × vtype))
(nd : (list.map prod.fst σ).nodup)

instance heap_ty.empty : has_emptyc heap_ty := ⟨[]⟩
instance vars_ty.empty : has_emptyc vars_ty := ⟨⟨[], list.nodup_nil⟩⟩

def vars_ty.cons (σ : vars_ty) (x : ident) (τ : vtype)
  (h : x ∉ list.map prod.fst σ.1) : vars_ty :=
⟨(x, τ) :: σ.1, list.nodup_cons.2 ⟨h, σ.2⟩⟩

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
    (x, τ) ∈ sd →
    vtype.of_ty (ast.exp.type.reg τ) vτ →
    is_field x v v' → ok v' vτ) →
  ok v (vtype.struct s)

def ok_opt (Γ : ast) (E : heap_ty) (v : value) : option vtype → Prop
| none := nil = v
| (some τ) := ok Γ E v τ

end value

def heap.ok (Γ : ast) (h : heap) (E : heap_ty) : Prop :=
list.forall₂ (value.ok Γ E) h E

def vars.ok (Γ : ast) (H : list vtype) (vs : vars) (σ : vars_ty) : Prop :=
list.forall₂ (prod.forall₂ eq (value.ok Γ H)) vs σ.1

open ast ast.stmt ast.exp ast.exp.type c0.type cont_ty

def exp.ok_vtype (Γ : ast) (Δ : ctx) (e : exp) (vτ : vtype) : Prop :=
∃ τ, exp.ok Γ Δ e τ ∧ vtype.of_ty τ vτ

def stmt.ok_vtype (Γ : ast) (ret : vtype) (Δ : ctx) (s : stmt) : Prop :=
∃ τ, vtype.of_ty (rego τ) ret ∧ stmt.ok Γ τ Δ s

inductive stmt_list.ok (Γ : ast) (ret : option type) : ctx → list stmt → Prop
| nil {} {Δ} : ret = none → stmt_list.ok Δ []
| one {} {Δ s K} : stmt.ok Γ ret Δ s → s.returns → stmt_list.ok Δ (s::K)
| cons {} {Δ s K} :
  stmt.ok Γ ret Δ s → stmt_list.ok Δ K → stmt_list.ok Δ (s::K)
| weak {} {Δ xτ K} : stmt_list.ok Δ K → stmt_list.ok (xτ::Δ) K

def stmt_list.ok_vtype (Γ : ast) (ret : vtype) (Δ : ctx) (K : list stmt) : Prop :=
∃ τ, vtype.of_ty (rego τ) ret ∧ stmt_list.ok Γ τ Δ K

namespace addr
inductive ok (Γ : ast) (E : heap_ty) (σ : vars_ty) : addr → vtype → Prop
| ref {} {n τ} : τ ∈ E.nth n → ok (ref n) τ
| var {} {i τ} : (i, τ) ∈ σ.1 → ok (var i) τ
| head {a τ τs} : ok a (vtype.cons τ τs) → ok (head a) τ
| tail {a τ τs} : ok a (vtype.cons τ τs) → ok (tail a) τs
| nth {a i v} : ok a (vtype.arr v) → ok (nth a i) v
| field {a s f τ sd vτ} :
  Γ.get_sdef s sd → (f, τ) ∈ sd →
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
  (Δ : ctx) (ret : vtype) : ∀ {α}, cont α → vtype → Prop
| If {} {s₁ s₂ K τ} :
  vtype.of_ty (rego τ) ret →
  stmt.ok Γ τ Δ s₁ →
  stmt.ok Γ τ Δ s₂ →
  s₁.returns ∧ s₂.returns ∨ stmt_list.ok Γ τ Δ K →
  cont.ok (cont.If s₁ s₂ K) vtype.bool

| asgn₁ {e τ K} :
  exp.ok_vtype Γ Δ e τ →
  stmt_list.ok_vtype Γ ret Δ K →
  cont.ok (cont.asgn₁ e K) τ
| asgn₂ {a τ K} :
  addr_opt.ok Γ E σ a τ →
  stmt_list.ok_vtype Γ ret Δ K →
  cont.ok (cont.asgn₂ a K) τ

| asnop {op e τ vτ K} :
  binop.ok_asnop op τ →
  vtype.of_ty (reg τ) vτ →
  exp.ok Γ Δ e (reg τ) →
  stmt_list.ok_vtype Γ ret Δ K →
  cont.ok (cont.asnop op e K) vτ

| eval {τ K} :
  stmt_list.ok_vtype Γ ret Δ K →
  cont.ok (cont.eval K) τ

| assert {K} :
  stmt_list.ok_vtype Γ ret Δ K →
  cont.ok (cont.assert K) vtype.bool

| ret {} : cont.ok cont.ret ret

| addr_deref {τ K} :
  cont.ok K τ → cont.ok (cont.addr_deref K) (vtype.ref τ)

| addr_field {s f sτ τ K} :
  vtype.field Γ s f sτ τ →
  vtype.of_ty (reg $ type.struct s) sτ →
  cont.ok K sτ →
  cont.ok (cont.addr_field f K) τ

| addr_index₁ {e₂ τ K} :
  exp.ok Γ Δ e₂ (reg int) →
  cont.ok K τ →
  cont.ok (cont.addr_index₁ e₂ K) (vtype.arr τ)
| addr_index₂ {a τ K} :
  addr_opt.ok Γ E σ a (vtype.arr τ) →
  cont.ok K τ →
  cont.ok (cont.addr_index₂ a K) vtype.int

| binop₁ {op e₂ τ₁ τ₂ vτ₁ vτ₂ K} :
  binop.ok op τ₁ τ₂ →
  vtype.of_ty (reg τ₁) vτ₁ →
  vtype.of_ty (reg τ₂) vτ₂ →
  exp.ok Γ Δ e₂ (reg τ₁) →
  cont.ok K vτ₂ →
  cont.ok (cont.binop₁ op e₂ K) vτ₁
| binop₂ {v op τ₁ τ₂ vτ₁ vτ₂ K} :
  binop.ok op τ₁ τ₂ →
  vtype.of_ty (reg τ₁) vτ₁ →
  vtype.of_ty (reg τ₂) vτ₂ →
  value.ok Γ E v vτ₁ →
  cont.ok K vτ₂ →
  cont.ok (cont.binop₂ v op K) vτ₁

| unop {op τ₁ τ₂ vτ₁ vτ₂ K} :
  unop.ok op τ₁ τ₂ →
  vtype.of_ty (reg τ₁) vτ₁ →
  vtype.of_ty (reg τ₂) vτ₂ →
  cont.ok K vτ₂ →
  cont.ok (cont.unop op K) vτ₁

| cond {e₁ e₂ τ K} :
  exp.ok_vtype Γ Δ e₁ τ →
  exp.ok_vtype Γ Δ e₂ τ →
  cont.ok K τ →
  cont.ok (cont.cond e₁ e₂ K) vtype.bool

| cons₁ {es τ τs K} :
  exp.ok_vtype Γ Δ es τs →
  cont.ok K (vtype.cons τ τs) →
  cont.ok (cont.cons₁ es K) τ
| cons₂ {v τ τs K} :
  value.ok Γ E v τ →
  cont.ok K (vtype.cons τ τs) →
  cont.ok (cont.cons₂ v K) τs

| call {f τs τ vτs vτ K} :
  Γ.get_fdef f ⟨τs, τ⟩ →
  vtype.of_ty (rego τ) vτ →
  vtype.of_ty (ls τs) vτs →
  cont.ok K vτs →
  cont.ok (cont.call f K) vτ

| deref {τ K} : cont.ok K τ → cont.ok (cont.deref K) τ

| alloc_arr {τ vτ K} :
  vtype.of_ty (reg $ type.arr τ) vτ →
  cont.ok K vτ →
  cont.ok (cont.alloc_arr τ K) vtype.int

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
  ctx.ok Δ →
  vars.ok Γ E η σ →
  cont.ok Γ E σ Δ τ K τ' →
  stack.ok σs S τ →
  stack.ok ((Δ, σ) :: σs) ((η, K) :: S) τ'

inductive env.ok (Γ : ast) : env_ty → env → vtype → Prop
| mk {E σs σ H η S Δ τ} :
  ctx.ok Δ →
  heap.ok Γ H E →
  vars.ok Γ E η σ →
  stack.ok Γ E σs S τ →
  env.ok ⟨E, σs, σ, Δ⟩ ⟨H, S, η⟩ τ

inductive state.ok (Γ : ast) : state → Prop
| stmt {T C vτ s ss} (τ) :
  env.ok Γ T C vτ →
  vtype.of_ty (rego τ) vτ →
  stmt.ok Γ τ T.ctx s →
  s.returns ∨ stmt_list.ok Γ τ T.ctx ss →
  state.ok (state.stmt C s ss)
| exp {E σs σ H η S Δ ret τ e α K} :
  env.ok Γ ⟨E, σs, σ, Δ⟩ ⟨H, S, η⟩ ret →
  exp.ok_vtype Γ Δ e τ →
  cont.ok Γ E σ Δ ret K τ →
  state.ok (state.exp α ⟨H, S, η⟩ e K)
| ret {E σs σ H η S Δ ret τ α v K} :
  env.ok Γ ⟨E, σs, σ, Δ⟩ ⟨H, S, η⟩ ret →
  cont_ty.ok Γ E σ α v τ →
  cont.ok Γ E σ Δ ret K τ →
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
