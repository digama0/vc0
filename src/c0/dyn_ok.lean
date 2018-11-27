import c0.dyn

namespace c0

inductive vtype
| int
| bool
| ref : vtype → vtype
| nil
| cons : vtype → vtype → vtype
| arr : vtype → vtype
| struct : ident → vtype → vtype

def vtype.arr' (τ : vtype) : ℕ → vtype
| 0 := vtype.nil
| (n+1) := vtype.cons τ (vtype.arr' n)

namespace vtype

open ast.exp.type
inductive of_ty (Γ : ast) : ast.exp.type → vtype → Prop
| void : of_ty void nil
| int : of_ty (reg type.int) int
| bool : of_ty (reg type.bool) bool
| ref {τ vτ} : of_ty (reg τ) vτ →
  of_ty (reg $ type.ref τ) (vtype.ref vτ)
| arr {τ vτ} : of_ty (reg τ) vτ →
  of_ty (reg $ type.arr τ) (vtype.ref $ vtype.arr vτ)
| struct {s sd vτ} :
  Γ.get_sdef s sd →
  of_ty (ls (prod.snd <$> sd)) vτ →
  of_ty (reg $ type.struct s) (struct s vτ)
| nil : of_ty (ls []) nil
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
def vars_ty := list vtype

instance : partial_order heap_ty :=
{ le := (<:+),
  le_refl := list.suffix_refl,
  le_trans := @list.is_suffix.trans _,
  le_antisymm := λ l₁ l₂ h₁ h₂, list.sublist_antisymm
    (list.sublist_of_suffix h₁) (list.sublist_of_suffix h₂) }

namespace value

inductive ok (E : heap_ty) : value → vtype → Prop
| int {n} : ok (int n) vtype.int
| bool {b} : ok (bool b) vtype.bool
| null {τ} : ok (ref none) (vtype.ref τ)
| ref {n τ} : τ ∈ list.nth E n → ok (ref (some n)) (vtype.ref τ)
| nil : ok nil vtype.nil
| cons {v₁ v₂ τ₁ τ₂} : ok v₁ τ₁ → ok v₂ τ₂ →
  ok (cons v₁ v₂) (vtype.cons τ₁ τ₂)
| arr {v τ n} : ok v (vtype.arr' τ n) → ok (arr n v) (vtype.arr τ)
| struct {v τ} (s) : ok v τ → ok (struct s v) (vtype.struct s τ)

def ok_opt (E : heap_ty) (v : value) : option vtype → Prop
| none := nil = v
| (some τ) := ok E v τ

end value

def heap.ok (h : heap) (E : heap_ty) : Prop :=
list.forall₂ (value.ok E) h E

structure vars.ok (H : list vtype) (vs : vars) (vτs : vars_ty) : Prop :=
(ok : list.forall₂ (λ (xτ : ident × value) vτ, value.ok H xτ.2 vτ) vs vτs)
(nd : (list.map prod.fst vs).nodup)

open ast ast.stmt ast.exp ast.exp.type c0.type cont_ty

def exp.ok_vtype (Γ : ast) (Δ : ctx) (e : exp) (vτ : vtype) : Prop :=
∃ τ, exp.ok Γ Δ e τ ∧ vtype.of_ty Γ τ vτ

def stmt.ok_vtype (Γ : ast) (Δ : ctx) (ret : vtype) (s : stmt) : Prop :=
∃ τ, vtype.of_ty Γ (rego τ) ret ∧ stmt.ok Γ τ Δ s

def stmt_list.ok (Γ : ast) (Δ : ctx) (ret : vtype) (ss : list stmt) : Prop :=
∀ s ∈ ss, stmt.ok_vtype Γ Δ ret s

def addr.ok (Γ : ast) (E : heap_ty) (H : heap) (η : vars)
  (a : addr) (τ : vtype) : Prop :=
∃ v, addr.get Γ H η a v ∧ value.ok E v τ

def addr_opt.ok (Γ : ast) (E : heap_ty) (H : heap) (η : vars) :
  option addr → vtype → Prop
| none     τ := true
| (some a) τ := addr.ok Γ E H η a τ

def cont_ty.ok (Γ : ast) (E : heap_ty) (H : heap) (η : vars) :
  ∀ α, cont_ty.ty α → vtype → Prop
| V := value.ok E
| A := addr_opt.ok Γ E H η

inductive cont.ok (Γ : ast) (E : heap_ty) (H : heap) (η : vars)
  (Δ : ctx) (ret : vtype) : ∀ {α}, cont α → vtype → Prop
| If {s₁ s₂ K} :
  stmt.ok_vtype Γ Δ ret s₁ →
  stmt.ok_vtype Γ Δ ret s₂ →
  stmt_list.ok Γ Δ ret K →
  cont.ok (cont.If s₁ s₂ K) vtype.bool

| asgn₁ {e τ K} :
  exp.ok_vtype Γ Δ e τ →
  stmt_list.ok Γ Δ ret K →
  cont.ok (cont.asgn₁ e K) τ
| asgn₂ {a τ K} :
  addr_opt.ok Γ E H η a τ →
  stmt_list.ok Γ Δ ret K →
  cont.ok (cont.asgn₂ a K) τ

| asnop {op e τ vτ K} :
  binop.ok_asnop op τ →
  vtype.of_ty Γ (reg τ) vτ →
  exp.ok_vtype Γ Δ e vτ →
  stmt_list.ok Γ Δ ret K →
  cont.ok (cont.asnop op e K) vτ

| eval {τ K} :
  stmt_list.ok Γ Δ ret K →
  cont.ok (cont.eval K) τ

| assert {K} :
  stmt_list.ok Γ Δ ret K →
  cont.ok (cont.assert K) vtype.bool

| ret : cont.ok cont.ret ret

| addr_deref {τ K} :
  cont.ok K τ → cont.ok (cont.addr_deref K) (vtype.ref τ)

| addr_field {s f sτ τ K} :
  vtype.field Γ s f sτ τ →
  vtype.of_ty Γ (reg $ type.struct s) sτ →
  cont.ok K sτ →
  cont.ok (cont.addr_field f K) τ

| addr_index₁ {e₂ τ K} :
  exp.ok Γ Δ e₂ (reg int) →
  cont.ok K τ →
  cont.ok (cont.addr_index₁ e₂ K) (vtype.arr τ)
| addr_index₂ {a τ K} :
  addr_opt.ok Γ E H η a (vtype.arr τ) →
  cont.ok K τ →
  cont.ok (cont.addr_index₂ a K) vtype.int

| binop₁ {op e₂ τ₁ τ₂ vτ₁ vτ₂ K} :
  binop.ok op τ₁ τ₂ →
  vtype.of_ty Γ (reg τ₁) vτ₁ →
  vtype.of_ty Γ (reg τ₂) vτ₂ →
  exp.ok Γ Δ e₂ (reg τ₁) →
  cont.ok K vτ₂ →
  cont.ok (cont.binop₁ op e₂ K) vτ₁
| binop₂ {v op τ₁ τ₂ vτ₁ vτ₂ K} :
  binop.ok op τ₁ τ₂ →
  vtype.of_ty Γ (reg τ₁) vτ₁ →
  vtype.of_ty Γ (reg τ₂) vτ₂ →
  value.ok E v vτ₁ →
  cont.ok K vτ₂ →
  cont.ok (cont.binop₂ v op K) vτ₁

| unop {op τ₁ τ₂ vτ₁ vτ₂ K} :
  unop.ok op τ₁ τ₂ →
  vtype.of_ty Γ (reg τ₁) vτ₁ →
  vtype.of_ty Γ (reg τ₂) vτ₂ →
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
  value.ok E v τ →
  cont.ok K (vtype.cons τ τs) →
  cont.ok (cont.cons₂ v K) τs

| call {f τs τ vτs vτ K} :
  Γ.get_fdef f ⟨τs, τ⟩ →
  vtype.of_ty Γ (rego τ) vτ →
  vtype.of_ty Γ (ls τs) vτs →
  cont.ok K vτs →
  cont.ok (cont.call f K) vτ

| deref {τ K} : cont.ok K τ → cont.ok (cont.deref K) τ

| alloc_arr {τ vτ K} :
  vtype.of_ty Γ (reg $ type.arr τ) vτ →
  cont.ok K vτ →
  cont.ok (cont.alloc_arr τ K) vtype.int

structure env_ty :=
(heap : heap_ty)
(stack : list (ctx × vars_ty))
(vars : vars_ty)
(ctx : ctx)

inductive stack.ok (Γ : ast) (E : heap_ty) (H : heap) :
  list (ctx × vars_ty) → list (vars × cont V) → vtype → Prop
| nil : stack.ok [] [] vtype.int
| cons {Δ η K S σ σs τ τ'} :
  ctx.ok Δ →
  vars.ok E η σ →
  cont.ok Γ E H η Δ τ K τ' →
  stack.ok σs S τ →
  stack.ok ((Δ, σ) :: σs) ((η, K) :: S) τ'

inductive env.ok (Γ : ast) : env_ty → env → vtype → Prop
| mk {E σs σ H η S Δ τ} :
  ctx.ok Δ →
  heap.ok H E →
  vars.ok E η σ →
  stack.ok Γ E H σs S τ →
  env.ok ⟨E, σs, σ, Δ⟩ ⟨H, S, η⟩ τ

inductive state.ok (Γ : ast) : state → Prop
| stmt {T C τ s ss} :
  env.ok Γ T C τ →
  stmt.ok_vtype Γ T.ctx τ s →
  stmt_list.ok Γ T.ctx τ ss →
  state.ok (state.stmt C s ss)
| exp {E σs σ H η S Δ ret τ e α K} :
  env.ok Γ ⟨E, σs, σ, Δ⟩ ⟨H, S, η⟩ ret →
  exp.ok_vtype Γ Δ e τ →
  cont.ok Γ E H η Δ ret K τ →
  state.ok (state.exp α ⟨H, S, η⟩ e K)
| ret {E σs σ H η S Δ ret τ α v K} :
  env.ok Γ ⟨E, σs, σ, Δ⟩ ⟨H, S, η⟩ ret →
  cont_ty.ok Γ E H η α v τ →
  cont.ok Γ E H η Δ ret K τ →
  state.ok (state.ret α ⟨H, S, η⟩ v K)
| err (err) : state.ok (state.err err)
| done (n) : state.ok (state.done n)

def io.ok (Γ : ast) : io → Prop
| none := true
| (some ((f, H, vs), (H', v))) :=
  ∀ ⦃E τs τ vτ vτs⦄,
    Γ.is_extern f →
    Γ.get_fdef f ⟨τs, τ⟩ →
    vtype.of_ty Γ (rego τ) vτ →
    vtype.of_ty Γ (ls τs) vτs →
    heap.ok H E →
    value.ok E vs vτs →
  ∃ E' ≥ E,
    heap.ok H' E' ∧
    value.ok E' v vτ

end c0
