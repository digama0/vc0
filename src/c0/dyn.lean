-- Dynamic semantics
import c0.ast_ok

namespace c0

@[derive decidable_eq]
inductive value
| int : int32 → value
| bool : bool → value
| nil : value
| cons : value → value → value
| ref : option ℕ → value
| arr : ℕ → value → value
| named : ident → value → value

inductive addr
| ref : nat → addr
| var : ident → addr
| head : addr → addr
| tail : addr → addr
| nth : addr → ℕ → addr
| field : addr → ident → addr

namespace addr

def nth' (a : addr) : ℕ → addr
| 0 := a.head
| (n+1) := (nth' n).tail

end addr

namespace value

inductive at_head (R : value → value → Prop) : value → value → Prop
| mk {v v' vs} : R v v' → at_head (cons v vs) (cons v' vs)

inductive at_tail (R : value → value → Prop) : value → value → Prop
| mk {v vs vs'} : R vs vs' → at_tail (cons v vs) (cons v vs')

def at_nth' (R : value → value → Prop) : ℕ → value → value → Prop
| 0 := at_head R
| (n+1) := at_tail (at_nth' n)

inductive at_nth (R : value → value → Prop) (i : ℕ) : value → value → Prop
| mk {v v' n} : i < n → at_nth' R i v v' → at_nth (arr n v) (arr n v')

inductive is_field (f : ident) : value → value → Prop
| one {v vs} : is_field (cons (named f v) vs) v
| cons {v' v vs} : is_field vs v → is_field (cons v' vs) v

inductive is_nth : ℕ → value → value → Prop
| zero {v vs} : is_nth 0 (cons v vs) v
| succ {n v vs v'} : is_nth n vs v' → is_nth (n+1) (cons v vs) v'

open sum
def to_err : option int32 → value ⊕ err
| none := inr err.arith
| (some n) := inl (int n)

inductive step_comp : comp → value → value → _root_.bool → Prop
| lt {n₁ n₂} : step_comp comp.lt (int n₁) (int n₂) (n₁ < n₂)
| le {n₁ n₂} : step_comp comp.le (int n₁) (int n₂) (n₁ ≤ n₂)
| gt {n₁ n₂} : step_comp comp.gt (int n₁) (int n₂) (n₂ < n₁)
| ge {n₁ n₂} : step_comp comp.ge (int n₁) (int n₂) (n₂ ≤ n₁)
| eq {v₁ v₂} : step_comp comp.eq v₁ v₂ (v₁ = v₂)
| ne {v₁ v₂} : step_comp comp.ne v₁ v₂ (v₁ ≠ v₂)

inductive step_binop : binop → value → value → value ⊕ err → Prop
| add {n₁ n₂} : step_binop binop.add (int n₁) (int n₂) (inl $ int (n₁ + n₂))
| sub {n₁ n₂} : step_binop binop.sub (int n₁) (int n₂) (inl $ int (n₁ - n₂))
| mul {n₁ n₂} : step_binop binop.mul (int n₁) (int n₂) (inl $ int (n₁ * n₂))
| div {n₁ n₂} : step_binop binop.mul (int n₁) (int n₂) (to_err $ n₁.div n₂)
| mod {n₁ n₂} : step_binop binop.mul (int n₁) (int n₂) (to_err $ n₁.mod n₂)
| band {n₁ n₂} : step_binop binop.band (int n₁) (int n₂) (inl $ int $ n₁.bitwise_and n₂)
| bxor {n₁ n₂} : step_binop binop.bxor (int n₁) (int n₂) (inl $ int $ n₁.bitwise_xor n₂)
| bor {n₁ n₂} : step_binop binop.bor (int n₁) (int n₂) (inl $ int $ n₁.bitwise_or n₂)
| shl {n₁ n₂} : step_binop binop.mul (int n₁) (int n₂) (to_err $ n₁.shl n₂)
| shr {n₁ n₂} : step_binop binop.mul (int n₁) (int n₂) (to_err $ n₁.shr n₂)
| comp {c v₁ v₂ b} :
  step_comp c v₁ v₂ b → step_binop (binop.comp c) v₁ v₂ (inl $ bool b)

inductive step_unop : unop → value → value → Prop
| neg {n} : step_unop unop.neg (int n) (int (-n))
| not {b} : step_unop unop.neg (bool b) (bool (bnot b))
| bnot {n} : step_unop unop.neg (int n) (int n.bitwise_not)

inductive default (Γ : ast) : type ⊕ sdef → value → Prop
| int : default (inl type.int) (int 0)
| bool : default (inl type.bool) (bool ff)
| ref {τ} : default (inl $ type.ref τ) (ref none)
| arr {τ} : default (inl $ type.arr τ) (ref none)
| struct {s sd v} : Γ.get_sdef s sd → default (inr sd) v →
  default (inl $ type.struct s) v
| nil : default (inr ∅) nil
| cons {Δ x τ h v vs} :
  default (inl τ) v → default (inr Δ) vs →
  default (inr (Δ.cons x τ h)) (cons (named x v) vs)

def repeat (v : value) : ℕ → value
| 0 := nil
| (n+1) := cons v (repeat n)

end value

@[reducible] def heap := list value

@[reducible] def vars := finmap ident (λ _, value)

instance heap.empty : has_emptyc heap := ⟨[]⟩

namespace addr

inductive get (h : heap) (η : vars) : addr → value → Prop
| ref {} {n v} : v ∈ h.nth n → get (ref n) v
| var {} {i v} : v ∈ η.lookup i → get (var i) v
| head {a v vs} : get a (value.cons v vs) → get (head a) v
| tail {a v vs} : get a (value.cons v vs) → get (tail a) vs
| nth {a i n v v'} : get a (value.arr n v) →
  i < n → value.is_nth i v v' → get (nth a i) v'
| field {a f v' v} :
  get a v' → value.is_field f v' v → get (field a f) v

inductive get_len (h : heap) (η : vars) : addr → ℕ → Prop
| mk {a n v} : get h η a (value.arr n v) → get_len a n

inductive update (h : heap) (η : vars) :
  (value → value → Prop) → addr → heap → vars → Prop
| ref {R n h'} : list.update_at R n h h' → update R (ref n) h' η
| var {R : value → value → Prop} {i x y} :
  x ∈ η.lookup i → R x y → update R (var i) h (η.replace i y)
| head {R a h' η'} :
  update (value.at_head R) a h' η' → update R (head a) h' η'
| tail {R a h' η'} :
  update (value.at_tail R) a h' η' → update R (tail a) h' η'
| nth {R a i h' η'} :
  update (value.at_nth R i) a h' η' → update R (nth a i) h' η'

end addr

def vars.assign (η : vars) (x : ident) (v : value) : vars :=
if x ∈ η then η.replace x v else η.insert x v

open ast

inductive cont_ty | V | A
open cont_ty
def cont_ty.ty : cont_ty → Type
| V := value
| A := option addr

inductive cont : cont_ty → Type
| If : stmt → stmt → list stmt → cont V        -- If _ s₁ s₂ : K
| asgn₁ : exp → list stmt → cont A             -- asgn _ e : K
| asgn₂ : option addr → list stmt → cont V     -- asgn a _ : K
| asgn_var : ident → list stmt → cont V        -- asgn x _ : K
| asnop : binop → exp → list stmt → cont A     -- asnop _ op e : K
| eval : list stmt → cont V                    -- eval _ : K
| assert : list stmt → cont V                  -- assert _ : K
| ret : cont V                                 -- ret _
| addr_deref : cont A → cont V                 -- &(*_) : K
| addr_field : ident → cont A → cont A         -- &(_.f) : K
| addr_index₁ : exp → cont A → cont A          -- &(_[e₂]) : K
| addr_index₂ : option addr → cont A → cont V  -- &(a[_]) : K
| binop₁ : binop → exp → cont V → cont V       -- _ op e₂ : K
| binop₂ : value → binop → cont V → cont V     -- v op _ : K
| unop : unop → cont V → cont V                -- op _ : K
| cond : exp → exp → cont V → cont V           -- _ ? e₁ : e₂ : K
| cons₁ : exp → cont V → cont V                -- (_, es) : K
| cons₂ : value → cont V → cont V              -- (v, _) : K
| call : ident → cont V → cont V               -- f(_) : K
| deref : cont V → cont A                      -- * _ : K
| alloc_arr : type → cont V → cont V           -- alloc_arr(τ, _) : K

structure env :=
(heap : heap)
(stack : list (vars × cont V))
(vars : vars)
attribute [pp_using_anonymous_constructor] env

instance env.empty : has_emptyc env := ⟨⟨∅, [], ∅⟩⟩

inductive state
| stmt : env → stmt → list stmt → state
| exp : ∀ α, env → exp → cont α → state
| ret : ∀ α, env → cont_ty.ty α → cont α → state
| err : err → state
| done : int32 → state

open ast.stmt ast.exp.type c0.type

inductive start (Γ : ast) : state → Prop
| mk {s} : Γ.get_body main (some int) ∅ s →
  start (state.stmt ∅ s [])

inductive state.final : state → Prop
| err {e} : state.final (state.err e)
| done {n} : state.final (state.done n)

inductive step_ret : env → value → state → Prop
| ret {H S η K η' v} :
  step_ret ⟨H, (η, K) :: S, η'⟩ v (state.ret V ⟨H, S, η⟩ v K)
| done {H η n} : step_ret ⟨H, [], η⟩ (value.int n) (state.done n)

inductive step_call : value → vars → Prop
| nil : step_call value.nil ∅
| cons {x v vs η} :
  step_call vs η → step_call (value.cons v vs) (η.insert x v)

inductive step_deref : env → option addr → cont V → state → Prop
| null {C K} : step_deref C none K (state.err err.mem)
| deref {C:env} {a v K} :
  addr.get C.heap C.vars a v →
  step_deref C (some a) K (state.ret V C v K)

inductive step_alloc : env → value → cont V → state → Prop
| mk {H S η v K} :
  step_alloc ⟨H, S, η⟩ v K
    (state.ret V ⟨H ++ [v], S, η⟩ (value.ref H.length) K)

def io := option ((ident × heap × value) × (heap × value))

inductive step (Γ : ast) : state → io → state → Prop
| decl {H S η v τ τ' s K} :
  ast.eval_ty Γ τ τ' →
  step (state.stmt ⟨H, S, η⟩ (decl v τ s) K) none
       (state.stmt ⟨H, S, η⟩ s K)

| decl_asgn {H S η v τ τ' e s K} :
  ast.eval_ty Γ τ τ' →
  step (state.stmt ⟨H, S, η⟩ (decl_asgn v τ e s) K) none
       (state.stmt ⟨H, S, η⟩ (asgn (lval.var v) e) (s :: K))

| If₁ {C c s₁ s₂ K} :
  step (state.stmt C (If c s₁ s₂) K) none
       (state.exp V C c $ cont.If s₁ s₂ K)
| If₂ {C b s₁ s₂ K} :
  step (state.ret V C (value.bool b) $ cont.If s₁ s₂ K) none
       (state.stmt C (cond b s₁ s₂) K)

| while {C c s K} :
  step (state.stmt C (while c s) K) none
       (state.exp V C c $ cont.If (seq s (while c s)) nop K)

| asgn₁ {C lv e K} :
  lval.is_var lv = none →
  step (state.stmt C (asgn lv e) K) none
       (state.exp A C lv.to_exp $ cont.asgn₁ e K)
| asgn₂ {C a e K} :
  step (state.ret A C a $ cont.asgn₁ e K) none
       (state.exp V C e $ cont.asgn₂ a K)
| asgn₃ {H H' S η η' a v K} :
  addr.update H η (λ _, eq v) a H' η' →
  step (state.ret V ⟨H, S, η⟩ v $ cont.asgn₂ (some a) K) none
       (state.stmt ⟨H', S, η'⟩ nop K)
| asgn_err {H S η v K} :
  step (state.ret V ⟨H, S, η⟩ v $ cont.asgn₂ none K) none
       (state.err err.mem)

| asgn_var₁ {C lv x e K} :
  x ∈ lval.is_var lv →
  step (state.stmt C (asgn lv e) K) none
       (state.exp V C e $ cont.asgn_var x K)
| asgn_var₂ {H S η x v K} :
  step (state.ret V ⟨H, S, η⟩ v $ cont.asgn_var x K) none
       (state.stmt ⟨H, S, η.assign x v⟩ nop K)

| asnop₁ {C lv op e K} :
  step (state.stmt C (asnop lv op e) K) none
       (state.exp A C lv.to_exp $ cont.asnop op e K)
| asnop₂ {C a op e K T} :
  step_deref C a (cont.binop₁ op e $ cont.asgn₂ a K) T →
  step (state.ret A C a $ cont.asnop op e K) none T

| eval₁ {C e K} :
  step (state.stmt C (eval e) K) none
       (state.exp V C e $ cont.eval K)
| eval₂ {C v K} :
  step (state.ret V C v $ cont.eval K) none
       (state.stmt C nop K)

| assert₁ {C e K} :
  step (state.stmt C (assert e) K) none
       (state.exp V C e $ cont.assert K)
| assert₂ {C b K} :
  step (state.ret V C (value.bool b) $ cont.assert K) none
       (cond b (state.stmt C nop K) (state.err err.abort))

| ret₁ {C e K} :
  step (state.stmt C (ret (some e)) K) none
       (state.exp V C e cont.ret)
| ret₂ {C T v} :
  step_ret C v T → step (state.ret V C v cont.ret) none T
| ret_none {C T K} :
  step_ret C value.nil T → step (state.stmt C (ret none) K) none T

| nop₁ {C T} : step_ret C value.nil T → step (state.stmt C nop []) none T
| nop₂ {C s K} : step (state.stmt C nop (s::K)) none (state.stmt C s K)

| seq {C s₁ s₂ K} :
  step (state.stmt C (seq s₁ s₂) K) none (state.stmt C s₁ (s₂::K))

| int {C n K} :
  step (state.exp V C (exp.int n) K) none
       (state.ret V C (value.int n) K)

| bool {C b K} :
  step (state.exp V C (exp.bool b) K) none
       (state.ret V C (value.bool b) K)

| null {C K} :
  step (state.exp V C exp.null K) none
       (state.ret V C (value.ref none) K)

| var {C:env} {i v K} : v ∈ C.vars.lookup i →
  step (state.exp V C (exp.var i) K) none
       (state.ret V C v K)

| binop₁ {C op e₁ e₂ K} :
  step (state.exp V C (exp.binop op e₁ e₂) K) none
       (state.exp V C e₁ $ cont.binop₁ op e₂ K)
| binop₂ {C op v₁ e₂ K} :
  step (state.ret V C v₁ $ cont.binop₁ op e₂ K) none
       (state.exp V C e₂ $ cont.binop₂ v₁ op K)
| binop₃ {C op v₁ v₂ v K} :
  value.step_binop op v₁ v₂ (sum.inl v) →
  step (state.ret V C v₂ $ cont.binop₂ v₁ op K) none
       (state.ret V C v K)
| binop_err {C op v₁ v₂ err K} :
  value.step_binop op v₁ v₂ (sum.inr err) →
  step (state.ret V C v₂ $ cont.binop₂ v₁ op K) none
       (state.err err)

| unop₁ {C op e K} :
  step (state.exp V C (exp.unop op e) K) none
       (state.exp V C e $ cont.unop op K)
| unop₂ {C op v v' K} :
  value.step_unop op v v' →
  step (state.ret V C v $ cont.unop op K) none
       (state.ret V C v' K)

| cond₁ {C c e₁ e₂ K} :
  step (state.exp V C (exp.cond c e₁ e₂) K) none
       (state.exp V C c $ cont.cond e₁ e₂ K)
| cond₂ {C b e₁ e₂ K} :
  step (state.ret V C (value.bool b) $ cont.cond e₁ e₂ K) none
       (state.exp V C (if b then e₁ else e₂) K)

| nil {C K} :
  step (state.exp V C exp.nil K) none
       (state.ret V C value.nil K)

| cons₁ {C e es K} :
  step (state.exp V C (exp.cons e es) K) none
       (state.exp V C e $ cont.cons₁ es K)
| cons₂ {C v es K} :
  step (state.ret V C v $ cont.cons₁ es K) none
       (state.exp V C es $ cont.cons₂ v K)
| cons₃ {C v₁ v₂ K} :
  step (state.ret V C v₂ $ cont.cons₂ v₁ K) none
       (state.ret V C (value.cons v₁ v₂) K)

| call₁ {C f es K} :
  step (state.exp V C (exp.call f es) K) none
       (state.exp V C es $ cont.call f K)
| call₂ {H S η η' f τ xτs s vs K} :
  Γ.get_body f τ xτs s →
  step_call vs η' →
  step (state.ret V ⟨H, S, η⟩ vs $ cont.call f K) none
       (state.stmt ⟨H, (η, K) :: S, η'⟩ s [])
| call_extern {H S η f vs H' v K} :
  Γ.is_extern f →
  step (state.ret V ⟨H, S, η⟩ vs $ cont.call f K)
       (some ((f, H, vs), (H', v)))
       (state.ret V ⟨H', S, η⟩ v K)

| deref {C e K} :
  step (state.exp V C (exp.deref e) K) none
       (state.exp V C e $ cont.addr_deref $ cont.deref K)

| index {C e n K} :
  step (state.exp V C (exp.index e n) K) none
       (state.exp A C e $ cont.addr_index₁ n $ cont.deref K)

| field {C:env} {e f K} :
  step (state.exp V C (exp.field e f) K) none
       (state.exp A C e $ cont.addr_field f $ cont.deref K)

| alloc_ref {C τ τ' v K T} :
  Γ.eval_ty τ τ' →
  value.default Γ (sum.inl τ') v →
  step_alloc C v K T →
  step (state.exp V C (exp.alloc_ref τ) K) none T

| alloc_arr₁ {C τ τ' e K} :
  Γ.eval_ty τ τ' →
  step (state.exp V C (exp.alloc_arr τ e) K) none
       (state.exp V C e $ cont.alloc_arr τ' K)
| alloc_arr₂ {C τ v K T} {i : int32} {n : ℕ} :
  (i : ℤ) = n →
  value.default Γ (sum.inl τ) v →
  step_alloc C (value.repeat v n) K T →
  step (state.ret V C (value.int i) $ cont.alloc_arr τ K) none T
| alloc_arr_err {C τ i K} : i < 0 →
  step (state.ret V C (value.int i) $ cont.alloc_arr τ K) none
       (state.err err.mem)

| addr_var {C v K} :
  step (state.exp A C (exp.var v) K) none
       (state.ret A C (some (addr.var v)) K)

| addr_deref₁ {C e K} :
  step (state.exp A C (exp.deref e) K) none
       (state.exp V C e $ cont.addr_deref K)
| addr_deref₂ {C v K} :
  step (state.ret V C (value.ref v) $ cont.addr_deref K) none
       (state.ret A C (addr.ref <$> v) K)

| addr_index₁ {C e n K} :
  step (state.exp A C (exp.index e n) K) none
       (state.exp A C e $ cont.addr_index₁ n K)
| addr_index₂ {C a n K} :
  step (state.ret A C a $ cont.addr_index₁ n K) none
       (state.exp V C n $ cont.addr_index₂ a K)
| addr_index₃ {C:env} {a n K} {i:int32} {j:ℕ} :
  addr.get_len C.heap C.vars a n → (i:ℤ) = j → j < n →
  step (state.ret V C (value.int i) $ cont.addr_index₂ (some a) K) none
       (state.ret A C (some (a.nth j)) K)
| addr_index_err₁ {C i K} :
  step (state.ret V C (value.int i) $ cont.addr_index₂ none K) none
       (state.err err.mem)
| addr_index_err₂ {C:env} {a n i K} :
  addr.get_len C.heap C.vars a n → (i < 0 ∨ (n:ℤ) ≤ (i:ℤ)) →
  step (state.ret V C (value.int i) $ cont.addr_index₂ (some a) K) none
       (state.err err.mem)

| addr_field₁ {C:env} {e f K} :
  step (state.exp A C (exp.field e f) K) none
       (state.exp A C e $ cont.addr_field f K)
| addr_field₂ {C a f K} :
  step (state.ret A C (some a) $ cont.addr_field f K) none
       (state.ret A C (some (a.field f)) K)
| addr_field_err {C f K} :
  step (state.ret A C none $ cont.addr_field f K) none
       (state.err err.mem)

end c0
