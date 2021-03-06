import c0.ast logic.function.basic util.basic

namespace c0
open ast function

def main := "main"

namespace type

def small : type → Prop
| (struct _) := false
| _ := true

end type

namespace binop

inductive ok : binop → type → type → Prop
| add      : ok add type.int type.int
| sub      : ok sub type.int type.int
| mul      : ok mul type.int type.int
| div      : ok div type.int type.int
| mod      : ok mod type.int type.int
| band     : ok band type.int type.int
| bxor     : ok bxor type.int type.int
| bor      : ok bor type.int type.int
| shl      : ok shl type.int type.int
| shr      : ok shr type.int type.int
| comp {c} : ok (comp c) type.int type.bool
| eq {τ:type} : τ.small → ok (comp comp.eq) τ type.bool
| ne {τ:type} : τ.small → ok (comp comp.ne) τ type.bool

inductive ok_asnop : binop → type → Prop
| mk {op} : ok op type.int type.int → ok_asnop op type.int

end binop

namespace unop

inductive ok : unop → type → type → Prop
| neg  : ok neg type.int type.int
| not  : ok not type.bool type.bool
| bnot : ok bnot type.int type.int

end unop

@[reducible] def sdef := alist (λ _ : ident, c0.type)

@[reducible] def ctx := alist (λ _ : ident, c0.type)

namespace ast

inductive eval_ty : ast → type → c0.type → Prop
| int : eval_ty [] type.int c0.type.int
| bool : eval_ty [] type.bool c0.type.bool
| var {v τ τ' Γ} : eval_ty Γ τ τ' →
  eval_ty (gdecl.typedef v τ :: Γ) (type.var v) τ'
| ref {Γ τ τ'} : eval_ty Γ τ τ' →
  eval_ty Γ (type.ref τ) (c0.type.ref τ')
| arr {Γ τ τ'} : eval_ty Γ τ τ' →
  eval_ty Γ (type.arr τ) (c0.type.arr τ')
| struct {s} : eval_ty [] (type.struct s) (c0.type.struct s)
| weak {d Γ τ τ'} : eval_ty Γ τ τ' → eval_ty (d :: Γ) τ τ'

inductive get_fdef : ast → ident → fdef → Prop
| mk {h f xτs τs' τ τ' body Γ} :
  gdecl.fdecl h f xτs τ body ∈ Γ →
  list.forall₂ (λ (xt : ident × type) τ, eval_ty Γ xt.2 τ) xτs τs' →
  option.forall₂ (eval_ty Γ) τ τ' →
  get_fdef Γ f ⟨τs', τ'⟩

inductive get_body : ast → ident → option c0.type → ctx → stmt → Prop
| mk {h f xτs Δ τ τ' nd body Γ} :
  gdecl.fdecl h f xτs τ (some body) ∈ Γ →
  alist.forall₂ (λ _, eval_ty Γ) (alist.mk' xτs nd) Δ →
  option.forall₂ (eval_ty Γ) τ τ' →
  get_body Γ f τ' Δ body

def is_fdef (Γ : ast) (f : ident) : Prop := ∃ τ xτs s, get_body Γ f τ xτs s

inductive is_extern : ast → ident → Prop
| mk {f xτs τ body Γ} :
  gdecl.fdecl tt f xτs τ body ∈ Γ →
  is_extern Γ f

inductive get_sdef : ast → ident → sdef → Prop
| mk {s xτs nd Δ Γ} :
  gdecl.sdecl s (some xτs) ∈ Γ →
  alist.forall₂ (λ _, eval_ty Γ) (alist.mk' xτs nd) Δ →
  get_sdef Γ s Δ

def sized (Γ : ast) : c0.type → Prop
| (c0.type.struct s) := ∃ sd, get_sdef Γ s sd
| _ := true

namespace exp
open sum c0.type

inductive type
| void
| reg : c0.type → type
| ls : list c0.type → type
open type

def rego : option c0.type → type
| none := void
| (some τ) := reg τ

def type.small : type → Prop
| (reg τ) := τ.small
| void := true
| _ := false

def typeable : exp → Prop
| (cond _ e₁ e₂) := typeable e₁ ∨ typeable e₂
| null := false
| _ := true

inductive ok (Γ : ast) (Δ : ctx) : exp → type → Prop
| int {} {n} : ok (int n) (reg c0.type.int)
| bool {} {b} : ok (bool b) (reg c0.type.bool)
| null {} {τ} : ok null (reg (ref τ))
| var {v τ} : τ ∈ Δ.lookup v → ok (var v) (reg τ)
| binop {op e₁ e₂ τ₁ τ₂} :
  ok e₁ (reg τ₁) → ok e₂ (reg τ₁) →
  binop.ok op τ₁ τ₂ → ok (binop op e₁ e₂) (reg τ₂)
| unop {op e τ₁ τ₂} : ok e (reg τ₁) →
  unop.ok op τ₁ τ₂ → ok (unop op e) (reg τ₂)
| cond {c e₁ e₂ τ} : ok c (reg c0.type.bool) →
  ok e₁ (reg τ) → ok e₂ (reg τ) →
  τ.small → ok (cond c e₁ e₂) (reg τ)
| nil {} : ok nil (ls [])
| cons {e es τ τs} :
  ok e (reg τ) → ok es (ls τs) →
  ok (cons e es) (ls (τ :: τs))
| call {f es τs τ} : get_fdef Γ f ⟨τs, τ⟩ →
  ok es (ls τs) → ok (call f es) (rego τ)
| field {s sd f e τ} :
  ok e (reg (struct s)) →
  get_sdef Γ s sd → τ ∈ sd.lookup f →
  ok (field e f) (reg τ)
| deref {e τ} : ok e (reg (ref τ)) → typeable e → ok (deref e) (reg τ)
| index {e₁ e₂ τ} :
  ok e₁ (reg (arr τ)) → ok e₂ (reg c0.type.int) →
  ok (index e₁ e₂) (reg τ)
| alloc_ref {τ τ'} : eval_ty Γ τ τ' → Γ.sized τ' →
  ok (alloc_ref τ) (reg (ref τ'))
| alloc_arr {τ τ' e} : eval_ty Γ τ τ' → Γ.sized τ' →
  ok e (reg c0.type.int) → ok (alloc_arr τ e) (reg (arr τ'))

def uses (R : ident → Prop) (δ : finset ident) : exp → Prop
| (int _) := true
| (bool _) := true
| null := true
| (var v) := v ∈ δ
| (binop _ e₁ e₂) := uses e₁ ∧ uses e₂
| (unop _ e) := uses e
| (cond c e₁ e₂) := uses c ∧ uses e₁ ∧ uses e₂
| nil := true
| (cons e es) := uses e ∧ uses es
| (call f es) := R f ∧ uses es
| (field e f) := uses e
| (deref e) := uses e
| (index e₁ e₂) := uses e₁ ∧ uses e₂
| (alloc_ref _) := true
| (alloc_arr _ e) := uses e

end exp

namespace lval

def is_var : lval → option ident
| (lval.var v) := some v
| _ := none

def uses (R : ident → Prop) (δ : finset ident) (lv : lval) : Prop :=
cond (is_var lv).is_some true (lv.to_exp.uses R δ)

end lval

namespace stmt
open c0.type exp.type

inductive ok (Γ : ast) (ret_τ : option c0.type) : ctx → stmt → Prop
| decl {Δ v τ τ' s} (h) :
  eval_ty Γ τ τ' → τ'.small →
  ok (alist.cons Δ v τ' h) s → ok Δ (decl v τ s)
| decl_asgn {Δ v e τ τ' s} (h) :
  eval_ty Γ τ τ' → τ'.small →
  exp.ok Γ Δ e (reg τ') →
  ok (alist.cons Δ v τ' h) s → ok Δ (decl_asgn v τ e s)
| If {Δ c s₁ s₂} : exp.ok Γ Δ c (reg bool) →
  ok Δ s₁ → ok Δ s₂ → ok Δ (If c s₁ s₂)
| while {Δ c s} : exp.ok Γ Δ c (reg bool) →
  ok Δ s → ok Δ (while c s)
| asgn {Δ lv e τ} :
  exp.ok Γ Δ (lval.to_exp lv) τ → exp.ok Γ Δ e τ →
  τ.small → ok Δ (asgn lv e)
| asnop {Δ lv op τ e} :
  exp.ok Γ Δ (lval.to_exp lv) (reg τ) → exp.ok Γ Δ e (reg τ) →
  binop.ok_asnop op τ →
  ok Δ (asnop lv op e)
| eval {Δ e τ} : exp.ok Γ Δ e τ → τ.small → ok Δ (eval e)
| assert {Δ e} : exp.ok Γ Δ e (reg bool) → ok Δ (assert e)
| ret {Δ e} :
  option.forall₂ (λ e τ, exp.ok Γ Δ e (reg τ)) e ret_τ →
  ok Δ (ret e)
| nop {} {Δ} : ok Δ nop
| seq {Δ s₁ s₂} : ok Δ s₁ → ok Δ s₂ → ok Δ (seq s₁ s₂)

inductive init (R : ident → Prop) :
  finset ident → finset ident → stmt → finset ident → Prop
| decl {v τ s γ δ δ'} :
  init (insert v γ) δ s δ' →
  init γ δ (decl v τ s) (δ'.erase v)
| decl_asgn {v e τ s γ δ δ'} :
  exp.uses R δ e →
  init (insert v γ) (insert v δ) s δ' →
  init γ δ (decl_asgn v τ e s) (δ'.erase v)
| If {c s₁ s₂ γ δ δ₁ δ₂} :
  exp.uses R δ c → init γ δ s₁ δ₁ → init γ δ s₂ δ₂ →
  init γ δ (If c s₁ s₂) (δ₁ ∩ δ₂)
| while {c s γ δ δ'} :
  exp.uses R δ c → init γ δ s δ' →
  init γ δ (while c s) δ
| asgn {lv e γ δ} :
  lval.uses R δ lv → exp.uses R δ e →
  init γ δ (asgn lv e) (option.cases_on lv.is_var δ (λ v, insert v δ))
| asnop {lv op e γ δ} :
  (lval.to_exp lv).uses R δ → exp.uses R δ e →
  init γ δ (asnop lv op e) δ
| eval {e γ δ} : exp.uses R δ e → init γ δ (eval e) δ
| assert {e γ δ} : exp.uses R δ e → init γ δ (assert e) δ
| ret {e γ δ} : (∀ e' ∈ e, exp.uses R δ e') → init γ δ (ret e) γ
| nop {} {γ δ} : init γ δ nop δ
| seq {s₁ s₂ γ δ₁ δ₂ δ₃} :
  init γ δ₁ s₁ δ₂ → init γ δ₂ s₂ δ₃ → init γ δ₁ (seq s₁ s₂) δ₃

inductive returns : stmt → Prop
| decl {v τ s} : returns s → returns (decl v τ s)
| decl_asgn {v e τ s} : returns s → returns (decl_asgn v τ e s)
| If {c s₁ s₂} : returns s₁ → returns s₂ → returns (If c s₁ s₂)
| ret {e} : returns (ret e)
| seq_left {s₁ s₂} : returns s₁ → returns (seq s₁ s₂)
| seq_right {s₁ s₂} : returns s₂ → returns (seq s₁ s₂)

def ok_init (R : ident → Prop) (Δ : ctx) (s : stmt) : Prop :=
let γ := Δ.keys.to_finset in ∃ δ', init R γ γ s δ'

end stmt
namespace gdecl

inductive ok (Γ : ast) : gdecl → Prop
| fdecl (header f xτs Δ ret ret' body h) :
  alist.forall₂ (λ i τ τ', eval_ty Γ τ τ' ∧ τ'.small) (alist.mk' xτs h) Δ →
  option.forall₂ (λ τ τ', eval_ty Γ τ τ' ∧ τ'.small) ret ret' →
  (∀ s ∈ body,
    header = ff ∧
    ¬ is_fdef Γ f ∧
    stmt.ok (fdecl header f xτs ret body :: Γ) ret' Δ s ∧
    (s.returns ∨ ret = none)) →
  ok (fdecl header f xτs ret body)
| typedef (x τ τ') :
  (∀ τ, typedef x τ ∉ Γ) →
  eval_ty Γ τ τ' → ok (typedef x τ)
| sdecl (s) : ok (sdecl s none)
| sdefn (s xτs) :
  (∀ sd, ¬ get_sdef Γ s sd) →
  (list.map prod.fst xτs).nodup →
  (∀ (xτ : ident × type), xτ ∈ xτs → ∃ τ, eval_ty Γ xτ.2 τ ∧ Γ.sized τ) →
  ok (sdecl s (some xτs))

end gdecl

inductive ok' : ast → ast → Prop
| nil {Γ} : ok' Γ []
| cons {Γ d ds} : gdecl.ok Γ d → ok' (d :: Γ) ds → ok' Γ (d :: ds)

def ok_func (Γ : ast) (f : ident) := Γ.is_extern f ∨ Γ.is_fdef f

structure ok (Γ : ast) : Prop :=
(gdecls : ok' [] Γ.reverse)
(fdef_uniq : ∀ ⦃i fd fd'⦄, Γ.get_fdef i fd → Γ.get_fdef i fd' → fd = fd')
(header_no_def : ∀ ⦃i⦄, Γ.is_extern i → ¬ Γ.is_fdef i)
(fdef_tdef : ∀ ⦃i fd⦄, Γ.get_fdef i fd → ∀ τ, gdecl.typedef i τ ∉ Γ)
(ok_init : ∀ ⦃f τ Δ s⦄, Γ.get_body f τ Δ s → s.ok_init (ok_func Γ) Δ)
(main : Γ.get_fdef main ⟨[], c0.type.int⟩ ∧ Γ.is_fdef main)

-- The ASTs described here are laid out in reverse order, i.e.
-- `Γ = [z, y, x]` if the declarations are x,y,z in source order.
-- This makes them easier to work with as contexts.
-- The `ds` represents a list in source order, so that `decls_ok`
-- says that an input AST is typecorrect.
def decls_ok (ds : ast) : Prop := ok ds.reverse

end ast

end c0
