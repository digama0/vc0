import c0.ast logic.function util.basic

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
| bit_and  : ok bit_and type.int type.int
| bit_xor  : ok bit_xor type.int type.int
| bit_or   : ok bit_or type.int type.int
| shl      : ok shl type.int type.int
| shr      : ok shr type.int type.int
| comp {c} : ok (comp c) type.int type.bool
| eq {τ:type} : τ.small → ok (comp comp.eq) τ type.bool
| ne {τ:type} : τ.small → ok (comp comp.ne) τ type.bool

end binop

namespace unop

inductive ok : unop → type → type → Prop
| neg      : ok neg type.int type.int
| not      : ok not type.bool type.bool
| bit_not  : ok bit_not type.int type.int

end unop

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

inductive get_body : ast → ident → stmt → Prop
| mk {h f xτs τ body Γ} :
  gdecl.fdecl h f xτs τ (some body) ∈ Γ →
  get_body Γ f body

inductive is_header : ast → ident → bool → Prop
| mk {h f xτs τ body Γ} :
  gdecl.fdecl h f xτs τ body ∈ Γ →
  is_header Γ f h

inductive get_typedef : ast → ident → type → Prop
| mk {v τ Γ} : gdecl.typedef v τ ∈ Γ → get_typedef Γ v τ

inductive get_sdef : ast → ident → sdef → Prop
| mk {s xτs xτs' Γ} :
  gdecl.sdecl s (some xτs) ∈ Γ →
  list.forall₂ (prod.forall₂ eq (eval_ty Γ)) xτs xτs' →
  get_sdef Γ s xτs'

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

inductive ok (R : ident → Prop) (Γ : ast)
  (Δ : list (ident × c0.type)) : exp → type → Prop
| int {n} : ok (int n) (reg c0.type.int)
| bool {b} : ok (bool b) (reg c0.type.bool)
| null {τ} : ok null (reg (ref τ))
| var {v τ} : (v, τ) ∈ Δ → ok (var v) (reg τ)
| binop {op e₁ e₂ τ₁ τ₂} :
  ok e₁ (reg τ₁) → ok e₂ (reg τ₁) →
  binop.ok op τ₁ τ₂ → ok (binop op e₁ e₂) (reg τ₂)
| unop {op e τ₁ τ₂} : ok e (reg τ₁) →
  unop.ok op τ₁ τ₂ → ok (unop op e) (reg τ₂)
| cond {c e₁ e₂ τ} : ok c (reg c0.type.bool) →
  ok e₁ (reg τ) → ok e₂ (reg τ) →
  τ.small → ok (cond c e₁ e₂) (reg τ)
| nil : ok nil (ls [])
| cons {e es τ τs} :
  ok e (reg τ) → ok es (ls τs) →
  ok (cons e es) (ls (τ :: τs))
| call {f es τs τ} : R f → get_fdef Γ f ⟨τs, τ⟩ →
  ok es (ls τs) → ok (call f es) (rego τ)
| field {s sd f e τ} :
  ok e (reg (struct s)) →
  get_sdef Γ s sd → (f, τ) ∈ sd →
  ok (field e f) (reg τ)
| deref {e τ} : ok e (reg (ref τ)) → typeable e → ok (deref e) (reg τ)
| index {e₁ e₂ τ} :
  ok e₁ (reg (arr τ)) → ok e₂ (reg c0.type.int) →
  ok (index e₁ e₂) (reg τ)
| alloc_ref {τ τ'} : eval_ty Γ τ τ' → Γ.sized τ' →
  ok (alloc_ref τ) (reg (ref τ'))
| alloc_arr {τ τ' e} : eval_ty Γ τ τ' → Γ.sized τ' →
  ok e (reg c0.type.int) → ok (alloc_arr τ e) (reg (arr τ'))

def use : exp → finset ident
| (int _) := ∅
| (bool _) := ∅
| null := ∅
| (var v) := finset.singleton v
| (binop _ e₁ e₂) := use e₁ ∪ use e₂
| (unop _ e) := use e
| (cond c e₁ e₂) := use c ∪ use e₁ ∪ use e₂
| nil := ∅
| (cons e es) := use e ∪ use es
| (call f es) := use es
| (field e f) := use e
| (deref e) := use e
| (index e₁ e₂) := use e₁ ∪ use e₂
| (alloc_ref _) := ∅
| (alloc_arr _ e) := use e

end exp

namespace stmt
open c0.type exp.type

inductive ok (R : ident → Prop) (Γ : ast) (ret_τ : option c0.type) : list (ident × c0.type) → stmt → Prop
| decl {Δ v τ τ' s} :
  (∀ τ, (v, τ) ∉ Δ) → eval_ty Γ τ τ' → τ'.small →
  ok ((v, τ') :: Δ) s → ok Δ (decl v τ s)
| decl_asgn {Δ v e τ τ' s} :
  (∀ τ, (v, τ) ∉ Δ) → eval_ty Γ τ τ' → τ'.small →
  exp.ok R Γ Δ e (reg τ') →
  ok ((v, τ') :: Δ) s → ok Δ (decl_asgn v τ e s)
| If {Δ c s₁ s₂} : exp.ok R Γ Δ c (reg bool) →
  ok Δ s₁ → ok Δ s₂ → ok Δ (If c s₁ s₂)
| while {Δ c s} : exp.ok R Γ Δ c (reg bool) →
  ok Δ s → ok Δ (while c s)
| asgn {Δ lv e τ} :
  exp.ok R Γ Δ (lval.to_exp lv) τ → exp.ok R Γ Δ e τ →
  τ.small → ok Δ (asgn lv e)
| asnop {Δ lv op e} :
  exp.ok R Γ Δ (lval.to_exp lv) (reg int) → exp.ok R Γ Δ e (reg int) →
  binop.ok op int int →
  ok Δ (asnop lv op e)
| eval {Δ e τ} : exp.ok R Γ Δ e τ → τ.small → ok Δ (eval e)
| assert {Δ e} : exp.ok R Γ Δ e (reg bool) → ok Δ (assert e)
| ret {Δ e} :
  option.forall₂ (λ e τ, exp.ok R Γ Δ e (reg τ)) e ret_τ →
  ok Δ (ret e)
| nop {Δ} : ok Δ nop
| seq {Δ s₁ s₂} : ok Δ s₁ → ok Δ s₂ → ok Δ (seq s₁ s₂)

def insert_lv : lval → finset ident → finset ident
| (lval.var v) δ := insert v δ
| _ δ := δ

inductive init : finset ident → finset ident → stmt → finset ident → Prop
| decl {v τ s γ δ δ'} :
  init (insert v γ) δ s δ' →
  init γ δ (decl v τ s) (δ'.erase v)
| decl_asgn {v e τ s γ δ δ'} :
  exp.use e ⊆ δ →
  init (insert v γ) (insert v δ) s δ' →
  init γ δ (decl_asgn v τ e s) (δ'.erase v)
| If {c s₁ s₂ γ δ δ₁ δ₂} :
  exp.use c ⊆ δ → init γ δ s₁ δ₁ → init γ δ s₂ δ₂ →
  init γ δ (If c s₁ s₂) (δ₁ ∩ δ₂)
| while {c s γ δ δ'} :
  exp.use c ⊆ δ → init γ δ s δ' →
  init γ δ (while c s) δ
| asgn {lv e γ δ} :
  (lval.to_exp lv).use ⊆ δ → exp.use e ⊆ δ →
  init γ δ (asgn lv e) (insert_lv lv δ)
| asnop {lv op e γ δ} :
  (lval.to_exp lv).use ⊆ δ → exp.use e ⊆ δ →
  init γ δ (asnop lv op e) δ
| eval {e γ δ} : exp.use e ⊆ δ → init γ δ (eval e) δ
| assert {e γ δ} : exp.use e ⊆ δ → init γ δ (assert e) δ
| ret {e γ δ} : (∀ e' ∈ e, exp.use e' ⊆ δ) → init γ δ (ret e) γ
| nop {γ δ} : init γ δ nop δ
| seq {s₁ s₂ γ δ₁ δ₂ δ₃} :
  init γ δ₁ s₁ δ₂ → init γ δ₂ s₂ δ₃ → init γ δ₁ (seq s₁ s₂) δ₃

def ok_init (Δ : list (ident × c0.type)) (s : stmt) : Prop :=
let γ := (Δ.map prod.fst).to_finset in ∃ δ', init γ γ s δ'

end stmt
namespace gdecl

inductive ok (R : ident → Prop) (Γ : ast) : gdecl → Prop
| fdecl (header f xτs xτs' ret ret' body) :
  eval_ty Γ ret ret' →
  (list.map prod.fst xτs).nodup →
  list.forall₂ (prod.forall₂ eq (λ τ τ', eval_ty Γ τ τ' ∧ τ'.small)) xτs xτs' →
  (∀ s ∈ body,
    header = ff ∧
    (∀ s', ¬ get_body Γ f s') ∧
    stmt.ok R (fdecl header f xτs ret body :: Γ) ret' xτs' s ∧
    s.ok_init xτs') →
  ok (fdecl header f xτs ret body)
| typedef (x τ τ') :
  (∀ τ, ¬ get_typedef Γ x τ) →
  eval_ty Γ τ τ' → ok (typedef x τ)
| sdecl (s) : ok (sdecl s none)
| sdefn (s xτs) :
  (∀ sd, ¬ get_sdef Γ s sd) →
  (list.map prod.fst xτs).nodup →
  (∀ (xτ : ident × type), xτ ∈ xτs → ∃ τ, eval_ty Γ xτ.2 τ) →
  ok (sdecl s (some xτs))

end gdecl

inductive ok' (R : ident → Prop) : ast → ast → Prop
| nil {Γ} : ok' Γ []
| cons {Γ d ds} : gdecl.ok R Γ d → ok' (d :: Γ) ds → ok' Γ (d :: ds)

structure ok (Γ : ast) : Prop :=
(gdecls : ok' (λ i, ∃ s, Γ.get_body i s) [] Γ)
(fdef_uniq : ∀ i fd fd', Γ.get_fdef i fd → Γ.get_fdef i fd' → fd = fd')
(header_no_def : ∀ i, Γ.is_header i tt → ∀ s, ¬ Γ.get_body i s)
(fdef_tdef : ∀ i fd, Γ.get_fdef i fd → ∀ τ, ¬ Γ.get_typedef i τ)
(main : Γ.get_fdef main ⟨[], c0.type.int⟩ ∧ ∃ s, Γ.get_body main s)

end ast

end c0
