
namespace rbtree
variables {α : Type*} {lt : α → α → Prop} [decidable_rel lt]

def union (t₁ t₂ : rbtree α lt) : rbtree α lt :=
t₁.fold (flip insert) t₂

def filter (p : α → Prop) [decidable_pred p] (t : rbtree α lt) : rbtree α lt :=
t.fold (λ a s, if p a then s.insert a else s) (mk_rbtree _ _)

def inter (t₁ t₂ : rbtree α lt) : rbtree α lt :=
t₁.filter (λ a, t₂.contains a)

def singleton (a : α) (lt : α → α → Prop . rbtree.default_lt)
  [decidable_rel lt] : rbtree α lt :=
(mk_rbtree α lt).insert a

end rbtree

namespace rbmap
variables {α : Type*} {β : Type*} {lt : α → α → Prop} [decidable_rel lt]

def singleton (a : α) (b : β) (lt : α → α → Prop . rbtree.default_lt)
  [decidable_rel lt] : rbmap α β lt :=
(mk_rbmap α β lt).insert a b

def keys_set (m : rbmap α β lt) : rbtree α lt :=
m.fold (λ a b s, s.insert a) (mk_rbtree _ _)

end rbmap
