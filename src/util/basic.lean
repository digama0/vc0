import data.pfun data.sigma data.zmod.basic

namespace roption

def pmap {α β} (o : roption α) (f : o.dom → α → β) : roption β :=
⟨o.dom, λ h, f h (o.get h)⟩

def forall₂ {α β} (R : α → β → Prop) (o₁ : roption α) (o₂ : roption β) : Prop :=
(∀ x ∈ o₁, ∃ y ∈ o₂, R x y) ∧ (∀ y ∈ o₂, ∃ x ∈ o₁, R x y)

theorem forall₂_dom {α β} {R : α → β → Prop} {o₁ : roption α} {o₂ : roption β}
  (H : forall₂ R o₁ o₂) : o₁.dom ↔ o₂.dom :=
⟨λ h, by rcases H.1 _ ⟨h, rfl⟩ with ⟨_, ⟨h', _⟩, _⟩; exact h',
 λ h, by rcases H.2 _ ⟨h, rfl⟩ with ⟨_, ⟨h', _⟩, _⟩; exact h'⟩

@[elab_as_eliminator]
def mem_cases {α} (o : roption α) {C : ∀ a ∈ o, Sort*}
  (H : ∀ h, C (o.get h) ⟨h, rfl⟩) : ∀ a h, C a h :=
λ a h', begin
  have h₂ := h', revert h',
  rw ← h₂.snd; exact λ h₂, H _
end

end roption

namespace option

inductive forall₂ {α α'} (R : α → α' → Prop) : option α → option α' → Prop
| none : forall₂ none none
| some {a a'} : R a a' → forall₂ (some a) (some a')

end option

namespace sum

inductive forall₂ {α β α' β'} (R : α → α' → Prop) (S : β → β' → Prop) : α ⊕ β → α' ⊕ β' → Prop
| inl {a a'} : R a a' → forall₂ (sum.inl a) (sum.inl a')
| inr {b b'} : S b b' → forall₂ (sum.inr b) (sum.inr b')

end sum
namespace prod

inductive forall₂ {α β α' β'} (R : α → α' → Prop) (S : β → β' → Prop) :
  α × β → α' × β' → Prop
| mk {a b a' b'} : R a a' → S b b' → forall₂ (a, b) (a', b')

end prod

namespace sigma

inductive forall₂ {ι} {α α' : ι → Type*} (R : ∀ i, α i → α' i → Prop) :
  (Σ i, α i) → (Σ i, α' i) → Prop
| mk (i a a') : R i a a' → forall₂ ⟨i, a⟩ ⟨i, a'⟩

theorem eta {α} {β : α → Type*} : ∀ x : Σ a, β a, (⟨x.1, x.2⟩ : Σ a, β a) = x
| ⟨a, b⟩ := rfl

end sigma

def int32 := zmod (2^32)

instance : comm_ring int32 := by unfold int32; apply_instance

-- TODO: this is unsigned comparison
instance : decidable_linear_order int32 :=
by unfold int32 zmod; apply_instance
