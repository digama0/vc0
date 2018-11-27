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
| none {} : forall₂ none none
| some {a a'} : R a a' → forall₂ (some a) (some a')

theorem forall₂.imp {α α'} {R S : α → α' → Prop} (H : ∀ a a', R a a' → S a a') :
  ∀ {o o'}, forall₂ R o o' → forall₂ S o o'
| _ _ forall₂.none := forall₂.none
| _ _ (forall₂.some h) := forall₂.some (H _ _ h)

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

theorem forall₂.imp {α β α' β'} {R R' : α → α' → Prop} {S S' : β → β' → Prop}
  (H₁ : ∀ a a', R a a' → R' a a') (H₂ : ∀ b b', S b b' → S' b b') :
  ∀ {x x'}, forall₂ R S x x' → forall₂ R' S' x x'
| _ _ ⟨h₁, h₂⟩ := ⟨H₁ _ _ h₁, H₂ _ _ h₂⟩

end prod

namespace sigma

inductive forall₂ {ι} {α α' : ι → Type*} (R : ∀ i, α i → α' i → Prop) :
  (Σ i, α i) → (Σ i, α' i) → Prop
| mk (i a a') : R i a a' → forall₂ ⟨i, a⟩ ⟨i, a'⟩

theorem eta {α} {β : α → Type*} : ∀ x : Σ a, β a, (⟨x.1, x.2⟩ : Σ a, β a) = x
| ⟨a, b⟩ := rfl

end sigma

def int32 := zmod (2^32)

instance int32.has_coe : has_coe int32 ℤ := sorry

instance : comm_ring int32 := by unfold int32; apply_instance

-- TODO: this is unsigned comparison
instance : decidable_linear_order int32 :=
by unfold int32 zmod; apply_instance

namespace int32
def div : int32 → int32 → option int32 := sorry
def mod : int32 → int32 → option int32 := sorry
def shl : int32 → int32 → option int32 := sorry
def shr : int32 → int32 → option int32 := sorry
def bitwise_and : int32 → int32 → int32 := sorry
def bitwise_xor : int32 → int32 → int32 := sorry
def bitwise_or : int32 → int32 → int32 := sorry
def bitwise_not : int32 → int32 := sorry
end int32
