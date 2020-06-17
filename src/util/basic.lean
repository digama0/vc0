import data.pfun data.sigma data.finmap

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
| mk {i a a'} : R i a a' → forall₂ ⟨i, a⟩ ⟨i, a'⟩

theorem forall₂.imp {ι} {α α' : ι → Type*}
  {R S : ∀ i, α i → α' i → Prop} (H : ∀ i a a', R i a a' → S i a a') :
  ∀ {s s'}, forall₂ R s s' → forall₂ S s s'
| _ _ ⟨r⟩ := ⟨H _ _ _ r⟩

theorem forall₂.flip {ι} {α α' : ι → Type*}
  {R : ∀ i, α i → α' i → Prop} :
  ∀ {s s'}, forall₂ (λ i, flip (R i)) s s' → forall₂ R s' s
| _ _ ⟨r⟩ := ⟨r⟩

end sigma

namespace list

inductive update_at {α} (R : α → α → Prop) : ℕ → list α → list α → Prop
| one {a b l} : R a b → update_at 0 (a :: l) (b :: l)
| cons {n a l l'} : update_at n l l' → update_at (n+1) (a :: l) (a :: l')

theorem update_at_forall₂ {α} {R : α → α → Prop} :
  ∀ {n l₁ l₂}, update_at R n l₁ l₂ → forall₂ (λ x y, R x y ∨ x = y) l₁ l₂
| _ _ _ (@update_at.one _ _ a b l h) :=
  forall₂.cons (or.inl h) (@forall₂_refl _ _ ⟨by exact λ a, or.inr rfl⟩ _)
| _ _ _ (@update_at.cons _ _ n a l₁ l₂ h) :=
  forall₂.cons (or.inr rfl) (update_at_forall₂ h)

theorem update_at_forall₂' {α} {R : α → α → Prop} [is_refl α R]
  {n l₁ l₂} (h : update_at R n l₁ l₂) : forall₂ R l₁ l₂ :=
(update_at_forall₂ h).imp (λ a b, or.rec id (by rintro rfl; apply refl))

lemma forall₂_comm {α β} {r : α → β → Prop} {a b} :
  forall₂ r a b ↔ forall₂ (flip r) b a := ⟨forall₂.flip, forall₂.flip⟩

lemma forall₂_and_right {α β} {r : α → β → Prop} {p : β → Prop}
  {l u} : forall₂ (λa b, r a b ∧ p b) l u ↔ forall₂ r l u ∧ (∀b∈u, p b) :=
by rw [and_comm, forall₂_comm, @forall₂_comm _ _ r, ← forall₂_and_left];
   conv in (_∧_) {rw and_comm}; refl

lemma forall₂.mp_trans {α β γ} {r : α → β → Prop} {q : β → γ → Prop}
  {s : α → γ → Prop} (h : ∀a b c, r a b → q b c → s a c) :
  ∀{l₁ l₂ l₃}, forall₂ r l₁ l₂ → forall₂ q l₂ l₃ → forall₂ s l₁ l₃
| []      []      []      forall₂.nil           forall₂.nil           := forall₂.nil
| (a::l₁) (b::l₂) (c::l₃) (forall₂.cons hr hrs) (forall₂.cons hq hqs) :=
  forall₂.cons (h a b c hr hq) (forall₂.mp_trans hrs hqs)

lemma forall₂.nth {α β} {R : α → β → Prop} :
  ∀{l₁ l₂}, forall₂ R l₁ l₂ → ∀ {a b n}, a ∈ l₁.nth n → b ∈ l₂.nth n → R a b
| (a::l₁) (b::l₂) (forall₂.cons hr hrs) _  _  0     rfl rfl := hr
| (a::l₁) (b::l₂) (forall₂.cons hr hrs) a' b' (n+1) h₁  h₂  := forall₂.nth hrs h₁ h₂

lemma forall₂.nth_right {α β} {R : α → β → Prop} :
  ∀{l₁ l₂}, forall₂ R l₁ l₂ → ∀ {a n}, a ∈ l₁.nth n → ∃ b ∈ l₂.nth n, R a b
| (a::l₁) (b::l₂) (forall₂.cons hr hrs) _  0     rfl := ⟨_, rfl, hr⟩
| (a::l₁) (b::l₂) (forall₂.cons hr hrs) a' (n+1) h₁  := forall₂.nth_right hrs h₁

lemma forall₂_reverse {α β} {R : α → β → Prop} :
  ∀ {l₁ l₂}, forall₂ R (reverse l₁) (reverse l₂) ↔ forall₂ R l₁ l₂ :=
suffices ∀ {l₁ l₂}, forall₂ R l₁ l₂ → forall₂ R (reverse l₁) (reverse l₂),
from λ l₁ l₂, ⟨λ h, by simpa using this h, this⟩,
suffices ∀ {l₁ l₂ r₁ r₂}, forall₂ R l₁ l₂ → forall₂ R r₁ r₂ →
  forall₂ R (reverse_core l₁ r₁) (reverse_core l₂ r₂),
from λ l₁ l₂ h, this h forall₂.nil,
λ l₁, begin
  induction l₁ with a l₁ IH; introv h₁ h₂;
    cases h₁ with _ b _ l₂ r h₁',
  exacts [h₂, IH h₁' (forall₂.cons r h₂)]
end

lemma forall₂_concat {α β} {R : α → β → Prop}
  {a b l₁ l₂} : forall₂ R (l₁ ++ [a]) (l₂ ++ [b]) ↔ forall₂ R l₁ l₂ ∧ R a b :=
by rw ← forall₂_reverse; simp [forall₂_reverse, and_comm]

lemma map_prod_fst_eq_of_forall₂_eq {α β γ} {R : β → γ → Prop} {l₁ l₂}
  (h : forall₂ (prod.forall₂ (@eq α) R) l₁ l₂) :
  l₁.map prod.fst = l₂.map prod.fst :=
begin
  rw [← list.forall₂_eq_eq_eq, list.forall₂_map_left_iff,
    list.forall₂_map_right_iff],
  refine h.imp _, rintro _ _ ⟨rfl, _⟩, refl
end

lemma map_sigma_fst_eq_of_forall₂_eq {α} {β β' : α → Type*}
  {R : ∀ a, β a → β' a → Prop} {l₁ l₂}
  (h : forall₂ (sigma.forall₂ R) l₁ l₂) :
  l₁.map sigma.fst = l₂.map sigma.fst :=
begin
  rw [← list.forall₂_eq_eq_eq, list.forall₂_map_left_iff,
    list.forall₂_map_right_iff],
  refine h.imp _, rintro _ _ ⟨⟩, refl
end

lemma rel_of_forall₂_of_nodup {α β γ} {R : β → γ → Prop} {l₁ l₂}
  (h : forall₂ (prod.forall₂ (@eq α) R) l₁ l₂)
  (nd : (l₁.map prod.fst).nodup)
  {a b c} (h₁ : (a, b) ∈ l₁) (h₂ : (a, c) ∈ l₂) : R b c :=
begin
  have nd' := nd, rw map_prod_fst_eq_of_forall₂_eq h at nd',
  induction h, {cases h₁},
  rcases h₁ with rfl | h₁; rcases h₂ with rfl | h₂,
  { cases h_a_1, assumption },
  { rcases h_a_1 with ⟨i, _, _, τ', rfl, _⟩,
    cases (list.nodup_cons.1 nd').1 (list.mem_map_of_mem prod.fst h₂:_) },
  { rcases h_a_1 with ⟨i, v', _, _, rfl, _⟩,
    cases (list.nodup_cons.1 nd).1 (list.mem_map_of_mem prod.fst h₁:_) },
  { exact h_ih (list.nodup_cons.1 nd).2 h₁ h₂ (list.nodup_cons.1 nd').2 }
end

theorem lookmap_forall₂ {α} (f : α → option α) :
  ∀ l, forall₂ (λ a b, a = b ∨ b ∈ f a) l (lookmap f l)
| []     := forall₂.nil
| (a::l) := begin
  dsimp only [lookmap],
  cases e : f a,
  { exact forall₂.cons (or.inl rfl) (lookmap_forall₂ l) },
  { refine forall₂.cons (or.inr e) (@forall₂_refl _ _ ⟨_⟩ l),
    exact λ _, or.inl rfl },
end

theorem lookmap_forall₂' {α} (f : α → option α)
  {β} (g : α → β) (H : ∀ a a' (b ∈ f a) (b' ∈ f a'), g a = g a') :
  ∀ l : list α, (l.map g).nodup → forall₂ (λ a b, (f a).get_or_else a = b) l (lookmap f l)
| []     nd := forall₂.nil
| (a::l) nd := begin
  cases list.nodup_cons.1 nd with nd₁ nd₂,
  dsimp only [lookmap],
  cases e : f a,
  { exact forall₂.cons (by rw e; refl) (lookmap_forall₂' l nd₂) },
  { refine forall₂.cons (by rw e; refl) (forall₂_same $ λ a' h, _),
    cases e' : f a', {refl},
    rw H _ _ _ e _ e' at nd₁,
    cases nd₁ (mem_map_of_mem _ h) },
end

inductive kreplace_rel {α} {β : α → Type*} (a) (b : β a) : ∀ a, β a → β a → Prop
| repl {} {b'} : kreplace_rel a b' b
| refl {} {a' b'} : a ≠ a' → kreplace_rel a' b' b'

theorem kreplace_forall₂ {α} {β : α → Type*} [decidable_eq α] (a) (b : β a)
  {l} (nd : nodupkeys l) : forall₂ (sigma.forall₂ (kreplace_rel a b)) l (kreplace a b l) :=
begin
  refine (lookmap_forall₂' _ _ _ _ nd).imp _,
  { rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h,
    split_ifs at h; cases h,
    { cases h_1, exact ⟨kreplace_rel.repl⟩ },
    { exact ⟨kreplace_rel.refl h_1⟩ } },
  { rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ s₁ h₁ s₂ h₂,
    split_ifs at h₁ h₂; cases h₁; cases h₂,
    exact h_1.symm.trans h }
end

theorem mem_erasep {α} (p : α → Prop) [decidable_pred p] {l : list α}
  (H : pairwise (λ a b, p a → p b → false) l)
  {a : α} : a ∈ erasep p l ↔ ¬ p a ∧ a ∈ l :=
⟨λ h, begin
  by_cases pa : p a,
  { rcases exists_of_erasep (mem_of_mem_erasep h) pa
      with ⟨b, l₁, l₂, h₁, pb, rfl, h₂⟩,
    rw h₂ at h,
    cases mem_append.1 h,
    { cases h₁ _ h_1 pa },
    { cases (pairwise_cons.1 (pairwise_append.1 H).2.1).1 _ h_1 pb pa } },
  { exact ⟨pa, (mem_erasep_of_neg pa).1 h⟩ }
end, λ ⟨h₁, h₂⟩, (mem_erasep_of_neg h₁).2 h₂⟩

theorem mem_kerase {α β} [decidable_eq α] {s : list (sigma β)}
  (nd : s.nodupkeys) {a a' : α} {b' : β a'} :
  sigma.mk a' b' ∈ kerase a s ↔ a ≠ a' ∧ sigma.mk a' b' ∈ s :=
mem_erasep _ $ (nodupkeys_iff_pairwise.1 nd).imp $
by rintro x y h rfl; exact h

@[simp] theorem cons_to_finset {α} [decidable_eq α] (a l) :
  (a :: l : list α).to_finset = insert a l.to_finset :=
by ext; simp

end list

def prod.to_sigma {α β} (x : α × β) : Σ a : α, β := ⟨x.1, x.2⟩

namespace alist
open list

theorem mem_lookup_iff {α} {β : α → Type*} [decidable_eq α]
  {a : α} {b : β a} {s : alist β} :
  b ∈ lookup a s ↔ sigma.mk a b ∈ s.entries :=
list.mem_lookup_iff s.2

theorem exists_mem_lookup_iff {α} {β : α → Type*} [decidable_eq α]
  {a : α} {s : alist β} : (∃ b, b ∈ lookup a s) ↔ a ∈ s :=
option.is_some_iff_exists.symm.trans lookup_is_some

theorem to_sigma_nodupkeys {α β} {l : list (α × β)} :
  (l.map prod.to_sigma).nodupkeys ↔ (l.map prod.fst).nodup :=
by rw [list.nodupkeys, list.keys, list.map_map]; refl

def mk' {α β} (l : list (α × β)) (h : (l.map prod.fst).nodup) : alist (λ _, β) :=
⟨l.map prod.to_sigma, to_sigma_nodupkeys.2 h⟩

@[simp] theorem mk'_entries {α β} (l : list (α × β)) (h) :
  (mk' l h).entries = l.map prod.to_sigma := rfl

@[simp] theorem mk'_keys {α β} (l : list (α × β)) (h) :
  (mk' l h).keys = l.map prod.fst :=
by rw [keys, list.keys, mk'_entries, list.map_map]; refl

def cons {α} {β : α → Type*} (s : alist β)
  (a : α) (b : β a) (h : a ∉ s) : alist β :=
⟨⟨a, b⟩ :: s.entries, nodup_cons.2 ⟨mt mem_keys.1 h, s.nodupkeys⟩⟩

theorem insert_eq_cons {α} {β : α → Type*} [decidable_eq α]
  {s : alist β} {a : α} {b : β a} (h : a ∉ s) : insert a b s = cons s a b h :=
ext $ by simp only [insert_entries_of_neg h]; refl

theorem cons_inj {α} {β : α → Type*} [decidable_eq α]
  {s s' : alist β} {a a' : α} {b : β a} {b' : β a'}
  {h : a ∉ s} {h' : a' ∉ s'}
  (eq : cons s a b h = cons s' a' b' h') :
  sigma.mk a b = ⟨a', b'⟩ ∧ s = s' :=
by cases s; cases s'; cases congr_arg alist.entries eq; exact ⟨rfl, rfl⟩

theorem lookup_cons_iff {α β} [decidable_eq α] {s a b h a' b'} :
  b' ∈ lookup a' (@cons α β s a b h) ↔ sigma.mk a' b' = ⟨a, b⟩ ∨ b' ∈ lookup a' s :=
mem_lookup_iff.trans $ or_congr iff.rfl mem_lookup_iff.symm

theorem lookup_cons_of_lookup {α β} [decidable_eq α] {s a b h a' b'}
  (H : b' ∈ lookup a' s) : b' ∈ lookup a' (@cons α β s a b h) :=
lookup_cons_iff.2 $ or.inr H

theorem lookup_cons_self {α β} [decidable_eq α] {s a b h} :
  b ∈ lookup a (@cons α β s a b h) :=
lookup_cons_iff.2 $ or.inl rfl

@[simp] theorem cons_keys {α} {β : α → Type*} (s : alist β)
  (a : α) (b : β a) (h : a ∉ s) : (alist.cons s a b h).keys = a :: s.keys := rfl

def forall₂ {α} {β γ : α → Type*} (R : ∀ a, β a → γ a → Prop)
  (l₁ : alist β) (l₂ : alist γ) : Prop :=
list.forall₂ (sigma.forall₂ R) l₁.entries l₂.entries

theorem forall₂.imp {α} {β β' : α → Type*}
  {R S : ∀ a, β a → β' a → Prop} (H : ∀ a b b', R a b b' → S a b b')
  {s s'} : forall₂ R s s' → forall₂ S s s' :=
list.forall₂.imp $ λ a b, sigma.forall₂.imp H

lemma forall₂_same {α} {β : α → Type*} {r : ∀ a, β a → β a → Prop} {s : alist β}
  (h : ∀ a (b : β a), sigma.mk a b ∈ s.entries → r a b b) : forall₂ r s s :=
forall₂_same $ λ ⟨a, b⟩ m, ⟨h _ _ m⟩

theorem forall₂.flip {α} {β β' : α → Type*}
  {R : ∀ a, β a → β' a → Prop}
  {s s'} (H : forall₂ (λ a, flip (R a)) s s') : forall₂ R s' s :=
H.flip.imp $ λ _ _, sigma.forall₂.flip

theorem forall₂.keys {α} {β β' : α → Type*}
  {R : ∀ a, β a → β' a → Prop} {s s'} :
  forall₂ R s s' → s.keys = s'.keys :=
map_sigma_fst_eq_of_forall₂_eq

theorem forall₂.mem_iff {α} {β β' : α → Type*}
  {R : ∀ a, β a → β' a → Prop} {s s'} (H : forall₂ R s s')
  {a} : a ∈ s ↔ a ∈ s' :=
by rw [mem_keys, H.keys, mem_keys]

@[elab_as_eliminator]
theorem forall₂.induction {α} {β γ : α → Type*}
  {R : ∀ a, β a → γ a → Prop}
  {P : @alist α β → @alist α γ → Prop} {l₁ : alist β} {l₂ : alist γ}
  (H : forall₂ R l₁ l₂) (H0 : P ∅ ∅)
  (H1 : ∀ l₁ l₂ a b c h₁ h₂, R a b c → forall₂ R l₁ l₂ →
     P l₁ l₂ → P (cons l₁ a b h₁) (cons l₂ a c h₂)) :
  P l₁ l₂ :=
begin
  cases l₁ with l₁ nd₁; cases l₂ with l₂ nd₂,
  dsimp [forall₂] at H,
  induction H, {exact H0},
  rcases H_a_1 with ⟨a, b, c, h⟩,
  cases nodupkeys_cons.1 nd₁ with m₁ nd₁,
  cases nodupkeys_cons.1 nd₂ with m₂ nd₂,
  refine H1 ⟨_, _⟩ ⟨_, _⟩ _ _ _ m₁ m₂ h H_a_2 (H_ih nd₁ nd₂),
end

theorem forall₂_cons {α} {β γ : α → Type*} {R : ∀ a, β a → γ a → Prop}
  {l₁ : alist β} {l₂ : alist γ} {a b c h₁ h₂} :
  forall₂ R (cons l₁ a b h₁) (cons l₂ a c h₂) ↔ R a b c ∧ forall₂ R l₁ l₂ :=
⟨by rintro (_|⟨_,_,_,_,⟨_,_,_,r⟩,h⟩); exact ⟨r, h⟩,
 λ ⟨r, h⟩, list.forall₂.cons ⟨r⟩ h⟩

theorem forall₂.rel_of_mem {α} {β₁ β₂ : α → Type*} [decidable_eq α]
  {R : ∀ a, β₁ a → β₂ a → Prop} {s₁ s₂} (H : forall₂ R s₁ s₂)
  {a} {b₁ : β₁ a} {b₂ : β₂ a}
  (h₁ : sigma.mk a b₁ ∈ s₁.entries)
  (h₂ : sigma.mk a b₂ ∈ s₂.entries) : R a b₁ b₂ :=
begin
  cases s₁ with l₁ nd₁, cases s₂ with l₂ nd₂,
  dsimp only [forall₂] at *,
  induction H, {cases h₁},
  rcases h₁ with rfl | h₁; rcases h₂ with rfl | h₂,
  { cases H_a_1, assumption },
  { rcases H_a_1 with ⟨i, _, b₂', _⟩,
    cases (list.nodupkeys_cons.1 nd₂).1 (list.mem_keys.2 ⟨_, h₂⟩) },
  { rcases H_a_1 with ⟨i, b₁', _, _⟩,
    cases (list.nodupkeys_cons.1 nd₁).1 (list.mem_keys.2 ⟨_, h₁⟩) },
  { cases H_a, cases H_b,
    exact H_ih (list.nodupkeys_cons.1 nd₁).2 h₁ (list.nodupkeys_cons.1 nd₂).2 h₂ }
end

theorem forall₂.rel_of_lookup {α} {β β' : α → Type*} [decidable_eq α]
  {R : ∀ a, β a → β' a → Prop} {s s'} (H : forall₂ R s s')
  {a b b'} (h₁ : b ∈ s.lookup a) (h₂ : b' ∈ s'.lookup a) : R a b b' :=
by rw mem_lookup_iff at h₁ h₂; exact H.rel_of_mem h₁ h₂

theorem forall₂.rel_of_lookup_right {α} {β β' : α → Type*} [decidable_eq α]
  {R : ∀ a, β a → β' a → Prop} {s s'} (H : forall₂ R s s')
  {a b} (h : b ∈ s.lookup a) : ∃ b' ∈ s'.lookup a, R a b b' :=
let ⟨b', h'⟩ := exists_mem_lookup_iff.2
  (H.mem_iff.1 (exists_mem_lookup_iff.1 ⟨_, h⟩)) in
⟨b', h', H.rel_of_lookup h h'⟩

theorem replace_forall₂ {α} {β : α → Type*} [decidable_eq α]
  (a) (b : β a) (s : alist β) : forall₂ (kreplace_rel a b) s (replace a b s) :=
kreplace_forall₂ _ _ s.2

def map {α} {β γ : α → Type*}
  (f : ∀ a, β a → γ a) (s : alist β) : alist γ :=
⟨list.map (sigma.map id f) s.entries, by rw [
    list.nodupkeys, list.keys, list.map_map,
    (by ext ⟨a, b⟩; refl : sigma.fst ∘ sigma.map id f = sigma.fst)];
  exact s.2⟩

theorem map_entries {α} {β γ : α → Type*}
  (f : ∀ a, β a → γ a) (s : alist β) :
  (map f s).entries = list.map (sigma.map id f) s.entries := rfl

theorem mem_map_entries {α} {β γ : α → Type*}
  {f : ∀ a, β a → γ a} {s : alist β} {a} {c : γ a} :
  sigma.mk a c ∈ (map f s).entries ↔ ∃ b : β a, sigma.mk a b ∈ s.entries ∧ f a b = c :=
mem_map.trans ⟨
  by rintro ⟨⟨a, b⟩, h, ⟨⟩⟩; exact ⟨_, h, rfl⟩,
  by rintro ⟨b, h, ⟨⟩⟩; exact ⟨_, h, rfl⟩⟩

theorem lookup_map {α} {β γ : α → Type*} [decidable_eq α]
  {f : ∀ a, β a → γ a} {s : alist β} {a} {c : γ a} :
  c ∈ (map f s).lookup a ↔ ∃ b : β a, b ∈ s.lookup a ∧ f a b = c :=
mem_lookup_iff.trans $ mem_map_entries.trans $ by simp only [mem_lookup_iff]

theorem forall₂_map_left_iff {α} {β γ δ : α → Type*}
  {r : ∀ a, γ a → δ a → Prop} {f : ∀ a, β a → γ a} {l : alist β} {u : alist δ} :
  alist.forall₂ r (alist.map f l) u ↔ alist.forall₂ (λ a c d, r a (f a c) d) l u :=
begin
  unfold forall₂, refine list.forall₂_map_left_iff.trans _,
  apply iff_of_eq, congr', ext ⟨a, b⟩ ⟨a', d⟩,
  split; rintro ⟨_, _, d, r⟩; exact ⟨r⟩
end

theorem forall₂_map_right_iff {α} {β γ δ : α → Type*}
  {r : ∀ a, β a → δ a → Prop} {f : ∀ a, γ a → δ a} {l : alist β} {u : alist γ} :
  alist.forall₂ r l (alist.map f u) ↔ alist.forall₂ (λ a b c, r a b (f a c)) l u :=
⟨λ h, (forall₂_map_left_iff.1 h.flip).flip,
 λ h, ((@forall₂_map_left_iff _ _ _ _ (λ a, flip (r a)) _ _ _).2 h.flip).flip⟩

theorem lookup_replace_of_ne {α} {β : α → Type*} [decidable_eq α]
  {a} {b : β a} {s : alist β} {a'} (ne : a ≠ a'):
  lookup a' (replace a b s) = lookup a' s :=
begin
  ext b',
  split; intro h,
  { rcases (replace_forall₂ a b s).flip.rel_of_lookup_right h with ⟨b'', m, _|_⟩;
    [cases ne rfl, exact m] },
  { rcases (replace_forall₂ a b s).rel_of_lookup_right h with ⟨b'', m, _|_⟩;
    [cases ne rfl, exact m] },
end

theorem lookup_replace_self {α} {β : α → Type*} [decidable_eq α]
  {a} {b : β a} {s : alist β} (h : a ∈ s) :
  b ∈ lookup a (replace a b s) :=
by rcases exists_mem_lookup_iff.2 h with ⟨b', h⟩;
  rcases (replace_forall₂ a b s).rel_of_lookup_right h with ⟨b'', m, _|_⟩;
  [exact m, cases h_1_h_a rfl]

theorem replace_cons_self {α} {β : α → Type*} [decidable_eq α]
  {a} {b b' : β a} {s : alist β} (h) : replace a b' (cons s a b h) = cons s a b' h :=
by simp [replace, cons, kreplace]; rw [lookmap_cons_some]; simp

theorem replace_cons_of_ne {α} {β : α → Type*} [decidable_eq α]
  {a} {b : β a} {s : alist β} (h) {a'} {b' : β a'} (ne : a' ≠ a) :
  ∃ h', replace a' b' (cons s a b h) = cons (replace a' b' s) a b h' :=
⟨mt alist.mem_replace.1 h,
  by simp [replace, cons, kreplace]; rw [lookmap_cons_none]; simp [ne]⟩

@[simp] theorem entries_erase {α β} [decidable_eq α] (a : α) (s : alist β) :
  (erase a s).entries = s.entries.kerase a := rfl

theorem lookup_erase' {α β} [decidable_eq α] {s : alist β} {a a' : α} {b' : β a'} :
  b' ∈ lookup a' (erase a s) ↔ a ≠ a' ∧ b' ∈ lookup a' s :=
by rw [mem_lookup_iff, entries_erase, mem_kerase s.2, mem_lookup_iff]

def values {α β} (s : alist (λ _ : α, β)) : list β := s.entries.map sigma.snd

@[elab_as_eliminator]
def rec' {α β} {C : @alist α β → Sort*}
  (H0 : C ∅) (H1 : ∀ s a b h, C s → C (cons s a b h)) (s) : C s :=
begin
  cases s with l nd,
  induction l with ab l IH,
  { exact H0 },
  { cases ab with a b,
    have := list.nodupkeys_cons.1 nd,
    exact H1 ⟨l, this.2⟩ a b this.1 (IH this.2) }
end

@[simp] theorem rec'_empty {α β C H0 H1} : @rec' α β C H0 H1 ∅ = H0 := rfl

@[simp] theorem rec'_cons {α β C H0 H1} : ∀ s a b h,
  @rec' α β C H0 H1 (cons s a b h) = H1 s a b h (@rec' α β C H0 H1 s)
| ⟨l, nd⟩ a b h := rfl

end alist

namespace finset

theorem singleton_subset {α} {a : α} {s : finset α} :
  singleton a ⊆ s ↔ a ∈ s :=
by simp [subset_def]; refl

theorem union_subset_iff {α} [decidable_eq α]
  {s₁ s₂ t : finset α} : s₁ ∪ s₂ ⊆ t ↔ s₁ ⊆ t ∧ s₂ ⊆ t :=
⟨λ h, ⟨
  subset.trans (subset_union_left _ _) h,
  subset.trans (subset_union_right _ _) h⟩,
λ ⟨h₁, h₂⟩, union_subset h₁ h₂⟩

end finset

namespace finmap
open list

theorem mem_lookup_iff {α} {β : α → Type*} [decidable_eq α]
  {a : α} {b : β a} {s : finmap β} :
  b ∈ lookup a s ↔ sigma.mk a b ∈ s.entries :=
induction_on s $ λ s, alist.mem_lookup_iff

theorem exists_mem_lookup_iff {α} {β : α → Type*} [decidable_eq α]
  {a : α} {s : finmap β} : (∃ b, b ∈ lookup a s) ↔ a ∈ s :=
induction_on s $ λ s, alist.exists_mem_lookup_iff

theorem lookup_insert_of_neg {α} {β : α → Type*} [decidable_eq α]
  {a : α} {b : β a} {s : finmap β} (h : a ∉ s) {a' : α} {b' : β a'} :
  b' ∈ (insert a b s).lookup a' ↔
  sigma.mk a' b' = ⟨a, b⟩ ∨ b' ∈ s.lookup a' :=
by rw [mem_lookup_iff, mem_lookup_iff, insert_entries_of_neg h, multiset.mem_cons]

theorem lookup_insert_self {α β} [decidable_eq α] {s a b} :
  a ∉ s → b ∈ lookup a (@insert α β _ a b s) :=
induction_on s $ λ s h,
by simp [insert, alist.insert_eq_cons h]; exact alist.lookup_cons_self

theorem lookup_erase' {α β} [decidable_eq α] {s : finmap β} {a a' : α} {b' : β a'} :
  b' ∈ lookup a' (erase a s) ↔ a ≠ a' ∧ b' ∈ lookup a' s :=
induction_on s $ λ s, alist.lookup_erase'

theorem lookup_replace_of_ne {α} {β : α → Type*} [decidable_eq α]
  {a} {b : β a} {s : finmap β} {a'} : a ≠ a' →
  lookup a' (replace a b s) = lookup a' s :=
induction_on s $ λ s, alist.lookup_replace_of_ne

theorem lookup_replace_self {α} {β : α → Type*} [decidable_eq α]
  {a} {b : β a} {s : finmap β} : a ∈ s →
  b ∈ lookup a (replace a b s) :=
induction_on s $ λ s, alist.lookup_replace_self

@[simp] theorem keys_to_finmap {α} {β : α → Type*} [decidable_eq α]
  (s : alist β) : keys s.to_finmap = s.keys.to_finset :=
to_finset_eq _

@[simp] theorem keys_insert {α} {β : α → Type*} [decidable_eq α]
  (a : α) (b : β a) (s : finmap β) :
  (insert a b s).keys = has_insert.insert a s.keys :=
induction_on s $ λ s, by ext; simp; by_cases a_1 = a; simp [h]

end finmap
