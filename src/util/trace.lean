/-
trace.lean
Author: Mario Carneiro

This file defines a coinductive datatype for "traces", which are possible
program behaviors including I/O. Because Lean does not yet support coinductive
datatypes, we have to define this one manually (one would like to define
`trace := gfp trace1` and skip all the lemmas).

A trace is coinductively defined by `trace1 α := roption (η ⊕ (Σ i:ι, o i → α))`.
Here `η` is the type of possible final states (including stuck states and
error states if applicable), `ι` is the type of I/O inputs (possible functions
to call and arguments to pass), and `o i` is the type of I/O return values
(dependent on the input). The trace is really a tree because the I/O output is
nondeterministic; the program behavior describes what will happen for any
return value. The `roption` handles program divergence; if the program does
not terminate then no trace will be produced.
-/
import util.basic

namespace vc0
section
variables (η : Type) {ι : Type} (o : ι → Type)

def trace1 (α : Type) : Type := roption (η ⊕ (Σ i, o i → α))

variables {η o}
def trace1.out {α} (t : trace1 η o α) : roption (Σ i, o i → α) :=
t.bind $ λ x, match x with
| (sum.inl _) := roption.none
| (sum.inr x) := roption.some x
end

theorem trace1.mem_out {α} (t : trace1 η o α) {x} : x ∈ t.out ↔
  (sum.inr x : η ⊕ (Σ i, o i → α)) ∈ (by exact t : roption _) :=
roption.mem_bind_iff.trans
⟨by rintro ⟨_|x, ⟨h, e⟩, ⟨⟩, rfl⟩; exact ⟨_, e⟩,
  λ h, ⟨sum.inr x, h, trivial, rfl⟩⟩

def trace1.fst {α} (t : trace1 η o α) : roption ι :=
sigma.fst <$> trace1.out t

def trace1.snd {α} (t : trace1 η o α) : ∀ i ∈ t.fst, o i → α :=
roption.mem_cases _ (by exact λ h, ((trace1.out t).get h).2)

theorem trace1.fst_snd_mem {α} (t : trace1 η o α) : ∀ i h,
  (⟨i, trace1.snd t i h⟩ : Σ i, o i → α) ∈ t.out :=
roption.mem_cases _ begin
  change ∀ h : t.out.dom, (⟨(t.out.get h).1, (t.out.get h).2⟩ : Σ i, o i → α) ∈ t.out,
  intro h, rw sigma.eta, apply roption.get_mem
end

theorem trace1.snd_eq {α} (t : trace1 η o α) (i h g)
  (H : (⟨i, g⟩ : Σ i, o i → α) ∈ t.out) : trace1.snd t i h = g :=
by simpa using roption.mem_unique (t.fst_snd_mem i h) H

instance trace1.functor : functor (trace1 η o) :=
{ map := λ α β f, roption.map $ sum.map id $ sigma.map id $ λ i, (∘) f }

instance trace1.is_lawful_functor : is_lawful_functor (trace1 η o) :=
{ id_map := λ α, roption.map_id' $ by rintro (_|⟨i, g⟩); refl,
  comp_map := λ α β γ g h t, begin
    refine eq.trans _ (roption.map_map _ _ _).symm,
    simp [(<$>)], congr, ext (_|⟨i, g⟩); refl
  end }

def trace1.pmap {α β} (t : trace1 η o α)
  (f : ∀ x:Σ i, o i → α, x ∈ t.out → o x.1 → α → β) : trace1 η o β :=
⟨t.dom, λ h, begin
  cases e : t.get h with a x,
  { exact sum.inl a },
  { exact sum.inr ⟨x.1, λ b, f _ (t.mem_out.2 ⟨h, e⟩) b (x.2 b)⟩ }
end⟩

theorem trace1.pmap_inl {α β} (t : trace1 η o α) (f h)
  {a} (H : t.get h = sum.inl a) :
  (t.pmap f : trace1 η o β).get h = sum.inl a :=
by simp [trace1.pmap, H]

theorem trace1.pmap_inr {α β} (t : trace1 η o α) (f h)
  {x} (H : t.get h = sum.inr x) :
  (t.pmap f : trace1 η o β).get h =
  sum.inr ⟨x.1, λ b, f _ (t.mem_out.2 ⟨h, H⟩) b (x.2 b)⟩ :=
by simp [trace1.pmap, H]

def trace1.out_map {α β} (f : α → β) (t : trace1 η o α) :
  (f <$> t : trace1 η o β).out = (sigma.map id $ λ i, (∘) f) <$> t.out :=
roption.ext $ λ x, by simp [trace1.mem_out, (<$>), sum.map]; refl

theorem trace1.fst_map {α β} (f : α → β) (t : trace1 η o α) :
  (f <$> t : trace1 η o β).fst = t.fst :=
show sigma.fst <$> trace1.out _ = sigma.fst <$> _, begin
  rw [trace1.out_map, ← comp_map],
  congr' 1, ext ⟨a, b⟩, refl
end

theorem trace1.snd_map {α β} (f : α → β) (t : trace1 η o α) (i h h' b) :
  (f <$> t : trace1 η o β).snd i h b = f (t.snd i h' b) :=
begin
  have := (f <$> t).fst_snd_mem i h,
  simp [t.out_map f] at this,
  rcases this with ⟨i, g, h₁, h₂⟩,
  injection h₂ with h₃ h₄, subst h₃, simp at h₄,
  rw [← h₄, ← t.snd_eq _ h' _ h₁]
end

variables (η o)
def traceN : ℕ → Type → Type
| 0     α := α
| (n+1) α := traceN n (trace1 η o α)
variables {η o}

def traceN.map : ∀ (n) {α β}, (α → β) → traceN η o n α → traceN η o n β
| 0     α β f := f
| (n+1) α β f := @traceN.map n _ _ ((<$>) f)

instance traceN.functor (n) : functor (traceN η o n) :=
{ map := @traceN.map _ _ _ n }

instance traceN.is_lawful_functor : ∀ n, is_lawful_functor (traceN η o n)
| 0 := by split; intros; refl
| (n+1) := begin
    split; intros,
    { show (<$>) id <$> x = x,
      rw [(funext (@id_map (trace1 η o) _ _ _) : (<$>) id = id),
        @id_map _ _ (traceN.is_lawful_functor n)] },
    { change ((<$>) (h ∘ g) <$> x : traceN η o n (trace1 η o γ)) =
        (<$>) h <$> (<$>) g <$> x,
      rw [(funext (@comp_map (trace1 η o) _ _ _ _ _ _ _) :
          (<$>) (h ∘ g) = (<$>) h ∘ (<$>) g),
        @comp_map _ _ (traceN.is_lawful_functor n)] },
  end

def trace1.forall₂ {α β} (R : α → β → Prop) : trace1 η o α → trace1 η o β → Prop :=
roption.forall₂ $ sum.forall₂ eq $ sigma.forall₂ $ λ i f g, ∀ x, R (f x) (g x)

def traceN.forall₂ : ∀ {n α β}, (α → β → Prop) → traceN η o n α → traceN η o n β → Prop
| 0     α β R := R
| (n+1) α β R := @traceN.forall₂ n _ _ (trace1.forall₂ R)

def traceN.fst : ∀ {n α}, traceN η o (n+1) α → roption ι
| 0     α t := trace1.fst t
| (n+1) α t := @traceN.fst n _ t

def traceN.out : ∀ {n α}, traceN η o (n+1) α → roption (Σ i, o i → traceN η o n α)
| 0     α := trace1.out
| (n+1) α := @traceN.out n _

def traceN.snd : ∀ {n α} (t : traceN η o (n+1) α) (i ∈ t.fst), o i → traceN η o n α
| 0     α t := trace1.snd t
| (n+1) α t := @traceN.snd n _ t

theorem traceN.fst_map : ∀ n {α β} (f : α → β) (t : traceN η o (n+1) α),
  (f <$> t : traceN η o (n+1) β).fst = t.fst
| 0     α β f := trace1.fst_map _
| (n+1) α β f := traceN.fst_map n _

theorem traceN.snd_map : ∀ n {α β} (f : α → β) (t : traceN η o (n+1) α) (i h h' b),
  (f <$> t : traceN η o (n+1) β).snd i h b = f <$> t.snd i h' b
| 0     α β f := trace1.snd_map _
| (n+1) α β f := traceN.snd_map n _

theorem traceN.snd_map' (n) {α β} (f : α → β) (t : traceN η o (n+1) α) (i h b) :
  (f <$> t : traceN η o (n+1) β).snd i h b = f <$> t.snd i (by rwa t.fst_map _ _ at h) b :=
traceN.snd_map _ _ _ _ _ _ _

theorem traceN.out_map : ∀ n {α β} (f : α → β) (t : traceN η o n (trace1 η o α)),
  (f <$> t : traceN η o (n+1) β).out =
  (sigma.map id $ by exact λ i g x, f <$> g x) <$> t.out
| 0     α β f t := trace1.out_map _ _
| (n+1) α β f t := traceN.out_map n _ _

variables (η o)
def trace : Type := -- gfp trace1
{f : ∀ n, traceN η o n unit // ∀ n, f n = (λ _, ()) <$> f (n+1) }
variables {η o}

theorem trace_fst_aux (f : ∀ n, traceN η o n unit)
  (H : ∀ n, f n = (λ _, ()) <$> f (n+1)) :
  ∀ n, (f (n+1)).fst = (f 1).fst
| 0 := rfl
| (n+1) := by rw [← trace_fst_aux n, H (n+1), traceN.fst_map]; refl

theorem trace_map_aux (f : ∀ n, traceN η o n unit)
  (H : ∀ n, f n = (λ _, ()) <$> f (n+1)) :
  ∀ n, sigma.fst <$> (f (n+1)).out = sigma.fst <$> (f 1).out
| 0 := rfl
| (n+1) := begin
  rw [← trace_map_aux n, H (n+1), traceN.out_map, ← comp_map],
  congr, ext ⟨i, b⟩, refl
end

def trace.destruct : trace η o → trace1 η o (trace η o)
| ⟨f, H⟩ := trace1.pmap (f 1) (λ x i b _, begin
  have hx : ∀ n, x.1 ∈ traceN.fst (f (n + 1)),
  { intro n, rwa trace_fst_aux _ H n, exact roption.mem_map _ i },
  have := λ n, traceN.out (f (n+1)),
  refine ⟨λ n, traceN.snd (f (n+1)) _ (hx n) b, λ n, _⟩,
  refine eq.trans _ ((f (n+1+1)).snd_map' n (λ _, ()) _ _ b),
  { rw traceN.fst_map, exact hx (n+1) },
  { congr, apply H }
end)

def traceN.iter {α} (F : α → trace1 η o α) (a : α) : ∀ n, traceN η o n α
| 0     := a
| (n+1) := (F <$> traceN.iter n : traceN η o n (trace1 η o α))

theorem traceN.iter_fst {α} (F : α → trace1 η o α) (a : α) :
  ∀ n, (traceN.iter F a (n+1)).fst = (F a).fst
| 0     := rfl
| (n+1) := (traceN.fst_map _ _ _).trans (traceN.iter_fst n)

theorem traceN.iter_snd' {α} (F : α → trace1 η o α) (a : α) : ∀ n i h b,
  (traceN.iter F a (n+1)).snd i h b =
  traceN.iter F ((F a).snd i (by rwa traceN.iter_fst at h) b) n
| 0     i h b := rfl
| (n+1) i h b := (traceN.snd_map' _ _ _ i h b).trans (congr_arg _ (traceN.iter_snd' n _ _ _))

theorem traceN.iter_snd {α} (F : α → trace1 η o α) (a : α) (n i h h' b) :
  (traceN.iter F a (n+1)).snd i h b = traceN.iter F ((F a).snd i h' b) n :=
traceN.iter_snd' _ _ _ _ _ _

def trace.corec {α} (F : α → trace1 η o α) (a : α) : trace η o :=
⟨λ n, (λ _, ()) <$> traceN.iter F a n, λ n,
  by rw traceN.iter; exact
  eq.trans (by refl) ((comp_map _ _ _).trans (comp_map _ _ _))⟩

theorem trace.corec_eq {α} (F : α → trace1 η o α) (a : α) :
  trace.destruct (trace.corec F a) = trace.corec F <$> F a :=
roption.ext' iff.rfl $ λ h₁ h₂, begin
  change (F a).dom at h₁,
  change h₂ with h₁, clear h₂,
  change (trace1.pmap _ _).get _ = sum.map _ _ _,
  have e : ((λ _, ()) <$> traceN.iter F a 1).get h₁ =
    sum.map id (sigma.map id (λ _ _ _, ())) ((F a).get h₁) := rfl,
  cases e' : (F a).get h₁; rw e' at e,
  { rw trace1.pmap_inl _ _ _ e, refl },
  { rw trace1.pmap_inr _ _ _ e, cases val with i g,
    simp! [sigma.map], ext b,
    simp [trace.corec], ext n,
    suffices : ∀ h, traceN.snd ((λ _, ()) <$> traceN.iter F a (n+1))
      i h b = (λ _, ()) <$> traceN.iter F (g b) n, {apply this},
    intro,
    rw traceN.fst_map at h,
    rw [traceN.snd_map _ _ _ _ _ h, traceN.iter_snd', trace1.snd_eq],
    exact (trace1.mem_out _).2 ⟨_, e'⟩ },
end

theorem trace.eq_of_bisim (R : trace η o → trace η o → Prop)
  (H : ∀ t₁ t₂, R t₁ t₂ → trace1.forall₂ R t₁.destruct t₂.destruct) :
  ∀ t₁ t₂, R t₁ t₂ → t₁ = t₂ :=
sorry

end

end vc0
