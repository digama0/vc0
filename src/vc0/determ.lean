import vc0.basic

namespace c0
open ast

inductive io_equiv : io → state → io → state → Prop
| none {s} : io_equiv none s none s
| some {i o₁ o₂ s₁ s₂} : (o₁ = o₂ → s₁ = s₂) →
  io_equiv (some (i, o₁)) s₁ (some (i, o₂)) s₂

namespace value

theorem step_comp.determ {op v₁ v₂ b₁ b₂}
  (h₁ : step_comp op v₁ v₂ b₁)
  (h₂ : step_comp op v₁ v₂ b₂) : b₁ = b₂ :=
begin
  suffices : ∀ {op' v₁' v₂'} (e : (op, v₁, v₂) = (op', v₁', v₂'))
    (h₂ : step_comp op' v₁' v₂' b₂), b₁ = b₂,
  from this rfl h₂,
  clear h₂, intros,
  induction h₁; induction h₂; cases e; refl
end

theorem step_binop.determ {op v₁ v₂ w₁ w₂}
  (h₁ : step_binop op v₁ v₂ w₁) (h₂ : step_binop op v₁ v₂ w₂) : w₁ = w₂ :=
begin
  cases h₁; cases h₂; try {refl},
  cases h₁_a.determ h₂_a, refl
end

theorem step_unop.determ {op v w₁ w₂}
  (h₁ : step_unop op v w₁) (h₂ : step_unop op v w₂) : w₁ = w₂ :=
by cases h₁; cases h₂; refl

theorem default.determ {Γ} (ok : okind Γ) {ts v₁ v₂}
  (h₁ : default Γ ts v₁)
  (h₂ : default Γ ts v₂) : v₁ = v₂ :=
begin
  induction h₁ generalizing v₂; try {cases h₂}; try {refl},
  { cases get_sdef_determ ok h₁_a h₂_a,
    exact h₁_ih h₂_a_1 },
  { generalize_hyp e : alist.cons h₁_Δ h₁_x h₁_τ h₁_h = Δ' at h₂,
    cases h₂, {cases e},
    rcases alist.cons_inj e with ⟨⟨⟩, rfl⟩,
    cases h₁_ih_a h₂_a, cases h₁_ih_a_1 h₂_a_1, refl }
end

theorem is_nth.determ {n v v₁ v₂}
  (h₁ : is_nth n v v₁) (h₂ : is_nth n v v₂) : v₁ = v₂ :=
by induction h₁ generalizing v₂; cases h₂;
   [refl, {cases h₁_ih h₂_a, refl}]

end value

namespace addr

theorem get.determ {H η a v₁ v₂}
  (h₁ : get H η a v₁)
  (h₂ : get H η a v₂) : v₁ = v₂ :=
begin
  induction h₁ generalizing v₂; cases h₂,
  { exact option.mem_unique h₁_a h₂_a },
  { exact option.mem_unique h₁_a h₂_a },
  { cases h₁_ih h₂_a_1, refl },
  { cases h₁_ih h₂_a_1, refl },
  { cases h₁_ih h₂_a_1, exact h₁_a_2.determ h₂_a_2 },
  { sorry }
end

theorem get_len.determ {H η a v₁ v₂}
  (h₁ : get_len H η a v₁)
  (h₂ : get_len H η a v₂) : v₁ = v₂ :=
by cases h₁; cases h₂; cases h₁_a_1.determ h₂_a_1; refl

theorem update.determ {H η a H₁ η₁ H₂ η₂}
  {R : value → value → Prop} (Rd : ∀ x y₁ y₂, R x y₁ → R x y₂ → y₁ = y₂)
  (h₁ : update H η R a H₁ η₁)
  (h₂ : update H η R a H₂ η₂) : (H₁, η₁) = (H₂, η₂) :=
sorry

theorem eq.determ {v : value} (_ : value) : ∀ y₁ y₂, v = y₁ → v = y₂ → y₁ = y₂
| _ _ rfl h := h

end addr

theorem step_deref.determ {C a K s₁ s₂}
  (h₁ : step_deref C a K s₁) (h₂ : step_deref C a K s₂) : s₁ = s₂ :=
by cases h₁; cases h₂; [refl, {cases h₁_a_1.determ h₂_a_1, refl}]

theorem step_ret.determ {C v s₁ s₂}
  (h₁ : step_ret C v s₁) (h₂ : step_ret C v s₂) : s₁ = s₂ :=
by cases h₁; cases h₂; refl

theorem step_call.determ {Γ : ast} (ok : Γ.okind)
  {vs xτs η₁ η₂}
  (h₁ : step_call xτs vs η₁) (h₂ : step_call xτs vs η₂) : η₁ = η₂ :=
begin
  induction h₁ with Δ x τ v vs η h sc IH generalizing η₂,
  { cases h₂, refl },
  { generalize_hyp e₁ : alist.cons Δ x τ _ = Δ' at h₂,
    cases h₂, rcases alist.cons_inj e₁ with ⟨⟨⟩, rfl⟩,
    cases IH h₂_a, refl }
end

theorem step_alloc.determ {C v K s₁ s₂}
  (sa₁ : step_alloc C v K s₁) (sa₂ : step_alloc C v K s₂) : s₁ = s₂ :=
by cases sa₁; cases sa₂; refl

theorem index_not_lt_zero {i : int32} {n : ℕ} (e : (i : ℤ) = n) : ¬ i < 0 :=
not_lt_of_le $ by rw [← int32.coe_le, e, int32.coe_zero]; apply int.coe_nat_nonneg

theorem index_not_lt_zero_or {i : int32} {j n : ℕ}
  (e : (i : ℤ) = j) (lt : j < n) : ¬ (i < 0 ∨ (n : ℤ) ≤ i)
| (or.inl h) := index_not_lt_zero e h
| (or.inr h) := not_lt_of_le h $ by rwa [e, int.coe_nat_lt]

set_option profiler true
theorem determ {Γ : ast} (ok : Γ.ok) {s o₁ s₁ o₂ s₂}
  (h₁ : step Γ s o₁ s₁) (h₂ : step Γ s o₂ s₂) : io_equiv o₁ s₁ o₂ s₂ :=
begin
  cases h₁,
  case c0.step.asgn_var₁ : C lv x e K h {
    cases h₂,
    case c0.step.asgn₁ : h' { rw h' at h, cases h },
    case c0.step.asgn_var₁ : y h' {
      cases option.mem_unique h h', constructor } },
  case c0.step.asgn₁ : C lv e K h {
    cases h₂,
    case c0.step.asgn_var₁ : x h' { rw h at h', cases h' },
    case c0.step.asgn₁ : h' { constructor } },
  case c0.step.asgn₃ : H H' S η η' a v K h {
    cases h₂,
    rcases h.determ addr.eq.determ h₂_a_1 with ⟨rfl, rfl⟩,
    constructor },
  case c0.step.asnop₂ : C a op e K h {
    cases h₂, cases step_deref.determ h h₂_a_1, constructor },
  case c0.step.ret₂ : C v h {
    cases h₂, cases h.determ h₂_a, constructor },
  case c0.step.ret_none : C v h {
    cases h₂, cases h.determ h₂_a, constructor },
  case c0.step.nop₁ : C h {
    cases h₂, cases h.determ h₂_a, constructor },
  case c0.step.var : C i v K h {
    cases h₂, cases option.mem_unique h h₂_a, constructor },
  case c0.step.binop₃ : C op v₁ v₂ v K h {
    cases h₂; cases h.determ h₂_a; constructor },
  case c0.step.binop_err : C op v₁ v₂ err K h {
    cases h₂; cases h.determ h₂_a; constructor },
  case c0.step.unop₂ : C op v v₁ K h {
    cases h₂, cases h.determ h₂_a, constructor },
  case c0.step.call₂ : H S η η₁ f τ₁ xτs₁ s₁ vs K hb₁ sc₁ {
    cases h₂,
    case c0.step.call₂ : η₂ τ₂ xτs₂ s₂ hb₂ sc₂ {
      cases hb₁.determ ok.ind hb₂,
      cases sc₁.determ ok.ind sc₂,
      constructor },
    case c0.step.call_extern : H' v' h' {
      cases ok.header_no_def h' ⟨_, _, _, hb₁⟩ } },
  case c0.step.call_extern : H S η f vs H' v K h {
    cases h₂,
    case c0.step.call₂ : η₂ τ₂ xτs₂ s₂ hb₂ sc₂ {
      cases ok.header_no_def h ⟨_, _, _, hb₂⟩ },
    case c0.step.call_extern : H' v' h' {
      constructor, rintro ⟨⟩, refl } },
  case c0.step.deref' : C a K h {
    cases h₂, cases h.determ h₂_a_1, constructor },
  case c0.step.alloc_ref : C τ τ' v K tτ v0 sa {
    cases h₂,
    cases tτ.determ ok.ind h₂_a,
    cases v0.determ ok.ind h₂_a_1,
    cases sa.determ h₂_a_2, constructor },
  case c0.step.alloc_arr₁ : C τ τ' e K tτ {
    cases h₂, cases tτ.determ ok.ind h₂_a, constructor },
  case c0.step.alloc_arr₂ : C τ v K i n e v0 sa {
    cases h₂,
    case c0.step.alloc_arr₂ : v' n' e' v0' sa' {
      cases v0.determ ok.ind v0',
      cases int.coe_nat_inj (e.symm.trans e'),
      cases sa.determ sa', constructor },
    case c0.step.alloc_arr_err : h' {
      cases index_not_lt_zero e h' } },
  case c0.step.alloc_arr_err : C τ i K h {
    cases h₂,
    case c0.step.alloc_arr₂ : v' n' e' v0' sa' {
      cases index_not_lt_zero e' h },
    case c0.step.alloc_arr_err : h' { constructor } },
  case c0.step.addr_index₃ : C a n K i j hl e lt {
    cases h₂,
    case c0.step.addr_index₃ : n' j' hl' e' lt' {
      cases int.coe_nat_inj (e.symm.trans e'), constructor },
    case c0.step.addr_index_err₂ : n' hl' lt' {
      cases hl.determ hl',
      cases index_not_lt_zero_or e lt lt' } },
  case c0.step.addr_index_err₂ : C a n K i hl lt {
    cases h₂,
    case c0.step.addr_index₃ : n' j' hl' e' lt' {
      cases hl.determ hl',
      cases index_not_lt_zero_or e' lt' lt },
    case c0.step.addr_index_err₂ : n' hl' lt' { constructor } },
  all_goals {{ cases h₂; constructor }}
end

theorem determ' {Γ : ast} (ok : Γ.ok) {s o s₁ s₂}
  (h₁ : step Γ s o s₁) (h₂ : step Γ s o s₂) : s₁ = s₂ :=
by cases determ ok h₁ h₂; [refl, exact a rfl]

end c0
