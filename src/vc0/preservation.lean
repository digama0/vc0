import vc0.basic

namespace c0

open ast ast.gdecl

theorem start_ok (Γ : ast) (ok : Γ.ok) : ∀ s, start Γ s → state.ok Γ s
| _ (@start.mk _ s h) :=
  by rcases get_body_ok' ok.ind h with ⟨h₁, h₂|⟨⟨⟩⟩, _, h₃⟩; exact
  state.ok.stmt (some type.int) env.ok.empty vtype.of_ty.int h₁ h₃ (or.inl h₂)

namespace value

theorem default.ok {Γ : ast} {ts v} (Γok : Γ.ok)
  (h : default Γ ts v) (E) : ok_type_or_sdef Γ E v ts :=
begin
  induction h,
  { exact ⟨_, vtype.of_ty.int, ok.int⟩ },
  { exact ⟨_, vtype.of_ty.bool, ok.bool⟩ },
  { exact ⟨_, vtype.of_ty.ref (vtype.of_ty_fn _).2, ok.null⟩ },
  { exact ⟨_, vtype.of_ty.arr (vtype.of_ty_fn _).2, ok.null⟩ },
  { rcases h_ih with ⟨vs, vm, al, IH⟩,
    refine ⟨_, vtype.of_ty.struct, ok.struct vm
      (λ sd' h₁, _) (λ sd' x t τ v' h₁ h₂ h₃ h₄, _)⟩;
    cases get_sdef_determ Γok.ind h_a h₁, {exact al},
    rcases IH h₄ h₂ with ⟨vτ', tτ, vt'⟩,
    cases vtype.of_ty_determ h₃ tτ,
    exact vt' },
  { exact ⟨∅, to_map.nil, list.forall₂.nil, by rintro _ _ _ _ ⟨⟩⟩ },
  case c0.value.default.cons : Δ x τ h v vs h₁ h₂ IH₁ IH₂ {
    rcases IH₁ with ⟨τ', tτ₁, vok⟩,
    rcases IH₂ with ⟨τs', tm, al, IH⟩,
    have tm' := tm.cons (mt al.mem_iff.2 h),
    refine ⟨_, tm', al.cons ⟨⟨⟩⟩,
      λ y yτ v' yf m, _⟩,
    rcases alist.mem_lookup_iff.1 m with ⟨⟨⟩⟩ | m,
    { have := (is_field_lookup tm').1 yf,
      cases option.mem_unique
        ((is_field_lookup tm').1 yf) alist.lookup_cons_self,
      exact ⟨_, tτ₁, vok⟩ },
    { have := alist.mem_lookup_iff.2 m,
      rcases alist.mem_lookup_iff.1 ((is_field_lookup tm').1 yf) with ⟨⟨⟩⟩ | yf,
      { cases h ⟨_, m⟩ },
      exact IH ((is_field_lookup tm).2 (alist.mem_lookup_iff.2 yf)) this } },
end

theorem default.ok' {Γ : ast} {t τ v} (ok : Γ.ok)
  (h : default Γ (sum.inl t) v) (E)
  (tτ : vtype.of_ty (exp.type.reg t) τ) : value.ok Γ E v τ :=
let ⟨τ', h₁, h₂⟩ := h.ok ok E in vtype.of_ty_determ h₁ tτ ▸ h₂

theorem ok.repeat {Γ E v τ} (h : value.ok Γ E v τ) :
  ∀ {n}, value.ok Γ E (value.repeat v n) (vtype.arr' τ n)
| 0     := value.ok.nil
| (n+1) := value.ok.cons h ok.repeat

end value

namespace addr

theorem at_head.ok {Γ E τ τs} {R : value → value → Prop}
  (Rok : ∀ x, value.ok Γ E x τ → ∀ y, R x y → value.ok Γ E y τ)
  (x) (xok : value.ok Γ E x (vtype.cons τ τs)) (y)
  (h : value.at_head R x y) : value.ok Γ E y (vtype.cons τ τs) :=
begin
  rcases xok with _|_|_|_|_|⟨x, vs, _, _, xok, xsok⟩,
  rcases h with ⟨x, y, vs, r⟩,
  exact value.ok.cons (Rok _ xok _ r) xsok
end

theorem at_tail.ok {Γ E τ τs} {R : value → value → Prop}
  (Rok : ∀ x, value.ok Γ E x τs → ∀ y, R x y → value.ok Γ E y τs)
  (x) (xok : value.ok Γ E x (vtype.cons τ τs)) (y)
  (h : value.at_tail R x y) : value.ok Γ E y (vtype.cons τ τs) :=
begin
  rcases xok with _|_|_|_|_|⟨x, vs, _, _, xok, xsok⟩,
  rcases h with ⟨x, y, vs, r⟩,
  exact value.ok.cons xok (Rok _ xsok _ r)
end

theorem update.ok {Γ E Δ H σ η} (σok : vars_ty.ok Δ σ)
  (Hok : heap.ok Γ H E) (ηok : vars.ok Γ E η σ)
  {R a H' η' τ} (aok : addr.ok Γ E σ a τ)
  (h : update H η R a H' η')
  (Rok : ∀ x, value.ok Γ E x τ → ∀ y, R x y → value.ok Γ E y τ) :
  heap.ok Γ H' E ∧ vars.ok Γ E η' σ :=
begin
  induction h generalizing τ,
  case c0.addr.update.ref : R n H' {
    rcases aok with ⟨_, _, m⟩,
    suffices : ∀ E', list.forall₂ (value.ok Γ E) H E' → τ ∈ list.nth E' n →
      list.forall₂ (value.ok Γ E) H' E', from ⟨this _ Hok m, ηok⟩,
    clear Hok m,
    induction h_a with v v' vs r n v' H H' h IH;
      intros E' Hok m; cases Hok with _ τ' _ E' v'ok vsok,
    { cases m,
      exact list.forall₂.cons (Rok _ v'ok _ r) vsok },
    { exact list.forall₂.cons v'ok (IH _ vsok m) } },
  case c0.addr.update.var : R i v v' mη r {
    refine ⟨Hok, λ j τ' τσ, _⟩,
    rcases ηok _ _ τσ with ⟨x, xη, xok⟩,
    rcases aok with _|⟨_, _, mσ⟩,
    revert η, refine λ η, finmap.induction_on η (λ η, _), intros,
    have := alist.replace_forall₂ i v' η,
    rcases this.rel_of_lookup_right xη with ⟨v', m', h⟩,
    refine ⟨v', m', _⟩,
    cases h,
    { cases option.mem_unique mη xη,
      cases option.mem_unique mσ τσ,
      exact Rok _ xok _ r },
    { exact xok } },
  case c0.addr.update.head : R a H' η' h IH {
    rcases aok with _|_|⟨_, _, τs, aok⟩,
    exact IH aok (at_head.ok Rok) },
  case c0.addr.update.tail : R a H' η' h IH {
    rcases aok with _|_|_|⟨_, τ₁, _, aok⟩,
    exact IH aok (at_tail.ok Rok) },
  case c0.addr.update.nth : R a i H' η' h IH {
    rcases aok with _|_|_|_|⟨_, τ₁, _, aok⟩,
    apply IH aok,
    rintro _ (_|_|_|_|_|_|⟨x,_,n,xok⟩) _ ⟨_, y, _, lt, r⟩,
    apply value.ok.arr,
    clear h IH a_1 a_2,
    induction i generalizing x y n,
    { cases n, {cases lt},
      exact at_head.ok Rok _ xok _ r },
    { cases n, {cases lt},
      refine at_tail.ok _ _ xok _ r,
      exact λ x xok y, i_ih xok (nat.lt_of_succ_lt_succ lt) } }
end

theorem get.ok {Γ E Δ H σ η}
  (σok : vars_ty.ok Δ σ) (Hok : heap.ok Γ H E) (ηok : vars.ok Γ E η σ)
  {v a τ} (aok : addr.ok Γ E σ a τ) (h : get H η a v) : value.ok Γ E v τ :=
begin
  induction h generalizing τ,
  case c0.addr.get.ref : n v h {
    cases aok, exact list.forall₂.nth Hok h aok_a },
  case c0.addr.get.var : n v h {
    cases aok, exact ηok.ok_of_mem aok_a h },
  case c0.addr.get.head : a v vs h IH {
    rcases aok with _|_|⟨_, _, τs, aok⟩,
    cases IH aok, exact a_1 },
  case c0.addr.get.tail : a v vs h IH {
    rcases aok with _|_|_|⟨_, τ₁, _, aok⟩,
    cases IH aok, exact a_2 },
  case c0.addr.get.nth : a i n v v' h lt h' IH {
    rcases aok with _|_|_|_|⟨_, _, _, aok⟩,
    cases IH aok, exact h'.ok a_1 lt },
  case c0.addr.get.field : a f v' v h hf IH {
    rcases aok with _|_|_|_|_|⟨_, s, _, t, sd, _, hsd, m, tτ, aok⟩,
    cases IH aok, exact a_3 _ _ _ _ _ hsd m tτ hf }
end

end addr

theorem assign.ok {Γ E Δ σ η x v t τ}
  (σok : vars_ty.ok Δ σ) (ηok : vars.ok Γ E η σ)
  (xok : t ∈ Δ.lookup x)
  (tτ : vtype.of_ty (exp.type.reg t) τ)
  (vok : value.ok Γ E v τ) :
∃ σ', vars_ty.ok Δ σ' ∧
  σ'.keys = insert x σ.keys ∧
  vars.ok Γ E (vars.assign η x v) σ' :=
begin
  by_cases xσ : x ∈ σ,
  { refine ⟨σ, σok, (finset.insert_eq_of_mem (finmap.mem_keys.2 xσ)).symm, _⟩,
    rw [vars.assign, if_pos (ηok.mem xσ)],
    intros y τ' hy,
    by_cases x = y,
    { subst y,
      rcases σok _ _ hy with ⟨t', h₁, h₂⟩,
      cases option.mem_unique xok h₁,
      cases vtype.of_ty_determ tτ h₂,
      exact ⟨v, finmap.lookup_replace_self (ηok.mem xσ), vok⟩ },
    { rcases ηok _ _ hy with ⟨v', h₁, h₂⟩,
      refine ⟨v', _, h₂⟩,
      convert h₁ using 1,
      exact finmap.lookup_replace_of_ne h } },
  { refine ⟨σ.insert x τ, λ y τ' hy, _, finmap.keys_insert _ _ _, λ y τ' hy, _⟩;
      rw finmap.lookup_insert_of_neg xσ at hy;
      rcases hy with ⟨⟨⟩⟩ | hy,
    { exact ⟨_, xok, tτ⟩ },
    { exact σok _ _ hy },
    { refine ⟨v, _, vok⟩,
      rw vars.assign, split_ifs,
      { exact finmap.lookup_replace_self h },
      { exact (finmap.lookup_insert_of_neg h).2 (or.inl rfl) } },
    { rcases ηok _ _ hy with ⟨v', h₁, h₂⟩,
      refine ⟨v', _, h₂⟩,
      rw vars.assign, split_ifs,
      { rwa finmap.lookup_replace_of_ne,
        rintro rfl,
        cases xσ (finmap.exists_mem_lookup_iff.1 ⟨_, hy⟩) },
      { exact (finmap.lookup_insert_of_neg h).2 (or.inr h₁) } } }
end

theorem value.step_binop.ok {Γ E op t₁ t₂ τ₁ τ₂ v₁ v₂ v}
  (sok : value.step_binop op v₁ v₂ (sum.inl v))
  (opok : binop.ok op t₁ t₂)
  (tτ₁ : vtype.of_ty (exp.type.reg t₁) τ₁)
  (tτ₂ : vtype.of_ty (exp.type.reg t₂) τ₂)
  (vok₁ : value.ok Γ E v₁ τ₁) (vok₂ : value.ok Γ E v₂ τ₁) :
  value.ok Γ E v τ₂ :=
begin
  generalize_hyp e : sum.inl v = o at sok,
  cases sok; cases opok; try {cases e}; cases tτ₁; cases tτ₂; try {constructor},
  all_goals {
    rcases (⟨_, e⟩ : ∃ x, sum.inl v = value.to_err x) with ⟨_|_, ⟨⟩⟩,
    constructor }
end

theorem value.step_unop.ok {Γ E op t₁ t₂ τ₁ τ₂ v v'}
  (sok : value.step_unop op v v')
  (opok : unop.ok op t₁ t₂)
  (tτ₁ : vtype.of_ty (exp.type.reg t₁) τ₁)
  (tτ₂ : vtype.of_ty (exp.type.reg t₂) τ₂)
  (vok₁ : value.ok Γ E v τ₁) : value.ok Γ E v' τ₂ :=
by cases sok; cases opok; cases tτ₁; cases tτ₂; constructor

theorem stmt_list.ok.mono {Γ Δ δ₁ δ₂ ret K}
  (ss : δ₁ ⊆ δ₂) (Kok : stmt_list.ok Γ ret Δ δ₁ K) :
  stmt_list.ok Γ ret Δ δ₂ K :=
begin
  induction Kok generalizing δ₂,
  { exact stmt_list.ok.nil Kok_a },
  { rcases Kok_a_2.mono ss with ⟨δ', ss', i⟩,
    exact stmt_list.ok.one Kok_a Kok_a_1 i },
  { rcases Kok_a_1.mono ss with ⟨δ', ss', i⟩,
    exact stmt_list.ok.cons Kok_a i (Kok_ih ss') },
  { exact stmt_list.ok.weak (Kok_ih (finset.erase_subset_erase _ ss)) }
end

theorem stmt_list.ok.cons_inv {Γ E Δ σ η ret s K}
  (σok : vars_ty.ok Δ σ)
  (ηok : vars.ok Γ E η σ) : stmt_list.ok Γ ret Δ σ.keys (s :: K) →
  ∃ Δ' σ' δ', vars_ty.ok Δ' σ' ∧ vars.ok Γ E η σ' ∧
    stmt.ok Γ ret Δ' s ∧
    stmt.init Δ'.keys.to_finset σ'.keys s δ' ∧
    (stmt.returns s ∨ stmt_list.ok Γ ret Δ' δ' K) :=
begin
  generalize e : (s :: K : list stmt) = K',
  generalize e' : σ.keys = δ,
  intro Kok, induction Kok generalizing σ; cases e; subst Kok_δ,
  { exact ⟨_, _, _, σok, ηok, Kok_a, Kok_a_2, or.inl Kok_a_1⟩ },
  { rcases Kok_a_1.subset Kok_a rfl σok.subset with ⟨ss₁', ss₂'⟩,
    exact ⟨_, _, _, σok, ηok, Kok_a, Kok_a_1, or.inr Kok_a_2⟩ },
  { exact Kok_ih rfl σok.erase ηok.erase (finmap.keys_erase _ _) }
end

theorem step_deref.ok {Γ E σs Δ σ H S η ret a τ K s'}
  (σok : vars_ty.ok Δ σ) (Eok : heap.ok Γ H E)
  (ηok : vars.ok Γ E η σ) (Sok : stack.ok Γ E σs S ret)
  (aok : addr_opt.ok Γ E σ a τ)
  (Kok : cont.ok' Γ E σ Δ ret K τ)
  (h : step_deref ⟨H, S, η⟩ a K s') : state.ok Γ s' :=
begin
  cases h,
  { apply state.ok.err },
  { exact state.ok.ret ⟨σok, Eok, ηok, Sok⟩
      (h_a_1.ok σok Eok ηok aok) Kok }
end

theorem step_ret.ok {Γ E σs Δ σ H S η τ v s'}
  (σok : vars_ty.ok Δ σ) (Eok : heap.ok Γ H E)
  (ηok : vars.ok Γ E η σ) (Sok : stack.ok Γ E σs S τ)
  (vok : value.ok Γ E v τ)
  (h : step_ret ⟨H, S, η⟩ v s') : state.ok Γ s' :=
begin
  cases h,
  { cases Sok with Δ' η K' S' σ σs τ₁ τ' σok' ηok' Kok' Sok',
    exact state.ok.ret ⟨σok', Eok, ηok', Sok'⟩ vok Kok' },
  { apply state.ok.done }
end

theorem step_call.ok {Γ : ast} {Δ : ctx} {E vs τs η}
  (τok : vtype.of_ty (exp.type.ls Δ.values) τs)
  (sc : step_call Δ vs η) (vok : value.ok Γ E vs τs) :
  ∃ σ, vars_ty.ok Δ σ ∧ vars.ok Γ E η σ ∧ Δ.keys.to_finset ⊆ σ.keys ∧ ∀ x ∈ η, x ∈ σ :=
begin
  induction sc with Δ x τ v vs η h a IH generalizing τs; cases τok; cases vok,
  { exact ⟨∅, by rintro _ _ ⟨⟩, by rintro _ _ ⟨⟩, λ _, id, by rintro _ ⟨_, ⟨⟩⟩⟩ },
  { rcases IH τok_a_1 vok_a_1 with ⟨σ, σok, ηok, ss, ησ⟩,
    have ηok' := ηok.insert (mt (σok.mem ∘ ησ _) h) vok_a,
    refine ⟨_, (σok.weak _).insert (mt σok.mem h) alist.lookup_cons_self τok_a,
      ηok', _, λ y h, _⟩,
    { rw [alist.cons_keys, list.cons_to_finset, finmap.keys_insert],
      exact finset.insert_subset_insert _ ss },
    { rw [← finmap.mem_keys, finmap.keys_insert, finset.mem_insert, finmap.mem_keys] at h ⊢,
      exact h.imp_right (ησ _) } }
end

theorem step_alloc.ok {Γ E σs Δ σ H S ret η τ v K s}
  (σok : vars_ty.ok Δ σ) (Eok : heap.ok Γ H E)
  (ηok : vars.ok Γ E η σ) (Sok : stack.ok Γ E σs S ret)
  (vok : value.ok Γ E v τ) (Kok : cont.ok' Γ E σ Δ ret K (vtype.ref τ))
  (h : step_alloc ⟨H, S, η⟩ v K s) : state.ok Γ s :=
begin
  cases h,
  have EE : E ≤ E.add τ := E.le_add τ,
  refine state.ok.ret
    ⟨σok, Eok.add (vok.mono EE), ηok.mono EE, Sok.mono EE⟩
    (value.ok.ref _) (Kok.mono EE),
  rw list.forall₂_length_eq Eok,
  apply list.nth_concat_length
end

theorem preservation {Γ : ast} (ok : Γ.ok)
  {s} (sok : state.ok Γ s) {o} (iok : io.ok Γ o)
  {s'} (H : step Γ s o s') : state.ok Γ s' :=
begin
  cases H,
  case c0.step.decl : H S η v τ τ' s K H₁ {
    rcases sok with ⟨_, _, _, _, _, τ, _, _, _, t,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      tτ, ⟨_, _, _, τ', _, hn, ττ', τsm, sok⟩, si, Kok⟩,
    cases si,
    refine state.ok.stmt t ⟨σok.weak _, Eok, ηok, Sok⟩ tτ sok
      (by simpa using si_a) _,
    rcases Kok with ⟨⟨_, _, _, r⟩⟩|Kok,
    { exact or.inl r },
    { exact or.inr Kok.weak } },
  case c0.step.decl_asgn : H S η v τ τ' e s K H₁ {
    rcases sok with ⟨_, _, _, _, _, τ, _, _, _, t,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      tτ, sok, si, Kok⟩, cases si, cases sok,
    refine state.ok.stmt t ⟨σok.weak sok_h, Eok, ηok, Sok⟩ tτ
      (stmt.ok.asgn _ (exp.ok.var Γ alist.lookup_cons_self) sok_a_2.weak' sok_a_1)
      (ast.stmt.init.asgn (finset.empty_subset _) si_a) (or.inr _),
    change stmt.init (insert v sok_Δ.keys.to_finset)
      (insert v sok_σ.keys) s si_δ' at si_a_1,
    rw [← list.cons_to_finset, ← alist.cons_keys] at si_a_1,
    rcases Kok with ⟨⟨⟩⟩|Kok,
    { exact stmt_list.ok.one sok_a_3 Kok_a si_a_1 },
    { exact Kok.weak.cons sok_a_3 si_a_1 } },
  case c0.step.If₁ : C c s₁ s₂ K {
    rcases sok with ⟨_, _, _, _, _, τ, _, _, _, t,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      tτ, sok, si, Kok⟩, cases si, cases sok,
    refine state.ok.exp ⟨σok, Eok, ηok, Sok⟩ si_a ⟨⟩
      ⟨_, sok_a_1, vtype.of_ty.bool⟩
      (cont.ok.If tτ sok_a_2 si_a_1 sok_a_3 si_a_2 _),
    rcases Kok with ⟨⟨⟩⟩|Kok,
    { exact or.inl ⟨Kok_a, Kok_a_1⟩ },
    { exact or.inr Kok } },
  case c0.step.If₂ : C b s₁ s₂ K {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      _, _, _, _, δ₁, δ₂, _, t, tτ, s₁ok, i₁, s₂ok, i₂, Kok⟩,
    cases b,
    exact state.ok.stmt t ⟨σok, Eok, ηok, Sok⟩ tτ s₂ok i₂
      (Kok.imp and.right $ stmt_list.ok.mono (finset.inter_subset_right _ _)),
    exact state.ok.stmt t ⟨σok, Eok, ηok, Sok⟩ tτ s₁ok i₁
      (Kok.imp and.left $ stmt_list.ok.mono (finset.inter_subset_left _ _)) },
  case c0.step.while : C c s K {
    rcases sok with ⟨_, _, _, _, _, τ, _, _, _, t,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      tτ, sok, si, ⟨⟨⟩⟩|Kok⟩, cases si, cases id sok,
    have := si_a_1.subset a_1 rfl σok.subset,
    rcases si.mono this.1 with ⟨δ'', ss', i'⟩,
    exact (state.ok.exp ⟨σok, Eok, ηok, Sok⟩ si_a ⟨⟩ ⟨_, a, vtype.of_ty.bool⟩ $
      cont.ok.If tτ (a_1.seq sok) (si_a_1.seq i') stmt.ok.nop stmt.init.nop $
      or.inr $ Kok.mono $ finset.subset_inter ss' (finset.subset.refl _)) },
  case c0.step.asgn₁ : C lv e K eq {
    rcases sok with ⟨_, _, _, _, _, τ, _, _, _, t,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      tτ, sok, si, ⟨⟨⟩⟩|Kok⟩, cases si, cases sok,
    rcases vtype.of_ty_fn sok_τ with ⟨vτ, hv⟩,
    rw [lval.use, eq] at si_a, rw eq at Kok,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ si_a lv.ok ⟨_, sok_a_1, hv⟩
      (cont.ok.asgn₁ _ _ ⟨_, sok_a_2, hv⟩ si_a_1 ⟨t, tτ, Kok⟩) },
  case c0.step.asgn₂ : C a e K {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      aok, _|⟨_, _, _, _, ⟨t, eok, tτ⟩, eu, t', tτ', Kok⟩⟩,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ eu ⟨⟩
      ⟨_, eok, tτ⟩ (cont.ok.asgn₂ aok ⟨_, tτ', Kok⟩) },
  case c0.step.asgn₃ : H H' S η η' a v K h {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      vok, _|_|⟨_, _, _, _, aok, t, tτ, Kok⟩⟩,
    rcases h.ok σok Eok ηok aok (λ _ _ _ e, e ▸ vok) with ⟨Eok', ηok'⟩,
    exact state.ok.stmt t ⟨σok, Eok', ηok', Sok⟩ tτ
      stmt.ok.nop stmt.init.nop (or.inr Kok) },
  case c0.step.asgn_var₁ : C lv x e K eq {
    rcases sok with ⟨_, _, _, _, _, τ, _, _, _, t,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      tτ, sok, si, ⟨⟨⟩⟩|Kok⟩, cases si, cases sok,
    cases lv; cases eq,
    rcases vtype.of_ty_fn sok_τ with ⟨vτ, hv⟩,
    rcases sok_a_1 with _|_|_|⟨_, t', tΔ⟩,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ si_a_1 ⟨⟩
      ⟨_, sok_a_2, hv⟩ (cont.ok.asgn_var tΔ hv ⟨_, tτ, Kok⟩) },
  case c0.step.asgn_var₂ : H S η x v K {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      vok, Kok⟩, cases Kok, rcases Kok_a_2 with ⟨t, tτ, Kok⟩,
    rcases assign.ok σok ηok Kok_a Kok_a_1 vok with ⟨σ', σok', e, ηok'⟩,
    exact state.ok.stmt _ ⟨σok', Eok, ηok', Sok⟩ tτ
      stmt.ok.nop stmt.init.nop (or.inr (by rwa e)) },
  case c0.step.asgn_err : H S η v K { apply state.ok.err },
  case c0.step.asnop₁ : C lv op e K {
    rcases sok with ⟨_, _, _, _, _, τ, _, _, _, t,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      tτ, sok, si, ⟨⟨⟩⟩|Kok⟩, cases si, cases id sok,
    rcases vtype.of_ty_fn (exp.type.reg τ_1) with ⟨vτ, hv⟩,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ si_a lv.ok
      ⟨_, a, hv⟩ (cont.ok.asnop a_2 hv a_1 si_a_1 ⟨_, tτ, Kok⟩) },
  case c0.step.asnop₂ : C a op e K h {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      aok, Kok⟩, cases Kok, cases Kok_a with _ opok,
    exact step_deref.ok σok Eok ηok Sok aok
      (cont.ok.binop₁ opok Kok_a_1 Kok_a_1 Kok_a_2 Kok_a_3 $
       cont.ok.asgn₂ aok Kok_a_4) h },
  case c0.step.eval₁ : C e K {
    rcases sok with ⟨_, _, _, _, _, τ, _, _, _, t,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      tτ, sok, si, ⟨⟨⟩⟩|Kok⟩, cases si, cases id sok,
    rcases vtype.of_ty_fn τ_1 with ⟨vτ, hv⟩,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ si_a ⟨⟩
      ⟨_, a, hv⟩ (cont.ok.eval _ _ ⟨t, tτ, Kok⟩) },
  case c0.step.eval₂ : C e K {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      aok, Kok⟩, cases Kok, rcases Kok_a with ⟨t, tτ, Kok⟩,
    exact state.ok.stmt t ⟨σok, Eok, ηok, Sok⟩ tτ
      stmt.ok.nop stmt.init.nop (or.inr Kok) },
  case c0.step.assert₁ : C e K {
    rcases sok with ⟨_, _, _, _, _, τ, _, _, _, t,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      tτ, sok, si, ⟨⟨⟩⟩|Kok⟩, cases si, cases id sok,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ si_a ⟨⟩
      ⟨_, a, vtype.of_ty.bool⟩ (cont.ok.assert _ _ ⟨t, tτ, Kok⟩) },
  case c0.step.assert₂ : C b K {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      aok, Kok⟩,
    cases b, {apply state.ok.err},
    cases Kok, rcases Kok_a with ⟨t, tτ, Kok⟩,
    exact state.ok.stmt t ⟨σok, Eok, ηok, Sok⟩ tτ
      stmt.ok.nop stmt.init.nop (or.inr Kok) },
  case c0.step.ret₁ : C e K {
    rcases sok with ⟨_, _, _, _, _, τ, _, _, _, t,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      tτ, sok, si, Kok⟩, cases si, cases id sok, cases a,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ (si_a _ rfl) ⟨⟩
      ⟨_, a_a_1, tτ⟩ cont.ok.ret },
  case c0.step.ret₂ : C v h {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      vok, ⟨⟩⟩,
    exact h.ok σok Eok ηok Sok vok },
  case c0.step.ret_none : C v h {
    rcases sok with ⟨_, _, _, _, _, τ, _, _, _, t,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      tτ, sok, si, Kok⟩, cases id sok, cases a, cases tτ,
    exact h.ok σok Eok ηok Sok value.ok.nil },
  case c0.step.nop₁ : C h {
    rcases sok with ⟨_, _, _, _, _, τ, _, _, _, t,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      tτ, _, si, ⟨⟨⟩⟩|Kok⟩, cases si, cases Kok.eq_none, cases tτ,
    exact h.ok σok Eok ηok Sok value.ok.nil },
  case c0.step.nop₂ : C s K {
    rcases sok with ⟨_, _, _, _, _, τ, _, _, _, t,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      tτ, _, si, ⟨⟨⟩⟩|Kok⟩, cases si,
    rcases Kok.cons_inv σok ηok with ⟨Δ', σ', δ', σok', ηok', sok, si', Kok⟩,
    exact state.ok.stmt t ⟨σok', Eok, ηok', Sok⟩ tτ sok si' Kok },
  case c0.step.seq : C s₁ s₂ K {
    rcases sok with ⟨_, _, _, _, _, τ, _, _, _, t,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      tτ, sok, si, Kok⟩, cases si, cases id sok, rcases Kok with ⟨⟨⟩⟩|Kok,
    { exact state.ok.stmt t ⟨σok, Eok, ηok, Sok⟩ tτ a si_a (or.inl Kok_a) },
    { exact state.ok.stmt t ⟨σok, Eok, ηok, Sok⟩ tτ a si_a
        (or.inr $ stmt_list.ok.one a_1 Kok_a si_a_1) },
    { exact state.ok.stmt t ⟨σok, Eok, ηok, Sok⟩ tτ a si_a
        (or.inr $ Kok.cons a_1 si_a_1) } },
  case c0.step.int : C n K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, _, ⟨t, ⟨⟩, tτ⟩, Kok⟩, cases tτ,
    exact state.ok.ret ⟨σok, Eok, ηok, Sok⟩ value.ok.int Kok },
  case c0.step.bool : C b K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, _, ⟨t, ⟨⟩, tτ⟩, Kok⟩, cases tτ,
    exact state.ok.ret ⟨σok, Eok, ηok, Sok⟩ value.ok.bool Kok },
  case c0.step.null : C K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, _, ⟨t, ⟨⟩, tτ⟩, Kok⟩, cases tτ,
    exact state.ok.ret ⟨σok, Eok, ηok, Sok⟩ value.ok.null Kok },
  case c0.step.var : C i v K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, _, ⟨_, _|_|_|⟨_, t, iΔ⟩, tτ⟩, Kok⟩,
    rcases finmap.exists_mem_lookup_iff.2
      (finmap.mem_keys.1 $ finset.singleton_subset.1 eu) with ⟨τ', iτ'⟩,
    cases vtype.of_ty_determ tτ (σok.ok_of_mem iτ' iΔ),
    exact state.ok.ret ⟨σok, Eok, ηok, Sok⟩ (ηok.ok_of_mem iτ' H_a) Kok },
  case c0.step.binop₁ : C op e₁ e₂ K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, _, ⟨t, eok, tτ⟩, Kok⟩, cases eok,
    have eu₁ := finset.subset.trans (finset.subset_union_left _ _) eu,
    have eu₂ := finset.subset.trans (finset.subset_union_right _ _) eu,
    rcases vtype.of_ty_fn (exp.type.reg eok_τ₁) with ⟨vτ₁, hv₁⟩,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ eu₁ ⟨⟩
      ⟨_, eok_a, hv₁⟩ (cont.ok.binop₁ eok_a_2 hv₁ tτ eok_a_1 eu₂ Kok) },
  case c0.step.binop₂ : C op v₁ e₂ K {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      vok, Kok⟩, cases Kok,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ Kok_a_4 ⟨⟩ ⟨_, Kok_a_3, Kok_a_1⟩
      (cont.ok.binop₂ Kok_a Kok_a_1 Kok_a_2 vok Kok_a_5) },
  case c0.step.binop₃ : C op v₁ v₂ v K sb {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      vok₂, Kok⟩, cases Kok,
    exact state.ok.ret ⟨σok, Eok, ηok, Sok⟩
      (sb.ok Kok_a Kok_a_1 Kok_a_2 Kok_a_3 vok₂) Kok_a_4 },
  case c0.step.binop_err : C op v₁ v₂ err K sb { apply state.ok.err },
  case c0.step.unop₁ : C op e K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, _, ⟨t, eok, tτ⟩, Kok⟩, cases eok,
    rcases vtype.of_ty_fn (exp.type.reg eok_τ₁) with ⟨vτ₁, hv₁⟩,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ eu ⟨⟩
      ⟨_, eok_a, hv₁⟩ (cont.ok.unop eok_a_1 hv₁ tτ Kok) },
  case c0.step.unop₂ : C op v v' K su {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      vok, Kok⟩, cases Kok,
    exact state.ok.ret ⟨σok, Eok, ηok, Sok⟩
      (su.ok Kok_a Kok_a_1 Kok_a_2 vok) Kok_a_3 },
  case c0.step.cond₁ : C c e₁ e₂ K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, _, ⟨t, eok, tτ⟩, Kok⟩, cases eok,
    have eu₁₂ := finset.subset.trans (finset.subset_union_left _ _) eu,
    have euc := finset.subset.trans (finset.subset_union_left _ _) eu₁₂,
    have eu₁ := finset.subset.trans (finset.subset_union_right _ _) eu₁₂,
    have eu₂ := finset.subset.trans (finset.subset_union_right _ _) eu,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ euc ⟨⟩ ⟨_, eok_a, vtype.of_ty.bool⟩
      (cont.ok.cond ⟨_, eok_a_1, tτ⟩ eu₁ ⟨_, eok_a_2, tτ⟩ eu₂ Kok) },
  case c0.step.cond₂ : C b e₁ e₂ K {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      vok, Kok⟩, cases Kok,
    cases b,
    { exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ Kok_a_3 ⟨⟩ Kok_a_2 Kok_a_4 },
    { exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ Kok_a_1 ⟨⟩ Kok_a Kok_a_4 } },
  case c0.step.nil : C K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, _, ⟨t, ⟨⟩, tτ⟩, Kok⟩, cases tτ,
    exact state.ok.ret ⟨σok, Eok, ηok, Sok⟩ value.ok.nil Kok },
  case c0.step.cons₁ : C e es K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, _, ⟨t, eok, tτ⟩, Kok⟩, cases eok, cases tτ,
    have eu₁ := finset.subset.trans (finset.subset_union_left _ _) eu,
    have eu₂ := finset.subset.trans (finset.subset_union_right _ _) eu,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ eu₁ ⟨⟩ ⟨_, eok_a, tτ_a⟩
      (cont.ok.cons₁ ⟨_, eok_a_1, tτ_a_1⟩ eu₂ Kok) },
  case c0.step.cons₂ : C v es K {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      vok, Kok⟩, cases Kok,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ Kok_a_1 ⟨⟩ Kok_a
      (cont.ok.cons₂ vok Kok_a_2) },
  case c0.step.cons₃ : C v₁ v₂ K {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      vok₂, Kok⟩, cases Kok,
    exact state.ok.ret ⟨σok, Eok, ηok, Sok⟩
      (value.ok.cons Kok_a vok₂) Kok_a_1 },
  case c0.step.call₁ : C op e K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, _, ⟨t, eok, tτ⟩, Kok⟩, cases eok,
    rcases vtype.of_ty_fn (exp.type.ls eok_τs) with ⟨vτs, tτs⟩,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ eu ⟨⟩
      ⟨_, eok_a_1, tτs⟩ (cont.ok.call eok_a tτ tτs Kok) },
  case c0.step.call₂ : H S η η' f τ Δ' s vs K bok sc {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      vok, Kok⟩, cases Kok,
    cases ok.fdef_uniq _ _ _ bok.get_fdef Kok_a,
    rcases sc.ok Kok_a_2 vok with ⟨σ', σok', ηok', ss, _⟩,
    rcases get_body_ok' ok.ind bok with ⟨sok, r, δ, si⟩,
    rcases si.mono ss with ⟨δ', ss', si'⟩,
    exact state.ok.stmt _ ⟨σok', Eok, ηok', Sok.cons σok ηok Kok_a_3⟩
      Kok_a_1 sok si' (r.imp_right stmt_list.ok.nil) },
  case c0.step.call_extern : H S η f vs H' v K ext {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      vok, Kok⟩, cases Kok,
    rcases iok ext Kok_a Kok_a_1 Kok_a_2 Eok vok with ⟨E', EE, Eok', vok'⟩,
    exact state.ok.ret ⟨σok, Eok', ηok.mono EE, Sok.mono EE⟩
       vok' (Kok_a_3.mono EE) },
  case c0.step.deref : C e K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, _, ⟨t, eok, tτ⟩, Kok⟩, cases eok,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ eu ⟨⟩ ⟨_, eok_a, tτ.ref⟩
      (cont.ok.addr_deref $ cont.ok.deref Kok) },
  case c0.step.index : C e n K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, _, ⟨t, eok, tτ⟩, Kok⟩, cases eok,
    have eu₁ := finset.subset.trans (finset.subset_union_left _ _) eu,
    have eu₂ := finset.subset.trans (finset.subset_union_right _ _) eu,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ eu₁ ⟨⟩ ⟨_, eok_a, tτ.arr⟩
      (cont.ok.addr_index₁ eok_a_1 eu₂ $ cont.ok.deref Kok) },
  case c0.step.field : C e n K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, _, ⟨t, eok, tτ⟩, Kok⟩, cases eok,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ eu
      (lv_ok_of_struct ok.ind eok_a) ⟨_, eok_a, vtype.of_ty.struct⟩
      (cont.ok.addr_field eok_a_1 eok_a_2 tτ $ cont.ok.deref Kok) },
  case c0.step.deref' : C a K sd {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      aok, Kok⟩, cases Kok,
    exact sd.ok σok Eok ηok Sok aok Kok_a },
  case c0.step.alloc_ref : C τ τ' v K ττ' v0 sa {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, _, ⟨t, eok, tτ⟩, Kok⟩, cases eok,
    cases ast.eval_ty.determ ok.ind ττ' eok_a, cases tτ,
    refine sa.ok σok Eok ηok Sok (v0.ok' ok _ tτ_a) Kok },
  case c0.step.alloc_arr₁ : C τ τ' e K ττ' {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, _, ⟨t, eok, tτ⟩, Kok⟩, cases eok,
    cases ast.eval_ty.determ ok.ind ττ' eok_a, cases tτ,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ eu ⟨⟩ ⟨_, eok_a_2, vtype.of_ty.int⟩
      (cont.ok.alloc_arr tτ eok_a_1 Kok) },
  case c0.step.alloc_arr₂ : C τ v K i n e v0 sa {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      vok, Kok⟩, cases Kok, cases Kok_a,
    exact sa.ok σok Eok ηok Sok (v0.ok' ok _ Kok_a_a).repeat.arr Kok_a_2 },
  case c0.step.alloc_arr_err : C τ i K i0 { apply state.ok.err },
  case c0.step.addr_var : C v K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, _, ⟨t, eok, tτ⟩, Kok⟩, cases eok,
    rcases finmap.exists_mem_lookup_iff.2
      (finmap.mem_keys.1 $ finset.singleton_subset.1 eu) with ⟨τ', vτ'⟩,
    cases vtype.of_ty_determ (σok.ok_of_mem vτ' eok_a) tτ,
    exact state.ok.ret ⟨σok, Eok, ηok, Sok⟩ (addr.ok.var vτ') Kok },
  case c0.step.addr_deref₁ : C e K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, _, ⟨t, eok, tτ⟩, Kok⟩, cases eok,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ eu ⟨⟩ ⟨_, eok_a, tτ.ref⟩
      (cont.ok.addr_deref Kok) },
  case c0.step.addr_deref₂ : C v K {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      vok, Kok⟩, cases Kok,
    refine state.ok.ret ⟨σok, Eok, ηok, Sok⟩ (addr.ok.ref_opt vok) Kok_a },
  case c0.step.addr_index₁ : C e n K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, _, ⟨t, eok, tτ⟩, Kok⟩, cases eok,
    have eu₁ := finset.subset.trans (finset.subset_union_left _ _) eu,
    have eu₂ := finset.subset.trans (finset.subset_union_right _ _) eu,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ eu₁ ⟨⟩ ⟨_, eok_a, tτ.arr⟩
      (cont.ok.addr_index₁ eok_a_1 eu₂ Kok) },
  case c0.step.addr_index₂ : C a n K {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      vok, Kok⟩, cases Kok,
    refine state.ok.exp ⟨σok, Eok, ηok, Sok⟩ Kok_a_1 ⟨⟩ ⟨_, Kok_a, vtype.of_ty.int⟩
      (cont.ok.addr_index₂ (addr.ok.ref_opt vok) Kok_a_2) },
  case c0.step.addr_index₃ : C a n K i j len e lt {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      _, Kok⟩, cases Kok,
    cases len with _ _ v len,
    exact state.ok.ret ⟨σok, Eok, ηok, Sok⟩ (addr.ok.nth Kok_a_1) Kok_a_2 },
  case c0.step.addr_index_err₁ : C i K { apply state.ok.err },
  case c0.step.addr_index_err₂ : C a n K i { apply state.ok.err },
  case c0.step.addr_field₁ : C e f K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, _, ⟨t, eok, tτ⟩, Kok⟩, cases eok,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ eu
      (lv_ok_of_struct ok.ind eok_a) ⟨_, eok_a, vtype.of_ty.struct⟩
      (cont.ok.addr_field eok_a_1 eok_a_2 tτ Kok) },
  case c0.step.addr_field₂ : C a f K {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      aok, Kok⟩, cases Kok,
    exact state.ok.ret ⟨σok, Eok, ηok, Sok⟩
      (addr.ok.field Kok_a Kok_a_1 Kok_a_2 aok) Kok_a_3 },
  case c0.step.addr_field_err : C f K { apply state.ok.err }
end

end c0
