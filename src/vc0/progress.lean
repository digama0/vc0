import vc0.basic

namespace c0
open ast

namespace value

def ts_sized (Γ : ast) : type ⊕ sdef → Prop
| (sum.inl τ) := Γ.sized τ
| (sum.inr sd) := ∀ τ ∈ sd.values, Γ.sized τ

theorem default_exists {Γ : ast} (ok : Γ.okind) :
  ∀ ts, ts_sized Γ ts → ∃ (v : value), default Γ ts v :=
ast.okind.induction' ok $ λ Γ ok IH, begin
  have : ∀ {τ}, Γ.sized τ → ∃ (v : value), default Γ (sum.inl τ) v,
  { intros τ sz, induction τ,
    { exact ⟨_, default.int⟩ },
    { exact ⟨_, default.bool⟩ },
    { exact ⟨_, default.ref⟩ },
    { exact ⟨_, default.arr⟩ },
    { cases sz with sd h,
      cases (get_sdef_ex_iff ok).1 ⟨_, h⟩ with xτs m,
      cases IH with d Γ ok' IH'; rcases m with rfl | m,
      { rcases sdecl_ok1 ok' with ⟨nd, sd', al, sz⟩,
        cases get_sdef_determ ok h ⟨or.inl rfl, al.imp $ λ _ _ _ h, h.weak⟩,
        rcases IH' (sum.inr sd) sz with ⟨v, h'⟩,
        exact ⟨_, default.struct h h'.weak⟩ },
      { cases ok,
        cases (get_sdef_ex_iff ok_a_1).2 ⟨_, m⟩ with sd' h₁,
        cases IH' (sum.inl (type.struct τ)) ⟨_, h₁⟩ with v h₂,
        exact ⟨v, h₂.weak⟩ } } },
  rintro (τ | sd) sz,
  { exact this sz },
  { refine alist.rec' (λ sz, ⟨_, default.nil⟩) (λ sd x τ h IH sz, _) sd sz,
    cases list.forall_mem_cons.1 sz with sz₁ sz₂,
    cases this sz₁ with v v0,
    cases IH sz₂ with vs vs0,
    exact ⟨_, default.cons v0 vs0⟩ }
end

end value

namespace addr

theorem update_at.progress {α β} (S : α → β → Prop) {b}
  {R : α → α → Prop} (hR : ∀ x, S x b → ∃ y, R x y) :
  ∀ {l₁ l₂}, list.forall₂ S l₁ l₂ → ∀ {n}, b ∈ list.nth l₂ n → ∃ l', list.update_at R n l₁ l'
| _ _ (@list.forall₂.cons _ _ S a b' l₁ l₂ r h) 0 rfl :=
  let ⟨y, r⟩ := hR a r in ⟨_, list.update_at.one r⟩
| _ _ (@list.forall₂.cons _ _ S a b' l₁ l₂ r h) (n+1) h' :=
  let ⟨l₂, r⟩ := update_at.progress h h' in
  ⟨_, list.update_at.cons r⟩

theorem at_head.progress {Γ E τ τs}
  {R : value → value → Prop} (hR : ∀ x, value.ok Γ E x τ → ∃ y, R x y)
  (x) (xok : value.ok Γ E x (vtype.cons τ τs)) :
  ∃ y, value.at_head R x y :=
by cases xok; cases hR _ xok_a with v' h'; exact ⟨_, ⟨h'⟩⟩

theorem at_tail.progress {Γ E τ τs}
  {R : value → value → Prop} (hR : ∀ x, value.ok Γ E x τs → ∃ y, R x y)
  (x) (xok : value.ok Γ E x (vtype.cons τ τs)) :
  ∃ y, value.at_tail R x y :=
by cases xok; cases hR _ xok_a_1 with v' h'; exact ⟨_, ⟨h'⟩⟩

theorem at_nth'.progress {Γ E τ}
  {R : value → value → Prop} (hR : ∀ x, value.ok Γ E x τ → ∃ y, R x y) :
  ∀ {i n}, i < n → ∀ x, value.ok Γ E x (vtype.arr' τ n) →
  ∃ y, value.at_nth' R i x y
| 0     (n+1) h := at_head.progress hR
| (i+1) (n+1) h := at_tail.progress (at_nth'.progress (nat.lt_of_succ_lt_succ h))

theorem at_nth.progress {Γ E τ}
  {R : value → value → Prop} (hR : ∀ x, value.ok Γ E x τ → ∃ y, R x y)
  {i n} (lt : i < n) (x) (xok : value.ok Γ E x (vtype.arr τ n)) :
  ∃ y, value.at_nth R i x y :=
begin
  cases xok,
  cases at_nth'.progress hR lt _ xok_a with y h,
  exact ⟨_, lt, h⟩
end

theorem at_field.progress {Γ E τ}
  {R : value → value → Prop} (hR : ∀ x, value.ok Γ E x τ → ∃ y, R x y)
  {s sd f} (hd : Γ.get_sdef s sd)
  {t} (ht : t ∈ sd.lookup f) (tτ : vtype.of_ty (exp.type.reg t) τ)
  (x) (xok : value.ok Γ E x (vtype.struct s)) :
  ∃ y, value.at_field R f x y :=
begin
  rcases xok with _|_|_|_|_|_|_|_|⟨_, vs, rfl, al⟩,
  cases vtype.of_ty_alist sd with τs sτ,
  rcases value.of_map_ok.1 (al _ _ hd sτ) with ⟨vs', e, h⟩,
  cases value.of_map_inj e,
  rcases sτ.rel_of_lookup_right ht with ⟨τ', hτ, tτ'⟩,
  cases vtype.of_ty_determ tτ tτ',
  rcases h.flip.rel_of_lookup_right hτ with ⟨v, m, vok⟩,
  cases hR _ vok with y r,
  exact ⟨_, r, m, rfl, rfl⟩
end

theorem update.progress {Γ E σ H η} (ok : ast.okind Γ)
  (Eok : heap.ok Γ H E) (ηok : vars.ok Γ E η σ)
  {a τ} (aok : addr.ok Γ E σ a τ)
  {R : value → value → Prop} (hR : ∀ x, value.ok Γ E x τ → ∃ y, R x y)
  (Rok : ∀ x, value.ok Γ E x τ → ∀ y, R x y → value.ok Γ E y τ) :
  ∃ H' η', update H η R a H' η' :=
begin
  induction a generalizing τ R; cases aok,
  { cases update_at.progress _ hR Eok aok_a with H' h,
    exact ⟨_, _, update.ref h⟩ },
  { rcases ηok _ _ aok_a with ⟨v, h, vok⟩,
    cases hR v vok with v' h',
    exact ⟨_, _, update.var h h'⟩ },
  { rcases a_ih aok_a_1 (at_head.progress hR) (at_head.ok Rok) with ⟨H', η', h⟩,
    exact ⟨_, _, update.head h⟩ },
  { rcases a_ih aok_a_1 (at_tail.progress hR) (at_tail.ok Rok) with ⟨H', η', h⟩,
    exact ⟨_, _, update.tail h⟩ },
  { rcases a_ih aok_a_2 (at_nth.progress hR aok_a_1) (at_nth.ok Rok aok_a_1) with ⟨H', η', h⟩,
    exact ⟨_, _, update.nth h⟩ },
  { rcases a_ih aok_a_4 (at_field.progress hR aok_a_1 aok_a_2 aok_a_3)
      (at_field.ok ok Rok aok_a_1 aok_a_2 aok_a_3) with ⟨H', η', h⟩,
    exact ⟨_, _, update.field h⟩ }
end

theorem get.progress {Γ E σ Δ H η a τ}
  (Eok : heap.ok Γ H E) (σok : vars_ty.ok Δ σ)
  (ηok : vars.ok Γ E η σ) (aok : addr.ok Γ E σ a τ) :
  ∃ v, get H η a v :=
begin
  induction aok,
  { rcases Eok.flip.nth_right aok_a with ⟨v, h, vok⟩,
    exact ⟨_, get.ref h⟩ },
  { rcases ηok _ _ aok_a with ⟨v, h, vok⟩,
    exact ⟨_, get.var h⟩ },
  { rcases aok_ih with ⟨v, h⟩,
    cases get.ok σok Eok ηok aok_a_1 h,
    exact ⟨_, get.head h⟩ },
  { rcases aok_ih with ⟨v, h⟩,
    cases get.ok σok Eok ηok aok_a_1 h,
    exact ⟨_, get.tail h⟩ },
  case c0.addr.ok.nth : a i n τ lt aok IH {
    rcases IH with ⟨_, h⟩,
    cases get.ok σok Eok ηok aok h,
    suffices : ∃ v', value.is_nth i v v',
    { cases this with v' h', exact ⟨v', get.nth h h'⟩ },
    clear h aok _x,
    induction i with i IH generalizing n v,
    { cases n, {cases lt},
      cases a_1, exact ⟨_, value.is_nth.zero⟩ },
    { cases n, {cases lt},
      cases a_1 with _ _ _ _ _ v vs _ _ vok vsok,
      cases IH (nat.lt_of_succ_lt_succ lt) vsok with v' h',
      exact ⟨_, value.is_nth.succ h'⟩ } },
  case c0.addr.ok.field : a s f t sd τ hd hf tτ aok IH {
    rcases IH with ⟨v, h⟩,
    cases get.ok σok Eok ηok aok h, subst v,
    cases vtype.of_ty_alist sd with τs sτ,
    rcases value.of_map_ok.1 (a_1 _ _ hd sτ) with ⟨vs', e, al⟩,
    cases value.of_map_inj e,
    rcases sτ.rel_of_lookup_right hf with ⟨τ', hτ, tτ'⟩,
    cases vtype.of_ty_determ tτ tτ',
    rcases al.flip.rel_of_lookup_right hτ with ⟨v', h', vok⟩,
    exact ⟨v', get.field h h'⟩ }
end

theorem get_len.progress {Γ E σ Δ H η a τ n}
  (Eok : heap.ok Γ H E) (σok : vars_ty.ok Δ σ)
  (ηok : vars.ok Γ E η σ) (aok : addr.ok Γ E σ a (vtype.arr τ n)) :
  get_len H η a n :=
begin
  cases get.progress Eok σok ηok aok with v h,
  cases get.ok σok Eok ηok aok h, exact ⟨h⟩
end

end addr

theorem alloc_arr.progress (i:int32) :
  (∃ (j:ℕ), (i:ℤ) = j) ∨ i < 0 :=
begin
  cases lt_or_le (i:ℤ) 0 with h₁,
  { rw [← int32.coe_zero, int32.coe_lt] at h₁,
    exact or.inr h₁ },
  { cases e : (i:ℤ) with j,
    { exact or.inl ⟨_, rfl⟩ },
    { rw e at h, cases h } },
end

theorem bounds.progress (n : ℕ) (i:int32) :
  (∃ (j:ℕ), (i:ℤ) = j ∧ j < n) ∨ i < 0 ∨ (n:ℤ) ≤ (i:ℤ) :=
begin
  rcases alloc_arr.progress i with ⟨j, e⟩ | h,
  { cases lt_or_le (i:ℤ) (n:ℤ) with h₂,
    { refine or.inl ⟨j, e, int.coe_nat_lt.1 _⟩,
      rw ← e, exact h₂ },
    { exact or.inr (or.inr h) } },
  { exact or.inr (or.inl h) }
end

theorem step_binop.progress {Γ E op v₁ v₂ t₁ t₂ τ₁}
  (opok : binop.ok op t₁ t₂)
  (tτ₁ : vtype.of_ty (exp.type.reg t₁) τ₁)
  (vok₁ : value.ok Γ E v₁ τ₁)
  (vok₂ : value.ok Γ E v₂ τ₁) :
  ∃ v, value.step_binop op v₁ v₂ v :=
begin
  cases opok,
  case c0.binop.ok.comp {
    cases tτ₁, cases vok₁ with n₁, cases vok₂ with n₂,
    have : ∃ b, value.step_comp opok_1 (value.int n₁) (value.int n₂) b,
    { cases opok_1; exact ⟨_, by constructor⟩ },
    cases this with b h,
    exact ⟨_, value.step_binop.comp h⟩ },
  case c0.binop.ok.eq { exact ⟨_, by constructor; constructor⟩ },
  case c0.binop.ok.ne { exact ⟨_, by constructor; constructor⟩ },
  all_goals {
    cases tτ₁, cases vok₁, cases vok₂,
    exact ⟨_, by constructor⟩ }
end

theorem step_unop.progress  {Γ E op v t₁ t₂ τ₁}
  (opok : unop.ok op t₁ t₂)
  (tτ : vtype.of_ty (exp.type.reg t₁) τ₁)
  (vok : value.ok Γ E v τ₁) :
  ∃ v', value.step_unop op v v' :=
by cases opok; {
  cases tτ, cases vok,
  exact ⟨_, by constructor⟩ }

theorem step_call.progress {Γ E Δ f vs ts τs t τ s}
  (ok : ast.ok Γ)
  (fd : get_fdef Γ f ⟨ts, t⟩)
  (hs : get_body Γ f τ Δ s)
  (tτ : vtype.of_ty (exp.type.ls ts) τs)
  (vsok : value.ok Γ E vs τs) :
  ∃ η, step_call Δ vs η :=
begin
  cases hs,
  have : list.forall₂ (λ (c : ident × ast.type), eval_ty Γ c.2) hs_xτs Δ.values,
  { rw [alist.values, list.forall₂_map_right_iff],
    unfold alist.forall₂ at hs_a_1,
    rw [alist.mk'_entries, list.forall₂_map_left_iff] at hs_a_1,
    refine hs_a_1.imp _, rintro _ _ ⟨i, t, τ, h⟩, exact h },
  cases ok.fdef_uniq fd (ast.get_fdef.mk hs_a this hs_a_2),
  clear _x this fd hs_a hs_a_1 hs_a_2 hs_nd,
  change Δ.entries.map sigma.snd with Δ.values,
  refine alist.rec' _ (λ Δ x t h IH, _) Δ vs τs vsok tτ; intros vs τs vsok tτ,
  { cases tτ, cases vsok,
    exact ⟨_, by constructor⟩ },
  { cases tτ, cases vsok,
    rcases IH _ _ vsok_a_1 tτ_a_1 with ⟨η, h⟩,
    exact ⟨_, step_call.cons _ h⟩ }
end

theorem step_ret.progress {Γ E σs H S η τ v}
  (Sok : stack.ok Γ E σs S τ) (vok : value.ok Γ E v τ) :
  ∃ s', step_ret ⟨H, S, η⟩ v s' :=
begin
  cases Sok,
  { cases vok, exact ⟨_, step_ret.done⟩ },
  { exact ⟨_, step_ret.ret⟩ }
end

theorem step_deref.progress {Γ E σ Δ H S η a τ K}
  (Eok : heap.ok Γ H E) (σok : vars_ty.ok Δ σ)
  (ηok : vars.ok Γ E η σ) (aok : addr_opt.ok Γ E σ a τ) :
  ∃ s', step_deref ⟨H, S, η⟩ a K s' :=
begin
  cases a,
  { exact ⟨_, step_deref.null⟩ },
  { cases addr.get.progress Eok σok ηok aok with v h,
    exact ⟨_, step_deref.deref h⟩ }
end

inductive progresses (Γ : ast) (s : state) : Prop
| final {} : s.final → progresses
| prog {s'} : step Γ s none s' → progresses
| io {i} (f : heap × value → state) :
  (∀ o, step Γ s (some (i, o)) (f o)) → progresses
open progresses

theorem progress {Γ : ast} (ok : Γ.ok)
  {s} (stok : state.ok Γ s) : progresses Γ s :=
begin
  cases stok,
  case c0.state.ok.stmt : E σs σ Δ C τ δ s K t Cok tτ sok si Kok {
    cases Cok with _ _ _ H η S _ _ σok Eok ηok Sok,
    cases sok,
    { exact prog (step.decl sok_a) },
    { exact prog (step.decl_asgn sok_a) },
    { exact prog step.If₁ },
    { exact prog step.while },
    { cases e : lval.is_var sok_lv,
      { exact prog (step.asgn₁ e) },
      { exact prog (step.asgn_var₁ e) } },
    { exact prog step.asnop₁ },
    { exact prog step.eval₁ },
    { exact prog step.assert₁ },
    { cases sok_e,
      { cases sok_a, cases tτ,
        cases step_ret.progress Sok value.ok.nil with s' h,
        exact prog (step.ret_none h) },
      { exact prog step.ret₁ } },
    { cases K,
      { rcases Kok with ⟨⟨⟩⟩ | Kok,
        cases Kok.eq_none, cases tτ,
        cases step_ret.progress Sok value.ok.nil with s' h,
        exact prog (step.nop₁ h) },
      { exact prog step.nop₂ } },
    { exact prog step.seq } },
  case c0.state.ok.exp : E σs σ H η S Δ ret τ e α K Cok eu lok eok {
    cases Cok with _ _ _ H η S _ _ σok Eok ηok Sok,
    rcases eok with ⟨t, eok, tτ⟩,
    cases α,
    { cases eok,
      { exact prog step.int },
      { exact prog step.bool },
      { exact prog step.null },
      { rcases finmap.exists_mem_lookup_iff.2 (finmap.mem_keys.1 eu) with ⟨τ', iτ'⟩,
        rcases ηok _ _ iτ' with ⟨v, h, vok⟩,
        exact prog (step.var h) },
      { exact prog step.binop₁ },
      { exact prog step.unop₁ },
      { exact prog step.cond₁ },
      { exact prog step.nil },
      { exact prog step.cons₁ },
      { exact prog step.call₁ },
      { exact prog step.field },
      { exact prog step.deref },
      { exact prog step.index },
      { cases value.default_exists ok.ind (sum.inl _) eok_a_1 with v v0,
        exact prog (step.alloc_ref eok_a v0 ⟨⟩) },
      { exact prog (step.alloc_arr₁ eok_a) } },
    { cases lok,
      { exact prog step.addr_var },
      { exact prog step.addr_deref₁ },
      { exact prog step.addr_index₁ },
      { exact prog step.addr_field₁ } } },
  case c0.state.ok.ret : E σs σ H η S Δ ret τ α a K Cok aok Kok {
    cases Cok with _ _ _ H η S _ _ σok Eok ηok Sok,
    cases Kok,
    { cases aok,
      exact prog step.If₂ },
    { exact prog step.asgn₂ },
    { cases Kok_a,
      { exact prog step.asgn_err },
      { rcases addr.update.progress ok.ind Eok ηok
          Kok_a_1 (by exact λ _ _, ⟨a, rfl⟩)
          (addr.eq.ok aok) with ⟨H', η', h⟩,
        exact prog (step.asgn₃ h) } },
    { exact prog step.asgn_var₂ },
    { cases step_deref.progress Eok σok ηok aok with s' h,
      exact prog (step.asnop₂ h) },
    { exact prog step.eval₂ },
    { cases aok,
      exact prog step.assert₂ },
    { cases step_ret.progress Sok aok with s' h,
      exact prog (step.ret₂ h) },
    { cases aok;
      exact prog step.addr_deref₂ },
    { cases a,
      { exact prog step.addr_field_err },
      { exact prog step.addr_field₂ } },
    { cases aok;
      exact prog step.addr_index₂ },
    { cases aok, cases Kok_o,
      { exact prog step.addr_index_err₁ },
      { cases Kok_a _ rfl with n aok,
        have h := addr.get_len.progress Eok σok ηok aok,
        rcases bounds.progress n aok_1 with ⟨j, h₁, h₂⟩ | h',
        { exact prog (step.addr_index₃ h h₁ h₂) },
        { exact prog (step.addr_index_err₂ h h') } } },
    { exact prog step.binop₂ },
    { rcases step_binop.progress Kok_a Kok_a_1 Kok_a_3 aok with ⟨v|err, h⟩,
      { exact prog (step.binop₃ h) },
      { exact prog (step.binop_err h) } },
    { rcases step_unop.progress Kok_a Kok_a_1 aok with ⟨v, h⟩,
      exact prog (step.unop₂ h) },
    { cases aok,
      exact prog step.cond₂ },
    { exact prog step.cons₂ },
    { exact prog step.cons₃ },
    { cases Kok,
      rcases Kok_a_6 with ext | ⟨τ, Δ, s, h⟩,
      { exact progresses.io
          (λ o, state.ret cont_ty.V ⟨o.1, S, η⟩ o.2 Kok_K)
          (λ ⟨H', v⟩, step.call_extern ext) },
      { cases step_call.progress ok Kok_a_5 h Kok_a_8 aok with η h',
        exact prog (step.call₂ h h') } },
    { cases step_deref.progress Eok σok ηok aok with s' h,
      exact prog (step.deref' h) },
    { cases aok,
      rcases alloc_arr.progress aok_1 with ⟨j, h⟩ | h,
      { cases value.default_exists ok.ind (sum.inl _) Kok_a_1 with v v0,
        exact prog (step.alloc_arr₂ h v0 ⟨⟩) },
      { exact prog (step.alloc_arr_err h) } } },
  case c0.state.ok.err : err { exact final state.final.err },
  case c0.state.ok.done : n { exact final state.final.done },
end

end c0
