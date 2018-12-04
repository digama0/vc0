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

theorem update.progress {Γ E σ H η}
  (Eok : heap.ok Γ H E) (ηok : vars.ok Γ E η σ)
  {a τ} (aok : ok Γ E σ a τ)
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
  { rcases a_ih aok_a_2 (λ v vok, _) (at_nth.ok Rok aok_a_1) with ⟨H', η', h⟩,
    { exact ⟨_, _, update.nth h⟩ },
    { cases vok,
      refine ⟨_, ⟨_, _⟩⟩, } }
end

theorem get.progress {H η a} :
  ∃ v, get H η a v :=
sorry

theorem get_len.progress {H η a} :
  ∃ n, get_len H η a n :=
sorry

end addr

theorem bounds.progress (n : ℕ) (i:int32) :
  (∃ (j:ℕ), (i:ℤ) = j ∧ j < n) ∨ i < 0 ∨ (n:ℤ) ≤ (i:ℤ) :=
sorry

theorem alloc_arr.progress (i:int32) :
  (∃ (j:ℕ), (i:ℤ) = j) ∨ i < 0 :=
sorry

theorem step_binop.progress {op v₁ v₂} :
  ∃ v, value.step_binop op v₁ v₂ v :=
sorry

theorem step_unop.progress {op v} :
  ∃ v', value.step_unop op v v' :=
sorry

theorem fdef.progress {Γ : ast} (f : ident) :
  Γ.is_extern f ∨ Γ.is_fdef f :=
sorry

theorem step_call.progress {Δ : ctx} {vs} :
  ∃ η, step_call Δ vs η :=
sorry

theorem step_ret.progress {Γ E σs H S η τ v}
  (Sok : stack.ok Γ E σs S τ) (vok : value.ok Γ E v τ) :
  ∃ s', step_ret ⟨H, S, η⟩ v s' :=
begin
  cases Sok,
  { cases vok, exact ⟨_, step_ret.done⟩ },
  { exact ⟨_, step_ret.ret⟩ }
end

theorem step_deref.progress {C a K} :
  ∃ s', step_deref C a K s' :=
begin
  cases a,
  { exact ⟨_, step_deref.null⟩ },
  { cases addr.get.progress with v h,
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
      { rcases finmap.exists_mem_lookup_iff.2
          (finmap.mem_keys.1 $ finset.singleton_subset.1 eu) with ⟨τ', iτ'⟩,
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
      { rcases addr.update.progress with ⟨H', η', h⟩,
        exact prog (step.asgn₃ h) } },
    { exact prog step.asgn_var₂ },
    { cases step_deref.progress with s' h,
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
    { cases aok, cases Kok_a,
      { exact prog step.addr_index_err₁ },
      { cases addr.get_len.progress with n h,
        rcases bounds.progress n aok_1 with ⟨j, h₁, h₂⟩ | h',
        { exact prog (step.addr_index₃ h h₁ h₂) },
        { exact prog (step.addr_index_err₂ h h') } } },
    { exact prog step.binop₂ },
    { rcases step_binop.progress with ⟨v|err, h⟩,
      { exact prog (step.binop₃ h) },
      { exact prog (step.binop_err h) } },
    { rcases step_unop.progress with ⟨v, h⟩,
      exact prog (step.unop₂ h) },
    { cases aok,
      exact prog step.cond₂ },
    { exact prog step.cons₂ },
    { exact prog step.cons₃ },
    { cases Kok,
      rcases fdef.progress Kok_f with ext | ⟨τ, Δ, s, h⟩,
      { exact progresses.io
          (λ o, state.ret cont_ty.V ⟨o.1, S, η⟩ o.2 Kok_K)
          (λ ⟨H', v⟩, step.call_extern ext) },
      { cases step_call.progress with η h',
        exact prog (step.call₂ h h') } },
    { cases step_deref.progress with s' h,
      exact prog (step.deref' h) },
    { cases aok,
      rcases alloc_arr.progress aok_1 with ⟨j, h⟩ | h,
      { cases value.default_exists ok.ind (sum.inl _) Kok_a_1 with v v0,
        exact prog (step.alloc_arr₂ h v0 ⟨⟩) },
      { exact prog (step.alloc_arr_err h) } } },
  case c0.state.ok.err : err { exact final state.final.err },
  case c0.state.ok.done : n { exact final state.final.done },
end

inductive io_equiv : io → state → io → state → Prop
| none {s} : io_equiv none s none s
| some {i o₁ o₂ s₁ s₂} : (o₁ = o₂ → s₁ = s₂) →
  io_equiv (some (i, o₁)) s₁ (some (i, o₂)) s₂

theorem determ {Γ : ast} (ok : Γ.ok) {s o₁ s₁ o₂ s₂}
  (h₁ : step Γ s o₁ s₁) (h₂ : step Γ s o₂ s₂) : io_equiv o₁ s₁ o₂ s₂ :=
sorry

theorem determ' {Γ : ast} (ok : Γ.ok) {s o s₁ s₂}
  (h₁ : step Γ s o s₁) (h₂ : step Γ s o s₂) : s₁ = s₂ :=
by cases determ ok h₁ h₂; [refl, exact a rfl]

end c0