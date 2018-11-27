import c0.dyn_ok

namespace c0

open ast ast.gdecl

namespace ast

@[elab_as_eliminator]
theorem ok_induction {P : ast → Prop} {Γ : ast} (h : Γ.ok) (H₀ : P [])
  (H₁ : ∀ d Γ, gdecl.ok Γ d → P Γ → P (d :: Γ)) : P Γ :=
begin
  rw ← Γ.reverse_reverse,
  suffices : ∀ Γ ds, ok' Γ ds → P Γ → P (list.reverse_core ds Γ),
  from this [] Γ.reverse h.gdecls H₀,
  clear h Γ, introv h₁ h₂,
  induction h₁, {exact h₂},
  exact h₁_ih (H₁ _ _ h₁_a h₂)
end

inductive below (P : ast → Prop) : ast → Prop
| nil {} : below []
| cons (d Γ) : gdecl.ok Γ d → P Γ → below (d :: Γ)

@[elab_as_eliminator]
theorem ok_induction' {P : ast → Prop} {Γ : ast} (h : Γ.ok)
  (H : ∀ Γ, below P Γ → P Γ) : P Γ :=
ok_induction h (H [] below.nil)
  (λ d Γ h₁ h₂, H _ (below.cons d Γ h₁ h₂))

namespace eval_ty

@[elab_as_eliminator]
theorem induction₁ {P : type → c0.type → Prop} {Γ : ast}
  {τ τ'} (H : eval_ty Γ τ τ')
  (Hint : P type.int c0.type.int)
  (Hbool : P type.bool c0.type.bool)
  (Href : ∀ τ τ', eval_ty Γ τ τ' → P τ τ' → P (type.ref τ) (c0.type.ref τ'))
  (Harr : ∀ τ τ', eval_ty Γ τ τ' → P τ τ' → P (type.arr τ) (c0.type.arr τ'))
  (Hstruct : ∀ s, P (type.struct s) (c0.type.struct s))
  (Hweak : ∀ d Γ', Γ = d :: Γ' → ∀ τ τ', eval_ty Γ' τ τ' → P τ τ')
  (Hvar : ∀ v τ₀ Γ', Γ = typedef v τ₀ :: Γ' →
    ∀ τ', eval_ty Γ τ₀ τ' → P τ₀ τ' → P (type.var v) τ') : P τ τ' :=
begin
  generalize e : Γ = Γ', rw e at H,
  induction H; cases e; try {solve_by_elim},
  { exact Hvar _ _ _ rfl _ (weak H_a) (Hweak _ _ rfl _ _ H_a) },
  { exact Href _ _ H_a (H_ih rfl) },
  { exact Harr _ _ H_a (H_ih rfl) }
end

theorem var_determ {Γ : ast} (ok : Γ.ok) : ∀ {v τ₁ τ₂},
  typedef v τ₁ ∈ Γ → typedef v τ₂ ∈ Γ → τ₁ = τ₂ :=
ok_induction ok (by rintro _ _ _ ⟨⟩) $
begin
  rintro d Γ h IH v τ₁ τ₂ (rfl | h₁) (⟨⟨⟩⟩ | h₂),
  { refl },
  { cases h, cases h_a _ h₂ },
  { cases h, cases h_a _ h₁ },
  { exact IH h₁ h₂ }
end

theorem mem_of_var {Γ : ast} {v τ} :
  eval_ty Γ (type.var v) τ → ∃ τ', typedef v τ' ∈ Γ ∧
    ∃ d Γ', Γ = d :: Γ' ∧ eval_ty Γ' τ' τ :=
begin
  generalize e : type.var v = x,
  intro h, induction h; cases e,
  { exact ⟨_, or.inl rfl, _, _, rfl, h_a⟩ },
  { rcases h_ih rfl with ⟨τ', h₁, d', Γ'', rfl, h₂⟩,
    exact ⟨τ', or.inr h₁, _, _, rfl, weak h₂⟩ }
end

theorem int' : ∀ Γ, eval_ty Γ type.int c0.type.int
| [] := int
| (d::Γ) := weak (int' _)

theorem bool' : ∀ Γ, eval_ty Γ type.bool c0.type.bool
| [] := bool
| (d::Γ) := weak (bool' _)

theorem struct' (s) : ∀ Γ, eval_ty Γ (type.struct s) (c0.type.struct s)
| [] := struct
| (d::Γ) := weak (struct' _)

theorem ref_inv {Γ t τ} (H : eval_ty Γ (type.ref t) τ) :
  ∃ τ', eval_ty Γ t τ' ∧ c0.type.ref τ' = τ :=
begin
  generalize e : type.ref t = t', rw e at H,
  induction H; cases e,
  { exact ⟨_, H_a, rfl⟩ },
  { rcases H_ih rfl with ⟨τ', h₁, h₂⟩,
    exact ⟨τ', weak h₁, h₂⟩ }
end

theorem arr_inv {Γ t τ} (H : eval_ty Γ (type.arr t) τ) :
  ∃ τ', eval_ty Γ t τ' ∧ c0.type.arr τ' = τ :=
begin
  generalize e : type.arr t = t', rw e at H,
  induction H; cases e,
  { exact ⟨_, H_a, rfl⟩ },
  { rcases H_ih rfl with ⟨τ', h₁, h₂⟩,
    exact ⟨τ', weak h₁, h₂⟩ }
end

theorem determ {Γ : ast} (ok : Γ.ok) : ∀ {t τ₁ τ₂}
  (h₁ : eval_ty Γ t τ₁) (h₂ : eval_ty Γ t τ₂), τ₁ = τ₂ :=
begin
  have := @var_determ _ ok, revert this,
  refine ok_induction' ok (λ Γ IH VI t, _),
  replace IH : below
    (λ Γ', ∀ {t τ₁ τ₂}, eval_ty Γ' t τ₁ → eval_ty Γ' t τ₂ → τ₁ = τ₂) Γ,
  { cases IH; constructor, {assumption},
    exact @IH_a_1 (λ v τ₁ τ₂ h₁ h₂, VI (or.inr h₁) (or.inr h₂)) },
  induction t,
  { suffices : ∀ {τ}, eval_ty Γ type.int τ → τ = c0.type.int,
    { intros, exact (this h₁).trans (this h₂).symm },
    intros, cases a, {refl},
    { cases IH, exact IH_a_1 a_a (eval_ty.int' _) } },
  { suffices : ∀ {τ}, eval_ty Γ type.bool τ → τ = c0.type.bool,
    { intros, exact (this h₁).trans (this h₂).symm },
    intros, cases a, {refl},
    { cases IH, exact IH_a_1 a_a (eval_ty.bool' _) } },
  { intros,
    rcases mem_of_var h₁ with ⟨τ, m₁, d, Γ', rfl, h₁'⟩,
    rcases mem_of_var h₂ with ⟨τ', m₂, _, _, ⟨⟩, h₂'⟩,
    cases VI m₁ m₂,
    cases IH, exact IH_a_1 h₁' h₂' },
  { intros,
    rcases ref_inv h₁ with ⟨τ₁', h₁', rfl⟩,
    rcases ref_inv h₂ with ⟨τ₂', h₂', rfl⟩,
    cases t_ih h₁' h₂', refl },
  { intros,
    rcases arr_inv h₁ with ⟨τ₁', h₁', rfl⟩,
    rcases arr_inv h₂ with ⟨τ₂', h₂', rfl⟩,
    cases t_ih h₁' h₂', refl },
  { suffices : ∀ {s τ}, eval_ty Γ (type.struct s) τ → τ = c0.type.struct s,
    { intros, exact (this h₁).trans (this h₂).symm },
    intros, cases a, {refl},
    { cases IH, exact IH_a_1 a_a (eval_ty.struct' _ _) } }
end

theorem determ_opt {Γ : ast} (ok : Γ.ok) {t τ₁ τ₂}
  (h₁ : option.forall₂ (eval_ty Γ) t τ₁)
  (h₂ : option.forall₂ (eval_ty Γ) t τ₂) : τ₁ = τ₂ :=
begin
  cases h₁; cases h₂, {refl},
  cases determ ok h₁_a_1 h₂_a_1, refl
end

theorem determ_list_prod {α} {Γ : ast} (ok : Γ.ok) {xts xτs₁ xτs₂}
  (h₁ : list.forall₂ (prod.forall₂ (@eq α) (eval_ty Γ)) xts xτs₁)
  (h₂ : list.forall₂ (prod.forall₂ eq (eval_ty Γ)) xts xτs₂) : xτs₁ = xτs₂ :=
begin
  induction xts with xt xts generalizing xτs₁ xτs₂; cases h₁; cases h₂, {refl},
  rcases h₁_a_1 with ⟨x, τ, rfl, _⟩,
  rcases h₂_a_1 with ⟨_, τ', rfl, _⟩,
  cases xts_ih h₁_a_2 h₂_a_2,
  cases determ ok h₁_a_1_a_1 h₂_a_1_a_2, refl
end

end eval_ty

theorem get_fdef.weak {Γ f fd d} (h : get_fdef Γ f fd) : get_fdef (d :: Γ) f fd :=
by cases h with h f xτs τs' τ τ' body Γ h₁ h₂ h₃; exact
⟨or.inr h₁, h₂.imp (λ _ _, eval_ty.weak), h₃.imp (λ _ _, eval_ty.weak)⟩

theorem get_body.weak {Γ f τ Δ s d} (h : get_body Γ f τ Δ s) : get_body (d :: Γ) f τ Δ s :=
by cases h with h f xτs xτs' τ τ' body Γ h₁ h₂ h₃; exact
⟨or.inr h₁, h₂.imp (λ _ _ h, h.imp (λ _ _, id) (λ _ _, eval_ty.weak)),
  h₃.imp (λ _ _, eval_ty.weak)⟩

theorem is_fdef.weak {Γ f d} : is_fdef Γ f → is_fdef (d :: Γ) f
| ⟨τ, xτs, s, h⟩ := ⟨τ, xτs, s, h.weak⟩

theorem is_extern.weak {Γ f d} (h : is_extern Γ f) : is_extern (d :: Γ) f :=
by cases h with f xτs τ body Γ h; exact ⟨or.inr h⟩

theorem get_sdef.weak {Γ s sd d} (h : get_sdef Γ s sd) : get_sdef (d :: Γ) s sd :=
by cases h with s xτs xτs' Γ h₁ h₂; exact
⟨or.inr h₁, h₂.imp (λ _ _ h, h.imp (λ _ _, id) (λ _ _, eval_ty.weak))⟩

theorem sized.weak {Γ τ d} (h : sized Γ τ) : sized (d :: Γ) τ :=
begin
  cases τ; try {trivial},
  exact h.imp (λ _, get_sdef.weak)
end

namespace exp

theorem ok.weak {Γ Δ e τ d} (h : exp.ok Γ Δ e τ) : exp.ok (d :: Γ) Δ e τ :=
begin
  induction h,
  { exact ok.int },
  { exact ok.bool },
  { exact ok.null },
  { exact ok.var _ h_a },
  { exact ok.binop h_ih_a h_ih_a_1 h_a_2 },
  { exact ok.unop h_ih h_a_1 },
  { exact ok.cond h_ih_a h_ih_a_1 h_ih_a_2 h_a_3 },
  { exact ok.nil },
  { exact ok.cons h_ih_a h_ih_a_1 },
  { exact ok.call h_a.weak h_ih },
  { exact ok.field h_ih h_a_1.weak h_a_2 },
  { exact ok.deref h_ih h_a_1 },
  { exact ok.index h_ih_a h_ih_a_1 },
  { exact ok.alloc_ref _ h_a.weak h_a_1.weak },
  { exact ok.alloc_arr h_a.weak h_a_1.weak h_ih },
end

end exp

namespace stmt

theorem ok.weak {Γ ret_τ Δ s d} (h : stmt.ok Γ ret_τ Δ s) : stmt.ok (d :: Γ) ret_τ Δ s :=
begin
  induction h,
  { exact ok.decl h_a h_a_1.weak h_a_2 h_ih },
  { exact ok.decl_asgn h_a h_a_1.weak h_a_2 h_a_3.weak h_ih },
  { exact ok.If h_a.weak h_ih_a h_ih_a_1 },
  { exact ok.while h_a.weak h_ih },
  { exact ok.asgn _ h_a.weak h_a_1.weak h_a_2 },
  { exact ok.asnop _ h_a.weak h_a_1.weak h_a_2 },
  { exact ok.eval _ h_a.weak h_a_1 },
  { exact ok.assert _ h_a.weak },
  { exact ok.ret (h_a.imp (λ _ _, exp.ok.weak)) },
  { exact ok.nop },
  { exact ok.seq h_ih_a h_ih_a_1 },
end

end stmt
end ast

inductive fdecl_ok (Γ : ast) (header xτs ret body) : Prop
| mk (xτs' ret') :
  (list.map prod.fst xτs).nodup →
  list.forall₂ (prod.forall₂ eq (λ τ τ', eval_ty Γ τ τ' ∧ τ'.small)) xτs xτs' →
  option.forall₂ (eval_ty Γ) ret ret' →
  (∀ s ∈ (body : option stmt),
    header = ff ∧
    stmt.ok Γ ret' xτs' s ∧
    s.ok_init xτs') →
  fdecl_ok

theorem fdecl_ok_of_mem {Γ : ast} (ok : Γ.ok) :
  ∀ {header f xτs ret body},
  fdecl header f xτs ret body ∈ Γ →
  fdecl_ok Γ header xτs ret body :=
ast.ok_induction ok (by rintro _ _ _ _ _ ⟨⟩) $
λ d Γ g IH header f xτs ret body m, begin
  rcases m with rfl | m,
  { cases g with _ _ _ xτs' _ ret' _ h₁ h₂ h₃ h₄,
    refine ⟨xτs', ret', h₂,
      h₃.imp (λ _ _ h, h.imp (λ _ _, id) (λ _ _ ⟨h₁, h₂⟩, ⟨h₁.weak, h₂⟩)),
      h₁.imp (λ _ _ h, h.weak),
      λ s hs, _⟩,
    rcases h₄ s hs with ⟨hs₁, _, hs₂, hs₃⟩,
    exact ⟨hs₁, hs₂, hs₃⟩ },
  { cases IH m with xτs' ret' h₁ h₂ h₃ h₄,
    refine ⟨xτs', ret', h₁,
      h₂.imp (λ _ _ h, h.imp (λ _ _, id) (λ _ _ ⟨h₁, h₂⟩, ⟨h₁.weak, h₂⟩)),
      h₃.imp (λ _ _ h, h.weak),
      λ s hs, _⟩,
    rcases h₄ s hs with ⟨hs₁, hs₂, hs₃⟩,
    exact ⟨hs₁, hs₂.weak, hs₃⟩ }
end

theorem get_body_ok {Γ : ast} (ok : Γ.ok) {f τ Δ s}
  (h : Γ.get_body f τ Δ s) : stmt.ok Γ τ Δ s :=
begin
  cases h,
  cases fdecl_ok_of_mem ok h_a,
  cases ast.eval_ty.determ_opt ok h_a_2 a_2,
  have : list.forall₂ (prod.forall₂ eq (eval_ty Γ)) h_xτs xτs' :=
    a_1.imp (λ _ _ h, h.imp (λ _ _, id) (λ _ _, and.left)),
  cases ast.eval_ty.determ_list_prod ok h_a_1 this,
  exact (a_3 _ rfl).2.1
end

theorem start_ok (Γ : ast) (ok : Γ.ok) : ∀ s, start Γ s → state.ok Γ s
| _ (@start.mk _ s h) := begin
  iterate 8 {constructor},
  existsi some type.int,
  iterate 2 {constructor},
  swap, rintro _ ⟨⟩,
  exact get_body_ok ok h
end

theorem preservation {Γ : ast} (ok : Γ.ok)
  {s} (h₁ : state.ok Γ s) {o} (h₂ : io.ok Γ o)
  {s'} (H : step Γ s o s') : state.ok Γ s' :=
sorry

theorem progress {Γ : ast} (ok : Γ.ok)
  {s} (h₁ : state.ok Γ s) : s.final ∨ ∃ o s', step Γ s o s' :=
sorry

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
