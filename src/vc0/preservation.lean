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

theorem determ_alist {α} {Γ : ast} (ok : Γ.ok) : ∀ {xts Δ₁ Δ₂}
  (h₁ : alist.forall₂ (λ _:α, eval_ty Γ) xts Δ₁)
  (h₂ : alist.forall₂ (λ _, eval_ty Γ) xts Δ₂), Δ₁ = Δ₂
| ⟨xts, nd⟩ ⟨L₁, nd₁⟩ ⟨L₂, nd₂⟩ h₁ h₂ := begin
  congr, dsimp [alist.forall₂] at h₁ h₂, clear nd nd₁ nd₂ determ_alist,
  induction xts with xt xts generalizing L₁ L₂; cases h₁; cases h₂, {refl},
  rcases h₁_a_1 with ⟨i, x, τ, _⟩,
  rcases h₂_a_1 with ⟨_, _, τ', _⟩,
  cases xts_ih _ _ h₁_a_2 h₂_a_2,
  cases determ ok h₁_a_1_a h₂_a_1_a_1, refl
end

end eval_ty

theorem get_fdef.weak {Γ f fd d} (h : get_fdef Γ f fd) : get_fdef (d :: Γ) f fd :=
by cases h with h f xτs τs' τ τ' body Γ h₁ h₂ h₃; exact
⟨or.inr h₁, h₂.imp (λ _ _, eval_ty.weak), h₃.imp (λ _ _, eval_ty.weak)⟩

theorem get_body.weak {Γ f τ Δ s d} (h : get_body Γ f τ Δ s) : get_body (d :: Γ) f τ Δ s :=
by cases h with h f xτs Δ τ τ' nd body Γ h₁ h₂ h₃; exact
⟨or.inr h₁, h₂.imp (λ _ _ _, eval_ty.weak), h₃.imp (λ _ _, eval_ty.weak)⟩

theorem is_fdef.weak {Γ f d} : is_fdef Γ f → is_fdef (d :: Γ) f
| ⟨τ, xτs, s, h⟩ := ⟨τ, xτs, s, h.weak⟩

theorem is_extern.weak {Γ f d} (h : is_extern Γ f) : is_extern (d :: Γ) f :=
by cases h with f xτs τ body Γ h; exact ⟨or.inr h⟩

theorem get_sdef.weak {Γ s sd d} (h : get_sdef Γ s sd) : get_sdef (d :: Γ) s sd :=
by cases h with s xτs nd Δ Γ h₁ h₂; exact
⟨or.inr h₁, h₂.imp (λ _ _ _, eval_ty.weak)⟩

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

theorem ok.weak' {Γ Δ e τ v t h} (H : exp.ok Γ Δ e τ) : exp.ok Γ (Δ.cons v t h) e τ :=
begin
  induction H,
  { exact ok.int },
  { exact ok.bool },
  { exact ok.null },
  { exact ok.var _ (alist.lookup_cons_of_lookup H_a) },
  { exact ok.binop H_ih_a H_ih_a_1 H_a_2 },
  { exact ok.unop H_ih H_a_1 },
  { exact ok.cond H_ih_a H_ih_a_1 H_ih_a_2 H_a_3 },
  { exact ok.nil },
  { exact ok.cons H_ih_a H_ih_a_1 },
  { exact ok.call H_a H_ih },
  { exact ok.field H_ih H_a_1 H_a_2 },
  { exact ok.deref H_ih H_a_1 },
  { exact ok.index H_ih_a H_ih_a_1 },
  { exact ok.alloc_ref _ H_a H_a_1 },
  { exact ok.alloc_arr H_a H_a_1 H_ih },
end

end exp

namespace stmt

theorem ok.weak {Γ ret_τ Δ s d} (h : stmt.ok Γ ret_τ Δ s) : stmt.ok (d :: Γ) ret_τ Δ s :=
begin
  induction h,
  { exact ok.decl h_h h_a.weak h_a_1 h_ih },
  { exact ok.decl_asgn h_h h_a.weak h_a_1 h_a_2.weak h_ih },
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

theorem init.subset {Γ Δ ret γ δ s δ'} (ok : stmt.ok Γ ret Δ s)
  (e : Δ.keys.to_finset = γ)
  (h : init γ δ s δ') (ss : δ ⊆ γ) : δ ⊆ δ' ∧ δ' ⊆ γ :=
begin
  have lem : ∀ {Δ : ctx} {γ δ δ' : finset ident} {v},
    list.to_finset (alist.keys Δ) = γ → v ∉ Δ →
    δ ⊆ γ → δ ⊆ δ' ∧ δ' ⊆ insert v γ → δ ⊆ δ'.erase v ∧ δ'.erase v ⊆ γ,
  { rintro Δ γ δ δ' v e hn ss ⟨ss₁, ss₂⟩,
    refine ⟨λ x xδ, finset.mem_erase.2 ⟨_, ss₁ xδ⟩,
      finset.subset.trans (finset.erase_subset_erase _ ss₂)
        (finset.erase_insert_subset _ _)⟩,
    rintro rfl, subst γ,
    cases hn (alist.mem_keys.1 $ list.mem_to_finset.1 $ ss xδ) },
  induction ok generalizing γ δ δ'; cases h; try {exact ⟨λ x, id, ss⟩},
  { refine lem e ok_h ss (ok_ih _ h_a
      (λ x xδ, finset.mem_insert_of_mem (ss xδ))),
    subst γ, simp },
  { cases ok_ih _ h_a_1 (finset.insert_subset_insert _ ss) with IH₁ IH₂,
    refine lem e ok_h ss ⟨λ x xδ, IH₁ (finset.mem_insert_of_mem xδ), IH₂⟩,
    subst γ, simp },
  { cases ok_ih_a e h_a_1 ss with l₁ r₁,
    cases ok_ih_a_1 e h_a_2 ss with l₂ r₂,
    exact ⟨λ x xδ, finset.mem_inter.2 ⟨l₁ xδ, l₂ xδ⟩,
      λ x xδ, r₁ (finset.mem_inter.1 xδ).1⟩ },
  { cases ok_lv; try {exact ⟨λ x, id, ss⟩},
    refine ⟨finset.subset_insert _ _, finset.insert_subset.2 ⟨_, ss⟩⟩,
    subst γ, cases ok_a,
    exact list.mem_to_finset.2 (alist.mem_keys.2 $
      alist.exists_mem_lookup_iff.1 ⟨_, ok_a_a⟩) },
  { exact ⟨ss, λ _, id⟩ },
  { cases ok_ih_a e h_a ss with l₁ r₁,
    cases ok_ih_a_1 e h_a_1 r₁ with l₂ r₂,
    exact ⟨finset.subset.trans l₁ l₂, r₂⟩ }
end

theorem init.mono {γ δ₁ δ₂ s δ₁'}
  (h : init γ δ₁ s δ₁') (ss : δ₁ ⊆ δ₂) :
  ∃ δ₂', δ₁' ⊆ δ₂' ∧ init γ δ₂ s δ₂' :=
begin
  have sts := @finset.subset.trans,
  induction h generalizing δ₂,
  { rcases h_ih ss with ⟨δ₂', ss', i⟩,
    exact ⟨_, finset.erase_subset_erase _ ss', init.decl i⟩ },
  { rcases h_ih (finset.insert_subset_insert _ ss) with ⟨δ₂', ss', i⟩,
    exact ⟨_, finset.erase_subset_erase _ ss',
      init.decl_asgn (sts h_a ss) i⟩ },
  { rcases h_ih_a ss with ⟨δ₃, ss₁, i₁⟩,
    rcases h_ih_a_1 ss with ⟨δ₄, ss₂, i₂⟩,
    exact ⟨_, finset.inter_subset_inter ss₁ ss₂,
      init.If (sts h_a ss) i₁ i₂⟩ },
  { rcases h_ih ss with ⟨δ', ss', i⟩,
    exact ⟨_, ss, init.while (sts h_a ss) i⟩ },
  { refine ⟨_, _, init.asgn (sts h_a ss) (sts h_a_1 ss)⟩,
    cases h_lv; try {exact ss},
    exact finset.insert_subset_insert _ ss },
  { exact ⟨_, ss, init.asnop (sts h_a ss) (sts h_a_1 ss)⟩ },
  { exact ⟨_, ss, init.eval (sts h_a ss)⟩ },
  { exact ⟨_, ss, init.assert (sts h_a ss)⟩ },
  { exact ⟨_, λ _, id, init.ret (λ e h, sts (h_a e h) ss)⟩ },
  { exact ⟨_, ss, init.nop⟩ },
  { rcases h_ih_a ss with ⟨δ₃, ss₁, i₁⟩,
    rcases h_ih_a_1 ss₁ with ⟨δ₄, ss₂, i₂⟩,
    exact ⟨_, ss₂, init.seq i₁ i₂⟩ }
end

end stmt
end ast

inductive fdecl_ok (Γ : ast) (header xτs ret body) : Prop
| mk (Δ ret' h) :
  alist.forall₂ (λ (i:ident) τ τ', eval_ty Γ τ τ' ∧ τ'.small) (alist.mk' xτs h) Δ →
  option.forall₂ (eval_ty Γ) ret ret' →
  (∀ s ∈ (body : option stmt),
    header = ff ∧
    stmt.ok Γ ret' Δ s ∧
    s.returns ∧ s.ok_init Δ) →
  fdecl_ok

theorem fdecl_ok_of_mem {Γ : ast} (ok : Γ.ok) :
  ∀ {header f xτs ret body},
  fdecl header f xτs ret body ∈ Γ →
  fdecl_ok Γ header xτs ret body :=
ast.ok_induction ok (by rintro _ _ _ _ _ ⟨⟩) $
λ d Γ g IH header f xτs ret body m, begin
  rcases m with rfl | m,
  { cases g with _ _ _ Δ _ ret' _ h₁ h₂ h₃ h₄,
    refine ⟨Δ, ret', h₁,
      h₂.imp (λ _ _ _ ⟨h₁, h₂⟩, ⟨h₁.weak, h₂⟩),
      h₃.imp (λ _ _ h, h.weak),
      λ s hs, _⟩,
    rcases h₄ s hs with ⟨hs₁, _, hs₂, hs₃, hs₄⟩,
    exact ⟨hs₁, hs₂, hs₃, hs₄⟩ },
  { cases IH m with Δ ret' h₁ h₂ h₃ h₄,
    refine ⟨Δ, ret', h₁,
      h₂.imp (λ _ _ _ ⟨h₁, h₂⟩, ⟨h₁.weak, h₂⟩),
      h₃.imp (λ _ _ h, h.weak),
      λ s hs, _⟩,
    rcases h₄ s hs with ⟨hs₁, hs₂, hs₃⟩,
    exact ⟨hs₁, hs₂.weak, hs₃⟩ }
end

theorem sdecl_ok_of_mem {Γ : ast} (ok : Γ.ok) :
  ∀ {s xτs},
  sdecl s (some xτs) ∈ Γ →
  ∃ nd Δ, alist.forall₂ (λ _, eval_ty Γ) (alist.mk' xτs nd) Δ ∧
   ∀ τ ∈ Δ.values, Γ.sized τ :=
ast.ok_induction ok (by rintro _ _ ⟨⟩) $
λ d Γ g IH s xτs m, begin
  suffices : ∃ nd Δ,
    alist.forall₂ (λ _, eval_ty Γ) (alist.mk' xτs nd) Δ ∧
    ∀ τ ∈ Δ.values, Γ.sized τ,
  { rcases this with ⟨nd, Δ, h₁, h₂⟩,
    exact ⟨nd, Δ, h₁.imp (λ _ _ _, eval_ty.weak), λ τ h, (h₂ τ h).weak⟩ },
  rcases m with rfl | m,
  { rcases g with _|_|_|⟨_, _, h, nd, H⟩, clear h, refine ⟨nd, _⟩,
    induction xτs with xτ xτs IH,
    { exact ⟨∅, list.forall₂.nil, list.forall_mem_nil _⟩ },
    cases xτ with x τ,
    cases list.nodup_cons.1 nd with nd₁ nd₂,
    rcases list.forall_mem_cons.1 H with ⟨⟨τ', h, hs⟩, H'⟩,
    rcases IH nd₂ H' with ⟨Δ, h₁, h₂⟩,
    refine ⟨Δ.cons x τ' _, list.forall₂.cons ⟨_, _, _, h⟩ h₁,
      list.forall_mem_cons.2 ⟨hs, h₂⟩⟩,
    rwa [← h₁.mem_iff, ← alist.mem_keys, alist.mk'_keys] },
  { exact IH m }
end

theorem get_sdef_ex_iff {Γ : ast} (ok : Γ.ok) {s} :
  (∃ sd, get_sdef Γ s sd) ↔ ∃ body, gdecl.sdecl s (some body) ∈ Γ :=
begin
  split,
  { rintro ⟨sd, _, xτs, _, _, _, m, h⟩, exact ⟨_, m⟩ },
  { rintro ⟨xτs, m⟩,
    rcases sdecl_ok_of_mem ok m with ⟨nd, Δ, h₁, h₂⟩,
    exact ⟨_, m, h₁⟩ }
end

instance is_sdecl (s d) : decidable (∃ body, d = gdecl.sdecl s (some body)) :=
by rcases d with _|_|⟨_, _|_⟩;
   try { apply is_false, rintro ⟨body, h⟩, cases h, done };
   { simp, apply_instance }

instance sdecl_mem (Γ : ast) (s) : decidable (∃ body, gdecl.sdecl s (some body) ∈ Γ) :=
decidable_of_iff' (∃ d ∈ Γ, ∃ body, d = gdecl.sdecl s (some body))
  ⟨by rintro ⟨x, h⟩; exact ⟨_, h, x, rfl⟩,
   by rintro ⟨_, h, x, rfl⟩; exact ⟨x, h⟩⟩

def get_sdef_dec {Γ : ast} (ok : Γ.ok) {s} : decidable (∃ sd, get_sdef Γ s sd) :=
decidable_of_iff' _ (get_sdef_ex_iff ok)

theorem get_body_ok' {Γ : ast} (ok : Γ.ok) {f τ Δ s} (h : Γ.get_body f τ Δ s) :
  stmt.ok Γ τ Δ s ∧ stmt.returns s ∧ stmt.ok_init Δ s :=
begin
  cases h,
  cases fdecl_ok_of_mem ok h_a,
  cases ast.eval_ty.determ_opt ok h_a_2 a_1,
  have : alist.forall₂ (λ _, eval_ty Γ) (alist.mk' h_xτs h_nd) Δ_1 :=
    a.imp (λ _ _ _, and.left),
  cases ast.eval_ty.determ_alist ok h_a_1 this,
  exact (a_2 _ rfl).2
end

theorem get_body_ok {Γ : ast} (ok : Γ.ok) {f τ Δ s}
  (h : Γ.get_body f τ Δ s) : stmt.ok Γ τ Δ s :=
(get_body_ok' ok h).1

theorem vars_ty.ok.mem {Δ σ} (σok : vars_ty.ok Δ σ) {x} (h : x ∈ σ) : x ∈ Δ :=
let ⟨τ, h⟩ := finmap.exists_mem_lookup_iff.2 h,
    ⟨v, t, h⟩ := σok _ _ h in alist.exists_mem_lookup_iff.1 ⟨v, t⟩

theorem vars_ty.ok.subset {Δ σ} (σok : vars_ty.ok Δ σ) : σ.keys ⊆ Δ.keys.to_finset :=
λ x h, list.mem_to_finset.2 $ alist.mem_keys.2 $ σok.mem $ finmap.mem_keys.1 h

theorem vars_ty.ok.weak {Δ σ x τ} (h) (σok : vars_ty.ok Δ σ) :
  vars_ty.ok (Δ.cons x τ h) σ :=
λ x' τ' h, let ⟨t, m, h⟩ := σok _ _ h in
  ⟨t, alist.lookup_cons_of_lookup m, h⟩

theorem vars_ty.ok.insert {Δ σ x t τ}
  (σok : vars_ty.ok Δ σ) (hn : x ∉ σ) (h₁ : t ∈ alist.lookup x Δ)
  (h₂ : vtype.of_ty (exp.type.reg t) τ) : vars_ty.ok Δ (σ.insert x τ) :=
λ x' τ' h, begin
  rcases (finmap.lookup_insert_of_neg hn).1 h with ⟨⟨⟩⟩ | h,
  exacts [⟨_, h₁, h₂⟩, σok _ _ h]
end

theorem vars_ty.ok.erase {Δ σ x t h}
  (σok : vars_ty.ok (alist.cons Δ x t h) σ) : vars_ty.ok Δ (σ.erase x) :=
λ x' τ' h, begin
  rcases finmap.lookup_erase.1 h with ⟨ne, h⟩,
  rcases σok _ _ h with ⟨t', m, tτ'⟩,
  rcases alist.mem_lookup_iff.1 m with ⟨⟨⟩⟩ | m, {cases ne rfl},
  exact ⟨t', alist.mem_lookup_iff.2 m, tτ'⟩
end

theorem vars.ok.mem {Γ E σ η} (ηok : vars.ok Γ E η σ) {x} (h : x ∈ σ) : x ∈ η :=
let ⟨τ, h⟩ := finmap.exists_mem_lookup_iff.2 h,
    ⟨v, t, h⟩ := ηok _ _ h in finmap.exists_mem_lookup_iff.1 ⟨v, t⟩

theorem vars.ok.ok_of_mem {Γ E σ η} (ηok : vars.ok Γ E η σ)
  {x τ} (h₁ : τ ∈ σ.lookup x) {v} (h₂ : v ∈ η.lookup x) : value.ok Γ E v τ :=
let ⟨v', m, h⟩ := ηok _ _ h₁ in option.mem_unique m h₂ ▸ h

theorem vars.ok.insert {Γ E σ η x v τ} (ηok : vars.ok Γ E η σ)
  (hn : x ∉ η) (vok : value.ok Γ E v τ) :
  vars.ok Γ E (η.insert x v) (σ.insert x τ) :=
λ x' τ' h, begin
  rcases (finmap.lookup_insert_of_neg (mt ηok.mem hn)).1 h with ⟨⟨⟩⟩ | h,
  { exact ⟨_, finmap.lookup_insert_self hn, vok⟩ },
  { rcases ηok _ _ h with ⟨v, vη, h⟩,
    exact ⟨v, (finmap.lookup_insert_of_neg hn).2 (or.inr vη), h⟩ }
end

theorem vars.ok.erase {Γ E σ η x}
  (ηok : vars.ok Γ E η σ) : vars.ok Γ E η (σ.erase x) :=
λ x' τ' h, ηok _ _ (finmap.lookup_erase.1 h).2

theorem env.ok.empty {Γ} : env.ok Γ ∅ ∅ vtype.int :=
⟨by rintro _ _ ⟨⟩, list.forall₂.nil, by rintro _ _ ⟨⟩, stack.ok.nil⟩

theorem start_ok (Γ : ast) (ok : Γ.ok) : ∀ s, start Γ s → state.ok Γ s
| _ (@start.mk _ s h) := let ⟨h₁, h₂, _, h₃⟩ := get_body_ok' ok h in
  state.ok.stmt (some type.int) env.ok.empty vtype.of_ty.int h₁ h₃ (or.inl h₂)

namespace value

theorem is_nth.ok {Γ E i n v v' τ}
  (vok : ok Γ E v (vtype.arr' τ n)) (lt : i < n)
  (h : is_nth i v v') : ok Γ E v' τ :=
begin
  induction h generalizing n,
  { cases n, {cases lt},
    cases vok, exact vok_a },
  { cases n, {cases lt},
    cases vok, exact h_ih vok_a_1 (nat.lt_of_succ_lt_succ lt) }
end

end value

namespace vtype

open ast.exp.type
def of_ty_fn : ∀ τ, {vτ // of_ty τ vτ}
| void := ⟨_, of_ty.void⟩
| (reg type.int) := ⟨_, of_ty.int⟩
| (reg type.bool) := ⟨_, of_ty.bool⟩
| (reg (type.ref τ)) := let ⟨τ, h⟩ := of_ty_fn (reg τ) in ⟨_, of_ty.ref h⟩
| (reg (type.arr τ)) := let ⟨τ, h⟩ := of_ty_fn (reg τ) in ⟨_, of_ty.arr h⟩
| (reg (type.struct s)) := ⟨_, of_ty.struct⟩
| (ls []) := ⟨_, of_ty.nil⟩
| (ls (τ :: τs)) :=
  let ⟨τ', h₁⟩ := of_ty_fn (reg τ),
      ⟨τs', h₂⟩ := of_ty_fn (ls τs) in
  ⟨_, of_ty.cons h₁ h₂⟩

end vtype

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

theorem assign.ok {Γ E Δ H σ η}
  (σok : vars_ty.ok Δ σ) (Hok : heap.ok Γ H E) (ηok : vars.ok Γ E η σ)
  {v a τ} (aok : addr.ok Γ E σ a τ) (vok : value.ok Γ E v τ)
  {H' η'} (h : assign H η v a H' η') :
  ∃ σ', vars_ty.ok Δ σ' ∧ heap.ok Γ H' E ∧ vars.ok Γ E η' σ' :=
begin
  rcases h with ⟨a, H', η', h⟩ | ⟨x, hn⟩,
  { refine ⟨σ, σok, update.ok σok Hok ηok aok h _⟩,
    rintro x xok _ rfl, exact vok },
  { cases aok, rcases σok _ _ aok_a with ⟨t, tΔ, tτ⟩,
    exact ⟨σ.insert x τ, σok.insert (mt ηok.mem hn) tΔ tτ,
      Hok, ηok.insert hn vok⟩ }
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
    cases IH aok, exact a_1 _ _ _ _ _ hsd m tτ hf }
end

end addr

theorem stmt_list.ok.eq_none {Γ Δ δ ret}
  (Kok : stmt_list.ok Γ ret Δ δ []) : ret = none :=
begin
  generalize e : ([]:list stmt) = ss, rw e at Kok,
  induction Kok; cases e; [exact Kok_a, exact Kok_ih rfl]
end

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

theorem stmt_list.ok'.weak {Γ} {σ : vars_ty} {ret Δ K x τ h}
  (Kok : stmt_list.ok' Γ (σ.erase x) ret Δ K) :
  stmt_list.ok' Γ σ ret (Δ.cons x τ h) K :=
stmt_list.ok.weak (by simpa [stmt_list.ok'] using Kok)

theorem stmt_list.ok.cons_inv {Γ E Δ σ η ret s K}
  (σok : vars_ty.ok Δ σ)
  (ηok : vars.ok Γ E η σ) : stmt_list.ok' Γ σ ret Δ (s :: K) →
  ∃ Δ' σ', vars_ty.ok Δ' σ' ∧ vars.ok Γ E η σ' ∧
    stmt.ok Γ ret Δ' s ∧ (stmt.returns s ∨ stmt_list.ok' Γ σ' ret Δ' K) :=
suffices ∀ {δ K'} (e : (s :: K : list stmt) = K') (ss : δ ⊆ σ.keys)
  (Kok : stmt_list.ok Γ ret Δ δ K'),
  ∃ Δ' σ', vars_ty.ok Δ' σ' ∧ vars.ok Γ E η σ' ∧
    stmt.ok Γ ret Δ' s ∧ (stmt.returns s ∨ stmt_list.ok Γ ret Δ' σ.keys K),
from this rfl (λ _, id),
begin
  intros, induction Kok generalizing σ; cases e,
  { exact ⟨_, _, σok, ηok, Kok_a, or.inl Kok_a_1⟩ },
  { rcases Kok_a_1.subset Kok_a rfl
      (finset.subset.trans ss σok.subset) with ⟨ss₁', ss₂'⟩,
    refine ⟨_, _, σok, ηok, Kok_a, or.inr (Kok_a_2.mono _)⟩,
     },
  { refine Kok_ih (finset.subset.trans
      (finset.erase_subset_erase _ (by simpa using ss₂))
      (finset.erase_insert_subset _ _)) rfl σok.erase ηok.erase _,
    simpa using finset.erase_subset_erase _ ss₁ }
end

theorem step_deref.ok {Γ E σs Δ σ H S η ret a τ K s'}
  (Cok : env.ok Γ ⟨E, σs, σ, Δ⟩ ⟨H, S, η⟩ ret)
  (aok : addr_opt.ok Γ E σ a τ)
  (Kok : cont.ok Γ E σ Δ ret K τ)
  (h : step_deref ⟨H, S, η⟩ a K s') : state.ok Γ s' :=
begin
  cases h,
  { apply state.ok.err },
  { cases Cok with E σs σ H S η Δ _ σok Eok ηok Sok,
    exact state.ok.ret ⟨σok, Eok, ηok, Sok⟩
      (h_a_1.ok σok Eok ηok aok) Kok }
end

theorem step_ret.ok {Γ E σs Δ σ H S η τ v s'}
  (Cok : env.ok Γ ⟨E, σs, σ, Δ⟩ ⟨H, S, η⟩ τ)
  (vok : value.ok Γ E v τ)
  (h : step_ret ⟨H, S, η⟩ v s') : state.ok Γ s' :=
begin
  cases Cok with E σs σ H S η Δ _ σok Eok ηok Sok,
  cases h,
  { cases Sok with Δ' η K' S' σ σs τ₁ τ' σok' ηok' Kok' Sok',
    exact state.ok.ret ⟨σok', Eok, ηok', Sok'⟩ vok Kok' },
  { apply state.ok.done }
end

theorem preservation {Γ : ast} (ok : Γ.ok)
  {s} (sok : state.ok Γ s) {o} (iok : io.ok Γ o)
  {s'} (H : step Γ s o s') : state.ok Γ s' :=
begin
  cases H,
  /-
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
  -/
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
    refine state.ok.exp ⟨σok, Eok, ηok, Sok⟩ si_a
      ⟨_, sok_a_1, vtype.of_ty.bool⟩
      (cont.ok.If tτ sok_a_2 si_a_1 sok_a_3 si_a_2 _),
    rcases Kok with ⟨⟨⟩⟩|Kok,
    { exact or.inl ⟨Kok_a, Kok_a_1⟩ },
    { exact or.inr Kok } },
  case c0.step.If₂ : C b s₁ s₂ K {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      _, _, _, δ₁, δ₂, _, t, tτ, s₁ok, i₁, s₂ok, i₂, Kok⟩,
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
    exact (state.ok.exp ⟨σok, Eok, ηok, Sok⟩ si_a ⟨_, a, vtype.of_ty.bool⟩ $
      cont.ok.If tτ (a_1.seq sok) (si_a_1.seq i') stmt.ok.nop stmt.init.nop $
      or.inr $ Kok.mono $ finset.subset_inter ss' (finset.subset.refl _)) },
  case c0.step.asgn₁ : C lv e K {
    rcases sok with ⟨_, _, _, _, _, τ, _, _, _, t,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      tτ, sok, si, ⟨⟨⟩⟩|Kok⟩, cases si, cases sok,
    rcases vtype.of_ty_fn sok_τ with ⟨vτ, hv⟩,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ _ ⟨_, sok_a_1, hv⟩
      (cont.ok.asgn₁ _ _ ⟨_, sok_a_2, hv⟩ ⟨t, tτ, Kok⟩) },
  case c0.step.asgn₂ : C a e K {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      aok, _|⟨_, _, _, ⟨t, eok, tτ⟩, Kok⟩⟩,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ ⟨_, eok, tτ⟩
      (cont.ok.asgn₂ aok Kok) },
  case c0.step.asgn₃ : H H' S η η' a v K h {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      vok, _|_|⟨_, _, _, aok, t, tτ, Kok⟩⟩,
    rcases h.ok σok Eok ηok aok vok with ⟨σ', σok', Eok', ηok'⟩,
    exact state.ok.stmt t ⟨σok', Eok', ηok', Sok⟩ tτ stmt.ok.nop (or.inr Kok) },
  case c0.step.asgn_err : H S η v K { apply state.ok.err },
  case c0.step.asnop₁ : C lv op e K {
    rcases sok with ⟨_, _, _, _, _, τ, _, _, _, t,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      tτ, sok, ⟨⟨⟩⟩|Kok⟩, cases id sok,
    rcases vtype.of_ty_fn (exp.type.reg τ_1) with ⟨vτ, hv⟩,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ ⟨_, a, hv⟩
      (cont.ok.asnop _ _ a_2 hv a_1 ⟨t, tτ, Kok⟩) },
  case c0.step.asnop₂ : C a op e K h {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      aok, Kok⟩, cases Kok, cases Kok_a, cases Kok_a_1,
    exact step_deref.ok ⟨σok, Eok, ηok, Sok⟩ aok
      (cont.ok.binop₁ Kok_a_a Kok_a_1 Kok_a_1 Kok_a_2 $
       cont.ok.asgn₂ aok Kok_a_3) h },
  case c0.step.eval₁ : C e K {
    rcases sok with ⟨_, _, _, _, _, τ, _, _, _, t,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      tτ, sok, ⟨⟨⟩⟩|Kok⟩, cases id sok,
    rcases vtype.of_ty_fn τ_1 with ⟨vτ, hv⟩,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ ⟨_, a, hv⟩
      (cont.ok.eval _ _ ⟨t, tτ, Kok⟩) },
  case c0.step.eval₂ : C e K {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      aok, Kok⟩,
    cases Kok, rcases Kok_a with ⟨t, tτ, Kok⟩,
    exact state.ok.stmt t ⟨σok, Eok, ηok, Sok⟩ tτ stmt.ok.nop (or.inr Kok) },
  case c0.step.assert₁ : C e K {
    rcases sok with ⟨_, _, _, _, _, τ, _, _, _, t,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      tτ, sok, ⟨⟨⟩⟩|Kok⟩, cases id sok,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ ⟨_, a, vtype.of_ty.bool⟩
      (cont.ok.assert _ _ ⟨t, tτ, Kok⟩) },
  case c0.step.assert₂ : C b K {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      aok, Kok⟩,
    cases b, {apply state.ok.err},
    cases Kok, rcases Kok_a with ⟨t, tτ, Kok⟩,
    exact state.ok.stmt t ⟨σok, Eok, ηok, Sok⟩ tτ stmt.ok.nop (or.inr Kok) },
  case c0.step.ret₁ : C e K {
    rcases sok with ⟨_, _, _, _, _, τ, _, _, _, t,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      tτ, sok, si, Kok⟩, cases id sok, cases a,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ ⟨_, a_a_1, tτ⟩ cont.ok.ret },
  case c0.step.ret₂ : C v h {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      vok, ⟨⟩⟩,
    exact step_ret.ok ⟨σok, Eok, ηok, Sok⟩ vok h },
  case c0.step.ret_none : C v h {
    rcases sok with ⟨_, _, _, _, _, τ, _, _, _, t,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      tτ, sok, si, Kok⟩, cases id sok, cases a, cases tτ,
    exact step_ret.ok ⟨σok, Eok, ηok, Sok⟩ value.ok.nil h },
  -- },
  case c0.step.nop₁ : C h {
    rcases sok with ⟨_, _, _, _, _, τ, _, _, _, t,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      tτ, _, ⟨⟨⟩⟩|Kok⟩, cases Kok.eq_none, cases tτ,
    exact step_ret.ok ⟨σok, Eok, ηok, Sok⟩ value.ok.nil h },
  case c0.step.nop₂ : C s K {
    rcases sok with ⟨_, _, _, _, _, τ, _, _, _, t,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      tτ, _, ⟨⟨⟩⟩|Kok⟩,
    rcases Kok.cons_inv σok ηok with ⟨Δ', σ', σok', ηok', sok, Kok⟩,
    exact state.ok.stmt t ⟨σok', Eok, ηok', Sok⟩ tτ sok Kok },
  case c0.step.seq : C s₁ s₂ K {
    rcases sok with ⟨_, _, _, _, _, τ, _, _, _, t,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      tτ, sok, ⟨⟨⟩⟩|Kok⟩; cases id sok,
    { exact state.ok.stmt t ⟨σok, Eok, ηok, Sok⟩ tτ a (or.inl sok_a_1_a) },
    { exact state.ok.stmt t ⟨σok, Eok, ηok, Sok⟩ tτ a
        (or.inr $ stmt_list.ok.one a_1 sok_a_1_a) },
    { exact state.ok.stmt t ⟨σok, Eok, ηok, Sok⟩ tτ a (or.inr $ Kok.cons a_1) } },
  case c0.step.int : C n K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      ⟨t, ⟨⟩, tτ⟩, Kok⟩, cases tτ,
    exact state.ok.ret ⟨σok, Eok, ηok, Sok⟩ value.ok.int Kok },
  case c0.step.bool : C b K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      ⟨t, ⟨⟩, tτ⟩, Kok⟩, cases tτ,
    exact state.ok.ret ⟨σok, Eok, ηok, Sok⟩ value.ok.bool Kok },
  case c0.step.null : C K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      ⟨t, ⟨⟩, tτ⟩, Kok⟩, cases tτ,
    exact state.ok.ret ⟨σok, Eok, ηok, Sok⟩ value.ok.null Kok },
  case c0.step.var : C i v K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      ⟨_, _|_|_|⟨_, t, m⟩, tτ⟩, Kok⟩,
    exact state.ok.ret ⟨σok, Eok, ηok, Sok⟩ _ Kok },
end

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
