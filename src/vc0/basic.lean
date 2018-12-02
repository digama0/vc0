import c0.dyn_ok

namespace c0

open ast ast.gdecl

namespace ast

inductive okind : ast → Prop
| nil : okind []
| cons {d Γ} : gdecl.ok Γ d → okind Γ → okind (d :: Γ)

theorem ok.ind {Γ : ast} (h : Γ.ok) : Γ.okind :=
begin
  rw ← Γ.reverse_reverse,
  suffices : ∀ Γ ds, ok' Γ ds → okind Γ → okind (list.reverse_core ds Γ),
  from this [] Γ.reverse h.gdecls okind.nil,
  clear h Γ, introv h₁ h₂,
  induction h₁, {exact h₂},
  exact h₁_ih (okind.cons h₁_a h₂)
end

inductive below (P : ast → Prop) : ast → Prop
| nil {} : below []
| cons (d Γ) : gdecl.ok Γ d → P Γ → below (d :: Γ)

@[elab_as_eliminator]
theorem okind.induction' {P : ast → Prop} {Γ : ast} (h : Γ.okind)
  (H : ∀ Γ, okind Γ → below P Γ → P Γ) : P Γ :=
okind.rec_on h (H [] okind.nil below.nil)
  (λ d Γ h₁ ok h₂, H _ (okind.cons h₁ ok) (below.cons d Γ h₁ h₂))

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

theorem var_determ {Γ : ast} (ok : Γ.okind) : ∀ {v τ₁ τ₂},
  typedef v τ₁ ∈ Γ → typedef v τ₂ ∈ Γ → τ₁ = τ₂ :=
begin
  induction ok with d Γ h _ IH, {rintro _ _ _ ⟨⟩},
  rintro v τ₁ τ₂ (rfl | h₁) (⟨⟨⟩⟩ | h₂),
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

theorem determ {Γ : ast} (ok : Γ.okind) : ∀ {t τ₁ τ₂}
  (h₁ : eval_ty Γ t τ₁) (h₂ : eval_ty Γ t τ₂), τ₁ = τ₂ :=
okind.induction' ok $ λ Γ ok IH t, begin
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
    cases var_determ ok m₁ m₂,
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

theorem determ_opt {Γ : ast} (ok : Γ.okind) {t τ₁ τ₂}
  (h₁ : option.forall₂ (eval_ty Γ) t τ₁)
  (h₂ : option.forall₂ (eval_ty Γ) t τ₂) : τ₁ = τ₂ :=
begin
  cases h₁; cases h₂, {refl},
  cases determ ok h₁_a_1 h₂_a_1, refl
end

theorem determ_alist {α} {Γ : ast} (ok : Γ.okind) : ∀ {xts Δ₁ Δ₂}
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

theorem get_body.get_fdef {Γ : ast} {f τ Δ s}
  (h : Γ.get_body f τ Δ s) : Γ.get_fdef f ⟨Δ.values, τ⟩ :=
begin
  cases h with h xτs ts _ t _ nd _ _ m tsΔ tτ,
  refine ⟨m, _, tτ⟩,
  cases Δ with Δ nd',
  refine list.forall₂_map_right_iff.2 ((list.forall₂_map_left_iff.1 tsΔ).imp _),
  rintro ⟨i, t⟩ ⟨_, τ⟩ ⟨_, _, _, h⟩, exact h
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
    (s.returns ∨ ret = none) ∧
    s.ok_init Δ) →
  fdecl_ok

theorem fdecl_ok_of_mem {Γ : ast} (ok : Γ.okind)
  {header f xτs ret body} :
  fdecl header f xτs ret body ∈ Γ →
  fdecl_ok Γ header xτs ret body :=
begin
  induction ok with d Γ g ok IH; rintro (rfl | m),
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

theorem sdecl_ok_of_mem {Γ : ast} (ok : Γ.okind) {s xτs} :
  sdecl s (some xτs) ∈ Γ →
  ∃ nd Δ, alist.forall₂ (λ _, eval_ty Γ) (alist.mk' xτs nd) Δ ∧
   ∀ τ ∈ Δ.values, Γ.sized τ :=
begin
  induction ok with d Γ g ok IH; intro m, {cases m},
  suffices : ∃ nd Δ,
    alist.forall₂ (λ _, eval_ty Γ) (alist.mk' xτs nd) Δ ∧
    ∀ τ ∈ Δ.values, Γ.sized τ,
  { rcases this with ⟨nd, Δ, h₁, h₂⟩,
    exact ⟨nd, Δ, h₁.imp (λ _ _ _, eval_ty.weak), λ τ h, (h₂ τ h).weak⟩ },
  rcases m with rfl | m,
  { rcases g with _|_|_|⟨_, _, h, nd, H⟩, clear h IH, refine ⟨nd, _⟩,
    induction xτs with xτ xτs IH,
    { exact ⟨∅, list.forall₂.nil, list.forall_mem_nil _⟩ },
    cases xτ with x τ,
    cases list.nodup_cons.1 nd with nd₁ nd₂,
    rcases list.forall_mem_cons.1 H with ⟨⟨τ', h, hs⟩, H'⟩,
    rcases IH nd₂ H' with ⟨Δ, h₁, h₂⟩,
    refine ⟨Δ.cons x τ' _, list.forall₂.cons ⟨h⟩ h₁,
      list.forall_mem_cons.2 ⟨hs, h₂⟩⟩,
    rwa [← h₁.mem_iff, ← alist.mem_keys, alist.mk'_keys] },
  { exact IH m }
end

theorem get_sdef_ex_iff {Γ : ast} (ok : Γ.okind) {s} :
  (∃ sd, get_sdef Γ s sd) ↔ ∃ body, gdecl.sdecl s (some body) ∈ Γ :=
begin
  split,
  { rintro ⟨sd, _, xτs, _, _, _, m, h⟩, exact ⟨_, m⟩ },
  { rintro ⟨xτs, m⟩,
    rcases sdecl_ok_of_mem ok m with ⟨nd, Δ, h₁, h₂⟩,
    exact ⟨_, m, h₁⟩ }
end

theorem get_sdef_pairwise {Γ : ast} (ok : Γ.okind) {s} :
  Γ.pairwise (λ d₁ d₂, ∀ xτs₁ xτs₂,
    d₁ = sdecl s (some xτs₁) → d₂ = sdecl s (some xτs₂) → false) :=
begin
  induction ok with d Γ g ok IH; constructor,
  { rintro _ h xτs₁ xτs₂ rfl rfl,
    rcases (get_sdef_ex_iff ok).2 ⟨_, h⟩ with ⟨sd, h'⟩,
    cases g, cases g_a _ h' },
  { exact IH }
end

theorem get_sdef_determ {Γ : ast} (ok : Γ.okind) {s sd₁ sd₂}
  (h₁ : get_sdef Γ s sd₁) (h₂ : get_sdef Γ s sd₂) : sd₁ = sd₂ :=
begin
  have : ∀ (d₁ ∈ Γ) (d₂ ∈ Γ) xτs₁ xτs₂,
    d₁ = sdecl s (some xτs₁) → d₂ = sdecl s (some xτs₂) → xτs₁ = xτs₂,
  { refine list.forall_of_forall_of_pairwise _ _ ((get_sdef_pairwise ok).imp _),
    { exact λ x y H xτs₁ xτs₂ h₁ h₂, (H _ _ h₂ h₁).symm },
    { rintro _ _ _ _ rfl ⟨⟩, refl }, swap,
    { rintro a b H _ _ h₁ h₂, cases H _ _ h₁ h₂ } },
  cases h₁, cases h₂,
  cases this _ h₁_a _ h₂_a _ _ rfl rfl,
  exact ast.eval_ty.determ_alist ok h₁_a_1 h₂_a_1
end

instance is_sdecl (s d) : decidable (∃ body, d = gdecl.sdecl s (some body)) :=
by rcases d with _|_|⟨_, _|_⟩;
   try { apply is_false, rintro ⟨body, h⟩, cases h, done };
   { simp, apply_instance }

instance sdecl_mem (Γ : ast) (s) : decidable (∃ body, gdecl.sdecl s (some body) ∈ Γ) :=
decidable_of_iff' (∃ d ∈ Γ, ∃ body, d = gdecl.sdecl s (some body))
  ⟨by rintro ⟨x, h⟩; exact ⟨_, h, x, rfl⟩,
   by rintro ⟨_, h, x, rfl⟩; exact ⟨x, h⟩⟩

def get_sdef_dec {Γ : ast} (ok : Γ.okind) {s} : decidable (∃ sd, get_sdef Γ s sd) :=
decidable_of_iff' _ (get_sdef_ex_iff ok)

theorem get_body_ok' {Γ : ast} (ok : Γ.okind) {f τ Δ s} (h : Γ.get_body f τ Δ s) :
  stmt.ok Γ τ Δ s ∧ (stmt.returns s ∨ τ = none) ∧ stmt.ok_init Δ s :=
begin
  cases h,
  cases fdecl_ok_of_mem ok h_a,
  cases ast.eval_ty.determ_opt ok h_a_2 a_1,
  have : alist.forall₂ (λ _, eval_ty Γ) (alist.mk' h_xτs h_nd) Δ_1 :=
    a.imp (λ _ _ _, and.left),
  cases ast.eval_ty.determ_alist ok h_a_1 this,
  refine (a_2 _ rfl).2.imp_right (and.imp_left (or.imp_right _)),
  rintro rfl, cases a_1, refl
end

theorem get_body_ok {Γ : ast} (ok : Γ.okind) {f τ Δ s}
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

theorem vars_ty.ok.ok_of_mem {Δ σ x t τ}
  (σok : vars_ty.ok Δ σ) (h₁ : τ ∈ σ.lookup x) (h₂ : t ∈ Δ.lookup x) : vtype.of_ty (exp.type.reg t) τ :=
let ⟨v', m, h⟩ := σok _ _ h₁ in option.mem_unique m h₂ ▸ h

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

theorem heap_le_nth {E E' : heap_ty} (EE : E ≤ E')
  {i τ} (h : τ ∈ E.nth i) : τ ∈ E'.nth i :=
begin
  rcases EE with ⟨l, rfl⟩,
  induction E with τ' E IH generalizing i, {cases h},
  cases i; [{cases h, exact rfl}, exact IH h]
end

theorem value.ok.mono {Γ E E' v τ} (EE : E ≤ E')
  (h : value.ok Γ E v τ) : value.ok Γ E' v τ :=
begin
  induction h; constructor; try {assumption},
  exact heap_le_nth EE h_a
end

theorem vars.ok.mono {Γ E E' σ η} (EE : E ≤ E')
  (ηok : vars.ok Γ E η σ) : vars.ok Γ E' η σ :=
λ i τ h, let ⟨t, h₁, h₂⟩ := ηok i τ h in ⟨t, h₁, h₂.mono EE⟩

theorem addr.ok.mono {Γ E E' σ a τ} (EE : E ≤ E')
 (aok : addr.ok Γ E σ a τ) : addr.ok Γ E' σ a τ :=
begin
  induction aok; constructor; try {assumption},
  exact heap_le_nth EE aok_a
end

theorem addr_opt.ok.mono {Γ E E' σ} (EE : E ≤ E') :
  ∀ {a τ}, addr_opt.ok Γ E σ a τ → addr_opt.ok Γ E' σ a τ
| none     τ h := trivial
| (some a) τ h := addr.ok.mono EE h

theorem cont.ok.mono {Γ E E' σ Δ ret δ α τ K} (EE : E ≤ E')
  (Kok : @cont.ok Γ E σ Δ ret δ α τ K) : cont.ok Γ E' σ Δ ret δ τ K :=
by induction Kok; constructor; {
  assumption <|>
  exact addr_opt.ok.mono EE (by assumption) <|>
  exact value.ok.mono EE (by assumption) }

theorem stack.ok.mono {Γ E E' σs S ret} (EE : E ≤ E')
  (Sok : stack.ok Γ E σs S ret) : stack.ok Γ E' σs S ret :=
by induction Sok; constructor; {
  assumption <|>
  exact vars.ok.mono EE (by assumption) <|>
  exact cont.ok.mono EE (by assumption) }

theorem heap_ty.le_add (E : heap_ty) (τ) : E ≤ E.add τ := ⟨_, rfl⟩

theorem heap.ok.add {Γ E H v τ}
  (Eok : heap.ok Γ H E) (vok : value.ok Γ (E.add τ) v τ) :
  heap.ok Γ (H ++ [v]) (E.add τ) :=
list.forall₂_concat.2 ⟨Eok.imp (λ _ _, value.ok.mono (E.le_add _)), vok⟩

theorem env.ok.empty {Γ} : env.ok Γ ∅ ∅ vtype.int :=
⟨by rintro _ _ ⟨⟩, list.forall₂.nil, by rintro _ _ ⟨⟩, stack.ok.nil⟩

namespace vtype

open ast.exp.type
def of_ty_fn : ∀ τ, {vτ // of_ty τ vτ}
| void := ⟨_, of_ty.void⟩
| (reg type.int) := ⟨_, of_ty.int⟩
| (reg type.bool) := ⟨_, of_ty.bool⟩
| (reg (type.ref τ)) := let f := of_ty_fn (reg τ) in ⟨_, of_ty.ref f.2⟩
| (reg (type.arr τ)) := let f := of_ty_fn (reg τ) in ⟨_, of_ty.arr f.2⟩
| (reg (type.struct s)) := ⟨_, of_ty.struct⟩
| (ls []) := ⟨_, of_ty.nil⟩
| (ls (τ :: τs)) :=
  let f₁ := of_ty_fn (reg τ),
      f₂ := of_ty_fn (ls τs) in
  ⟨_, of_ty.cons f₁.2 f₂.2⟩

theorem of_ty_eq : ∀ {τ vτ}, of_ty τ vτ → vτ = (of_ty_fn τ).1
| void                  vτ h := by cases h; refl
| (reg type.int)        vτ h := by cases h; refl
| (reg type.bool)       vτ h := by cases h; refl
| (reg (type.ref τ))    vτ h := by cases h; rw [of_ty_eq h_a, of_ty_fn]
| (reg (type.arr τ))    vτ h := by cases h; rw [of_ty_eq h_a, of_ty_fn]
| (reg (type.struct s)) vτ h := by cases h; refl
| (ls [])               vτ h := by cases h; refl
| (ls (τ :: τs))        vτ h := by cases h; rw [of_ty_eq h_a, of_ty_eq h_a_1, of_ty_fn]

theorem of_ty_determ {τ vτ₁ vτ₂} (h₁ : of_ty τ vτ₁) (h₂ : of_ty τ vτ₂) : vτ₁ = vτ₂ :=
(of_ty_eq h₁).trans (of_ty_eq h₂).symm

end vtype

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

def ok_type_or_sdef (Γ E) (v : value) : type ⊕ sdef → Prop
| (sum.inl τ) := ∃ τ', vtype.of_ty (exp.type.reg τ) τ' ∧ value.ok Γ E v τ'
| (sum.inr sd) := ∃ vs, to_map v vs ∧
  alist.forall₂ (λ _ _ _, true) sd vs ∧
  ∀ ⦃x τ v'⦄, is_field x v v' →
    τ ∈ sd.lookup x →
    ∃ vτ, vtype.of_ty (exp.type.reg τ) vτ ∧ value.ok Γ E v' vτ

theorem is_field_lookup {x v vs v'} (h : to_map v vs) :
  is_field x v v' ↔ v' ∈ vs.lookup x :=
begin
  split; intro H,
  { induction H generalizing vs; cases h,
    { exact alist.lookup_cons_self },
    { exact alist.lookup_cons_of_lookup (H_ih h_a) } },
  { induction h generalizing v', {cases H},
    rcases alist.mem_lookup_iff.1 H with ⟨⟨⟩⟩ | m,
    { constructor },
    { exact is_field.cons (h_ih $ alist.mem_lookup_iff.2 m) } }
end

end value

namespace addr

theorem ok.ref_opt {Γ E σ n τ}
  (h : value.ok Γ E (value.ref n) (vtype.ref τ)) :
  addr_opt.ok Γ E σ (addr.ref <$> n) τ :=
by cases h; [trivial, exact addr.ok.ref h_a]

end addr

end c0
