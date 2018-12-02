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

theorem start_ok (Γ : ast) (ok : Γ.ok) : ∀ s, start Γ s → state.ok Γ s
| _ (@start.mk _ s h) :=
  by rcases get_body_ok' ok.ind h with ⟨h₁, h₂|⟨⟨⟩⟩, _, h₃⟩; exact
  state.ok.stmt (some type.int) env.ok.empty vtype.of_ty.int h₁ h₃ (or.inl h₂)

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

theorem ok.ref_opt {Γ E σ n τ}
  (h : value.ok Γ E (value.ref n) (vtype.ref τ)) :
  addr_opt.ok Γ E σ (addr.ref <$> n) τ :=
by cases h; [trivial, exact addr.ok.ref h_a]

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
    refine state.ok.exp ⟨σok, Eok, ηok, Sok⟩ si_a
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
    exact (state.ok.exp ⟨σok, Eok, ηok, Sok⟩ si_a ⟨_, a, vtype.of_ty.bool⟩ $
      cont.ok.If tτ (a_1.seq sok) (si_a_1.seq i') stmt.ok.nop stmt.init.nop $
      or.inr $ Kok.mono $ finset.subset_inter ss' (finset.subset.refl _)) },
  case c0.step.asgn₁ : C lv e K eq {
    rcases sok with ⟨_, _, _, _, _, τ, _, _, _, t,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      tτ, sok, si, ⟨⟨⟩⟩|Kok⟩, cases si, cases sok,
    rcases vtype.of_ty_fn sok_τ with ⟨vτ, hv⟩,
    rw [lval.use, eq] at si_a, rw eq at Kok,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ si_a ⟨_, sok_a_1, hv⟩
      (cont.ok.asgn₁ _ _ ⟨_, sok_a_2, hv⟩ si_a_1 ⟨t, tτ, Kok⟩) },
  case c0.step.asgn₂ : C a e K {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      aok, _|⟨_, _, _, _, ⟨t, eok, tτ⟩, eu, t', tτ', Kok⟩⟩,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ eu ⟨_, eok, tτ⟩
      (cont.ok.asgn₂ aok ⟨_, tτ', Kok⟩) },
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
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ si_a_1 ⟨_, sok_a_2, hv⟩
      (cont.ok.asgn_var tΔ hv ⟨_, tτ, Kok⟩) },
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
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ si_a ⟨_, a, hv⟩
      (cont.ok.asnop a_2 hv a_1 si_a_1 ⟨_, tτ, Kok⟩) },
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
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ si_a ⟨_, a, hv⟩
      (cont.ok.eval _ _ ⟨t, tτ, Kok⟩) },
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
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ si_a ⟨_, a, vtype.of_ty.bool⟩
      (cont.ok.assert _ _ ⟨t, tτ, Kok⟩) },
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
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ (si_a _ rfl)
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
      eu, ⟨t, ⟨⟩, tτ⟩, Kok⟩, cases tτ,
    exact state.ok.ret ⟨σok, Eok, ηok, Sok⟩ value.ok.int Kok },
  case c0.step.bool : C b K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, ⟨t, ⟨⟩, tτ⟩, Kok⟩, cases tτ,
    exact state.ok.ret ⟨σok, Eok, ηok, Sok⟩ value.ok.bool Kok },
  case c0.step.null : C K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, ⟨t, ⟨⟩, tτ⟩, Kok⟩, cases tτ,
    exact state.ok.ret ⟨σok, Eok, ηok, Sok⟩ value.ok.null Kok },
  case c0.step.var : C i v K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, ⟨_, _|_|_|⟨_, t, iΔ⟩, tτ⟩, Kok⟩,
    rcases finmap.exists_mem_lookup_iff.2
      (finmap.mem_keys.1 $ finset.singleton_subset.1 eu) with ⟨τ', iτ'⟩,
    cases vtype.of_ty_determ tτ (σok.ok_of_mem iτ' iΔ),
    exact state.ok.ret ⟨σok, Eok, ηok, Sok⟩ (ηok.ok_of_mem iτ' H_a) Kok },
  case c0.step.binop₁ : C op e₁ e₂ K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, ⟨t, eok, tτ⟩, Kok⟩, cases eok,
    have eu₁ := finset.subset.trans (finset.subset_union_left _ _) eu,
    have eu₂ := finset.subset.trans (finset.subset_union_right _ _) eu,
    rcases vtype.of_ty_fn (exp.type.reg eok_τ₁) with ⟨vτ₁, hv₁⟩,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ eu₁ ⟨_, eok_a, hv₁⟩
      (cont.ok.binop₁ eok_a_2 hv₁ tτ eok_a_1 eu₂ Kok) },
  case c0.step.binop₂ : C op v₁ e₂ K {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      vok, Kok⟩, cases Kok,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ Kok_a_4 ⟨_, Kok_a_3, Kok_a_1⟩
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
      eu, ⟨t, eok, tτ⟩, Kok⟩, cases eok,
    rcases vtype.of_ty_fn (exp.type.reg eok_τ₁) with ⟨vτ₁, hv₁⟩,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ eu ⟨_, eok_a, hv₁⟩
      (cont.ok.unop eok_a_1 hv₁ tτ Kok) },
  case c0.step.unop₂ : C op v v' K su {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      vok, Kok⟩, cases Kok,
    exact state.ok.ret ⟨σok, Eok, ηok, Sok⟩
      (su.ok Kok_a Kok_a_1 Kok_a_2 vok) Kok_a_3 },
  case c0.step.cond₁ : C c e₁ e₂ K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, ⟨t, eok, tτ⟩, Kok⟩, cases eok,
    have eu₁₂ := finset.subset.trans (finset.subset_union_left _ _) eu,
    have euc := finset.subset.trans (finset.subset_union_left _ _) eu₁₂,
    have eu₁ := finset.subset.trans (finset.subset_union_right _ _) eu₁₂,
    have eu₂ := finset.subset.trans (finset.subset_union_right _ _) eu,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ euc ⟨_, eok_a, vtype.of_ty.bool⟩
      (cont.ok.cond ⟨_, eok_a_1, tτ⟩ eu₁ ⟨_, eok_a_2, tτ⟩ eu₂ Kok) },
  case c0.step.cond₂ : C b e₁ e₂ K {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      vok, Kok⟩, cases Kok,
    cases b,
    { exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ Kok_a_3 Kok_a_2 Kok_a_4 },
    { exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ Kok_a_1 Kok_a Kok_a_4 } },
  case c0.step.nil : C K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, ⟨t, ⟨⟩, tτ⟩, Kok⟩, cases tτ,
    exact state.ok.ret ⟨σok, Eok, ηok, Sok⟩ value.ok.nil Kok },
  case c0.step.cons₁ : C e es K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, ⟨t, eok, tτ⟩, Kok⟩, cases eok, cases tτ,
    have eu₁ := finset.subset.trans (finset.subset_union_left _ _) eu,
    have eu₂ := finset.subset.trans (finset.subset_union_right _ _) eu,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ eu₁ ⟨_, eok_a, tτ_a⟩
      (cont.ok.cons₁ ⟨_, eok_a_1, tτ_a_1⟩ eu₂ Kok) },
  case c0.step.cons₂ : C v es K {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      vok, Kok⟩, cases Kok,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ Kok_a_1 Kok_a
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
      eu, ⟨t, eok, tτ⟩, Kok⟩, cases eok,
    rcases vtype.of_ty_fn (exp.type.ls eok_τs) with ⟨vτs, tτs⟩,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ eu ⟨_, eok_a_1, tτs⟩
      (cont.ok.call eok_a tτ tτs Kok) },
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
      eu, ⟨t, eok, tτ⟩, Kok⟩, cases eok,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ eu ⟨_, eok_a, tτ.ref⟩
      (cont.ok.addr_deref $ cont.ok.deref Kok) },
  case c0.step.index : C e n K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, ⟨t, eok, tτ⟩, Kok⟩, cases eok,
    have eu₁ := finset.subset.trans (finset.subset_union_left _ _) eu,
    have eu₂ := finset.subset.trans (finset.subset_union_right _ _) eu,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ eu₁ ⟨_, eok_a, tτ.arr⟩
      (cont.ok.addr_index₁ eok_a_1 eu₂ $ cont.ok.deref Kok) },
  case c0.step.field : C e n K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, ⟨t, eok, tτ⟩, Kok⟩, cases eok,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ eu ⟨_, eok_a, vtype.of_ty.struct⟩
      (cont.ok.addr_field eok_a_1 eok_a_2 tτ $ cont.ok.deref Kok) },
  case c0.step.deref' : C a K sd {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      aok, Kok⟩, cases Kok,
    exact sd.ok σok Eok ηok Sok aok Kok_a },
  case c0.step.alloc_ref : C τ τ' v K ττ' v0 sa {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, ⟨t, eok, tτ⟩, Kok⟩, cases eok,
    cases ast.eval_ty.determ ok.ind ττ' eok_a, cases tτ,
    refine sa.ok σok Eok ηok Sok (v0.ok' ok _ tτ_a) Kok },
  case c0.step.alloc_arr₁ : C τ τ' e K ττ' {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, ⟨t, eok, tτ⟩, Kok⟩, cases eok,
    cases ast.eval_ty.determ ok.ind ττ' eok_a, cases tτ,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ eu ⟨_, eok_a_2, vtype.of_ty.int⟩
      (cont.ok.alloc_arr tτ Kok) },
  case c0.step.alloc_arr₂ : C τ v K i n e v0 sa {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      vok, Kok⟩, cases Kok, cases Kok_a,
    exact sa.ok σok Eok ηok Sok (v0.ok' ok _ Kok_a_a).repeat.arr Kok_a_1 },
  case c0.step.alloc_arr_err : C τ i K i0 { apply state.ok.err },
  case c0.step.addr_var : C v K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, ⟨t, eok, tτ⟩, Kok⟩, cases eok,
    rcases finmap.exists_mem_lookup_iff.2
      (finmap.mem_keys.1 $ finset.singleton_subset.1 eu) with ⟨τ', vτ'⟩,
    cases vtype.of_ty_determ (σok.ok_of_mem vτ' eok_a) tτ,
    exact state.ok.ret ⟨σok, Eok, ηok, Sok⟩ (addr.ok.var vτ') Kok },
  case c0.step.addr_deref₁ : C e K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, ⟨t, eok, tτ⟩, Kok⟩, cases eok,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ eu ⟨_, eok_a, tτ.ref⟩
      (cont.ok.addr_deref Kok) },
  case c0.step.addr_deref₂ : C v K {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      vok, Kok⟩, cases Kok,
    refine state.ok.ret ⟨σok, Eok, ηok, Sok⟩ (addr.ok.ref_opt vok) Kok_a },
  case c0.step.addr_index₁ : C e n K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, ⟨t, eok, tτ⟩, Kok⟩, cases eok,
    have eu₁ := finset.subset.trans (finset.subset_union_left _ _) eu,
    have eu₂ := finset.subset.trans (finset.subset_union_right _ _) eu,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ eu₁ ⟨_, eok_a, tτ.arr⟩
      (cont.ok.addr_index₁ eok_a_1 eu₂ Kok) },
  case c0.step.addr_index₂ : C a n K {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      vok, Kok⟩, cases Kok,
    refine state.ok.exp ⟨σok, Eok, ηok, Sok⟩ Kok_a_1 ⟨_, Kok_a, vtype.of_ty.int⟩
      (cont.ok.addr_index₂ (addr.ok.ref_opt vok) Kok_a_2) },
  case c0.step.addr_index₃ : C a n K i j len e lt {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      _, Kok⟩, cases Kok,
    cases len with _ _ v len,
    exact state.ok.ret ⟨σok, Eok, ηok, Sok⟩ (addr.ok.nth Kok_a_1) Kok_a_2 },
  case c0.step.addr_index_err₁ : C i K { apply state.ok.err },
  case c0.step.addr_index_err₂ : C a n i K { apply state.ok.err },
  case c0.step.addr_field₁ : C e f K {
    rcases sok with _|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      eu, ⟨t, eok, tτ⟩, Kok⟩, cases eok,
    exact state.ok.exp ⟨σok, Eok, ηok, Sok⟩ eu ⟨_, eok_a, vtype.of_ty.struct⟩
      (cont.ok.addr_field eok_a_1 eok_a_2 tτ Kok) },
  case c0.step.addr_field₂ : C a f K {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, σok, Eok, ηok, Sok⟩,
      aok, Kok⟩, cases Kok,
    exact state.ok.ret ⟨σok, Eok, ηok, Sok⟩
      (addr.ok.field Kok_a Kok_a_1 Kok_a_2 aok) Kok_a_3 },
  case c0.step.addr_field_err : C f K { apply state.ok.err }
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
