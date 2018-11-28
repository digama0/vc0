import c0.dyn_ok

namespace c0

open ast ast.gdecl

theorem ctx.ok.nil : ctx.ok [] := list.nodup_nil

theorem ctx.ok.cons {v τ Δ} (h₁ : ctx.ok Δ) (h₂ : ∀ τ', (v, τ') ∉ Δ) :
  ctx.ok ((v, τ) :: Δ) :=
by refine list.nodup_cons.2 ⟨λ h, _, h₁⟩;
   rcases list.mem_map.1 h with ⟨⟨v, t⟩, ht, ⟨⟩⟩;
   exact h₂ _ ht

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

theorem ok.weak' {Γ Δ e τ vt} (h : exp.ok Γ Δ e τ) : exp.ok Γ (vt :: Δ) e τ :=
begin
  induction h,
  { exact ok.int },
  { exact ok.bool },
  { exact ok.null },
  { exact ok.var _ (or.inr h_a) },
  { exact ok.binop h_ih_a h_ih_a_1 h_a_2 },
  { exact ok.unop h_ih h_a_1 },
  { exact ok.cond h_ih_a h_ih_a_1 h_ih_a_2 h_a_3 },
  { exact ok.nil },
  { exact ok.cons h_ih_a h_ih_a_1 },
  { exact ok.call h_a h_ih },
  { exact ok.field h_ih h_a_1 h_a_2 },
  { exact ok.deref h_ih h_a_1 },
  { exact ok.index h_ih_a h_ih_a_1 },
  { exact ok.alloc_ref _ h_a h_a_1 },
  { exact ok.alloc_arr h_a h_a_1 h_ih },
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

theorem sdecl_ok_of_mem {Γ : ast} (ok : Γ.ok) :
  ∀ {s xτs},
  sdecl s (some xτs) ∈ Γ →
  ∃ xτs', list.forall₂ (prod.forall₂ eq (eval_ty Γ)) xτs xτs' ∧
   ∀ xτ ∈ xτs', Γ.sized (xτ : ident × type).2 :=
ast.ok_induction ok (by rintro _ _ ⟨⟩) $
λ d Γ g IH s xτs m, begin
  suffices : ∃ xτs',
    list.forall₂ (prod.forall₂ eq (eval_ty Γ)) xτs xτs' ∧
      ∀ (xτ : ident × type), xτ ∈ xτs' → sized Γ xτ.2,
  from this.imp (λ xτs', and.imp
    (list.forall₂.imp $ λ a b h, h.imp (λ _ _, id) (λ _ _, eval_ty.weak))
    (λ H xτ h, (H xτ h).weak)),
  rcases m with rfl | m,
  { cases g, clear g_a g_a_1,
    induction xτs with xτ xτs IH,
    { exact ⟨[], list.forall₂.nil, list.forall_mem_nil _⟩ },
    cases xτ with x τ,
    cases list.forall_mem_cons.1 g_a_2 with h₁ h₂,
    rcases IH h₂ with ⟨xτs', h₁', h₂'⟩,
    rcases h₁ with ⟨τ', h, hs⟩,
    exact ⟨(x, τ')::xτs', list.forall₂.cons ⟨rfl, h⟩ h₁',
      list.forall_mem_cons.2 ⟨hs, h₂'⟩⟩ },
  { exact IH m }
end

theorem get_sdef_ex_iff {Γ : ast} (ok : Γ.ok) {s} :
  (∃ sd, get_sdef Γ s sd) ↔ ∃ body, gdecl.sdecl s (some body) ∈ Γ :=
begin
  split,
  { rintro ⟨sd, _, xτs, _, _, m, h⟩, exact ⟨_, m⟩ },
  { rintro ⟨xτs, m⟩,
    rcases sdecl_ok_of_mem ok m with ⟨xτs', h₁, h₂⟩,
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

theorem vars.ok.empty {Γ H} : vars.ok Γ H ∅ ∅ :=
⟨list.forall₂.nil, list.nodup_nil⟩

theorem env.ok.empty {Γ} : env.ok Γ ∅ ∅ vtype.int :=
⟨ctx.ok.nil, list.forall₂.nil, vars.ok.empty, stack.ok.nil⟩

theorem start_ok (Γ : ast) (ok : Γ.ok) : ∀ s, start Γ s → state.ok Γ s
| _ (@start.mk _ s h) := state.ok.stmt env.ok.empty
  ⟨some type.int, vtype.of_ty.int, get_body_ok ok h⟩ stmt_list.ok.nil

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

theorem preservation {Γ : ast} (ok : Γ.ok)
  {s} (sok : state.ok Γ s) {o} (iok : io.ok Γ o)
  {s'} (H : step Γ s o s') : state.ok Γ s' :=
begin
  cases H,
  case c0.step.decl : H S η v τ τ' s K H₁ {
    rcases sok with ⟨_, _, τ, _, _,
      ⟨E, σs, σ, H, η, S, Δ, _, Δok, Eok, ηok, Sok⟩,
      ⟨t, tτ, _, _, _, τ', _, hn, ττ', τsm, sok⟩, Kok⟩,
    exact state.ok.stmt ⟨Δok.cons hn, Eok, ηok, Sok⟩ ⟨t, tτ, sok⟩ Kok.weak },
  case c0.step.decl_asgn : H S η v τ τ' e s K H₁ {
    rcases sok with ⟨_, _, τ, _, _,
      ⟨E, σs, σ, H, η, S, Δ, _, Δok, Eok, ηok, Sok⟩,
      ⟨t, tτ, sok⟩, Kok⟩, cases sok,
    exact state.ok.stmt ⟨Δok.cons sok_a_1, Eok, ηok, Sok⟩
      ⟨t, tτ, stmt.ok.asgn _ (exp.ok.var Γ (or.inl rfl)) sok_a_4.weak' sok_a_3⟩
      (Kok.weak.cons ⟨t, tτ, sok_a_5⟩) },
  case c0.step.If₁ : C c s₁ s₂ K {
    rcases sok with ⟨T, _, τ, _, _,
      ⟨E, σs, σ, H, η, S, Δ, _, Δok, Eok, ηok, Sok⟩,
      ⟨t, tτ, sok⟩, Kok⟩, cases sok,
    exact state.ok.exp ⟨Δok, Eok, ηok, Sok⟩
      ⟨_, sok_a_1, vtype.of_ty.bool⟩
      (cont.ok.If ⟨t, tτ, sok_a_2⟩ ⟨t, tτ, sok_a_3⟩ Kok) },
  case c0.step.If₂ : C b s₁ s₂ K {
    rcases sok with _|_|⟨E, σs, σ, H, η, S, Δ, ret, τ, α, v, K,
      ⟨E, σs, σ, H, η, S, Δ, _, Δok, Eok, ηok, Sok⟩,
      ⟨⟨⟩⟩, _, _, _, s₁ok, s₂ok, Kok⟩,
    refine state.ok.stmt ⟨Δok, Eok, ηok, Sok⟩ _ Kok,
    cases b; [exact s₂ok, exact s₁ok] },
  case c0.step.while : C c s K {
    rcases sok with ⟨T, _, τ, _, _,
      ⟨E, σs, σ, H, η, S, Δ, _, Δok, Eok, ηok, Sok⟩,
      ⟨t, tτ, sok⟩, Kok⟩, cases id sok,
    exact state.ok.exp ⟨Δok, Eok, ηok, Sok⟩ ⟨_, a, vtype.of_ty.bool⟩
      (cont.ok.If ⟨_, tτ, a_1.seq sok⟩ ⟨_, tτ, stmt.ok.nop⟩ Kok) },
  case c0.step.asgn₁ : C lv e K {
    rcases sok with ⟨T, _, τ, _, _,
      ⟨E, σs, σ, H, η, S, Δ, _, Δok, Eok, ηok, Sok⟩,
      ⟨t, tτ, sok⟩, Kok⟩, cases sok,
    rcases vtype.of_ty_fn sok_τ with ⟨vτ, hv⟩,
    exact state.ok.exp ⟨Δok, Eok, ηok, Sok⟩ ⟨_, sok_a_1, hv⟩
      (cont.ok.asgn₁ _ _ _ ⟨_, sok_a_2, hv⟩ Kok) },
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
