import c0.ast_ok order.lattice util.rbmap

namespace c0

instance : has_lt ident := by unfold ident; apply_instance

end c0

namespace c0c
open c0 c0.ast lattice
hide type
open c0 (type)

@[derive decidable_eq]
inductive fstate | hdecl | decl | defn

structure sdef :=
(fields : rbmap ident type)
(size : ℕ)
(align : ℕ)
(offs : rbmap ident ℕ)

structure func_ctx :=
(fdefs : rbmap ident ((list type × option type) × fstate))
(sdefs : rbmap ident sdef)

namespace check
open c0.ast lattice
hide type
open c0 (type)

def defs := rbtree ident × bool

instance : has_bot defs := ⟨(mk_rbtree _, ff)⟩

instance : has_sup defs :=
⟨λ ⟨s₁, b₁⟩ ⟨s₂, b₂⟩, (s₁.union s₂, b₁ || b₂)⟩

instance : has_inf defs :=
⟨λ ⟨s₁, b₁⟩ ⟨s₂, b₂⟩, (s₁.inter s₂, b₁ && b₂)⟩

def defs.insert : defs → ident → defs
| (s, b) x := (s.insert x, b)

instance : has_mem ident defs := ⟨λ x d, d.1.contains x⟩

def step_state {m} [monad m] [monad_except string m] : bool → bool → option fstate → m fstate
| tt ff _ := return fstate.hdecl
| tt tt _ := throw "cannot define a function in a header"
| ff ff old := return (old.get_or_else fstate.decl)
| ff tt none := return fstate.defn
| ff tt (some fstate.hdecl) := throw "a header function must not be defined"
| ff tt (some fstate.decl) := return fstate.defn
| ff tt (some fstate.defn) := throw "a function must not be defined twice"

structure globals :=
(ctx : func_ctx)
(tdefs : rbmap ident type)
(frefs : rbtree ident)

@[reducible] def checker := state_t globals (except string)

@[reducible] def checkerF := reader_t (rbmap ident type) checker

def checker.run (m : checker unit) : except string (rbmap ident type × func_ctx) := do
  (_, ⟨c, td, refs⟩) ← m.run
    ⟨⟨rbmap.singleton main (([], type.int), fstate.decl), mk_rbmap _ _⟩,
      mk_rbmap _ _, rbtree.singleton main⟩,
  let s := refs.filter (λ f, fstate.decl ∈ prod.snd <$> c.fdefs.find f),
  guard_error ("undefined functions: " ++ string.intercalate ", " (s.to_list)) s.empty,
  guard_error "main cannot be external" (fstate.hdecl ∉ prod.snd <$> c.fdefs.find main),
  return (td, c)

def lookup_local (v : ident) : checkerF (option type) :=
(λ m, rbmap.find m v) <$> read

def lookup_fn (f : ident) : checkerF (list type × option type) := do
  v ← lookup_local f,
  guard_error "function is shadowed" v.is_none,
  modify (λ g, {frefs := g.frefs.insert f, ..g}),
  g ← get,
  prod.fst <$> (g.ctx.fdefs.find f).unwrap "function not declared"

def lookup_type (v : ident) : checker (option type) :=
(λ g : globals, g.tdefs.find v) <$> get

def eval_type : ast.type → checker type
| ast.type.int := return type.int
| ast.type.bool := return type.bool
| (ast.type.var v) := lookup_type v >>= option.unwrap "type not declared"
| (ast.type.ref τ) := type.ref <$> eval_type τ
| (ast.type.arr τ) := type.arr <$> eval_type τ
| (ast.type.struct s) := return (type.struct s)

def sz_align : type → checker (ℕ × ℕ)
| type.int := return (4, 4)
| type.bool := return (1, 1)
| (type.ref τ) := return (8, 8)
| (type.arr τ) := return (8, 8)
| (type.struct s) := do
  g ← get,
  sd ← (g.ctx.sdefs.find s).unwrap ("unsized struct " ++ s ++ " used in sized context"),
  return (sd.size, sd.align)

def check_small {m} [monad m] [monad_except string m] : type → m unit
| (type.struct s) := throw ("struct type " ++ s ++ " used in invalid position")
| _ := return ()

def define_all : checkerF defs :=
(λ m, (rbmap.keys_set m, tt)) <$> read

def check_fdecl (fname : ident) (ret : option type) : option stmt → list ident → list type → checkerF unit := sorry

def build_sdef : list (ident × type) → rbmap ident type → ℕ → ℕ → rbmap ident ℕ → checker sdef
| [] fm n al om := return ⟨fm, n, al, om⟩
| ((x, t) :: xs) fm sz al om := do
  guard_error ("field " ++ x ++ " duplicated in structure") (¬ fm.contains x),
  (sz1, al1) ← sz_align t,
  let loc := nat.align_to sz al1,
  build_sdef xs (fm.insert x t) (loc + sz1) (max al1 al) (om.insert x loc)

def check_gdecl : gdecl → checker unit
| (gdecl.fdecl header f xts t body) := do
  g ← get,
  guard_error ("function name already used as type: " ++ f) (¬ g.tdefs.contains f),
  let fd := g.ctx.fdefs.find f,
  let (xs, ts) := list.unzip xts,
  ts' ← mmap eval_type ts,
  mmap' check_small ts',
  t' ← traverse eval_type t,
  traverse check_small t',
  s' ← match fd with
  | none := step_state header body.is_some none
  | some (t1, s) := do
    guard_error "redeclaration types must match" ((ts', t') = t1),
    step_state header body.is_some (some s)
  end,
  put {ctx := {fdefs := g.ctx.fdefs.insert f ((ts', t'), s'), ..g.ctx}, ..g},
  (check_fdecl f t' body xs ts').run (mk_rbmap _ _)
| (gdecl.typedef x t) := do
  g ← get,
  guard_error ("type name was already used as a function: " ++ x) (¬ g.ctx.fdefs.contains x),
  guard_error ("type name '" ++ x ++ "' defined more than once") (¬ g.tdefs.contains x),
  t' ← eval_type t,
  put {tdefs := g.tdefs.insert x t', ..g}
| (gdecl.sdecl _ none) := return ()
| (gdecl.sdecl s (some xts)) := do
  g ← get,
  guard_error ("struct " ++ s ++ " is already defined") (¬ g.ctx.sdefs.contains s),
  xts' ← xts.mmap (λ xt, prod.mk xt.1 <$> eval_type xt.2),
  sd ← build_sdef xts' (mk_rbmap _ _) 0 1 (mk_rbmap _ _),
  put {ctx := {sdefs := g.ctx.sdefs.insert s sd, ..g.ctx}, ..g}

def typecheck (ds : ast) : except string (rbmap ident type × func_ctx) :=
checker.run $ mmap' check_gdecl ds


end check

end c0c
