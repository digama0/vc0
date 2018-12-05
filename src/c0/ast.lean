import c0.common util.basic util.int32

namespace c0
namespace ast

inductive type
| int | bool
| var : ident → type
| ref : type → type
| arr : type → type
| struct : ident → type

-- | the expressions
inductive exp
| int : int32 → exp              -- An integer literal e.g. @42@
| bool : bool → exp              -- A boolean literal @true@ or @false@
| null                            -- The null literal for pointers
| var : ident → exp              -- an identifier
| binop : binop → exp → exp → exp -- a binary operation @e1 op e2@
| unop : unop → exp → exp         -- a unary operation @op e@
| cond : exp → exp → exp → exp    -- a ternary conditional @cond ? e1 : e2@
| nil                             -- an empty expression list
| cons : exp → exp → exp          -- a comma (e1, ...) in an expression list
| call : ident → exp → exp        -- a function call $f(e1, ..., en)@
| deref : exp → exp               -- a pointer dereference @*e@
| index : exp → exp → exp         -- an array dereference @e1[e2]@
| field : exp → ident → exp       -- a field access @e.f@
| alloc_ref : type → exp           -- a pointer allocation @alloc(ty)@
| alloc_arr : type → exp → exp     -- an array allocation @alloc_array(ty, len)@

inductive lval
| var : ident → lval
| deref : lval → lval
| index : lval → exp → lval
| field : lval → ident → lval

inductive stmt
| decl : ident → type → stmt → stmt
| decl_asgn : ident → type → exp → stmt → stmt
| If : exp → stmt → stmt → stmt
| while : exp → stmt → stmt
| asgn : lval → exp → stmt  -- ^ @x = e;@
| asnop : lval → binop → exp → stmt -- ^ @x op= e;@
| eval : exp → stmt        -- ^ @e;@ (a bare expression statement)
| assert : exp → stmt      -- ^ @assert(e);@ (an assertion)
| ret : option exp → stmt  -- ^ @return e;@
| nop : stmt               -- ^ an empty statement
| seq : stmt → stmt → stmt -- ^ @stmt; stmt@

inductive gdecl
| fdecl : bool → ident → list (ident × type) → option type → option stmt → gdecl
| typedef : ident → type → gdecl
| sdecl : ident → option (list (ident × type)) → gdecl

def lval.to_exp : lval → exp
| (lval.var v) := exp.var v
| (lval.deref e) := e.to_exp.deref
| (lval.index e₁ e₂) := e₁.to_exp.index e₂
| (lval.field e f) := e.to_exp.field f

end ast

@[reducible] def ast := list ast.gdecl

end c0
