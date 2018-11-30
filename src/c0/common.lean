

namespace c0

def ident : Type := string

inductive comp | lt | le | gt | ge | eq | ne

inductive asize | a8 | a32 | a64

inductive err | arith | mem | abort

inductive type
| int | bool
| ref : type -> type
| arr : type → type
| struct : ident → type

structure fdef :=
(params : list type)
(ret : option type)

inductive binop
| add  -- @x y : int |- x + y : int@
| sub  -- @x y : int |- x - y : int@
| mul  -- @x y : int |- x * y : int@
| div  -- @x y : int |- x / y : int@
| mod  -- @x y : int |- x % y : int@
| band -- @x y : int |- x & y : int@
| bxor -- @x y : int |- x ^ y : int@
| bor  -- @x y : int |- x | y : int@
| shl  -- @x y : int |- x << y : int@
| shr  -- @x y : int |- x >> y : int@
| comp : comp → binop -- @x y : int |- x ?= y : bool@ (we coerce bool to int if necessary in the args)

inductive unop
| neg    -- ^ @x : int |- -x : int@
| not    -- ^ @x : bool |- !x : bool@
| bnot -- ^ @x : int |- ~x : int@

end c0
