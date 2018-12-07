# vc0: Verified C0

This repository describes a formalization of the static and dynamic semantics of the language C0 (http://c0.typesafety.net/). Future plans for this repository include a verified compiler for the language. At present it contains:

* [`c0/ast.lean`](src/c0/ast.lean): The AST of a parsed C0 program. (The parser is not formalized.)
* [`c0/ast_ok.lean`](src/c0/ast_ok.lean): Static typing for valid ASTs. This is the property that is checked by the `cc0` compiler; if it fails to hold then a compile error is produced.
* [`c0/dyn.lean`](src/c0/dyn.lean): Dynamic semantics of running C0 programs. This is a specification for the execution behavior of the program, as a small step relation.
* [`c0/dyn_ok.lean`](src/c0/dyn_ok.lean): Type correctness of states. This is not checked by the compiler, but rather is the set of invariants that hold throughout the execution of a valid program.

The main theorems proven are:

* [`vc0/preservation.lean`](src/vc0/preservation.lean): If `s` is a valid state, and `s` steps to `s'`, then `s'` is also a valid state.
* [`vc0/progress.lean`](src/vc0/progress.lean): If `s` is a valid state, then either `s` is a final state, or `s` steps to some `s'`.
* [`vc0/determ.lean`](src/vc0/determ.lean): If `s` steps to `s'` and `s` also steps to `s''`, then `s' = s''` (determinism).
