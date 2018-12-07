import c0.ast

open c0 c0.ast c0.ast.gdecl c0.ast.type c0.ast.exp c0.ast.lval c0.ast.stmt

def cell : ast := list.reverse [
  sdecl "CA" $ some [
    ("rule", (arr int))],
  sdecl "config" $ some [
    ("size", int),
    ("vals", (arr int))],
  fdecl ff "init_CA" [("f", int)] (some (ref (struct "CA"))) $ some $
    decl_asgn "len" int (int 8)
    (decl_asgn "ca" (ref (struct "CA")) (alloc_ref (struct "CA"))
    (asgn (field (deref (var "ca")) "rule") (alloc_arr int (var "len"));
    decl_asgn "i" int (int 0)
    (while (binop (binop.comp comp.lt) (var "i") (var "len"))
    ( asgn (index (field (deref (var "ca")) "rule") (var "i")) (binop binop.shr (binop binop.band (var "f") (binop binop.shl (int 1) (var "i"))) (var "i"));
      asnop (var "i") binop.add (int 1) ));
    ret (some (var "ca")))),
  fdecl ff "lookup" [("ca", (ref (struct "CA"))), ("left", int), ("middle", int), ("right", int)] (some int) $ some $
    ret (some (index (field (deref (var "ca")) "rule") (binop binop.bor (binop binop.bor (var "left") (binop binop.shl (var "middle") (int 1))) (binop binop.shl (var "right") (int 2))))),
  sdecl "rand" $ some [
    ("seed", int)],
  typedef "rand_t" (ref (struct "rand")),
  fdecl ff "init_rand" [("seed", int)] (some (var "rand_t")) $ some $
    decl_asgn "gen" (var "rand_t") (alloc_ref (struct "rand"))
    (asgn (field (deref (var "gen")) "seed") (var "seed");
    ret (some (var "gen"))),
  fdecl ff "rand" [("gen", (var "rand_t"))] (some int) $ some $
    asgn (field (deref (var "gen")) "seed") (binop binop.add (binop binop.mul (field (deref (var "gen")) "seed") (int 1664525)) (int 1013904223));
    ret (some (field (deref (var "gen")) "seed")),
  fdecl ff "new_config" [("size", int)] (some (ref (struct "config"))) $ some $
    decl_asgn "gen" (var "rand_t") (call "init_rand" $ of_list [(int 12632286)])
    (decl_asgn "c" (ref (struct "config")) (alloc_ref (struct "config"))
    (asgn (field (deref (var "c")) "size") (var "size");
    asgn (field (deref (var "c")) "vals") (alloc_arr int (var "size"));
    decl_asgn "i" int (int 0)
    (while (binop (binop.comp comp.lt) (var "i") (var "size"))
    ( asgn (index (field (deref (var "c")) "vals") (var "i")) (cond (binop (binop.comp comp.eq) (binop binop.mod (call "rand" $ of_list [(var "gen")]) (int 2)) (int 0)) (int 0) (int 1));
      asnop (var "i") binop.add (int 1) ));
    ret (some (var "c")))),
  fdecl ff "get_left" [("c", (ref (struct "config"))), ("index", int)] (some int) $ some $
    If (binop (binop.comp comp.eq) (var "index") (int 0))
    ( ret (some (index (field (deref (var "c")) "vals") (binop binop.sub (field (deref (var "c")) "size") (int 1)))) )
    ( nop );
    ret (some (index (field (deref (var "c")) "vals") (binop binop.sub (var "index") (int 1)))),
  fdecl ff "get_right" [("c", (ref (struct "config"))), ("index", int)] (some int) $ some $
    If (binop (binop.comp comp.eq) (var "index") (binop binop.sub (field (deref (var "c")) "size") (int 1)))
    ( ret (some (index (field (deref (var "c")) "vals") (int 0))) )
    ( nop );
    ret (some (index (field (deref (var "c")) "vals") (binop binop.add (var "index") (int 1)))),
  fdecl ff "update" [("ca", (ref (struct "CA"))), ("c_old", (ref (struct "config"))), ("c_new", (ref (struct "config")))] none $ some $
    decl_asgn "i" int (int 0)
    (while (binop (binop.comp comp.lt) (var "i") (field (deref (var "c_old")) "size"))
    ( asgn (index (field (deref (var "c_new")) "vals") (var "i")) (call "lookup" $ of_list [(var "ca"), (call "get_left" $ of_list [(var "c_old"), (var "i")]), (index (field (deref (var "c_old")) "vals") (var "i")), (call "get_right" $ of_list [(var "c_old"), (var "i")])]);
      asnop (var "i") binop.add (int 1) )),
  sdecl "io" $ some [
    ("in", (ref (struct "config"))),
    ("out", (ref (struct "config")))],
  typedef "data" (struct "io"),
  fdecl ff "init" [("param", int)] (some (ref (var "data"))) $ some $
    decl_asgn "size" int (binop binop.add (binop binop.div (var "param") (int 19)) (int 19))
    (decl_asgn "c" (ref (struct "config")) (call "new_config" $ of_list [(var "size")])
    (decl_asgn "d" (ref (struct "config")) (call "new_config" $ of_list [(var "size")])
    (decl_asgn "io" (ref (var "data")) (alloc_ref (var "data"))
    (asgn (field (deref (var "io")) "in") (var "c");
    asgn (field (deref (var "io")) "out") (var "d");
    ret (some (var "io")))))),
  fdecl ff "prepare" [("io", (ref (var "data"))), ("param", int)] none $ some $
    decl_asgn "n" int (binop binop.add (binop binop.div (var "param") (int 19)) (int 19))
    (decl_asgn "i" int (int 0)
    (while (binop (binop.comp comp.lt) (var "i") (binop binop.div (var "n") (int 2)))
    ( asgn (index (field (deref (field (deref (var "io")) "out")) "vals") (var "i")) (index (field (deref (field (deref (var "io")) "in")) "vals") (var "i"));
      asnop (var "i") binop.add (int 1) ));
    ret none),
  fdecl ff "run" [("io", (ref (var "data"))), ("param", int)] none $ some $
    decl_asgn "c" (ref (struct "config")) (field (deref (var "io")) "out")
    (decl_asgn "size" int (field (deref (var "c")) "size")
    (decl_asgn "c_old" (ref (struct "config")) (call "new_config" $ of_list [(var "size")])
    (decl_asgn "ca" (ref (struct "CA")) (call "init_CA" $ of_list [(int 90)])
    (decl_asgn "i" int (int 0)
    (while (binop (binop.comp comp.lt) (var "i") (int 100))
    ( eval (call "update" $ of_list [(var "ca"), (var "c"), (var "c_old")]);
      eval (call "update" $ of_list [(var "ca"), (var "c_old"), (var "c")]);
      asnop (var "i") binop.add (int 2) )))))),
  fdecl ff "checksum" [("io", (ref (var "data"))), ("param", int)] (some int) $ some $
    decl_asgn "c" (ref (struct "config")) (field (deref (var "io")) "out")
    (decl_asgn "sum" int (int 0)
    (decl_asgn "i" int (int 0)
    (while (binop (binop.comp comp.lt) (var "i") (field (deref (var "c")) "size"))
    ( asnop (var "sum") binop.add (index (field (deref (var "c")) "vals") (var "i"));
      asnop (var "i") binop.add (int 1) ));
    ret (some (var "sum")))),
  fdecl ff "main" [] (some int) $ some $
    decl_asgn "c" (ref (var "data")) (call "init" $ of_list [(int 1000)])
    (eval (call "prepare" $ of_list [(var "c"), (int 1000)]);
    eval (call "run" $ of_list [(var "c"), (int 1000)]);
    ret (some (call "checksum" $ of_list [(var "c"), (int 1000)])))
]
