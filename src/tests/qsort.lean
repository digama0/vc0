import c0.ast

open c0 c0.ast c0.ast.gdecl c0.ast.type c0.ast.exp c0.ast.lval c0.ast.stmt

def qsort : ast := list.reverse [
  fdecl ff "is_sorted" [("A", (arr int)), ("lower", int), ("upper", int)] (some bool) $ some $
    decl_asgn "i" int (var "lower")
    (while (binop (binop.comp comp.lt) (var "i") (binop binop.sub (var "upper") (int 1)))
    ( If (unop unop.not (binop (binop.comp comp.le) (index (var "A") (var "i")) (index (var "A") (binop binop.add (var "i") (int 1)))))
      ( ret (some (bool ff)) )
      ( nop );
      asnop (var "i") binop.add (int 1) ));
    ret (some (bool tt)),
  fdecl ff "leq" [("x", int), ("A", (arr int)), ("lower", int), ("upper", int)] (some bool) $ some $
    decl_asgn "i" int (var "lower")
    (while (binop (binop.comp comp.lt) (var "i") (var "upper"))
    ( If (unop unop.not (binop (binop.comp comp.le) (var "x") (index (var "A") (var "i"))))
      ( ret (some (bool ff)) )
      ( nop );
      asnop (var "i") binop.add (int 1) ));
    ret (some (bool tt)),
  fdecl ff "geq" [("x", int), ("A", (arr int)), ("lower", int), ("upper", int)] (some bool) $ some $
    decl_asgn "i" int (var "lower")
    (while (binop (binop.comp comp.lt) (var "i") (var "upper"))
    ( If (unop unop.not (binop (binop.comp comp.ge) (var "x") (index (var "A") (var "i"))))
      ( ret (some (bool ff)) )
      ( nop );
      asnop (var "i") binop.add (int 1) ));
    ret (some (bool tt)),
  fdecl ff "gt" [("x", int), ("A", (arr int)), ("lower", int), ("upper", int)] (some bool) $ some $
    decl_asgn "i" int (var "lower")
    (while (binop (binop.comp comp.lt) (var "i") (var "upper"))
    ( If (unop unop.not (binop (binop.comp comp.gt) (var "x") (index (var "A") (var "i"))))
      ( ret (some (bool ff)) )
      ( nop );
      asnop (var "i") binop.add (int 1) ));
    ret (some (bool tt)),
  fdecl ff "lt" [("x", int), ("A", (arr int)), ("lower", int), ("upper", int)] (some bool) $ some $
    decl_asgn "i" int (var "lower")
    (while (binop (binop.comp comp.lt) (var "i") (var "upper"))
    ( If (unop unop.not (binop (binop.comp comp.lt) (var "x") (index (var "A") (var "i"))))
      ( ret (some (bool ff)) )
      ( nop );
      asnop (var "i") binop.add (int 1) ));
    ret (some (bool tt)),
  fdecl ff "swap" [("A", (arr int)), ("i", int), ("j", int)] none $ some $
    decl_asgn "tmp" int (index (var "A") (var "i"))
    (asgn (index (var "A") (var "i")) (index (var "A") (var "j"));
    asgn (index (var "A") (var "j")) (var "tmp")),
  fdecl ff "partition" [("A", (arr int)), ("lower", int), ("upper", int)] (some int) $ some $
    decl_asgn "pivot_index" int (binop binop.add (var "lower") (binop binop.div (binop binop.sub (var "upper") (var "lower")) (int 2)))
    (decl_asgn "pivot" int (index (var "A") (var "pivot_index"))
    (eval (call "swap" $ of_list [(var "A"), (var "pivot_index"), (binop binop.sub (var "upper") (int 1))]);
    decl_asgn "left" int (var "lower")
    (decl_asgn "right" int (var "lower")
    (while (binop (binop.comp comp.lt) (var "right") (binop binop.sub (var "upper") (int 1)))
    ( If (binop (binop.comp comp.le) (var "pivot") (index (var "A") (var "right")))
      ( asnop (var "right") binop.add (int 1) )
      ( eval (call "swap" $ of_list [(var "A"), (var "left"), (var "right")]);
        asnop (var "left") binop.add (int 1);
        asnop (var "right") binop.add (int 1) ) );
    eval (call "swap" $ of_list [(var "A"), (var "left"), (binop binop.sub (var "upper") (int 1))]);
    ret (some (var "left")))))),
  fdecl ff "qsort" [("A", (arr int)), ("lower", int), ("upper", int)] none $ some $
    If (binop (binop.comp comp.le) (binop binop.sub (var "upper") (var "lower")) (int 1))
    ( ret none )
    ( nop );
    decl_asgn "i" int (call "partition" $ of_list [(var "A"), (var "lower"), (var "upper")])
    (eval (call "qsort" $ of_list [(var "A"), (var "lower"), (var "i")]);
    eval (call "qsort" $ of_list [(var "A"), (binop binop.add (var "i") (int 1)), (var "upper")]);
    ret none),
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
  sdecl "io" $ some [
    ("size", int),
    ("in", (arr int)),
    ("out", (arr int))],
  typedef "data" (struct "io"),
  fdecl ff "init" [("param", int)] (some (ref (var "data"))) $ some $
    decl_asgn "gen" (var "rand_t") (call "init_rand" $ of_list [(int (-559038737))])
    (decl_asgn "n" int (var "param")
    (decl_asgn "in" (arr int) (alloc_arr int (var "n"))
    (decl_asgn "out" (arr int) (alloc_arr int (var "n"))
    (decl_asgn "i" int (int 0)
    (while (binop (binop.comp comp.lt) (var "i") (var "n"))
    ( asgn (index (var "in") (var "i")) (call "rand" $ of_list [(var "gen")]);
      asnop (var "i") binop.add (int 1) ));
    decl_asgn "io" (ref (var "data")) (alloc_ref (var "data"))
    (asgn (field (deref (var "io")) "size") (var "param");
    asgn (field (deref (var "io")) "in") (var "in");
    asgn (field (deref (var "io")) "out") (var "out");
    ret (some (var "io"))))))),
  fdecl ff "prepare" [("io", (ref (var "data"))), ("param", int)] none $ some $
    decl_asgn "n" int (field (deref (var "io")) "size")
    (decl_asgn "i" int (int 0)
    (while (binop (binop.comp comp.lt) (var "i") (var "n"))
    ( asgn (index (field (deref (var "io")) "out") (var "i")) (index (field (deref (var "io")) "in") (var "i"));
      asnop (var "i") binop.add (int 1) ))),
  fdecl ff "run" [("io", (ref (var "data"))), ("param", int)] none $ some $
    eval (call "qsort" $ of_list [(field (deref (var "io")) "out"), (int 0), (field (deref (var "io")) "size")]),
  fdecl ff "sum" [("A", (arr int)), ("lower", int), ("upper", int)] (some int) $ some $
    decl_asgn "r" int (int 0)
    (decl_asgn "i" int (var "lower")
    (while (binop (binop.comp comp.lt) (var "i") (var "upper"))
    ( asgn (var "r") (binop binop.add (var "r") (index (var "A") (var "i")));
      asnop (var "i") binop.add (int 1) ));
    ret (some (var "r"))),
  fdecl ff "checksum" [("io", (ref (var "data"))), ("param", int)] (some int) $ some $
    decl_asgn "n" int (field (deref (var "io")) "size")
    (decl_asgn "b" int (cond (call "is_sorted" $ of_list [(field (deref (var "io")) "out"), (int 0), (var "n")]) (int 1) (int 0))
    (decl_asgn "sum" int (call "sum" $ of_list [(field (deref (var "io")) "out"), (int 0), (var "n")])
    (ret (some (binop binop.add (var "b") (var "sum")))))),
  fdecl ff "main" [] (some int) $ some $
    decl_asgn "io" (ref (var "data")) (call "init" $ of_list [(int 1000)])
    (eval (call "prepare" $ of_list [(var "io"), (int 1000)]);
    eval (call "run" $ of_list [(var "io"), (int 1000)]);
    ret (some (call "checksum" $ of_list [(var "io"), (int 1000)])))
]
