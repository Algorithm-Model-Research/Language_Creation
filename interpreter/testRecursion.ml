(* ocamlc interpreter.ml testRecursion.ml -o testRecursion *)

open Interpreter

let assert_equal a b = assert (a = b)

let test_1 () =
  assert_equal
    (type_check []
       (LambdaRec ("f", TInt, TInt, "x", Plus (Var "x", Var "x"))))
    (TArrow (TInt, TInt))

let test_2 () =
  assert_equal
    (multi_step (LambdaRec ("f", TInt, TInt, "x", Plus (Var "x", Var "x"))))
    (LambdaRec ("f", TInt, TInt, "x", Plus (Var "x", Var "x")))

let test_3 () =
  assert_equal
    (type_check []
       (LambdaRec
          ( "f"
          , TInt
          , TInt
          , "x"
          , If
              ( IsZero (Var "x")
              , Num 0
              , Apply (Var "f", Plus (Var "x", Num (-1))) ) )))
    (TArrow (TInt, TInt))

let test_4 () =
  assert_equal
    (multi_step
       (Apply
          ( LambdaRec
              ( "f"
              , TInt
              , TInt
              , "x"
              , If
                  ( IsZero (Var "x")
                  , Num 0
                  , Apply (Var "f", Plus (Var "x", Num (-1))) ) )
          , Num 5 )))
    (Num 0)

let test_5 () =
  assert_equal
    (type_check []
       (LambdaRec
          ( "f1"
          , TInt
          , TArrow (TInt, TInt)
          , "x1"
          , LambdaRec
              ( "f2"
              , TInt
              , TInt
              , "x2"
              , If
                  ( IsZero (Var "x1")
                  , Apply (Var "f2", Var "x1")
                  , Apply
                      (Apply (Var "f1", Var "x2"), Plus (Var "x1", Num (-1)))
                  ) ) )))
    (TArrow (TInt, TArrow (TInt, TInt)))

let test_6 () =
  assert_equal
    (type_check []
       (LambdaRec
          ( "factorial"
          , TInt
          , TInt
          , "n"
          , If
              ( IsZero (Var "n")
              , Num 1
              , Mult
                  (Var "n", Apply (Var "factorial", Plus (Var "n", Num (-1))))
              ) )))
    (TArrow (TInt, TInt))

let test_7 () =
  assert_equal
    (multi_step
       (Apply
          ( LambdaRec
              ( "factorial"
              , TInt
              , TInt
              , "n"
              , If
                  ( IsZero (Var "n")
                  , Num 1
                  , Mult
                      ( Var "n"
                      , Apply (Var "factorial", Plus (Var "n", Num (-1))) )
                  ) )
          , Num 6 )))
    (Num 720)

let () =
  test_1 ();
  test_2 ();
  test_3 ();
  test_4 ();
  test_5 ();
  test_6 ();
  test_7 ();
