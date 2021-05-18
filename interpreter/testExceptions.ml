(* ocamlc interpreter.ml testExceptions.ml -o testExceptions *)

open Interpreter

let assert_equal a b = assert (a = b)

let assert_raises exc f =
  match f () with
  | exception exc' when exc = exc' -> ()
  | _ -> assert false

let test_1 () =
  assert_equal
    (multi_step (RaiseDivByZero (TInt, Plus (Num 4, Num 2))))
    (RaiseDivByZero (TInt, Num 6))

let test_2 () =
  assert_equal
    (multi_step (Div (Plus (Num 4, Num 2), Num 0)))
    (RaiseDivByZero (TInt, Num 6))

let test_3 () =
  assert_equal
    (multi_step (Try (Plus (Num 4, Num 4), Lambda ("x", TInt, Var "x"))))
    (Num 8)

let test_4 () =
  assert_equal
    (multi_step
       (Try (Div (Num 4, Num 0), Lambda ("x", TInt, Plus (Var "x", Num 1)))))
    (Num 5)

let test_5 () =
  assert_equal
    (multi_step (Apply (Lambda ("x", TInt, Var "x"), Div (Num 4, Num 0))))
    (RaiseDivByZero (TInt, Num 4))

let test_6 () =
  assert_equal
    (multi_step (If (IsZero (Div (Num 4, Num 0)), Num 1, Num 2)))
    (RaiseDivByZero (TInt, Num 4))

let test_7 () =
  assert_equal
    (type_check [] (RaiseDivByZero (TInt, Plus (Num 4, Num 2))))
    TInt

let test_8 () =
  assert_equal
    (type_check []
       (Try (Div (Num 4, Num 0), Lambda ("x", TInt, Plus (Var "x", Num 1)))))
    TInt

let test_9 () =
  assert_equal
    (type_check []
       (If (IsZero (Num 0), RaiseDivByZero (TBool, Num 4), False)))
    TBool

let test_10 () =
  assert_raises Type_error (fun _ ->
      type_check []
        (Try (Div (Num 4, Num 0), Lambda ("x", TBool, Plus (Var "x", Num 1)))))

let test_11 () =
  assert_raises Type_error (fun _ ->
      type_check [] (Try (Div (Num 4, Num 0), Lambda ("x", TInt, False))))

let () =
  test_1 ();
  test_2 ();
  test_3 ();
  test_4 ();
  test_5 ();
  test_6 ();
  test_7 ();
  test_8 ();
  test_9 ();
  test_10 ();
  test_11 ();
