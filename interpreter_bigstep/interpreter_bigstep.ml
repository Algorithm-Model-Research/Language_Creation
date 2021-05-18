exception Eval_error

type exp =
    | True
    | False
    | If of exp * exp * exp
    | Num of int
    | IsZero of exp
    | Plus of exp * exp
    | Mult of exp * exp
    
    
let rec string_of_exp (e: exp) = 
    match e with
    | True -> "true"
    | False -> "false"
    | If(e1, e2, e3) -> "if " ^ string_of_exp(e1) ^ " then " ^ string_of_exp(e2) ^ " else " ^ string_of_exp(e3)
    | Num e1 -> string_of_int(e1)
    | IsZero e1 -> "(" ^ "isZero " ^ string_of_exp(e1) ^ ")"
    | Plus(e1,e2) -> "(" ^ string_of_exp(e1) ^ " + " ^ string_of_exp(e2) ^ ")"
    | Mult(e1,e2) -> "(" ^ string_of_exp(e1) ^ " * " ^ string_of_exp(e2) ^ ")"
;;

let rec eval (e : exp) =
    match e with
    | True -> True
    | False -> False
    | If(e1, e2, e3) -> if eval e1 = True then eval e2 else eval e3
    | Num e1 -> Num e1
    | IsZero e1 -> if eval e1 = True then raise Eval_error else if eval e1 = False then raise Eval_error else if (eval e1 = Num 0) then True else False
    | Plus(e1,e2) ->
        begin match eval e1, eval e2 with
        | Num n1, Num n2 -> Num (n1 + n2)
        | _ -> raise Eval_error
        end
    | Mult(e1,e2) ->
        begin match eval e1, eval e2 with
        | Num n1, Num n2 -> Num (n1 * n2)
        | _ -> raise Eval_error
        end
;;
        
