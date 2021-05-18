exception Eval_error
exception Type_error
exception Substitution_error

open List

type typ = 
	| TBool 
	| TInt 
	| TArrow of typ * typ

type exp =
  | True
  | False
  | If of exp * exp * exp
  | Num of int
  | IsZero of exp
  | Plus of exp * exp
  | Mult of exp * exp
  | Var of string
  | Lambda of string * typ * exp
  | Apply of exp * exp
  | LambdaRec of string * typ * typ * string * exp
  | Div of exp * exp
  | Try of exp * exp
  | RaiseDivByZero of typ * exp 


type type_environment = (string * typ) list


let rec remove_x x list = match list with 
  |[] -> []
  |hd::tl-> if hd = x then remove_x x tl else hd::(remove_x x tl)


let rec free_variables (expo : exp) = 
  match expo with
  | True -> []
  | False -> []
  | If(e1,e2,e3) -> free_variables e1 @ free_variables e2 @ free_variables e3
  | Num e1 -> []
  | IsZero e1 -> free_variables e1
  | Plus(e1,e2) -> free_variables e1 @ free_variables e2
  | Mult(e1,e2)->free_variables e1 @ free_variables e1
  | Var var -> [var]
  | Lambda(str,typ,e1) -> (remove_x str (free_variables e1) )
  | LambdaRec(str1,typ1,typ2,str2,e1)-> remove_x str1 (remove_x str2 (free_variables e1))
  | Div(e1,e2) -> free_variables e1 @ free_variables e2
  | Try(e1, e2) -> free_variables e1 @ free_variables e2
  | RaiseDivByZero(typ, e1) -> free_variables e1
;;

let contains list (str:string) = mem str list

let rec substitution (e1 : exp) (x : string) (e2 : exp) = 
  match e1 with
  |Var(var)-> if var = x then e2 else Var(var)
  |True -> True 
  |False -> False 
  |Num(e) -> Num(e)
  |Plus(exp1,exp2) -> Plus( substitution exp1 x e2 , substitution exp2 x e2)
  |Mult(exp1,exp2) -> Mult(substitution exp1 x e2 , substitution exp2 x e2)
  |IsZero(e)-> IsZero(substitution e x e2 )
  |If(exp1,exp2,exp3)-> If( (substitution exp1 x e2) , (substitution exp2 x e2) ,(substitution exp3 x e2))
  |Lambda(y,typ,exp1)-> if( (y = x) || (contains (free_variables e2) y)) then Lambda(y,typ,exp1) else Lambda(y,typ, substitution exp1 x e2)                    
  |Apply(exp1, exp2)-> Apply((substitution exp1 x e2) , (substitution exp2 x e2))
  |LambdaRec(str1, typ1, typ2 ,str2 , e)->  if((str2 = x) || (str1 = x)) then LambdaRec(str1, typ1, typ2 ,str2 , e) 
                                                        else if((contains (free_variables e2) str1) ||   (contains (free_variables e2) str2)     )  
                                                                then raise Substitution_error
                                                                           else(substitution (LambdaRec(str1, typ1, typ2 ,str2 , e)) x e2)

  |Div(exp1, exp2)->Div(substitution exp1 x e2 , substitution exp2 x e2)
  |Try(exp1,exp2)->Try(substitution exp1 x e2 , substitution exp2 x e2)
  |RaiseDivByZero(typ1,exp1)->RaiseDivByZero(typ1 , substitution exp1 x e2)
;;

let rec step (e: exp) = 
  match e with
  | True  -> raise Eval_error
  | False -> raise Eval_error
  | If(True,e2,e3) -> e2
  | If(False,e2,e3) -> e3
  | If(e1,e2,e3)->
     begin match e1 with
      |Num n -> raise Eval_error 
      |RaiseDivByZero(typ, Num n)->RaiseDivByZero(typ, Num n)
     |_->let temp = step(e1) in If(temp,e2,e3)
    end
  | Num e1 -> raise Eval_error
  | IsZero(Num(0)) -> True
  | IsZero(True)->raise Eval_error
  | IsZero(False)->raise Eval_error
  | IsZero e1 ->
        begin match e1 with
        | Num n -> if ((n) == 0) then True else False
        | RaiseDivByZero(typ, Num n)-> RaiseDivByZero(typ, Num n)
        | _ -> let temp = step e1 in IsZero temp
        end
  | Plus(e1,e2) ->
      begin match e1 with
        | Num n1 -> 
          begin match e2 with 
          |Num n2 -> Num (n1 + n2)
          |  _-> Plus(e1,(step e2))
        end
        |_-> Plus((step e1),e2)
      end
  | Plus(True,e2)->raise Eval_error
  | Plus(e1,True)-> raise Eval_error
  | Plus(False, e2)->raise Eval_error
  | Plus(e1,False)->raise Eval_error
  | Mult(e1,e2) -> 
    begin match e1 with
      | Num n1 -> 
        begin match e2 with 
        |Num n2 -> Num (n1 * n2)
        |  _-> Mult(e1,(step e2))
      end
      |_-> Mult((step e1),e2)
    end
  | Mult(True,e2)->raise Eval_error
  | Mult(e1,True)-> raise Eval_error
  | Mult(False, e2)->raise Eval_error
  | Mult(e1,False)->raise Eval_error
  | Apply(exp1,exp2)-> 
    begin match exp1 with
    |Lambda(x, typ, e)->
       begin match exp2 with
        | True -> substitution e x exp2
        | False -> substitution e x exp2
        | Var(e1) -> substitution e x exp2 
        | Num(e2)-> substitution e x exp2
        | Lambda(x',typ',e')-> substitution e x exp2
        | Div(e1,e2)->substitution e x exp2
        | Try(e1,e2)->substitution e x exp2
        | _-> Apply(exp1,step exp2)
       end
    |LambdaRec(str1, typ1, typ2 ,str2 , e)-> 
       begin match exp2 with
         | True -> substitution (substitution e str2 exp2) str1 (LambdaRec(str1, typ1, typ2 ,str2 , e))
         | False -> substitution (substitution e str2 exp2) str1 (LambdaRec(str1, typ1, typ2 ,str2 , e))
         | Var(e1) -> substitution (substitution e str2 exp2) str1 (LambdaRec(str1, typ1, typ2 ,str2 , e))
         | Num(e2) -> substitution (substitution e str2 exp2) str1 (LambdaRec(str1, typ1, typ2 ,str2 , e))
         | Lambda(x',typ',e') -> substitution (substitution e str2 exp2) str1 (LambdaRec(str1, typ1, typ2 ,str2 , e))
         | _-> Apply(exp1,step exp2)
         end
    |_->Apply(step exp1 , exp2)
    end
           
  | Var var -> raise Eval_error
  | Div(e1,e2)->
      begin match e1 with 
      |Num(n1) ->
        begin match e2 with
        |Num(n2) -> if(n2 == 0) then ( RaiseDivByZero(TInt, Num(n1))) else Num(n1/n2)
        | _-> Div(e1,(step e2))
        end
      |_-> Div((step e1),e2)
      end
  | Try(True,e1)->True 
  | Try(False,e1)->False 
  | Try(Num(e1),e2)->Num(e1)
  | Try(RaiseDivByZero(typ, n1),e1)-> (step (Apply(e1,n1)))
  | Try(e1,e2)->Try((step e1), e2)
  | RaiseDivByZero(e1,e2)->
        begin match e2 with
        |True -> raise Eval_error
        |False -> raise Eval_error
        |Num n1-> raise Eval_error
        |_-> RaiseDivByZero(e1,(step e2))
        end
  | RaiseDivByZero(t, RaiseDivByZero(n1, n2))->RaiseDivByZero(n1,n2)
  | If(RaiseDivByZero(n1, n2),e2,e3)-> RaiseDivByZero(n1, n2)
  | IsZero(RaiseDivByZero(n1, n2)) -> RaiseDivByZero(n1, n2)
  | Plus(RaiseDivByZero(n1, n2),e2) -> RaiseDivByZero(n1, n2)
  | Plus(e1,RaiseDivByZero(n1, n2)) -> RaiseDivByZero(n1, n2)
  | Mult(e1,RaiseDivByZero(n1, n2)) -> RaiseDivByZero(n1, n2)
  | Mult(RaiseDivByZero(n1, n2),e2) -> RaiseDivByZero(n1, n2)
  | Apply(RaiseDivByZero(n1, n2),e2) -> RaiseDivByZero(n1, n2)
  | Apply(e1,RaiseDivByZero(n1, n2)) -> RaiseDivByZero(n1, n2)


let rec multi_step(e: exp) = 
  match e with
  | True -> True
  | False -> False
  | If(e1,e2,e3) -> multi_step(step(If(e1,e2,e3)))
  | Num e1-> Num e1
  | IsZero e1 -> multi_step(step(IsZero(e1)))
  | Plus(e1,e2) -> multi_step(step(Plus(e1,e2)))
  | Mult(e1,e2)-> multi_step(step(Mult(e1,e2)))
  | Var var -> Var var
  | Lambda(x, typ, e1)-> Lambda(x, typ, e1)
  | RaiseDivByZero(typ, Num e1) -> RaiseDivByZero(typ, Num e1)
  | LambdaRec(str1,typ1,typ2,str2,e1)->LambdaRec(str1,typ1,typ2,str2,e1)
  | Apply(e1, e2) -> multi_step(step(Apply(e1,e2)))
  | Div(e1,e2) -> multi_step(step(Div(e1,e2)))
  | Try(e1, e2) -> multi_step(step(Try(e1,e2)))
  | RaiseDivByZero(typ, e1) -> multi_step(step(RaiseDivByZero(typ,e1)))
;;


let rec type_check (te: type_environment) (e: exp) = 
  match e with
  |True-> TBool
  |False-> TBool
  |If(e1,e2,e3)->
    begin match type_check te e1 with
    |TBool -> 
      begin match type_check te e2, type_check te e3 with
      |TInt, TInt-> TInt
      |TBool, TBool-> TBool
      |(TArrow(n1,n2), TArrow(n3,n4)) -> if ((n1 = n3) && (n2 = n4)) then TArrow(n1,n2) else raise Type_error
      |_-> raise Type_error
      end
    |_ -> raise Type_error
    end
  | Num e1-> TInt
  | IsZero e1->
      begin match type_check te e1 with
      |TInt -> TBool
      |_->raise Type_error
      end
  | Plus(e1,e2) ->
      begin match type_check te e1, type_check te e2 with 
      | TInt, TInt-> TInt
      | _ -> raise Type_error
      end
  | Mult(e1,e2) ->
      begin match type_check te e1 , type_check te e2 with 
      | TInt, TInt-> TInt
      | _ -> raise Type_error
      end
  | Var var -> 
      begin match te with
      |[]-> raise Type_error
      |(input1,input2) :: str-> if input1 = var then input2  else type_check str (Var var)
      |_ -> raise Type_error
      end
  | Lambda(expo,typ,e1) -> TArrow(typ,(type_check ((expo,typ)::te) e1))
  | LambdaRec(str1,typ1,typ2,str2,e1)-> (if((type_check ((str1,TArrow(typ1,typ2))::(str2,typ1)::te) (Lambda(str2,typ1,e1)))<>(TArrow(typ1,typ2))) then raise Type_error else TArrow(typ1,typ2))
  | Apply(e1,e2)->
      begin match type_check te e1 with
      |TArrow(typ1,typ2)->(if((type_check te e2)<>typ1) then raise Type_error else typ2)
      |_-> raise Type_error
    end
  | Div(e1,e2) ->
      begin match type_check te e1 , type_check te e2 with 
      | TInt, TInt-> TInt
      | _ -> raise Type_error
      end
  | Try(exp1, exp2)->
      begin match (type_check te exp1) with
      |temp1-> 
        begin match(type_check te exp2 ) with 
        |TArrow(TInt,temp2)-> if(temp2 = temp1) then temp2 else  raise Type_error
        end
      end
  | RaiseDivByZero(typ, exp)-> typ
;;