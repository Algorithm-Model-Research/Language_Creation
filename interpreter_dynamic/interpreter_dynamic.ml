open List

type typ = 
	| TBool 
	| TInt 
	| TArrow of typ * typ

type type_environment = (string*typ) list



type exp =
  | True
  | False
  | If of exp * exp * exp
  | Num of int
  | IsZero of exp
  | Plus of exp * exp
  | Mult of exp * exp
  | Var of string
  | Lambda of string * exp
  | Apply of exp * exp
  | Let of string * exp * exp
  | TypeError
  type environment = (string * exp) list

exception Eval_error 
exception Subsitution_error

let rec step(env: environment) (e:exp) = match e with
    |True -> (env,True)
    |False -> (env,False)
    |Num(e)-> (env,Num(e))
    |Lambda(x,e)->(env,Lambda(x,e))
    |Let(x,e1,e2)-> (env, Apply(Lambda(x,e2),e1)) 
    |TypeError->(env,TypeError)
    |Var(str) -> 
        begin match env with
         |[]-> (env,TypeError)
         |(s,e2) :: tl-> if(s = str) then (env,e2) else (step tl (Var(str)) )
         |_-> (env,TypeError)
         end
    |IsZero(e)->
              begin match e with
             |Num(e1)-> if ((e1)==0) then (env,True) else (env,False)
             |True->(env,TypeError)
             |False->(env,TypeError)
             |TypeError->(env,TypeError)
             |Lambda(x,e)->(env,TypeError)
             |_-> let (envtemp,temp) = (step env e) in (envtemp@env,IsZero(temp))
              end
    |Plus(e1,e2) ->
        begin match e1 with 
          |Num(n1) ->
                begin match e2 with
                 | Num(n2) -> (env,Num(n1+n2))
                 |True-> (env,TypeError)
                 |False->(env,TypeError)
                 |Lambda(x,e)-> (env,TypeError)
                 |TypeError->(env,TypeError)
                 | _-> let (envtemp,temp) = (step env e2) in (envtemp@env,Plus(e1,temp))
                end
          |True-> (env,TypeError)
          |False->(env,TypeError)
          |Lambda(x,e)->(env,TypeError)
          |TypeError->(env,TypeError)
          |_-> let (envtemp,temp) = (step env e1) in (envtemp@env,Plus(temp,e2))
          end
    |Mult(e1,e2)->
        begin match e1 with 
         |Num(n1) ->
                begin match e2 with
                | Num(n2) -> (env,Num(n1*n2))
                | False->(env,TypeError)
                | True->(env,TypeError)
                | Lambda(x,e)->(env,TypeError)
                | TypeError->(env,TypeError)
                | _-> let (envtemp,temp) = (step env e2) in (envtemp@env,Mult(e1,temp))
                end
             |True->(env,TypeError)
             |False->(env,TypeError)
             |Lambda(x,e)->(env,TypeError)
             |TypeError->(env,TypeError)
             |_-> let (envtemp,temp) = (step env e1) in (envtemp@env,Mult(temp,e2))
              end
   |If(e,e2,e3)->
     begin match e with
     |Num(n) ->  (env, TypeError)
     |True->(env,e2)
     |False->(env,e3)
     |TypeError-> (env,TypeError)
     |Lambda(x,e)->(env,TypeError)
     |_->let (envtemp,temp) = (step env e) in (envtemp@env,If(temp,e2,e3))
      end
    |Apply(exp1,exp2)-> 
        begin match exp1 with
        |Lambda(x, et)->
          begin match exp2 with
          |True -> ((x,True)::env,et)
          |False -> ((x,False)::env,et)
          |Num(e2)-> ((x,Num(e2))::env,et)
          |Lambda(x',temp)->(((x,Lambda(x',temp))::env),et)
          |TypeError->(env,TypeError)
          |_->let (envtemp,temp) = (step env exp2) in (((x,temp)::env),Apply(exp1,temp))
          end
        |True->(env,TypeError)
        |False->(env,TypeError)
        |Num(e1)->(env,TypeError)
        |TypeError->(env,TypeError)
        |_->let (envtemp,temp) = (step env exp1) in (env,Apply(temp,exp2))
        end
   
   let rec multi_step (env:environment)(e:exp) = match e with
        |True -> (env,True)
        |False -> (env,False)
        |Num(e)->  (env,Num(e))
        |Var(str)->(env,Var(str))
        |Lambda(x, e)-> (env,Lambda(x,  e))
        |TypeError->(env,TypeError)
        |If(e1,e2,e3) -> let (env,temp) = (step env e) in (multi_step env temp )
        |IsZero(e) -> let (env,temp) = (step env e) in (multi_step env temp )
        |Plus(e1,e2) -> let (env,temp) = (step env e) in (multi_step env temp )
        |Mult(e1,e2)-> let (env,temp) = (step env e) in (multi_step env temp )
        |Apply(exp1,exp2)-> let (env,temp) = (step env e) in (multi_step env temp )
        |Let(x, exp1,exp2)-> let (env,temp) = (step env e) in (multi_step env temp )
        


