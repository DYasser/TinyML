(*
* TinyML
* Eval.fs: evaluator
*)

module TinyML.Eval

open Ast

(*
let incr = fun (x:int) ->
    x + 1 
*)

let rec eval_expr (env : value env) (e : expr) : value =
    match e with
    | Lit lit -> VLit lit

    | Var x ->
        try
            let _, v = List.find (fun (y, _) -> x = y) env
            v
            //addition of not found in env exception 
        with _ -> unexpected_error "eval_expr: the variable <%s> not in environment" (pretty_expr e)

    | Lambda (x, _, e) -> Closure (env, x, e)

    | App (e1, e2) ->
        let v1 = eval_expr env e1
        let v2 = eval_expr env e2
        match v1 with
        | Closure (env1, x, e) -> eval_expr ((x, v2) :: env1) e
        | RecClosure (env1, f, x, e) -> eval_expr ((x, v2) :: (f, v1) :: env1) e
        | _ -> unexpected_error "eval_expr: non-closure in left side of application: %s" (pretty_value v1)
        
    | IfThenElse (e1, e2, None) ->
        let v1 = eval_expr env e1
        match v1 with
        | VLit (LBool true) -> eval_expr env e2
        | VLit (LBool false) -> VLit LUnit
        | _ -> unexpected_error "eval_expr: non-boolean in if guard: %s" (pretty_value v1)
        
    | IfThenElse (e1, e2, Some e3) ->
        let v1 = eval_expr env e1
        eval_expr env (match v1 with
                       | VLit (LBool true) -> e2
                       | VLit (LBool false) -> e3
                       | _ -> unexpected_error "eval_expr: non-boolean in if guard: %s" (pretty_value v1)
                       )
    | Tuple (es) -> VTuple (List.map (eval_expr env) es)

    | Let (x, _, e1, e2) -> 
        let v1 = eval_expr env e1
        eval_expr ((x, v1) :: env) e2

    // let rec f = e1 in e2 
    | LetRec (f, _, e1, e2) -> 
        let v1 = eval_expr env e1
        let vx = (
        //| [] ->// [] base case of the recursion//| x :: xs -> eval_expr xs
            match v1 with
            | Closure (venv1, x, e) -> RecClosure (venv1, f, x, e)
            | _ -> unexpected_error "eval_expr: expected closure in rec binding but got: %s" (pretty_value v1)
        //value:  <|[];exr;x;if x = 0 then 0 else exr 0|>
        )
        //taking f and vs from the operation above and the rest of env to be checked
        eval_expr ((f,vx)::env) e2

    //Variants of binop
    | BinOp (e1, "+", e2) -> binop (+) (+) env e1 e2
    | BinOp (e1, "-", e2) -> binop (-) (-) env e1 e2
    | BinOp (e1, "*", e2) -> binop ( * ) ( * ) env e1 e2
    | BinOp (e1, "/", e2) -> binop ( / ) ( / ) env e1 e2 // added division
    | BinOp (e1, "%", e2) -> binop ( % ) ( % ) env e1 e2 // added modulo
    //| BinOp (e1, "**", e2) -> binop_f ( ** ) env e1 e2 // add power
    //| BinOp (e1, "++", _) -> binop (+) (+) env e1 (Lit (LInt 1)) // add increment
    | BinOp (e1, "<" , e2) -> binop_int_bool (<) (<) env e1 e2 
    | BinOp (e1, "<=", e2) -> binop_int_bool (<=) (<=) env e1 e2 
    | BinOp (e1, ">" , e2) -> binop_int_bool (>) (>)  env e1 e2 
    | BinOp (e1, ">=", e2) -> binop_int_bool (>=) (>=) env e1 e2 
    | BinOp (e1, "=" , e2) -> binop_int_bool (=) (=)  env e1 e2 
    | BinOp (e1, "<>", e2) -> binop_int_bool (<>) (<>) env e1 e2 
    | BinOp (e1, "and", e2) -> binop_bool_bool (&&) env e1 e2
    | BinOp (e1, "or", e2) -> binop_bool_bool (||) env e1 e2

    | UnOp("not", e1) -> negation env e1
    | UnOp ("-", e) ->
        let v = eval_expr env e
        match v with
        | VLit (LInt x) -> VLit (LInt (-x))
        | VLit (LFloat x) -> VLit (LFloat (-x))
        | _ -> unexpected_error "eval_expr: cannot use minus operator on value (%s)" (pretty_value v)

    | _ -> unexpected_error "eval_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e

and negation env e1 = 
    let v = eval_expr env e1
    match v with
    | VLit (LBool b) -> VLit (LBool (not b))
    | _ -> unexpected_error "eval_expr: negation operator not working on non-bool value (%s)" (pretty_value v)

and binop_bool_bool op env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2
    match v1,v2 with
    | VLit (LBool a), VLit (LBool b) -> VLit (LBool (op a b))
    | _ -> unexpected_error "eval_expr: illegal operands in binary operator: %s <op_bool> %s"  (pretty_value v1) (pretty_value v2)

and binop_int_bool op_int op_float env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2
    match v1,v2 with
    | VLit (LInt a), VLit (LInt b) -> VLit (LBool (op_int a b))
    | VLit (LFloat a), VLit (LFloat b) -> VLit (LBool (op_float a b))
    | _ -> unexpected_error "eval_expr: illegal operands in binary operator: %s <op_bool> %s"  (pretty_value v1) (pretty_value v2)

and binop op_int op_float env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2
    match v1, v2 with 
    | VLit (LInt x), VLit (LInt y) -> VLit (LInt (op_int x y))
    | VLit (LFloat x), VLit (LFloat y) -> VLit (LFloat (op_float x y))
    | VLit (LInt x), VLit (LFloat y) -> VLit (LFloat (op_float (float x) y))
    | VLit (LFloat x), VLit (LInt y) -> VLit (LFloat (op_float x (float y)))
    | _ -> unexpected_error "eval_expr: illegal operands in binary operator: %s <op> %s" (pretty_value v1) (pretty_value v2)

(*and binop_one op env e1 =
    let v1 = eval_expr env e1
    let eInt:expr = Lit (LInt 1)
    let eFloat:expr = Lit (LFloat 1.0)
    if (op.CompareTo("+") = 1) then 
        match v1 with
        | VLit (LInt x) -> binop (+) (+) env e1 eInt
        | VLit (LFloat x) -> binop (+) (+) env e1 eFloat
        | _ -> unexpected_error "eval_expr: illegal operands in binary operator <+>: %s" (pretty_value v1)
    else
        VLit (LInt 1)
*)

(*
polymorphism: ('a -> 'b) -> 'a -> 'b

\/ 'a,'b . ('a -> 'b) -> 'a -> 'b
let map = fun f -> fun x -> f x
    
    *)