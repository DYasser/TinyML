(*
* TinyML
* Typing.fs: typing algorithms
*)

//Ctrl + , -> search for variables definitions

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt

type subst = (tyvar * ty) list

// TODO implement this
let compose_subst (s1 : subst) (s2 : subst) : subst = s1 @ s2 //@ means append (wrong obv)

// TODO Continue implementing this
let rec unify (t1 : ty) (t2 : ty) : subst = 
    match (t1, t2) with
    | TyName s1, TyName s2 when s1 = s2 -> []
    | TyVar tv, t
    | t, TyVar tv ->[tv, t]
    | TyArrow (t1, t2), TyArrow (t3, t4) -> 
        let s1 = unify t1 t3
        let s2 = unify t2 t4
        in
            compose_subst s1 s2 
    |TyTuple ts1, TyTuple ts2 when List.length ts1  = List.length ts2 -> 
        List.fold(fun s (t1, t2) -> compose_subst s (unify t1 t2)) [] (List.zip ts1 ts2)
        // <> means differs
        //if List.length ts1 <> List.length ts2 then type_error "cannot unify tuples %O and %O because they have different lengths" ts1 ts2
        //List.fold(fun s (t1, t2) -> compose_subst s (unify t1 t2)) [] (List.zip ts1 ts2)
    | _ -> type_error "Cannot unify types %O and %O" t1 t2

// TODO Continue implementing this
let rec apply_subst (s : subst) (t : ty) : ty =
    match t with 
//    | TyName s -> TyName s
    | TyName _ -> t
    | TyArrow (t1, t2) -> TyArrow(apply_subst s t1, apply_subst s t2)
    | TyVar tv ->
        try
            let _, t1 =  List.find(fun (tv1, _) -> tv1 = tv) s
            in t1
        with KeyNotFoundException -> t 
    | TyTuple ts ->
        TyTuple (List.map(apply_subst s) ts)


//takes a type and produces a set of types
let rec freevars_ty (t : ty) : tyvar Set =
    match t with    //since we have a type we watch it to 4 different outcomes
    | TyName _ -> Set.empty
    // Set.union or use + between both sets 
    | TyArrow (t1, t2) -> Set.union (freevars_ty t1) (freevars_ty t2)
    | TyVar tv -> Set.singleton tv
    | TyTuple ts -> List.fold (fun set t -> Set.union set (freevars_ty t)) Set.empty ts 

let freevars_scheme (Forall (tvs, t)) =
    // Set.difference or use - between both sets 
    Set.difference (freevars_ty t) (Set.ofList tvs)
    
let freevars_scheme_env env =
    List.fold (fun r (_, sch) -> r + freevars_scheme sch) Set.empty env

// type inference
//

let gamma0 = [
    ("+", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("-", TyArrow (TyInt, TyArrow (TyInt, TyInt)))

]

// TODO Continuing implementing
let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    match e with
    | Lit (LInt _) -> TyInt, []
    //| Lit (LInt _) -> TyChar, subst.Empty
    | Lit (LFloat _) -> TyFloat, []
    | Lit (LString _) -> TyString, []
    | Lit (LChar _) -> TyChar, []
    | Lit (LBool _) -> TyBool, []
    | Lit LUnit -> TyUnit, []
    
    | Let(x, tyo, e1, e2) ->
        let t1, s1 = typeinfer_expr env e1
        //FTVs, free type variables
        let tvs = freevars_ty t1 - freevars_scheme_env env
        //sch-> type scheme (sigma)
        let sch = Forall (Set.toList tvs, t1)
        let t2, s2 = typeinfer_expr ((x,sch)::env) e2
        t2, compose_subst s2 s1

    | _ -> failwith "Not Completed"
// type checker
//
    
let rec typecheck_expr (env : ty env) (e : expr) : ty =
    match e with
    | Lit (LInt _) -> TyInt
    | Lit (LFloat _) -> TyFloat
    | Lit (LString _) -> TyString
    | Lit (LChar _) -> TyChar
    | Lit (LBool _) -> TyBool
    | Lit LUnit -> TyUnit

    | Var x ->
        let _, t = List.find (fun (y, _) -> x = y) env
        t

    | Lambda (x, None, e) -> unexpected_error "typecheck_expr: unannotated lambda is not supported"
    
    | Lambda (x, Some t1, e) ->
        let t2 = typecheck_expr ((x, t1) :: env) e
        TyArrow (t1, t2)

    | App (e1, e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1 with
        | TyArrow (l, r) ->
            if l = t2 then r 
            else type_error "wrong application: argument type %s does not match function domain %s" (pretty_ty t2) (pretty_ty l)
        | _ -> type_error "expecting a function on left side of application, but got %s" (pretty_ty t1)

    | Let (x, tyo, e1, e2) -> //tyo => type option
        let t1 = typecheck_expr env e1
        match tyo with
        | None -> ()
        | Some t -> if t <> t1 then type_error "type annotation in let binding of %s is wrong: exptected %s, but got %s" x (pretty_ty t) (pretty_ty t1)
        typecheck_expr ((x, t1) :: env) e2

    | IfThenElse (e1, e2, e3o) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyBool then type_error "if condition must be a bool, but got a %s" (pretty_ty t1)
        let t2 = typecheck_expr env e2
        match e3o with
        | None ->
            if t2 <> TyUnit then type_error "if-then without else requires unit type on then branch, but got %s" (pretty_ty t2)
            TyUnit
        | Some e3 ->
            let t3 = typecheck_expr env e3
            if t2 <> t3 then type_error "type mismatch in if-then-else: then branch has type %s and is different from else branch type %s" (pretty_ty t2) (pretty_ty t3)
            t2

    | Tuple es ->
        TyTuple (List.map (typecheck_expr env) es)

    | LetRec (f, None, e1, e2) ->
        unexpected_error "typecheck_expr: unannotated let rec is not supported"
        
    | LetRec (f, Some tf, e1, e2) ->
        let env0 = (f, tf) :: env
        let t1 = typecheck_expr env0 e1
        match t1 with
        | TyArrow _ -> ()
        | _ -> type_error "let rec is restricted to functions, but got type %s" (pretty_ty t1)
        if t1 <> tf then type_error "let rec type mismatch: expected %s, but got %s" (pretty_ty tf) (pretty_ty t1)
        typecheck_expr env0 e2

    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> TyInt
        | TyFloat, TyFloat -> TyFloat
        | TyInt, TyFloat
        | TyFloat, TyInt -> TyFloat
        | _ -> type_error "binary operator expects two int operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        
    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> ()
        | _ -> type_error "binary operator expects two numeric operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool

    | BinOp (e1, ("and" | "or" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyBool, TyBool -> ()
        | _ -> type_error "binary operator expects two bools operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool

    | BinOp (_, op, _) -> unexpected_error "typecheck_expr: unsupported binary operator (%s)" op

    | UnOp ("not", e) ->
        let t = typecheck_expr env e
        if t <> TyBool then type_error "unary not expects a bool operand, but got %s" (pretty_ty t)
        TyBool
            
    | UnOp ("-", e) ->
        let t = typecheck_expr env e
        match t with
        | TyInt -> TyInt
        | TyFloat -> TyFloat
        | _ -> type_error "unary negation expects a numeric operand, but got %s" (pretty_ty t)

    | UnOp (op, _) -> unexpected_error "typecheck_expr: unsupported unary operator (%s)" op

    | _ -> unexpected_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
