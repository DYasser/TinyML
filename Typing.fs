(*
* TinyML
* Typing.fs: typing algorithms
*)

//Ctrl + , -> search for variables definitions

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt

type subst = (tyvar * ty) list

//Fresh Type
let mutable fresh_type:tyvar = 0
let new_fresh_ty () = 
    fresh_type <- fresh_type + 1
    fresh_type

//Apply Substitution
//
let rec apply_subst (s : subst) (t : ty) : ty =
    match t with 
    //| TyName s -> TyName s
    | TyName _ -> t
    | TyVar tv ->
        try
            let _, t1 =  List.find(fun (tv1, _) -> tv1 = tv) s
            in t1
        with _ -> t //KeyNotFoundException
    | TyArrow (t1, t2) -> TyArrow(apply_subst s t1, apply_subst s t2)
    | TyTuple ts -> TyTuple (List.map(apply_subst s) ts)
    | TyList tl -> TyList (apply_subst s tl)    //Added subst list
    
let rec apply_subst_scheme (s : subst) (sch : scheme) : scheme =
    match sch with
    | Forall (a, t) ->
        let get_tyvar = List.map (fun (var, _) -> var)
        let varSet = Set a
        let tyvarSet = Set (get_tyvar s) 
        if (Set.intersect varSet tyvarSet).Count > 0
        then unexpected_error "apply_subst_scheme: found 'a' inside the substitution, sch=%s, subst=%s" (pretty_scheme sch) (pretty_subst s)
        else
            Forall (a, apply_subst s t)

let rec apply_subst_env (s : subst) (env : scheme env) : scheme env =
    match env with
    | [] -> []
    | (x, sch)::xs -> (x, apply_subst_scheme s sch)::(apply_subst_env s xs)
// End of apply substitution

//Substitution Composition
//
let compose_subst (s1 : subst) (s2 : subst) : subst = // s1 @ s2 concatenates s1 and s2 lists 
    let apply_s2 = List.map (fun ( x , t) -> ( x , apply_subst s2 t))
    let new_subst = apply_s2 s1 //Apply s2 to s1 types
    
    let var1 = List.map (fun (x, _) -> x) s1
    let var2 = List.map (fun (x, _) -> x) s2
    //let var1 = Set.ofList var1

    let intersect = Set.intersect ( Set.ofList var1 ) (Set.ofList var2) // give commong vars of the two sets
     
    if intersect.Count > 0 // if there is any common 
    then
        let test = ( fun (e:tyvar) ->
            let (_, t1) = List.find (fun (var, _) -> var = e) s1
            let (_, t2) = List.find (fun (var, _) -> var = e) s2
            if t1 <> t2 // domain must be disjoint
                then unexpected_error "compose_subst: not possible to do substitution of s2=%s and s1=%s" (pretty_subst s1) (pretty_subst s2)
        )
        Set.iter test intersect
    let s2 = List.filter (fun (var, _) -> not (Set.contains var intersect)) s2
    new_subst @ s2

//Unification
let rec unify (t1 : ty) (t2 : ty) : subst = 
    match (t1, t2) with
    | TyName ty1, TyName ty2 -> if ( ty1 = ty2 ) then [] else type_error "unify: Cannot unify %s and %s" (ty1) (ty2)
    | TyVar a, t | t, TyVar a ->[a, t]
    | TyArrow (t1, t2), TyArrow (t3, t4) -> 
        let s1 = unify t1 t3
        let t2 = apply_subst s1 t2
        let t4 = apply_subst s1 t4
        let s2 = unify t2 t4
        in compose_subst s1 s2 
    |TyTuple ts1, TyTuple ts2 -> 
        if ( List.length ts1 ) <> ( List.length ts2 ) then type_error "unify: Cannot unify tuples %O and %O because they have different lengths" ts1 ts2

        List.fold(fun s (t1, t2) -> compose_subst s (unify t1 t2)) [] (List.zip ts1 ts2)
        // <> means differs
        //List.fold(fun s (t1, t2) -> compose_subst s (unify t1 t2)) [] (List.zip ts1 ts2)
    | TyList(t1), TyList(t2) -> unify t1 t2
    | _ -> type_error "unify: Cannot unify types %s and %s" (pretty_ty t1) (pretty_ty t2)

//FTVs
//
let rec freevars_ty (t : ty) : tyvar Set =
    //takes a type and produces a set of types
    match t with    //since we have a type we watch it to 5 different outcomes
    | TyName _ -> Set.empty
    | TyVar tv -> Set.singleton tv
    // Set.union or use + between both sets 
    | TyArrow (t1, t2) -> Set.union (freevars_ty t1) (freevars_ty t2)
    | TyTuple ts -> List.fold (fun set t -> Set.union set (freevars_ty t)) Set.empty ts 
    | TyList x -> freevars_ty x

let freevars_scheme (Forall (tvs, t)) =
    // Set.difference or use - between both sets 
    Set.difference (freevars_ty t) (Set.ofList tvs)

let rec freevars_scheme_env env =
    match env with
        | [] -> Set.empty
        | (_,sch)::r -> Set.union (freevars_scheme sch) (freevars_scheme_env r)
//End of FTVs

//generalization
let generalization env t :scheme = 
    let var = Set.difference (freevars_ty t) (freevars_scheme_env env)
    Forall (Set.toList var, t)

//instantiation
let rec instantiation (s:scheme) : ty =
    match s with
    | Forall (var, t) ->
        let toBeRefresh = Set.intersect (freevars_ty t) (Set var)// build up a substitution mapping each of the type variable that needs to
                    // be refresh, in a new fresh type variable
        let new_fresh = (fun v -> (v, TyVar(new_fresh_ty ())))
        let sub = List.map new_fresh (List.sort (Set.toList toBeRefresh))
        apply_subst sub t
    //| _ -> unexpected_error "instantiation: not an instatiation"

let gamma0 = [
    ("+", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("-", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
]


// type inference
//
let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    match e with
    | Lit (LInt _) -> TyInt, []
    //| Lit (LInt _) -> TyChar, subst.Empty
    | Lit (LFloat _) -> TyFloat, []
    | Lit (LString _) -> TyString, []
    | Lit (LChar _) -> TyChar, []
    | Lit (LBool _) -> TyBool, []
    | Lit LUnit -> TyUnit, []
    
    | Var x ->
        try
            let _, sch = List.find (fun (y, _) -> x = y) env
            (instantiation (sch), [])
        with _ -> type_error "typeinfer_expr: unkown variable <%s>" x


    | Lambda (x, None, e1) ->
        // (t1) -> (t2)
        let fresh = new_fresh_ty ()
        let local_env = (x,Forall ([], TyVar fresh))::env
        let t2, s = typeinfer_expr local_env e1 
        let t1 = apply_subst s (TyVar fresh)
        (TyArrow (t1, t2), s)

    | Lambda (x, Some t, e1) ->
            let env = (x,Forall ([], t))::env
            let t1, s1 = typeinfer_expr env e1
            (TyArrow (t, t1), s1)

    | App (e1, e2) ->
        let fresh = new_fresh_ty ()
        let t1, s1 = typeinfer_expr env e1
        let local_env = apply_subst_env s1 env
        let t2, s2 = typeinfer_expr local_env e2
        let t1 = apply_subst s2 t1
        let t3 = TyArrow (t2, TyVar fresh)
        let s3 = unify t1 t3
        let s = compose_subst s3 (compose_subst s2 s1) 
        (apply_subst s3 (TyVar fresh), s)

    
    | Let (x, None, e1, e2) ->
        let t1, s1 = typeinfer_expr env e1
        let env = apply_subst_env s1 env
        let sch = generalization env t1 
        let env = (x,sch)::env
        let t2, s2 = typeinfer_expr env e2
        let s = compose_subst s2 s1
        (t2, s)
    | Let (x, Some t, e1, e2) ->
        let t1, s1 = typeinfer_expr env e1
        let su = unify t1 t
        let s = compose_subst su s1
        let env = (x,Forall ([], t))::env
        let env = apply_subst_env s env
        let t2, s2 = typeinfer_expr env e2
        let s = compose_subst s2 s
        (t2, s)
    (*| Let(x, tyo, e1, e2) ->
        let t1, s1 = typeinfer_expr env e1
        //FTVs, free type variables
        let tvs = freevars_ty t1 - freevars_scheme_env env
        //sch-> type scheme (sigma)
        let sch = Forall (Set.toList tvs, t1)
        let t2, s2 = typeinfer_expr ((x,sch)::env) e2
        t2, compose_subst s2 s1
    *)

    | IfThenElse (e1, e2, e3o) ->
        let t1, s1 = typeinfer_expr env e1
        let s2 = unify t1 TyBool

        let s3 = compose_subst s2 s1 //errors handled by compose_subst

        let local_env = apply_subst_env s3 env 
        let t2, s4 = typeinfer_expr local_env e2

        let s5 = compose_subst s4 s3

        match e3o with
        | None ->
            let su = unify t2 TyUnit
            let s = compose_subst su s5

            (TyUnit, s)
        | Some e3 ->
            let env = apply_subst_env s5 env
            let t3, s6 = typeinfer_expr env e3

            let t2 = apply_subst s6 t2 
            let s8 = unify t2 t3

            let s9 = compose_subst s8 (compose_subst s6 s5)

            (apply_subst s8 t3, s9)

    | Tuple es ->
        let state = List.fold (fun state e ->
            match state with
            | (env, s, ts) ->
                let local_env = apply_subst_env s env
                let t1, s1 = typeinfer_expr local_env e
                let ts = List.map (fun t -> apply_subst s1 t) ts
                let s = compose_subst s1 s
                let ts = ts @ [t1]
                (local_env, s, ts)) (env, [], []) es
        let (env, subst, ts) = state 
        (TyTuple ts, subst)
    | LetRec (f, Some y, e1, e2)->
        let init = TyArrow (TyVar (new_fresh_ty ()), TyVar (new_fresh_ty ()))

        let local_env1 = (f,Forall ([], init))::env
        let t1, s1 = typeinfer_expr local_env1 e1
        let init = apply_subst s1 init 
        let su = unify init t1             

        let t1 = apply_subst su t1       
        let s = compose_subst su s1

        let local_env2 = apply_subst_env s env
        let local_env2 = (f, generalization local_env2 t1)::local_env2
        let t2, s2 = typeinfer_expr local_env2 e2

        let s = compose_subst s2 s
        (t2, s)
    | LetRec (f, None, e1, e2) ->
        let init = TyArrow (TyVar (new_fresh_ty ()), TyVar (new_fresh_ty ()))

        let local_env1 = (f,Forall ([], init))::env
        let t1, s1 = typeinfer_expr local_env1 e1
        let init = apply_subst s1 init 
        let su = unify init t1             

        let t1 = apply_subst su t1       
        let s = compose_subst su s1

        let local_env2 = apply_subst_env s env
        let local_env2 = (f, generalization local_env2 t1)::local_env2
        let t2, s2 = typeinfer_expr local_env2 e2

        let s = compose_subst s2 s
        (t2, s)
     
    | BinOp (e1, ("+" | "-" | "*" | "/" | "%" as op), e2) ->
        operate env e1 e2 op
    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
        compare env e1 e2 op
    | BinOp (e1, ("and" | "or"), e2) ->
        binop TyBool TyBool env e1 e2
    | BinOp (_, op, _) -> unexpected_error "typeinfer_expr: unsupported binary operator (%s)" op

    | UnOp ("not", e) ->
        unop TyBool TyBool env e
    | UnOp ("-", e) ->
        negation env e

    | UnOp (op, _) -> unexpected_error "typeinfer_expr: unsupported unary operator (%s)" op

 
    | _ -> unexpected_error "typeinfer_expr: not recognized expression: %s" (pretty_expr e)
//End of TypeInference

(*and binop_2 op_int op_float env e1 e2 =
    let t1, s1 = typeinfer_expr env e1
    let t2, s2 = typeinfer_expr env e2
    match t1, t2 with 
    | (x) ,  (y) ->  (TyInt,[])
    | TyFloat x, TyFloat y -> (TyInt,[])
    | TyInt x , TyFloat y -> (TyInt,[])
    | TyFloat x, TyInt y -> (TyInt,[])
    | _ -> unexpected_error "eval_expr: illegal operands in binary operator <op>: %s + %s" (pretty_ty t1) (pretty_ty t2)
  *)  

and operate env e1 e2 op= 
    let t1, s1 = typeinfer_expr  env e1
    let t2, s2 = typeinfer_expr  env e2
    match t1,t2 with
    | TyInt, TyInt -> binop TyInt TyInt env e1 e2
    | TyFloat, TyFloat -> binop TyFloat TyFloat env e1 e2
    | TyInt, TyFloat | TyFloat, TyInt  -> unexpected_error "operate: operation (%s) between int and float not supported" op
    | _ , TyInt -> binop TyInt TyInt env e1 e2
    | _ , TyFloat -> binop TyFloat TyFloat env e1 e2
    | TyInt, _ -> binop TyInt TyInt env e1 e2
    | TyFloat, _ -> binop TyFloat TyFloat env e1 e2
    | _ -> unexpected_error "operate: unsupported binary operation (%s) between %s and %s" op (pretty_ty t1) (pretty_ty t2)

and compare env e1 e2 op=
    let t1, s1 = typeinfer_expr  env e1
    let t2, s2 = typeinfer_expr  env e2
    match t1,t2 with
    | TyInt, TyInt -> binop TyInt TyBool env e1 e2
    | TyFloat, TyFloat -> binop TyFloat TyBool env e1 e2
    | TyInt, TyFloat | TyFloat, TyInt  -> unexpected_error "compare: comparison (%s) between int and float not supported" op
    | _ , TyInt -> binop TyInt TyBool env e1 e2
    | _ , TyFloat -> binop TyFloat TyBool env e1 e2
    | TyInt, _ -> binop TyInt TyBool env e1 e2
    | TyFloat, _ -> binop TyFloat TyBool env e1 e2
    | _ -> unexpected_error "compare: unsupported binary operation (%s) with expressions: %s, %s" op (pretty_ty t1 ) (pretty_expr e2)
   
and negation env e=
    let t, s = typeinfer_expr env e
    match t with
    | TyInt -> unop TyInt TyInt env e
    | TyFloat -> unop TyFloat TyFloat env e
    | _ -> unexpected_error "negation: unsupported unary operation (%s) with %s" "-" (pretty_expr e)


and binop e res env e1 e2 =
    let t1, s1 = typeinfer_expr  env e1
    let s2 = unify t1 e
    let s3 = compose_subst s2 s1
    let env = apply_subst_env s3 env

    let t2, s4 = typeinfer_expr  env e2
    let s5 = unify t2 e
    let s6 = compose_subst s5 s4
    (res, s6)

and unop eType resType env exp =
    let t, s = typeinfer_expr env exp
    let su = unify t eType
    let s = compose_subst su s
    (resType, s)

// Type Checker
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
