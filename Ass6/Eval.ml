open M_syntax


(* TODO : Make a functor on exp and typ *)
module ExpEnv : 

sig
  
  type env

  val empty : env

  val lookup : id -> env -> exp

  val bind : id -> exp -> env -> env

end = struct

  module IdMap = Identifier.Map

  type env = ExpEnv of value IdMap.t
  and value = exp (* TODO : Parameterize *) 

  let empty = ExpEnv IdMap.empty

  let lookup x (ExpEnv env) = IdMap.find x env

  let bind x v (ExpEnv env) = ExpEnv (IdMap.add x v env)

end


(* TODO : Parameterized module *)
module TypEnv : 

sig
  
  type env

  val empty : env

  val lookup : id -> env -> typ

  val bind : id -> typ -> env -> env

end = struct

  module IdMap = Identifier.Map

  type env = TypEnv of value IdMap.t
  and value = typ (* TODO : Parameterize *) 

  let empty = TypEnv IdMap.empty

  let lookup x (TypEnv env) = IdMap.find x env

  let bind x v (TypEnv env) = TypEnv (IdMap.add x v env)

end



let rec _type_of (env : TypEnv.env) (e : exp) : typ = match e with
  | Int _ -> TInt
  | Bool _ -> TBool

  | BinOp (op, e1, e2) -> (match _type_of env e1, _type_of env e2 with
      | TInt, TInt when op = Plus || op = Minus || op = Times -> TInt
      | TInt, TInt when op = LT || op = GT || op = EQ -> TBool
      | _ -> failwith "Type Error")

  | If (e1, e2 ,e3) -> 
      let t_cond = _type_of env e1 in
      let t_true = _type_of env e2 in
      let t_false = _type_of env e3 in
        if TBool = t_cond && t_true = t_false then t_true
        else failwith "Type Error"

  | Id x -> TypEnv.lookup x env

  | Let (x, with_e, in_e) ->
      let env' = TypEnv.bind x (_type_of env with_e) env in _type_of env' in_e

  | Fun (x, t, b) -> let env' = TypEnv.bind x t env in TFun (t, _type_of env' b)

  (* TODO *)
  | Fix (x, t, b) -> failwith "NYI"

  | App (e1, e2) -> (match _type_of env e1 with
      | TFun (t1, t2) when _type_of env e2 = t1 -> t2
      | _ -> failwith "Type Error")

  | Empty t -> TList t

  | Cons (e1, e2) -> (match _type_of env e2 with
      | TList t when _type_of env e1 = t -> TList t
      | _ -> failwith "Type Error")

  | Head e -> (match _type_of env e with
      | TList t -> t
      | _ -> failwith "Type Error")

  | Tail e -> (match _type_of env e with
      | TList t -> TList t
      | _ -> failwith "Type Error")

  | IsEmpty e -> (match _type_of env e with
      | TList t -> TBool
      | _ -> failwith "Type Error")

  | Tuple (e_list) -> TTuple (List.map (_type_of env) e_list)

  | Proj (e, i) -> (match _type_of env e with
      | TTuple (t_list) -> List.nth t_list i
      | _ -> failwith "Type Error")

  | _ -> failwith "Type Error"
      


let type_of (e : exp) : typ = _type_of TypEnv.empty e


(* TODO : Rename consistently *)
type context =  
  | Top
  | BinOpR      of binOp * exp * context
  | BinOpL      of binOp * int * context
  | IfC         of exp * exp * context
  | LetV        of id * exp * ExpEnv.env * context
  | RestoreEnv  of ExpEnv.env * context
  | AppR        of exp * context
  | AppL        of id * exp * ExpEnv.env * context
  | ConsL       of exp * context
  | ConsR       of exp * context
  | HeadCont    of context
  | TailCont    of context
  | IsEmptyCont of context
  | ProjCont    of int * context
  | TupleCont   of exp list * exp list * context
  

let rec is_value (e : exp) : bool = match e with
  | Int _ | Bool _ | Fun _ | Empty _ -> true
  | Cons (v1, v2) -> is_value v1 && is_value v2
  | Tuple (vlst) -> List.for_all is_value vlst
  | _ -> false


let app_arith_op (op : binOp) (nL : int) (nR : int) : int =
  match op with
    | Plus  -> nL + nR
    | Minus -> nL - nR
    | Times -> nL * nR
    | _ -> failwith "Invalid op"

let app_relational_op (op : binOp) (nL : int) (nR : int) : bool =
  match op with
    | LT -> nL < nR
    | GT -> nL > nR
    | EQ -> nL = nR
    | _ -> failwith "Invalid op"


let step (e : exp) 
         (cont : context)
         (env : ExpEnv.env) : exp * context * ExpEnv.env = match (e, cont) with
  | BinOp (op, eL, eR), cont      -> eL, BinOpR (op, eR, cont), env
  | Int nL, BinOpR (op, eR, cont) -> eR, BinOpL (op, nL, cont), env
  | Int nR, BinOpL (op, nL, cont) -> (match op with 
        | Plus | Minus | Times -> Int  (app_arith_op op nL nR), cont, env
        | LT   | GT    | EQ    -> Bool (app_relational_op op nL nR), cont, env)


  | If (eC, eT, eF), cont -> eC, IfC (eT, eF, cont), env
  | Bool b, IfC (eT, eF, cont) -> if b then eT, cont, env else eF, cont, env

  | Id x, cont -> 
      let v = ExpEnv.lookup x env in v, cont, env

  (* Invariant for Let bindings : We want to restore the environment after evaluating
   * in_e expression
   *
   * Consider the two cases
   *   Let x = 1 in 
   *     Let y = 2 in
   *       x + y
   *
   *   Let y = 2 in
   *     Let x = 1 in
   *       x + y
   *)
  | Let (x, with_e, in_e), cont -> with_e, LetV (x, in_e, env, cont), env
  | v, LetV (x, in_e, env', cont) when is_value v -> 
      in_e, RestoreEnv (env', cont), ExpEnv.bind x v env
  | v, RestoreEnv (env', cont) when is_value v -> v, cont, env'


  | App (e1, e2), cont -> e1, AppR (e2, cont), env
  | Fun (x, t, body), AppR (e2, cont) when t = type_of e2 -> e2, AppL (x, body, env, cont), env
  | v, AppL (x, body, env', cont) when is_value v ->
      body, RestoreEnv (env', cont), ExpEnv.bind x v env

  (* TODO *)
  | Fix (x, t, body), AppR (e2, cont) -> failwith "NYI"

  (* List processing *)

  | Head e, cont -> e, HeadCont (cont), env
  | v, HeadCont (cont) when is_value v -> (match v with
      | Empty _ -> failwith "Head of empty list requested"
      | Cons (atm, lst) -> (match type_of atm, type_of lst with 
          | t1, TList t2 when t1 = t2 -> atm, cont, env
          | _ -> failwith "Type Error : Cons type mismatch")
      | _ -> failwith "Type Error : Expected list")

  | Tail e, cont -> e, TailCont (cont), env
  | v, TailCont (cont) when is_value v -> (match v with
      | Empty _ -> failwith "Tail of empty list requested"
      | Cons (atm, lst) -> (match type_of atm, type_of lst with
          | t1, TList t2 when t1 = t2 -> lst, cont, env
          | _ -> failwith "Type Error : Cons type mismatch")
      | _ -> failwith "Type Error : Expected list")

  | IsEmpty e, cont -> e, IsEmptyCont (cont), env
  | v, IsEmptyCont (cont) when is_value v -> (match v with
     | Empty _ -> Bool true, cont, env
     | Cons (atm, lst) -> (match type_of atm, type_of lst with
         | t1, TList t2 when t1 = t2 -> Bool false, cont, env
         | _ -> failwith "Type Error : Cons Type mismatch")
     | _ -> failwith "Expected list")

  (* XXX : Write Test : Is is_value guard necessary, may cause a infinite recursion when not done *)
  | Cons (atm, lst), cont when not (is_value atm && is_value lst) -> atm, ConsR (lst, cont), env
  | vatm, ConsR (lst, cont) when is_value vatm -> lst, ConsL (vatm, cont), env
  | vlst, ConsL (vatm, cont) when is_value vlst -> Cons (vatm, vlst), cont, env


  | Proj (e, n), cont -> e, ProjCont (n, cont), env
  | v, ProjCont (n, cont) when is_value v -> (match v with
      | Tuple (vlist) -> List.nth vlist n, cont, env
      | _ -> failwith "Expected Tuple")


  (* Base case *)
  | Tuple (elist), cont when not (is_value e) ->
      let open List in hd elist, TupleCont (tl elist, [], cont), env

  (* General case *)
  | v, TupleCont (elist, vlist, cont) when is_value v -> let open List in
      if [] = elist then Tuple (rev (v::vlist)), cont, env
      else hd elist, TupleCont (tl elist, v::vlist, cont), env

  | Read (typ), cont -> (match M_util.parse (read_line ()) with
     | M_util.ParseError err -> failwith err
     | M_util.Exp e' when is_value e' && typ = type_of e' -> e', cont, env
     | _ -> failwith "Not a value")

  (* XXX : what exp to return when printing? *)
  (* XXX : Test if Write is capable of printing composite expressions *)
  (* TODO : Check if print_exp prints a new line after the expression *)
  | Write (v), cont when is_value v -> M_util.print_exp v; v, cont, env

  | _ -> failwith "Unexpected Expression : Check your types"
  

let rec run (e : exp) (cont : context) (env : ExpEnv.env) = match (e, cont) with
  | v, Top when is_value v -> v
  | e, k -> let (e', k', env') = step e k env in run e' k' env' 
