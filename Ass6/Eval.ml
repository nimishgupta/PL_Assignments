open M_syntax


module Env : sig
  
  type env
  val empty : env
  (* XXX : Why don't we have values like previous assignments, lazy ?? *)
  (* val lookup : id -> env -> exp * env *)
  val lookup : id -> env -> exp

  (* val bind : id -> exp * env -> env -> env *)
  val bind : id -> exp -> env -> env

end = struct
  module IdMap = Identifier.Map

  type env = Env of value IdMap.t
  and value = exp (* * env *)

  let empty = Env IdMap.empty

  let lookup x (Env env) = IdMap.find x env

  (* let bind x (v,e) (Env env) = Env (IdMap.add x (v,e) env) *)
  let bind x v (Env env) = Env (IdMap.add x v env)

end


type context =  
  | Top
  | BinOpR of binOp * exp * context
  | BinOpL of binOp * int * context
  | IfC of exp * exp * context
  | LetV of id * exp * env * context
  | RestoreEnv of env * context
  | AppR   of exp * context
  | AppL   of id * exp * env * context
  | ConsL of exp * context
  | ConsR of exp * context
  | HeadCont of context
  | TailCont of context
  | IsEmptyCont of context
  | TupleCont of exp list * exp list * context
  

let rec is_value (e : exp) : bool = match w with
  | Int _ | Bool _ | Fun _ | Empty _ -> true
  (* Do not impose correctness on types in composite expressions *)
  | Cons (v1, v2) -> is_value v1 && is_value v2
  | Tuple (vlst) -> List.for_all is_value vlst
  | _ -> false


let app_arith_op (op : binOp) (nL : int) (nR : int) : int =
  match binOp with
    | Plus  -> nL + nR
    | Minus -> nL - nR
    | Times -> nL * nR
    | _ -> failwith "Invalid op"

let app_relational_op (op : binOp) (nL : int) (nR : int) : bool =
  match binOp with
    | LT -> nL < nR
    | GT -> nL > nR
    | EQ -> nL = nR
    | _ -> failwith "Invalid op"




let step (e : exp) (cont : context) (env : env) : exp * context * env = match (e, cont) with
  | BinOp (op, eL, eR), cont      -> eL, BinOpR (op, eR, cont), env
  | Int nL, BinOpR (op, eR, cont) -> eR, BinOpL (op, nL, cont), env
  | Int nR, BinOpL (op, eL, cont) ->
      (match op with 
        | Plus | Minus | Times -> Int  (app_arith_op (op, nL, nR)), cont
        | LT   | GT    | EQ    -> Bool (app_relational_op (op, nL, nR)), cont)


  | If (eC, eT, eF), cont -> eC, IfC (eT, eF, cont)
  | Bool b, IfC (eT, eF, cont) -> if b then eT, cont else eF, cont

  | Id x, cont -> 
      let v = lookup x env in v, cont, env


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
      in_e, RestoreEnv (env', cont), bind x v env
  | v, RestoreEnv (env', cont) when is_value v -> v, cont, env'


  (* TODO : Take care of types *)
  | App (e1, e2), cont -> e1, AppR (e2, cont), env
  | Fun (x, t, body), AppR (e2, cont) -> e2, AppL (x, body, env, cont), env
  | v, AppL (x, body, env', cont) when is_value v ->
      body, RestoreEnv (env', cont), bind x v env

  (* TODO *)
  | Fix (x, t, body), AppR (e2, cont) -> failwith "NYI"

  (* List processing *)

  (* TODO : Type Checking? *)

  (* Can the code of list be made more concise *)
  | Head e, cont -> e, HeadCont (cont), env
  | v, HeadCont (cont) when is_value v -> (match v with
      | Empty _ -> failwith "Head of empty list requested"
      | Cons (atm, lst) -> atm, cont, env (* XXX : Subject to condition that type of atm is similar to element of type of list *)
      | _ -> failwith "Expected list")

  | Tail e, cont -> e, TailCont (cont), env
  | v, TailCont (cont) when is_value v -> (match v with
      | Empty _ -> failwith "Tail of empty list requested"
      | Cons (atm, lst) -> lst, cont, env  (* XXX : Subject to condition that type of atm is similar to element of type of list *)
      | _ -> failwith "Expected list")

  | IsEmpty e, cont -> e, IsEmptyCont (cont), env
  | v, IsEmptyCont (cont) when is_value v -> (match v with
     | Empty _ -> Bool true, cont, env
     | Cons _ -> Bool false, cont, env (* XXX : Should we check if types match *)
     | _ -> failwith "Expected list")

  (* XXX : Write Test : Is is_value guard necessary, may cause a infinite recursion when not done *)
  | Cons (atm, lst), cont when !is_value atm || !is_value lst -> atm, ConsR (lst, cont), env
  | vatm, ConsR (lst, cont) when is_value vatm -> lst, ConsL (vatm, cont), env
  | vlst, ConsL (vatm, cont) when is_value vlst -> Cons (vatm, vlst), cont, env


  | Proj (e, n), cont -> e, ProjCont (n, cont), env
  | v, ProjCont (n, cont) when is_value v -> (match v with
      | Tuple (vlist) -> List.nth vlist n, cont, env
      | _ -> failwith "Expected Tuple")


  (* Base case *)
  | Tuple (elist), cont when !is_value e ->
      let open List in hd elist, TupleCont (tl elist, [], cont), env

  (* General case *)
  | v, TupleCont (elist, vlist, cont) when is_value v -> 
      let open List in
        if is_empty elist
        then Tuple (rev v::vlist), cont, env
        else hd elist, TupleCont (tl elist, v::vlist, cont), env

  (* TODO : Reads and Writes *)
  | Read (typ), cont -> (match typ with
      | TInt -> 
      | TBool ->
      | TFun (t1, t2) -> Read 
      | TTuple (tlist) ->
      | TList t ->)

  (* XXX : what exp to return? *)
  (* XXX : Test if Write is capable of printing composite expressions *)
  | Write (v), cont when is_value v -> print_exp v; v, cont, env
  | _ -> failwith "Unexpected control string"
  

let rec run (e : exp) (cont : context) (env : env) = match (e, cont) with
  | v, Top when is_value v -> v
  | e, k -> let (e', k', env') = step e k env in run e' k' env' 
