open M_syntax


(* TODO : Make a functor on exp and typ *)
module ExpEnv : 

sig
  
  type env

  val empty : env

  val lookup : id -> env -> value

  val bind : id -> value -> env -> env

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

  val lookup : id -> env -> value

  val bind : id -> value -> env -> env

end = struct

  module IdMap = Identifier.Map

  type env = TypEnv of value IdMap.t
  and value = typ (* TODO : Parameterize *) 

  let empty = TypEnv IdMap.empty

  let lookup x (TypEnv env) = IdMap.find x env

  let bind x v (TypEnv env) = TypEnv (IdMap.add x v env)

end



let rec type_of (env : TypEnv.env) (e : exp) : typ = match e with
  | Int _ -> TInt
  | Bool _ -> TBool

  | BinOp op, e1, e2-> (match type_of e1 env, type_of e2 env with
      | TInt, TInt when op = Plus || op = Minus || op = Times -> TInt
      | TInt, TInt when op = LT || op = GT || op = EQ -> TBool
      | _ -> failwith "Type Error")

  | If (e1, e2 ,e3) -> 
      let t_cond = type_of e1 env in
      let t_true = type_of e2 env in
      let t_false = type_of e3 env in
        if TBool = t_cond && t_true = t_false then TBool
        else failwith "Type Error"

  | Id x -> TypEnv.lookup x env

  | Let (x, with_e, in_e) ->
      let env' = TypEnv.bind x (type_of with_e env) in type_of in_e env'

  | Fun (x, t, b) -> let env' = TypEnv.bind x t in TFun (t, type_of b env')

  | Fix (x, t, b) -> "NYI"

  | App (e1, e2) -> (match type_of e1 env with
      | TFun (t1, t2) -> if type_of e2 env = t1 then t2 else failwith "Type Error"
      | _ -> failwith "Type Error")

  | Empty t -> TList t

  | Cons (e1, e2) -> (match type_of e2 env with
      | TList t -> if t = type_of e1 env then TList t else failwith "Type Error"
      | _ -> failwith "Type Error")

  | Head e -> (match type_of e env with
      | TList t -> t
      | _ -> failwith "Type Error")

  | Tail e -> (match type_of e env with
      | TList t -> TList t
      | _ -> failwith "Type Error")

  | IsEmpty e -> (match type_of e env with
      | TList t -> TBool
      | _ -> failwith "Type Error")

  | Tuple (e_list) -> TTuple (List.map (type_of env) e_list)

  | Proj (e, i) -> (match type_of e env with
      | TTuple (t_list) -> List.nth t_list i
      | _ -> failwith "Type Error")

  | _ -> "Type Error"
      


let type_of (e : exp) : typ = _type_of TypEnv.empty e


(* TODO : Rename consistently *)
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




let step (e : exp) 
         (cont : context)
         (env : ExpEnv.env) : exp * context * ExpEnv.env = match (e, cont) with
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


  | App (e1, e2), cont -> e1, AppR (e2, cont), env
  | Fun (x, t, body), AppR (e2, cont) when t = type_of e2 -> e2, AppL (x, body, env, cont), env
  | v, AppL (x, body, env', cont) when is_value v ->
      body, RestoreEnv (env', cont), bind x v env

  (* TODO *)
  | Fix (x, t, body), AppR (e2, cont) -> failwith "NYI"

  (* List processing *)

  (* Can the code of list be made more concise *)
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
     | Cons atm, lst -> (match type_of atm, type_of lst with
         | t1, TList t2 when t1 = t2 -> Bool false, cont, env
         | _ -> failwith "Type Error : Cons Type mismatch")
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

  | Read (typ), cont -> (match parse (read_line ()) with
     | ParseError err -> failwith err
     | Exp e' when is_value e' && typ = type_of e' -> e', cont, env
     | _ -> failwith "Not a value")

  (* XXX : what exp to return? *)
  (* XXX : Test if Write is capable of printing composite expressions *)
  (* TODO : Check if print_exp prints a new line after the expression *)
  | Write (v), cont when is_value v -> print_exp v; v, cont, env

  | _ -> failwith "Unexpected Expression : Check your types"
  

let rec run (e : exp) (cont : context) (env : env) = match (e, cont) with
  | v, Top when is_value v -> v
  | e, k -> let (e', k', env') = step e k env in run e' k' env' 
