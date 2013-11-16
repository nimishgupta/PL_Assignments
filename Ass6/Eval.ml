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
(*  | AppR   of exp * context *)
(*  | AppL   of id * exp * env * context *)
  

let is_val (e : exp) : bool = match w with
  | Int _ | Bool _ | Fun _ | Tuple _ | List _ -> true
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
      (* (* Make sure to restore old environment after extracting x from it *)
      let (v, env') = lookup x env in v, cont, env' *)

      (* We now have an explicit continuation to restore the environment whenever required *)
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

  (* Should I store the environment at the time of let exp *)
  | Let (x, with_e, in_e), cont -> with_e, LetV (x, in_e, env, cont), env
  | v, LetV (x, in_e, env', cont) when is_value v -> 
      in_e, RestoreEnv (env', cont), bind x v env
  | v, RestoreEnv (env', context) when is_value v -> v, context, env'
      

  | _ -> failwith "Unexpected control string"
  
  
  
let rec run (e : exp) (cont : context) (env : env) = match (e, cont) with
  | v, Top when is_value v -> v
  | e, k -> let (e', k', env') = step e k env in run e' k' env' 
