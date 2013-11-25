open M_syntax


(* TODO : Make a functor on exp and typ *)
module ExpEnv : 

sig
  
  type env

  val empty : env

  val lookup : id -> env -> exp

  val bind : id -> exp -> env -> env

end = struct

  module Env = Map.Make (Identifier)

  type env = exp Env.t

  let empty = Env.empty

  let print_env_elem id exp = print_string ((Identifier.to_string id) ^ " == " ^ (M_util.string_of_exp exp) ^ "\n")

  let print_env env = Env.iter print_env_elem env

  let lookup x env' =
     try Env.find x env'
     with Not_found -> print_string ("Identifier : " ^ (Identifier.to_string x) ^ " not foun in environment below\n"); print_env env'; raise Not_found

  let bind = Env.add


end


module TypEnv : 

sig
  
  type env

  val empty : env

  val lookup : id -> env -> typ

  val bind : id -> typ -> env -> env

end = struct

  module Env = Map.Make (Identifier)

  type env = typ Env.t

  let empty = Env.empty

  let print_env_elem id typ = print_string ((Identifier.to_string id) ^ " == " ^ (M_util.string_of_typ typ) ^ "\n")

  let print_env env = Env.iter print_env_elem env


  let lookup x env' = 
     try Env.find x env'
     with Not_found -> print_string ("Identifier : " ^ (Identifier.to_string x) ^ " not foun in environment below\n"); print_env env'; raise Not_found



  let bind x v env = Env.add x v env

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

  | Fix (x, t, b) -> (match t with
      | TFun _ -> let env' = TypEnv.bind x t env in if t = _type_of env' b then t else failwith "Type Error"
      | _ -> failwith "Type Error")

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


type context =  
  | Top
  | BinOpR      of binOp * exp * context
  | BinOpL      of binOp * int * context
  | IfCont      of exp * exp * context
  | LetV        of id * exp * ExpEnv.env * context
  | RestoreEnv  of ExpEnv.env * context
  | AppR        of exp * context
  | AppL        of id * typ * exp * ExpEnv.env * context
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

  | If (eC, eT, eF), cont -> eC, IfCont (eT, eF, cont), env
  | Bool b, IfCont (eT, eF, cont) -> if b then eT, cont, env else eF, cont, env

  | Id x, cont -> let v = ExpEnv.lookup x env in v, cont, env

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
  | Fun (x, t, body), AppR (e2, cont) -> e2, AppL (x, t, body, env, cont), env
  | v, AppL (x, t, body, env', cont) when is_value v && t = type_of v ->
      body, RestoreEnv (env', cont), ExpEnv.bind x v env

  (* augment environment by replacing x by a fixpoint *)
  (* | Fix (x, _, body), cont -> body, RestoreEnv (env, cont), ExpEnv.bind x e env *)
  | Fix (x, _, body), cont -> body, cont, ExpEnv.bind x e env

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

  | _ -> failwith "Unexpected Expression : Invalid Expression/Type"
  

let rec run (e : exp) (cont : context) (env : ExpEnv.env) = match (e, cont) with
  | v, Top when is_value v -> v
  | e, k -> let (e', k', env') = step e k env in run e' k' env' 



(*****************************************************************************************
 *                                                                                       *
 *                                       TESTS                                           *
 *                                                                                       *
 *****************************************************************************************)


let rec repl () = 
  print_string "> ";
  match M_util.parse (read_line ()) with
    | M_util.Exp exp -> 
        let v = run exp Top ExpEnv.empty in
        let _ = run (Write v) Top ExpEnv.empty in
        print_newline ();
        repl ()
    | M_util.ParseError msg ->
        print_string msg;
        print_newline ();
        repl ()


let _ =  
  match Array.to_list Sys.argv with
    | [ exe; "repl" ] -> print_string "Press Ctrl + C to quit.\n"; repl ()
    
    (* parse from file specified on command line *)
    | [ exe; f] -> (match (M_util.parse_from_file f) with

                     | M_util.Exp exp ->
                       let v = run exp Top ExpEnv.empty in
                       let _ = run (Write v) Top ExpEnv.empty in
                       print_newline ()

                     | M_util.ParseError msg -> 
                        print_string msg;
                        print_newline ()
                   )
    | _ -> ()
