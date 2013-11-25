open M_syntax

module Env =
struct

  module IdMap = Identifier.Map

  type 'a env = 'a IdMap.t

  let empty  = IdMap.empty
  let lookup = IdMap.find
  let bind   = IdMap.add

end

type exp_env = exp Env.env
type typ_env = typ Env.env


let rec _type_of (env : typ_env) (e : exp) : typ = match e with
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

  | Id x -> Env.lookup x env

  | Let (x, with_e, in_e) ->
      let env' = Env.bind x (_type_of env with_e) env in _type_of env' in_e

  | Fun (x, t, b) -> let env' = Env.bind x t env in TFun (t, _type_of env' b)

  | Fix (x, t, b) -> (match t with
      | TFun _ -> let env' = Env.bind x t env in if t = _type_of env' b then t else failwith "Type Error"
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

  | Read t -> t

  | Write e -> _type_of env e


let type_of (e : exp) : typ = _type_of Env.empty e


type context =  
  | Top
  | BinOpR      of binOp * exp * context
  | BinOpL      of binOp * int * context
  | IfCont      of exp * exp * context
  | LetV        of id * exp * exp_env * context
  | RestoreEnv  of exp_env * context
  | AppR        of exp * context
  | AppL        of id * typ * exp * exp_env * context
  | ConsL       of exp * context
  | ConsR       of exp * context
  | HeadCont    of context
  | TailCont    of context
  | IsEmptyCont of context
  | ProjCont    of int * context
  | TupleCont   of exp list * exp list * context

let empty_context : context = Top

let is_empty_context (k : context) : bool = Top = k
  

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
         (env : exp_env) : exp * context * exp_env = match (e, cont) with
  | BinOp (op, eL, eR), cont      -> eL, BinOpR (op, eR, cont), env
  | Int nL, BinOpR (op, eR, cont) -> eR, BinOpL (op, nL, cont), env
  | Int nR, BinOpL (op, nL, cont) -> (match op with 
        | Plus | Minus | Times -> Int  (app_arith_op op nL nR), cont, env
        | LT   | GT    | EQ    -> Bool (app_relational_op op nL nR), cont, env)

  | If (eC, eT, eF), cont -> eC, IfCont (eT, eF, cont), env
  | Bool b, IfCont (eT, eF, cont) -> if b then eT, cont, env else eF, cont, env

  | Id x, cont -> let v = Env.lookup x env in v, cont, env

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
      in_e, RestoreEnv (env', cont), Env.bind x v env
  | v, RestoreEnv (env', cont) when is_value v -> v, cont, env'


  | App (e1, e2), cont -> e1, AppR (e2, cont), env
  | Fun (x, t, body), AppR (e2, cont) -> e2, AppL (x, t, body, env, cont), env
  | v, AppL (x, t, body, env', cont) when is_value v && t = type_of v ->
      body, RestoreEnv (env', cont), Env.bind x v env

  (* augment environment by replacing x by a fixpoint *)
  | Fix (x, _, body), cont -> body, cont, Env.bind x e env

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
  | Write (v), cont when is_value v -> M_util.print_exp v; print_newline (); v, cont, env

  | _ -> failwith "Unexpected Expression : Invalid Expression/Type"


let rec run (e : exp) (cont : context) (env : exp_env) = match (e, cont) with
  | v, Top when is_value v -> v
  | e, k -> let (e', k', env') = step e k env in run e' k' env' 

let eval (e : exp) : exp = let _ = type_of e in run e empty_context Env.empty



(*****************************************************************************************
 *                                                                                       *
 *                                       TESTS                                           *
 *                                                                                       *
 *****************************************************************************************)


let rec repl () = 
  print_string "> ";
  match M_util.parse (read_line ()) with
    | M_util.Exp exp -> 
        let v = eval exp in
        let _ = eval (Write v) in
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
                       let v = eval exp in
                       let _ = eval (Write v) in ()

                     | M_util.ParseError msg -> 
                        print_string msg;
                        print_newline ()
                   )
    | _ -> ()


let exec_exp (e_str : string) : exp = match M_util.parse e_str with 
  | M_util.Exp exp -> eval exp
  | M_util.ParseError msg -> failwith msg


let _ = exec_exp "let x = 300 in (let x = 50 in x) + x"


TEST = exec_exp "3"     = Int (3)
TEST = exec_exp "true"  = Bool (true)
TEST = exec_exp "false" = Bool (false)
TEST = exec_exp "if true then 1 else 0" = Int (1)
TEST = exec_exp "if false then 1 else 0" = Int (0)


