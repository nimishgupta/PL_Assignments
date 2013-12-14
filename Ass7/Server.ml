open M_syntax

module Env =
struct

  module IdMap = Identifier.Map

  type 'a env = 'a IdMap.t

  let empty  = IdMap.empty
  let lookup = IdMap.find
  let bind   = IdMap.add

end

type exp_env = Env of value Env.env
and value = exp * exp_env

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


let rec is_value (e : exp) : bool = match e with
  | Int _ | Bool _  | Fun _ | Empty _ -> true
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


  type context =  
    | Top
    | BinOpR      of binOp * exp * exp_env * context
    | BinOpL      of binOp * int * exp_env * context
    | IfCont      of exp * exp * exp_env * context
    | LetV        of id * exp * exp_env * context
    | AppR        of exp * exp_env * context
    | AppL        of id * typ * exp * exp_env * exp_env * context
    | ConsL       of exp * exp_env * context
    | ConsR       of exp * exp_env * context
    | HeadCont    of exp_env * context
    | TailCont    of exp_env * context
    | IsEmptyCont of exp_env * context
    | ProjCont    of int * exp_env * context
    | TupleCont   of exp list * exp list * exp_env * context
    | WriteCont   of exp_env * context

  let empty_context : context = Top

  let is_empty_context (k : context) : bool = Top = k
  

  let step (e : exp) 
           (cont : context)
           (env : exp_env) : exp * context * exp_env = match (e, cont) with

    | BinOp (op, eL, eR), cont            -> eL, BinOpR (op, eR, env, cont), env
    | Int nL, BinOpR (op, eR, env', cont) -> eR, BinOpL (op, nL, env', cont), env'
    | Int nR, BinOpL (op, nL, env', cont) -> (match op with 
        | Plus | Minus | Times -> Int  (app_arith_op op nL nR), cont, env'
        | LT   | GT    | EQ    -> Bool (app_relational_op op nL nR), cont, env')

    | If (eC, eT, eF), cont -> eC, IfCont (eT, eF, env, cont), env
    | Bool b, IfCont (eT, eF, env', cont) -> if b then eT, cont, env' else eF, cont, env'

    | Id x, cont -> 
        let Env _env = env in 
        let (v, env') = Env.lookup x _env in
        v, cont, env'

    | Let (x, with_e, in_e), cont -> with_e, LetV (x, in_e, env, cont), env
    | v, LetV (x, in_e, env', cont) when is_value v -> 
        (match v with
          (* If with_e evals to a function-value then we need to preserve its environment *)
          | Fun _ -> let Env _env = env  in in_e, cont, Env (Env.bind x (v, env)  _env)
          | _     -> let Env _env = env' in in_e, cont, Env (Env.bind x (v, env') _env))

    | App (e1, e2), cont -> e1, AppR (e2, env, cont), env
    | Fun (x, t, body), AppR (e2, env', cont) -> e2, AppL (x, t, body, env, env', cont), env'
    | v, AppL (x, t, body, fenv, orig_env, cont) when is_value v && t = type_of v ->
        let Env _fenv = fenv in 
        body, cont, Env (Env.bind x (v, orig_env) _fenv)

    | Fix (x, _, body), cont -> 
        let Env _env = env in
        body, cont, Env (Env.bind x (e,env) _env)

    | Head e, cont -> e, HeadCont (env, cont), env
    | v, HeadCont (env', cont) when is_value v -> (match v with
        | Cons (atm, lst) -> (match type_of atm, type_of lst with 
            | t1, TList t2 when t1 = t2 -> atm, cont, env'
            | _ -> failwith "Type Error : Cons type mismatch")
        | Empty _ -> failwith "Head of empty list requested"
        | _ -> failwith "Type Error : Expected list")

    | Tail e, cont -> e, TailCont (env, cont), env
    | v, TailCont (env', cont) when is_value v -> (match v with
        | Cons (atm, lst) -> (match type_of atm, type_of lst with
            | t1, TList t2 when t1 = t2 -> lst, cont, env'
            | _ -> failwith "Type Error : Cons type mismatch")
        | Empty _ -> failwith "Tail of empty list requested"
        | _ -> failwith "Type Error : Expected list")

    | IsEmpty e, cont -> e, IsEmptyCont (env, cont), env
    | v, IsEmptyCont (env', cont) when is_value v -> (match v with
        | Cons _  -> Bool false, cont, env'
        | Empty _ -> Bool true, cont, env'
        | _ -> failwith "Expected list")

    | Cons (atm, lst), cont when not (is_value atm && is_value lst) -> 
        atm, ConsR (lst, env, cont), env
    | vatm, ConsR (lst,  env', cont) when is_value vatm -> lst, ConsL (vatm, env', cont), env'
    | vlst, ConsL (vatm, env', cont) when is_value vlst -> Cons (vatm, vlst), cont, env'


    | Proj (e, n), cont -> e, ProjCont (n, env, cont), env
    | v, ProjCont (n, env', cont) when is_value v -> (match v with
        | Tuple (vlist) -> List.nth vlist n, cont, env'
        | _ -> failwith "Expected Tuple")


  (* Base case *)
    | Tuple (elist), cont when not (is_value e) ->
        let open List in hd elist, TupleCont (tl elist, [], env, cont), env

  (* General case *)
    | v, TupleCont (elist, vlist, env', cont) when is_value v -> let open List in
        if [] = elist then Tuple (rev (v::vlist)), cont, env'
        else hd elist, TupleCont (tl elist, v::vlist, env', cont), env'

    | Read (typ), cont -> (match M_util.parse (read_line ()) with
        | M_util.ParseError err -> failwith err
        | M_util.Exp e' when is_value e' && typ = type_of e' -> e', cont, env
        | _ -> failwith "Not a value")

    | Write (e), cont -> e, WriteCont (env, cont), env

    (* XXX : what exp to return when printing? *)
    | v, WriteCont (env', cont) when is_value v -> 
        M_util.print_exp v; print_newline (); v, cont, env'

    | _ -> failwith "Unexpected Expression : Invalid Expression/Type"



let rec run (e : exp) (cont : context) (env : exp_env) = match (e, cont) with
  | v, Top when is_value v -> v
  | e, k -> let (e', k', env') = step e k env in run e' k' env' 


let to_native (s : string) : string =
  let open Cryptokit in
  transform_string (Hexa.decode ()) s

let to_web (s : string) : string = 
  let open Cryptokit in
  transform_string (Hexa.encode ()) s


let crypto_sign (k : Cryptokit.RSA.key) (s : string) : string =
  let d = Digest.to_hex (Digest.string s) in
  Cryptokit.RSA.sign k d

let sign_match (k : Cryptokit.RSA.key) (sign : string) (s : string) : bool =
  let d  = Cryptokit.RSA.unwrap_signature k sign in
  let d' = (Digest.to_hex (Digest.string s)) in
  (* XXX : Cryptokit idiosyncracy *)
  d' = String.sub d (String.length d - String.length d') (String.length d')

let to_form (key : Cryptokit.RSA.key) (t : M_syntax.typ) (env : exp_env) (k : context): string  =
  let open Cryptokit in
  let env_str   = to_web (Marshal.to_string env []) in
  let cont_str  = to_web (Marshal.to_string k [])   in
  let type_str  = to_web (Marshal.to_string t [])   in
  let env_sign  = to_web (crypto_sign key env_str)  in
  let cont_sign = to_web (crypto_sign key cont_str) in
  let type_sign = to_web (crypto_sign key type_str) in
  "<HTML><BODY> 
      <form name=\"myform\" action=\"\" method=\"POST\">
      <input type=\"hidden\" name=\"env_str\"   value=\"" ^ env_str    ^ "\">
      <input type=\"hidden\" name=\"env_sign\"  value=\"" ^ env_sign   ^ "\">
      <input type=\"hidden\" name=\"cont_str\"  value=\"" ^ cont_str   ^ "\">
      <input type=\"hidden\" name=\"cont_sign\" value=\"" ^ cont_sign  ^ "\">
      <input type=\"hidden\" name=\"type_str\"  value=\"" ^ type_str   ^ "\">
      <input type=\"hidden\" name=\"type_sign\" value=\"" ^ type_sign  ^ "\">
      Enter input (" ^ (M_util.string_of_typ t) ^ ") : 
      <input type=\"text\"   name=\"param\" value=\"\">
      <input type=\"submit\" value=\"Submit\">
      </form>
  </BODY<</HTML>"

let to_result (e : M_syntax.exp) : string = 
  "<HTML><BODY>" ^ "Result is : " ^ (M_util.string_of_exp e) ^ "</BODY></HTML>"

let rec run_server (key : Cryptokit.RSA.key) (e : exp) (cont : context) (env : exp_env) : string = 
  match (e, cont) with
    | v, Top when is_value v -> to_result v
    | Read (typ), cont -> to_form key typ env cont
    | e, k -> let (e', k', env') = step e k env in run_server key e' k' env'


let eval (e : exp) : exp = let _ = type_of e in run e empty_context (Env (Env.empty))

let rec split (str : string) (sep : Char.t) : string list =
  let open String in
    try let i = index str sep
        in (sub str 0 i) :: split (sub str (i+1) ((length str) - (i+1))) sep
    with Not_found -> [str]


let body_to_assoclst (body : string) : (string * string) list =
  let varlst = split body '&' in
  List.map (fun el -> let l = split el '=' in List.hd l, List.hd (List.tl l)) varlst

type post_form = {
                   env_str   : string;
                   env_sign  : string;
                   cont_str  : string;
                   cont_sign : string;
                   type_str  : string;
                   type_sign : string;
                   param     : string;
                 }


exception Parse_error of string

let parse_body (body : string) : post_form =
  let open List in
  let assoclst = body_to_assoclst body in
  try
    {
      env_str   = assoc "env_str"   assoclst;
      env_sign  = assoc "env_sign"  assoclst;
      cont_str  = assoc "cont_str"  assoclst;
      cont_sign = assoc "cont_sign" assoclst;
      type_str  = assoc "type_str"  assoclst;
      type_sign = assoc "type_sign" assoclst;
      param     = assoc "param"     assoclst;
    }
  with _ -> raise (Parse_error "Corrupt request, missing arguments")


module Request = Cohttp.Request
module Server  = Cohttp_async.Server

(* TODO : Refactor *)
let handle_body (key : Cryptokit.RSA.key) (body : string) : Server.response Async.Std.Deferred.t =
  try
    let b = parse_body body
    in if not (sign_match key (to_native b.env_sign) b.env_str)   ||
          not (sign_match key (to_native b.cont_sign) b.cont_str) ||
          not (sign_match key (to_native b.type_sign) b.type_str)
       then Server.respond_with_string "Tampered Request" ~code: `Bad_request
       else let env = Marshal.from_string (to_native b.env_str)  0 in
            let con = Marshal.from_string (to_native b.cont_str) 0 in
            let typ = Marshal.from_string (to_native b.type_str) 0 in
            (match M_util.parse b.param with

              | M_util.Exp v when (is_value v) && ((type_of v) = typ)-> 
                  (try
                     let resp = run_server key v con env in
                     Server.respond_with_string resp ~code: `OK
                   with _ -> Server.respond_with_string "Internal error" ~code: `Bad_request)

              | M_util.ParseError msg -> 
                  Server.respond_with_string ("Error: " ^ msg) ~code: `Bad_request

              | _ -> Server.respond_with_string "Error: Invalid input" ~code: `Bad_request)

  with _ -> Server.respond_with_string "Corrupt request" ~code: `Bad_request


open Async.Std
(* This shouldn't be necessary, but let's you handle lots of data:
   http://en.wikipedia.org/wiki/Chunked_transfer_encoding *)
let cat_chunks (body : string Pipe.Reader.t) : string Deferred.t =
  Pipe.fold body ~init:"" ~f:(fun x y -> Deferred.return (x ^ y))


let handle_client (key : Cryptokit.RSA.key)
                  (e : M_syntax.exp)
                  ~(body : string Pipe.Reader.t option)
                  (client_addr : Socket.Address.Inet.t)
                  (request : Request.t) : Server.response Deferred.t =
  let open Request in match request.meth with
    | `GET -> Server.respond_with_string (run_server key e empty_context (Env (Env.empty))) ~code: `OK
    | `POST -> (match body with
        | None -> Server.respond_with_string "missing body" ~code: `Bad_request
        | Some body -> cat_chunks body >>= (handle_body key))
    | _ -> Server.respond_with_string "" ~code: `Bad_request

    

let run (key : Cryptokit.RSA.key) (port : int) (e : M_syntax.exp) = 
  Server.create (Tcp.on_port port) (handle_client key e)



(* TODO : Make this non-blocking
let rec repl () = 
  print_string "> ";
  (match M_util.parse (read_line ()) with
     | M_util.Exp exp -> 
         let v = eval exp in
         eval (Write v)

    | M_util.ParseError msg ->
        print_endline msg);
  repl ()
*)

let usage = "cs691f run Server [ repl | FILENAME | PORT FILENAME ]"


let _ =  
  match Array.to_list Sys.argv with
    (* | [ exe; "repl" ] -> print_string "Press Ctrl + C to quit.\n"; repl () *)
    
    (* parse from file specified on command line *)
    | [ exe; f] -> (match (M_util.parse_from_file f) with
        | M_util.Exp exp ->
            let v = eval exp in
            let _ = eval (Write v) in ()

        | M_util.ParseError msg -> print_endline msg)

    | [ exe; port; f] -> (match (M_util.parse_from_file f) with
        | M_util.ParseError msg -> print_endline msg

        | M_util.Exp e -> 
            let key = Cryptokit.RSA.new_key 1024 in
            let _ = run key (int_of_string port) e in
            print_endline ("Serving " ^ f ^ " on port " ^ port);
            Core.Std.never_returns (Scheduler.go ()))

    | _ -> print_endline usage

let exec_exp (e_str : string) : exp = match M_util.parse e_str with 
  | M_util.Exp exp -> eval exp
  | M_util.ParseError msg -> failwith msg







(*****************************************************************************************
 *                                                                                       *
 *                                       TESTS                                           *
 *                                                                                       *
 *****************************************************************************************)


(* Check if correct exp evaluates fine *)
TEST = exec_exp "3"     = Int (3)
TEST = exec_exp "true"  = Bool (true)
TEST = exec_exp "false" = Bool (false)
TEST = exec_exp "if true then 1 else 0" = Int (1)
TEST = exec_exp "if false then 1 else 0" = Int (0)

(* Bin op *)
TEST = exec_exp "3 + 5" = Int (8)
TEST = exec_exp "3 - 5" = Int (-2)
TEST = exec_exp "3 * 5" = Int (15)
TEST = exec_exp "3 < 5" = Bool (true)
TEST = exec_exp "3 > 5" = Bool (false)
TEST = exec_exp "3 = 5" = Bool (false)

(* composite *)
TEST = exec_exp "if true then 1 + 2 else 3 + 5" = Int (3)

(* env check : Nested Let *)
TEST = exec_exp "let x = 5 in let y = 6 in x + y" = Int (11)
TEST = exec_exp "let y = 5 in let x = 6 in x + y" = Int (11)

(* env check *)
TEST = exec_exp "let x = 11 in x + (let x = 5 in x) + (let x = 8 in x)" = Int (24)

(* Basic function evaluation *)
TEST = exec_exp "let double = fun (x : int) -> 2 * x in double 5" =
       exec_exp "let double = fun (n : int) -> n + n in double 5"

(* Check closure *)
TEST = exec_exp "(let x = 5 in fun (y : int) -> x * y) 2" = Int (10)

(* Check currying *)
TEST = exec_exp "let add = fun (x : int) -> fun (y : int) -> x + y in (add 3) 5" = Int (8)

let double = "let double = fun (x : int) -> x + x in"


(* Check Higher order functions *)
TEST = exec_exp "let double = fun (x : int) -> x + x in
                 let binop = fun (op : int -> int) ->
                               fun (x : int) -> op x in
                 binop double 6" = Int (12)

(* class test case *)
TEST = exec_exp "let x = 300 in (let x = 50 in x) + x" = Int (350)


TEST = exec_exp "let inc = (fun (x : int) -> 
                              fun (y : int) ->
                                x + y) 1 in
                 inc 8" = Int (9)
(* fix *)
TEST = exec_exp "let fact = fix (self : int -> int) ->
                              fun (n : int) -> 
                                if 0 = n then 1 else n * self (n - 1) in
                 fact 5" = Int (120)

(* List tests *)
TEST = exec_exp "let length = fix (self : int list -> int) ->
                                fun (lst : int list) ->
                                  if empty? lst
                                  then 0
                                  else 1 + self (tail lst) in
                 let lst = 1 :: 2 :: 3 :: empty<int> in 
                 length lst" = Int (3)

let map = "let int_map = fix (self : (int -> int) -> int list -> int list) ->
                           fun (f : int -> int) ->
                             fun (lst : int list) ->
                               if empty? lst
                               then empty<int>
                               else f (head lst) :: self f (tail lst) in"


TEST = exec_exp (map ^ " " ^ double ^ " " ^ "let lst = 1 :: 2 :: 3 :: empty<int> in int_map double lst") = Cons (Int 2, Cons (Int 4, Cons (Int 6, Empty (TInt))))

(* List of functions *)
TEST = exec_exp "let id = fun (x : int) -> x in
                 let double = fun (x : int) -> 2 * x in
                 let triple = fun (x : int) -> 3 * x in
                 let lst = id :: double :: triple :: empty<int -> int> in
                 let y = 1 in
((head lst) y) :: ((head (tail lst)) y) :: ((head (tail (tail lst))) y) :: empty <int>" = 
Cons (Int 1, Cons (Int 2, Cons (Int 3, Empty TInt)))

TEST = exec_exp "let x = (1, 2, 3) in x.0 :: x.1 :: x.2 :: empty<int>" =
Cons (Int 1, Cons (Int 2, Cons (Int 3, Empty TInt)))

TEST = exec_exp "let a = 3 in
                 let b = 2 in
                 write (a + b)" = Int 5
