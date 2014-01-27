module Term = ANSITerminal

(* Student solution must have this signature *)
module type SOLUTION = sig

  val typeinf : Typeinf_syntax.Implicit.exp -> Typeinf_syntax.Explicit.exp

end

module TypeChecker = struct
  (* A type-checker for the explicitly typed language used in type-inference *)
  open Typeinf_syntax
  open Explicit

  exception Type_error of string

  module type ENV = sig
    type t
    val empty : t
    val lookup : id -> t -> typ
    val bind : id -> typ -> t -> t
  end

  module Env : ENV = struct
    module IdMap = Identifier.Map
    type t = typ IdMap.t

    let empty = IdMap.empty
    
    let lookup (x : id) (env : t) =
      try IdMap.find x env 
      with Not_found -> 
        raise (Type_error (Format.sprintf "%s not found" 
                             (Identifier.to_string x)))

    let bind = IdMap.add

  end

  type env = Env.t

  let rec synth (env : env) (e : exp) : typ = match e with
    | Int _ -> TInt
    | Bool _ -> TBool
    | Arith (_, e1, e2) ->
      check env e1 TInt;
      check env e2 TInt;
      TInt
    | Cmp (_, e1, e2) ->
      check env e1 TInt;
      check env e2 TInt;
      TBool
    | If (e1, e2, e3) -> 
      check env e1 TBool;
      let t = synth env e2 in
      check env e3 t;
      t
    | Id x -> Env.lookup x env
    | Let (x, e1, e2) -> synth (Env.bind x (synth env e1) env) e2
    | Fun (x, t, e) -> TFun (t, synth (Env.bind x t env) e)
    | Fix (x, t, e) ->
      check (Env.bind x t env) e t;
      t
    | App (e1, e2) ->
      (match synth env e1 with
       | TFun (t1, t2) -> check env e2 t1; t2
       | _ -> raise (Type_error "expected function"))
    | Empty t -> TList t
    | Cons (e1, e2) ->
      let t = synth env e1 in
      check env e2 (TList t);
      TList t
    | Head e ->
      (match synth env e with
       | TList t -> t
       | _ -> raise (Type_error "head expected list"))
    | Tail e ->
      (match synth env e with
       | TList t -> TList t
       | _ -> raise (Type_error "tail expected list"))
    | IsEmpty e ->
      (match synth env e with
        | TList _ -> TBool
        | _ -> raise (Type_error "is_empty expected list"))
    | Pair (e1, e2) -> TPair (synth env e1, synth env e2)
    | ProjL e ->
      (match synth env e with
        | TPair (t1, _) -> t1
        | _ -> raise (Type_error "ProjL expected pair"))
    | ProjR e ->
      (match synth env e with
        | TPair (_, t2) -> t2
        | _ -> raise (Type_error "ProjR expected pair"))

  and check (env : env) (e : exp) (t : typ) : unit =
    if synth env e = t then
      ()
    else
      raise (Type_error "type error")

  let typecheck (e : exp) : typ = synth Env.empty e
end
module Make (Solution : SOLUTION) = struct

  module Util = Typeinf_util
  module Implicit = Typeinf_syntax.Implicit
  module Explicit = Typeinf_syntax.Explicit

  let output_filename = "errors_caught.txt"

  let dump (out : out_channel) (in_ : in_channel) : unit =
    let rec loop () = 
      Printf.fprintf out "%s\n" (input_line in_);
      loop () in
    try
      loop ()
    with End_of_file -> close_in in_

  let report_failure (log : out_channel) (msg : string) 
                     (filename : string) : unit =
    Printf.fprintf log "\n\n/* %s */\n" msg;
    let ch = open_in filename in
    dump log ch

  let fail_re = Str.regexp_string "fail"

  let run_test (log : out_channel) (filename : string) : unit =
    let should_fail = 
      try let (_:int) = Str.search_forward fail_re filename 0 in true
      with Not_found -> false in 
    match Util.parse_from_file filename with
    | Util.ParseError msg ->
      Term.printf [Term.red] "Error parsing test file %s; reason: %s\n%!"
        filename msg
    | Util.Exp exp ->
      try
        let explicit_exp = Solution.typeinf exp in
        if should_fail then
          (Term.printf [Term.magenta] "%s : expected type error\n%!" filename;
           report_failure log "expected type error" filename)
        else
          try 
            let _ = TypeChecker.typecheck explicit_exp in
            Term.printf [Term.green] "%s : success\n%!" filename
          with 
          | TypeChecker.Type_error msg ->
            let msg = Format.sprintf "%s : result is not typable (%s)"
                        filename msg in
            (Term.print_string [Term.magenta] msg; report_failure log msg filename)
          | exn ->
           Term.printf [Term.red] "Error type-checking on %s; reason: %s\n%!"
             filename (Printexc.to_string exn)
      with exn ->
        if should_fail then
          Term.printf [Term.green] "%s : success\n%!" filename
        else          
          (Term.printf [Term.magenta]
             "%s : expected type inference to succeed\n%!" filename;
           report_failure log 
             (Format.sprintf "expected type inference to succeed (%s)"
              (Printexc.to_string exn))
             filename)

  let run_tests (files : string list) =
    let output = open_out "errors_caught.txt" in
    List.iter (run_test output) files;
    close_out output

end

module Main = Make (Typeinf)

let _ = Main.run_tests (List.tl (Array.to_list Sys.argv))