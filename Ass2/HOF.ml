open HOF_syntax
open List

type value =
  | Num of int
  | Closure of id list * exp * env 
  | RecordValue of (field * value) list

and env = (id * value) list


let string_of_value (v: value) : string =
  match v with
    | Num (n) -> string_of_int n
    | Closure (ids, exp, env) -> "Closure"
    | RecordValue (_) -> "Record Value"


let int_of_value (v : value ) : int =
  match v with 
    | Num (n) -> n
    | _ -> failwith "int_of_value: Expected Integer"

(* Tests for int_of_value *)
TEST = int_of_value (Num 5)  = 5
TEST = int_of_value (Num 0)  = 0
TEST = int_of_value (Num (-5)) = -5
TEST = (try let v = RecordValue ([("x", Num 5);]) 
            in int_of_value (v)
        with Failure _ -> (-1)) = (-1)
TEST = (let v = Closure (["x"; "y";],
                         Add (Id "x", Id "y"),
                         [("x", Num 6);
                          ("y", Num 7);])
        in try int_of_value (v)
           with _ -> (-1)) = (-1)



(* TODO : Implement using higher order list function *)
let rec lookup (binds : env) (x : id) : value =
  match binds with 
    | [] -> failwith "lookup: Free identifier"
    | (y, v)::rest -> if x = y
                      then v
                      else lookup rest x


let en0 : env = [("z", Num 7);
                 ("y", Num 6);
                 ("x", Num 5);]

TEST = int_of_value (lookup en0 "x") = 5
TEST = int_of_value (lookup en0 "y") = 6
TEST = int_of_value (lookup en0 "z") = 7
TEST = (try (int_of_value (lookup en0 "a")) with _ -> -1) = -1



let augment_env (ids  : id list)
                (vals : value list)
                (en0 : env) : env =
  append (combine ids vals) en0

(* Make sure nothing is clobbered *)
TEST = int_of_value (lookup (augment_env [] [] en0) "x") = 5
TEST = int_of_value (lookup (augment_env [] [] en0) "y") = 6
TEST = int_of_value (lookup (augment_env [] [] en0) "z") = 7
TEST = (let aug_en = augment_env ["a";] [(Num 8);] en0
        in int_of_value (lookup aug_en "x")) = 5
TEST = (let aug_en = augment_env ["a";] [(Num 8);] en0
        in int_of_value (lookup aug_en "y")) = 6
TEST = (let aug_en = augment_env ["a";] [(Num 8);] en0
        in int_of_value (lookup aug_en "z")) = 7
TEST = (let aug_en = augment_env ["a";] [(Num 8);] en0
        in int_of_value (lookup aug_en "a")) = 8

(* Make sure error is flagged on length mismatch *)
TEST = (try let aug_en = augment_env ["a";] [] en0
            in int_of_value (lookup aug_en "a")
        with _ -> -1) = -1

TEST = (try let aug_en = augment_env [] [Num 8] en0
            in int_of_value (lookup aug_en "a")
        with _ -> -1) = -1

TEST = (try let aug_en = augment_env ["a"; "b"; "c";] [(Num 8); (Num 9); (Num 10); (Num 11);] en0
            in int_of_value (lookup aug_en "a")
        with _ -> -1) = -1



let rec eval_helper (binds : env) (e : exp) : value =
  match e with
    | Int (n) -> Num (n)

    | Add (e1, e2) -> Num (int_of_value (eval_helper binds e1) +
                           int_of_value (eval_helper binds e2))

    (* XXX : Why is this in the core language, why not desugar it? *)
    | Sub (e1, e2) -> eval_helper binds (Add (e1, Mul (Int (-1), e2))) 

    | Mul (e1, e2) -> Num (int_of_value (eval_helper binds e1) *
                           int_of_value (eval_helper binds e2))

    | Let (x, with_e, in_e) -> 
      (* 
        1. Evaluate with_e using global environment
        2. Augment the current environment "locally" with (x -> with_e)
        2. Evaluate in_e with augmented environment
      *)
       let withExpValue = eval_helper binds with_e
       in let binds_prime =  (x, withExpValue)::binds
          in eval_helper binds_prime in_e

    | Id (x) -> lookup binds x

    | If0 (pred, true_branch, false_branch) -> if 0 = int_of_value (eval_helper binds pred)
                                               then eval_helper binds true_branch
                                               else eval_helper binds false_branch

    | Lambda (ids, body) -> Closure (ids, body, binds)

    | Apply (e, params) -> 
      (*
        Evaluate e using bindings given by params
        1. Augment a local environment with all the bindings
        2. Evaluate body in environment
      *)

      (match (eval_helper binds e) with
        | Closure (idList, body, func_env) -> 

            (* Helper function that evaluates params of 'lambda' function in original environment *)
            let rec f (exps : exp list) : value list = 
              if [] <> exps
              then (eval_helper binds (hd exps))::(f (tl exps))
              else []

            in eval_helper (augment_env idList (f params) func_env) body

        | _ -> failwith "eval_helper: Expected function")

    | Record (recordList) -> 
      (
        let rec f_eval (recs : (field * exp) list) : (field * value) list = 
          if [] <> recs
          then match (hd recs) with
                | (f, e) -> (f, (eval_helper binds e))::(f_eval (tl recs))
          else []

        in RecordValue (f_eval recordList)
      )

    | SetField (e, searchField, new_e) -> 
    (* lookup field in recordList, if found then evaluate new_e and replace old_e with new_e
    *)
      (
        match (eval_helper binds e) with
          | RecordValue (recs) ->

            let rec f_replace (rv : (field * value) list) : (field * value) list =
              if [] = rv then failwith "eval_helper: Field not present in record"
              else match (hd rv) with
                    | (f, v) -> if f = searchField
                                then (f, (eval_helper binds new_e))::(tl rv)
                                else (hd rv)::(f_replace (tl rv))

            in RecordValue (f_replace recs)

          | _ -> failwith "eval_helper: Expected Records"
      )



    | GetField (e, searchField) -> 

    (* lookup filed in recordList, if found then give the new value*)
      (
        match (eval_helper binds e) with
          | RecordValue (recs) ->
            (* 
              Search for searchField through the record list, if found return
              its value else fail with exception 
            *)
            let rec f_lookup (rv : (field * value) list) : value =
              if [] = rv then failwith "eval_helper: Field not present in record"
              else match (hd rv) with
                    | (f, v) -> if f = searchField then v else f_lookup (tl rv)
                    (*| _ -> "Unknown record type"i *)

            in f_lookup recs
            
          | _ -> failwith "eval_helper: Expected Records"
      )
      
(** Evaluates expressions to values. *)
let eval (e : HOF_syntax.exp) : value = eval_helper [] e


(* Test eval *)


let out (e : exp) : int = int_of_value (eval e)


(* Int *)
TEST = out (Int 5)  = 5
TEST = out (Int (-5)) = (-5)
TEST = out (Int 0)  = 0

(* Add *)
TEST = out (Add (Int 5, Int (-5))) = 0
TEST = out (Add (Add (Int 5, Int (-5)), Add (Int 6, Int (-6)))) = 0

(* Sub *)
TEST = out (Sub (Int 5, Int 5)) = 0
TEST = out (Sub (Int 5, Int 4)) = 1
TEST = out (Sub (Int 4, Int 5)) = (-1)
TEST = out (Sub (Add (Int 5, Int (-5)), Add (Int 6, Int (-6)))) = 0
TEST = out (Sub (Sub (Int 5, Int 5), Add (Int 6, Int (-6)))) = 0
TEST = out (Sub (Sub (Int 5, Int 5), Sub (Int 6, Int 6))) = 0


(* Mul *)
TEST = out (Mul (Int 5, Int 5)) = 5*5
TEST = out (Mul (Int 5, Int (-1))) = 5 * (-1)
TEST = out (Mul (Int 0, Int 5)) = 5 * 0
TEST = out (Mul (Add (Int 3, Int 2), Int 9)) = (2+3) * 9
TEST = out (Mul (Mul (Int 3, Int 2), Mul (Int 7, Int 2))) = 3*2*7*2

(* Let *)
TEST = let e : exp = Let ("x", Int 10, Id ("x"))
       in out e = 10

TEST = let e : exp = Let ("x",
                          Int 10,
                          Let ("y",
                               Add (Int 20, Id ("x")),
                               Add (Id ("x"), Id ("y"))
                              )
                         )
       in out e = 40


(* If0 *)
TEST = let e : exp = If0 (Int 0, Int 1234, Int 4321)
       in out e = 1234
TEST = let e : exp = If0 (Int 10, Int 1234, Int 4321)
       in out e = 4321
TEST = let e : exp = If0 (Int (-10), Int 1234, Int 4321)
       in out e = 4321
TEST = let e : exp = If0 (Add (Int 2, Int 2), Int 1234, Int 4321)
       in out e = 4321
TEST = let e : exp = If0 (Sub (Int 2, Int 2), Int 1234, Int 4321)
       in out e = 1234
TEST = let e : exp = If0 (Add (Int 2, Int 2), Add (Int 4, Int 5), Add (Int 5, Int 6))
       in out e = 5+6
TEST = let e : exp = If0 (Add (Int 2, Int 2),
                          If0 (Sub (Int 2, Int 2),
                               Add (Int 5, Int 6),
                               Int 9),
                          Int 10)
       in out e = 10
TEST = let e : exp = If0 (Mul (Int 0, Int 2),
                          If0 (Sub (Int 2, Int 2),
                               Add (Int 5, Int 6),
                               Int 9),
                          Int 10)
       in out e = 5+6



(* Functions and Apply *)
let f_e : exp = Lambda (["a"; "b"; "c";],
                         Add (Id ("a"),
                              Add (Id "b", Id "c")));;


TEST = let e : exp = Apply (f_e, [Int (2); Int (3); Int (5);])
       in out e = 5+3+2

TEST = let e : exp = Apply (f_e, [Add (Int 5, Int 8);
                                  If0 (Int 1, Int 1, Int (-1));
                                  Int 5;])
       in out e = (5+8)+(-1)+5

TEST = (try (let e : exp = Apply (Add (Int 1, Int 2), 
                                  [Int 7; Int 8;])
             in out e)
        with _ -> (-1)) = (-1)




(* RECORDS TESTS *)
let rec_e : exp = Record ([("x", Int 49);("y", f_e)];)
TEST = let e : exp = GetField (rec_e, "x")
       in out e = 49

TEST = (match (let e : exp = GetField (rec_e, "y")
              in eval e) with
          | Closure (_, _, _) -> true
          | _ -> false) = true

TEST = (match (let e : exp = GetField (SetField (rec_e, "y", rec_e), "y")
              in eval e) with
         | RecordValue (_) -> true
         | _ -> false) = true


TEST = (try (let e : exp = GetField (Int 6, "x")
             in out e)
        with _ -> (-1)) = (-1)

TEST = (try (let e : exp = GetField (SetField (Add (Int 7, Int 8),
                                               "x",
                                               Add (Int 9, Int 9)), "x")
             in out e)
        with _ -> (-1)) = (-1)








  (** Desugars extended HOF to HOF. *)
  (* val desugar : HOF_sugar.exp -> HOF_syntax.exp *)


module S = HOF_sugar;;

let rec desugar (s_exp : S.exp) : exp =
  match s_exp with
    | S.Int (n) -> Int (n)
    | S.Add (e1, e2) -> Add (desugar e1, desugar e2)
    | S.Sub (e1, e2) -> Sub (desugar e1, desugar e2)
    | S.Mul (e1, e2) -> Mul (desugar e1, desugar e2)
    | S.Let (x, with_e, in_e) -> Let (x, desugar with_e, desugar in_e)
    | S.Id (x) -> Id x
    | S.If0 (pred, true_branch, false_branch) -> If0 (desugar pred,
                                                      desugar true_branch,
                                                      desugar false_branch)

    | S.Lambda (idList, body) -> Lambda (idList, desugar body)

    | S.Apply (e, params) -> 
    (* TODO : rewrite in terms of lists functions *)
      let rec f (exps : S.exp list) : exp list =
        if [] <> exps
        then (desugar (hd exps))::(f (tl exps))
        else []
      in Apply (desugar e, f params)
       


    | S.Record (recordList) ->
    (* TODO : rewrite in terms of lists functions *)
      let rec f (recs : (field * S.exp) list) : (field * exp) list =
        if [] <> recs
        then match (hd recs) with
              | (fld, s_e) -> (fld, desugar s_e)::(f (tl recs))
        else []
      in Record (f recordList)


    | S.SetField (e1, fld, e2) -> SetField (desugar e1, fld, desugar e2)
    | S.GetField (e1, fld) -> GetField (desugar e1, fld)


    (*  Assume that the conditional evaluates to a boolean. *)
    | S.True -> Int 0
    | S.False -> Int 1
    | S.If (pred, true_branch, false_branch) -> desugar (S.If0 (S.IntEq (pred, S.True),
                                                                true_branch,
                                                                false_branch))
     
    (*  Assume that the sub-expressions evalute to booleans.  *)
    | S.And (e1, e2) -> desugar (S.If (e1, e2, S.False))
    | S.Or (e1, e2)  -> desugar (S.If (e1, S.True, e2))

    (*  Assume that the sub-expressions evaluate to integers. *)
    | S.IntEq (e1, e2) -> desugar (S.If0 (S.Sub (e1, e2), S.True, S.False))



    (* List Semantics *)
    | S.Empty -> desugar (S.Lambda (["pick";], S.True))
    | S.Cons (e1, e2) -> desugar (S.Lambda (["pick";],
                                            S.If0 (S.Id "pick",
                                                   S.False,
                                                   S.If0 (S.IntEq (S.Int 1, S.Id "pick"),
                                                          e1, e2))))
    
    (*  Assume that the sub-expression is either Cons or Empty. *)

    | S.Head (e) -> desugar (S.If ((S.IsEmpty (e)),
                                   (failwith "desugar: list empty"),
                                   (S.Apply (e, [(S.Int 1);]))))

    | S.Tail (e) -> desugar (S.If ((S.IsEmpty (e)),
                                   (failwith "desugar: list empty"),
                                   (S.Apply (e, [(S.Int 2);]))))

    | S.IsEmpty (e) -> desugar (S.Apply (e, [(S.Int 0);]))


(*
   XXX : Semantics of lists

   Head (Cons (x, y)) -> x
   Head (x) -> Undefined
   Tail (Cons (x, y)) -> y
   IsEmpty (Cons (x, y)) -> False
   IsEmpty (Empty) -> True
*)



(* Desugaring Tests *)

let out (e : S.exp) : int =
  int_of_value (eval (desugar e))
  

TEST = let e : S.exp = S.If (S.True, S.Int 1234, S.Int 4321)
       in out e = out (S.Int 1234)

TEST = let e : S.exp = S.If (S.False, S.Int 1234, S.Int 4321)
       in out e = out (S.Int 4321)


TEST = let e : S.exp = S.IsEmpty (S.Cons (S.Int 39, S.Int 47))
       in out e = out S.False

TEST = let e : S.exp = S.IsEmpty (S.Empty)
       in out e = out S.True


TEST = let e : S.exp = S.Let ("x",
                              S.IsEmpty (S.Cons (S.Int 39, S.Int 47)),
                              S.If (S.Id "x", S.Int 99, S.Int 9))
       in out e = out (S.Int 9)

TEST = let e : S.exp = S.Let ("x",
                               S.Int 10,
                               S.If (S.IntEq (S.Id "x", S.Int 10),
                                     S.Int 99,
                                     S.Int 9))
       in out e = out (S.Int 99)

TEST = try (let e : S.exp = S.Let ("x",
                              S.Empty,
                              S.Head (S.Id "x"))
            in out e = 2)
       with _ -> (-1) = (-1)




let rec repl () = 
  print_string "> ";
  match HOF_util.parse (read_line ()) with
    | HOF_util.Exp exp -> 
        let v = eval (desugar exp) in
        print_string (string_of_value v);
        print_newline ();
        repl ()
    | HOF_util.ParseError msg ->
        print_string msg;
        print_newline ();
        repl ()

let _ =  
  match Array.to_list Sys.argv with
    | [ exe; "repl" ] -> print_string "Press Ctrl + C to quit.\n"; repl ()
    | _ -> ()
