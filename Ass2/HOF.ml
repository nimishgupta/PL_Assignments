open HOF_syntax
open List

(*
type expList =
  | ExpList of exp * expList
  | EmptyExpList
*)



(* 
 XXX : How is id list * exp * env is a closure, environment itself is a
       list of (id * value) then why exp * (list of (id * exp))
*)

type value =
  | Num of int
  | Closure of id list * exp * env 
  | RecordValue of (field * value) list

and env =
  (* 
    XXX : What if I were to define environment as collection of identifiers
          and corresponding "un-evaluated" expressions, why have we made
          such a desing choice
   *)
  | Env of id * value * env
  | EmptyEnv

and valueList =
  | ValueList of value * valueList
  | EmptyValueList



let int_of_value (v : value ) : int =
  match v with 
    | Num (n) -> n
    | _ -> failwith "Expected Integer"

;;

(* how to check for failwith *)
TEST = int_of_value (Num 5)  = 5
TEST = int_of_value (Num 0)  = 0
TEST = int_of_value (Num (-5)) = -5




let rec lookup (binds : env) (x : id) : value =
  match binds with 
    | EmptyEnv -> failwith "Free identifier"
    | Env (y, v, rest) -> if x = y
                          then v
                          else lookup rest x



let rec augment_env (ids : id list) (vs : valueList) (env : env) : env =

(* 
  "idList" as "id * idList" not compatible with "id list"

  let head_of_idList (ids : idList) : id =
    match ids with 
      | IdList (id, rest) -> id
      | EmptyIdList -> failwith "Head of Empty idList"

  in

  let tail_of_idList (ids : idList) : idList =
    match ids with
      | IdList (id, rest) -> rest
      | EmptyIdList -> failwith "Tail of Empty idList"

  in
*)

  let head_of_valueList (vs : valueList) : value =
    match vs with
      | ValueList (v, rest) -> v
      | EmptyValueList -> failwith "Head of Empty valueList"

  in                                         

  let tail_of_valueList (vs : valueList) : valueList =
    match vs with
      | ValueList (v, rest) -> rest
      | EmptyValueList -> failwith "Tail of Empty valueList"

  in if ([] = ids) && (EmptyValueList = vs) then EmptyEnv
     else if ([] = ids) || (EmptyValueList = vs) then failwith "Parameter mismatch"
     else Env (hd ids, head_of_valueList vs,
                augment_env (tl ids) (tail_of_valueList vs) env)

(* XXX : Can I use higher order list functions in program *)


(* XXX : Why evaluate eagerly in the program, is it a design pattern or a design choice *)





let rec eval_helper (binds : env) (e : exp) : value =
  match e with
    | Int (n) -> Num (n)

    | Add (e1, e2) -> Num (int_of_value (eval_helper binds e1) +
                           int_of_value (eval_helper binds e2))

    (* XXX : Why is this in the core language, why not desugar it? *)
    | Sub (e1, e2) -> eval_helper binds (Add (e1, Mul (Int (-1), e2))) 

    | Mul (e1, e2) -> Num (int_of_value (eval_helper binds e1) *
                           int_of_value (eval_helper binds e2))

    | Let (replaceId, with_e, in_e) -> 
      (* 
        1. evaluate with_e using global environment and augment the current
            environment locally with replaceId -> with_e
        2. evaluate in_e with augmented environment
      *)
       let withExpValue = eval_helper binds with_e
       in let binds_prime = Env (replaceId, withExpValue, binds)
          in eval_helper binds_prime in_e

    | Id (x) -> lookup binds x

    (* XXX : What if I want to add the false branch as optional *)
    | If0 (pred, true_branch, false_branch) -> if 0 <> int_of_value (eval_helper binds pred)
                                               then eval_helper binds true_branch
                                               else eval_helper binds false_branch

    | Lambda (idList, body) -> Closure (idList, body, binds)

    | Apply (e, paramList) -> 
      (*
        Evaluate e using bindings given by paramList
        1. Augment a local environment with all the bindings
        2. Evaluate body in environment
      *)

      (match (eval_helper binds e) with
        | Closure (idList, body, func_env) -> 
            (* Helper function that evaluates params of 'lambda' function in original environment *)
            let rec f (exps : exp list) : valueList = 
              if [] <> exps
              then ValueList ((eval_helper binds (hd exps)), f (tl exps))
              else EmptyValueList

            in eval_helper (augment_env idList (f paramList) func_env) body

        | _ -> failwith "Expected function")

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
              if [] = rv then failwith "Field not present in record"
              else match (hd rv) with
                    | (f, v) -> if f = searchField
                                then (f, (eval_helper binds new_e))::(tl rv)
                                else (hd rv)::(f_replace (tl rv))

            in RecordValue (f_replace recs)

          | _ -> failwith "Expected Records"
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
              if [] = rv then failwith "Field not present in record"
              else match (hd rv) with
                    | (f, v) -> if f = searchField then v else f_lookup (tl rv)
                    (*| _ -> "Unknown record type"i *)

            in f_lookup recs
            
          | _ -> failwith "Expected Records"
      )
      

(** Evaluates expressions to values. *)
let eval (e : HOF_syntax.exp) : value = eval_helper EmptyEnv e






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

    | S.Apply (e, paramList) -> 
    (* TODO : rewrite in terms of lists functions *)
      let rec f (exps : S.exp list) : exp list =
        if [] <> exps
        then (desugar (hd exps))::(f (tl exps))
        else []
      in Apply (desugar e, f paramList)
       
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
    | S.True -> Int 1
    | S.False -> Int 0

    (*  Assume that the conditional evaluates to a boolean. *)

    | S.If (pred, true_branch, false_branch) ->  failwith "desugaring of predicate is not clear"

    (*  Assume that the sub-expressions evalute to booleans.  *)
    | S.And (e1, e2) -> desugar (S.If (e1, e2, S.False))
    | S.Or (e1, e2)  -> desugar (S.If (e1, S.True, e2))


    (*  Assume that the sub-expressions evaluate to integers. *)
    | S.IntEq (e1, e2) -> desugar (S.If0 (S.Sub (e1, e2), S.False, S.True))

    (* TODO *)
    | S.Empty -> failwith "desugaring of S.Empty is not clear"
    | S.Cons (e1, e2) -> failwith "desugaring of S.Cons in not clear"
    
    (*  Assume that the sub-expression is either Cons or Empty. *)
    | S.Head (e) -> failwith "desugaring of S.Head is not clear"
    | S.Tail (e) -> failwith "desugaring of S.Tail is not clear"
    | S.IsEmpty (e) -> failwith "desugaring of S.IsEmpty is not clear"


(*
   XXX : Lists have to be implemented using records

   Head (Cons (x, y)) -> x
   Head (x) -> Undefined
   Tail (Cons (x, y)) -> y
   IsEmpty (Cons (x, y)) -> False
   IsEmpty (Empty) -> True
*)



let exp1 : exp = Let ("x", Int 10, Id ("x"));;
let exp2 : exp = Let ("x", Int 10, Let ("y",
                                        Add (Int 20, Id ("x")),
                                        Add (Id ("x"), Id ("y"))
                                       );
                     );;


(* FUNCTION TESTS *)
let exp3 : exp = Lambda (["a"; "b"; "c";],
                         Add (Id ("a"),
                              Add (Id "b", Id "c")));;

let exp4 : exp = Apply (exp3, [Int (2); Int (3); Int (5);]);;





(* RECORDS TESTS *)
let exp5 : exp = Record ([("x", Int 49);("y", exp2)];);;
let exp6 : exp = GetField (exp5, "x");;
let exp7 : exp = GetField (exp5, "y");;
let exp8 : exp = GetField (SetField (exp5, "y", exp4), "y");;


print_string  (string_of_int (int_of_value (eval (Int 5))) ^ "\n");
print_string  (string_of_int (int_of_value (eval exp2)) ^ "\n");
print_string  (string_of_int (int_of_value (eval exp4)) ^ "\n");
print_string  (string_of_int (int_of_value (eval exp6)) ^ "\n");
print_string  (string_of_int (int_of_value (eval exp7)) ^ "\n");
print_string  (string_of_int (int_of_value (eval exp8)) ^ "\n");




(* TODO : 
 1. Test lookup
 2. Test eval_helper
 3. Test eval
*)



(* Possible test cases
1. let z = (Record of multiple values) in GetField
2. let z = Record of multiple values in which one of them is a function of multiple ids in Apply (GetField (Function), paramlist)
3. Test case with nested records
*)
