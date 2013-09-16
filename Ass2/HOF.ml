(** Core Language and some desugaring *)


(*
  XXX : Why wouldnt a single ';' would do?
*)
open HOF_syntax;;
open List;;

(*
type idList = 
  | IdList of id * idList
  | EmptyIdList
*)

type expList =
  | ExpList of exp * expList
  | EmptyExpList



(* 
 XXX : How is idList * exp * env is a closure, environment itself is a
       list of (id * value) then why exp * (list of (id * exp))
*)

type value =
  | Num of int
  | Closure of id list * exp * env 
(*
  | RecordValue of (field * exp??) list
*)

and env =
  (* XXX : What if I were to define environment as collection of identifiers and corresponding "un-evaluated" expressions, why have we made such a desing choice *)
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
TEST = int_of_value (Num 5)  = 5;
TEST = int_of_value (Num 0)  = 0;
TEST = int_of_value (Num (-5)) = -5;;






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





let rec eval_helper (binds : env) (e : exp) : value =
  match e with
    | Int (n) -> Num (n)

    | Add (e1, e2) -> Num (int_of_value (eval_helper binds e1) +
                           int_of_value (eval_helper binds e2))

    (* XXX : Why is this in the core language, why not desugar it? *)
    | Sub (e1, e2) -> eval_helper binds (Add (e1, Mul (Int (-1), e2))) 

    | Mul (e1, e2) -> Num (int_of_value (eval_helper binds e1) *
                           int_of_value (eval_helper binds e2))

    | Let (replaceId, withExp, inExp) -> 
      (* 
        1. evaluate withExp using global environment and augment the current
            environment locally with replaceId -> withExp
        2. evaluate inExp with augmented environment
       *)
       let withExpValue = eval_helper binds withExp
       in let bindsPrime = Env (replaceId, withExpValue, binds)
          in eval_helper bindsPrime inExp

    | Id (x) -> lookup binds x

    (* XXX : What if I want to add the false branch as optional *)
    | If0 (predicate, true_branch, false_branch) -> if 0 <> int_of_value (eval_helper binds predicate)
                                                    then eval_helper binds true_branch
                                                    else eval_helper binds false_branch

    | Lambda (idList, body) -> Closure (idList, body, binds)

    | Apply (lambda, paramList) -> 
      (*
        Evaluate e1 using bindings given by eList
        1. Augment a local environment with all the bindings
           XXX : Why do we need to evaluate all the paramters while augmenting our environment, because our environment definition requires us to do like that 
        2. Evaluate body in environment)
      *)

      (* XXX : Why do we need to evaluate lambda over here in the current environment
               Is it just to make sure that we are applying things to a function and not any arbitrary expression and also to decompose it into its constituents*)
               
      (match (eval_helper binds lambda) with
        | Closure (idList, body, func_env) -> 
            (* Helper function that evaluates params of 'lambda' function in original environment *)
            (*
            let rec f (exps : expList) : valueList = 
              match exps with
                | ExpList (e, rest) -> ValueList ((eval_helper binds e), f rest)
                | EmptyExpList -> EmptyValueList
            *)
            let rec f (exps : exp list) : valueList = 
              if [] <> exps
              then ValueList ((eval_helper binds (hd exps)), f (tl exps))
              else EmptyValueList

            in eval_helper (augment_env idList (f paramList) func_env) body

        | _ -> failwith "Expected function")

    | Record (recordList) -> failwith "have not implemented yet"
    (* To implement records, we shall convert them into (id * value) list *)
        let f (recordList : (field * exp) list) : (field * value) list =
          if [] <> recordList
          then match (hd recordList) with
                | (field, e) -> RecordValue ((field, eval_helper binds e), f tl recordList)
          else []
        in f recordList

    | SetField (recordList, field, new_e) -> 
    (* lookup field in recordList, if found then evaluate new_e and replace old_e with new_e
    *)
    | GetField (recordList, searchField) -> 
    (* lookup filed in recordList, if found then give the new value*)
    | _ -> failwith "Not yet implemented"

(** Evaluates expressions to values. *)
let eval (e : HOF_syntax.exp) : value = eval_helper EmptyEnv e






  (** Desugars extended HOF to HOF. *)
  (* val desugar : HOF_sugar.exp -> HOF_syntax.exp *)



let exp1 : exp = Let ("x", Int 10, Id ("x"));;
let exp2 : exp = Let ("x", Int 10, Let ("y",
                                        Add (Int 20, Id ("x")),
                                        Add (Id ("x"), Id ("y"))
                                       );
                     );;
let exp3 : exp = Lambda (["a"; "b"; "c";],
                         Add (Id ("a"),
                              Add (Id "b", Id "c")));;


let exp4 : exp = Apply (exp3, [Int (2); Int (3); Int (5);]);;


print_string  (string_of_int (int_of_value (eval (Int 5))) ^ "\n");
print_string  (string_of_int (int_of_value (eval exp2)) ^ "\n");
print_string  (string_of_int (int_of_value (eval exp4)) ^ "\n");



(* TODO : 
 1. Test lookup
 2. Test eval_helper
 3. Test eval
*)
