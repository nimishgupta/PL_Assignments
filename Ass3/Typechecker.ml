open Typed_syntax
open List

module TypeChecker = struct

exception Type_error of string

type tenv = (id * typ) list

let rec string_of_typ (t : typ) : string =
  match t with
    | TNum -> "Integer"
    | TBool -> "Boolean"
    | TFun (t1, t2) -> "f : " ^ (string_of_typ t1)  ^ " -> " ^ (string_of_typ t2)
    | TPair (t1, t2) -> "(" ^ (string_of_typ t1) ^ ", " ^ (string_of_typ t2) ^ ")"
    | TList (t1) -> string_of_typ (t1) ^ "List"

(* Looks up type of given identifier 'x' in given environment 'tenv' *)
let lookup_typ (x : id) (tev : tenv) : typ =
  try assoc x tev
  with Not_found -> raise (Type_error ("free identifier " ^ x))



(* Processes an expression (along with its environment) to determine its type and return it
   It may happen that the types may not match as expected, it then throws out an exception *)
let rec exp_type (e: exp) (tev : tenv) : typ =
  match e with
    | Int _ -> TNum
    | Bool _ -> TBool

    (* TODO : Refactor out common code from Arith and Cmp *)
    (* XXX: Shouldn't we check the type of arithOp *)
    | Arith (_, e1, e2) -> (match exp_type e1 tev, exp_type e2 tev with
                              | TNum, TNum -> TNum
                              | _ -> raise (Type_error "Arithmetic operator expects integers"))

    (* XXX: Shouldn't we check the type of intCmp opertor *)
    | Cmp (_, e1, e2) -> (match exp_type e1 tev, exp_type e2 tev with
                            | (TNum, TNum) -> TBool
                            | _ -> raise (Type_error "Comparison operator expects integers"))

    | If (e1, e2, e3) -> (match exp_type e1 tev with
                            | TBool -> 
                              let t2 = exp_type e2 tev in
                              let t3 = exp_type e3 tev in
                              if t2 = t3 then t2
                              else raise (Type_error ("Expected expression of type " ^
                                                      (string_of_typ t2) ^ 
                                                      " instead received " ^
                                                      (string_of_typ t3)))

                            | _ -> raise (Type_error "Expected boolean for \"If\" predicate"))

    | Id (x) -> lookup_typ x tev

    | Let (x, with_e, in_e) -> let aug_tev = (x, exp_type with_e tev)::tev
                               in  exp_type in_e aug_tev

    | Fun (x, x_typ, body_e) -> let aug_tev = (x, x_typ)::tev in TFun (x_typ, exp_type body_e aug_tev)

    | App (func_e, arg_e) -> let t_func =  exp_type func_e tev in
                             let t_arg  =  exp_type arg_e  tev in
                             (match t_func with
                                | TFun (t_param, t_body) -> (* param_type should match argument type *)
                                                            if t_arg = t_param then t_body
                                                            else raise (Type_error ("Argument mismatch, expected " ^
                                                                                    (string_of_typ t_param) ^
                                                                                    ", instead received " ^
                                                                                    (string_of_typ t_arg)))
                                | _ -> (* raise (Type_error ("Expected function, instead received " ^ (string_of_typ t_func)))) *) TNum)

    (* TODO : *)
    (* Fix point function takes the helper as an argument and returns the recursive function *)
    (* x is a function identifier, t_x is the type of that function TFun (t1, t2), e1 is the body containing x *)
    (* it is supposed to give us a function x that can recurse *)
    (* Type of e1 should be t_x and it should be a function TFun (t1, t2) *)
    | Fix (x, t_x, e1) -> (* if x has type t_x and e1 is a function that has type t_x then t_x *)
                          (* TODO : Should we augment the environment *)
                          let aug_tev = (x, t_x)::tev in
                          let t_e1 = exp_type e1 aug_tev (* XXX : Should this be the augmented environment? *) in
                          if t_x = t_e1 then (match t_x with | TFun (_, _) -> t_x | _ -> raise (Type_error ("Fix : Expected a function")))
                          else raise (Type_error ("Fix : Mismatch of types"))


    | Empty (t_emp) -> TList (t_emp)
    | Cons (e1, e2) -> let t_hd = exp_type e1 tev in
                       let t_tl = exp_type e2 tev in
                       (match t_tl with
                          | TList (t_lst_elem) -> if t_hd = t_lst_elem
                                                  then t_tl
                                                  else raise (Type_error ("Expected element of type " ^ (string_of_typ t_lst_elem) ^ " , instead received " ^ (string_of_typ t_hd)))
                          | _ -> raise (Type_error ("Expected " ^ (string_of_typ t_hd) ^ " list, instead received " ^ (string_of_typ t_tl))))

    (* TODO : refactor into "typecheck_list_properties" *)
    | Head (e) -> let t_exp = exp_type e tev in
                  (match t_exp with
                     | TList (t_lst_elem) -> t_lst_elem
                     | _ -> raise (Type_error ("Expected a list, instead received " ^ (string_of_typ t_exp))))

    | Tail (e) -> let t_exp = exp_type e tev in
                  (match t_exp with
                     | TList (t_lst_elem) -> TList (t_lst_elem)
                     | _ -> raise (Type_error ("Expected a list, instead received " ^ (string_of_typ t_exp))))


    | IsEmpty (e) -> let t_exp = exp_type e tev in
                     (match t_exp with
                        | TList (t_lst_elem) -> TBool
                        | _ -> raise (Type_error ("Expected a list, instead received " ^ (string_of_typ t_exp))))

    | Pair (e1, e2) -> TPair (exp_type e1 tev, exp_type e2 tev)

    (* TODO : Refactor into "typecheck_pair_projections" *)
    | ProjL (e) -> let t_exp = exp_type e tev in
                   (match t_exp with
                      | TPair (t1, t2) -> t1
                      | _ -> raise (Type_error ("Expected a pair, instead received " ^ (string_of_typ t_exp))))

    | ProjR (e) -> let t_exp = exp_type e tev in
                   (match t_exp with
                      | TPair (t1, t2) -> t2
                      | _ -> raise (Type_error ("Expected a pair, instead received " ^ (string_of_typ t_exp))))


let type_check (e : exp) : typ = exp_type e []
                           
end

module REPL = Typed_eval.Make (TypeChecker)
