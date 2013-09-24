open Typed_syntax

module TypeChecker = struct

exception Type_error of string

type tenv = (id * typ) list

let rec string_of_typ (t : typ) : string =
  match t with
    | TNum -> "Integer"
    | TBool -> "Boolean"
    | TFun (t1, t2) -> "f : " ^ (string_of_typ t1)  ^ " -> " (string_of_typ t2)
    | TPair (t1, t2) -> "(" ^ (string_of_typ t1) ^ ", " ^ (string_of_typ t2) ^ ")"
    | TList (t1) -> string_of_typ (t1) ^ "List"

let lookup_typ (x : id) (tev : tenv) : typ =
  try assoc x tev
  with Not_found -> raise (Type_error ("free identifier " ^ x))

let rec exp_type (e: exp) (tev : tenv) : typ =
  match e with
    | Int _ -> TNum
    | Bool _ -> TBool

    | Arith (_, e1, e2) -> match exp_type e1 tev, exp_type e2 tev with
                            | TNum, TNum -> TNum
                            | _ -> raise (Type_error "Arithmetic operator expects integers")

    | Cmp (_, e1, e2) -> match exp_type e1 tev, exp_type e2 tev with
                            | TNum, TNum -> TNum
                            | _ -> raise (Type_error "Comparison operator expects integers")

    | If (e1, e2, e3) -> match exp_type e1 tev with
                          | TBool -> 
                            let t2 = exp_type e2 tev
                            in let t3 = exp_type e3 tev
                               in if t2 = t3 then t2
                                  else raise (Type_error ("Expected expression of type " ^
                                                          (string_of_typ t2) ^ 
                                                          " instead received " ^
                                                          (string_of_typ t3)))

                          | _ -> raise (Type_error "Expected boolean for \"If\" predicate")

    | Id (x) -> lookup_typ x tev

    | Let (x, with_e, in_e) -> let aug_tev = (x, exp_type with_e tev)::tev
                               in  exp_type in_e aug_tev

    | Fun (x, x_typ, body_e) -> let aug_tev = (x, x_type)::tev in TFun (x_typ, exp_type body_e aug_tev)

    | App (func_e, arg_e) -> let t_func =  exp_type func_e tev
                             let t_arg  =  exp_type arg_e  tev
                             in match t_func with
                                  | TFun (t_param, t_body) -> (* param_type should match argument type *)
                                                                    if t_arg = t_param then t_body
                                                                    else raise (Type_error ("Argument mismatch, expected " ^
                                                                                            (string_of_typ t_param) ^
                                                                                            ", instead received " ^
                                                                                            (string_of_typ t_arg)))
                                  | _ -> raise (Type_error ("Expected function, instead received " ^ (string_of_typ t_func)))

    | Fix (x, t_x, e1) -> (* XXX : returns another function *)

    | _ -> raise (Type_error "Not implemented yet")



let type_check (e : exp) : typ = exp_type e []
                           

end

module REPL = Typed_eval.Make (TypeChecker)
