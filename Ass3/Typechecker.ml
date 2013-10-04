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

    | Arith (_, e1, e2) -> (match exp_type e1 tev, exp_type e2 tev with
                              | TNum, TNum -> TNum
                              | _ -> raise (Type_error "Arithmetic operator expects integers"))

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
                                | _ -> raise (Type_error ("Expected function, instead received " ^ (string_of_typ t_func))))

    (* Fix point function takes the helper as an argument and returns the recursive function *)
    (* x is a function identifier, t_x is the type of that function TFun (t1, t2), e1 is the body containing x *)
    (* it is supposed to give us a function x that can recurse *)
    (* Type of e1 should be t_x and it should be a function TFun (t1, t2) *)
    | Fix (x, t_x, e1) -> (* if x has type t_x and e1 is a function that has type t_x then t_x *)
                          let aug_tev = (x, t_x)::tev in
                          let t_e1 = exp_type e1 aug_tev in
                          if t_x = t_e1 then 
                            (match t_x with
                               | TFun (_, _) -> t_x 
                               | _ -> raise (Type_error ("Fix : Expected a function")))
                          else raise (Type_error ("Fix : Mismatch of types"))


    | Empty (t_emp) -> TList (t_emp)
    | Cons (e1, e2) -> let t_hd = exp_type e1 tev in
                       let t_tl = exp_type e2 tev in
                       (match t_tl with
                          | TList (t_lst_elem) -> if t_hd = t_lst_elem
                                                  then t_tl
                                                  else raise (Type_error ("Expected element of type " ^ (string_of_typ t_lst_elem) ^ " , instead received " ^ (string_of_typ t_hd)))
                          | _ -> raise (Type_error ("Expected " ^ (string_of_typ t_hd) ^ " list, instead received " ^ (string_of_typ t_tl))))

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


let tc = TypeChecker.type_check

(* Int *)
TEST = tc (Int (0)) = TNum
(* Bool *)
TEST = tc (Bool (true)) = TBool

(* Arith *)
TEST = tc (Arith (Plus, Int (0), Int (1))) = TNum
TEST = (try tc (Arith (Plus, Int (0), Bool (false))) = TNum
        with TypeChecker.Type_error _ -> false) = false

TEST = (try tc (Arith (Plus, Bool (true), Int (0))) = TNum
        with TypeChecker.Type_error _ -> false) = false

TEST = (try (tc (Arith (Plus, Bool (true), Bool (true)))) = TNum
        with TypeChecker.Type_error _ -> false) = false

TEST = tc (Arith (Plus, Arith (Plus, Int (0), Int (0)),
                        Arith (Minus, Int (1), Int (1)))) = TNum

(* Cmp *)
TEST = tc (Cmp (LT, Int (0), Int (1))) = TBool
TEST = tc (Cmp (LT, Int (0), Int (1))) = TBool
TEST = try TBool = tc (Cmp (LT, Int (0), Bool (true)))
       with TypeChecker.Type_error _ -> false = false
TEST = try TBool = tc (Cmp (LT, Bool (true), Int (0)))
       with TypeChecker.Type_error _ -> false = false
TEST = try TBool = tc (Cmp (LT, Bool (true), Bool (false)))
       with TypeChecker.Type_error _ -> false = false


(* If *)
TEST = tc (If (Bool (true), Int (0), Int (1))) = tc (Int (0))
TEST = tc (If (Bool (true), Bool (true), Bool (false))) = tc (Bool (false))
TEST = try TNum = tc (If (Int (0), Int (0), Int (0)))
       with TypeChecker.Type_error _ -> false = false
TEST = try TNum = tc (If (Bool (true), Int (0), Bool (false)))
       with TypeChecker.Type_error _ -> false = false
TEST = try TNum = tc (If (Bool (false), Bool (true), Int (0)))
       with TypeChecker.Type_error _ -> false = false


(* Id *)

(* Let *)
TEST = tc (Let ("x", Int (5), Arith (Plus, Id ("x"), Int (3)))) = TNum
TEST = try TNum  = tc (Let ("x", Int (5), If (Id ("x"), Int (0), Int (5))))
       with TypeChecker.Type_error _ -> false = false
TEST = tc (Let ("x", Int (5), Cmp (LT, Int (9), Int (3)))) = TBool

(* Fun *)

TEST = tc (Fun ("x", TNum, Arith (Plus, Id ("x"), Int (5)))) = TFun (TNum, TNum)
TEST = try TFun (TNum, TNum)  = tc (Fun ("x", TNum, If (Id ("x"), Int (0), Int (5))))
       with TypeChecker.Type_error _ -> false = false
TEST = tc (Fun ("x", TNum, Cmp (LT, Int (9), Int (3)))) = TFun (TNum, TBool)


(* App *)
let f1 = Fun ("x", TNum, Arith (Plus, Id ("x"), Int (5)))
let f2 = Fun ("x", TNum, Arith (Plus, Int (9), Int (0)))
let f3 = Fun ("x", TNum, If (Int (0), Int (9), Int (0)))
TEST = tc (App (f1, Int (0))) = TNum
(* blow up the match for function param and argument *)
TEST = try TNum = tc (App (f1, Bool (true)))
       with TypeChecker.Type_error _ -> false = false
(* Pass (Not a function) *)
TEST = try TNum = tc (App (Int (0), Int (5)))
       with TypeChecker.Type_error _ -> false = false
(* blow up the function *)
TEST = try TNum = tc (App (f3, Int (9)))
       with TypeChecker.Type_error _ -> false = false
(* blow up the argument *)
TEST = try TNum = tc (App (f1, If (Int (0), Int (0), Int (0))))
       with TypeChecker.Type_error _ -> false = false


(* Fix *)
(* Normal case (factorial) *)
TEST = tc (Fix ("self", TFun (TNum, TNum),
                Fun ("n", TNum, If (Cmp (EQ, Id "n", Int (0)),
                                    Int (1),
                                    Arith (Times,
                                           Id ("n"),
                                            App (Id "self",
                                                 Arith (Minus,
                                                        Id "n",
                                                         Int (-1)))))))) = TFun (TNum, TNum)

(* e1 blows up *)
TEST = try TFun (TNum, TNum) = tc (Fix ("self", TFun (TNum, TNum),
                                        Fun ("n", TNum,
                                              Arith (Plus,
                                                     Bool (true),
                                                     Int (0)))))
       with TypeChecker.Type_error _ -> false  = false

(* type of e1 <> t_x *)
TEST = try TFun (TNum, TNum) = tc (Fix ("self", TFun (TNum, TNum),
                                        Fun ("n", TBool,
                                             If (Id "n", Bool (true), App (Id "self", Bool (true))))))
       with TypeChecker.Type_error _ -> false = false


(* t_s is not a function *)
TEST = try TFun (TNum, TNum) = tc (Fix ("self", TFun (TNum, TNum),
                                        Int (0)))
       with TypeChecker.Type_error _ -> false = false




(* Empty *)
TEST = tc (Empty (TNum)) = TList (TNum)
TEST = tc (Empty (TBool)) = TList (TBool)

(* Cons *)

(* Same type *)
TEST = tc (Cons (Int (0), Empty (TNum))) = TList (TNum)
TEST = tc (Cons (Bool (true), Empty (TBool))) = TList (TBool)

(* Different Type *)
TEST = try TList (TNum) = tc (Cons (Empty (TNum), Int (3)))
       with TypeChecker.Type_error _ -> false = false

(* Cons with Cons *)
TEST = tc (Cons (Int (0), Cons (Int (0), Empty (TNum)))) = TList (TNum)

(* e1 blows up *)
TEST = try TList (TNum) = tc (Cons (Arith (Plus, Int (0), Bool (true)), Empty (TNum)))
       with TypeChecker.Type_error _ -> false = false

(* e2 blows up *)
TEST = try TList (TNum) = tc (Cons (Int (0), Arith (Plus, Int (0), Bool (true))))
       with TypeChecker.Type_error _ -> false = false



let l1 = Cons (Int (3), Empty (TNum))
(* Head *)
(* List *)
TEST = tc (Head (l1)) = TNum
(* Non List *)
TEST = try TNum = tc (Head (Int (0)))
       with TypeChecker.Type_error _ -> false = false
(* Empty *)
TEST = try TNum = tc (Head (Empty (TNum)))
       with TypeChecker.Type_error _ -> false = false

(* e blows up *)
TEST = try TNum = tc (Head (Arith (Plus, Int (0), Bool (false))))
       with TypeChecker.Type_error _ -> false = false


(* Tail *)
(* List *)
TEST = tc (Tail (l1)) = TList (TNum)
(* Non List *)
TEST = try TList (TNum) = tc (Tail (Int (0)))
       with TypeChecker.Type_error _ -> false = false
(* Empty *)
TEST = try TList (TNum) = tc (Tail (Empty (TNum)))
       with TypeChecker.Type_error _ -> false = false

(* e blows up *)
TEST = try TList (TNum) = tc (Tail (Arith (Plus, Int (0), Bool (false))))
       with TypeChecker.Type_error _ -> false = false



(* IsEmpty *)
TEST = tc (IsEmpty (l1)) = TBool
(* Non List *)
TEST = try TBool = tc (IsEmpty (Int (0)))
       with TypeChecker.Type_error _ -> false = false
(* Empty *)
TEST = try TBool = tc (IsEmpty (Empty (TNum)))
       with TypeChecker.Type_error _ -> false = false

(* e blows up *)
TEST = try TBool = tc (IsEmpty (Arith (Plus, Int (0), Bool (false))))
       with TypeChecker.Type_error _ -> false = false




(* Pairs *)
(* e1, e2 same *)
TEST = tc (Pair (Int (0), Int (1))) = TPair (TNum, TNum)
(* e1, e2 different *)
TEST = tc (Pair (Int (0), Bool (false))) = TPair (TNum, TBool)
(* e1 blows up *)
TEST = try TPair (TNum, TBool) = tc (Pair (Arith (Plus, Int (0), Bool (true)),
                                           Bool (false)))
       with TypeChecker.Type_error _ -> false = false

(* e2 blows up *)
TEST = try TPair (TNum, TBool) = tc (Pair (Bool (true),
                                           Arith (Plus, Int (0), Bool (true))))
       with TypeChecker.Type_error _ -> false = false


let p1 = Pair (Int (0), Bool (false))

(* Projection Left *)
(* pair *)
TEST = tc (ProjL (p1)) = TNum
(* not a pair *)
TEST = try TNum = tc (ProjL (Int (0)))
       with TypeChecker.Type_error _ -> false = false
(* expression blows up *)
TEST = try TNum = tc (ProjL (Pair (Arith (Plus, Int (0), Bool (false)),
                                   Bool (false))))
       with TypeChecker.Type_error _ -> false = false
                                            


(* Projection Right *)
(* pair *)
TEST = tc (ProjR (p1)) = TBool
(* not a pair *)
TEST = try TBool = tc (ProjR (Int (0)))
       with TypeChecker.Type_error _ -> false = false
(* expression blows up *)
TEST = try TBool = tc (ProjR (Pair (Arith (Plus, Int (0), Bool (false)),
                                   Bool (false))))
       with TypeChecker.Type_error _ -> false = false





module REPL = Typed_eval.Make (TypeChecker)
