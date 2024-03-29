(* Step 1. Placeholder Type Identifiers *)


module I  = Typeinf_syntax.Implicit
module E  = Typeinf_syntax.Explicit
module Id = Identifier



let rec from_implicit (exp : I.exp) : E.exp =
  match exp with
    | I.Int (n) -> E.Int n
    | I.Bool (b) -> E.Bool b
    | I.Arith (op, e1, e2) -> E.Arith (op, from_implicit e1, from_implicit e2)
    | I.Cmp (op, e1, e2) -> E.Cmp (op, from_implicit e1, from_implicit e2)
    | I.If (ec, et, ef) -> E.If (from_implicit ec, from_implicit et, from_implicit ef)
    | I.Id (x) -> E.Id (x)
    | I.Let (x, with_e, in_e) -> E.Let (x, from_implicit with_e, from_implicit in_e)
    | I.Fun (x, body) -> E.Fun (x, E.TId (Id.fresh (Id.to_string x)), from_implicit body)
    | I.Fix (x, e) -> E.Fix (x, E.TId (Id.fresh (Id.to_string x)), from_implicit e)
    | I.App (e1, e2) -> E.App (from_implicit e1, from_implicit e2)
    | I.Empty -> E.Empty (E.TId (Id.fresh "empty"))
    | I.Cons (e1, e2) -> E.Cons (from_implicit e1, from_implicit e2)
    | I.Head (e) -> E.Head (from_implicit e)
    | I.Tail (e) -> E.Tail (from_implicit e)
    | I.IsEmpty (e) -> E.IsEmpty (from_implicit e)
    | I.Pair (e1, e2) -> E.Pair (from_implicit e1, from_implicit e2)
    | I.ProjL (e) -> E.ProjL (from_implicit e)
    | I.ProjR (e) -> E.ProjR (from_implicit e)



(* Step 2. Constraint Generation *)

type constraints = (E.typ * E.typ) list

let cs : constraints ref = ref []

let add_constraint (lhs : E.typ) (rhs : E.typ) : unit =
  cs := (lhs, rhs)::!cs


let print_list (lst : (E.typ * E.typ) list) : unit =
  let open Typeinf_util in
  let f ((t1,t2) : E.typ * E.typ) : unit =
    print_string ((string_of_typ t1) ^ " : " ^ (string_of_typ t2) ^ "\n") in
  List.iter f lst

  

let print_constraints () : unit =
  print_list !cs

type env = (Id.t * E.typ) list

let empty_env = []

let lookup (env : env) (x : Id.t) : E.typ = 
  List.assoc x env

let augment_env (env : env) (x : Id.t) (t : E.typ) : env =
  (x,t)::env




let rec cgen (env : env) (exp : E.exp) : E.typ =
  match exp with 

    | E.Int (n) -> E.TInt

    | E.Bool (b) -> E.TBool

    | E.Arith (op, e1, e2) -> add_constraint (cgen env e1) E.TInt;
                              add_constraint (cgen env e2) E.TInt;
                              E.TInt

    | E.Cmp (op, e1, e2) -> add_constraint (cgen env e1) E.TInt;
                            add_constraint (cgen env e2) E.TInt;
                            E.TBool

    | E.If (ec, et, ef) -> (* Constraints :
                            *   1. type of ec has to be 'bool'
                            *   2. type of "et" has to be same as that of "ef"
                            *)
                           add_constraint (cgen env ec) E.TBool;
                           let new_t = Id.fresh "t_id" in
                           add_constraint (E.TId new_t) (cgen env et) ;
                           add_constraint (E.TId new_t) (cgen env ef) ;
                           E.TId new_t

    | E.Id (x) -> (* lookup the type in the environment *)
       (try lookup env x 
        with Not_found -> failwith ("Unbound identifier : " ^ (Id.to_string x)))

    | E.Let (x, with_e, in_e) ->  (* Constraints :
                                   * 1. Generate constraints for with_e
                                   * 2. Assign the same type to x in the environment
                                   * 3. add constraints for in_e and return the type of in_e
                                   *)
                                   let with_e_t = cgen env with_e in
                                   let env' = augment_env env x with_e_t in
                                   cgen env' in_e

    | E.Fun (x, x_t, body) -> let env' = augment_env env x x_t in
                              E.TFun (x_t, cgen env' body)

    | E.Fix (x, x_t, e) -> (* x_t has to be a function *)
                           let env' = augment_env env x x_t in
                           let t_e = cgen env' e in
                           add_constraint x_t t_e;
                           t_e

    | E.App (e1, e2) -> (* e1 has to have a type of function 
                         * e2 should match the type of the argument expected by function of e1
                         * type of the App should be the type of e1 body *)
                        let arg_t  = E.TId (Id.fresh "arg_t") in
                        let body_t = E.TId (Id.fresh "body_t") in
                        add_constraint (cgen env e1) (E.TFun (arg_t, body_t)) ;
                        add_constraint arg_t (cgen env e2);
                        body_t

    | E.Empty (t) -> E.TList t

    | E.Cons (e1, e2) -> let t = E.TId (Id.fresh "t") in
                         add_constraint (cgen env e2) (E.TList t) ;
                         add_constraint t (cgen env e1);
                         E.TList t

    | E.Head (e) -> let t = E.TId (Id.fresh "t") in
                    add_constraint (cgen env e) (E.TList t);
                    t

    | E.Tail (e) -> let t = E.TId (Id.fresh "t") in
                    add_constraint (cgen env e) (E.TList t);
                    E.TList t

    | E.IsEmpty (e) -> let t = E.TId (Id.fresh "t") in
                       add_constraint (cgen env e) (E.TList t);
                       E.TBool

    | E.Pair (e1, e2) -> E.TPair (cgen env e1, cgen env e2)

    | E.ProjL (e) -> let tpl = E.TId (Id.fresh "tpl") in
                     let tpr = E.TId (Id.fresh "tpr") in
                     add_constraint (cgen env e) (E.TPair (tpl, tpr));
                     tpl

    | E.ProjR (e) -> let tpl = E.TId (Id.fresh "tpl") in
                     let tpr = E.TId (Id.fresh "tpr") in
                     add_constraint (cgen env e) (E.TPair (tpl, tpr));
                     tpr




(* Step 3. Constraint Solving *)

module type SUBST = sig
  type t

  val empty     : t
  val singleton : Id.t -> E.typ -> t
  val apply     : t -> E.typ -> E.typ
  val compose   : t -> t -> t
  val to_list   : t -> (Id.t * E.typ) list
end

module Subst : SUBST = struct

  module TypMap = Map.Make (Id)

  type t = E.typ TypMap.t


  let to_list (s : t) : (Id.t * E.typ) list =
    let f (x : Id.t) (v: E.typ) (acc : (Id.t * E.typ) list) : (Id.t * E.typ) list =
      (x,v)::acc
    in TypMap.fold f s []


  let rec occurs_check (x : Id.t) (term : E.typ) : bool = 
    match term with
      | E.TId (x') -> x = x'

      | E.TInt
      | E.TBool -> false

      | E.TFun (t1, t2) 
      | E.TPair (t1, t2) -> (occurs_check x t1) ||
                            (occurs_check x t2)

      | E.TList (t') -> occurs_check x t'


  let singleton (x : Id.t) (t : E.typ) : t =
    TypMap.add x t TypMap.empty

  let empty = TypMap.empty


  (* Takes in a substitution map and apply it to typ received producing a new type *)
  let rec apply (s : t) (typ : E.typ) : E.typ =
    match typ with
      | E.TId (x) -> (try 
                      apply s (TypMap.find x s)
                      with Not_found -> typ)
      | E.TInt -> E.TInt
      | E.TBool -> E.TBool
      | E.TFun (t1, t2) -> E.TFun ((apply s t1), (apply s t2))
      | E.TPair (t1, t2) -> E.TPair ((apply s t1), (apply s t2))
      | E.TList (t') -> E.TList (apply s t')


  (* 
   * Composition algorithm
   * s1 = { x1 |=> t1, x2 |=> t2 .. xn |=> tn }
   * s2 = { y1 |=> u1, y2 |=> u2 .. yn |=> yn }
   *
   * compose s1 s2 => s1 o s2
   *  - A new set having the elems : x1 |=> t1 s2, x2 |=> t2 s2, ... xn |=> tn s2
   *  - Delete the following members later : tm s2 = xm, ui/yi such that yi is in {x1, x2 .. xn}
   *)

  let compose (s1 : t) (s2 : t) : t =
    (* 1. Transform s1 by : for all rhs in s1 apply s2
     * 2. prune the transform removing identity forms
     * 3. Add to transform those variables in lhs of s2 that don't occur in lhs of s1 
     *)
    (* Apply 1. *)
    let sf = (TypMap.map (apply s2) s1) in
    let f (x : Id.t) (v : E.typ) : bool = not (E.TId (x) = v) in
    let mf (x : Id.t) (v1 : E.typ option) (v2 : E.typ option) : E.typ option =
      (match v1, v2 with
        | Some v1', Some v2' ->  add_constraint v1' v2'; v1 
        | Some _, None -> v1
        | None, Some _ -> v2
        | _, _ -> failwith "should not have happened") in

    (* Apply 2. & 3. *)
    let final_subst = TypMap.filter f (TypMap.merge mf sf s2) in

    (* occurs-check *)
    let occurs_check_wrap (x : Id.t) (v : E.typ) : bool =
      not (occurs_check x v) in

    if TypMap.for_all occurs_check_wrap final_subst
    then final_subst
    else failwith "occurs check failed"

end




(* 
 * Write the unification algorithm 
 *    1) Takes two types as arguments 
 *    2) Produces a substitution that maps identifiers to types
 *
 *    Some properties
 *    1) Unification of distinct base types should fail
 *    2) Unification of identical base types should return empty substitution
 *    3) Unification with variable should produce a singleton substitution
 *    4) Unification should recur into type constructors
 *    5) Unification failures may occur across recursive cases
 *    6) unification should produce a substitution that is transitively closed
 *)

let rec unify (t_lhs : E.typ) (t_rhs : E.typ) : Subst.t =

  if t_lhs = t_rhs
  then Subst.empty
  else
    
    match t_lhs, t_rhs with

    | E.TId (x), E.TId (y) -> (* impose ordering *)
                              if (Id.compare x y) < 0
                              then Subst.singleton x t_rhs
                              else Subst.singleton y t_lhs

    (* Empty set is identity for compose. 'compose' provides implicit occurs check *)
    | E.TId (x), _ -> Subst.compose Subst.empty (Subst.singleton x t_rhs) 
    | _, E.TId (x) -> Subst.compose Subst.empty (Subst.singleton x t_lhs)

    (* | E.TInt, E.TInt -> Subst.empty *)
    | _, E.TInt
    | E.TInt, _ -> failwith "unification failed"

    (* | E.TBool, E.TBool -> Subst.empty *)
    | _, E.TBool
    | E.TBool, _ -> failwith "unification failed"

    | E.TFun (t1, t2), E.TFun (t1', t2') -> Subst.compose (unify t1 t1') (unify t2 t2')
    | _, E.TFun _
    | E.TFun _, _ -> failwith "unification failed"

    | E.TPair (t1, t2), E.TPair (t1', t2') -> Subst.compose (unify t1 t1') (unify t2 t2')
    | _, E.TPair _
    | E.TPair _, _ -> failwith "unification failed"

    | E.TList (t1), E.TList (t1') -> unify t1 t1'
    (* | _, E.TList _ *)
    (* | E.TList _, _ -> failwith "type error" *)



(* Step 5. Constraint solving *)

(*
let solve_constraints () : Subst.t = 
  let f (acc : Subst.t) ((t1,t2) : E.typ * E.typ) : Subst.t =
    print_string ("Here\n");
    print_string (Typeinf_util.string_of_typ t1);
    print_string ("\n");
    print_string (Typeinf_util.string_of_typ t2);
    print_string ("\n");
    Subst.compose acc (unify t1 t2) in
  List.fold_left f Subst.empty !cs
*)


let rec _solve_constraints (s : Subst.t) : Subst.t =
  if [] <> !cs
  then let (t1, t2) = List.hd !cs in
       cs := List.tl !cs;
       _solve_constraints (Subst.compose s (unify t1 t2))
  else s

let solve_constraints () : Subst.t  =
  _solve_constraints (Subst.empty)
  

(* Step 6 : Type annotation *)

let rec annotate_types (s : Subst.t) (exp : E.exp) : E.exp =

  match exp with

    | E.Int (n) -> E.Int (n)

    | E.Bool (b) -> E.Bool (b)

    | E.Arith (op, e1, e2) -> E.Arith (op, annotate_types s e1,
                                           annotate_types s e2)

    | E.Cmp (op, e1, e2) -> E.Cmp (op, annotate_types s e1,
                                       annotate_types s e2)

    | E.If (ec, et, ef) -> E.If (annotate_types s ec,
                                 annotate_types s et,
                                 annotate_types s ef)

    | E.Id (x) -> E.Id (x)

    | E.Let (x, with_e, in_e) ->  E.Let (x, annotate_types s with_e,
                                            annotate_types s in_e)

    | E.Fun (x, x_t, e) ->
      let t = Subst.apply s x_t in
      E.Fun (x, t, annotate_types s e)

    | E.Fix (x, x_t, e) -> 
      let t = Subst.apply s x_t in
      E.Fix (x, t, annotate_types s e)


    | E.App (e1, e2) -> E.App (annotate_types s e1,
                               annotate_types s e2)

    | E.Empty (t) -> E.Empty (Subst.apply s t)

    | E.Cons (e1, e2) -> E.Cons (annotate_types s e1,
                                 annotate_types s e2)

    | E.Head (e) -> E.Head (annotate_types s e)

    | E.Tail (e) -> E.Tail (annotate_types s e)

    | E.IsEmpty (e) -> E.IsEmpty (annotate_types s e)

    | E.Pair (e1, e2) -> E.Pair (annotate_types s e1,
                                  annotate_types s e2)

    | E.ProjL (e) -> E.ProjL (annotate_types s e)

    | E.ProjR (e) -> E.ProjR (annotate_types s e)




(* Step 7 : Type Checking (Optional Sanity Check) *)
let rec tc (env : env) (exp : E.exp) : E.typ =
  match exp with
    | E.Int _ -> E.TInt
    | E.Bool _ -> E.TBool

    | E.Arith (_, e1, e2) -> 
        (match tc env e1, tc env e2 with
           | E.TInt, E.TInt -> E.TInt
           | _ , _ -> failwith "Type checking failed") 

    |E.Cmp (_, e1, e2) -> 
       (match tc env e1, tc env e2 with
          | E.TInt, E.TInt -> E.TBool
          | _ , _ -> failwith "Type checking failed") 

    | E.If (e_cond, e_true, e_false) ->
        let t_e_cond = tc env e_cond in
        let t_e_true = tc env e_true in
        let t_e_false = tc env e_false in
        if t_e_cond = E.TBool && t_e_true = t_e_false then t_e_true
        else failwith "Type checking failed"

    | E.Id (x) -> lookup env x

    | E.Let (x, with_e, in_e) -> 
        let env' = augment_env env x (tc env with_e) in
        tc env' in_e


    | E.Fun (x, t_x, body) -> 
        let env' = augment_env env x t_x in
        E.TFun (t_x, tc env' body)

    | E.Fix (x, t_x, e) -> 
        let env' = augment_env env x t_x in
        let t_e = tc env' e in
        if t_e = t_x
        then 
        (match t_x with
          | E.TFun (_,_) -> t_x
          | _ -> failwith ("Fix : expected a function"))
        else failwith ("Fix: types mismatch")

    | E.App (e1, e2) ->
        let t_e1 = tc env e1 in
        let t_e2 = tc env e2 in
        (match t_e1 with
           | E.TFun (t_param, t_body) -> 
              if t_e2 = t_param 
              then t_body 
              else failwith "Function application type mismatch"
           | _ -> failwith "application type mismatch")

    | E.Empty (t) -> E.TList (t)

    | E.Cons (e1, e2) -> 
        let t_hd = tc env e1 in
        let t_rest = tc env e2 in
        (match t_rest with
         | E.TList (t) -> 
             if t_hd = t
             then t_rest
             else failwith "Cons : Type mismatch"

         | _ -> failwith "Cons : Not a list")

    | E.Head (e) -> 
       let t_exp = tc env e in
       (match t_exp with
                      | E.TList (t) -> t
                      | _ -> failwith "Head : Not a list")


    | E.Tail (e) -> let t_exp = tc env e in
                  (match t_exp with
                     | E.TList (_) -> t_exp
                     | _ -> failwith "Tail : Not a list")

    | E.IsEmpty (e) -> 
        let t_exp = tc env e in
        (match t_exp with
           | E.TList _ -> E.TBool
           | _ -> failwith "IsEmpty : Not a list")
                      

    | E.Pair (e1, e2) -> E.TPair (tc env e1, tc env e2)

    | E.ProjL (e) -> let t_exp = tc env e in
                   (match t_exp with
                      | E.TPair (t_left, _) -> t_left
                      | _-> failwith "ProjL : Not a pair")

   | E.ProjR (e) -> let t_exp = tc env e in
                  (match t_exp with
                     | E.TPair (_, t_right) -> t_right
                     | _ -> failwith "ProjR : Not a pair")


(* Step 8 : Finish *)

let typinf (i_exp : I.exp) : E.exp =
  let e_exp = from_implicit (i_exp) in
  let _ = cgen empty_env e_exp in (* Generate constraints *)
  (* print_constraints (); *)
  let substs = solve_constraints () in (* Solve constraints using unification *)
  let e_annot = annotate_types substs e_exp in
  (*Sanity check *)
  let _ = tc empty_env e_annot in
  e_annot



let rec repl () = 
  print_string "> ";
  match Typeinf_util.parse (read_line ()) with
    | Typeinf_util.Exp exp -> 
        let e = typinf exp in
        print_string (Typeinf_util.string_of_exp e);
        print_newline ();
        repl ()
    | Typeinf_util.ParseError msg ->
        print_string msg;
        print_newline ();
        repl ()


let _ =  
  match Array.to_list Sys.argv with
    | [ exe; "repl" ] -> print_string "Press Ctrl + C to quit.\n"; repl ()
    
    (* parse from file specified on command line *)
    | [ exe; f] -> (match (Typeinf_util.parse_from_file f) with

                     | Typeinf_util.Exp exp ->
                       let e = typinf exp in
                       print_string (Typeinf_util.string_of_exp e);
                       print_newline ()

                     | Typeinf_util.ParseError msg -> 
                        print_string msg;
                        print_newline ()
                   )
    | _ -> ()







(* Some examples of operations on substitutions *)
let x = Id.fresh "x"
let y = Id.fresh "y"
TEST "Subst.apply should replace x with TInt" =
  let s = Subst.singleton x E.TInt in
  Subst.apply s (E.TId x) = E.TInt

TEST "Subst.apply should recur into type constructors" =
  let s = Subst.singleton x E.TInt in
  Subst.apply s (E.TFun (E.TId x, E.TBool)) = (E.TFun (E.TInt, E.TBool))

TEST "Subst.compose should distribute over Subst.apply (1)" =
  let s1 = Subst.singleton x E.TInt in
  let s2 = Subst.singleton y E.TBool in
  Subst.apply (Subst.compose s1 s2) (E.TFun (E.TId x, E.TId y)) =
  Subst.apply s1 (Subst.apply s2 (E.TFun (E.TId x, E.TId y)))

TEST "Subst.compose should distribute over Subst.apply (2)" =
  let s1 = Subst.singleton x E.TBool in
  let s2 = Subst.singleton y (E.TId x) in
  Subst.apply (Subst.compose s1 s2) (E.TFun (E.TId x, E.TId y)) =
  Subst.apply s1 (Subst.apply s2 (E.TFun (E.TId x, E.TId y)))




(* An incomplete suite of tests for unification *)
TEST "unifying identical base types should return the empty substitution" =
  Subst.to_list (unify E.TInt E.TInt) = []

TEST "unifying distinct base types should fail" =
  try let _ = unify E.TInt E.TBool in false
  with Failure "unification failed" -> true

TEST "unifying with a variable should produce a singleton substitution" =
  let x = Id.fresh "myvar" in
  Subst.to_list (unify E.TInt (E.TId x)) = [(x, E.TInt)]

TEST "unification should recur into type constructors" =
  let x = Identifier.fresh "myvar" in
  add_constraint (E.TFun (E.TInt, E.TInt)) 
                 (E.TFun (E.TId x, E.TInt));
  Subst.to_list (solve_constraints ()) = 
  [(x, E.TInt)]

TEST "unification failures may occur across recursive cases" =
  try
    let x = Id.fresh "myvar" in  
    add_constraint (E.TFun (E.TInt, E.TId x)) 
                   (E.TFun (E.TId x, E.TBool));
    let _ = solve_constraints () in
    false
  with Failure "unification failed" -> true

TEST "unification should produce a substitution that is transitively closed" =
  let x = Id.fresh "myvar1" in  
  let y = Id.fresh "myvar2" in  
  let z = Id.fresh "myvar3" in  
  add_constraint (E.TFun (E.TFun (E.TInt, E.TId x), E.TId y))
                 (E.TFun (E.TFun (E.TId x, E.TId y), E.TId z));
  let subst = solve_constraints ()  in
  Subst.to_list subst = [ (z, E.TInt); (y, E.TInt); (x, E.TInt) ]

TEST "unification should detect constraint violations that require transitive
      closure" =
  try
    let x = Identifier.fresh "myvar1" in  
    let y = Identifier.fresh "myvar2" in  
    add_constraint (E.TFun (E.TFun (E.TInt, E.TId x), E.TId y))
                   (E.TFun (E.TFun (E.TId x, E.TId y), E.TBool));
    let _ = solve_constraints ()  in
    false
  with Failure "unification failed" -> true

TEST "unification should implement the occurs check (to avoid infinite loops)" =
  try
    let x = Identifier.fresh "myvar" in  
    let _ = unify (E.TFun (E.TInt, E.TId x)) (E.TId x) in
    false (* a bug is likely to cause an infinite loop *)
  with Failure "occurs check failed" -> true
