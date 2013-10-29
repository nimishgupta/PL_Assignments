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

type env = (Id.t * E.typ) list

let lookup (env : env) (x : Id.t) : E.typ = 
  failwith "NYI"

let augment_env (env : env) (x : Id.t) (t : E.typ) : env =
  failwith "NYI"




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
                  (* XXX : What if there is a free variable? *)
                  lookup env x

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

    | E.Fix (x, x_t, e) -> failwith "NYI"

    | E.App (e1, e2) -> (* e1 has to have a type of function 
                         * e2 should match the type of the argument expected by function of e1
                         * type of the App should be the type of e1 body *)
                        let arg_t  = E.TId (Id.fresh "arg_t") in
                        let body_t = E.TId (Id.fresh "body_t") in
                        add_constraint (E.TFun (arg_t, body_t)) (cgen env e1);
                        add_constraint arg_t (cgen env e2);
                        body_t

    | E.Empty (t) -> E.TList t

    | E.Cons (e1, e2) -> let t = E.TId (Id.fresh "t") in
                         add_constraint (E.TList t) (cgen env e2);
                         add_constraint t (cgen env e1);
                         E.TList t

    | E.Head (e) -> let t = E.TId (Id.fresh "t") in
                    add_constraint (E.TList t) (cgen env e);
                    t

    | E.Tail (e) -> let t = E.TId (Id.fresh "t") in
                    add_constraint (E.TList t) (cgen env e);
                    E.TList t

    | E.IsEmpty (e) -> let t = E.TId (Id.fresh "t") in
                       add_constraint (E.TList t) (cgen env e);
                       E.TBool

    | E.Pair (e1, e2) -> E.TPair (cgen env e1, cgen env e2)

    | E.ProjL (e) -> let tpl = E.TId (Id.fresh "tpl") in
                     let tpr = E.TId (Id.fresh "tpr") in
                     add_constraint (E.TPair (tpl, tpr)) (cgen env e);
                     tpl

    | E.ProjR (e) -> let tpl = E.TId (Id.fresh "tpl") in
                     let tpr = E.TId (Id.fresh "tpr") in
                     add_constraint (E.TPair (tpl, tpr)) (cgen env e);
                     tpr




(* Step 3. Constraint Solving *)

module type SUBST = sig
  type t

  val empty     : t
  val singleton : Id.t -> E.typ -> t
  val apply     : t -> E.typ -> E.typ
  val compose   : t -> t -> t
end

module Subst : SUBST = struct

  module TypMap = Map.Make (Id)

  type t = E.typ TypMap.t

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
   * TODO : 
   *
   * - Maintain transitive closures x |=> y, y |=> x is effectively occurs-check with transitivity
   * - Maintain the property of distributivity over apply
   *     apply (compose s1 s2) e => apply s1 (apply s2 e)
   * - Match base types for duplicate variables
   * - It might as well introduce new substitution variables 
   *    x |=> TInt, x |=> y gives x |=> TInt & y |=> TInt
   *)

  (* 
   * Composition algorithm
   * s1 = { x1 |=> t1, x2 |=> t2 .. xn |=> tn }
   * s2 = { y1 |=> u1, y2 |=> u2 .. yn |=> yn }
   *
   * compose s1 s2 => s1 o s2
   *  - A new set having the elems : x1 |=> t1 s2, x2 |=> t2 s2, ... xn |=> tn s2
   *  - Delete the following members later : tm s2 = xm, ui/yi such that yi is in {x1, x2 .. xn}
   *
   * TODO : Perform an occurs-check later
   *)
  let compose (s1 : t) (s2 : t) : t =
    (* Transform s1 by : for all rhs in s1 apply s2
     * prune the transform removing identity forms
     * Add to transform those variables in lhs of s2 that don't occur in lhs of s1 
     *)
    let sf = (TypMap.map (apply s2) s1) in
    let mf (x : Id.t) (v1 : E.typ option) (v2 : E.typ option) : E.typ option =
      (match v1, v2 with
        | Some v1', Some _ -> Some v1'
        | Some v1', None -> Some v1'
        | None, Some v2' -> Some v2'
        | _, _ -> failwith "should not have happened") in

    let f (x : Id.t) (v : E.typ) : bool = 
      not (E.TId (x) = v) in

    TypMap.filter f (TypMap.merge mf sf s2)

end


(* TODO : Move into substitution and make occurs-check implicit part of substitution *)
(* TODO : Rewrite : Taking a map of substitutions into account *)
let rec occurs_check (x : Id.t) (term : E.typ) : bool = 
  match term with
    | E.TId (x') -> x = x'

    | E.TInt
    | E.TBool -> false

    | E.TFun (t1, t2) 
    | E.TPair (t1, t2) -> (occurs_check x t1) || (occurs_check x t2)

    | E.TList (t') -> occurs_check x t'


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

    (* TODO : Unify with empty set, occurs check would then be implicit *)
    | E.TId (x), _ -> if occurs_check x t_rhs 
                      then failwith "occurs-check failed"
                      else Subst.singleton x t_rhs

    | _, E.TId (x) -> if occurs_check x t_lhs 
                      then failwith "occurs-check failed"
                      else Subst.singleton x t_lhs

    (* | E.TInt, E.TInt -> Subst.empty *)
    | _, E.TInt
    | E.TInt, _  -> failwith "type error"

    (* | E.TBool, E.TBool -> Subst.empty *)
    | _, E.TBool
    | E.TBool, _ -> failwith "type error"

    | E.TFun (t1, t2), E.TFun (t1', t2') -> Subst.compose (unify t1 t1') (unify t2 t2')
    | _, E.TFun _
    | E.TFun _, _ -> failwith "type error"

    | E.TPair (t1, t2), E.TPair (t1', t2') -> Subst.compose (unify t1 t1') (unify t2 t2')
    | _, E.TPair _
    | E.TPair _, _ -> failwith "type error"

    | E.TList (t1), E.TList (t1') -> unify t1 t1'
    (* | _, E.TList _ *)
    (* | E.TList _, _ -> failwith "type error" *)


let solve_constraints () : Subst.t = 
  let f (acc : Subst.t) ((t1,t2) : E.typ * E.typ) : Subst.t =
    Subst.compose acc (unify t1 t2) in
  List.fold_left f Subst.empty !cs



(* Write occurs check taking substitution into account
 * Write a type checker, adapt from HOF
 * Bring the stages together
 * Write unit tests
 * Write functional tests
 * Give a thought to transitive closure
 *)


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

