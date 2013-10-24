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

(* TODO : Make it a map *)
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
                           add_constraint (cgen env et) (E.TId new_t);
                           add_constraint (cgen env ef) (E.TId new_t);
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
                        add_constraint (E.TFun (arg_t,body_t)) (cgen env e1);
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

