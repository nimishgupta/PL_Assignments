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

type constraints = (E.exp * E.typ) list


let cs : constraints ref = ref []


let add_constraint (e : E.exp) (t : E.typ) : unit =
  cs := (e, t)::!cs


let cgen (env : env) (exp : E.exp) : E.typ =
  match exp with 

    | E.Int (n) -> add_constraint n E.TInt,
                   E.TInt

    | E.Bool (b) -> add_constraint b E.TBool,
                    E.TBool

    | E.Arith (op, e1, e2) -> cgen env e1,
                              cgen env e2,
                              add_constraint e1 E.TInt,
                              add_constraint e2 E.Tint,
                              E.TInt

    | E.Cmp (op, e1, e2) -> cgen env e1,
                            cgen env e2,
                            add_constraint e1 E.Int,
                            add_constraint e2 E.Int,
                            E.TBool

    | E.If (ec, et, ef) -> cgen env ec,
                           cgen env et,
                           cgen env ef,
                           (* Constraints :
                            *   1. type of ec has to be 'bool'
                            *   2. type of "et" has to be same as that of "ef"
                            *)
                           add_constraint ec E.TBool,
                           let new_t = Id.fresh "t_id" in
                           add_constraint et new_t,
                           add_constraint ef new_t,
                           new_t

    | E.Id (x) -> (* lookup the type in the environment *)
                  (* XXX : What if there is a free variable? *)
                  lookup env x

    | E.Let (x, with_e, in_e) ->  (* Constraints :
                                   * 1. Generate constraints for with_e
                                   * 1. Assign a new type to with_e
                                   * 2. Assign the same type to x in the environment
                                   * 3. add constraints for in_e
                                   * 4. Assign a new type to in_e 
                                   *)
                                   cgen env with_e,
                                   let new_t = Id.fresh (Id.to_string x) in
                                   let env' = augment_env x new_t in
                                   add_constraint with_e new_t,
                                   add_constraint x      new_t,
                                   cgen env' in_e,
                                   let in_e_t = Id.fresh "t_id" in
                                   add_constraint in_e in_e_t,
                                   in_e_t

    | E.Fun (x, body) -> E.Fun (x, E.TId (Id.fresh (Id.to_string x)), cgen env body)
    | E.Fix (x, e) -> E.Fix (x, E.TId (Id.fresh (Id.to_string x)), cgen env e)
    | E.App (e1, e2) -> E.App (cgen env e1, cgen env e2)
    | E.Empty -> E.Empty (E.TId (Id.fresh "empty"))
    | E.Cons (e1, e2) -> E.Cons (cgen env e1, cgen env e2)
    | E.Head (e) -> E.Head (cgen env e)
    | E.Tail (e) -> E.Tail (cgen env e)
    | E.IsEmpty (e) -> E.IsEmpty (cgen env e)
    | E.Pair (e1, e2) -> E.Pair (cgen env e1, cgen env e2)
    | E.ProjL (e) -> E.ProjL (cgen env e)
    | E.ProjR (e) -> E.ProjR (cgen env e)
