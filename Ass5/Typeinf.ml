(* Step 1. Placeholder Type Identifiers *)


module I = Typeinf_syntax.Implicit
module E = Typeinf_syntax.Explicit
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





