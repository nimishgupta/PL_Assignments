open Typed_syntax

module TypeChecker = struct

exception Type_error of string

let type_check (e : exp) : typ = 
                           raise (Type_error "type checker not implemented")

end

module REPL = Typed_eval.Make (TypeChecker)
