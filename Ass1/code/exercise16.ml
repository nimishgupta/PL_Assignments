type exp =
  | Int of int
  | Add of exp * exp
  | Mul of exp * exp

let rec print (e : exp) : string =
  match e with
    | Int (x) -> string_of_int x
    | Add (e1, e2) -> "(" ^ print e1 ^ " + " ^ print e2 ^ ")"
    | Mul (e1, e2) -> "(" ^ print e1 ^ " * " ^ print e2 ^ ")"

;;

print_string (print (Add (Int 10, Int 5)) ^ "\n");
print_string (print (Mul (Add (Int 2, Int 3), Int 5)) ^ "\n");
print_string (print (Mul ((Mul (Int 3, Int 0)), Mul (Int 3, Int 5))) ^ "\n");


TEST = print (Add (Int 10, Int 5)) = "(10 + 5)"
TEST = print (Mul (Add (Int 2, Int 3), Int 5)) = "((2 + 3) * 5)"
TEST = print (Mul ((Mul (Int 3, Int 0)), Mul (Int 3, Int 5))) = "((3 * 0) * (3 * 5))"

