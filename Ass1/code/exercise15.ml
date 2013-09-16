type exp =
  | Int of int
  | Add of exp * exp
  | Mul of exp * exp

let rec eval (e : exp) : int =
  match e with
    | Int (x) -> x
    | Add (x, y) -> eval x + eval y
    | Mul (x, y) -> eval x * eval y


let ex1 = Add (Int 10, Int 5)
let ex2 = Mul (Add (Int 2, Int 3), Int 5)
let ex3 = Mul ((Mul (Int 3, Int 0)), Mul (Int 3, Int 5))

;;

print_string (string_of_int (eval ex1) ^ "\n");
print_string (string_of_int (eval ex2) ^ "\n");
print_string (string_of_int (eval ex3) ^ "\n");

TEST = eval ex1 = 15
TEST = eval ex2 = 25
TEST = eval ex3 = 0

