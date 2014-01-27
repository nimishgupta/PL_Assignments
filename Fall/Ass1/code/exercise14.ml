type exp = 
  | Int of int
  | Add of exp * exp
  | Mul of exp * exp

let ex1 : exp = Add (Int 10, Int 5)
let ex2 : exp = Mul (Add (Int 2, Int 3), Int 5)
let ex3 : exp = Mul (Mul (Mul (Int 3, Int 0), Int 3), Int 5)
