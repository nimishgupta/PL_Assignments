type intlst = 
  | Empty
  | Cons of int * intlst


let rec insert_sorted (n : int) (il : intlst) : intlst =
  match il with
    | Empty -> Cons (n, Empty)
    | Cons (hd, tl) -> if n < hd then Cons (n, il)
                       else Cons (hd, insert_sorted n tl)

let il1 : intlst = Cons (2, Cons (5, Cons (8, Empty)))

;;


TEST = insert_sorted 60 Empty = Cons (60, Empty)
TEST = insert_sorted 1 il1    = Cons (1, il1)
TEST = insert_sorted 2 il1    = Cons (2, il1)
TEST = insert_sorted 6 il1    = Cons (2, Cons (5, Cons (6, Cons (8, Empty))))
TEST = insert_sorted 60 il1   = Cons (2, Cons (5, Cons (8, Cons (60, Empty))))
