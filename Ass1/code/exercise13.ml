type intlst = 
  | Empty
  | Cons of int * intlst


let rec insert_sorted (n : int) (il : intlst) : intlst =
  match il with
    | Empty -> Cons (n, Empty)
    | Cons (hd, tl) -> if n < hd then Cons (n, il)
                       else Cons (hd, insert_sorted n tl)

let rec insertion_sort (il : intlst) : intlst =
  match il with
    | Empty -> Empty
    | Cons (hd, tl) -> insert_sorted hd (insertion_sort tl)

TEST = insertion_sort (Cons (1, Empty)) = Cons (1, Empty)
TEST = insertion_sort (Cons (2, Cons (1, Empty))) = Cons (1, Cons (2, Empty))
TEST = insertion_sort (Cons (2, Cons (1, Cons (2, Empty)))) = Cons (1, Cons (2, Cons (2, Empty)))
TEST = insertion_sort (Cons (1, Cons (2, Cons (3, Empty)))) = Cons (1, Cons (2, Cons (3, Empty)))
