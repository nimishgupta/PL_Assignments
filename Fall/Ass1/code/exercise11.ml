type intlst = 
  | Cons of int * intlst
  | Empty



let rec is_sorted (il : intlst) : bool =
  match il with
    | Empty -> true
    | Cons (hd, tl) -> if is_sorted tl then
                        match tl with 
                          | Empty -> true
                          | Cons (hd1, tl1) -> if hd <= hd1 then true
                                               else false
                       else false

;;

print_string ((string_of_bool (is_sorted Empty)) ^ "\n");
print_string ((string_of_bool (is_sorted (Cons (1, Empty)))) ^ "\n");
print_string ((string_of_bool (is_sorted (Cons (1, Cons (2, Empty))))) ^ "\n");
print_string ((string_of_bool (is_sorted (Cons (2, Cons (1, Empty))))) ^ "\n");
print_string ((string_of_bool (is_sorted (Cons (2, Cons (2, Empty))))) ^ "\n");


TEST = is_sorted Empty = true
TEST = is_sorted (Cons (1, Empty)) = true
TEST = is_sorted (Cons (1, Cons (2, Empty))) = true
TEST = is_sorted (Cons (2, Cons (1, Empty))) = false
TEST = is_sorted (Cons (2, Cons (2, Empty))) = true
