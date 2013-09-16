type intlist = 
  | Cons of int * intlist
  | Empty

let rec all_even (il : intlist) : bool =
  match il with
    | Empty -> true
    | Cons (hd, tl) -> if hd mod 2 = 0 then all_even tl
                       else false

;;

print_string ((string_of_bool (all_even Empty)) ^ "\n");
print_string ((string_of_bool (all_even (Cons (1, Empty)))) ^ "\n");
print_string ((string_of_bool (all_even (Cons (2, Empty)))) ^ "\n");
print_string ((string_of_bool (all_even (Cons (1, Cons (2, Empty))))) ^ "\n");
print_string ((string_of_bool (all_even (Cons (2, Cons (4, Empty))))) ^ "\n");


TEST = all_even Empty = true
TEST = all_even (Cons (1, Empty)) = false 
TEST = all_even (Cons (2, Empty)) = true
TEST = all_even (Cons (1, Cons (2, Empty))) = false 
TEST = all_even (Cons (2, Cons (4, Empty))) = true
