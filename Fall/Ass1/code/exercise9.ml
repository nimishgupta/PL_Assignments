type intlist = 
  | Cons of int * intlist
  | Empty

let rec all_positive (il : intlist) : bool =
  match il with
    | Empty -> true
    | Cons (hd, tl) -> if hd >= 0 then all_positive tl
                       else false

;;

print_string ((string_of_bool (all_positive Empty)) ^ "\n");
print_string ((string_of_bool (all_positive (Cons (1, Empty)))) ^ "\n");
print_string ((string_of_bool (all_positive (Cons (-1, Empty)))) ^ "\n");
print_string ((string_of_bool (all_positive (Cons (1, Cons (-2, Empty))))) ^ "\n");
print_string ((string_of_bool (all_positive (Cons (-2, Cons (2, Empty))))) ^ "\n");


TEST = all_positive Empty = true
TEST = all_positive (Cons (1, Empty)) = true 
TEST = all_positive (Cons (-1, Empty)) = false
TEST = all_positive (Cons (1, Cons (-2, Empty))) = false
TEST = all_positive (Cons (-2, Cons (2, Empty))) = false
