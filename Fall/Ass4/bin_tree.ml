type tree =
  | Tree of int * tree * tree
  | Empty 


let rec insert (n : int) (t : tree) : tree = 
  match t with
    | Empty -> Tree (n, Empty, Empty)
    | Tree (root, left, right) -> if n <= root 
                                  then Tree (root, insert n left, right) 
                                  else Tree (root, left, insert n right)


let rec find (n : int) (t : tree) : tree = 
  match t with 
    | Empty -> Empty
    | Tree (root, left, right) -> if n = root then t
                                  else if n < root then find n left
                                  else find n right
                               
  
