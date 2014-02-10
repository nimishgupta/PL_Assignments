(* Implement a (binary) trie *)

type bitstring = bool list


type 'a trie =
  | Leaf
  | Node of 'a trie * bitstring * 'a option * 'a trie


let rec search (sk: bitstring) (t : 'a trie): 'a option =
  match t with
    | Leaf -> None
    | Node (lhs, nk, v, rhs) -> match nk, sk with
        | [], [] -> v
        | [], b :: sk' -> search sk' (if b then rhs else lhs)
        | _, []      -> None
        | l :: nk', m :: sk' -> 
            if l = m then search sk' (Node (lhs, nk', v, rhs)) else None 


let rec insert (ik: bitstring) (iv: 'a) (t : 'a trie) : 'a trie =
  match t with
    | Leaf -> Node (Leaf, ik, (Some iv), Leaf)
    | Node (lhs, nk, onv, rhs) -> match nk, ik with
        | [], [] -> Node (lhs, [], (Some iv), rhs) (* Replace node value *)

        | [], b :: ik' ->
            (* node key exausted, peek at head of remaining search string
               and accordingly insert to either left or right *)
            if b then Node (lhs, [], onv, (insert ik' iv rhs))
            else Node ((insert ik' iv lhs), [], onv, rhs)

        | l :: nk', [] -> 
            (* search key exausted, need to split the original node *)
            if l then Node (Leaf, [], (Some iv), (Node (lhs, nk', onv, rhs)))
            else Node (Node (lhs, nk', onv, rhs), [], (Some iv), Leaf)

      | l :: nk', m :: ik' ->
            (* If both heads of node key and search key are same then
               continue matching, otherwise, split current node 
            *) 
            if l = m 
            then let Node (lhs', nk'', onv', rhs') = insert ik' iv (Node (lhs, nk', onv, rhs)) in
                 (Node (lhs', (l :: nk''), onv', rhs'))
            else if l
                 then Node ((insert ik' iv Leaf), [], None, (Node (lhs, nk', onv, rhs)))
                 else Node (Node (lhs, nk', onv, rhs), [], None, (insert ik' iv Leaf))


(* TESTS *)

let empty_trie: string trie = Leaf

TEST "Empty tree search" = search [true; false; true] empty_trie  = None 
TEST "Insert and search found" = search [true; false; true] (insert [true; false; true] "abc" empty_trie) = Some "abc"
TEST "Replace and search found new" = search [true; false; true] 
                                             (insert [true; false; true] "def" 
                                                (insert [true; false; true] "abc" empty_trie)) = Some "def"
TEST "Search incorrect path, not found" = search [true; true; true] (insert [true; false; true] "abc" empty_trie) = None
TEST "Search partial path, not found1 underspecified bit string" = search [true; false] (insert [true; false; true] "abc" empty_trie) = None
TEST "Search partial path, not found2 overspecified bit string"  = search [true; false; true; true] (insert [true; false; true] "abc" empty_trie) = None

TEST "Insert and search not found" = search [false; false; true] (insert [true; false; true] "abc" empty_trie) = None
TEST "Insert multiple and search found first" = search [true; false; true] 
                                                       (insert [true; false; true; false; true] "def"
                                                          (insert [true; false; true] "abc" empty_trie)) = Some "abc"
