type 'a trie =
  | Leaf
  | Node of 'a trie * bool list * 'a option * 'a trie

let rec prefix_match (key1: bool list) (key2: bool list) : bool list * bool list =
  match key1, key2 with
    | k :: key1', k' :: key2' when k =  k' -> prefix_match key1' key2'
    | _, _ -> (key1, key2)
  
let rec search (in_trie: 'a trie) (bits : bool list) : 'a option =
  match in_trie with
    | Leaf -> None
    | Node (ltrie, key, v, rtrie) -> (match prefix_match key bits with
        | [], []    -> v (* perfect match *)
        | [], true  :: bits' ->  search rtrie bits' (* exausted trie key *)
        | [], false :: bits' ->  search ltrie bits' (* exausted trie key *)
        | _, _ -> None (* Does not match any further *))


let rec insert (in_trie : 'a trie) (v : 'a) (bits : bool list): 'a trie =
  match in_trie with
    | Leaf -> Node (Leaf, bits, Some v, Leaf)
    | Node (ltrie, key, v', rtrie) -> (match prefix_match key bits with
        | [], [] -> Node (ltrie, key, Some v, rtrie) (*Found, replace val *)
        | [], true :: bits' -> Node (ltrie, key, v', (insert rtrie v bits'))
        | [], false :: bits' -> Node ((insert ltrie v bits'), key, v', rtrie)
        | _ :: key', true  :: bits' -> let ltrie' = Node (ltrie, key', v', rtrie) in Node (ltrie', [], None, Node (Leaf, bits', Some v, Leaf))
        | _ :: key', false :: bits' -> let rtrie' = Node (ltrie, key', v', rtrie) in Node (Node (Leaf, bits', Some v, Leaf), [], None, rtrie')
        | _ :: key', [] -> Node (ltrie, key, Some v, rtrie))
