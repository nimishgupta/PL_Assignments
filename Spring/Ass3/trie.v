(* Implement a (binary) trie *)
Require Import Bool List.
Set Implicit Arguments.

Section Tries.

Variable A: Set.

Definition bitstring: Set := list bool.

Inductive trie: Set :=
  | Leaf: trie
  | Node: trie -> bitstring ->  option A -> trie -> trie.


Fixpoint prefix_match (key1 key2: bitstring): bitstring * bitstring :=
  match key1, key2 with
    | k :: key1', (k' :: key2') => 
        if eqb k k' then prefix_match key1' key2'
        else (key1, key2) 
    | _, _ => (key1, key2)
  end.

Fixpoint search (bits: bitstring) (in_trie: trie): option A :=
  match in_trie with
    | Leaf => None
    | Node ltrie k v rtrie => 
        let (left1, left2) := prefix_match k bits in 
        match left1, left2 with
          | nil, nil => v (* perfect match *)
          | nil, b :: bits' => search bits' (if b then rtrie else ltrie) (* exausted trie key *)
          | _, _ => None (* Does not match any further *)
       end
  end.

(*
let rec insert (bits : bool list) (v : 'a) (in_trie : 'a trie) : 'a trie =
  match in_trie with
    | Leaf -> Node (Leaf, bits, Some v, Leaf)
    | Node (ltrie, key, v', rtrie) -> (match prefix_match key bits with
        | [], [] -> Node (ltrie, key, Some v, rtrie) (*Found, replace val *)
        | [], true  :: bits' -> Node (ltrie, key, v', (insert bits' v rtrie))
        | [], false :: bits' -> Node ((insert bits' v ltrie), key, v', rtrie)
        | _ :: key', true  :: bits' ->
            let ltrie' = Node (ltrie, key', v', rtrie) in
            Node (ltrie', [], None, Node (Leaf, bits', Some v, Leaf))
        | _ :: key', false :: bits' ->
            let rtrie' = Node (ltrie, key', v', rtrie) in
            Node (Node (Leaf, bits', Some v, Leaf), [], None, rtrie')
        | _ :: key', [] -> Node (ltrie, key, Some v, rtrie))
*)

(* Definition empty_trie {A: Set}: trie A := Leaf. *)


Fixpoint insert (bits: bitstring) (v: A) (in_trie: trie): trie :=
  match in_trie with
    | Leaf => Node Leaf bits (Some v) Leaf
    | Node ltrie key v' rtrie => let (left1, left2) := prefix_match key bits in
        match left1, left2 with
          | nil, nil => Node ltrie key (Some v) rtrie (* Found, replace val *)
          | nil, true :: bits' => Node ltrie key v' (insert bits' v rtrie)
          | nil, false :: bits' => Node (insert bits' v ltrie) key v' rtrie
          | _ :: key', true :: bits' =>
              let ltrie' := Node ltrie key' v' rtrie in
              Node ltrie' nil None (Node Leaf bits' (Some v) Leaf)
          | _ :: key', false :: bits' =>
              let rtrie' := Node ltrie key' v' rtrie in
              Node (Node Leaf bits' (Some v) Leaf) nil None rtrie'
          | _ :: key', nil => Node ltrie key (Some v) rtrie
        end
  end.

End Tries.