(* Implement a (binary) trie *)
Require Import Bool.
Set Implicit Arguments.

(* XXX: Should consider defining this as list of bools *)
Inductive bits: Set :=
  | Emptybits
  | Bit : bool -> bits -> bits.

Inductive trie (A: Set): Set :=
  | Leaf: trie A
  | Node: trie A -> (* bits -> *) option A -> trie A -> trie A.



Fixpoint search {A: Set} (in_trie: trie A) (key: bits) : option A :=
  match key, in_trie with
    | Emptybits, Node _ val _ => val
    | _, Leaf => None
    | Bit true  bits', Node _ _ rtrie => search rtrie bits' 
    | Bit false bits', Node ltrie _ _ => search ltrie bits'
  end.

Check search.

(* case "Replace"
   case "Add"
     case "Fill in missing nodes"
*)

Fixpoint insert {A: Set} (val: A) (in_trie: trie A) (key: bits) : trie A :=
  match key, in_trie with
    | Emptybits, Node ltrie _ rtrie => Node ltrie (Some val) rtrie
    | Emptybits, Leaf  => Node Leaf (Some val) Leaf
    | Bit true bits', Node ltrie v rtrie => Node ltrie v (insert _ val rtrie bits') 
    | Bit true bits', Leaf => Node Leaf None (insert _ val Leaf bits')
    | Bit false bits', Node ltrie v rtrie => Node (insert _ val ltrie bits') v rtrie
    | Bit false bits', Leaf => Node _ (insert val Leaf bits') None Leaf
  end.


  
  