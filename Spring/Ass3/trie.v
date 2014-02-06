(* Implement a (binary) trie *)
Require Import Bool.
Set Implicit Arguments.

Section Tries.

Variable A: Set.

(* XXX: Should consider defining this as list of bools *)
Inductive bits: Set :=
  | Emptybits
  | Bit : bool -> bits -> bits.

Inductive trie: Set :=
  | Leaf: trie
  | Node: A -> trie -> (* bits -> *) option A -> trie -> trie.



Fixpoint search (in_trie: trie) (key: bits) : option A :=
  match key, in_trie with
    | Emptybits, Node _ _ val _ => val
    | _, Leaf => None
    | Bit true  bits', Node _ _ _ rtrie => search rtrie bits' 
    | Bit false bits', Node _ ltrie _ _ => search ltrie bits'
  end.

Check search.

(* case "Replace"
   case "Add"
     case "Fill in missing nodes"
*)

Fixpoint insert (val: A) (in_trie: trie) (key: bits) : trie :=
  match key, in_trie  with
    | Emptybits, Node _ ltrie _ rtrie => Node _ ltrie (Some val) rtrie
    | Emptybits, Leaf  => Node _ Leaf (Some val) Leaf
    | Bit true bits', Node _ ltrie v rtrie => Node _ ltrie v (insert val rtrie bits') 
    | Bit true bits', Leaf => Node _ Leaf None (insert val Leaf bits')
    | Bit false bits', Node _ ltrie v rtrie => Node _ (insert val ltrie bits') v rtrie
    | Bit false bits', Leaf => Node _ (insert val Leaf bits') None Leaf
  end.


  
  