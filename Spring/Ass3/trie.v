(* Implement a (binary) trie *)
Require Import Bool List CpdtTactics.
Set Implicit Arguments.

Section Tries.

Variable A: Set.

Definition bitstring: Set := list bool.

Inductive trie: Set :=
  | Leaf: trie
  | Node: trie -> bitstring ->  option A -> trie -> trie.


(* Redundant for now
Fixpoint prefix_match (key1 key2: bitstring): bitstring * bitstring :=
  match key1, key2 with
    | k :: key1', (k' :: key2') => 
        if eqb k k' then prefix_match key1' key2'
        else (key1, key2) 
    | _, _ => (key1, key2)
  end.
*)


Fixpoint search (sk: bitstring) (t : trie): option A :=
  match t with
    | Leaf => None
    | Node lhs nk v rhs =>
        match nk, sk with
          | nil, nil      => v
          | nil, b :: sk' => search sk' (if b then rhs else lhs)
          | _, nil        => None
          | l :: nk', m :: sk' => 
              if eqb l m then search sk' (Node lhs nk' v rhs) 
              else None 
        end
  end.


(*
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
*)


Fixpoint insert (ik: bitstring) (iv: A) (t : trie) : trie :=
  match t with
    | Leaf => Node Leaf ik (Some iv) Leaf
    | Node lhs nk onv rhs => match nk, ik with
        | nil, nil => Node lhs nil (Some iv) rhs (* Replace node value *)

        | nil, b :: ik' =>
            (* node key exausted, peek at head of remaining search string
               and accordingly insert to either left or right *)
            if b then Node lhs nil onv (insert ik' iv rhs)
            else Node (insert ik' iv lhs) nil onv rhs

        | l :: nk', nil => 
            (* search key exausted, need to split the original node *)
            if l then Node Leaf nil (Some iv) (Node lhs nk' onv rhs)
            else Node (Node lhs nk' onv rhs) nil (Some iv) Leaf

        | l :: nk', m :: ik' =>
            (* If both heads of node key and search key are same then
               continue matching, otherwise, split current node 
             *) 
            if eqb l m 
            then match insert ik' iv (Node lhs nk' onv rhs) with
                   | Leaf => Leaf
                   | Node lhs' nk'' onv' rhs' => Node lhs' (l :: nk'') onv' rhs'
                 end
            else if l
            then Node (insert ik' iv Leaf) nil None (Node lhs nk' onv rhs)
            else Node (Node lhs nk' onv rhs) nil None (insert ik' iv Leaf)
        end
   end.
                          

Lemma search_insert_top :
  forall (k: bitstring) (v: A) (lhs rhs: trie),
    search k (Node lhs k (Some v) rhs) = Some v.
Proof.
  intro.
  induction k.
  + intros.
    simpl.
    reflexivity.
  + intros.
    simpl.
    rewrite eqb_reflx.
    auto.
Qed.

Lemma insert_produces_node : 
  forall (k: bitstring) (v: A) (t: trie), exists (lhs rhs: trie) (k': bitstring) (v': A),
    insert k v t = Node lhs k' (Some v') rhs.
Proof.
  intros.
  destruct k.
  + unfold insert.
    destruct t.
Admitted.
 


(* TODO *)
Lemma search_rec :
  forall (b: bool) (k k': bitstring) (v: A) (w: option A) (t1 t2: trie),
    search (b :: k) (insert (b :: k) v (Node t1 (b :: k') w t2)) = 
    search k (insert k v (Node t1 k' w t2)).
Proof.
  intros.
  induction k.
  + unfold insert at 1.
    rewrite eqb_reflx.
    destruct k'.
    - rewrite search_insert_top.
      unfold insert.
      auto.
    - destruct b0.
      * rewrite search_insert_top.
        unfold insert.
        auto.
      * rewrite search_insert_top.
        unfold insert.
        rewrite search_insert_top.
        auto.
  + unfold insert at 1.
    rewrite eqb_reflx.
    fold insert.
    destruct k'.
    - destruct a.
      * unfold search at 1.
        rewrite eqb_reflx.
        fold search.
        simpl.
        reflexivity.
      * unfold search at 1.
        rewrite eqb_reflx.
        fold search.
        simpl.
        reflexivity.
    - 
Admitted.

(* TODO *)
Lemma correct_even :
  forall (b: bool) (k k': bitstring) (v: A) (w: option A) (t1 t2: trie),
    (forall (v: A) (t: trie), search k (insert k v t) = Some v) ->
      search (b :: k) (insert (b :: k) v (Node t1 (b :: k') w t2)) = Some v.
Proof.
  intros.
  induction k.
  + unfold insert.
    rewrite eqb_reflx.
    destruct k'.
    - rewrite search_insert_top.
      reflexivity.
    - destruct b0.
      * rewrite search_insert_top.
        reflexivity.
      * rewrite search_insert_top.
        reflexivity.
  + unfold insert.
    rewrite eqb_reflx.
    fold insert.
    destruct k'.
    - destruct a.
      * simpl.
        rewrite eqb_reflx.        
              
  
Admitted.

Lemma correct_odd:
  forall (b b': bool) (k k': bitstring) (v: A) (w: option A) (t1 t2: trie),
    (forall (v: A) (t: trie), search k (insert k v t) = Some v) -> b <> b'
      -> search (b :: k) (insert (b :: k) v (Node t1 (b' :: k') w t2)) = Some v.
Proof.
  intros.
  induction k.
  unfold insert.
  
Admitted.
    

Theorem insert_then_search:
  forall (k: bitstring) (v: A) (t: trie),
    search k (insert k v t) = Some v.
  Proof.
  intros.
  induction k.
  + destruct t.
    - unfold insert.
      rewrite search_insert_top.
      reflexivity.
    - unfold insert.
      induction b.
      * rewrite search_insert_top.
        reflexivity.
      * destruct a.
        Hint Rewrite search_insert_top.
        auto.
    auto.
  + destruct t.
    - unfold insert.
      rewrite search_insert_top.
      reflexivity.
    - destruct b.
      


End Tries.