(* Implement a (binary) trie *)
Require Import Bool List CpdtTactics.
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

(*
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
*)
Fixpoint search (k: bitstring) (t : trie): option A :=
  match t with
    | Leaf => None
    | Node lhs k' v rhs =>
        match k', k with
          | nil, nil      => v
          | nil, b :: k'' => search k'' (if b then rhs else lhs)
          | _, nil        => None
          | l :: kl, m :: k'l => 
              if eqb l m then search k'l (Node lhs kl v rhs) 
              else None 
        end
  end.


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

(* TODO *)
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

(* TODO *)
Lemma search_rec :
  forall (b: bool) (k k': bitstring) (v: A) (w: option A) (t1 t2: trie),
    search (b :: k) (insert (b :: k) v (Node t1 (b :: k') w t2)) = 
    search k (insert k v (Node t1 k' w t2)).
Proof.
  intros.
Admitted.

(* TODO *)
Lemma correct_even :
  forall (b: bool) (k k': bitstring) (v: A) (w: option A) (t1 t2: trie),
    (forall (v: A) (t: trie), search k (insert k v t) = Some v) ->
      search (b :: k) (insert (b :: k) v (Node t1 (b :: k') w t2)) = Some v.
Admitted.

Lemma correct_odd:
  forall (b b': bool) (k k': bitstring) (v: A) (w: option A) (t1 t2: trie),
    (forall (v: A) (t: trie), search k (insert k v t) = Some v) -> b <> b'
      -> search (b :: k) (insert (b :: k) v (Node t1 (b' :: k') w t2)) = Some v.
Admitted.
    

Theorem insert_then_search:
  forall (A: Set) (k: bitstring) (v: A) (t: trie A),
    search k (insert k v t) = Some v.
  Proof.
  intros.
  induction t.
  


    destruct b.
    destruct b0.
    reflexivity.
    destruct b.
    simpl.
    reflexivity.
    induction k.
    + 

End Tries.