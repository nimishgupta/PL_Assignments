(* Implement a (binary) trie *)
Require Import Bool List CpdtTactics.
Set Implicit Arguments.

Section Tries.

Variable A: Set.

Definition bitstring: Set := list bool.

Inductive trie: Set :=
  | Leaf: trie
  | Node: trie -> bitstring ->  option A -> trie -> trie.


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
                   | Node lhs' nk'' onv' rhs' => Node lhs' (l :: nk'') onv' rhs'
                   | Leaf => (Node lhs nk' onv rhs)
                 end
            else if l
            then Node (insert ik' iv Leaf) nil None (Node lhs nk' onv rhs)
            else Node (Node lhs nk' onv rhs) nil None (insert ik' iv Leaf)
        end
   end.

Hint Rewrite eqb_reflx.

Lemma search_insert_top :
  forall (k: bitstring) (v: A) (lhs rhs: trie),
    search k (Node lhs k (Some v) rhs) = Some v.
Proof.
  intro.
  induction k; try solve[crush].
Qed.

Hint Rewrite search_insert_top.

Lemma insert_produces_node : 
  forall (k: bitstring) (v: A) (t: trie), exists (lhs rhs: trie) (k': bitstring) (v': option A),
    insert k v t = Node lhs k' v' rhs.
Proof.
  intros.
  induction k.
  + simpl.
    destruct t.
    - eauto.
    - destruct b.
      * eauto.
      * destruct b. eauto. eauto.
  + simpl.
    destruct t.
    - eauto.
    - destruct b.
      * destruct a.
        exists t1. exists (insert k v t2). exists nil. exists o. auto.
        exists (insert k v t1). exists t2. exists nil. exists o. auto.
      * destruct (eqb b a).
          destruct (insert k v (Node t1 b0 o t2)). eauto. eauto.
          destruct b. eauto. eauto.
Qed.

Hint Rewrite insert_produces_node. 
 
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
    - crush.
    - destruct b0; crush.
  + unfold insert at 1.
    rewrite eqb_reflx.
    fold insert.
    destruct k'.
    - destruct a; crush.
    - simpl.
      remember (eqb b0 a).
      destruct b1.
      * (* Check insert_produces_node. *)
        destruct (insert_produces_node k v (Node t1 k' w t2)) as [lhs [rhs [k2 [v2 H]]]].
        Hint Rewrite eqb_reflx.
        crush.
      * simpl.
        destruct b0; try solve[crush].
Qed.

Hint Rewrite search_rec.

Lemma correct_even :
  forall (b: bool) (k k': bitstring) (v: A) (w: option A) (t1 t2: trie),
    (forall (v: A) (t: trie), search k (insert k v t) = Some v) ->
      search (b :: k) (insert (b :: k) v (Node t1 (b :: k') w t2)) = Some v.
Proof.
  intros.
  induction k'.
  + simpl. rewrite eqb_reflx.
    destruct (insert_produces_node k v (Node t1 nil w t2)) as [lhs [rhs [k2 [v2 H2]]]].
    crush.
  + simpl. rewrite eqb_reflx.
    destruct (insert_produces_node k v (Node t1 (a::k') w t2)) as [lhs [rhs [k2 [v2 H2]]]].
    crush.
Qed.

Hint Rewrite correct_even. 
    
Lemma correct_odd:
  forall (b b': bool) (k k': bitstring) (v: A) (w: option A) (t1 t2: trie),
    (forall (v: A) (t: trie), search k (insert k v t) = Some v) -> b' <> b
      -> search (b :: k) (insert (b :: k) v (Node t1 (b' :: k') w t2)) = Some v.
Proof.
  intros.
  assert (eqb b' b = false).
  rewrite eqb_false_iff.
  exact H0.
  induction k'.
  + simpl. rewrite H1.
    destruct b'.
    - destruct b. 
      * tauto.
      * crush.
    - destruct b. 
      * crush.
      * tauto.
  + simpl. rewrite H1.
    destruct b'.
    - destruct b.
      * tauto.
      * crush.
    - destruct b.
      * crush.
      * tauto.
Qed.

Hint Rewrite correct_odd.
    

Theorem insert_then_search:
  forall (k: bitstring) (v: A) (t: trie),
    search k (insert k v t) = Some v.
Proof.
  induction k.
  + simpl.
    destruct t.
    - trivial.
    - destruct b.
      * trivial.
      * destruct b; crush.
  + destruct t.
    - crush.
    - destruct b.
      * destruct a; crush.
      * remember (eqb b a).
        destruct b1.
        {
          assert (b = a). { rewrite <- eqb_true_iff. rewrite Heqb1. trivial. }
          rewrite H.
          rewrite correct_even.
          trivial.
          crush.
        }

        {
          assert (b <> a). { rewrite <- eqb_false_iff. rewrite Heqb1. trivial. }
          rewrite correct_odd.
          trivial.
          crush.
          crush.
        }
Qed.
   
End Tries.