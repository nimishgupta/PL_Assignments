Set Implicit Arguments.

Require Import CpdtTactics.
Require Import List Arith Bool.

Section Compare.

  Inductive compare (x y : nat) : Set :=
  | EQ : x = y -> compare x y
  | LT : y > x -> compare x y
  | GT : x > y -> compare x y.

  Lemma compare_impl : 
    forall x y, compare x y -> compare (S x) (S y).
    intros.
    destruct H.
    apply EQ. crush.
    apply LT. crush.
    apply GT. crush.
  Defined.

  Fixpoint cmp (x y : nat) : compare x y := 
    match x, y with
      | O, O => EQ (eq_refl O)
      | S x', O => GT (lt_O_Sn x')
      | O, S y' => LT (lt_O_Sn y')
      | S x', S y' => compare_impl (cmp x' y')
    end.

End Compare.

Module BinaryTree.

  Variable A : Set.

  Inductive tree :  Set :=
  | Leaf : tree
  | Node : tree -> nat -> A -> tree -> tree.

  Inductive mem (sk: nat): tree -> Prop :=
    | mem_root : forall lhs rhs v, mem sk (Node lhs sk v rhs)
    | mem_lhs  : forall lhs rhs nk v, mem sk lhs -> mem sk (Node lhs nk v rhs)
    | mem_rhs  : forall lhs rhs nk v, mem sk rhs -> mem sk (Node lhs nk v rhs).

  Lemma not_mem_leaf : forall k, ~ mem k Leaf.
  Proof.
    unfold not; intros k H.
    inversion H.
  Qed.

  Lemma mem_equal: forall k k' v, mem k (Node Leaf k' v Leaf) -> k = k'.
  Proof.
    intros k k' v H.
    inversion H.
    + trivial.
    + apply not_mem_leaf in H1. crush.
    + apply not_mem_leaf in H1. crush.
  Qed.

  
  (* All keys in t are greater than k *) 
  Inductive min (k: nat) (t: tree) : Prop :=
    min_intro: (forall k', mem k' t -> k < k') -> min k t.

  Lemma min_leaf: forall n, min n Leaf.
  Proof.
  intro n. apply min_intro. intros k' H. inversion_clear H.
  Qed.

  Lemma min_v_equal: forall n k lhs rhs v v', min n (Node lhs k v rhs) -> 
                                                    min n (Node lhs k v' rhs).
  Proof.
  intros.
  crush. apply H0. inversion H.
  + apply mem_root.
  + apply mem_lhs. apply H2.
  + apply mem_rhs. apply H2.
  Qed.

  Hint Resolve min_v_equal.
  

  Hint Resolve min_leaf.

  (* all keys in t are less that k *)
  Inductive maj (k: nat) (t: tree): Prop :=
    maj_intro: (forall k', mem k' t -> k' < k) -> maj k t.
  
  Lemma maj_leaf: forall n, maj n Leaf.
  Proof.
  intro n. apply maj_intro. intros k' H. inversion_clear H.
  Qed.

  Hint Resolve maj_leaf. 

  Lemma maj_v_equal: forall n k lhs rhs v v', maj n (Node lhs k v rhs) -> 
                                                  maj n (Node lhs k v' rhs).
  Proof.
  intros.
  crush.
  apply H0. inversion H.
  + apply mem_root.
  + apply mem_lhs. auto.
  + apply mem_rhs. auto.
  Qed.

  Hint Resolve maj_v_equal.



  Inductive bst: tree -> Prop :=
    | bst_leaf : bst Leaf
    | bst_node : forall k v lhs rhs, bst lhs -> bst rhs ->
                                  maj k lhs ->
                                  min k rhs -> bst (Node lhs k v rhs).

  Lemma bst_maj_split : forall lhs rhs k v n,
          bst (Node lhs k v rhs) -> maj n (Node lhs k v rhs) -> 
                  (n > k) /\ maj n lhs /\ maj n rhs.
  Proof.
  intros. inversion H.
  split.
  + inversion H0. crush. apply H9. apply mem_root.
  + split.
    - crush. apply H9. apply mem_root.
    - crush. apply H9. apply mem_rhs. auto.
  Defined.

  Lemma bst_min_split: forall lhs rhs k v n,
          bst (Node lhs k v rhs) -> min n (Node lhs k v rhs) ->
                 (n < k) /\ min n lhs /\ min n rhs.
  Proof.
  intros. inversion H.
  split.
  + inversion H0. crush. apply H9. apply mem_root.
  + split.
    - crush. apply H9. apply mem_lhs. auto.
    - crush. apply H9. apply mem_rhs. auto.
  Defined.

  Lemma maj_widen: forall lhs rhs k v n, 
                 n > k -> maj n lhs -> maj n rhs -> maj n (Node lhs k v rhs).
  Proof.
  intros.
  apply maj_intro. intros. inversion H2.
  + apply H.
  + inversion H0. apply H8. auto.
  + inversion H1. apply H8. auto.
  Defined.

  Lemma min_widen:forall lhs rhs k v n,
                 n < k -> min n lhs -> min n rhs -> min n (Node lhs k v rhs).
  Proof.
  intros.
  apply min_intro. intros. inversion H2.
  + apply H.
  + inversion H0. apply H8. auto.
  + inversion H1. apply H8. auto.
  Defined.
  
 
  Fixpoint ins (i: nat) (v: A) (t: tree) {struct t} : bst t -> { r : tree |
                 (bst r /\ (forall k, maj k t /\ i < k -> maj k r) /\
                           (forall k, min k t /\ i > k -> min k r)) }.
    refine (match t with
              | Leaf => fun bstH => exist _ (Node Leaf i v Leaf) _
              | Node lhs j v' rhs => fun bstH => match cmp i j with
                  | EQ _ =>  exist _ (Node lhs i v rhs) _
                  | LT _ =>  match ins i v lhs _ with
                      | exist lhs' h' => exist _ (Node lhs' j v' rhs) _
                    end  
                  | GT _ =>  match ins i v rhs _ with
                      | exist rhs' h' => exist _ (Node lhs j v' rhs') _
                    end
                end
            end).
    Proof.
    + split.
      * apply bst_node; auto.
      * split.
        - intros. apply maj_intro. intros. apply mem_equal in H0. rewrite H0. apply H.
        - intros. apply min_intro. intros. apply mem_equal in H0. rewrite H0. apply H.
    + split.
      * inversion bstH. apply bst_node; auto. rewrite e. auto. rewrite e. auto.
      * split.
        - intros. rewrite e. destruct H. eauto.
        - intros. rewrite e. destruct H. eauto.
    + inversion bstH. auto.
    + split.
      * inversion bstH. apply bst_node.
        - apply h'.
        - auto.
        - apply h'. auto.
        - auto.
      * split.
        - destruct h'. destruct H0. intros. destruct H2. apply bst_maj_split in H2. destruct H2. destruct H4. apply maj_widen. auto. apply H0. auto. auto. auto.
        - destruct h'. destruct H0. intros. destruct H2. apply bst_min_split in H2. destruct H2. destruct H4. apply min_widen. auto. apply H1. auto. auto. auto.
    + inversion bstH. auto.
    + split.
      * inversion bstH. apply bst_node.
        - auto.
        - apply h'.
        - auto.
        - apply h'. auto.
      * split.
        - destruct h'. destruct H0. intros. destruct H2. apply bst_maj_split in H2. destruct H2. destruct H4. apply maj_widen. auto. auto. apply H0. auto. auto.
        - destruct h'. destruct H0. intros. destruct H2. apply bst_min_split in H2. destruct H2. destruct H4. apply min_widen. auto. auto. apply H1. auto. auto.
    Defined.
    
  
  Definition insert (i: nat) (v: A) (t: tree): bst t -> {r : tree | bst r}.
    refine (match t with
              | Leaf => fun bstH => exist _ (Node Leaf i v Leaf) _
              | _ => fun bstH => match ins i v bstH with
                   | exist t' h' => exist _ t' _
                end
            end).
  Proof.
    + apply bst_node; auto. 
    + destruct h'. auto.
  Defined.

End BinaryTree.