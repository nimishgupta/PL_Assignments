Require Import Arith Bool List.
Set Implicit Arguments.

Inductive type : Set :=
  | Nat
  | Bool
  (* Accept two type from { Nat, Bool, Pair } and give a new type *)
  (* What is the new type *)
  | Pair: type -> type -> type.


Fixpoint typeDenote (t: type): Set :=
  match t with
    | Nat  => nat
    | Bool => bool
  (* XXX : need to check if this is correct *)
    (* | Pair t1 t2 => (typeDenote t1) * (typeDenote t2) *)
    (* ((typeDenote t1), (typeDenote t2)) <> ((typeDenote t1) * (typeDenote t2)) *)
    | Pair t1 t2 => (typeDenote t1) * (typeDenote t2)
  (* %type asks coq parser to parse "*" term as a type instead of product *)
  end%type.


Inductive tbinop: type -> type -> type -> Set :=
  | TPlus : tbinop Nat Nat Nat
  | TTimes : tbinop Nat Nat Nat
  | TEq : forall t, tbinop t t Bool
  | TLt: tbinop Nat Nat Bool
  | TMakePair: forall t1 t2, tbinop t1 t2 (Pair t1 t2).

Definition beq_pair {a b : Type} (eqA : a -> a -> bool) (eqB : b -> b -> bool) (x y: a*b) : bool
    := let (xa, xb) := x in let (ya, yb) := y in eqA xa ya && eqB xb yb.


(* TODO : Need to make this function go away *)
Fixpoint my_lt (m n: nat) : bool :=
  match m, n with
    | O, O => true
    | O, _ => false
    | _, O => false
    | S m', S n' => my_lt m' n'
  end.


Fixpoint type_comparator (t: type) : typeDenote t -> typeDenote t -> bool :=
  match t with
    | Nat => beq_nat
    | Bool => eqb
    | Pair t1 t2 => beq_pair (type_comparator t1) (type_comparator t2)
  end.

Definition tbinopDenote targ1 targ2 tres (b: tbinop targ1 targ2 tres)
  : typeDenote targ1 -> typeDenote targ2 -> typeDenote tres :=
  match b in tbinop targ1 targ2 tres 
    return typeDenote targ1 -> typeDenote targ2 -> typeDenote tres with
    | TPlus  => plus
    | TTimes => mult
    | TEq t => type_comparator t
    (* TODO : Need to make this function go away *)
    | TLt    => (* leb *) my_lt
    | TMakePair _ _ => pair
  end.


(* Pair operations *)
Inductive tpairop: type -> type -> Set :=
  | ProjL: forall t1 t2, tpairop (Pair t1 t2) t1
  | ProjR: forall t1 t2, tpairop (Pair t1 t2) t2.


(* typed expression in our language *)
Inductive texp : type -> Set :=
  | TNConst: nat -> texp Nat
  | TBConst: bool -> texp Bool
  | TBinop: forall t1 t2 t, tbinop t1 t2 t -> texp t1 -> texp t2 -> texp t
  | TPairop: forall t1 t2, tpairop t1 t2 -> texp t1 -> texp t2.


Definition projL {a b: Type} (p : a*b) : a :=
  let (l, _) := p in l.

Definition projR {a b: Type} (p : a*b) : b :=
  let (_, r) := p in r.

Definition tpairopDenote targ1 tres (op : tpairop targ1 tres)
 : typeDenote targ1 -> typeDenote tres :=
  match op with
    | ProjL _ _ => projL
    | ProjR _ _ => projR
  end.

Fixpoint texpDenote t (e: texp t): typeDenote t :=
  match e with
    | TNConst n => n
    | TBConst b => b
    | TBinop _ _ _ op e1 e2 => (tbinopDenote op) (texpDenote e1) (texpDenote e2)
    | TPairop _ _ op e' => (tpairopDenote op) (texpDenote e')
  end.

Eval simpl in texpDenote (TNConst 42).
Eval simpl in texpDenote (TBConst true).
Eval simpl in texpDenote (TBinop (TMakePair Nat Bool) (TNConst 42) (TBConst true)).
Eval simpl in texpDenote (TBinop TTimes (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)).
Eval simpl in texpDenote (TBinop TTimes 
                                   (TPairop (ProjL Nat Nat) 
                                     (TBinop (TMakePair Nat Nat) (TNConst 7) (TNConst 2)))
                                   (TPairop (ProjR Nat Nat) 
                                     (TBinop (TMakePair Nat Nat) (TNConst 7) (TNConst 2)))).
Eval simpl in texpDenote (TBinop (TEq Nat) (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)).
Eval simpl in texpDenote (TBinop (TEq Nat) (TNConst 8) (TBinop TTimes (TNConst 4) (TNConst 2))).
Eval simpl in texpDenote (TBinop (TEq (Pair (Pair Nat Bool) Bool))
                                    (TBinop (TMakePair (Pair Nat Bool) Bool) 
                                                  (TBinop (TMakePair Nat Bool) (TNConst 4) (TBConst true))
                                                  (TBConst false))
                                    (TBinop (TMakePair (Pair Nat Bool) Bool) 
                                                  (TBinop (TMakePair Nat Bool) (TNConst 3) (TBConst true))
                                                  (TBConst false))).

Eval simpl in texpDenote (TBinop (TEq (Pair (Pair Nat Bool) Bool))
                                    (TBinop (TMakePair (Pair Nat Bool) Bool) 
                                                  (TBinop (TMakePair Nat Bool) (TNConst 4) (TBConst true))
                                                  (TBConst false))
                                    (TBinop (TMakePair (Pair Nat Bool) Bool) 
                                                  (TBinop (TMakePair Nat Bool) (TNConst 4) (TBConst true))
                                                  (TBConst false))).
Eval simpl in texpDenote (TBinop TLt (TBinop TPlus (TNConst 2)(TNConst 2)) (TNConst 7)).


(* Compiler for stack machine *)

Definition tstack := list type.

(* instruction is types in the sense that it tells us the type of stack that it expects
   and type of stacks that it will produce
 *)
Inductive tinstr: tstack -> tstack -> Set :=
  | TiNConst : forall s, nat -> tinstr s (Nat :: s)
  | TiBConst : forall s, bool -> tinstr s (Bool :: s)
  | TiBinop : forall arg1 arg2 res s, 
                tbinop arg1 arg2 res -> tinstr (arg1 :: arg2 :: s) (res :: s).
  (* TODO : See if tiPairop would come *)

Inductive tprog: tstack -> tstack -> Set :=
  | TNil: forall s, tprog s s
  | TCons: forall s1 s2 s3, tinstr s1 s2 -> tprog s2 s3 -> tprog s1 s3.

Fixpoint vstack (ts: tstack): Set :=
  match ts with
    | nil => unit
    | t :: ts' => typeDenote t * vstack ts'
  end%type.


Definition tinstrDenote ts ts' (i: tinstr ts ts'): vstack ts -> vstack ts' :=
  match i with
    | TiNConst _ n => fun s => (n, s)
    | TiBConst _ b => fun s => (b, s)
    | TiBinop _ _ _ _ b => fun s =>
                             let '(arg1, (arg2, s')) := s in
                             ((tbinopDenote b) arg1 arg2, s')
    (* TODO : See if pairop would come *)
  end.


Fixpoint tprogDenote ts ts' (p : tprog ts ts') : vstack ts -> vstack ts' :=
  match p with
    | TNil _ => fun s => s
    | TCons _ _ _ i p' => fun s => tprogDenote p' (tinstrDenote i s)
end.


Fixpoint tconcat ts ts' ts'' (p: tprog ts ts'): tprog ts' ts'' -> tprog ts ts'' :=
  match p with
    | TNil _ => fun p' => p'
    | TCons _ _ _ i p1 => fun p' => TCons i (tconcat p1 p')
  end.

Fixpoint tcompile t (e: texp t) (ts: tstack): tprog ts (t::ts) :=
  match e with
    | TNConst n => TCons (TiNConst _ n) (TNil _)
    | TBConst b => TCons (TiBConst _ b) (TNil _)
    | TBinop _ _ _ b e1 e2 => tconcat (tcompile e2 _) 
                                      (tconcat (tcompile e1 _) (TCons (TiBinop _ b) (TNil _)))
    (* TODO : See if pairop would come *)
  end.