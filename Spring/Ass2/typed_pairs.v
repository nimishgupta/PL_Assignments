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

Definition make_pair targ1 targ2 (l : targ1) (r : targ2): (targ1 * targ2) :=
  (l, r)%type.

(* Need to define recursive define for pairs *)
Definition eqp t1 t2 (p1 p2: t1 * t2) : bool :=
  let (a1, b1) := p1 in
  let (a2, b2) := p2 in
  (* (TEq _ a1 a2) andb (TEq _ b1 b2) *)
  false
%type.

(* Print eqp. *)

(* Check typeDenote (Pair _ _). *)

Definition tbinopDenote targ1 targ2 tres (b: tbinop targ1 targ2 tres)
  : typeDenote targ1 -> typeDenote targ2 -> typeDenote tres :=
  match b in tbinop targ1 targ2 tres 
    return typeDenote targ1 -> typeDenote targ2 -> typeDenote tres with
    (* Wrappers? *)
    | TPlus     => plus
    | TTimes    => mult
    | TEq Nat   => beq_nat
    | TEq Bool  => eqb
    | TLt       => leb
    | TEq ((* Should we have a forall clause *) Pair t1 t2)  => 
        eqp
    (* Check if make_pair has to be a dependent type *)
    | TMakePair _ _ => make_pair
  end.




(********************************************************************************************)


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

Eval simpl in typeDenote (Pair Bool (Pair Bool Nat)).




Definition projL targ tres (p : targ) : tres :=
  let (l, _) := p in l.

Definition projR targ tres (p : targ) : tres :=
  let (_, r) := p in r.

Definition tpairopDenote targ1 tres (op : tpairop targ1 tres)
 : typeDenote targ1 -> typeDenote tres :=
  match op with
    | ProjL => projL
    | ProjR => projR
  end.

Definition texpDenote t (e: texp t): typeDenote t :=
  match e with
    | TNConst n => n
    | TBConst b => b
    | TBinop _ _ _ op e1 e2 => (tbinopDenote op) (texpDenote e1) (texpDenote e2)
    | TPairop _ _ op e' => (tpairopDenote op) (texpDenote e')
  end.