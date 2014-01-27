Require Import Bool List.
Set Implicit Arguments.

(* Boolean (binary) operators *)
Inductive binop: Set := And | Or.

(* Expressions in our language *)
Inductive exp: Set :=
  | Const : bool -> exp
  | Binop : binop -> exp -> exp -> exp.

(* Define binary operator over booleans *)
Definition binopDenote (b : binop) : bool -> bool -> bool :=
  match b with
    | And => andb
    | Or => orb
  end.

(* Define expression evaluation for booleans *)
Fixpoint expDenote (e : exp) : bool :=
  match e with
    | Const b => b
    | Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
  end.

(* Tests *)
Eval simpl in expDenote (Const true).
Eval simpl in expDenote (Binop Or (Const true) (Const false)).
Eval simpl in expDenote (Binop And (Binop Or (Const true) (Const true)) (Const false)).


(* Target language, we are compiling to a stack machine *)
Inductive instr: Set :=
  | iConst : bool -> instr
  | iBinop : binop -> instr.

Definition prog := list instr.
Definition stack := list bool.

(* Define execution of an (single) instruction
 * An instruction can be a constant or a binary operator
 * In case of a (boolean) constant we just push it on the stack
 * In case of binary operator, we pop 2 elements off stack and
 * apply the operator to those two elements
 *)
Definition instrDenote (i : instr) (s : stack) : option stack :=
  match i with
    | iConst b => Some (b :: s)
    | iBinop op => match s with
      | b1 :: b2 :: s' => Some ((binopDenote op) b1 b2 :: s')
      | _ => None
    end
  end.

(* Define execution of a whole program *)
Fixpoint progDenote (p : prog) (s : stack) : option stack :=
  match p with
    | nil => Some s
    | i :: p' => match instrDenote i s with
      | Some s' => progDenote p' s'
      | None => None
    end
  end.


(* Compiler Definition *)
Fixpoint compile (e : exp) : prog :=
  match e with
    | Const b => iConst b :: nil
    | Binop op e1 e2 => (compile e2) ++ (compile e1) ++ (iBinop op) :: nil
  end.

(* Test *)
Eval simpl in compile (Const true).
Eval simpl in compile (Binop And (Const true) (Const false)).
Eval simpl in compile (Binop And (Binop Or (Const true) (Const false)) (Const true)).
Eval simpl in progDenote (compile (Const false)) nil.
Eval simpl in progDenote (compile (Binop Or (Const false) (Const true))) nil.
Eval simpl in progDenote (compile (Binop And (Binop Or (Const true) (Const false)) (Const true))) nil.


(* We want to prove the theorem *)
Theorem compile_correct: forall e, progDenote (compile e) nil = Some (expDenote e :: nil).

(* we try by induction but we need a stronger induction argument for a stronger assumption *)
Abort.

(* Stronger induction argument *)
Lemma compile_correct': forall e p s, progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).
(* we prove it by induction on e *)
induction e.
(* some tactic *)
intros.
(* Subgoal 1 *)
(* Manipulation of lhs and rhs *)
unfold compile.
unfold expDenote.
unfold progDenote at 1.
(* Evaluation *)
simpl.
fold progDenote.
reflexivity. (* lhs = rhs *)


(* Subgoal 2 *)
intros.
unfold compile.
fold compile.
unfold expDenote.
fold expDenote.
(* Check app_assoc_reverse. *)
rewrite app_assoc_reverse.
rewrite IHe2.
rewrite app_assoc_reverse.
rewrite IHe1.
unfold progDenote at 1.
simpl.
fold progDenote.
reflexivity.
(* Save it for later use *)
Qed.


(* Back to our original theorem *)
Theorem compile_correct: forall e, progDenote (compile e) nil = Some (expDenote e :: nil).
intros.
(* Check app_nil_end *)
rewrite (app_nil_end (compile e)).
rewrite compile_correct'.
reflexivity.
Qed.
