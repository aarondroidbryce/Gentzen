Add LoadPath "theories/Casteran" as Ordering.
Add LoadPath "theories/Maths" as Maths_Facts.
Add LoadPath "theories/Logic" as Systems.

From Maths_Facts Require Import naturals.
From Maths_Facts Require Import lists.
From Systems Require Import definitions.
From Systems Require Import fol.

(* Defining substitution indicators. When we later define formula substitution,
we will want to take some formula A, and replace any instances of the
subformula E with the formula F. However, we will only want to do this at
certain places in A. Substitution indicators will control this.
For instance, if A is "B \/ (C \/ D)" we might be given a substitution
indicator S that looks like "0 (1 0)" which indicates that we want to
substitute C (if C is E) but leave B,D alone even if they are E. *)
(* *)
Inductive subst_ind : Type :=
| ind_0 : subst_ind
| ind_1 : subst_ind
| lor_ind : subst_ind -> subst_ind -> subst_ind.

Notation "(0)" := ind_0.
Notation "(1)" := ind_1.
Notation "( x y )" := (lor_ind x y).

Fixpoint non_target (A : formula) : subst_ind :=
match A with
| lor B C => lor_ind (non_target B) (non_target C)
| _ => (0)
end.

Fixpoint target (A : formula) : subst_ind :=
match A with
| lor B C => lor_ind (target B) (target C)
| _ => (1)
end.


(* Replace formula E with formula F at certain places in a formula A *)
(* *)
Fixpoint subst_ind_fit (A : formula) (S : subst_ind) : bool :=
match A, S with
| lor B C, lor_ind S_B S_C =>
    subst_ind_fit B S_B && subst_ind_fit C S_C
| _, lor_ind _ _ => false
| lor _ _, _ => false
| _, _ => true
end.

Fixpoint formula_sub_ind_fit (A D E : formula) (S : subst_ind) : formula :=
match A with
| lor B C =>
  (match S with
  | lor_ind S1 S2 => lor (formula_sub_ind_fit B D E S1)
                         (formula_sub_ind_fit C D E S2)
  | _ => A
  end)
| _ =>
  (match eq_f A D, S with
  | true, (1) => E
  | _, _ => A
  end)
end.

Definition formula_sub_ind (A D E : formula) (S : subst_ind) : formula :=
match subst_ind_fit A S with
| false => A
| true => formula_sub_ind_fit A D E S
end.

(* Some miscellaneous lemmas about formula substitution we will need *)
(* *)
Lemma sub_fit_true :
    forall (A D E : formula) (S : subst_ind),
        subst_ind_fit A S = true ->
            formula_sub_ind A D E S = formula_sub_ind_fit A D E S.
Proof.
intros A D E S FS.
unfold formula_sub_ind.
destruct A;
rewrite FS;
reflexivity.
Qed.

Lemma sub_fit_false :
    forall (A D E : formula) (S : subst_ind),
        subst_ind_fit A S = false ->
            formula_sub_ind A D E S = A.
Proof.
intros A D E S FS.
unfold formula_sub_ind.
destruct A;
rewrite FS;
reflexivity.
Qed.

Lemma formula_sub_ind_fit_0 :
    forall (A D E : formula),
        formula_sub_ind_fit A D E (0) = A.
Proof.
intros A D E.
destruct A;
unfold formula_sub_ind_fit.
4 : case (eq_f (univ n A) D).
2 : case (eq_f (neg A) D).
1 : case (eq_f (atom a) D).
all : reflexivity.
Qed.

Lemma formula_sub_ind_0 :
    forall (A D E : formula),
        formula_sub_ind A D E (0) = A.
Proof.
intros A D E.
case (subst_ind_fit A (0)) eqn:HA;
unfold formula_sub_ind;
rewrite HA.
- rewrite formula_sub_ind_fit_0.
  reflexivity.
- reflexivity.
Qed.

Lemma formula_sub_ind_lor :
    forall (A B D E : formula) (S_A S_B : subst_ind),
        subst_ind_fit A S_A && subst_ind_fit B S_B = true ->
            formula_sub_ind (lor A B) D E (lor_ind S_A S_B) = 
                lor (formula_sub_ind A D E S_A) (formula_sub_ind B D E S_B).
Proof.
intros A B D E S_A S_B FS.
unfold formula_sub_ind.
destruct (and_bool_prop _ _ FS) as [FSA FSB].
rewrite FSA,FSB.
unfold subst_ind_fit; fold subst_ind_fit.
rewrite FS.
unfold formula_sub_ind_fit; fold formula_sub_ind_fit.
reflexivity.
Qed.

(*
Lemma subst_ind_fit_lor :
    forall (A B : formula) (S_A S_B : subst_ind),
        subst_ind_fit (lor A B) (lor_ind S_A S_B) = true ->
            subst_ind_fit A S_A && subst_ind_fit B S_B = true.
Proof.
intros A B S_A S_B FAB.
apply FAB.
Qed.
*)

Lemma non_target_fit :
    forall (A : formula),
        subst_ind_fit A (non_target A) = true.
Proof.
intros A.
unfold subst_ind_fit, non_target.
induction A.
3 : rewrite IHA1, IHA2;
    unfold "&&".
all : reflexivity.
Qed.

Lemma non_target_sub' :
    forall (A D E : formula),
        formula_sub_ind_fit A D E (non_target A) = A.
Proof.
intros A D E.
induction A;
unfold non_target, formula_sub_ind_fit;
fold non_target formula_sub_ind_fit.
4 : case (eq_f (univ n A) D).
3 : rewrite IHA1, IHA2.
2 : case (eq_f (neg A) D).
1 : case (eq_f (atom a) D).
all : reflexivity.
Qed.

Lemma non_target_sub :
    forall (A C D : formula),
        formula_sub_ind A C D (non_target A) = A.
Proof.
intros A C D.
unfold formula_sub_ind.
rewrite non_target_fit.
apply non_target_sub'.
Qed.

Lemma non_target_sub_lor :
    forall (A B D E : formula) (S : subst_ind),
        formula_sub_ind (lor A B) D E (lor_ind (non_target A) S) =
            lor A (formula_sub_ind B D E S).
Proof.
intros A B D E S.
unfold formula_sub_ind, subst_ind_fit, formula_sub_ind_fit;
fold subst_ind_fit formula_sub_ind_fit.
rewrite non_target_fit, non_target_sub'.
unfold "&&".
case (subst_ind_fit B S) eqn:HB;
reflexivity.
Qed.

Lemma non_target_term_sub :
    forall (A : formula) (n : nat) (t : term),
        non_target A = non_target (substitution A n t).
Proof.
intros A n t.
induction A;
unfold non_target, substitution;
fold non_target substitution.
3 : rewrite IHA1,IHA2.
4 : case (eq_nat n0 n).
all : reflexivity.
Qed.

(*
Lemma target_fit :
    forall (A : formula),
        subst_ind_fit A (target A) = true.
Proof.
intros A.
induction A;
unfold subst_ind_fit, target;
fold subst_ind_fit target.
3 : rewrite IHA1,IHA2;
    unfold "&&".
all : reflexivity.
Qed.
*)

(*
Lemma target_term_sub : forall (A : formula) (n : nat) (t : term),
  target A = target (substitution A n t).
Proof.
intros. induction A; auto; simpl.
- rewrite IHA1, IHA2. auto.
- destruct (eq_nat n0 n); auto.
Qed.
*)

Lemma formula_sub_ind_closed :
    forall (A B C : formula),
        closed A = true ->
            (closed B = true -> closed C = true) ->
                forall (S : subst_ind),
                    closed (formula_sub_ind A B C S) = true.
Proof.
intros A B C.
induction A;
intros CA CBC S;
unfold formula_sub_ind.
4 : case (subst_ind_fit (univ n A) S).
3 : case (subst_ind_fit (lor A1 A2) S) eqn:FS.
2 : case (subst_ind_fit (neg A) S).
1 : case (subst_ind_fit (atom a) S).
all : try apply CA;
      unfold formula_sub_ind_fit;
      fold formula_sub_ind_fit;
      destruct S;
      try apply CA.
7 : { unfold formula_sub_ind, formula_sub_ind_fit, subst_ind_fit, closed in *;
      fold formula_sub_ind formula_sub_ind_fit subst_ind_fit closed in *.
      destruct (and_bool_prop _ _ CA) as [CA1 CA2].
      destruct (and_bool_prop _ _ FS) as [FS1 FS2].
      pose proof (IHA1 CA1 CBC S1) as CFA1.
      rewrite FS1 in CFA1.
      rewrite CFA1.
      pose proof (IHA2 CA2 CBC S2) as CFA2.
      rewrite FS2 in CFA2.
      rewrite CFA2.
      unfold "&&".
      reflexivity. }
7-9 : case (eq_f (univ n A) B) eqn:EQ.
4-6 : case (eq_f (neg A) B) eqn:EQ.
1-3 : case (eq_f (atom a) B) eqn:EQ.
all : try apply CA;
      apply f_eq_decid in EQ;
      destruct EQ;
      apply (CBC CA).
Qed.

Lemma formula_sub_ind_1 :
    forall (A B : formula),
        (subst_ind_fit A (1) = true) ->
            formula_sub_ind A A B (1) = B.
Proof.
intros A B FS.
destruct A;
unfold formula_sub_ind, subst_ind_fit, formula_sub_ind_fit.
3 : inversion FS.
all : rewrite eq_f_refl;
      reflexivity.
Qed.

Theorem lor_sub_right:
    forall C A E,
        (subst_ind_fit A (1) = true) ->
            formula_sub_ind (lor C A) A E (lor_ind (non_target C) (1)) = lor C E.
Proof.
intros C A E FS.
rewrite formula_sub_ind_lor.
- rewrite (formula_sub_ind_1 _ E FS).
  rewrite non_target_sub.
  reflexivity.
- rewrite non_target_fit.
  unfold "&&".
  apply FS.
Qed.

Theorem lor_sub_left:
    forall A D E,
        (subst_ind_fit A (1) = true) ->
            formula_sub_ind (lor A D) A E (lor_ind (1) (non_target D)) = lor E D.
Proof.
intros A D E FS.
rewrite formula_sub_ind_lor.
- rewrite (formula_sub_ind_1 _ E FS).
  rewrite non_target_sub.
  reflexivity.
- rewrite FS.
  unfold "&&".
  apply non_target_fit.
Qed.