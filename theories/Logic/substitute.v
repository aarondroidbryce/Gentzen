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
| lor B E => lor_ind (non_target B) (non_target E)
| _ => (0)
end.

Fixpoint target (A : formula) : subst_ind :=
match A with
| lor B E => lor_ind (target B) (target E)
| _ => (1)
end.


(* Replace formula E with formula F at certain places in a formula A *)
(* *)
Fixpoint subst_ind_fit (A : formula) (S : subst_ind) : bool :=
match A, S with
| lor B E, lor_ind S_B S_C =>
    subst_ind_fit B S_B && subst_ind_fit E S_C
| _, lor_ind _ _ => false
| lor _ _, _ => false
| _, _ => true
end.

Fixpoint formula_sub_ind_fit (A E F : formula) (S : subst_ind) : formula :=
match A with
| lor B G =>
  (match S with
  | lor_ind S1 S2 => lor (formula_sub_ind_fit B E F S1)
                         (formula_sub_ind_fit G E F S2)
  | _ => A
  end)
| _ =>
  (match eq_f A E, S with
  | true, (1) => F
  | _, _ => A
  end)
end.

Fixpoint formula_sub_ind (A E F : formula) (S : subst_ind) : formula :=
match subst_ind_fit A S with
| false => A
| true => formula_sub_ind_fit A E F S
end.

(* Some miscellaneous lemmas about formula substitution we will need *)
(* *)
Lemma sub_fit_true : forall (A E F : formula) (S : subst_ind),
  subst_ind_fit A S = true ->
  formula_sub_ind A E F S = formula_sub_ind_fit A E F S.
Proof. intros. unfold formula_sub_ind. destruct A; rewrite H; auto. Qed.

Lemma sub_fit_false : forall (A E F : formula) (S : subst_ind),
  subst_ind_fit A S = false ->
  formula_sub_ind A E F S = A.
Proof. intros. unfold formula_sub_ind. destruct A; rewrite H; auto. Qed.

Lemma formula_sub_ind_fit_0 : forall (A B C : formula),
  formula_sub_ind_fit A B C (0) = A.
Proof.
intros.
destruct A.
- simpl. destruct B; auto. destruct (eq_atom a a0); auto.
- simpl. destruct B; auto. destruct (eq_f A B); auto.
- auto.
- simpl. destruct B; auto. destruct (eq_nat n n0 && eq_f A B); auto.
Qed.

Lemma formula_sub_ind_0 : forall (A B C : formula),
  formula_sub_ind A B C (0) = A.
Proof.
intros. case (subst_ind_fit A (0)) eqn:HA.
- unfold formula_sub_ind.
  destruct A; rewrite HA; rewrite formula_sub_ind_fit_0; auto.
- apply sub_fit_false. apply HA.
Qed.

Lemma formula_sub_ind_lor : forall (A B C D : formula) (S_A S_B : subst_ind),
  subst_ind_fit A S_A && subst_ind_fit B S_B = true ->
  formula_sub_ind (lor A B) C D (lor_ind S_A S_B) = 
  lor (formula_sub_ind A C D S_A) (formula_sub_ind B C D S_B).
Proof.
intros. simpl. rewrite H. unfold formula_sub_ind.
destruct (and_bool_prop _ _ H) as [HA HB].
destruct A; destruct B; rewrite HA, HB; auto.
Qed.

Lemma subst_ind_fit_lor : forall (B C : formula) (S_B S_C : subst_ind),
  subst_ind_fit (lor B C) (lor_ind S_B S_C) = true ->
  subst_ind_fit B S_B && subst_ind_fit C S_C = true.
Proof. intros. apply H. Qed.

Lemma non_target_fit : forall (A : formula),
  subst_ind_fit A (non_target A) = true.
Proof. intros. induction A; auto. simpl. rewrite IHA1, IHA2. auto. Qed.

Lemma non_target_sub' : forall (A C D : formula),
  formula_sub_ind_fit A C D (non_target A) = A.
Proof.
intros. induction A.
- unfold non_target. unfold formula_sub_ind_fit.
  destruct (eq_f (atom a) C); auto.
- unfold non_target. unfold formula_sub_ind_fit.
  destruct (eq_f (neg A) C); auto.
- simpl. rewrite IHA1, IHA2. auto.
- simpl. destruct C; auto. destruct (eq_nat n n0 && eq_f A C); auto.
Qed.

Lemma non_target_sub : forall (A C D : formula),
  formula_sub_ind A C D (non_target A) = A.
Proof.
intros. induction A.
- unfold non_target. apply formula_sub_ind_0.
- unfold non_target. apply formula_sub_ind_0.
- simpl. rewrite non_target_fit, non_target_fit. simpl.
  repeat rewrite non_target_sub'. auto.
- unfold non_target. apply formula_sub_ind_0.
Qed.

Lemma non_target_sub_lor : forall (A B C D : formula) (S : subst_ind),
  formula_sub_ind (lor A B) C D (lor_ind (non_target A) S) =
  lor A (formula_sub_ind B C D S).
Proof.
intros. simpl.
destruct (subst_ind_fit B S) eqn:HB; rewrite non_target_fit; simpl.
- rewrite non_target_sub', sub_fit_true. auto. apply HB.
- rewrite sub_fit_false. auto. apply HB.
Qed.

Lemma non_target_term_sub : forall (A : formula) (n : nat) (t : term),
  non_target A = non_target (substitution A n t).
Proof.
intros. induction A; auto; simpl.
- rewrite IHA1, IHA2. auto.
- destruct (eq_nat n0 n); auto.
Qed.

Lemma target_fit : forall f, subst_ind_fit f (target f) = true.
Proof.
intros f. induction f; simpl; auto. rewrite IHf1,IHf2. auto.
Qed.

Lemma target_term_sub : forall (A : formula) (n : nat) (t : term),
  target A = target (substitution A n t).
Proof.
intros. induction A; auto; simpl.
- rewrite IHA1, IHA2. auto.
- destruct (eq_nat n0 n); auto.
Qed.

Lemma formula_sub_ind_closed : forall (A B C : formula),
  closed A = true -> (closed B = true -> closed C = true) ->
  forall (S : subst_ind), closed (formula_sub_ind A B C S) = true.
Proof.
intros A B C. induction A; intros; unfold formula_sub_ind.
- destruct (subst_ind_fit (atom a) S); try apply H.
  simpl. destruct B; try apply H.
  destruct (eq_atom a a0) eqn:Ha; try apply H.
  destruct S; try apply H. apply H0.
  apply atom_beq_eq in Ha. rewrite <- Ha. auto.
- destruct (subst_ind_fit (neg A) S); try apply H.
  simpl. destruct B; try apply H.
  destruct (eq_f A B) eqn:HA; try apply H.
  destruct S; try apply H. apply H0.
  apply f_eq_decid in HA. rewrite <- HA. auto.
- destruct (subst_ind_fit (lor A1 A2) S) eqn:Hs; try apply H. simpl.
  destruct S; try apply H. simpl.
  inversion H. destruct (and_bool_prop _ _ H2).
  inversion Hs. destruct (and_bool_prop _ _ H5).
  clear H. clear Hs. clear H2. clear H5.
  rewrite <- (sub_fit_true _ _ _ _ H4).
  rewrite <- (sub_fit_true _ _ _ _ H6).
  rewrite (IHA1 H1 H0 S1). rewrite (IHA2 H3 H0 S2).
  rewrite H1, H3. auto.
- destruct (subst_ind_fit (univ n A) S); try apply H.
  simpl. destruct B; try apply H.
  destruct (eq_nat n n0) eqn:Hn; destruct (eq_f A B) eqn:HA; try apply H.
  destruct S; try apply H. apply H0.
  apply f_eq_decid in HA. rewrite <- HA.
  apply nat_eq_decid in Hn. rewrite <- Hn. auto.
Qed.

Lemma formula_sub_ind_1 : forall (A B : formula),
(subst_ind_fit A (1) = true) -> formula_sub_ind A A B (1) = B.
Proof.
intros.
destruct A.
- simpl. rewrite eq_atom_refl. auto.
- simpl. rewrite eq_f_refl. auto.
- inversion H.
- simpl. rewrite eq_f_refl. rewrite eq_nat_refl. auto.
Qed.

Theorem lor_sub_right: forall f g r , (subst_ind_fit r (1) = true) -> formula_sub_ind (lor f r) r g (lor_ind (non_target f) (1)) = lor f g.
Proof.
intros.
rewrite formula_sub_ind_lor.
- rewrite (formula_sub_ind_1 _ g H). rewrite non_target_sub. auto.
- rewrite non_target_fit. auto.
Qed.

Theorem lor_sub_left: forall f g r, (subst_ind_fit r (1) = true) -> formula_sub_ind (lor r f) r g (lor_ind (1) (non_target f)) = lor g f.
Proof.
intros.
rewrite formula_sub_ind_lor.
- rewrite (formula_sub_ind_1 _ g H). rewrite non_target_sub. auto.
- rewrite non_target_fit. rewrite H. auto.
Qed.