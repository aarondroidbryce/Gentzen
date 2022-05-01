Add LoadPath "theories/Casteran" as Ordering.
Add LoadPath "theories/Maths" as Maths_Facts.
Add LoadPath "theories/Logic" as Systems.

Require Import Lia.
Require Import Nat.
Require Import Wellfounded.
From Ordering Require Import rpo.
From Maths_Facts Require Import naturals.
From Maths_Facts Require Import ordinals.
From Systems Require Import definitions.
From Systems Require Import fol.
From Systems Require Import PA_omega.
From Systems Require Import proof_trees.
From Systems Require Import substitute.
From Systems Require Import cut_elim.
From Systems Require Import Peano.
Notation "b1 && b2" := (andb b1 b2).
Notation "b1 || b2" := (orb b1 b2).
Notation eq_nat := Nat.eqb.



(*
###############################################################################
Section 13: The consistency of PA
###############################################################################
*)
Fixpoint disjunction_of (A E : formula) : bool :=
match A with
| lor B C0 =>
  (match eq_f B E, eq_f C0 E with
  | true, true => true
  | true, false => disjunction_of C0 E
  | false, true => disjunction_of B E
  | false, false => disjunction_of B E && disjunction_of C0 E
  end)
| _ => eq_f A E
end.

Definition danger : formula := atom (equ zero (succ zero)).

Definition dangerous_disjunct (A : formula) : bool := disjunction_of A danger.

Lemma danger_swap : forall (A B : formula), dangerous_disjunct (lor A B) = dangerous_disjunct (lor B A). intros. unfold dangerous_disjunct. unfold disjunction_of. fold disjunction_of. case (eq_f A danger) eqn:X; case (eq_f B danger) eqn:X1; auto; case (disjunction_of A danger) eqn:X2; case (disjunction_of B danger) eqn:X3; auto. Qed.

Lemma danger_split : forall (A B : formula), dangerous_disjunct (lor A B) = dangerous_disjunct A && dangerous_disjunct B.
Proof.
intros.
unfold dangerous_disjunct. unfold disjunction_of. fold disjunction_of. case (eq_f A danger) eqn:X.
- case (eq_f B danger) eqn:X1; destruct A; destruct B; unfold disjunction_of; fold disjunction_of; try rewrite X; try rewrite X1; auto; inversion X1; inversion X.
- case (eq_f B danger) eqn:X1; destruct B; unfold disjunction_of; fold disjunction_of; try rewrite X1; try rewrite X; auto; inversion X; inversion X1; try rewrite H1; case (disjunction_of A danger); auto.
Qed.

Lemma danger_closed : forall A, dangerous_disjunct A = true -> closed A = true.
Proof.
intros. unfold dangerous_disjunct in H. induction A.
- apply f_eq_decid in H. rewrite H. auto.
- inversion H.
- inversion H. rewrite H1. simpl. case (eq_f A1 danger) eqn:X; case (eq_f A2 danger) eqn:X1; rewrite IHA1,IHA2; auto; try apply f_eq_decid in X; try rewrite X; try apply f_eq_decid in X1; try rewrite X1; auto; apply and_bool_prop in H1; destruct H1; auto.
- inversion H.
Qed.

Lemma closed_danger : forall A, closed A = false -> dangerous_disjunct A = false.
Proof.
intros. case (dangerous_disjunct A) eqn:X; auto. rewrite danger_closed in H. inversion H. auto.
Qed.

Lemma danger_not_deg_0 : forall P A d alpha, P_proves P A d alpha -> dangerous_disjunct A = true -> 0 < d.
Proof.
intros P. induction P.
- intros. destruct X as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. destruct HP2 as [HP2a HP2b]. apply (IHP A _ alpha); auto. repeat split; auto. lia.
- intros. destruct X as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. destruct HP2 as [[HP2a HP2b] HP2c]. apply (IHP A _ (ptree_ord P)); auto. repeat split; auto.
- intros A. induction A.
  + intros. destruct X as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. rewrite HP1 in HP2. inversion HP2. unfold dangerous_disjunct in H. unfold disjunction_of in H. simpl in H. unfold eq_atom in H.
    destruct a; inversion H. apply and_bool_prop in H. destruct H. unfold eq_term in H. destruct t; inversion H. destruct t0; inversion H0.
    unfold correct_a in H1. unfold correctness in H1. simpl in H1. unfold eval in H1. fold eval in H1. case (eval t0) eqn:Y; inversion H1.
  + intros. unfold dangerous_disjunct in H. unfold disjunction_of in H. simpl in H. inversion H.
  + intros. destruct X as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. rewrite HP1 in HP2. inversion HP2.
  + intros. destruct X as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. rewrite HP1 in HP2. inversion HP2.
- intros. destruct X as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. destruct HP2 as [[[HP2a HP2b] HP2c] HP2d]. apply (IHP (ptree_formula P) _ (ptree_ord P)); auto. repeat split; auto. lia. rewrite HP2a. rewrite danger_swap. rewrite HP1. auto.
- intros. destruct X as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. destruct HP2 as [[[HP2a HP2b] HP2c] HP2d]. apply (IHP (ptree_formula P) _ (ptree_ord P)); auto. repeat split; auto. lia. rewrite <- HP1 in H. repeat rewrite danger_split in H. rewrite HP2a. rewrite danger_swap. repeat rewrite danger_split.
  apply and_bool_prop in H. destruct H as [H Y]. apply and_bool_prop in H. destruct H. rewrite H,H0,Y. auto.
- intros. destruct X as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. destruct HP2 as [[[HP2a HP2b] HP2c] HP2d]. apply (IHP (ptree_formula P) _ (ptree_ord P)); auto. repeat split; auto. lia. rewrite <- HP1 in H. repeat rewrite danger_split in H. rewrite HP2a. rewrite danger_swap. repeat rewrite danger_split.
  apply and_bool_prop in H. destruct H as [H Y]. apply and_bool_prop in H. destruct H. rewrite H,H0,Y. auto.
- intros. destruct X as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. destruct HP2 as [[[HP2a HP2b] HP2c] HP2d]. apply (IHP (ptree_formula P) _ (ptree_ord P)); auto. repeat split; auto. lia. rewrite <- HP1 in H. repeat rewrite danger_split in H. rewrite HP2a. rewrite danger_swap. repeat rewrite danger_split.
  apply and_bool_prop in H. destruct H. apply and_bool_prop in H. destruct H. apply and_bool_prop in H. destruct H. rewrite H,H0,H1,H2. auto.
- intros. destruct X as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. destruct HP2 as [[[HP2a HP2b] HP2c] HP2d]. apply (IHP (ptree_formula P) _ (ptree_ord P)); auto. repeat split; auto. lia. rewrite <- HP1 in H. repeat rewrite danger_split in H. rewrite HP2a. rewrite danger_split. rewrite H. auto.
- intros. destruct X as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. destruct HP2 as [[[HP2a HP2b] HP2c] HP2d]. apply (IHP (ptree_formula P) _ (ptree_ord P)); auto. repeat split; auto. lia. rewrite <- HP1 in H. repeat rewrite danger_split in H. rewrite HP2a. rewrite danger_split. rewrite danger_split. apply and_bool_prop in H. destruct H. rewrite H,H0. auto.
- intros. destruct X as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. destruct HP2 as [[[[HP2a HP2b] HP2c] HP2d] HP2e]. apply (IHP (ptree_formula P) _ (ptree_ord P)); auto. repeat split; auto. lia. rewrite <- HP1 in H. repeat rewrite danger_split in H. rewrite HP2a. apply and_bool_prop in H. destruct H. auto.
- intros. destruct X as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. rewrite <- HP1 in H. unfold dangerous_disjunct in H. unfold disjunction_of in H. inversion H.
- intros. destruct X as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. rewrite <- HP1 in H. rewrite danger_split in H. apply and_bool_prop in H. destruct H. unfold dangerous_disjunct in H. unfold disjunction_of in H. inversion H.
- intros. destruct X as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. rewrite <- HP1 in H. unfold dangerous_disjunct in H. unfold disjunction_of in H. inversion H.
- intros. destruct X as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. rewrite <- HP1 in H. rewrite danger_split in H. apply and_bool_prop in H. destruct H. unfold dangerous_disjunct in H. unfold disjunction_of in H. inversion H.
- intros. destruct X as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. rewrite <- HP1 in H. unfold dangerous_disjunct in H. unfold disjunction_of in H. inversion H.
- intros. destruct X as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. rewrite <- HP1 in H. rewrite danger_split in H. apply and_bool_prop in H. destruct H. unfold dangerous_disjunct in H. unfold disjunction_of in H. inversion H.
- intros. destruct X as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. rewrite <- HP1 in H0. unfold dangerous_disjunct in H0. unfold disjunction_of in H0. inversion H0.
- intros. destruct X as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. rewrite <- HP1 in H0. rewrite danger_split in H0. apply and_bool_prop in H0. destruct H0. unfold dangerous_disjunct in H0. unfold disjunction_of in H0. inversion H0.
- intros. destruct X as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. destruct HP2 as [[[[[[[HP2a HP2b] HP2c] HP2d] HP2e] HP2f] HP2g] HP2h]. lia.
- intros. destruct X as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. destruct HP2 as [[[[[[[HP2a HP2b] HP2c] HP2d] HP2e] HP2f] HP2g] HP2h]. lia.
- intros. destruct X as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. destruct HP2 as [[[[[[[HP2a HP2b] HP2c] HP2d] HP2e] HP2f] HP2g] HP2h]. lia.
Qed.

Lemma provable_not_danger : forall A d alpha, provable A d alpha -> dangerous_disjunct A = false.
Proof.
intros. case (dangerous_disjunct A) eqn:Y; auto.
- destruct (cut_elim_aux3 _ _ _ X) as [beta [P HP]]. pose (danger_not_deg_0 P A 0 beta HP Y). inversion l.
Qed.

Lemma danger_not_provable' : forall A P, dangerous_disjunct A = true -> valid P -> eq_f (ptree_formula P) A = false.
Proof.
intros. case (eq_f (ptree_formula P) A) eqn:Y; auto. intros. assert (provable (ptree_formula P) (ptree_deg P) (ptree_ord P)) as HP. exists P. repeat split; simpl; auto.
pose (provable_not_danger _ _ _ HP). apply f_eq_decid in Y. destruct Y. rewrite H in e. inversion e.
Qed.

Lemma danger_not_provable : forall A, dangerous_disjunct A = true -> forall P d alpha, P_proves P A d alpha -> False.
Proof.
intros. destruct X as [[[X1 X2] X3] X4]. pose proof (danger_not_provable' _ _ H X2). destruct X1. rewrite eq_f_refl in H0. inversion H0.
Qed.

Lemma danger_not_theorem : forall A, dangerous_disjunct A = true -> forall n alpha, PA_omega_theorem A n alpha -> False.
Proof.
intros. apply (danger_not_provable _ H _ _ _ (projT2(provable_theorem _ _ _ H0))). 
Qed.

Lemma inconsistent_danger : forall A n1 n2 alpha1 alpha2, PA_omega_theorem A n1 alpha1 -> PA_omega_theorem (neg A) n2 alpha2 -> False.
Proof.
intros. assert (closed danger = true). auto. assert (dangerous_disjunct danger = true). auto. apply (danger_not_theorem _ H2 _ _ (cut2 _ _ _ _ _ _ H (exchange1 _ _ _ _ (weakening (danger) _ _ _ H1 H0)))).
Qed.

Lemma PA_Consistent : forall A n1 n2 alpha1 alpha2, Peano_Theorems_Base A n1 alpha1 -> Peano_Theorems_Base (neg A) n2 alpha2 -> False.
Proof.
intros. pose proof (PA_Base_closed_PA_omega _ _ _  H (represent 0) (repr_closed _)). pose proof (PA_Base_closed_PA_omega _ _ _  H0 (represent 0) (repr_closed _)). rewrite closure_neg in H2; auto. apply (inconsistent_danger _ _ _ _ _ H1 H2). 
Qed.