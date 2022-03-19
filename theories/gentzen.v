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


Lemma cut_elim_aux1 : forall (alpha : ord) (P : ptree) (A : formula) (d : nat), P_proves P A (S d) alpha -> provable A d (ord_2_exp alpha).
Proof.
intros. inversion X. destruct X0 as [[H1 H2] H3]. pose (ptree_ord_nf _ H2). destruct H. admit.
Admitted.

Lemma cut_elim_aux2 : forall (A : formula) (d : nat),
  {alpha : ord & provable A d alpha} -> {beta : ord & provable A 0 beta}.
Proof.
intros. induction d.
- destruct X as [alpha H]. exists alpha. auto.
- apply IHd. destruct X as [alpha H]. exists (ord_2_exp alpha). destruct H as [P H]. apply (cut_elim_aux1 _ _ _ _ H).
Qed.

Lemma cut_elim_aux3 : forall (A : formula) (d : nat) (alpha : ord),
  provable A d alpha -> {beta : ord & provable A 0 beta}.
Proof. intros. apply (cut_elim_aux2 A d). exists alpha. auto. Qed.

Fixpoint cut_free (P : ptree) : Type :=
match P with
| deg_up d P' => cut_free P'

| ord_up alpha P' => cut_free P'

| node A => True


| exchange_ab A B d alpha P' => cut_free P'

| exchange_cab C0 A B d alpha P' => cut_free P'

| exchange_abd A B D d alpha P' => cut_free P'

| exchange_cabd C0 A B D d alpha P' => cut_free P'

| contraction_a A d alpha P' => cut_free P'

| contraction_ad A D d alpha P' => cut_free P'


| weakening_ad A D d alpha P' => cut_free P'

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2 => (cut_free P1) * (cut_free P2)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2 => (cut_free P1) * (cut_free P2)

| negation_a A d alpha P' => cut_free P'

| negation_ad A D d alpha P' => cut_free P'


| quantification_a A n t d alpha P' => cut_free P'

| quantification_ad A D n t d alpha P' => cut_free P'

| w_rule_a A n d alpha g => forall (m : nat), cut_free (g m)

| w_rule_ad A D n d alpha g => forall (m : nat), cut_free (g m)


| cut_ca C0 A d1 d2 alpha1 alpha2 P1 P2 => False

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 => False

| cut_cad C0 A D d1 d2 alpha1 alpha2 P1 P2 => False

end.


Lemma cut_elim_aux4 : forall (P : ptree),
  valid P -> ptree_deg P = 0 -> cut_free P.
Proof.
intros. induction P; simpl; auto.
- destruct X as [H1 H2]. simpl in H. rewrite H in H1. lia.
- destruct X as [[H1 H2] H3]. simpl in H. apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  simpl in H. rewrite H5 in H. rewrite H6 in H.
  destruct (max_0 _ _ H). split.
  + apply IHP1; auto.
  + apply IHP2; auto.
- destruct X as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  simpl in H. rewrite H5 in H. rewrite H6 in H.
  destruct (max_0 _ _ H). split.
  + apply IHP1; auto.
  + apply IHP2; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- rename f into A. rename p into g. rename n0 into d. rename o into alpha.
  intros. simpl in H. simpl in X. destruct (X m) as [[[H1 H2] H3] H4].
  rewrite H in H3. apply X0; auto. lia.
- rename f into A. rename f0 into D. rename p into g.
  rename n0 into d. rename o into alpha.
  intros. simpl in H. simpl in X. destruct (X m) as [[[H1 H2] H3] H4].
  rewrite H in H3. apply X0; auto. lia.
- simpl in H. apply max_succ_0 in H. auto.
- simpl in H. apply max_succ_0 in H. auto.
- simpl in H. apply max_succ_0 in H. auto.
Qed.

Definition P_proves' (P : ptree) (A : formula) : Type :=
  (ptree_formula P = A) * (valid P) *
  {d : nat & ptree_deg P = d & {alpha : ord & ptree_ord P = alpha}}.

Lemma cut_elim_aux5 : forall (A : formula) (d : nat) (alpha : ord),
  provable A d alpha -> {P : ptree & P_proves' P A & cut_free P}.
Proof.
intros. apply cut_elim_aux3 in X. destruct X as [gamma [P [[[H1 H2] H3] H4]]].
exists P.
- unfold P_proves'. repeat split; auto.
  exists 0; auto. lia. exists gamma; auto.
- apply cut_elim_aux4; auto. lia.
Qed.

Lemma provable_not_danger : forall A d alpha, provable A d alpha -> dangerous_disjunct A = false.
Proof.
intros. case (dangerous_disjunct A) eqn:Y; auto.
- destruct (cut_elim_aux3 _ _ _ X) as [beta [P HP]]. pose (danger_not_deg_0 P A 0 beta HP Y). inversion l.
Qed.

Lemma danger_not_provable : forall A P, dangerous_disjunct A = true -> valid P -> eq_f (ptree_formula P) A = false.
Proof.
intros. case (eq_f (ptree_formula P) A) eqn:Y; auto. intros. assert (provable (ptree_formula P) (ptree_deg P) (ptree_ord P)) as HP. exists P. repeat split; simpl; auto.
pose (provable_not_danger _ _ _ HP). apply f_eq_decid in Y. destruct Y. rewrite H in e. inversion e.
Qed.

Lemma danger_not_theorem : forall A n alpha, PA_omega_theorem A n alpha -> dangerous_disjunct A = false.
Proof.
intros. apply (provable_not_danger _ _ _ (provable_theorem _ _ _ H)). 
Qed.