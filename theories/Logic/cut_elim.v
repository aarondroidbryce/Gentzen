Add LoadPath "theories/Casteran" as Ordering.
Add LoadPath "theories/Maths" as Maths_Facts.
Add LoadPath "theories/Logic" as Systems.

Require Import Lia.
Require Import Nat.
From Maths_Facts Require Import naturals.
From Maths_Facts Require Import ordinals.
From Systems Require Import definitions.
From Systems Require Import fol.
From Systems Require Import PA_omega.
From Systems Require Import proof_trees.
From Systems Require Import substitute.

From Systems Require Import formula_sub.
From Systems Require Import inverse_neg.
From Systems Require Import inverse_dem_1.
From Systems Require Import inverse_dem_2.
From Systems Require Import inverse_omega.
From Systems Require Import neg_inverse_omega.


Notation "b1 && b2" := (andb b1 b2).
Notation "b1 || b2" := (orb b1 b2).
Notation eq_nat := Nat.eqb.


Fixpoint cut_elimination_0 (P : ptree) : ptree :=
match P with
| ord_up alpha P' => P'
| deg_up d P' => P'
| _ => P
end.


(* Defining cut_elimination_atom, the case where the cut formula is atom a *)
(* *)
Fixpoint cut_elimination_atom (P : ptree) : ptree :=
match P with
| cut_ca C (atom a) d1 d2 alpha1 alpha2 P1 P2 =>
  (match PA_omega_axiom (atom a) with
  | true =>
      formula_sub_ptree P2 (neg (atom a)) C (1)
  | false =>
      contraction_a
        C d1 alpha1
        (formula_sub_ptree P1 (atom a) C (lor_ind (non_target C) (1)))
  end)

| cut_ad (atom a) D d1 d2 alpha1 alpha2 P1 P2 =>
  (match PA_omega_axiom (atom a) with
  | true =>
      contraction_a
        D d2 alpha2
        (formula_sub_ptree P2 (neg (atom a)) D (lor_ind (1) (non_target D)))
  | false =>
      formula_sub_ptree P1 (atom a) D (1)
  end)

| cut_cad C (atom a) D d1 d2 alpha1 alpha2 P1 P2 =>
  (match PA_omega_axiom (atom a) with
  | true =>
      weakening_ad C D d2 alpha2
        (contraction_a
          D d2 alpha2
          (formula_sub_ptree P2 (neg (atom a)) D (lor_ind (1) (non_target D))))
  | false =>
      exchange_ab
        D C d1 (ord_succ alpha1)
        (weakening_ad
          D C d1 alpha1
          (contraction_a
            C d1 alpha1
            (formula_sub_ptree P1 (atom a) C (lor_ind (non_target C) (1)))))
  end)
| deg_up d P' => cut_elimination_atom P'
| ord_up alpha P' => cut_elimination_atom P'
| _ => P
end.


(* Defining cut_elimination_neg, the case where the cut formula is ~E *)
(* *)
Fixpoint cut_elimination_neg (P : ptree) : ptree :=
match P with
| cut_ca C (neg E) d1 d2 alpha1 alpha2 P1 P2 =>
    cut_ad
      E C d2 d1 alpha2 alpha1
      (dub_neg_sub_ptree P2 E (1))
      (exchange_ab C (neg E) d1 alpha1 P1)

| cut_ad (neg E) D d1 d2 alpha1 alpha2 P1 P2 =>
    cut_ca
      D E d2 d1 alpha2 alpha1
      (exchange_ab
        E D d2 alpha2
        (dub_neg_sub_ptree P2 E (lor_ind (1) (non_target D))))
      P1

| cut_cad C (neg E) D d1 d2 alpha1 alpha2 P1 P2 =>
    exchange_ab
      D C (ptree_deg (cut_cad
      D E C d2 d1 alpha2 alpha1
      (exchange_ab
      E D d2 alpha2
        (dub_neg_sub_ptree P2 E (lor_ind (1) (non_target D))))
          (exchange_ab C (neg E) d1 alpha1 P1))) (ptree_ord P)
        (cut_cad
          D E C d2 d1 alpha2 alpha1
          (exchange_ab
          E D d2 alpha2
            (dub_neg_sub_ptree P2 E (lor_ind (1) (non_target D))))
              (exchange_ab C (neg E) d1 alpha1 P1))
| deg_up d P' => cut_elimination_neg P'
| ord_up alpha P' => cut_elimination_neg P'
| _ => P
end.


(* Defining cut_elimination_lor, the case where the cut formula is E \/ F *)
(* *)
Definition associativity_1' (P : ptree) : ptree :=
match ptree_formula P, ptree_deg P, ptree_ord P with
| lor (lor C A) B, d, alpha =>
    exchange_ab
      (lor A B) C d alpha
      (exchange_cab
        A C B d alpha
        (exchange_abd C A B d alpha P))

| _, _, _ => P
end.

Definition associativity_2' (P : ptree) : ptree :=
match ptree_formula P, ptree_deg P, ptree_ord P with
| lor C (lor A B), d, alpha =>
    exchange_abd
      A C B d alpha
      (exchange_cab
        A B C d alpha
        (exchange_ab C (lor A B) d alpha P))

| _, _, _ => P
end.

Lemma associativity1_valid : forall (P : ptree),
  valid P -> valid (associativity_1' P).
Proof.
intros. unfold associativity_1'. destruct (ptree_formula P) eqn:HP; auto.
destruct f1; auto. repeat split; auto.
Qed.

Lemma associativity2_valid : forall (P : ptree),
  valid P -> valid (associativity_2' P).
Proof.
intros. unfold associativity_2'. destruct (ptree_formula P) eqn:HP; auto.
destruct f2; auto. repeat split; auto.
Qed.

Definition contraction_help (P : ptree) : ptree :=
match ptree_formula P, ptree_deg P, ptree_ord P with
| lor (lor C D) E, d, alpha =>
    (match eq_f D E with
    | true =>
        exchange_ab
          D C d alpha
          (contraction_ad
            D C d alpha
            (exchange_cab
              D C D d alpha
              (exchange_abd C D D d alpha P)))

    | false => P
    end)

| _, _, _ => P
end.

Fixpoint cut_elimination_lor (P : ptree) : ptree :=
match P with
| cut_ca C (lor E F) d1 d2 alpha1 alpha2 P1 P2 =>
    cut_ca
      C E
      (max (max d1 d2) (S (num_conn F)))
      d2
      (ord_succ (ord_max alpha1 alpha2))
      alpha2
      (cut_ca (lor C E) F d1 d2 alpha1 alpha2
        (associativity_2' P1)
        (demorgan2_sub_ptree P2 E F (1)))
      (demorgan1_sub_ptree P2 E F (1))

| cut_ad (lor E F) D d1 d2 alpha1 alpha2 P1 P2 =>
    contraction_a
      D
      (max (max d1 d2) (max (S (num_conn E)) (S (num_conn F))))
      (ord_succ (ord_succ (ord_max alpha1 alpha2)))
      (cut_cad
        D E D
        (max (max d1 d2) (S (num_conn F)))
        d2
        (ord_succ (ord_max alpha1 alpha2))
        alpha2
        (exchange_ab
          E D
          (max (max d1 d2) (S (num_conn F)))
          (ord_succ (ord_max alpha1 alpha2))
          (cut_cad
            E F D d1 d2 alpha1 alpha2 P1
            (demorgan2_sub_ptree P2 E F (lor_ind (1) (non_target D)))))
        (demorgan1_sub_ptree P2 E F (lor_ind (1) (non_target D))))

| cut_cad C (lor E F) D d1 d2 alpha1 alpha2 P1 P2 =>
    contraction_help
      (cut_cad
        (lor C D) E D
        (max (max d1 d2) (S (num_conn F)))
        d2
        (ord_succ (ord_max alpha1 alpha2))
        alpha2
        (exchange_cab
          C E D
          (max (max d1 d2) (S (num_conn F)))
          (ord_succ (ord_max alpha1 alpha2))
          (cut_cad (lor C E) F D d1 d2 alpha1 alpha2
            (associativity_2' P1)
            (demorgan2_sub_ptree P2 E F (lor_ind (1) (non_target D)))))
        (demorgan1_sub_ptree P2 E F (lor_ind (1) (non_target D))))

| deg_up d P' => cut_elimination_lor P'
| ord_up alpha P' => cut_elimination_lor P'
| _ => P
end.

(* Define cut_elimination, an operation on ptrees *)
(* *)
Fixpoint cut_elimination (P : ptree) : ptree :=
match ptree_ord P with
| Zero => cut_elimination_0 P
| cons a n b =>
  (match P with
  | cut_ca C A d1 d2 alpha1 alpha2 P1 P2 =>
    (match A with
    | atom a => cut_elimination_atom P
    | neg E => cut_elimination_neg P
    | lor E F => cut_elimination_lor P
    | univ n E => P
    end)
  | cut_ad A D d1 d2 alpha1 alpha2 P1 P2 =>
    (match A with
    | atom a => cut_elimination_atom P
    | neg E => cut_elimination_neg P
    | lor E F => cut_elimination_lor P
    | univ n E => P
    end)
  | cut_cad C A D d1 d2 alpha1 alpha2 P1 P2 =>
    (match A with
    | atom a => cut_elimination_atom P
    | neg E => cut_elimination_neg P
    | lor E F => cut_elimination_lor P
    | univ n E => P
    end)
  | deg_up d P' => cut_elimination P'
  | ord_up alpha P' => cut_elimination P'
  | _ => P
  end)
end.


(*
###############################################################################
Section 12:
Here we prove that if P is a valid ptree with ordinal alpha and degree d+1,
then cut_elimination(P) is a valid ptree with ordinal 2^alpha and degree d
###############################################################################
*)
(* *)

Theorem cut_elimination_formula : forall (P : ptree),
  valid P -> ptree_formula (cut_elimination P) = ptree_formula P.
Proof.
intros. induction P.
- simpl. destruct (ptree_ord P); simpl; auto. apply IHP. destruct X as [X1 X2]. apply X2.
- simpl. destruct o; simpl; auto. apply IHP. destruct X as [[X1 X2] X3]. apply X2.
- simpl. auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct (ord_succ o); simpl; auto.
- simpl. destruct (ord_succ (ord_max o o0)); simpl; auto.
- simpl. destruct (ord_succ (ord_max o o0)); simpl; auto.
- simpl. destruct (ord_succ o); simpl; auto.
- simpl. destruct (ord_succ o); simpl; auto.
- simpl. destruct (ord_succ o); simpl; auto.
- simpl. destruct (ord_succ o); simpl; auto.
- simpl. destruct (ord_succ o); simpl; auto.
- simpl. destruct (ord_succ o); simpl; auto.
- simpl. destruct (ord_succ (ord_max o o0)); simpl; auto.
  destruct f0.
  + destruct (correct_a a).
   * destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. pose proof (formula_sub_ptree_formula_neg P2 a f X4 (1)). rewrite H. rewrite X3. apply formula_sub_ind_1. auto.
   * auto.
  + case (eq_nat (max (max n0 n) (S (num_conn (f0)))) (S (num_conn f0))); auto. 
  + unfold ptree_formula. auto.
  + auto.
- simpl. destruct (ord_succ (ord_succ (ord_max o o0))); simpl; auto.
  destruct f.
  + destruct (correct_a a).
   * auto.
   * destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. pose proof (formula_sub_ptree_formula_atom P1 a f0 X2 (1)). rewrite H. rewrite X1. apply formula_sub_ind_1. auto. 
  + case (eq_nat (max (max n0 n) (S (num_conn (f0)))) (S (num_conn f0))); auto. 
  + unfold ptree_formula. auto.
  + auto.

- simpl. destruct (ord_succ (ord_max o o0)); simpl; auto.
  destruct f0.
  + destruct (correct_a a).
   * auto.
   * auto.
  + auto.
  + unfold ptree_formula. unfold contraction_help. simpl. rewrite eq_f_refl. auto.
  + auto.
Qed.



Theorem cut_elimination_ord : forall (P : ptree),
  valid P -> ord_ltb (ord_2_exp (ptree_ord P)) (ptree_ord (cut_elimination P)) = false.
Proof.
intros. induction P.
  - simpl. destruct (ptree_ord P) eqn:O.
   + simpl. rewrite O. auto.
   + destruct X as [X1 X2]. pose proof (IHP X2) as Y1. auto.
  - destruct X as [[X1 X2] X3]. simpl. destruct o. inversion X1. pose proof (IHP X2) as Y1. destruct (ord_semiconnex_bool (ord_2_exp (ptree_ord P)) (ptree_ord (cut_elimination P))) as [X | [X | X]].
    + rewrite X in Y1. inversion Y1.
    + apply ltb_asymm. apply (ord_ltb_trans _ _ _ X). apply ord_lt_ltb. apply ord_2_exp_monot; auto. apply ptree_ord_nf. auto.
    + apply ord_eqb_eq in X. destruct X. apply ltb_asymm. apply ord_lt_ltb. apply ord_2_exp_monot; auto. apply ptree_ord_nf. auto.
  - auto.
  - destruct X as  [[[X1 X2] X3] X4]. pose proof (IHP X2) as Y1. simpl. destruct (ord_2_exp_fp o). rewrite X4. apply ptree_ord_nf. auto. apply ord_lt_ltb in H. apply ltb_asymm. destruct o; auto. rewrite H. auto.
  - destruct X as  [[[X1 X2] X3] X4]. pose proof (IHP X2) as Y1. simpl. destruct (ord_2_exp_fp o). rewrite X4. apply ptree_ord_nf. auto. apply ord_lt_ltb in H. apply ltb_asymm. destruct o; auto. rewrite H. auto.
  - destruct X as  [[[X1 X2] X3] X4]. pose proof (IHP X2) as Y1. simpl. destruct (ord_2_exp_fp o). rewrite X4. apply ptree_ord_nf. auto. apply ord_lt_ltb in H. apply ltb_asymm. destruct o; auto. rewrite H. auto.
  - destruct X as  [[[X1 X2] X3] X4]. pose proof (IHP X2) as Y1. simpl. destruct (ord_2_exp_fp o). rewrite X4. apply ptree_ord_nf. auto. apply ord_lt_ltb in H. apply ltb_asymm. destruct o; auto. rewrite H. auto.
  - destruct X as  [[[X1 X2] X3] X4]. pose proof (IHP X2) as Y1. simpl. destruct (ord_2_exp_fp o). rewrite X4. apply ptree_ord_nf. auto. apply ord_lt_ltb in H. apply ltb_asymm. destruct o; auto. rewrite H. auto.
  - destruct X as  [[[X1 X2] X3] X4]. pose proof (IHP X2) as Y1. simpl. destruct (ord_2_exp_fp o). rewrite X4. apply ptree_ord_nf. auto. apply ord_lt_ltb in H. apply ltb_asymm. destruct o; auto. rewrite H. auto.
  - destruct X as  [[[[X1 X2] X3] X4] X5]. pose proof (IHP X3) as Y1. pose (ord_succ_not_exp_fp (ptree_ord P) (ord_succ_nf _ (ptree_ord_nf _ X3))) as F1. rewrite <- X5 in F1. apply ord_lt_ltb in F1. apply ltb_asymm. simpl. case (ord_succ o) eqn:Y. pose (ord_succ_non_Zero o). rewrite Y in e. inversion e. simpl. rewrite Y. auto.
  - destruct X as  [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. pose proof (IHP1 X2) as Y1. pose proof (IHP2 X4) as Y2. simpl. pose (ord_succ_not_exp_fp (ord_max (ptree_ord P1) (ptree_ord P2)) (ord_succ_nf _ (ord_max_nf _ _ (ptree_ord_nf _ X2) (ptree_ord_nf _ X4)))) as F1.
    rewrite <- X7 in F1. rewrite <- X8 in F1. apply ord_lt_ltb in F1. apply ltb_asymm. simpl. case (ord_succ (ord_max o o0)) eqn:Y. pose (ord_succ_non_Zero (ord_max o o0)). rewrite Y in e. inversion e. simpl. rewrite Y. auto.
  - destruct X as  [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. pose proof (IHP1 X2) as Y1. pose proof (IHP2 X4) as Y2. simpl. pose (ord_succ_not_exp_fp (ord_max (ptree_ord P1) (ptree_ord P2)) (ord_succ_nf _ (ord_max_nf _ _ (ptree_ord_nf _ X2) (ptree_ord_nf _ X4)))) as F1.
    rewrite <- X7 in F1. rewrite <- X8 in F1. apply ord_lt_ltb in F1. apply ltb_asymm. simpl. case (ord_succ (ord_max o o0)) eqn:Y. pose (ord_succ_non_Zero (ord_max o o0)). rewrite Y in e. inversion e. simpl. rewrite Y. auto.
  - destruct X as  [[[X1 X2] X3] X4]. pose proof (IHP X2) as Y1. pose (ord_succ_not_exp_fp (ptree_ord P) (ord_succ_nf _ (ptree_ord_nf _ X2))) as F1. rewrite <- X4 in F1. apply ord_lt_ltb in F1. apply ltb_asymm. simpl. case (ord_succ o) eqn:Y. pose (ord_succ_non_Zero o). rewrite Y in e. inversion e. simpl. rewrite Y. auto.
  - destruct X as  [[[X1 X2] X3] X4]. pose proof (IHP X2) as Y1. pose (ord_succ_not_exp_fp (ptree_ord P) (ord_succ_nf _ (ptree_ord_nf _ X2))) as F1. rewrite <- X4 in F1. apply ord_lt_ltb in F1. apply ltb_asymm. simpl. case (ord_succ o) eqn:Y. pose (ord_succ_non_Zero o). rewrite Y in e. inversion e. simpl. rewrite Y. auto.
  - destruct X as  [[[X1 X2] X3] X4]. pose proof (IHP X2) as Y1. pose (ord_succ_not_exp_fp (ptree_ord P) (ord_succ_nf _ (ptree_ord_nf _ X2))) as F1. rewrite <- X4 in F1. apply ord_lt_ltb in F1. apply ltb_asymm. simpl. case (ord_succ o) eqn:Y. pose (ord_succ_non_Zero o). rewrite Y in e. inversion e. simpl. rewrite Y. auto.
  - destruct X as  [[[X1 X2] X3] X4]. pose proof (IHP X2) as Y1. pose (ord_succ_not_exp_fp (ptree_ord P) (ord_succ_nf _ (ptree_ord_nf _ X2))) as F1. rewrite <- X4 in F1. apply ord_lt_ltb in F1. apply ltb_asymm. simpl. case (ord_succ o) eqn:Y. pose (ord_succ_non_Zero o). rewrite Y in e. inversion e. simpl. rewrite Y. auto.
  - destruct (X czero) as [[[X1 X2] X3] X4]. pose proof (H czero X2) as Y1. pose (ord_succ_not_exp_fp (ptree_ord (p czero)) (ord_succ_nf _ (ptree_ord_nf _ X2))) as F1. rewrite <- X4 in F1. apply ord_lt_ltb in F1. apply ltb_asymm. simpl. case (ord_succ o) eqn:Y. pose (ord_succ_non_Zero o). rewrite Y in e. inversion e. simpl. rewrite Y. auto.
  - destruct (X czero) as [[[X1 X2] X3] X4]. pose proof (H czero X2) as Y1. pose (ord_succ_not_exp_fp (ptree_ord (p czero)) (ord_succ_nf _ (ptree_ord_nf _ X2))) as F1. rewrite <- X4 in F1. apply ord_lt_ltb in F1. apply ltb_asymm. simpl. case (ord_succ o) eqn:Y. pose (ord_succ_non_Zero o). rewrite Y in e. inversion e. simpl. rewrite Y. auto.
  - case (ord_succ (ord_max o o0)) eqn:Y. pose (ord_succ_non_Zero (ord_max o o0)). rewrite Y in e. inversion e. unfold cut_elimination. unfold ptree_ord. fold ptree_ord. rewrite Y. destruct f0.
    + simpl. destruct (correct_a a).
      * simpl. apply ltb_asymm. rewrite <- Y. apply ord_lt_ltb. destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. rewrite formula_sub_ptree_ord_neg; auto. rewrite <- X8. apply (lt_trans _ _ _ (ord_succ_monot _)). apply ord_succ_lt_exp_succ_max_right. rewrite X7. apply ptree_ord_nf. auto. rewrite X8. apply ptree_ord_nf. auto.
      * simpl. apply ltb_asymm. rewrite <- Y. apply ord_lt_ltb. destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. apply (lt_trans _ _ _ (ord_succ_monot _)). apply ord_succ_lt_exp_succ_max_left. rewrite X7. apply ptree_ord_nf. auto. rewrite X8. apply ptree_ord_nf. auto.
    + simpl. case ( eq_nat (max (max n0 n) (S (num_conn f0))) (S (num_conn f0))) eqn:Y1.
      * simpl. case (ord_max o o0) eqn:Y2.
        --  simpl. rewrite <- Y. rewrite ord_max_symm. rewrite Y2. auto.
        --  destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. rewrite <- Y. rewrite <- Y2. rewrite ord_max_symm. apply ord_succ_lt_exp_succ_dub_succ. rewrite X7,X8. apply ord_max_nf; apply ptree_ord_nf; auto. apply ord_lt_ltb. apply ord_succ_not_exp_fp. rewrite X7,X8. apply ord_succ_nf. apply ord_max_nf; apply ptree_ord_nf; auto.  
      * simpl. rewrite <- Y. destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. pose (ord_succ_not_exp_fp (ord_max (ptree_ord P1) (ptree_ord P2)) (ord_succ_nf _ (ord_max_nf _ _ (ptree_ord_nf _ X2) (ptree_ord_nf _ X4)))) as F1. rewrite X7,X8. rewrite ord_max_symm. apply ord_succ_lt_exp_succ_dub_succ. apply ord_max_nf; apply ptree_ord_nf; auto. apply ord_lt_ltb. apply ord_succ_not_exp_fp. apply ord_succ_nf. apply ord_max_nf; apply ptree_ord_nf; auto.
    + simpl. rewrite (ord_max_lem2 _ _ (ltb_asymm _ _ (ord_lt_ltb _ _ (ord_max_succ_r _ _ )))). rewrite <- Y. destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. apply ord_succ_lt_exp_succ_dub_succ. rewrite X7,X8. apply ord_max_nf; apply ptree_ord_nf; auto. pose (ord_succ_not_exp_fp (ord_max (ptree_ord P1) (ptree_ord P2)) (ord_succ_nf _ (ord_max_nf _ _ (ptree_ord_nf _ X2) (ptree_ord_nf _ X4)))) as F1. apply ord_lt_ltb. rewrite X7,X8. auto. 
    + simpl. rewrite <- Y. destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. rewrite X7,X8. pose (ord_succ_not_exp_fp (ord_max (ptree_ord P1) (ptree_ord P2)) (ord_succ_nf _ (ord_max_nf _ _ (ptree_ord_nf _ X2) (ptree_ord_nf _ X4)))) as F1. apply ltb_asymm. apply ord_lt_ltb. auto.
  - case (ord_succ (ord_succ (ord_max o o0))) eqn:Y. pose (ord_succ_non_Zero (ord_succ (ord_max o o0))). rewrite Y in e. inversion e. unfold cut_elimination. unfold ptree_ord. fold ptree_ord. rewrite Y. destruct f.
    + simpl. destruct (correct_a a).
      * simpl. apply ltb_asymm. rewrite <- Y. apply ord_lt_ltb. destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. apply (lt_trans _ _ _ (ord_succ_monot _)). assert (nf (ord_succ o0)). apply ord_succ_nf. rewrite X8. apply ptree_ord_nf. auto. apply (lt_trans _ _ _ (ord_succ_not_exp_fp _ H)). apply ord_2_exp_monot; try repeat apply ord_succ_nf;
        try apply ord_max_nf; try rewrite X7; try rewrite X8; try apply ptree_ord_nf; auto. apply ord_lt_succ. apply ord_max_succ_r.
      * simpl. apply ltb_asymm. rewrite <- Y. apply ord_lt_ltb. destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. rewrite formula_sub_ptree_ord_atom; auto. rewrite <- X7. apply (lt_trans _ _ _ (ord_succ_monot _)). assert (nf (ord_succ o)). apply ord_succ_nf. rewrite X7. apply ptree_ord_nf. auto. apply (lt_trans _ _ _ (ord_succ_not_exp_fp _ H)). apply ord_2_exp_monot; try repeat apply ord_succ_nf;
      try apply ord_max_nf; try rewrite X7; try rewrite X8; try apply ptree_ord_nf; auto. apply ord_lt_succ. apply ord_max_succ_l.
    + simpl. case ( eq_nat (max (max n0 n) (S (num_conn f0))) (S (num_conn f0))) eqn:Y1.
      * simpl. apply ltb_asymm. rewrite <- Y. apply ord_lt_ltb. destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. pose proof (ord_succ_not_exp_fp (ord_max (ptree_ord P1) (ptree_ord P2)) (ord_succ_nf _ (ord_max_nf _ _ (ptree_ord_nf _ X2) (ptree_ord_nf _ X4)))) as F1. rewrite X7,X8. rewrite ord_max_symm. apply (lt_trans _ _ _ F1). apply ord_2_exp_monot; try repeat apply ord_succ_nf;
        try apply ord_max_nf; try rewrite X7; try rewrite X8; try apply ptree_ord_nf; auto. apply ord_succ_monot.
      * simpl. apply ltb_asymm. rewrite <- Y. apply ord_lt_ltb. destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. pose proof (ord_succ_not_exp_fp (ord_max (ptree_ord P1) (ptree_ord P2)) (ord_succ_nf _ (ord_max_nf _ _ (ptree_ord_nf _ X2) (ptree_ord_nf _ X4)))) as F1. rewrite X7,X8. rewrite ord_max_symm.  apply (lt_trans _ _ _ F1). apply ord_2_exp_monot; try repeat apply ord_succ_nf;
        try apply ord_max_nf; try rewrite X7; try rewrite X8; try apply ptree_ord_nf; auto. apply ord_succ_monot.
    + simpl. rewrite <- Y. destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. apply ltb_asymm. apply ord_lt_ltb. apply ord_succ_not_exp_fp. repeat apply ord_succ_nf; apply ord_max_nf; try rewrite X7; try rewrite X8; apply ptree_ord_nf; auto. 
    + simpl. rewrite <- Y. destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. rewrite X7,X8. apply ltb_asymm. apply ord_lt_ltb. refine (lt_trans _ _ _ _ (ord_succ_lt_exp_succ _ _ _)). apply ord_lt_succ. apply ord_succ_not_exp_fp. apply ord_succ_nf. apply ord_max_nf; apply ptree_ord_nf; auto. apply ord_succ_nf. apply ord_max_nf; apply ptree_ord_nf; auto. destruct (ord_max (ptree_ord P1) (ptree_ord P2)); try destruct o1_3; apply zero_lt.
  - case (ord_succ (ord_max o o0)) eqn:Y. pose (ord_succ_non_Zero (ord_max o o0)). rewrite Y in e. inversion e. unfold cut_elimination. unfold ptree_ord. fold ptree_ord. rewrite Y. destruct f0.
    + simpl. destruct (correct_a a).
      * simpl. apply ltb_asymm. rewrite <- Y. apply ord_lt_ltb. destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. apply ord_succ_lt_exp_succ_max_right. rewrite X7. apply ptree_ord_nf. auto. rewrite X8. apply ptree_ord_nf. auto.
      * simpl. apply ltb_asymm. rewrite <- Y. apply ord_lt_ltb. destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. apply ord_succ_lt_exp_succ_max_left. rewrite X7. apply ptree_ord_nf. auto. rewrite X8. apply ptree_ord_nf. auto.
    + simpl. apply ltb_asymm. rewrite <- Y. apply ord_lt_ltb. destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. pose (ord_succ_not_exp_fp (ord_max (ptree_ord P1) (ptree_ord P2)) (ord_succ_nf _ (ord_max_nf _ _ (ptree_ord_nf _ X2) (ptree_ord_nf _ X4)))) as F1. rewrite X7,X8. auto.
    + simpl. unfold contraction_help. simpl. rewrite eq_f_refl. simpl. rewrite (ord_max_lem2 _ _ (ltb_asymm _ _ (ord_lt_ltb _ _ (ord_max_succ_r _ _ )))). rewrite <- Y. destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. apply ord_succ_lt_exp_succ_dub_succ. rewrite X7,X8. apply ord_max_nf; apply ptree_ord_nf; auto. pose (ord_succ_not_exp_fp (ord_max (ptree_ord P1) (ptree_ord P2)) (ord_succ_nf _ (ord_max_nf _ _ (ptree_ord_nf _ X2) (ptree_ord_nf _ X4)))) as F1. apply ord_lt_ltb. rewrite X7,X8. auto. 
    + simpl. apply ltb_asymm. rewrite <- Y. apply ord_lt_ltb. destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. pose (ord_succ_not_exp_fp (ord_max (ptree_ord P1) (ptree_ord P2)) (ord_succ_nf _ (ord_max_nf _ _ (ptree_ord_nf _ X2) (ptree_ord_nf _ X4)))) as F1. rewrite X7,X8. auto.
Qed.

Theorem cut_elimination_valid : forall (P : ptree),
  valid P -> valid (cut_elimination P).
Proof.
  intros. induction P.
- simpl. destruct X. destruct (ptree_ord P); simpl; auto.
- simpl. destruct o; simpl; simpl in X; destruct X as [[X1 X2] X3]; auto.
- simpl. auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct (ord_succ o); simpl; auto.
- simpl. destruct (ord_succ (ord_max o o0)); simpl; auto.
- simpl. destruct (ord_succ (ord_max o o0)); simpl; auto.
- simpl. destruct (ord_succ o); simpl; auto.
- simpl. destruct (ord_succ o); simpl; auto.
- simpl. destruct (ord_succ o); simpl; auto.
- simpl. destruct (ord_succ o); simpl; auto.
- simpl. destruct (ord_succ o); simpl; auto.
- simpl. destruct (ord_succ o); simpl; auto.
- simpl. destruct (ord_succ (ord_max o o0)) eqn:F. simpl. auto. destruct f0.
  + case (correct_a a) eqn:H.
    * destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8].
      pose proof (provable_closed' P1 (lor f (atom a)) X2 X1) as Y1.
      simpl in Y1. apply and_bool_prop in Y1. destruct Y1 as [Y1 Y2].
      apply formula_sub_valid_neg; auto. simpl. unfold incorrect_a. rewrite (correct_correctness _ H). auto. rewrite X3. auto.
    * simpl. simpl in X. destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8].
      pose proof (provable_closed' P1 (lor f (atom a)) X2 X1) as Y1.
      simpl in Y1. apply and_bool_prop in Y1. destruct Y1 as [Y1 Y2].
      repeat split; auto.
      { pose proof (formula_sub_ptree_formula_atom P1 a f X2 (lor_ind (non_target f) (1) )). rewrite H0.
        rewrite X1. apply lor_sub_right. auto. }
      { apply formula_sub_valid_atom; simpl; auto. rewrite X1. simpl. apply and_bool_symm. apply non_target_fit. }
      { rewrite X5. apply eq_sym. apply formula_sub_ptree_deg_atom. auto. }
      { rewrite X7. apply eq_sym. apply formula_sub_ptree_ord_atom. auto. }
  + case (eq_nat (max (max n0 n) (S (num_conn f0))) (S (num_conn f0))) eqn:Hd.
    * destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8].
      repeat split; auto.
      { rewrite dub_neg_ptree_formula; auto. rewrite X3. unfold dub_neg_sub_formula. simpl. rewrite eq_f_refl. auto. } 
      { apply dub_neg_valid; auto. rewrite X3. auto. }
      { rewrite X6. apply eq_sym. apply dub_neg_ptree_deg. auto. }
      { rewrite X8. apply eq_sym. apply dub_neg_ptree_ord. auto. }
    * destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8].
      repeat split; auto.
      { rewrite dub_neg_ptree_formula; auto. rewrite X3. unfold dub_neg_sub_formula. simpl. rewrite eq_f_refl. auto. }
      { apply dub_neg_valid. auto. rewrite X3. auto. }
      { rewrite X6. apply eq_sym. apply dub_neg_ptree_deg. auto. }
      { rewrite X8. apply eq_sym. apply dub_neg_ptree_ord. auto. }
  + destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. repeat split; simpl; auto.
    * unfold associativity_2'. rewrite X1. simpl. auto.
    * unfold associativity_2'. rewrite X1. simpl. repeat split; auto.
    * rewrite demorgan2_ptree_formula; auto. rewrite X3. unfold demorgan2_sub_formula. simpl. repeat rewrite eq_f_refl. auto. 
    * apply demorgan2_valid; auto. rewrite X3. auto.
    * unfold associativity_2'. rewrite X1. simpl. auto.
    * rewrite demorgan2_ptree_deg; auto.
    * unfold associativity_2'. rewrite X1. simpl. auto.
    * rewrite demorgan2_ptree_ord; auto.
    * rewrite demorgan1_ptree_formula; auto. rewrite X3. unfold demorgan1_sub_formula. simpl. repeat rewrite eq_f_refl. auto. 
    * apply demorgan1_valid; auto. rewrite X3. auto.
    * rewrite demorgan1_ptree_deg; auto.
    * rewrite demorgan1_ptree_ord; auto.  
  + destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. repeat split; simpl; auto.
- simpl. destruct (ord_succ (ord_succ (ord_max o o0))) eqn:F. simpl. auto.
  destruct f.
  + case (correct_a a) eqn:H.
   * destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8].
     pose proof (provable_closed' P2 (lor (neg (atom a)) f0) X4 X3) as Z1.
     simpl in Z1. apply and_bool_prop in Z1. destruct Z1 as [Z1 Z2].
     repeat split; auto.
     { pose proof (formula_sub_ptree_formula_neg P2 a f0 X4 (lor_ind (1) (non_target f0))). rewrite H0.
       rewrite X3. apply lor_sub_left. auto. }
     { apply formula_sub_valid_neg; simpl; auto. apply correct_correctness in H. unfold incorrect_a. rewrite H. auto. rewrite X3. simpl. apply non_target_fit. }
     { rewrite X6. apply eq_sym. apply formula_sub_ptree_deg_neg. auto. }
     { rewrite X8. apply eq_sym. apply formula_sub_ptree_ord_neg. auto. }
   * destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8].
     pose proof (provable_closed' P2 (lor (neg (atom a)) f0) X4 X3) as Z1.
     simpl in Z1. apply and_bool_prop in Z1. destruct Z1 as [Z1 Z2].
     apply formula_sub_valid_atom; auto. rewrite X1. auto.
  + case (eq_nat (max (max n0 n) (S (num_conn f0))) (S (num_conn f0))) eqn:Hd.
    * simpl. simpl in X. destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8].
      repeat split; auto.
      {  pose proof (dub_neg_ptree_formula P2 f X4 (lor_ind (1) (non_target f0))). rewrite H. rewrite X3. unfold dub_neg_sub_formula. apply lor_sub_left. auto. }
      { apply dub_neg_valid. auto. rewrite X3. simpl. apply non_target_fit. }
      { rewrite X6. apply eq_sym. apply dub_neg_ptree_deg. auto. }
      { rewrite X8. apply eq_sym. apply dub_neg_ptree_ord. auto. }
    * simpl. simpl in X. destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8].
      repeat split; auto.
      { pose proof (dub_neg_ptree_formula P2 f X4 (lor_ind (1) (non_target f0))). rewrite H.
        rewrite X3. unfold dub_neg_sub_formula. apply lor_sub_left. auto. }
      { apply dub_neg_valid. auto. rewrite X3. simpl. apply non_target_fit. }
      { rewrite X6. apply eq_sym. apply dub_neg_ptree_deg. auto. }
      { rewrite X8. apply eq_sym. apply dub_neg_ptree_ord. auto. }
  + destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. repeat split; simpl; auto.
    * pose proof (demorgan2_ptree_formula P2 f1 f2 X4 (lor_ind (1) (non_target f0))). rewrite H. rewrite X3. unfold demorgan2_sub_formula. apply lor_sub_left. auto. 
    * apply demorgan2_valid. auto. rewrite X3. simpl. rewrite non_target_fit. auto.
    * rewrite demorgan2_ptree_deg; auto.
    * rewrite demorgan2_ptree_ord; auto.
    * rewrite demorgan1_ptree_formula; auto. rewrite X3. unfold demorgan1_sub_formula. simpl. rewrite non_target_fit. repeat rewrite eq_f_refl. simpl. rewrite non_target_sub'. auto. 
    * apply demorgan1_valid. auto. rewrite X3. simpl. rewrite non_target_fit. auto.
    * rewrite demorgan1_ptree_deg; auto.
    * rewrite demorgan1_ptree_ord; auto.
    * rewrite <- (nat_max_order (max _ _) n0). rewrite (nat_max_comm _ n0 n0). rewrite max_n_n. repeat rewrite nat_max_comm. simpl. rewrite (nat_max_symm (num_conn _)). auto.
    * rewrite <- F. rewrite (ord_max_lem2 (ord_succ (ord_max _ _))). auto. apply ltb_asymm. apply ord_lt_ltb. apply ord_max_succ_r.
  + auto.
- simpl. destruct (ord_succ (ord_max o o0)) eqn:F. simpl. auto.
  destruct f0.
  + case (correct_a a) eqn:H.
   * simpl. simpl in X. destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8].
     pose proof (provable_closed' P1 (lor f (atom a)) X2 X1) as Y1.
     simpl in Y1. apply and_bool_prop in Y1. destruct Y1 as [Y1 Y2].
     pose proof (provable_closed' P2 (lor (neg (atom a)) f1) X4 X3) as Z1.
     simpl in Z1. apply and_bool_prop in Z1. destruct Z1 as [Z1 Z2].
     repeat split; auto.
     { pose proof (formula_sub_ptree_formula_neg P2 a f1 X4 (lor_ind (1) (non_target f1))). rewrite H0.
       rewrite X3. apply lor_sub_left. auto. }
     { apply formula_sub_valid_neg; simpl; auto. apply correct_correctness in H. unfold incorrect_a. rewrite H. auto. rewrite X3. simpl. apply non_target_fit. }
     { rewrite X6. apply eq_sym. apply formula_sub_ptree_deg_neg. auto. }
     { rewrite X8. apply eq_sym. apply formula_sub_ptree_ord_neg. auto. }
   * simpl. simpl in X. destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8].
     pose proof (provable_closed' P1 (lor f (atom a)) X2 X1) as Y1.
     simpl in Y1. apply and_bool_prop in Y1. destruct Y1 as [Y1 Y2].
     pose proof (provable_closed' P2 (lor (neg (atom a)) f1) X4 X3) as Z1.
     simpl in Z1. apply and_bool_prop in Z1. destruct Z1 as [Z1 Z2].
     repeat split; auto.
     { pose proof (formula_sub_ptree_formula_atom P1 a f X2 (lor_ind (non_target f) (1) )). rewrite H0.
       rewrite X1. apply lor_sub_right. auto. }
     { apply formula_sub_valid_atom; simpl; auto. rewrite X1. simpl. apply and_bool_symm. apply non_target_fit. }
     { rewrite X5. apply eq_sym. apply formula_sub_ptree_deg_atom. auto. }
     { rewrite X7. apply eq_sym. apply formula_sub_ptree_ord_atom. auto. }
  + unfold valid. fold valid. simpl. simpl in X. destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8].
    repeat split; auto.
    * pose proof (dub_neg_ptree_formula P2 f0 X4 (lor_ind (1) (non_target f1))). rewrite H.
      rewrite X3. unfold dub_neg_sub_formula. apply lor_sub_left. auto. 
    * apply dub_neg_valid. auto. rewrite X3. simpl. apply non_target_fit.
    * rewrite X6. apply eq_sym. apply dub_neg_ptree_deg. auto.
    * rewrite X8. apply eq_sym. apply dub_neg_ptree_ord. auto.
    * rewrite <- F. rewrite ord_max_symm. reflexivity.
  + destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. unfold contraction_help. simpl. rewrite eq_f_refl. simpl. repeat split; simpl; auto.
    * unfold associativity_2'. rewrite X1. simpl. auto.
    * unfold associativity_2'. rewrite X1. simpl. repeat split; auto.
    * rewrite demorgan2_ptree_formula; auto. rewrite X3. unfold demorgan2_sub_formula. simpl. rewrite non_target_fit. repeat rewrite eq_f_refl. simpl. rewrite non_target_sub'. auto. 
    * apply demorgan2_valid. auto. rewrite X3. simpl. rewrite non_target_fit. auto.
    * unfold associativity_2'. rewrite X1. simpl. auto.
    * rewrite demorgan2_ptree_deg; auto.
    * unfold associativity_2'. rewrite X1. simpl. auto.
    * rewrite demorgan2_ptree_ord; auto.
    * rewrite demorgan1_ptree_formula; auto. rewrite X3. unfold demorgan1_sub_formula. simpl. rewrite non_target_fit. repeat rewrite eq_f_refl. simpl. rewrite non_target_sub'. auto. 
    * apply demorgan1_valid. auto. rewrite X3. simpl. rewrite non_target_fit. auto.
    * rewrite demorgan1_ptree_deg; auto.
    * rewrite demorgan1_ptree_ord; auto.
  + auto.
Qed.


Lemma cut_elim_ord_Zero : forall (P : ptree) (A : formula) (d : nat),
P_proves P A (S d) Zero -> provable A d (ord_2_exp Zero).
Proof.
unfold provable. unfold P_proves. intros P. induction P.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in X3. inversion X2. exists (ord_up (ord_2_exp Zero) P). repeat split; auto. simpl in X4. rewrite X4. simpl. apply zero_lt. simpl. apply one_nf. simpl. lia.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in X4. destruct X2 as [[H1 H2] H3]. rewrite X4 in H1. apply zero_minimal in H1. inversion H1.
- intros. destruct X as [[[X1 X2] X3] X4]. exists (ord_up (ord_2_exp Zero) (node f)). repeat split; auto. apply zero_lt. apply one_nf. simpl. lia.
- intros. destruct X as [[[X1 X2] X3] X4]. destruct X2 as [[[H1 H2] H3] H4]. simpl in X3,X4. rewrite X4 in *. destruct (IHP (lor f f0) d) as [P1 [[[Y1 Y2] Y3] Y4]]. repeat split; auto. lia. exists (exchange_ab f f0 (ptree_deg P1) (ptree_ord P1) P1). repeat split; simpl; auto.
- intros. destruct X as [[[X1 X2] X3] X4]. destruct X2 as [[[H1 H2] H3] H4]. simpl in X3,X4. rewrite X4 in *. destruct (IHP (lor (lor f f0) f1) d) as [P1 [[[Y1 Y2] Y3] Y4]]. repeat split; auto. lia. exists (exchange_cab f f0 f1 (ptree_deg P1) (ptree_ord P1) P1). repeat split; simpl; auto.
- intros. destruct X as [[[X1 X2] X3] X4]. destruct X2 as [[[H1 H2] H3] H4]. simpl in X3,X4. rewrite X4 in *. destruct (IHP (lor (lor f f0) f1) d) as [P1 [[[Y1 Y2] Y3] Y4]]. repeat split; auto. lia. exists (exchange_abd f f0 f1 (ptree_deg P1) (ptree_ord P1) P1). repeat split; simpl; auto.
- intros. destruct X as [[[X1 X2] X3] X4]. destruct X2 as [[[H1 H2] H3] H4]. simpl in X3,X4. rewrite X4 in *. destruct (IHP (lor (lor (lor f f0) f1) f2) d) as [P1 [[[Y1 Y2] Y3] Y4]]. repeat split; auto. lia. exists (exchange_cabd f f0 f1 f2 (ptree_deg P1) (ptree_ord P1) P1). repeat split; simpl; auto.
- intros. destruct X as [[[X1 X2] X3] X4]. destruct X2 as [[[H1 H2] H3] H4]. simpl in X3,X4. rewrite X4 in *. destruct (IHP (lor f f) d) as [P1 [[[Y1 Y2] Y3] Y4]]. repeat split; auto. lia. exists (contraction_a f (ptree_deg P1) (ptree_ord P1) P1). repeat split; simpl; auto.
- intros. destruct X as [[[X1 X2] X3] X4]. destruct X2 as [[[H1 H2] H3] H4]. simpl in X3,X4. rewrite X4 in *. destruct (IHP (lor (lor f f) f0) d) as [P1 [[[Y1 Y2] Y3] Y4]]. repeat split; auto. lia. exists (contraction_ad f f0 (ptree_deg P1) (ptree_ord P1) P1). repeat split; simpl; auto.
- intros. destruct X as [[[X1 X2] X3] X4]. destruct X2 as [[[H1 H2] H3] H4]. simpl in X3,X4. pose (ord_succ_non_Zero o). rewrite X4 in e. inversion e.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in X4. pose (ord_succ_non_Zero (ord_max o o0)). rewrite X4 in e. inversion e.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in X4. pose (ord_succ_non_Zero (ord_max o o0)). rewrite X4 in e. inversion e.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in X4. pose (ord_succ_non_Zero o). rewrite X4 in e. inversion e.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in X4. pose (ord_succ_non_Zero o). rewrite X4 in e. inversion e.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in X4. pose (ord_succ_non_Zero o). rewrite X4 in e. inversion e.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in X4. pose (ord_succ_non_Zero o). rewrite X4 in e. inversion e.
- intros. destruct X0 as [[[X1 X2] X3] X4]. simpl in X4. pose (ord_succ_non_Zero o). rewrite X4 in e. inversion e.
- intros. destruct X0 as [[[X1 X2] X3] X4]. simpl in X4. pose (ord_succ_non_Zero o). rewrite X4 in e. inversion e.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in X4. pose (ord_succ_non_Zero (ord_max o o0)). rewrite X4 in e. inversion e.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in X4. pose (ord_succ_non_Zero (ord_succ (ord_max o o0))). rewrite X4 in e. inversion e.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in X4. pose (ord_succ_non_Zero (ord_max o o0)). rewrite X4 in e. inversion e.
Qed.

Lemma height_zero_not_lor : forall (P : ptree) (f g : formula), valid P -> (ptree_ord P) = Zero -> (ptree_formula P) <> lor f g.
Proof.
intros P. induction P.
- intros. destruct X as [X1 X2]. auto.
- intros. destruct X as [[X1 X2] X3]. simpl in H. rewrite H in X1. inversion X1.
- intros. simpl. destruct f; discriminate.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in H. rewrite H in *. symmetry in X4. pose (IHP f f0 X2 X4). auto.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in H. rewrite H in *. symmetry in X4. pose (IHP (lor f f0) f1 X2 X4). auto.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in H. rewrite H in *. symmetry in X4. pose (IHP (lor f f0) f1 X2 X4). auto.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in H. rewrite H in *. symmetry in X4. pose (IHP (lor (lor f f0) f1) f2 X2 X4). auto.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in H. rewrite H in *. symmetry in X4. pose (IHP f f X2 X4). auto.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in H. rewrite H in *. symmetry in X4. pose (IHP (lor f f) f0 X2 X4). auto.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in H. pose (ord_succ_non_Zero o). rewrite H in e. rewrite ord_eqb_refl in e. inversion e.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in H. pose (ord_succ_non_Zero (ord_max o o0)). rewrite H in e. rewrite ord_eqb_refl in e. inversion e.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in H. pose (ord_succ_non_Zero (ord_max o o0)). rewrite H in e. rewrite ord_eqb_refl in e. inversion e.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in H. pose (ord_succ_non_Zero o). rewrite H in e. rewrite ord_eqb_refl in e. inversion e.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in H. pose (ord_succ_non_Zero o). rewrite H in e. rewrite ord_eqb_refl in e. inversion e.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in H. pose (ord_succ_non_Zero o). rewrite H in e. rewrite ord_eqb_refl in e. inversion e.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in H. pose (ord_succ_non_Zero o). rewrite H in e. rewrite ord_eqb_refl in e. inversion e.
- intros. destruct (X czero) as [[[X1 X2] X3] X4]. simpl in H0. pose (ord_succ_non_Zero o). rewrite H0 in e. rewrite ord_eqb_refl in e. inversion e.
- intros. destruct (X czero) as [[[X1 X2] X3] X4]. simpl in H0. pose (ord_succ_non_Zero o). rewrite H0 in e. rewrite ord_eqb_refl in e. inversion e.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in H. pose (ord_succ_non_Zero (ord_max o o0)). rewrite H in e. rewrite ord_eqb_refl in e. inversion e.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in H. pose (ord_succ_non_Zero (ord_succ (ord_max o o0))). rewrite H in e. rewrite ord_eqb_refl in e. inversion e.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in H. pose (ord_succ_non_Zero (ord_max o o0)). rewrite H in e. rewrite ord_eqb_refl in e. inversion e.
Qed.

Lemma cut_elim_ord_one : forall (P : ptree) (A : formula) (d : nat),
P_proves P A (S d) (cons Zero 0 Zero) -> provable A d (ord_2_exp (cons Zero 0 Zero)).
Proof.
unfold provable. unfold P_proves. intros P. induction P.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in X3. inversion X2. exists (ord_up (ord_2_exp (cons Zero 0 Zero)) P). repeat split; auto. simpl in X4. rewrite X4. simpl. apply coeff_lt. lia. simpl. apply single_nf. apply zero_nf. simpl. lia.
- intros. destruct X as [[[X1 X2] X3] X4]. simpl in X4. destruct X2 as [[H1 H2] H3]. rewrite X4 in H1. pose (ord_lt_one _ H1). rewrite e in *. destruct (cut_elim_ord_Zero P A d) as [P1 [[[Y1 Y2] Y3] Y4]]. unfold P_proves. repeat split; auto. simpl in Y4. exists (ord_up (ord_2_exp (ord_2_exp Zero)) P1). repeat split; simpl; auto. rewrite Y4. apply coeff_lt. lia. apply single_nf. apply zero_nf.
- intros. destruct X as [[[X1 X2] X3] X4]. exists (ord_up (ord_2_exp (cons Zero 0 Zero)) (node f)). repeat split; auto. apply zero_lt. apply single_nf. apply zero_nf. simpl. lia.
- intros. destruct X as [[[X1 X2] X3] X4]. destruct X2 as [[[H1 H2] H3] H4]. simpl in X3,X4. rewrite X4 in *. destruct (IHP (lor f f0) d) as [P1 [[[Y1 Y2] Y3] Y4]]. repeat split; auto. lia. exists (exchange_ab f f0 (ptree_deg P1) (ptree_ord P1) P1). repeat split; simpl; auto.
- intros. destruct X as [[[X1 X2] X3] X4]. destruct X2 as [[[H1 H2] H3] H4]. simpl in X3,X4. rewrite X4 in *. destruct (IHP (lor (lor f f0) f1) d) as [P1 [[[Y1 Y2] Y3] Y4]]. repeat split; auto. lia. exists (exchange_cab f f0 f1 (ptree_deg P1) (ptree_ord P1) P1). repeat split; simpl; auto.
- intros. destruct X as [[[X1 X2] X3] X4]. destruct X2 as [[[H1 H2] H3] H4]. simpl in X3,X4. rewrite X4 in *. destruct (IHP (lor (lor f f0) f1) d) as [P1 [[[Y1 Y2] Y3] Y4]]. repeat split; auto. lia. exists (exchange_abd f f0 f1 (ptree_deg P1) (ptree_ord P1) P1). repeat split; simpl; auto.
- intros. destruct X as [[[X1 X2] X3] X4]. destruct X2 as [[[H1 H2] H3] H4]. simpl in X3,X4. rewrite X4 in *. destruct (IHP (lor (lor (lor f f0) f1) f2) d) as [P1 [[[Y1 Y2] Y3] Y4]]. repeat split; auto. lia. exists (exchange_cabd f f0 f1 f2 (ptree_deg P1) (ptree_ord P1) P1). repeat split; simpl; auto.
- intros. destruct X as [[[X1 X2] X3] X4]. destruct X2 as [[[H1 H2] H3] H4]. simpl in X3,X4. rewrite X4 in *. destruct (IHP (lor f f) d) as [P1 [[[Y1 Y2] Y3] Y4]]. repeat split; auto. lia. exists (contraction_a f (ptree_deg P1) (ptree_ord P1) P1). repeat split; simpl; auto.
- intros. destruct X as [[[X1 X2] X3] X4]. destruct X2 as [[[H1 H2] H3] H4]. simpl in X3,X4. rewrite X4 in *. destruct (IHP (lor (lor f f) f0) d) as [P1 [[[Y1 Y2] Y3] Y4]]. repeat split; auto. lia. exists (contraction_ad f f0 (ptree_deg P1) (ptree_ord P1) P1). repeat split; simpl; auto.
- intros. destruct X as [[[X1 X2] X3] X4]. destruct X2 as [[[[H1 H2] H3] H4] H5]. simpl in X3,X4. apply ord_succ_one in X4. destruct X4. destruct (cut_elim_ord_Zero P f0 d) as [P1 [[[Y1 Y2] Y3] Y4]]. repeat split; auto. lia. exists (weakening_ad f f0 (ptree_deg P1) (ptree_ord P1) P1). repeat split; simpl; auto. rewrite Y4. auto.
- intros. destruct X as [[[X1 X2] X3] X4]. destruct X2 as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8]. simpl in X3,X4. apply ord_succ_one in X4. apply ord_max_0 in X4. destruct X4 as [Y1 Y2]. destruct Y1,Y2.
  destruct (cut_elim_ord_Zero P1 (neg f) (pred n)) as [P4 [[[Y1 Y2] Y3] Y4]]. repeat split; auto. lia.
  destruct (cut_elim_ord_Zero P2 (neg f0) (pred n0)) as [P5 [[[Z1 Z2] Z3] Z4]]. repeat split; auto. lia.
  exists (demorgan_ab f f0 (ptree_deg P4) (ptree_deg P5) (ptree_ord P4) (ptree_ord P5) P4 P5). repeat split; simpl; auto. lia. rewrite Y4,Z4. simpl. auto.
- intros. destruct X as [[[X1 X2] X3] X4]. destruct X2 as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8]. simpl in X3,X4. apply ord_succ_one in X4. apply ord_max_0 in X4. destruct X4 as [Y1 Y2]. destruct Y1,Y2.
  destruct (cut_elim_ord_Zero P1 (lor (neg f) f1) (pred n)) as [P4 [[[Y1 Y2] Y3] Y4]]. repeat split; auto. lia.
  destruct (cut_elim_ord_Zero P2 (lor (neg f0) f1) (pred n0)) as [P5 [[[Z1 Z2] Z3] Z4]]. repeat split; auto. lia.
  exists (demorgan_abd f f0 f1 (ptree_deg P4) (ptree_deg P5) (ptree_ord P4) (ptree_ord P5) P4 P5). repeat split; simpl; auto. lia. rewrite Y4,Z4. simpl. auto.
- intros. destruct X as [[[X1 X2] X3] X4]. destruct X2 as [[[H1 H2] H3] H4]. simpl in X3,X4. apply ord_succ_one in X4. destruct X4. destruct (cut_elim_ord_Zero P f d) as [P1 [[[Y1 Y2] Y3] Y4]]. repeat split; auto. lia. exists (negation_a f (ptree_deg P1) (ptree_ord P1) P1). repeat split; simpl; auto. rewrite Y4. auto.
- intros. destruct X as [[[X1 X2] X3] X4]. destruct X2 as [[[H1 H2] H3] H4]. simpl in X3,X4. apply ord_succ_one in X4. destruct X4. destruct (cut_elim_ord_Zero P (lor f f0) d) as [P1 [[[Y1 Y2] Y3] Y4]]. repeat split; auto. lia. exists (negation_ad f f0 (ptree_deg P1) (ptree_ord P1) P1). repeat split; simpl; auto. rewrite Y4. auto.
- intros. destruct X as [[[X1 X2] X3] X4]. destruct X2 as [[[H1 H2] H3] H4]. simpl in X3,X4. apply ord_succ_one in X4. destruct X4. destruct (cut_elim_ord_Zero P (neg (substitution f n (projT1 c))) (pred n0)) as [P1 [[[Y1 Y2] Y3] Y4]]. repeat split; auto. lia. exists (quantification_a f n c (ptree_deg P1) (ptree_ord P1) P1). repeat split; simpl; auto. lia. rewrite Y4. simpl. auto.
- intros. destruct X as [[[X1 X2] X3] X4]. destruct X2 as [[[H1 H2] H3] H4]. simpl in X3,X4. apply ord_succ_one in X4. destruct X4. destruct (cut_elim_ord_Zero P (lor (neg (substitution f n (projT1 c))) f0) (pred n0)) as [P1 [[[Y1 Y2] Y3] Y4]]. repeat split; auto. lia. exists (quantification_ad f f0 n c (ptree_deg P1) (ptree_ord P1) P1). repeat split; simpl; auto. lia. rewrite Y4. simpl. auto.
- intros. destruct X0 as [[[X1 X2] X3] X4]. simpl in X1,X3,X4. apply ord_succ_one in X4. destruct X4. unfold valid in X2. fold valid in X2. assert (forall c, P_proves (p c) (substitution f n (projT1 c)) (S d) Zero).
  { intros. unfold P_proves. destruct (X2 c) as [[[Y1 Y2] Y3] Y4]. repeat split; simpl; auto. lia. }
  exists (w_rule_a f n d (cons Zero 0 Zero) (fun m => projT1(cut_elim_ord_Zero (p m) _ _ (X0 m)))). repeat split; simpl; auto.
  + destruct cut_elim_ord_Zero as [P [[[HP1 HP2] HP3] HP4]]. simpl. auto.
  + destruct cut_elim_ord_Zero as [P [[[HP1 HP2] HP3] HP4]]. simpl. auto.
  + destruct cut_elim_ord_Zero as [P [[[HP1 HP2] HP3] HP4]]. simpl. auto.
  + destruct cut_elim_ord_Zero as [P [[[HP1 HP2] HP3] HP4]]. simpl. auto.
- intros. destruct X0 as [[[X1 X2] X3] X4]. simpl in X1,X3,X4. apply ord_succ_one in X4. destruct X4. unfold valid in X2. fold valid in X2. destruct (X2 czero) as [[[Y1 Y2] Y3] Y4]. symmetry in Y4. pose (height_zero_not_lor _ (substitution f n (represent 0)) f0 Y2 Y4). contradiction.
- intros. destruct X as [[[X1 X2] X3] X4]. destruct X2 as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8]. simpl in X3,X4. apply ord_succ_one in X4. apply ord_max_0 in X4. destruct X4 as [Y1 Y2]. destruct Y1,Y2. symmetry in H7. pose (height_zero_not_lor _ f f0 H2 H7). contradiction.
- intros. destruct X as [[[X1 X2] X3] X4]. destruct X2 as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8]. simpl in X3,X4. apply ord_succ_one in X4. pose (ord_succ_non_Zero (ord_max o o0)). rewrite X4 in e. rewrite ord_eqb_refl in e. inversion e.
- intros. destruct X as [[[X1 X2] X3] X4]. destruct X2 as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8]. simpl in X3,X4. apply ord_succ_one in X4. apply ord_max_0 in X4. destruct X4 as [Y1 Y2]. destruct Y1,Y2. symmetry in H7. pose (height_zero_not_lor _ f f0 H2 H7). contradiction.
Qed.

(* Having done the hard work of showing the Cut-elimination algorithm
terminates, we now complete the reasoning for:
'if A is provable, it has a Cut-free proof' *)
(* *)

Definition cut_remove (alpha : ord) : Type := (forall (P : ptree) (A : formula) (d : nat),
P_proves P A (S d) alpha -> provable A d (ord_2_exp alpha)).

Lemma cut_elim_aux0 : forall (alpha : ord), nf alpha -> forall (P : ptree) (A : formula) (d : nat),
   P_proves P A (S d) alpha -> provable A d (ord_2_exp alpha).
Proof.
apply (transfinite_induction cut_remove).
intros. unfold cut_remove. destruct x as [| alpha1 n alpha2]. intros. apply (cut_elim_ord_Zero P). auto. case (ord_eqb (cons Zero 0 Zero) (cons alpha1 n alpha2)) eqn:O.
intros. apply ord_eqb_eq in O. destruct O. apply (cut_elim_ord_one P). auto. assert (ord_lt (cons Zero 0 Zero) (cons alpha1 n alpha2)).
{ destruct (ord_semiconnex (cons Zero 0 Zero) (cons alpha1 n alpha2)) as [O1 | [O1 | O1]]. auto. inversion O1; inversion H1. destruct O1. inversion O. }
intros P. induction P.
- intros. destruct X0 as [[[X1 X2] X3] X4]. simpl in X3,X4. destruct X2 as [H1 H2]. apply IHP. unfold P_proves. repeat split; simpl; auto. lia.
- intros. destruct X0 as [[[X1 X2] X3] X4]. simpl in X1,X3,X4. destruct X4. destruct X2 as [[H1 H2] H3]. unfold cut_remove in X.
  assert (P_proves P A (S d) (ptree_ord P)). { unfold P_proves. repeat split; simpl; auto. } destruct (X (ptree_ord P) (ptree_ord_nf _ H2) H1 P A d X0) as [P1 [[[HP1 HP2] HP3] HP4]].
  exists (ord_up (ord_2_exp o) P1). unfold P_proves. repeat split; simpl; auto. rewrite HP4. apply ord_2_exp_monot; auto. apply ptree_ord_nf. auto. apply nf_2_exp. auto.
- intros. destruct X0 as [[[X1 X2] X3] X4]. simpl in X1,X3,X4. destruct X4. destruct d. exists (ord_up (ord_2_exp Zero) (node f)). unfold P_proves. repeat split; simpl; auto. apply zero_lt. apply single_nf. apply zero_nf.
  exists (ord_up (ord_2_exp Zero) (deg_up (S d) (node f))). unfold P_proves. repeat split; simpl; auto. apply zero_lt. lia. apply single_nf. apply zero_nf.
- intros. destruct X0 as [[[X1 X2] X3] X4]. simpl in X1,X3,X4. destruct X4. destruct X2 as [[[H1 H2] H3] H4]. unfold cut_remove in X.
  assert (P_proves P (lor f f0) (S d) o). { unfold P_proves. repeat split; simpl; auto. lia. } pose (IHP _ _ X0). destruct p as [P1 [[[HP1 HP2] HP3] HP4]]. exists (exchange_ab f f0 (ptree_deg P1) (ptree_ord P1) P1). repeat split; simpl; auto.    
- intros. destruct X0 as [[[X1 X2] X3] X4]. simpl in X1,X3,X4. destruct X4. destruct X2 as [[[H1 H2] H3] H4]. unfold cut_remove in X.
  assert (P_proves P (lor (lor f f0) f1) (S d) o). { unfold P_proves. repeat split; simpl; auto. lia. } pose (IHP _ _ X0). destruct p as [P1 [[[HP1 HP2] HP3] HP4]]. exists (exchange_cab f f0 f1 (ptree_deg P1) (ptree_ord P1) P1). repeat split; simpl; auto.
- intros. destruct X0 as [[[X1 X2] X3] X4]. simpl in X1,X3,X4. destruct X4. destruct X2 as [[[H1 H2] H3] H4]. unfold cut_remove in X.
  assert (P_proves P (lor (lor f f0) f1) (S d) o). { unfold P_proves. repeat split; simpl; auto. lia. } pose (IHP _ _ X0). destruct p as [P1 [[[HP1 HP2] HP3] HP4]]. exists (exchange_abd f f0 f1 (ptree_deg P1) (ptree_ord P1) P1). repeat split; simpl; auto.    
- intros. destruct X0 as [[[X1 X2] X3] X4]. simpl in X1,X3,X4. destruct X4. destruct X2 as [[[H1 H2] H3] H4]. unfold cut_remove in X.
  assert (P_proves P (lor (lor (lor f f0) f1) f2) (S d) o). { unfold P_proves. repeat split; simpl; auto. lia. } pose (IHP _ _ X0). destruct p as [P1 [[[HP1 HP2] HP3] HP4]]. exists (exchange_cabd f f0 f1 f2 (ptree_deg P1) (ptree_ord P1) P1). repeat split; simpl; auto.    
- intros. destruct X0 as [[[X1 X2] X3] X4]. simpl in X1,X3,X4. destruct X4. destruct X2 as [[[H1 H2] H3] H4]. unfold cut_remove in X.
  assert (P_proves P (lor f f) (S d) o). { unfold P_proves. repeat split; simpl; auto. lia. } pose (IHP _ _ X0). destruct p as [P1 [[[HP1 HP2] HP3] HP4]]. exists (contraction_a f (ptree_deg P1) (ptree_ord P1) P1). repeat split; simpl; auto.    
- intros. destruct X0 as [[[X1 X2] X3] X4]. simpl in X1,X3,X4. destruct X4. destruct X2 as [[[H1 H2] H3] H4]. unfold cut_remove in X.
  assert (P_proves P (lor (lor f f) f0) (S d) o). { unfold P_proves. repeat split; simpl; auto. lia. } pose (IHP _ _ X0). destruct p as [P1 [[[HP1 HP2] HP3] HP4]]. exists (contraction_ad f f0 (ptree_deg P1) (ptree_ord P1) P1). repeat split; simpl; auto.
- intros. destruct X0 as [[[X1 X2] X3] X4]. simpl in X1,X3,X4. destruct X4. destruct X2 as [[[[H1 H2] H3] H4] H5]. unfold cut_remove in X.
  assert (P_proves P f0 (S d) o). { unfold P_proves. repeat split; simpl; auto. lia. } destruct (X _ (ord_nf_succ _ H) (ord_succ_monot _) _ _ _ X0) as [P1 [[[HP1 HP2] HP3] HP4]]. exists (ord_up (ord_2_exp (ord_succ o)) (weakening_ad f f0 (ptree_deg P1) (ptree_ord P1) P1)). repeat split; simpl; auto.
  rewrite HP4. apply ord_succ_lt_exp_succ. apply ord_nf_succ. auto. apply succ_gt_one_gt_zero. auto. apply nf_2_exp. auto.  
- intros. destruct X0 as [[[X1 X2] X3] X4]. simpl in X1,X3,X4. destruct X4. destruct X2 as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8]. unfold cut_remove in X.
  assert (P_proves P1 (neg f) (S d) o). { unfold P_proves. repeat split; simpl; auto. lia. }
  assert (nf o). { rewrite H7. apply ptree_ord_nf. auto. }
  assert (P_proves P2 (neg f0) (S d) o0). { unfold P_proves. repeat split; simpl; auto. lia. }
  assert (nf o0). { rewrite H8. apply ptree_ord_nf. auto. }
  destruct (X _ H9 (ord_max_succ_l _ _) _ _ _ X0) as [P6 [[[HP1 Hp2] HP3] HP4]].
  destruct (X _ H10 (ord_max_succ_r _ _) _ _ _ X2) as [P7 [[[HQ1 HQ2] HQ3] HQ4]].
  exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (demorgan_ab f f0 (ptree_deg P6) (ptree_deg P7) (ord_2_exp o) (ord_2_exp o0) P6 P7)). repeat split; simpl; auto.
  apply ord_max_exp_both; auto. apply nf_2_exp. auto. lia.
- intros. destruct X0 as [[[X1 X2] X3] X4]. simpl in X1,X3,X4. destruct X4. destruct X2 as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8]. unfold cut_remove in X.
  assert (P_proves P1 (lor (neg f) f1) (S d) o). { unfold P_proves. repeat split; simpl; auto. lia. }
  assert (nf o). { rewrite H7. apply ptree_ord_nf. auto. }
  assert (P_proves P2 (lor (neg f0) f1) (S d) o0). { unfold P_proves. repeat split; simpl; auto. lia. }
  assert (nf o0). { rewrite H8. apply ptree_ord_nf. auto. }
  destruct (X _ H9 (ord_max_succ_l _ _) _ _ _ X0) as [P6 [[[HP1 Hp2] HP3] HP4]].
  destruct (X _ H10 (ord_max_succ_r _ _) _ _ _ X2) as [P7 [[[HQ1 HQ2] HQ3] HQ4]].
  exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (demorgan_abd f f0 f1 (ptree_deg P6) (ptree_deg P7) (ord_2_exp o) (ord_2_exp o0) P6 P7)). repeat split; simpl; auto.
  apply ord_max_exp_both; auto. apply nf_2_exp. auto. lia.
- intros. destruct X0 as [[[X1 X2] X3] X4]. simpl in X1,X3,X4. destruct X4. destruct X2 as [[[H1 H2] H3] H4]. unfold cut_remove in X.
  assert (P_proves P f (S d) o). { unfold P_proves. repeat split; simpl; auto. lia. } destruct (X _ (ord_nf_succ _ H) (ord_succ_monot _) _ _ _ X0) as [P1 [[[HP1 HP2] HP3] HP4]]. exists (ord_up (ord_2_exp (ord_succ o)) (negation_a f (ptree_deg P1) (ptree_ord P1) P1)). repeat split; simpl; auto.
  rewrite HP4. apply ord_succ_lt_exp_succ. apply ord_nf_succ. auto. apply succ_gt_one_gt_zero. auto. apply nf_2_exp. auto. 
- intros. destruct X0 as [[[X1 X2] X3] X4]. simpl in X1,X3,X4. destruct X4. destruct X2 as [[[H1 H2] H3] H4]. unfold cut_remove in X.
  assert (P_proves P (lor f f0) (S d) o). { unfold P_proves. repeat split; simpl; auto. lia. } destruct (X _ (ord_nf_succ _ H) (ord_succ_monot _) _ _ _ X0) as [P1 [[[HP1 HP2] HP3] HP4]]. exists (ord_up (ord_2_exp (ord_succ o)) (negation_ad f f0 (ptree_deg P1) (ptree_ord P1) P1)). repeat split; simpl; auto.
  rewrite HP4. apply ord_succ_lt_exp_succ. apply ord_nf_succ. auto. apply succ_gt_one_gt_zero. auto. apply nf_2_exp. auto. 
- intros. destruct X0 as [[[X1 X2] X3] X4]. simpl in X1,X3,X4. destruct X4. destruct X2 as [[[H1 H2] H3] H4]. unfold cut_remove in X.
  assert (P_proves P (neg (substitution f n0 (projT1 c))) (S d) o). { unfold P_proves. repeat split; simpl; auto. lia. } destruct (X _ (ord_nf_succ _ H) (ord_succ_monot _) _ _ _ X0) as [P1 [[[HP1 HP2] HP3] HP4]]. exists (ord_up (ord_2_exp (ord_succ o)) (quantification_a f n0 c (ptree_deg P1) (ptree_ord P1) P1)). repeat split; simpl; auto.
  rewrite HP4. apply ord_succ_lt_exp_succ. apply ord_nf_succ. auto. apply succ_gt_one_gt_zero. auto. apply nf_2_exp. auto. 
- intros. destruct X0 as [[[X1 X2] X3] X4]. simpl in X1,X3,X4. destruct X4. destruct X2 as [[[H1 H2] H3] H4]. unfold cut_remove in X.
  assert (P_proves P (lor (neg (substitution f n0 (projT1 c))) f0) (S d) o). { unfold P_proves. repeat split; simpl; auto. lia. } destruct (X _ (ord_nf_succ _ H) (ord_succ_monot _) _ _ _ X0) as [P1 [[[HP1 HP2] HP3] HP4]]. exists (ord_up (ord_2_exp (ord_succ o)) (quantification_ad f f0 n0 c (ptree_deg P1) (ptree_ord P1) P1)). repeat split; simpl; auto.
  rewrite HP4. apply ord_succ_lt_exp_succ. apply ord_nf_succ. auto. apply succ_gt_one_gt_zero. auto. apply nf_2_exp. auto. 
- intros. rename X0 into IHP. destruct X1 as [[[X1 X2] X3] X4]. simpl in X1,X3,X4.
  rewrite <- X4 in *. unfold cut_remove in X. unfold valid in X2. fold valid in X2.
  assert (forall c, P_proves (p c) (substitution f n0 (projT1 c)) (S d) o).
  { intros. unfold P_proves. destruct (X2 c) as [[[Y1 Y2] Y3] Y4]. repeat split; simpl; auto. destruct Y4. lia. }
  destruct o. rewrite ord_eqb_refl in O. inversion O.
  exists (ord_up (ord_2_exp (ord_succ (cons o1 n2 o2))) (w_rule_a f n0 d (ord_2_exp (cons o1 n2 o2)) (fun m => projT1(X _ (ord_nf_succ _ H) (ord_succ_monot _) (p m) _ _ (X0 m))))). repeat split; simpl; auto.
  + apply ord_succ_lt_exp_succ. apply ord_nf_succ. auto. apply zero_lt.
  + destruct X as [P [[[HP1 HP2] HP3] HP4]]. simpl. auto.
  + destruct X as [P [[[HP1 HP2] HP3] HP4]]. simpl. auto.
  + destruct X as [P [[[HP1 HP2] HP3] HP4]]. simpl. auto.
  + destruct X as [P [[[HP1 HP2] HP3] HP4]]. simpl. auto.
  + apply nf_2_exp. auto.
- intros. rename X0 into IHP. destruct X1 as [[[X1 X2] X3] X4]. simpl in X1,X3,X4.
  rewrite <- X4 in *. unfold cut_remove in X. unfold valid in X2. fold valid in X2.
  assert (forall m, P_proves (p m) (lor (substitution f n0 (projT1 m)) f0) (S d) o).
  { intros. unfold P_proves. destruct (X2 m) as [[[Y1 Y2] Y3] Y4]. repeat split; simpl; auto. destruct Y4. lia. }
  destruct o. rewrite ord_eqb_refl in O. inversion O.
  exists (ord_up (ord_2_exp (ord_succ (cons o1 n2 o2))) (w_rule_ad f f0 n0 d (ord_2_exp (cons o1 n2 o2)) (fun m => projT1(X _ (ord_nf_succ _ H) (ord_succ_monot _) (p m) _ _ (X0 m))))). repeat split; simpl; auto.
  + apply ord_succ_lt_exp_succ. apply ord_nf_succ. auto. apply zero_lt.
  + destruct X as [P [[[HP1 HP2] HP3] HP4]]. simpl. auto.
  + destruct X as [P [[[HP1 HP2] HP3] HP4]]. simpl. auto.
  + destruct X as [P [[[HP1 HP2] HP3] HP4]]. simpl. auto.
  + destruct X as [P [[[HP1 HP2] HP3] HP4]]. simpl. auto.
  + apply nf_2_exp. auto.
- case (eq_nat (max (max n0 n1) (S (num_conn f0))) (S (num_conn f0))) eqn:E1.
  + intros. inversion X0 as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. destruct HP4. inversion HP2 as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8].
    assert (P_proves P2 (neg f0) n1 o0) as HP5. repeat split; auto. lia. assert (P_proves P1 (lor f f0) n0 o) as HP6. repeat split; auto. lia.
    unfold cut_remove in X.
    assert (forall y : ord, nf y -> ord_lt y (ord_succ (ord_max o o0)) -> forall (P : ptree) (A : formula) (d : nat), P_proves P A d y -> provable A (pred d) (ord_2_exp y)) as IHP_PRED.
    { intros. destruct d0.
      { simpl. exists (weak_ord_up P (ord_2_exp y)). unfold weak_ord_up. destruct X9 as [[[Z1 Z2] Z3] Z4]. case (ord_ltb (ptree_ord P) (ord_2_exp y)) eqn:Y.
        { repeat split; simpl; auto. apply ord_ltb_lt. auto. apply nf_2_exp. auto. }
        { repeat split; simpl; auto. destruct Z4. destruct (ord_2_exp_fp (ptree_ord P)).
          { apply ptree_ord_nf. auto. }
          { apply ord_lt_ltb in H3. rewrite Y in H3. inversion H3. }
          { rewrite H3. auto. } } }
      { simpl. apply (X _ H1 H2 P _ _ X9). } }
    assert (nf o). rewrite X7. apply ptree_ord_nf. auto.
    assert (nf o0). rewrite X8. apply ptree_ord_nf. auto.
    destruct (IHP_PRED _ H1 (ord_max_succ_l _ _) P1 _ _ HP6) as [PY [[[Y1 Y2] Y3] Y4]].
    destruct (IHP_PRED _ H2 (ord_max_succ_r _ _) P2 _ _ HP5) as [PZ [[[Z1 Z2] Z3] Z4]].
    assert (valid (cut_ca f f0 (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ)) as HYZ. repeat split; auto.
    assert (num_conn f0 <= d). lia.
    assert (ptree_deg PY <= d). lia.
    assert (ptree_deg PZ <= d). lia.
    destruct f0.
    * exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_elimination (cut_ca f (atom a) (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))). 
      case (ord_succ (ord_max (ord_2_exp o) (ord_2_exp o0))) eqn:I1. pose proof (ord_succ_non_Zero (ord_max (ord_2_exp o) (ord_2_exp o0))). rewrite I1 in H6. inversion H6. repeat split; auto.
      --  unfold ptree_formula. fold ptree_formula. rewrite cut_elimination_formula; auto.
      --  simpl. rewrite I1. case (correct_a a) eqn:C.
          ++  rewrite formula_sub_ptree_ord_neg; auto. rewrite Z4. apply ord_2_exp_monot; auto. apply ord_max_succ_r.
          ++  simpl. apply ord_2_exp_monot; auto. apply ord_max_succ_l.
      --  apply cut_elimination_valid; auto.
      --  apply nf_2_exp. auto.
      --  simpl. rewrite I1. case (correct_a a) eqn:C.
          { rewrite formula_sub_ptree_deg_neg; auto. }
          { simpl. lia. }
    * exists (weak_ord_up (cut_elimination (cut_ca f (neg f0) (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ)) (ord_2_exp (ord_succ (ord_max o o0)))).
      case (ord_succ (ord_max (ord_2_exp o) (ord_2_exp o0))) eqn:I1. pose proof (ord_succ_non_Zero (ord_max (ord_2_exp o) (ord_2_exp o0))). rewrite I1 in H6. inversion H6. repeat split; auto.
      --  rewrite weak_ord_formula. unfold ptree_formula. fold ptree_formula. rewrite cut_elimination_formula; auto.
      --  apply weak_ord_valid. apply nf_2_exp. auto. apply cut_elimination_valid. auto. 
      --  rewrite weak_ord_deg. simpl. rewrite I1. simpl in *. lia.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (cut_elimination (cut_ca f (neg f0) (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I2; auto.
          simpl. rewrite I1. simpl. destruct (ord_semiconnex_bool (ord_succ (ord_succ (ord_max (ord_2_exp o0) (ord_2_exp o)))) (ord_2_exp (ord_succ (ord_max o o0)))) as [I3 | [I3 |I3]].
          ++  simpl in I2. rewrite I1 in I2. simpl in I2. rewrite I3 in I2. inversion I2.
          ++  simpl in I2. rewrite I1 in I2. simpl in I2. rewrite ord_max_symm in I2. rewrite ord_max_exp_equiv in I2; auto. destruct (ord_max o o0) eqn:O2. inversion O. rewrite <- O2 in *.
              rewrite ord_max_exp_equiv; auto. assert (ord_lt Zero (ord_max o o0)). rewrite O2. apply zero_lt. 
              pose proof (dub_succ_exp_eq _ H6 (ord_max_nf _ _ H1 H2) I2). apply ord_eqb_eq in H7. rewrite (ord_max_symm o0). auto.
          ++  apply ord_eqb_eq in I3. auto.
    * exists (weak_ord_up (cut_elimination (cut_ca f (lor f0_1 f0_2) (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ)) (ord_2_exp (ord_succ (ord_max o o0)))).
      case (ord_succ (ord_max (ord_2_exp o) (ord_2_exp o0))) eqn:I1. pose proof (ord_succ_non_Zero (ord_max (ord_2_exp o) (ord_2_exp o0))). rewrite I1 in H6. inversion H6. repeat split; auto.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (cut_elimination (cut_ca f (lor f0_1 f0_2) (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I2.
          ++  unfold ptree_formula. fold ptree_formula. rewrite cut_elimination_formula; auto.
          ++  unfold ptree_formula. fold ptree_formula. rewrite cut_elimination_formula; auto.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (cut_elimination (cut_ca f (lor f0_1 f0_2) (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I2.
          ++  repeat split; auto.
              **  apply ord_ltb_lt. auto.
              **  apply cut_elimination_valid; auto.
              **  apply nf_2_exp. auto.
          ++  apply cut_elimination_valid; auto.
      --  simpl. rewrite I1. unfold weak_ord_up. case (ord_ltb (ptree_ord (cut_ca f f0_1 (max (max (ptree_deg PY) (ptree_deg PZ)) (S (num_conn f0_2))) (ptree_deg PZ) (cons o1_1 n2 o1_2) (ord_2_exp o0) (cut_ca (lor f f0_1) f0_2 (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) (associativity_2' PY) (demorgan2_sub_ptree PZ f0_1 f0_2 (1))) (demorgan1_sub_ptree PZ f0_1 f0_2 (1)))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I2.
          ++ simpl in *. lia.
          ++ simpl in *. lia.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (cut_elimination (cut_ca f (lor f0_1 f0_2) (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I2; auto.
          simpl. rewrite I1. unfold ptree_ord. rewrite <- I1.
          simpl in I2. rewrite I1 in I2. unfold ptree_ord in I2. rewrite <- I1 in I2.
          rewrite ord_max_lem2. rewrite ord_max_lem2 in I2.
          ++  rewrite ord_max_exp_equiv in *; auto. apply ord_eqb_eq. assert (ord_lt Zero (ord_max o o0)). destruct (ord_max o o0). inversion H0; inversion H7. apply zero_lt. apply (dub_succ_exp_eq _ H6 (ord_nf_succ _ H) I2). 
          ++  apply ltb_asymm. apply ord_lt_ltb. apply ord_max_succ_r.
          ++  apply ltb_asymm. apply ord_lt_ltb. apply ord_max_succ_r.
    * assert (P_proves PY (lor f (univ n2 f0)) (ptree_deg PY) (ord_2_exp o)) as PY1. repeat split; auto.
      assert (max (ptree_deg PY) (ptree_deg PZ) < num_conn f0 + 2).
      { simpl in *. apply nat_eq_decid in E1. lia. }
      assert (max (max (ptree_deg PY) (ptree_deg PZ)) (num_conn f0 + 1) <= d).
      { simpl in *. apply nat_eq_decid in E1. lia. }
      exists (weak_ord_up (neg_w_rule_sub_ptree PZ _ _ _ _ _ _ PY1 (1)) (ord_2_exp (ord_succ (ord_max o o0)))). repeat split; auto.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (neg_w_rule_sub_ptree PZ PY f0 f n2 (ptree_deg PY) (ord_2_exp o) PY1 (1))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I1.
          ++  simpl. rewrite neg_w_rule_ptree_formula; auto. rewrite Z1. unfold neg_w_rule_sub_formula. simpl. rewrite eq_nat_refl. rewrite eq_f_refl. auto.
          ++  rewrite neg_w_rule_ptree_formula; auto. rewrite Z1. unfold neg_w_rule_sub_formula. simpl. rewrite eq_nat_refl. rewrite eq_f_refl. auto.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (neg_w_rule_sub_ptree PZ PY f0 f n2 (ptree_deg PY) (ord_2_exp o) PY1 (1))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I1.
          ++  repeat split. apply ord_ltb_lt. auto. apply neg_w_rule_valid; auto.
              { pose proof (provable_closed' PY _ Y2 Y1). simpl in H7. destruct (and_bool_prop _ _ H8). auto. }
              { rewrite Z1. auto. }
              { apply nf_2_exp. auto. }
          ++  apply neg_w_rule_valid; auto.
              { pose proof (provable_closed' PY _ Y2 Y1). simpl in H7. destruct (and_bool_prop _ _ H8). auto. }
              { rewrite Z1. auto. }
      --  pose proof (neg_w_rule_ptree_deg PZ _ _ _ _ _ _ PY1 Z2 H6 (1)).
          unfold weak_ord_up. case (ord_ltb (ptree_ord (neg_w_rule_sub_ptree PZ PY f0 f n2 (ptree_deg PY) (ord_2_exp o) PY1 (1))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I1; simpl; lia.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (neg_w_rule_sub_ptree PZ PY f0 f n2 (ptree_deg PY) (ord_2_exp o) PY1 (1))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I1; simpl; auto. 
          pose proof (neg_w_rule_ptree_ord PZ _ _ _ _ _ _ PY1 Z2 (1)).
          rewrite Z4 in H8.
          pose proof (ord_trans_inv _ _ _ (ord_add_exp_le_exp_max _ _ H1 H2) H8) as I2.
          destruct (ord_semiconnex_bool (ord_2_exp (ord_succ (ord_max o o0))) (ptree_ord (neg_w_rule_sub_ptree PZ PY f0 f n2 (ptree_deg PY) (ord_2_exp o) PY1 (1)))) as [I3 | [I3 | I3]].
          ++  rewrite I3 in I2. inversion I2.
          ++  rewrite I3 in I1. inversion I1.
          ++  apply ord_eqb_eq in I3. auto. 
    + assert ((S (num_conn f0)) < (max n0 n1)) as E2. rewrite eq_nat_symm in E1. rewrite (nat_eq_decid _ _ (nat_max_right_not _ _ E1)). apply (max_lem2 _ _ E1).
      intros. destruct X0 as [[[X1 X2] X3] X4]. simpl in X1,X3,X4. destruct X4. destruct X2 as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8]. unfold cut_remove in X. case (eq_nat (max (max n0 n1) (S (num_conn f0))) (S d)) eqn:E.
      * assert ((S (num_conn f0)) < (max n0 n1)). rewrite eq_nat_symm in E1. rewrite (nat_eq_decid _ _ (nat_max_right_not _ _ E1)). apply (max_lem2 _ _ E1).
        apply nat_eq_decid in E. case (lt_nat n0 n1) eqn:Y.
        --  rewrite (max_split1 _ _ Y) in E. symmetry in E. destruct E. assert (P_proves P2 (neg f0) (S d) o0). { unfold P_proves. repeat split; simpl; auto. lia. } assert (nf o0). rewrite H8. apply ptree_ord_nf. auto.
            destruct (X _ H10 (ord_max_succ_r _ _) _ _ _ X0) as [P7 [[[HP1 HP2] HP3] HP4]]. exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_ca f f0 n0 (ptree_deg P7) o (ord_2_exp o0) P1 P7)). repeat split; simpl; auto.
            apply ord_max_exp_r; auto. rewrite H7. apply ptree_ord_nf. auto. apply nf_2_exp. auto. apply lt_nat_decid in Y. lia.
        --  case (lt_nat n1 n0) eqn:Y1.
            ++  rewrite (max_split2 _ _ Y1) in E. symmetry in E. destruct E. assert (P_proves P1 (lor f f0) (S d) o). { unfold P_proves. repeat split; simpl; auto. lia. } assert (nf o). rewrite H7. apply ptree_ord_nf. auto.
                destruct (X _ H10 (ord_max_succ_l _ _) _ _ _ X0) as [P6 [[[HP1 HP2] HP3] HP4]]. exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_ca f f0 (ptree_deg P6) n1 (ord_2_exp o) o0 P6 P2)). repeat split; simpl; auto.
                apply ord_max_exp_l; auto. rewrite H8. apply ptree_ord_nf. auto. apply nf_2_exp. auto. apply lt_nat_decid in Y1. lia.
            ++  assert (n0 = n1). destruct (nat_semiconnex n0 n1) as [Y2 | [Y2 | Y2]]; try apply lt_nat_decid_conv in Y2. rewrite Y2 in Y. inversion Y. rewrite Y2 in Y1. inversion Y1. auto. destruct H10. rewrite max_n_n in E. symmetry in E. destruct E.
                assert (P_proves P1 (lor f f0) (S d) o). { unfold P_proves. repeat split; simpl; auto. lia. } assert (nf o). rewrite H7. apply ptree_ord_nf. auto.
                assert (P_proves P2 (neg f0) (S d) o0). { unfold P_proves. repeat split; simpl; auto. lia. } assert (nf o0). rewrite H8. apply ptree_ord_nf. auto.
                destruct (X _ H10 (ord_max_succ_l _ _) _ _ _ X0) as [P6 [[[HP1 Hp2] HP3] HP4]]. destruct (X _ H11 (ord_max_succ_r _ _) _ _ _ X2) as [P7 [[[HQ1 HQ2] HQ3] HQ4]].
                exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_ca f f0 (ptree_deg P6) (ptree_deg P7) (ord_2_exp o) (ord_2_exp o0) P6 P7)). repeat split; simpl; auto.
                apply ord_max_exp_both; auto. apply nf_2_exp. auto. lia.
      * assert (d >= max (max n0 n1) (S (num_conn f0))). { inversion X3. destruct H10. rewrite eq_nat_refl in E. inversion E. lia. } exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_ca f f0 n0 n1 o o0 P1 P2)). repeat split; simpl; auto. apply ord_succ_not_exp_fp. auto. apply nf_2_exp. auto.
- case (eq_nat (max (max n0 n1) (S (num_conn f))) (S (num_conn f))) eqn:E1.
  + intros. inversion X0 as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. destruct HP1. destruct HP4. inversion HP2 as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8].
    assert (P_proves P2 (lor (neg f) f0) n1 o0) as HP5. repeat split; auto. lia. assert (P_proves P1 f n0 o) as HP6. repeat split; auto. lia.
    unfold cut_remove in X.
    assert (forall y : ord, nf y -> ord_lt y (ord_succ (ord_max o o0)) -> forall (P : ptree) (A : formula) (d : nat), P_proves P A d y -> provable A (pred d) (ord_2_exp y)) as IHP_PRED.
    { intros. destruct d0.
      { simpl. exists (weak_ord_up P (ord_2_exp y)). unfold weak_ord_up. destruct X9 as [[[Z1 Z2] Z3] Z4]. case (ord_ltb (ptree_ord P) (ord_2_exp y)) eqn:Y.
        { repeat split; simpl; auto. apply ord_ltb_lt. auto. apply nf_2_exp. auto. }
        { repeat split; simpl; auto. destruct Z4. destruct (ord_2_exp_fp (ptree_ord P)).
          { apply ptree_ord_nf. auto. }
          { apply ord_lt_ltb in H3. rewrite Y in H3. inversion H3. }
          { rewrite H3. auto. } } }
      { simpl. apply (X _ H1 (lt_trans _ _ _ H2 (ord_succ_monot _)) P _ _ X9). } }
    assert (nf o). rewrite X7. apply ptree_ord_nf. auto.
    assert (nf o0). rewrite X8. apply ptree_ord_nf. auto.
    destruct (IHP_PRED _ H1 (ord_max_succ_l _ _) P1 _ _ HP6) as [PY [[[Y1 Y2] Y3] Y4]].
    destruct (IHP_PRED _ H2 (ord_max_succ_r _ _) P2 _ _ HP5) as [PZ [[[Z1 Z2] Z3] Z4]].
    assert (valid (cut_ad f f0 (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ)) as HYZ. repeat split; auto.
    assert (num_conn f <= d). lia.
    assert (ptree_deg PY <= d). lia.
    assert (ptree_deg PZ <= d). lia.
    destruct f.
    * exists (ord_up (ord_2_exp (ord_succ (ord_succ (ord_max o o0)))) (cut_elimination (cut_ad (atom a) f0 (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))). 
      case (ord_succ (ord_succ (ord_max (ord_2_exp o) (ord_2_exp o0)))) eqn:I1. pose proof (ord_succ_non_Zero (ord_succ (ord_max (ord_2_exp o) (ord_2_exp o0)))). rewrite I1 in H6. inversion H6. repeat split; auto.
      --  unfold ptree_formula. fold ptree_formula. rewrite cut_elimination_formula; auto.
      --  simpl. rewrite I1. case (correct_a a) eqn:C.
          ++  simpl. apply ord_2_exp_monot; auto. apply (lt_trans _ _ _ (ord_succ_monot _)). apply ord_lt_succ. apply ord_max_succ_r. 
          ++  rewrite formula_sub_ptree_ord_atom; auto. rewrite Y4. apply ord_2_exp_monot; auto. apply (lt_trans _ _ _ (ord_succ_monot _)). apply ord_lt_succ. apply ord_max_succ_l.
      --  apply cut_elimination_valid; auto.
      --  apply nf_2_exp. repeat apply ord_succ_nf. apply ord_max_nf; auto.
      --  simpl. rewrite I1. case (correct_a a) eqn:C.
          { simpl. lia. }
          { rewrite formula_sub_ptree_deg_atom; auto. }
    * exists (ord_up (ord_2_exp (ord_succ (ord_succ (ord_max o o0)))) (cut_elimination (cut_ad (neg f) f0 (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))).
      case (ord_succ (ord_succ (ord_max (ord_2_exp o) (ord_2_exp o0)))) eqn:I1. pose proof (ord_succ_non_Zero (ord_succ (ord_max (ord_2_exp o) (ord_2_exp o0)))). rewrite I1 in H6. inversion H6. repeat split; auto.
      --  unfold ptree_formula. fold ptree_formula. rewrite cut_elimination_formula; auto.
      --  simpl. rewrite I1. simpl. rewrite ord_max_exp_equiv; auto. rewrite ord_max_symm. case (ord_max o o0) eqn:Y. simpl. apply coeff_lt. lia. refine (lt_trans _ _ _ (ord_succ_lt_exp_succ _ _ _) _); try rewrite <- Y; try apply ord_max_nf; auto. rewrite Y. apply zero_lt. apply ord_2_exp_monot; try repeat apply ord_succ_nf; try apply ord_max_nf; auto. apply ord_succ_monot.
      --  apply cut_elimination_valid; auto.
      --  apply nf_2_exp. auto.
      --  simpl. rewrite I1. simpl in *. lia.
    * exists (weak_ord_up (cut_elimination (cut_ad (lor f1 f2) f0 (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ)) (ord_2_exp (ord_succ (ord_succ (ord_max o o0))))).
      case (ord_succ (ord_succ (ord_max (ord_2_exp o) (ord_2_exp o0)))) eqn:I1. pose proof (ord_succ_non_Zero (ord_succ (ord_max (ord_2_exp o) (ord_2_exp o0)))). rewrite I1 in H6. inversion H6. repeat split; auto.
      --  rewrite weak_ord_formula. unfold ptree_formula. fold ptree_formula. rewrite cut_elimination_formula; auto.
      --  apply weak_ord_valid.
          ++  apply nf_2_exp. repeat apply ord_succ_nf. apply ord_max_nf; auto.
          ++  apply cut_elimination_valid; auto.
      --  rewrite weak_ord_deg. simpl in *. rewrite I1. simpl. lia.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (cut_elimination (cut_ad (lor f1 f2) f0 (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))) (ord_2_exp (ord_succ (ord_succ (ord_max o o0))))) eqn:I2; auto.
          simpl. rewrite I1. unfold ptree_ord. rewrite <- I1.
          simpl in I2. rewrite I1 in I2. unfold ptree_ord in I2. rewrite <- I1 in I2.
          rewrite ord_max_exp_equiv in *; auto. apply ord_eqb_eq. destruct (ord_max o o0). simpl in *. inversion I2. rewrite (ord_lt_ltb _ _ (plus_two_lt_times_four _ (ord_nf_succ _ (ord_nf_succ _ H)) (zero_lt _ _ _))) in I2. inversion I2.
    * assert (P_proves (weakening_ad f0 (univ n2 f) (ptree_deg PY) (ord_2_exp o) PY) (lor f0 (univ n2 f)) (ptree_deg PY) (ord_succ (ord_2_exp o))) as PY1. repeat split; simpl; auto. pose proof (provable_closed' _ _ Z2 Z1). simpl in H6. destruct (and_bool_prop _ _ H6). apply H8.
      assert (max (ptree_deg PY) (ptree_deg PZ) < num_conn f + 2).
      { simpl in *. apply nat_eq_decid in E1. lia. }
      assert (max (max (ptree_deg PY) (ptree_deg PZ)) (num_conn f + 1) <= d).
      { simpl in *. apply nat_eq_decid in E1. lia. }
      exists (weak_ord_up (contraction_a f0 (ptree_deg (neg_w_rule_sub_ptree PZ _ _ _ _ _ _ PY1 (lor_ind (1) (non_target f0)))) (ord_add (ord_succ (ord_2_exp o)) (ord_2_exp o0)) (weak_ord_up (neg_w_rule_sub_ptree PZ _ _ _ _ _ _ PY1 (lor_ind (1) (non_target f0))) (ord_add (ord_succ (ord_2_exp o)) (ord_2_exp o0)))) (ord_2_exp (ord_succ (ord_succ (ord_max o o0))))). repeat split; auto.
      --  rewrite weak_ord_formula. auto.
      --  apply weak_ord_valid. apply nf_2_exp. auto. repeat split; auto.
          ++  rewrite weak_ord_formula. rewrite neg_w_rule_ptree_formula; auto. unfold neg_w_rule_sub_formula. rewrite Z1. simpl. rewrite non_target_fit. rewrite eq_nat_refl. rewrite eq_f_refl. simpl. rewrite non_target_sub'. auto.
          ++  apply weak_ord_valid. apply nf_add; try apply ord_succ_nf; apply nf_2_exp; auto. apply neg_w_rule_valid; auto. pose proof (provable_closed'  _ _ Z2 Z1). destruct (and_bool_prop _ _ H8). auto. rewrite Z1. simpl. apply non_target_fit.
          ++  rewrite weak_ord_deg. auto.
          ++  unfold weak_ord_up. case (ord_ltb (ptree_ord (neg_w_rule_sub_ptree PZ (weakening_ad f0 (univ n2 f) (ptree_deg PY) (ord_2_exp o) PY) f f0 n2 (ptree_deg PY) (ord_succ (ord_2_exp o)) PY1 (lor_ind (1) (non_target f0)))) (ord_add (ord_succ (ord_2_exp o)) (ord_2_exp o0))) eqn:I1.
              **  simpl. auto.
              **  pose proof (neg_w_rule_ptree_ord PZ _ _ _ _ _ _ PY1 Z2 (lor_ind (1) (non_target f0))). destruct (ord_semiconnex_bool (ord_add (ord_succ (ord_2_exp o)) (ptree_ord PZ)) (ptree_ord (neg_w_rule_sub_ptree PZ (weakening_ad f0 (univ n2 f) (ptree_deg PY) (ord_2_exp o) PY) f f0 n2 (ptree_deg PY) (ord_succ (ord_2_exp o)) PY1 (lor_ind (1) (non_target f0))))) as [I2 | [I2 | I2]]; rewrite Z4 in *.
                  { rewrite I2 in H8. inversion H8. }
                  { rewrite I2 in I1. inversion I1. }
                  { apply ord_eqb_eq in I2. rewrite I2. auto. }
      --  rewrite weak_ord_deg. simpl. pose proof (neg_w_rule_ptree_deg PZ _ _ _ _ _ _ PY1 Z2 H6 (lor_ind (1) (non_target f0))). lia.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (contraction_a f0 (ptree_deg (neg_w_rule_sub_ptree PZ (weakening_ad f0 (univ n2 f) (ptree_deg PY) (ord_2_exp o) PY) f f0 n2 (ptree_deg PY) (ord_succ (ord_2_exp o)) PY1 (lor_ind (1) (non_target f0)))) (ord_add (ord_succ (ord_2_exp o)) (ord_2_exp o0)) ((weak_ord_up (neg_w_rule_sub_ptree PZ (weakening_ad f0 (univ n2 f) (ptree_deg PY) (ord_2_exp o) PY) f f0 n2 (ptree_deg PY) (ord_succ (ord_2_exp o)) PY1 (lor_ind (1) (non_target f0)))) (ord_add (ord_succ (ord_2_exp o)) (ord_2_exp o0))))) (ord_2_exp (ord_succ (ord_succ (ord_max o o0))))) eqn:I1; unfold weak_ord_up; unfold weak_ord_up in I1; try rewrite I1; auto.
          simpl in *. rewrite ord_2_exp_succ_mult in I1; try apply ord_succ_nf; try apply ord_max_nf; auto. rewrite ord_2_exp_succ_mult in I1; try apply ord_max_nf; auto. rewrite times_four_lt in I1; auto. inversion I1.
    + assert ((S (num_conn f)) < (max n0 n1)) as E2. rewrite eq_nat_symm in E1. rewrite (nat_eq_decid _ _ (nat_max_right_not _ _ E1)). apply (max_lem2 _ _ E1).
      intros. destruct X0 as [[[X1 X2] X3] X4]. simpl in X1,X3,X4. destruct X4. destruct X2 as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8]. unfold cut_remove in X. case (eq_nat (max (max n0 n1) (S (num_conn f))) (S d)) eqn:E.
      * assert ((S (num_conn f)) < (max n0 n1)). rewrite eq_nat_symm in E1. rewrite (nat_eq_decid _ _ (nat_max_right_not _ _ E1)). lia.
        apply nat_eq_decid in E. case (lt_nat n0 n1) eqn:Y.
        --  rewrite (max_split1 _ _ Y) in E. symmetry in E. destruct E. assert (P_proves P2 (lor (neg f) f0) (S d) o0). { unfold P_proves. repeat split; simpl; auto. lia. } assert (nf o0). rewrite H8. apply ptree_ord_nf. auto.
            destruct (X _ H10 (lt_trans _ _ _ (ord_max_succ_r _ _) (ord_succ_monot _)) _ _ _ X0) as [P7 [[[HP1 HP2] HP3] HP4]]. exists (ord_up (ord_2_exp (ord_succ (ord_succ (ord_max o o0)))) (cut_ad f f0 n0 (ptree_deg P7) o (ord_2_exp o0) P1 P7)). repeat split; simpl; auto.
            ++  destruct (ord_max o o0) eqn:O2.
                **  symmetry in O2. destruct (ord_max_0 _ _ O2). destruct H11,H12. simpl. apply coeff_lt. lia.
                **  rewrite <- O2. refine (lt_trans _ _ _ _ (ord_succ_lt_exp_succ _ _ _)). apply ord_lt_succ. apply ord_max_exp_r; auto. rewrite H7. apply ptree_ord_nf. auto. rewrite O2. simpl. destruct o1_1. apply coeff_lt. lia. apply head_lt. apply zero_lt. apply ord_succ_nf. rewrite H7,H8. apply ord_max_nf; apply ptree_ord_nf; auto. destruct (ord_max o o0); try destruct o1_3; apply zero_lt. 
            ++  apply nf_2_exp; auto.
            ++  apply lt_nat_decid in Y. simpl in *. lia.
        --  case (lt_nat n1 n0) eqn:Y1.
            ++  rewrite (max_split2 _ _ Y1) in E. symmetry in E. destruct E. assert (P_proves P1 f (S d) o). { unfold P_proves. repeat split; simpl; auto. lia. } assert (nf o). rewrite H7. apply ptree_ord_nf. auto.
                destruct (X _ H10 (lt_trans _ _ _ (ord_max_succ_l _ _) (ord_succ_monot _)) _ _ _ X0) as [P6 [[[HP1 HP2] HP3] HP4]]. exists (ord_up (ord_2_exp (ord_succ (ord_succ (ord_max o o0)))) (cut_ad f f0 (ptree_deg P6) n1 (ord_2_exp o) o0 P6 P2)). repeat split; simpl; auto.
                **  destruct (ord_max o o0) eqn:O2.
                    { symmetry in O2. destruct (ord_max_0 _ _ O2). destruct H11,H12. simpl. apply coeff_lt. lia. }
                    { rewrite <- O2. refine (lt_trans _ _ _ _ (ord_succ_lt_exp_succ _ _ _)). apply ord_lt_succ. apply ord_max_exp_l; auto. rewrite H8. apply ptree_ord_nf. auto. rewrite O2. simpl. destruct o1_1. apply coeff_lt. lia. apply head_lt. apply zero_lt. apply ord_succ_nf. rewrite H7,H8. apply ord_max_nf; apply ptree_ord_nf; auto. destruct (ord_max o o0); try destruct o1_3; apply zero_lt. }
                ** apply nf_2_exp. auto.
                **  apply lt_nat_decid in Y1. lia.
            ++  assert (n0 = n1). destruct (nat_semiconnex n0 n1) as [Y2 | [Y2 | Y2]]; try apply lt_nat_decid_conv in Y2. rewrite Y2 in Y. inversion Y. rewrite Y2 in Y1. inversion Y1. auto. destruct H10. rewrite max_n_n in E. symmetry in E. destruct E.
                assert (P_proves P1 f (S d) o). { unfold P_proves. repeat split; simpl; auto. lia. } assert (nf o). rewrite H7. apply ptree_ord_nf. auto.
                assert (P_proves P2 (lor (neg f) f0) (S d) o0). { unfold P_proves. repeat split; simpl; auto. lia. } assert (nf o0). rewrite H8. apply ptree_ord_nf. auto.
                destruct (X _ H10 (lt_trans _ _ _ (ord_max_succ_l _ _) (ord_succ_monot _)) _ _ _ X0) as [P6 [[[HP1 Hp2] HP3] HP4]]. destruct (X _ H11 (lt_trans _ _ _ (ord_max_succ_r _ _) (ord_succ_monot _)) _ _ _ X2) as [P7 [[[HQ1 HQ2] HQ3] HQ4]].
                exists (ord_up (ord_2_exp (ord_succ (ord_succ (ord_max o o0)))) (cut_ad f f0 (ptree_deg P6) (ptree_deg P7) (ord_2_exp o) (ord_2_exp o0) P6 P7)). repeat split; simpl; auto.
                **  rewrite ord_max_exp_equiv; auto. destruct (ord_max o o0) eqn:O2. simpl. apply coeff_lt. lia. rewrite <- O2. refine (lt_trans _ _ _ _ (ord_succ_lt_exp_succ _ _ _)). apply ord_lt_succ. apply ord_succ_lt_exp_succ. apply ord_max_nf; auto. rewrite O2. apply zero_lt. apply ord_succ_nf; apply ord_max_nf; auto. destruct (ord_max o o0); try destruct o1_3; apply zero_lt.
                **  apply nf_2_exp. auto.
                **  lia.
      * assert (d >= max (max n0 n1) (S (num_conn f))). { inversion X3. destruct H10. rewrite eq_nat_refl in E. inversion E. lia. } exists (ord_up (ord_2_exp (ord_succ (ord_succ (ord_max o o0)))) (cut_ad f f0 n0 n1 o o0 P1 P2)). repeat split; simpl; auto. apply ord_succ_not_exp_fp. auto. apply nf_2_exp. auto.
    
- case (eq_nat (max (max n0 n1) (S (num_conn f0))) (S (num_conn f0))) eqn:E1.
  + intros. inversion X0 as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. destruct HP4. inversion HP2 as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8].
    assert (P_proves P2 (lor(neg f0) f1) n1 o0) as HP5. repeat split; auto. lia. assert (P_proves P1 (lor f f0) n0 o) as HP6. repeat split; auto. lia.
    unfold cut_remove in X.
    assert (forall y : ord, nf y -> ord_lt y (ord_succ (ord_max o o0)) -> forall (P : ptree) (A : formula) (d : nat), P_proves P A d y -> provable A (pred d) (ord_2_exp y)) as IHP_PRED.
    { intros. destruct d0.
      { simpl. exists (weak_ord_up P (ord_2_exp y)). unfold weak_ord_up. destruct X9 as [[[Z1 Z2] Z3] Z4]. case (ord_ltb (ptree_ord P) (ord_2_exp y)) eqn:Y.
        { repeat split; simpl; auto. apply ord_ltb_lt. auto. apply nf_2_exp. auto. }
        { repeat split; simpl; auto. destruct Z4. destruct (ord_2_exp_fp (ptree_ord P)).
          { apply ptree_ord_nf. auto. }
          { apply ord_lt_ltb in H3. rewrite Y in H3. inversion H3. }
          { rewrite H3. auto. } } }
      { simpl. apply (X _ H1 H2 P _ _ X9). } }
    assert (nf o). rewrite X7. apply ptree_ord_nf. auto.
    assert (nf o0). rewrite X8. apply ptree_ord_nf. auto.
    destruct (IHP_PRED _ H1 (ord_max_succ_l _ _) P1 _ _ HP6) as [PY [[[Y1 Y2] Y3] Y4]].
    destruct (IHP_PRED _ H2 (ord_max_succ_r _ _) P2 _ _ HP5) as [PZ [[[Z1 Z2] Z3] Z4]].
    assert (valid (cut_cad f f0 f1 (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ)) as HYZ. repeat split; auto.
    assert (num_conn f0 <= d). lia.
    assert (ptree_deg PY <= d). lia.
    assert (ptree_deg PZ <= d). lia.
    destruct f0.
    * exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_elimination (cut_cad f (atom a) f1 (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))). 
      case (ord_succ (ord_max (ord_2_exp o) (ord_2_exp o0))) eqn:I1. pose proof (ord_succ_non_Zero (ord_max (ord_2_exp o) (ord_2_exp o0))). rewrite I1 in H6. inversion H6. repeat split; auto.
      --  unfold ptree_formula. fold ptree_formula. rewrite cut_elimination_formula; auto.
      --  simpl. rewrite I1. case (correct_a a) eqn:C.
          ++  simpl. apply ord_exp_succ_shuffle; auto. destruct (ord_max o o0). inversion O. apply zero_lt.
          ++  simpl. rewrite ord_max_symm. apply ord_exp_succ_shuffle; auto. rewrite ord_max_symm. destruct (ord_max o o0). inversion O. apply zero_lt.
      --  apply cut_elimination_valid; auto.
      --  apply nf_2_exp. auto.
      --  simpl. rewrite I1. case (correct_a a) eqn:C.
          { simpl. auto. }
          { simpl. lia. }
    * exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_elimination (cut_cad f (neg f0) f1 (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))).
      case (ord_succ (ord_max (ord_2_exp o) (ord_2_exp o0))) eqn:I1. pose proof (ord_succ_non_Zero (ord_max (ord_2_exp o) (ord_2_exp o0))). rewrite I1 in H6. inversion H6. repeat split; auto.
      --  unfold ptree_formula. fold ptree_formula. rewrite cut_elimination_formula; auto.
      --  simpl. rewrite I1. case (eq_nat (max (max (ptree_deg PZ) (ptree_deg PY)) (S (num_conn f0))) (S (num_conn f0))); simpl; rewrite <- I1; rewrite ord_max_exp_equiv; auto; apply ord_succ_lt_exp_succ; try apply ord_nf_succ; auto; destruct (ord_max o o0); inversion O; apply zero_lt.
      --  apply cut_elimination_valid; auto.
      --  apply nf_2_exp. auto.
      --  simpl. rewrite I1. simpl in *. lia.
    * exists (weak_ord_up (cut_elimination (cut_cad f (lor f0_1 f0_2) f1 (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ)) (ord_2_exp (ord_succ (ord_max o o0)))).
      case (ord_succ (ord_max (ord_2_exp o) (ord_2_exp o0))) eqn:I1. pose proof (ord_succ_non_Zero (ord_max (ord_2_exp o) (ord_2_exp o0))). rewrite I1 in H6. inversion H6. repeat split; auto.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (cut_elimination (cut_cad f (lor f0_1 f0_2) f1 (ptree_deg PY)  (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I2.
          ++  unfold ptree_formula. fold ptree_formula. rewrite cut_elimination_formula; auto.
          ++  unfold ptree_formula. fold ptree_formula. rewrite cut_elimination_formula; auto.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (cut_elimination (cut_cad f (lor f0_1 f0_2) f1 (ptree_deg PY)  (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I2.
          ++  repeat split; auto.
              **  apply ord_ltb_lt. auto.
              **  apply cut_elimination_valid; auto.
              **  apply nf_2_exp. auto.
          ++  apply cut_elimination_valid; auto.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (cut_elimination (cut_cad f (lor f0_1 f0_2) f1 (ptree_deg PY)  (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I2.
          ++ simpl in *. rewrite I1. unfold contraction_help. unfold ptree_formula. rewrite eq_f_refl. unfold ptree_deg. fold ptree_deg. simpl in *. lia.
          ++ simpl in *. rewrite I1. unfold contraction_help. unfold ptree_formula. rewrite eq_f_refl. unfold ptree_deg. fold ptree_deg. simpl in *. lia.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (cut_elimination (cut_cad f (lor f0_1 f0_2) f1 (ptree_deg PY)  (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I2; auto.
          simpl. rewrite I1. unfold contraction_help. unfold ptree_formula. rewrite eq_f_refl. unfold ptree_ord. rewrite <- I1.
          simpl in I2. rewrite I1 in I2. unfold contraction_help in I2. unfold ptree_formula in I2. rewrite eq_f_refl in I2. unfold ptree_ord in I2. rewrite <- I1 in I2.
          rewrite ord_max_lem2. rewrite ord_max_lem2 in I2.
          ++  rewrite ord_max_exp_equiv in *; auto. apply ord_eqb_eq. assert (ord_lt Zero (ord_max o o0)). destruct (ord_max o o0). inversion H0; inversion H7. apply zero_lt. apply (dub_succ_exp_eq _ H6 (ord_nf_succ _ H) I2). 
          ++  apply ltb_asymm. apply ord_lt_ltb. apply ord_max_succ_r.
          ++  apply ltb_asymm. apply ord_lt_ltb. apply ord_max_succ_r.
    * assert (P_proves PY (lor f (univ n2 f0)) (ptree_deg PY) (ord_2_exp o)) as PY1. repeat split; auto.
      assert (max (ptree_deg PY) (ptree_deg PZ) < num_conn f0 + 2).
      { simpl in *. apply nat_eq_decid in E1. lia. }
      assert (max (max (ptree_deg PY) (ptree_deg PZ)) (num_conn f0 + 1) <= d).
      { simpl in *. apply nat_eq_decid in E1. lia. }
      exists (weak_ord_up (neg_w_rule_sub_ptree PZ _ _ _ _ _ _ PY1 (lor_ind (1) (non_target f1))) (ord_2_exp (ord_succ (ord_max o o0)))). repeat split; auto.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (neg_w_rule_sub_ptree PZ PY f0 f n2 (ptree_deg PY) (ord_2_exp o) PY1 (lor_ind (1) (non_target f1)))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I1.
          ++  simpl. rewrite neg_w_rule_ptree_formula; auto. rewrite Z1. unfold neg_w_rule_sub_formula. simpl. rewrite non_target_fit. rewrite eq_nat_refl. rewrite eq_f_refl. simpl. rewrite non_target_sub'. auto.
          ++  simpl. rewrite neg_w_rule_ptree_formula; auto. rewrite Z1. unfold neg_w_rule_sub_formula. simpl. rewrite non_target_fit. rewrite eq_nat_refl. rewrite eq_f_refl. simpl. rewrite non_target_sub'. auto.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (neg_w_rule_sub_ptree PZ PY f0 f n2 (ptree_deg PY) (ord_2_exp o) PY1 (lor_ind (1) (non_target f1)))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I1.
          ++  repeat split. apply ord_ltb_lt. auto. apply neg_w_rule_valid; auto.
              { pose proof (provable_closed' PY _ Y2 Y1). simpl in H7. destruct (and_bool_prop _ _ H8). auto. }
              { rewrite Z1. simpl; auto. apply non_target_fit. }
              { apply nf_2_exp. auto. }
          ++  apply neg_w_rule_valid; auto.
              { pose proof (provable_closed' PY _ Y2 Y1). simpl in H7. destruct (and_bool_prop _ _ H8). auto. }
              { rewrite Z1. simpl; auto. apply non_target_fit. }
      --  pose proof (neg_w_rule_ptree_deg PZ _ _ _ _ _ _ PY1 Z2 H6 (lor_ind (1) (non_target f1))).
          unfold weak_ord_up. case (ord_ltb (ptree_ord (neg_w_rule_sub_ptree PZ PY f0 f n2 (ptree_deg PY) (ord_2_exp o) PY1 (lor_ind (1) (non_target f1)))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I1; simpl; lia. 
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (neg_w_rule_sub_ptree PZ PY f0 f n2 (ptree_deg PY) (ord_2_exp o) PY1 (lor_ind (1) (non_target f1)))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I1; simpl; auto. 
          pose proof (neg_w_rule_ptree_ord PZ _ _ _ _ _ _ PY1 Z2 (lor_ind (1) (non_target f1))).
          rewrite Z4 in H8.
          pose proof (ord_trans_inv _ _ _ (ord_add_exp_le_exp_max _ _ H1 H2) H8) as I2.
          destruct (ord_semiconnex_bool (ord_2_exp (ord_succ (ord_max o o0))) (ptree_ord (neg_w_rule_sub_ptree PZ PY f0 f n2 (ptree_deg PY) (ord_2_exp o) PY1 (lor_ind (1) (non_target f1))))) as [I3 | [I3 | I3]].
          ++  rewrite I3 in I2. inversion I2.
          ++  rewrite I3 in I1. inversion I1.
          ++  apply ord_eqb_eq in I3. auto. 
    + assert ((S (num_conn f0)) < (max n0 n1)) as E2. rewrite eq_nat_symm in E1. rewrite (nat_eq_decid _ _ (nat_max_right_not _ _ E1)). apply (max_lem2 _ _ E1).
      intros. destruct X0 as [[[X1 X2] X3] X4]. simpl in X1,X3,X4. destruct X4. destruct X2 as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8]. unfold cut_remove in X. case (eq_nat (max (max n0 n1) (S (num_conn f0))) (S d)) eqn:E.
      * assert ((S (num_conn f0)) < (max n0 n1)). rewrite eq_nat_symm in E1. rewrite (nat_eq_decid _ _ (nat_max_right_not _ _ E1)). apply (max_lem2 _ _ E1).
        apply nat_eq_decid in E. case (lt_nat n0 n1) eqn:Y.
        --  rewrite (max_split1 _ _ Y) in E. symmetry in E. destruct E. assert (P_proves P2 (lor (neg f0) f1) (S d) o0). { unfold P_proves. repeat split; simpl; auto. lia. } assert (nf o0). rewrite H8. apply ptree_ord_nf. auto.
            destruct (X _ H10 (ord_max_succ_r _ _) _ _ _ X0) as [P7 [[[HP1 HP2] HP3] HP4]]. exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_cad f f0 f1 n0 (ptree_deg P7) o (ord_2_exp o0) P1 P7)). repeat split; simpl; auto.
            apply ord_max_exp_r; auto. rewrite H7. apply ptree_ord_nf. auto. apply nf_2_exp. auto. apply lt_nat_decid in Y. lia.
        --  case (lt_nat n1 n0) eqn:Y1.
            ++  rewrite (max_split2 _ _ Y1) in E. symmetry in E. destruct E. assert (P_proves P1 (lor f f0) (S d) o). { unfold P_proves. repeat split; simpl; auto. lia. } assert (nf o). rewrite H7. apply ptree_ord_nf. auto.
                destruct (X _ H10 (ord_max_succ_l _ _) _ _ _ X0) as [P6 [[[HP1 HP2] HP3] HP4]]. exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_cad f f0 f1 (ptree_deg P6) n1 (ord_2_exp o) o0 P6 P2)). repeat split; simpl; auto.
                apply ord_max_exp_l; auto. rewrite H8. apply ptree_ord_nf. auto. apply nf_2_exp. auto. apply lt_nat_decid in Y1. lia.
            ++  assert (n0 = n1). destruct (nat_semiconnex n0 n1) as [Y2 | [Y2 | Y2]]; try apply lt_nat_decid_conv in Y2. rewrite Y2 in Y. inversion Y. rewrite Y2 in Y1. inversion Y1. auto. destruct H10. rewrite max_n_n in E. symmetry in E. destruct E.
                assert (P_proves P1 (lor f f0) (S d) o). { unfold P_proves. repeat split; simpl; auto. lia. } assert (nf o). rewrite H7. apply ptree_ord_nf. auto.
                assert (P_proves P2 (lor (neg f0) f1) (S d) o0). { unfold P_proves. repeat split; simpl; auto. lia. } assert (nf o0). rewrite H8. apply ptree_ord_nf. auto.
                destruct (X _ H10 (ord_max_succ_l _ _) _ _ _ X0) as [P6 [[[HP1 Hp2] HP3] HP4]]. destruct (X _ H11 (ord_max_succ_r _ _) _ _ _ X2) as [P7 [[[HQ1 HQ2] HQ3] HQ4]].
                exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_cad f f0 f1 (ptree_deg P6) (ptree_deg P7) (ord_2_exp o) (ord_2_exp o0) P6 P7)). repeat split; simpl; auto.
                apply ord_max_exp_both; auto. apply nf_2_exp. auto. lia.
      * assert (d >= max (max n0 n1) (S (num_conn f0))). { inversion X3. destruct H10. rewrite eq_nat_refl in E. inversion E. lia. } exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_cad f f0 f1 n0 n1 o o0 P1 P2)). repeat split; simpl; auto. apply ord_succ_not_exp_fp. auto. apply nf_2_exp. auto.
Qed.

Lemma cut_elim_aux1 : forall (alpha : ord) (P : ptree) (A : formula) (d : nat), P_proves P A (S d) alpha -> provable A d (ord_2_exp alpha).
Proof.
intros alpha P A d X. inversion X as [[[X1 X2] X3] X4]. destruct X4. apply (cut_elim_aux0 _ (ptree_ord_nf _ X2) P _ _ X).
Qed.

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

| exchange_cab C A B d alpha P' => cut_free P'

| exchange_abd A B D d alpha P' => cut_free P'

| exchange_cabd C A B D d alpha P' => cut_free P'

| contraction_a A d alpha P' => cut_free P'

| contraction_ad A D d alpha P' => cut_free P'


| weakening_ad A D d alpha P' => cut_free P'

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2 => (cut_free P1) * (cut_free P2)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2 => (cut_free P1) * (cut_free P2)

| negation_a A d alpha P' => cut_free P'

| negation_ad A D d alpha P' => cut_free P'


| quantification_a A n t d alpha P' => cut_free P'

| quantification_ad A D n t d alpha P' => cut_free P'

| w_rule_a A n d alpha g => forall (c : c_term), cut_free (g c)

| w_rule_ad A D n d alpha g => forall (c : c_term), cut_free (g c)


| cut_ca C A d1 d2 alpha1 alpha2 P1 P2 => False

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 => False

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2 => False

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
  intros. simpl in H. simpl in X. destruct (X c) as [[[H1 H2] H3] H4].
  rewrite H in H3. apply X0; auto. lia.
- rename f into A. rename f0 into D. rename p into g.
  rename n0 into d. rename o into alpha.
  intros. simpl in H. simpl in X. destruct (X c) as [[[H1 H2] H3] H4].
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