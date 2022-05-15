Add LoadPath "theories/Casteran" as Ordering.
Add LoadPath "theories/Maths" as Maths_Facts.
Add LoadPath "theories/Logic" as Systems.

From Maths_Facts Require Import naturals.
From Maths_Facts Require Import ordinals.

From Systems Require Import definitions.
From Systems Require Import fol.
From Systems Require Import PA_omega.
From Systems Require Import proof_trees.
From Systems Require Import substitute.
From Systems Require Import inverse_omega.

Require Import Lia.

Definition neg_w_rule_sub_formula
  (A E F : formula) (n : nat) (S : subst_ind) : formula :=
  formula_sub_ind A (neg (univ n E)) F S.

Lemma neg_w_rule_sub_formula_closed : forall (A : formula),
  closed A = true ->
  forall (E F : formula) (n : nat) (S : subst_ind), closed F = true ->
    closed (neg_w_rule_sub_formula A E F n S) = true.
Proof.
intros. unfold neg_w_rule_sub_formula. apply formula_sub_ind_closed; auto.
Qed.

Definition weak_ord_up (P: ptree) (alpha : ord) :=
match ord_ltb (ptree_ord P) alpha with
| true => ord_up alpha P
| false => P
end.

Lemma weak_ord_formula : forall (P : ptree) (alpha : ord), ptree_formula (weak_ord_up P alpha) = ptree_formula P.
Proof.
intros. unfold weak_ord_up. case (ord_ltb (ptree_ord P) alpha); auto.
Qed.

Lemma weak_ord_deg : forall (P : ptree) (alpha : ord), ptree_deg (weak_ord_up P alpha) = ptree_deg P.
Proof.
intros. unfold weak_ord_up. case (ord_ltb (ptree_ord P) alpha); auto.
Qed.

Lemma weak_ord_valid : forall (P : ptree) (alpha : ord), nf alpha -> valid P -> valid (weak_ord_up P alpha).
Proof.
intros. unfold weak_ord_up. case (ord_ltb (ptree_ord P) alpha) eqn:Y; auto. repeat split; auto. apply ord_ltb_lt. auto.
Qed.

Fixpoint neg_w_rule_sub_ptree_fit
  (P Q : ptree) (E F : formula) (n d' : nat) (beta : ord) (H : P_proves Q (lor F (univ n E)) d' beta) (S : subst_ind) : ptree :=
  match P, S with
| deg_up d P', _ => match lt_nat (ptree_deg (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H S)) d with
    | true => deg_up d (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H S)
    | false => (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H S)
    end
| ord_up alpha P', _ => match ord_ltb (ptree_ord (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H S)) alpha with
    | true => ord_up alpha (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H S)
    | false => (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H S)
    end

| node A, _ => P

| exchange_ab A B d alpha P', lor_ind S_B S_A =>
    exchange_ab
      (neg_w_rule_sub_formula A E F n S_A)
      (neg_w_rule_sub_formula B E F n S_B)
      (ptree_deg (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H (lor_ind S_A S_B)))
      (ptree_ord (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H (lor_ind S_A S_B)))
      (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H (lor_ind S_A S_B))

| exchange_cab C A B d alpha P', lor_ind (lor_ind S_C S_B) S_A =>
    exchange_cab
      (neg_w_rule_sub_formula C E F n S_C)
      (neg_w_rule_sub_formula A E F n S_A)
      (neg_w_rule_sub_formula B E F n S_B)
      (ptree_deg (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H (lor_ind (lor_ind S_C S_A) S_B)))
      (ptree_ord (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H (lor_ind (lor_ind S_C S_A) S_B)))
      (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H (lor_ind (lor_ind S_C S_A) S_B))

| exchange_abd A B D d alpha P', lor_ind (lor_ind S_B S_A) S_D =>
    exchange_abd
      (neg_w_rule_sub_formula A E F n S_A)
      (neg_w_rule_sub_formula B E F n S_B)
      (neg_w_rule_sub_formula D E F n S_D)
      (ptree_deg (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H (lor_ind (lor_ind S_A S_B) S_D)))
      (ptree_ord (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H (lor_ind (lor_ind S_A S_B) S_D)))
      (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H (lor_ind (lor_ind S_A S_B) S_D))

| exchange_cabd C A B D d alpha P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D =>
    exchange_cabd
      (neg_w_rule_sub_formula C E F n S_C)
      (neg_w_rule_sub_formula A E F n S_A)
      (neg_w_rule_sub_formula B E F n S_B)
      (neg_w_rule_sub_formula D E F n S_D)
      (ptree_deg (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D)))
      (ptree_ord (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D)))
      (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D))

| contraction_a A d alpha P', _ =>
    contraction_a
      (neg_w_rule_sub_formula A E F n S)
      (ptree_deg (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H (lor_ind S S)))
      (ptree_ord (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H (lor_ind S S)))
      (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H (lor_ind S S))

| contraction_ad A D d alpha P', lor_ind S_A S_D =>
    contraction_ad
      (neg_w_rule_sub_formula A E F n S_A)
      (neg_w_rule_sub_formula D E F n S_D)
      (ptree_deg (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H (lor_ind (lor_ind S_A S_A) S_D)))
      (ptree_ord (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H (lor_ind (lor_ind S_A S_A) S_D)))
      (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H (lor_ind (lor_ind S_A S_A) S_D))

| weakening_ad A D d alpha P', lor_ind S_A S_D =>
    weakening_ad
      (neg_w_rule_sub_formula A E F n S_A)
      (neg_w_rule_sub_formula D E F n S_D)
      (ptree_deg (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H S_D))
      (ptree_ord (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H S_D))
      (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H S_D)

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, _ => P

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_AB S_D =>
    demorgan_abd
      A B
      (neg_w_rule_sub_formula D E F n S_D)
      (ptree_deg (neg_w_rule_sub_ptree_fit P1 Q E F n d' beta H (lor_ind (0) S_D)))
      (ptree_deg (neg_w_rule_sub_ptree_fit P2 Q E F n d' beta H (lor_ind (0) S_D)))
      (ptree_ord (neg_w_rule_sub_ptree_fit P1 Q E F n d' beta H (lor_ind (0) S_D)))
      (ptree_ord (neg_w_rule_sub_ptree_fit P2 Q E F n d' beta H (lor_ind (0) S_D)))
      (neg_w_rule_sub_ptree_fit P1 Q E F n d' beta H (lor_ind (0) S_D))
      (neg_w_rule_sub_ptree_fit P2 Q E F n d' beta H (lor_ind (0) S_D))

| negation_a A d alpha P', _ => P

| negation_ad A D d alpha P', lor_ind S_A S_D =>
    negation_ad
      A
      (neg_w_rule_sub_formula D E F n S_D)
      (ptree_deg (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H (lor_ind (non_target A) S_D)))
      (ptree_ord (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H (lor_ind (non_target A) S_D)))
      (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H (lor_ind (non_target A) S_D))

| quantification_a A k t d alpha P', _ =>
    (match eq_f A E, eq_nat k n, S with
    | true, true, (1) => (cut_ca F (substitution E n (projT1 t)) (ptree_deg (w_rule_sub_ptree Q E n t (lor_ind (non_target F) (1)))) d beta alpha (w_rule_sub_ptree Q E n t (lor_ind (non_target F) (1))) P')
    | _, _, _ => P
    end)

| quantification_ad A D k t d alpha P', lor_ind S_A S_D =>
    (match eq_f A E, eq_nat k n, S_A with
    | true, true, (1) => (cut_cad F (substitution E n (projT1 t)) (neg_w_rule_sub_formula D E F n S_D)
                              (ptree_deg (projT1(w_rule_invertible_cut_cad Q E F n d' beta t H)))
                              (ptree_deg (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H (lor_ind (0) S_D)))
                              beta (ptree_ord (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H (lor_ind (0) S_D)))
                              (projT1(w_rule_invertible_cut_cad Q E F n d' beta t H)) (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H (lor_ind (0) S_D)))
    | _, _, _ => quantification_ad
                    A (neg_w_rule_sub_formula D E F n S_D) k t
                    (ptree_deg (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H (lor_ind (0) S_D)))
                    (ptree_ord (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H (lor_ind (0) S_D)))
                    (neg_w_rule_sub_ptree_fit P' Q E F n d' beta H (lor_ind (0) S_D))
    end)

| w_rule_a A k d alpha g, _ => P

| w_rule_ad A D k d alpha g, lor_ind S_A S_D =>
    w_rule_ad
          A (neg_w_rule_sub_formula D E F n S_D) k
          (Nat.max (Nat.max d' d) (num_conn E + 1))
          (ord_add beta alpha)
          (fun (c : c_term) =>
            (weak_ord_up (neg_w_rule_sub_ptree_fit (g c) Q E F n d' beta H (lor_ind (non_target A) S_D)) (ord_add beta alpha)))

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ca
      (neg_w_rule_sub_formula C E F n S) A
      (ptree_deg (neg_w_rule_sub_ptree_fit P1 Q E F n d' beta H (lor_ind S (non_target A)))) d2
      (ptree_ord (neg_w_rule_sub_ptree_fit P1 Q E F n d' beta H (lor_ind S (non_target A)))) alpha2
      (neg_w_rule_sub_ptree_fit P1 Q E F n d' beta H (lor_ind S (non_target A)))  P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ad
      A (neg_w_rule_sub_formula D E F n S)
      d1 (ptree_deg (neg_w_rule_sub_ptree_fit P2 Q E F n d' beta H (lor_ind (0) S)))
      alpha1 (ptree_ord (neg_w_rule_sub_ptree_fit P2 Q E F n d' beta H (lor_ind (0) S)))
      P1   (neg_w_rule_sub_ptree_fit P2 Q E F n d' beta H (lor_ind (0) S))

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_D =>
    cut_cad
      (neg_w_rule_sub_formula C E F n S_C) A (neg_w_rule_sub_formula D E F n S_D)
      (ptree_deg (neg_w_rule_sub_ptree_fit P1 Q E F n d' beta H (lor_ind S_C (non_target A))))
      (ptree_deg (neg_w_rule_sub_ptree_fit P2 Q E F n d' beta H (lor_ind (0) S_D)))
      (ptree_ord (neg_w_rule_sub_ptree_fit P1 Q E F n d' beta H (lor_ind S_C (non_target A))))
      (ptree_ord (neg_w_rule_sub_ptree_fit P2 Q E F n d' beta H (lor_ind (0) S_D)))
      (neg_w_rule_sub_ptree_fit P1 Q E F n d' beta H (lor_ind S_C (non_target A)))
      (neg_w_rule_sub_ptree_fit P2 Q E F n d' beta H (lor_ind (0) S_D))

| _, _ => P
end.

Fixpoint neg_w_rule_sub_ptree
  (P Q : ptree) (E F : formula) (n d' : nat) (beta : ord) (H : P_proves Q (lor F (univ n E)) d' beta) (S : subst_ind) : ptree :=
match subst_ind_fit (ptree_formula P) S with
| false => P
| true => neg_w_rule_sub_ptree_fit P Q E F n d' beta H S
end.

(* First, we must prove that neg_w_rule_sub_ptree simply changes the base formula
of an ptree the way we expect with neg_w_rule_sub_formula *)
(* *)
Lemma neg_w_rule_ptree_formula_aux' :
  forall (P Q : ptree) (E F : formula) (n d' : nat) (beta : ord) (H : P_proves Q (lor F (univ n E)) d' beta) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
    neg_w_rule_sub_ptree P Q E F n d' beta H S = P.
Proof. intros. unfold neg_w_rule_sub_ptree. destruct P; rewrite H0; auto. Qed.

Lemma neg_w_rule_ptree_formula_aux :
  forall (P Q : ptree) (E F : formula) (n d' : nat) (beta : ord) (H : P_proves Q (lor F (univ n E)) d' beta) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
      ptree_formula (neg_w_rule_sub_ptree P Q E F n d' beta H S) =
      neg_w_rule_sub_formula (ptree_formula P) E F n S.
Proof.
intros. rewrite neg_w_rule_ptree_formula_aux'.
- unfold neg_w_rule_sub_formula. rewrite sub_fit_false. auto. apply H0.
- apply H0.
Qed.

Lemma neg_w_rule_ptree_formula_true :
  forall (P Q : ptree) (E F : formula) (n d' : nat) (beta : ord) (H : P_proves Q (lor F (univ n E)) d' beta) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    neg_w_rule_sub_ptree_fit P Q E F n d' beta H S = neg_w_rule_sub_ptree P Q E F n d' beta H S.
Proof. intros. unfold neg_w_rule_sub_ptree. destruct P; rewrite H0; auto. Qed.

Lemma neg_w_rule_ptree_formula' : forall (P Q : ptree) (E F : formula) (n d' : nat) (beta : ord) (H : P_proves Q (lor F (univ n E)) d' beta),
  valid P ->
  forall (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    ptree_formula (neg_w_rule_sub_ptree P Q E F n d' beta H S) =
    neg_w_rule_sub_formula (ptree_formula P) E F n S.
Proof.
intros P Q E F n d' beta HQ.
induction P; try intros H S Hs.

- simpl in Hs. simpl. rewrite Hs. simpl.
  rewrite (neg_w_rule_ptree_formula_true _ _ _ _ _ _ _ _ _ Hs).
  destruct H as [H1 H2]. case (lt_nat (ptree_deg (neg_w_rule_sub_ptree P Q E F n d' beta HQ S)) n0); apply (IHP H2); auto.

- simpl in Hs. simpl. rewrite Hs. simpl.
  rewrite (neg_w_rule_ptree_formula_true _ _ _ _ _ _ _ _ _ Hs).
  destruct H as [[H1 H2] H3]. case (ord_ltb (ptree_ord (neg_w_rule_sub_ptree P Q E F n d' beta HQ S)) o); apply (IHP H2); auto.

- simpl. inversion H.
  destruct (axiom_atomic _ H1); destruct H0; rewrite H0;
  unfold neg_w_rule_sub_formula; simpl; destruct S; auto.

- simpl.
  destruct S; inversion Hs; rewrite H1; simpl; unfold neg_w_rule_sub_formula.
  rewrite formula_sub_ind_lor; auto.

- simpl.
  destruct S; try destruct S1; inversion Hs; rewrite H1;
  simpl; unfold neg_w_rule_sub_formula.
  rewrite formula_sub_ind_lor, formula_sub_ind_lor; auto.
  apply (and_bool_prop _ _ H1).

- simpl.
  destruct S; try destruct S1; inversion Hs; rewrite H1;
  simpl; unfold neg_w_rule_sub_formula.
  rewrite formula_sub_ind_lor, formula_sub_ind_lor; auto.
  apply (and_bool_prop _ _ H1).

- simpl. destruct S; simpl.
  + unfold neg_w_rule_sub_formula. auto.
  + unfold neg_w_rule_sub_formula. auto.
  + destruct S1; try destruct S1_1; inversion Hs.
    rewrite H1. simpl. unfold neg_w_rule_sub_formula.
    destruct (and_bool_prop _ _ H1). destruct (and_bool_prop _ _ H0).
    repeat rewrite formula_sub_ind_lor; auto.

- simpl. inversion Hs. rewrite H1. auto.

- simpl. destruct S; inversion Hs.
  rewrite H1. simpl. unfold neg_w_rule_sub_formula.
  rewrite formula_sub_ind_lor. auto. apply H1.

- simpl. destruct S; auto. inversion Hs. rewrite H1. simpl.
  unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_lor. auto. apply H1.

- simpl. destruct S; auto.

- simpl. destruct S.
  + inversion Hs.
  + inversion Hs.
  + destruct S1; inversion Hs; rewrite H1; simpl; unfold neg_w_rule_sub_formula;
    rewrite formula_sub_ind_lor; auto; apply H1.

- simpl. destruct (eq_f f E) eqn:Heq; destruct S.
  + simpl. unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_0. auto.
  + unfold neg_w_rule_sub_formula. simpl. inversion H as [[[H1 H2] H3] H4]. auto.
  + inversion Hs.
  + simpl. unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_0. auto.
  + unfold neg_w_rule_sub_formula. simpl. auto.
  + inversion Hs.

- simpl. destruct (eq_f f E) eqn:Heq; destruct S.
  + inversion Hs.
  + inversion Hs.
  + destruct S1.
    * apply (subst_ind_fit_lor) in Hs. destruct (and_bool_prop _ _ Hs).
      rewrite H1. simpl. unfold neg_w_rule_sub_formula.
      rewrite formula_sub_ind_lor, formula_sub_ind_0. auto. apply Hs.
    * inversion Hs. rewrite H1. simpl. inversion H as [[[H2 H3] H4] H5].
      unfold neg_w_rule_sub_formula. simpl. rewrite H1. rewrite sub_fit_true; auto.
    * simpl. inversion Hs.
  + inversion Hs.
  + inversion Hs.
  + destruct S1.
    * apply (subst_ind_fit_lor) in Hs. destruct (and_bool_prop _ _ Hs).
      rewrite H1. simpl. unfold neg_w_rule_sub_formula.
      rewrite formula_sub_ind_lor, formula_sub_ind_0. auto. apply Hs.
    * inversion Hs. rewrite H1. simpl. unfold neg_w_rule_sub_formula.
      rewrite formula_sub_ind_lor; auto.
    * simpl. inversion Hs.

- simpl. destruct S; simpl; unfold neg_w_rule_sub_formula; auto; simpl; case (eq_nat n0 n); simpl; case (eq_f f E); auto.

- simpl. destruct S; inversion Hs. destruct S1; inversion Hs; rewrite H2; simpl; unfold neg_w_rule_sub_formula; simpl; case (eq_nat n0 n); case (eq_f f E); simpl; rewrite H2; rewrite sub_fit_true; auto.

- intros. destruct S; auto.

- intros. simpl. destruct S; auto; destruct S1; auto; unfold "&&"; simpl in H0; rewrite H0; simpl; unfold neg_w_rule_sub_formula; simpl; rewrite H0; rewrite sub_fit_true; auto.

- simpl. inversion Hs. rewrite H1. auto.

- simpl. inversion Hs. rewrite H1. auto.

- simpl. destruct S; inversion Hs.
  rewrite H1. simpl. unfold neg_w_rule_sub_formula.
  rewrite formula_sub_ind_lor; auto.
Qed.


Lemma neg_w_rule_ptree_formula : forall (P Q : ptree) (E F : formula) (n d' : nat) (beta : ord) (H : P_proves Q (lor F (univ n E)) d' beta),
  valid P ->
  forall (S : subst_ind),
    ptree_formula (neg_w_rule_sub_ptree P Q E F n d' beta H S) =
    neg_w_rule_sub_formula (ptree_formula P) E F n S.
Proof.
intros. destruct (subst_ind_fit (ptree_formula P) S) eqn:Hs.
- apply neg_w_rule_ptree_formula'. apply X. apply Hs.
- apply neg_w_rule_ptree_formula_aux. apply Hs.
Qed.



(* Second, we must prove that neg_w_rule_sub_ptree does not change the degree
of an ptree. *)
(* *)
Lemma  neg_w_rule_ptree_deg : forall (P Q : ptree) (E F : formula) (n d' : nat) (beta : ord) (H : P_proves Q (lor F (univ n E)) d' beta),
  valid P -> Nat.max d' (ptree_deg P) < (num_conn E + 2) ->
    forall (S : subst_ind), ptree_deg (neg_w_rule_sub_ptree P Q E F n d' beta H S) <= (Nat.max (Nat.max d' (ptree_deg P)) (num_conn E + 1)).
Proof.
intros P Q E F n d' beta HQ H HD. induction P; intros S.
- simpl. case (subst_ind_fit (ptree_formula P) S) eqn:X; simpl; auto; try lia.
  case (lt_nat (ptree_deg (neg_w_rule_sub_ptree_fit P Q E F n d' beta HQ S)) n0) eqn:Y; simpl; try lia.
  rewrite neg_w_rule_ptree_formula_true; auto.
  destruct H as [X1 X2]. simpl in HD. assert (Nat.max d' (ptree_deg P) < num_conn E + 2). { lia. }
  destruct (leq_type _ _ (IHP X2 H S)); lia.  
- simpl. case (subst_ind_fit (ptree_formula P) S) eqn:Hfit; auto; try lia. simpl in HD. destruct H as [[X1 X2] X3].
  case (ord_ltb (ptree_ord (neg_w_rule_sub_ptree_fit P Q E F n d' beta HQ S)) o) eqn:X; simpl;
  rewrite (neg_w_rule_ptree_formula_true _ _ _ _ _ _ _ _ _ Hfit); apply IHP; auto. 
- simpl in *. case (subst_ind_fit f S); simpl; lia.
- simpl. simpl in HD. destruct H as [[[X1 X2] X3] X4]. rewrite X3 in *. destruct S; simpl; try lia.
  case (subst_ind_fit f0 S1 && subst_ind_fit f S2) eqn:Y; simpl; try lia.
  rewrite neg_w_rule_ptree_formula_true; auto. rewrite X1. apply and_bool_symm in Y. auto.
- simpl. simpl in HD. destruct H as [[[X1 X2] X3] X4]. rewrite X3 in *. destruct S; simpl; try lia; destruct S1; simpl; try lia.
  case (subst_ind_fit f S1_1 && subst_ind_fit f1 S1_2 && subst_ind_fit f0 S2) eqn:Y; simpl; try lia.
  rewrite neg_w_rule_ptree_formula_true; auto. rewrite X1. simpl. destruct (and_bool_prop _ _ Y). destruct (and_bool_prop _ _ H). rewrite H0,H1,H2. auto.
- simpl. simpl in HD. destruct H as [[[X1 X2] X3] X4]. rewrite X3 in *. destruct S; simpl; try lia; destruct S1; simpl; try lia.
  case (subst_ind_fit f0 S1_1 && subst_ind_fit f S1_2 && subst_ind_fit f1 S2) eqn:Y; simpl; try lia.
  rewrite neg_w_rule_ptree_formula_true; auto. rewrite X1. simpl. destruct (and_bool_prop _ _ Y). destruct (and_bool_prop _ _ H). rewrite H0,H1,H2. auto.
- simpl. simpl in HD. destruct H as [[[X1 X2] X3] X4]. rewrite X3 in *. destruct S; simpl; try lia; destruct S1; simpl; try lia; destruct S1_1; simpl; try lia.
  case (subst_ind_fit f S1_1_1 && subst_ind_fit f1 S1_1_2 && subst_ind_fit f0 S1_2 && subst_ind_fit f2 S2) eqn:Y; simpl; try lia.
  rewrite neg_w_rule_ptree_formula_true; auto. rewrite X1. simpl. destruct (and_bool_prop _ _ Y). destruct (and_bool_prop _ _ H). destruct (and_bool_prop _ _ H1). rewrite H0,H2,H3,H4. auto.
- simpl. simpl in HD. destruct H as [[[X1 X2] X3] X4]. rewrite X3 in *. destruct (subst_ind_fit f S) eqn:Y; simpl; try lia.
  rewrite neg_w_rule_ptree_formula_true; auto. rewrite X1. simpl. rewrite Y. auto.
- simpl. simpl in HD. destruct H as [[[X1 X2] X3] X4]. rewrite X3 in *. destruct S; simpl; try lia.
  case (subst_ind_fit f S1 && subst_ind_fit f0 S2) eqn:Y; simpl; try lia.
  rewrite neg_w_rule_ptree_formula_true; auto. rewrite X1. simpl. destruct (and_bool_prop _ _ Y). rewrite H,H0. auto.
- simpl. simpl in HD. destruct H as [[[[X0 X1] X2] X3] X4]. rewrite X3 in *. destruct S; simpl; try lia.
  case (subst_ind_fit f S1 && subst_ind_fit f0 S2) eqn:Y; simpl; try lia.
  rewrite neg_w_rule_ptree_formula_true; auto. rewrite X0. destruct (and_bool_prop _ _ Y). apply H0.
- destruct S; simpl; try lia.
- simpl. simpl in HD. destruct H as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. rewrite X5,X6 in *. destruct S; simpl; try lia; destruct S1; simpl; try lia;
  case (subst_ind_fit f1 S2) eqn:Y; simpl; try lia;
  rewrite neg_w_rule_ptree_formula_true; auto; try rewrite neg_w_rule_ptree_formula_true; auto. 
  + destruct (nat_semiconnex_bool (ptree_deg (neg_w_rule_sub_ptree P1 Q E F n d' beta HQ (lor_ind (0) S2))) (ptree_deg (neg_w_rule_sub_ptree P2 Q E F n d' beta HQ (lor_ind (0) S2)))) as [Y1 | [Y1 | Y1]].
    * rewrite (max_split1 _ _ Y1). destruct (nat_semiconnex_bool (ptree_deg P1) (ptree_deg P2)) as [Y2 | [Y2 | Y2]].
      --  rewrite (max_split1 _ _ Y2). rewrite (max_split1 _ _ Y2) in HD. apply IHP2; auto.
      --  rewrite (max_split2 _ _ Y2). rewrite (max_split2 _ _ Y2) in HD. apply lt_nat_decid in Y2.
          assert (Nat.max (Nat.max d' (ptree_deg P2)) (num_conn E + 1) <= Nat.max (Nat.max d' (ptree_deg P1)) (num_conn E + 1)). lia.
          assert ((Nat.max d' (ptree_deg P2)) < (num_conn E) + 2). lia.
          assert ((ptree_deg (neg_w_rule_sub_ptree P2 Q E F n d' beta HQ (lor_ind (0) S2))) <= Nat.max (Nat.max d' (ptree_deg P2)) (num_conn E + 1)). auto.
          lia.
      --  apply nat_eq_decid in Y2. destruct Y2. rewrite max_n_n in *. auto.
    * rewrite (max_split2 _ _ Y1). destruct (nat_semiconnex_bool (ptree_deg P1) (ptree_deg P2)) as [Y2 | [Y2 | Y2]].
      --  rewrite (max_split1 _ _ Y2). rewrite (max_split1 _ _ Y2) in HD. apply lt_nat_decid in Y2.
          assert (Nat.max (Nat.max d' (ptree_deg P1)) (num_conn E + 1) <= Nat.max (Nat.max d' (ptree_deg P2)) (num_conn E + 1)). lia.
          assert ((Nat.max d' (ptree_deg P1)) < (num_conn E) + 2). lia.
          assert ((ptree_deg (neg_w_rule_sub_ptree P1 Q E F n d' beta HQ (lor_ind (0) S2))) <= Nat.max (Nat.max d' (ptree_deg P1)) (num_conn E + 1)). auto.
          lia.
      --  rewrite (max_split2 _ _ Y2). rewrite (max_split2 _ _ Y2) in HD. apply IHP1; auto.
      --  apply nat_eq_decid in Y2. destruct Y2. rewrite max_n_n in *. auto.
    * apply nat_eq_decid in Y1. rewrite Y1. rewrite max_n_n in *. destruct (nat_semiconnex_bool (ptree_deg P1) (ptree_deg P2)) as [Y2 | [Y2 | Y2]].
      --  rewrite (max_split1 _ _ Y2). rewrite (max_split1 _ _ Y2) in HD. apply IHP2; auto.
      --  rewrite (max_split2 _ _ Y2). rewrite (max_split2 _ _ Y2) in HD. apply lt_nat_decid in Y2.
          assert (Nat.max (Nat.max d' (ptree_deg P2)) (num_conn E + 1) <= Nat.max (Nat.max d' (ptree_deg P1)) (num_conn E + 1)). lia.
          assert ((Nat.max d' (ptree_deg P2)) < (num_conn E) + 2). lia.
          assert ((ptree_deg (neg_w_rule_sub_ptree P2 Q E F n d' beta HQ (lor_ind (0) S2))) <= Nat.max (Nat.max d' (ptree_deg P2)) (num_conn E + 1)). auto.
          lia.
      --  apply nat_eq_decid in Y2. destruct Y2. rewrite max_n_n in *. auto.
  + rewrite X3. auto.
  + rewrite X1. auto.
  + destruct (nat_semiconnex_bool (ptree_deg (neg_w_rule_sub_ptree P1 Q E F n d' beta HQ (lor_ind (0) S2))) (ptree_deg (neg_w_rule_sub_ptree P2 Q E F n d' beta HQ (lor_ind (0) S2)))) as [Y1 | [Y1 | Y1]].
    * rewrite (max_split1 _ _ Y1). destruct (nat_semiconnex_bool (ptree_deg P1) (ptree_deg P2)) as [Y2 | [Y2 | Y2]].
      --  rewrite (max_split1 _ _ Y2). rewrite (max_split1 _ _ Y2) in HD. apply IHP2; auto.
      --  rewrite (max_split2 _ _ Y2). rewrite (max_split2 _ _ Y2) in HD. apply lt_nat_decid in Y2.
          assert (Nat.max (Nat.max d' (ptree_deg P2)) (num_conn E + 1) <= Nat.max (Nat.max d' (ptree_deg P1)) (num_conn E + 1)). lia.
          assert ((Nat.max d' (ptree_deg P2)) < (num_conn E) + 2). lia.
          assert ((ptree_deg (neg_w_rule_sub_ptree P2 Q E F n d' beta HQ (lor_ind (0) S2))) <= Nat.max (Nat.max d' (ptree_deg P2)) (num_conn E + 1)). auto.
          lia.
      --  apply nat_eq_decid in Y2. destruct Y2. rewrite max_n_n in *. auto.
    * rewrite (max_split2 _ _ Y1). destruct (nat_semiconnex_bool (ptree_deg P1) (ptree_deg P2)) as [Y2 | [Y2 | Y2]].
      --  rewrite (max_split1 _ _ Y2). rewrite (max_split1 _ _ Y2) in HD. apply lt_nat_decid in Y2.
          assert (Nat.max (Nat.max d' (ptree_deg P1)) (num_conn E + 1) <= Nat.max (Nat.max d' (ptree_deg P2)) (num_conn E + 1)). lia.
          assert ((Nat.max d' (ptree_deg P1)) < (num_conn E) + 2). lia.
          assert ((ptree_deg (neg_w_rule_sub_ptree P1 Q E F n d' beta HQ (lor_ind (0) S2))) <= Nat.max (Nat.max d' (ptree_deg P1)) (num_conn E + 1)). auto.
          lia.
      --  rewrite (max_split2 _ _ Y2). rewrite (max_split2 _ _ Y2) in HD. apply IHP1; auto.
      --  apply nat_eq_decid in Y2. destruct Y2. rewrite max_n_n in *. auto.
    * apply nat_eq_decid in Y1. rewrite Y1. rewrite max_n_n in *. destruct (nat_semiconnex_bool (ptree_deg P1) (ptree_deg P2)) as [Y2 | [Y2 | Y2]].
      --  rewrite (max_split1 _ _ Y2). rewrite (max_split1 _ _ Y2) in HD. apply IHP2; auto.
      --  rewrite (max_split2 _ _ Y2). rewrite (max_split2 _ _ Y2) in HD. apply lt_nat_decid in Y2.
          assert (Nat.max (Nat.max d' (ptree_deg P2)) (num_conn E + 1) <= Nat.max (Nat.max d' (ptree_deg P1)) (num_conn E + 1)). lia.
          assert ((Nat.max d' (ptree_deg P2)) < (num_conn E) + 2). lia.
          assert ((ptree_deg (neg_w_rule_sub_ptree P2 Q E F n d' beta HQ (lor_ind (0) S2))) <= Nat.max (Nat.max d' (ptree_deg P2)) (num_conn E + 1)). auto.
          lia.
      --  apply nat_eq_decid in Y2. destruct Y2. rewrite max_n_n in *. auto.
  + rewrite X3. auto.
  + rewrite X1. auto.
- destruct S; simpl; try lia.
- simpl. simpl in HD. destruct H as [[[X1 X2] X3] X4]. rewrite X3 in *. destruct S; simpl; try lia; destruct S1; simpl; try lia;
  case (subst_ind_fit f0 S2) eqn:Y; simpl; try lia;
  rewrite neg_w_rule_ptree_formula_true; auto; rewrite X1; simpl; rewrite non_target_fit; auto.
- simpl. simpl in HD. destruct H as [[[X1 X2] X3] X4]. rewrite X3 in *. destruct S; simpl; try lia;
  case (eq_f f E) eqn:Y; case (eq_nat n0 n) eqn:Y1; simpl; try lia.
  destruct HQ as [[[Q1 Q2] Q3] Q4]. rewrite <- w_rule_ptree_deg; auto. rewrite num_conn_sub. lia. 
- simpl. simpl in HD. destruct H as [[[X1 X2] X3] X4]. rewrite X3 in *. destruct S; simpl; try lia; destruct S1; simpl; try lia;
  case (subst_ind_fit f0 S2) eqn:Y; simpl; try lia; case (eq_f f E) eqn:Y1; case (eq_nat n0 n) eqn:Y2; simpl; try lia;
  try rewrite neg_w_rule_ptree_formula_true; auto; try rewrite X1; simpl; auto. rewrite num_conn_sub.
  unfold w_rule_invertible_cut_cad. destruct HQ. destruct p. destruct p. simpl.
  pose proof (IHP X2 HD (lor_ind (0) S2)). lia.
- destruct S; simpl; try lia.
- simpl. simpl in HD. destruct S; simpl; try lia; destruct S1; simpl; try lia;
  case (subst_ind_fit f0 S2) eqn:Y; simpl; try lia;
  rewrite neg_w_rule_ptree_formula_true; auto.
- simpl. simpl in HD. destruct H as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. rewrite X5,X6 in *. case (subst_ind_fit f S) eqn:Y; simpl; try lia. rewrite neg_w_rule_ptree_formula_true; auto.
  + assert (Nat.max d' (ptree_deg P1) < num_conn E + 2). lia. pose proof (IHP1 X2 H (lor_ind S (non_target f0))). lia.
  + rewrite X1. simpl. rewrite Y. apply non_target_fit. 
- simpl. simpl in HD. destruct H as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. rewrite X5,X6 in *. case (subst_ind_fit f0 S) eqn:Y; simpl; try lia. rewrite neg_w_rule_ptree_formula_true; auto.
  + assert (Nat.max d' (ptree_deg P2) < num_conn E + 2). lia. pose proof (IHP2 X4 H (lor_ind (0) S)). lia.
  + rewrite X3. auto. 
- simpl. simpl in HD. destruct H as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. rewrite X5,X6 in *. destruct S; simpl; try lia;
  case (subst_ind_fit f S1 && subst_ind_fit f1 S2) eqn:Y; simpl; try lia;
  rewrite neg_w_rule_ptree_formula_true; auto; try rewrite neg_w_rule_ptree_formula_true; auto; apply and_bool_prop in Y; destruct Y as [HS1 HS2].
  + destruct (nat_semiconnex_bool (ptree_deg (neg_w_rule_sub_ptree P1 Q E F n d' beta HQ (lor_ind S1 (non_target f0)))) (ptree_deg (neg_w_rule_sub_ptree P2 Q E F n d' beta HQ (lor_ind (0) S2)))) as [Y1 | [Y1 | Y1]].
    * rewrite (max_split1 _ _ Y1). destruct (nat_semiconnex_bool (ptree_deg P1) (ptree_deg P2)) as [Y2 | [Y2 | Y2]].
      --  rewrite (max_split1 _ _ Y2). rewrite (max_split1 _ _ Y2) in HD.
          assert (Nat.max d' (ptree_deg P2) < num_conn E + 2). lia. pose proof (IHP2 X4 H (lor_ind (0) S2)). lia.
      --  rewrite (max_split2 _ _ Y2). rewrite (max_split2 _ _ Y2) in HD. apply lt_nat_decid in Y2.
          assert (Nat.max (Nat.max d' (ptree_deg P2)) (num_conn E + 1) <= Nat.max (Nat.max d' (ptree_deg P1)) (num_conn E + 1)). lia.
          assert ((Nat.max d' (ptree_deg P2)) < (num_conn E) + 2). lia.
          assert ((ptree_deg (neg_w_rule_sub_ptree P2 Q E F n d' beta HQ (lor_ind (0) S2))) <= Nat.max (Nat.max d' (ptree_deg P2)) (num_conn E + 1)). auto.
          lia.
      --  apply nat_eq_decid in Y2. destruct Y2. rewrite max_n_n in *.
          assert (Nat.max d' (ptree_deg P1) < num_conn E + 2). lia. pose proof (IHP2 X4 H (lor_ind (0) S2)). lia.
    * rewrite (max_split2 _ _ Y1). destruct (nat_semiconnex_bool (ptree_deg P1) (ptree_deg P2)) as [Y2 | [Y2 | Y2]].
      --  rewrite (max_split1 _ _ Y2). rewrite (max_split1 _ _ Y2) in HD. apply lt_nat_decid in Y2.
          assert (Nat.max (Nat.max d' (ptree_deg P1)) (num_conn E + 1) <= Nat.max (Nat.max d' (ptree_deg P2)) (num_conn E + 1)). lia.
          assert ((Nat.max d' (ptree_deg P1)) < (num_conn E) + 2). lia.
          assert ((ptree_deg (neg_w_rule_sub_ptree P1 Q E F n d' beta HQ (lor_ind S1 (non_target f0)))) <= Nat.max (Nat.max d' (ptree_deg P1)) (num_conn E + 1)). auto.
          lia.
      --  rewrite (max_split2 _ _ Y2). rewrite (max_split2 _ _ Y2) in HD. assert (Nat.max d' (ptree_deg P1) < num_conn E + 2). lia. pose proof (IHP1 X2 H (lor_ind S1 (non_target f0))). lia.
      --  apply nat_eq_decid in Y2. destruct Y2. rewrite max_n_n in *. assert (Nat.max d' (ptree_deg P1) < num_conn E + 2). lia. pose proof (IHP1 X2 H (lor_ind S1 (non_target f0))). lia.
    * apply nat_eq_decid in Y1. rewrite Y1. rewrite max_n_n in *. destruct (nat_semiconnex_bool (ptree_deg P1) (ptree_deg P2)) as [Y2 | [Y2 | Y2]].
    --  rewrite (max_split1 _ _ Y2). rewrite (max_split1 _ _ Y2) in HD.
        assert (Nat.max d' (ptree_deg P2) < num_conn E + 2). lia. pose proof (IHP2 X4 H (lor_ind (0) S2)). lia.
    --  rewrite (max_split2 _ _ Y2). rewrite (max_split2 _ _ Y2) in HD. apply lt_nat_decid in Y2.
        assert (Nat.max (Nat.max d' (ptree_deg P2)) (num_conn E + 1) <= Nat.max (Nat.max d' (ptree_deg P1)) (num_conn E + 1)). lia.
        assert ((Nat.max d' (ptree_deg P2)) < (num_conn E) + 2). lia.
        assert ((ptree_deg (neg_w_rule_sub_ptree P2 Q E F n d' beta HQ (lor_ind (0) S2))) <= Nat.max (Nat.max d' (ptree_deg P2)) (num_conn E + 1)). auto.
        lia.
    --  apply nat_eq_decid in Y2. destruct Y2. rewrite max_n_n in *.
        assert (Nat.max d' (ptree_deg P1) < num_conn E + 2). lia. pose proof (IHP2 X4 H (lor_ind (0) S2)). lia.  
  + rewrite X3. simpl. auto.
  + rewrite X1. simpl. rewrite non_target_fit. rewrite HS1. auto.
Qed.


(* Third, we must prove that neg_w_rule_sub_ptree does not change the ordinal
of an ptree. *)
(* *)
Lemma neg_w_rule_ptree_ord : forall (P Q : ptree) (E F : formula) (n d' : nat) (beta : ord) (H : P_proves Q (lor F (univ n E)) d' beta),
  valid P ->
  forall (S : subst_ind), ord_ltb (ord_add beta (ptree_ord P)) (ptree_ord (neg_w_rule_sub_ptree P Q E F n d' beta H S)) = false.
Proof.
intros P Q E F n d' beta HQ H. induction P; intros S.
- simpl. inversion H as [X1 X2]. case (subst_ind_fit (ptree_formula P) S) eqn:Hfit; simpl; auto. case (lt_nat (ptree_deg (neg_w_rule_sub_ptree_fit P Q E F n d' beta HQ S)) n0) eqn:X; simpl; auto.
  + rewrite neg_w_rule_ptree_formula_true; auto.
  + rewrite neg_w_rule_ptree_formula_true; auto.
  + apply add_left_non_decr.
- simpl. inversion H as [[X1 X2] X3]. case (subst_ind_fit (ptree_formula P) S) eqn:Hfit; simpl; auto. case (ord_ltb (ptree_ord (neg_w_rule_sub_ptree_fit P Q E F n d' beta HQ S)) o) eqn:X; simpl; auto.
  + apply add_left_non_decr.
  + rewrite neg_w_rule_ptree_formula_true; auto. apply (ord_trans_inv _ (ord_add beta (ptree_ord P))); auto. apply ltb_asymm. apply ord_lt_ltb. apply add_right_incr. auto.
  + apply add_left_non_decr.
- simpl. destruct beta; case (subst_ind_fit f S); auto.
- simpl. inversion H as [[[X1 X2] X3] X4]. destruct S; simpl; auto.
  + apply add_left_non_decr.
  + apply add_left_non_decr.
  + case (subst_ind_fit f0 S1 && subst_ind_fit f S2) eqn:Y.
    * rewrite neg_w_rule_ptree_formula_true. simpl. destruct X4. auto. rewrite X1. simpl. destruct (and_bool_prop _ _ Y) as [Y1 Y2]. rewrite Y1,Y2. auto.
    * apply add_left_non_decr.
- simpl. inversion H as [[[X1 X2] X3] X4]. destruct S; simpl; auto.
  + apply add_left_non_decr.
  + apply add_left_non_decr.
  + destruct S1; simpl; auto.
    * apply add_left_non_decr.
    * apply add_left_non_decr.
    * case (subst_ind_fit f S1_1 && subst_ind_fit f1 S1_2 && subst_ind_fit f0 S2) eqn:Y.
      --  rewrite neg_w_rule_ptree_formula_true. simpl. destruct X4. auto. rewrite X1. simpl. destruct (and_bool_prop _ _ Y) as [Y1 Y2]. destruct (and_bool_prop _ _ Y1) as [Y3 Y4]. rewrite Y2,Y3,Y4. auto.
      --  apply add_left_non_decr.
- simpl. inversion H as [[[X1 X2] X3] X4]. destruct S; simpl; auto.
  + apply add_left_non_decr.
  + apply add_left_non_decr.
  + destruct S1; simpl; auto.
    * apply add_left_non_decr.
    * apply add_left_non_decr.
    * case (subst_ind_fit f0 S1_1 && subst_ind_fit f S1_2 && subst_ind_fit f1 S2) eqn:Y.
      --  rewrite neg_w_rule_ptree_formula_true. simpl. destruct X4. auto. rewrite X1. simpl. destruct (and_bool_prop _ _ Y) as [Y1 Y2]. destruct (and_bool_prop _ _ Y1) as [Y3 Y4]. rewrite Y2,Y3,Y4. auto.
      --  apply add_left_non_decr.
- simpl. inversion H as [[[X1 X2] X3] X4]. destruct S; simpl; auto.
  + apply add_left_non_decr.
  + apply add_left_non_decr.
  + destruct S1; simpl; auto.
    * apply add_left_non_decr.
    * apply add_left_non_decr.
    * destruct S1_1.
      --  apply add_left_non_decr.
      --  apply add_left_non_decr.
      --  case (subst_ind_fit f S1_1_1 && subst_ind_fit f1 S1_1_2 && subst_ind_fit f0 S1_2 && subst_ind_fit f2 S2) eqn:Y.
          ++  rewrite neg_w_rule_ptree_formula_true. simpl. destruct X4. auto. rewrite X1. simpl. destruct (and_bool_prop _ _ Y) as [Y1 Y3]. destruct (and_bool_prop _ _ Y1) as [Y2 Y4]. destruct (and_bool_prop _ _ Y2) as [Y5 Y6]. rewrite Y3,Y4,Y5,Y6. auto.
          ++  apply add_left_non_decr.
- simpl. inversion H as [[[X1 X2] X3] X4]. case (subst_ind_fit f S) eqn:Y.
  + simpl. rewrite neg_w_rule_ptree_formula_true. destruct X4. auto. rewrite X1. simpl. rewrite Y. auto.
  + apply add_left_non_decr.
- simpl. inversion H as [[[X1 X2] X3] X4]. destruct S; simpl; auto.
  + apply add_left_non_decr.
  + apply add_left_non_decr.
  + case (subst_ind_fit f S1 && subst_ind_fit f0 S2) eqn:Y.
    * simpl. rewrite neg_w_rule_ptree_formula_true. destruct X4. auto. rewrite X1. simpl. destruct (and_bool_prop _ _ Y) as [Y1 Y2]. rewrite Y1,Y2. auto.
    * apply add_left_non_decr.
- simpl. inversion H as [[[[X0 X1] X2] X3] X4]. destruct S; simpl; auto.
  + apply add_left_non_decr.
  + apply add_left_non_decr.
  + case (subst_ind_fit f S1 && subst_ind_fit f0 S2) eqn:Y.
    * simpl. rewrite neg_w_rule_ptree_formula_true. rewrite X4. auto. rewrite ord_succ_add_succ.
      --  apply ord_ltb_succ_false. auto.
      --  destruct HQ as [[[Q1 Q2] Q3] Q4]. destruct Q4. apply ptree_ord_nf. auto.
      --  apply ptree_ord_nf. auto.
      --  rewrite X0. destruct (and_bool_prop _ _ Y) as [Y1 Y2]. rewrite Y2. auto.
    * apply add_left_non_decr.
- simpl. inversion H as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. inversion HQ as [[[Q1 Q2] Q3] Q4]. rewrite X7,X8. destruct Q4.
  assert (nf (ord_max (ptree_ord P1) (ptree_ord P2))). apply ord_max_nf; apply ptree_ord_nf; auto.
  rewrite ord_succ_add_succ; try apply ptree_ord_nf; auto. destruct S; simpl; auto; apply ord_ltb_succ_false; apply add_left_non_decr.
- simpl. inversion H as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. inversion HQ as [[[Q1 Q2] Q3] Q4]. rewrite X7,X8. destruct Q4.
  assert (nf (ord_max (ptree_ord P1) (ptree_ord P2))). apply ord_max_nf; apply ptree_ord_nf; auto.
  rewrite ord_succ_add_succ; try apply ptree_ord_nf; auto. destruct S; simpl; auto; try destruct S1; simpl; try case (subst_ind_fit f1 S2) eqn:Y; try apply ord_ltb_succ_false; try apply add_left_non_decr;
  repeat rewrite neg_w_rule_ptree_formula_true; auto; try rewrite X1; try rewrite X3; simpl; auto.
  + rewrite ord_max_add_comm. apply ord_max_split_false; auto.
  + rewrite ord_max_add_comm. apply ord_max_split_false; auto.
- simpl. inversion H as [[[X1 X2] X3] X4]. inversion HQ as [[[Q1 Q2] Q3] Q4]. rewrite X4. destruct Q4. destruct S; simpl; auto; rewrite ord_succ_add_succ; try apply ord_ltb_succ_false; try apply add_left_non_decr; apply ptree_ord_nf; auto.
- simpl. inversion H as [[[X1 X2] X3] X4]. destruct S; simpl; auto.
  + apply add_left_non_decr.
  + apply add_left_non_decr.
  + destruct HQ as [[[Q1 Q2] Q3] Q4]. destruct Q4. rewrite X4. rewrite ord_succ_add_succ; try apply ptree_ord_nf; auto.
    destruct S1; simpl; case (subst_ind_fit f0 S2) eqn:Y; simpl; auto; apply ord_ltb_succ_false; try apply add_left_non_decr;
    rewrite neg_w_rule_ptree_formula_true; auto; rewrite X1; simpl; rewrite non_target_fit; auto.
- simpl. inversion H as [[[X1 X2] X3] X4]. inversion HQ as [[[Q1 Q2] Q3] Q4]. rewrite X4. destruct Q4. rewrite ord_succ_add_succ; try apply ptree_ord_nf; auto.
  destruct S; simpl; case (eq_f f E); simpl; case (eq_nat n0 n); simpl; auto; apply ord_ltb_succ_false; try apply add_left_non_decr. apply ord_max_le_add; apply ptree_ord_nf; auto.
- simpl. inversion H as [[[X1 X2] X3] X4]. inversion HQ as [[[Q1 Q2] Q3] Q4]. rewrite X4. destruct Q4. rewrite ord_succ_add_succ; try apply ptree_ord_nf; auto.
  destruct S; simpl; try destruct S1; simpl; case (eq_f f E); simpl; try case (subst_ind_fit f0 S2) eqn:Y; simpl; case (eq_nat n0 n); simpl; auto; apply ord_ltb_succ_false; try apply add_left_non_decr; rewrite neg_w_rule_ptree_formula_true; auto; try rewrite X1; simpl; auto.
  destruct (ord_semiconnex_bool (ptree_ord Q) (ptree_ord (neg_w_rule_sub_ptree P Q E F n d' (ptree_ord Q) HQ (lor_ind (0) S2)))) as [Y1 | [Y1 |Y1]].
  + rewrite ord_max_lem1; auto.
  + rewrite (ord_max_lem2 _ _ (ltb_asymm _ _ Y1)); auto. apply add_right_non_decr.
  + apply ord_eqb_eq in Y1. destruct Y1. rewrite (ord_max_lem2 _ _ (ord_ltb_irrefl _)); auto. apply add_right_non_decr.
- simpl. destruct (H czero) as [[[X1 X2] X3] X4]. inversion HQ as [[[Q1 Q2] Q3] Q4]. fold valid in *. rewrite X4. destruct Q4. destruct S; simpl; auto; rewrite ord_succ_add_succ; try apply ord_ltb_succ_false; try apply add_left_non_decr; apply ptree_ord_nf; auto.
- simpl. destruct (H czero) as [[[X1 X2] X3] X4]. fold valid in *. destruct S; simpl; auto.
  + apply add_left_non_decr.
  + apply add_left_non_decr.
  + destruct HQ as [[[Q1 Q2] Q3] Q4]. destruct Q4. rewrite X4. rewrite ord_succ_add_succ; try apply ptree_ord_nf; auto.
    destruct S1; simpl; case (subst_ind_fit f0 S2) eqn:Y; simpl; auto; apply ord_ltb_succ_false; try apply add_left_non_decr; apply ord_ltb_irrefl.
- simpl. inversion H as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. inversion HQ as [[[Q1 Q2] Q3] Q4]. rewrite X7,X8. destruct Q4.
    assert (nf (ord_max (ptree_ord P1) (ptree_ord P2))). apply ord_max_nf; apply ptree_ord_nf; auto.
    rewrite ord_succ_add_succ; try apply ptree_ord_nf; auto. case (subst_ind_fit f S) eqn:Y; simpl; apply ord_ltb_succ_false; try apply add_left_non_decr.
    repeat rewrite neg_w_rule_ptree_formula_true; auto; try rewrite X1; try rewrite X3; simpl; try rewrite Y; try apply non_target_fit.
    rewrite ord_max_add_comm. apply ord_max_split_false; auto. apply add_left_non_decr.
- simpl. inversion H as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. inversion HQ as [[[Q1 Q2] Q3] Q4]. rewrite X7,X8. destruct Q4.
  assert (nf (ord_max (ptree_ord P1) (ptree_ord P2))). apply ord_max_nf; apply ptree_ord_nf; auto.
  rewrite ord_succ_add_succ; try apply ptree_ord_nf; auto. case (subst_ind_fit f0 S) eqn:Y; simpl; apply ord_ltb_succ_false; try apply add_left_non_decr.
  repeat rewrite neg_w_rule_ptree_formula_true; auto; try rewrite X1; try rewrite X3; simpl; auto.
  rewrite ord_max_add_comm. apply ord_max_split_false; auto. apply add_left_non_decr.
- simpl. inversion H as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. inversion HQ as [[[Q1 Q2] Q3] Q4]. rewrite X7,X8. destruct Q4.
  assert (nf (ord_max (ptree_ord P1) (ptree_ord P2))). apply ord_max_nf; apply ptree_ord_nf; auto.
  rewrite ord_succ_add_succ; try apply ptree_ord_nf; auto. destruct S; simpl; auto; try case (subst_ind_fit f S1 && subst_ind_fit f1 S2) eqn:Y; try apply ord_ltb_succ_false; try apply add_left_non_decr;
  repeat rewrite neg_w_rule_ptree_formula_true; auto; try rewrite X1; try rewrite X3; simpl; auto; try destruct (and_bool_prop _ _ Y) as [Y1 Y2]; try rewrite Y1; auto; try apply non_target_fit.
  rewrite ord_max_add_comm. apply ord_max_split_false; auto.
Qed.

(*

Lemma neg_w_rule_ptree_ord_zero : forall (P Q : ptree) (E F : formula) (n d' : nat) (beta : ord) (H : P_proves Q (lor F (univ n E)) d' (ord_succ beta)),
  valid P -> (ptree_ord P) = Zero ->
  forall (S : subst_ind), ord_ltb (ord_add beta (ptree_ord P)) (ptree_ord (neg_w_rule_sub_ptree P Q E F n d' (ord_succ beta) H S)) = false.
Proof.
intros  P Q E F n d' beta HQ X ORD. induction P; simpl in ORD; intros S.
- simpl in *. destruct X as [X1 X2]. case (subst_ind_fit (ptree_formula P) S) eqn:Hfit; simpl; auto. case (lt_nat (ptree_deg (neg_w_rule_sub_ptree_fit P Q E F n d' (ord_succ beta) HQ S)) n0) eqn:Y; simpl; auto.
  + rewrite neg_w_rule_ptree_formula_true; auto.
  + rewrite neg_w_rule_ptree_formula_true; auto.
  + apply add_left_non_decr.
- simpl in *. destruct X as [[X1 X2] X3]. rewrite ORD in *. inversion X1.
- simpl.  case (subst_ind_fit f S) eqn:Hfit; simpl; auto; destruct beta; auto.
- destruct X as [[[X1 X2] X3] X4]. destruct S; simpl; auto.
  + apply add_left_non_decr.
  + apply add_left_non_decr.
  + rewrite ORD in *. case (subst_ind_fit f0 S1 && subst_ind_fit f S2) eqn:Y.
    * rewrite neg_w_rule_ptree_formula_true. simpl. destruct X4. auto. rewrite X1. simpl. destruct (and_bool_prop _ _ Y) as [Y1 Y2]. rewrite Y1,Y2. auto.
    * apply add_left_non_decr.
- simpl. inversion X as [[[X1 X2] X3] X4]. destruct S; simpl; auto.
  + apply add_left_non_decr.
  + apply add_left_non_decr.
  + destruct S1; simpl; auto.
    * apply add_left_non_decr.
    * apply add_left_non_decr.
    * case (subst_ind_fit f S1_1 && subst_ind_fit f1 S1_2 && subst_ind_fit f0 S2) eqn:Y.
      --  rewrite neg_w_rule_ptree_formula_true. simpl. destruct X4. auto. rewrite X1. simpl. destruct (and_bool_prop _ _ Y) as [Y1 Y2]. destruct (and_bool_prop _ _ Y1) as [Y3 Y4]. rewrite Y2,Y3,Y4. auto.
      --  apply add_left_non_decr.
- simpl. inversion X as [[[X1 X2] X3] X4]. destruct S; simpl; auto.
  + apply add_left_non_decr.
  + apply add_left_non_decr.
  + destruct S1; simpl; auto.
    * apply add_left_non_decr.
    * apply add_left_non_decr.
    * case (subst_ind_fit f0 S1_1 && subst_ind_fit f S1_2 && subst_ind_fit f1 S2) eqn:Y.
      --  rewrite neg_w_rule_ptree_formula_true. simpl. destruct X4. auto. rewrite X1. simpl. destruct (and_bool_prop _ _ Y) as [Y1 Y2]. destruct (and_bool_prop _ _ Y1) as [Y3 Y4]. rewrite Y2,Y3,Y4. auto.
      --  apply add_left_non_decr.
- simpl. inversion X as [[[X1 X2] X3] X4]. destruct S; simpl; auto.
  + apply add_left_non_decr.
  + apply add_left_non_decr.
  + destruct S1; simpl; auto.
    * apply add_left_non_decr.
    * apply add_left_non_decr.
    * destruct S1_1.
      --  apply add_left_non_decr.
      --  apply add_left_non_decr.
      --  case (subst_ind_fit f S1_1_1 && subst_ind_fit f1 S1_1_2 && subst_ind_fit f0 S1_2 && subst_ind_fit f2 S2) eqn:Y.
          ++  rewrite neg_w_rule_ptree_formula_true. simpl. destruct X4. auto. rewrite X1. simpl. destruct (and_bool_prop _ _ Y) as [Y1 Y3]. destruct (and_bool_prop _ _ Y1) as [Y2 Y4]. destruct (and_bool_prop _ _ Y2) as [Y5 Y6]. rewrite Y3,Y4,Y5,Y6. auto.
          ++  apply add_left_non_decr.
- simpl. inversion X as [[[X1 X2] X3] X4]. case (subst_ind_fit f S) eqn:Y.
  + simpl. rewrite neg_w_rule_ptree_formula_true. destruct X4. auto. rewrite X1. simpl. rewrite Y. auto.
  + apply add_left_non_decr.
- simpl. inversion X as [[[X1 X2] X3] X4]. destruct S; simpl; auto.
  + apply add_left_non_decr.
  + apply add_left_non_decr.
  + case (subst_ind_fit f S1 && subst_ind_fit f0 S2) eqn:Y.
    * simpl. rewrite neg_w_rule_ptree_formula_true. destruct X4. auto. rewrite X1. simpl. destruct (and_bool_prop _ _ Y) as [Y1 Y2]. rewrite Y1,Y2. auto.
    * apply add_left_non_decr.
- pose proof (ord_succ_non_Zero o) as BAD. rewrite ORD in BAD. inversion BAD.
- pose proof (ord_succ_non_Zero (ord_max o o0)) as BAD. rewrite ORD in BAD. inversion BAD.
- pose proof (ord_succ_non_Zero (ord_max o o0)) as BAD. rewrite ORD in BAD. inversion BAD.
- pose proof (ord_succ_non_Zero o) as BAD. rewrite ORD in BAD. inversion BAD.
- pose proof (ord_succ_non_Zero o) as BAD. rewrite ORD in BAD. inversion BAD.
- pose proof (ord_succ_non_Zero o) as BAD. rewrite ORD in BAD. inversion BAD.
- pose proof (ord_succ_non_Zero o) as BAD. rewrite ORD in BAD. inversion BAD.
- pose proof (ord_succ_non_Zero o) as BAD. rewrite ORD in BAD. inversion BAD.
- pose proof (ord_succ_non_Zero o) as BAD. rewrite ORD in BAD. inversion BAD.
- pose proof (ord_succ_non_Zero (ord_max o o0)) as BAD. rewrite ORD in BAD. inversion BAD.
- pose proof (ord_succ_non_Zero (ord_max o o0)) as BAD. rewrite ORD in BAD. inversion BAD.
- pose proof (ord_succ_non_Zero (ord_max o o0)) as BAD. rewrite ORD in BAD. inversion BAD.
Qed.

Lemma neg_w_rule_ptree_ord_small : forall (P Q : ptree) (E F : formula) (n d' : nat) (beta : ord) (H : P_proves Q (lor F (univ n E)) d' (ord_succ beta)),
  valid P -> (ord_lt Zero (ptree_ord P)) ->
  forall (S : subst_ind), ord_ltb (ord_add beta (ptree_ord P)) (ptree_ord (neg_w_rule_sub_ptree P Q E F n d' (ord_succ beta) H S)) = false.
Proof.
intros P Q E F n d' beta HQ H I. assert (nf beta). { destruct HQ as [[[Q1 Q2] Q3] Q4]. apply ord_nf_succ. destruct Q4. apply ptree_ord_nf. auto. } induction P; intros S.
- simpl. inversion H as [X1 X2]. case (subst_ind_fit (ptree_formula P) S) eqn:Hfit; simpl; auto. case (lt_nat (ptree_deg (neg_w_rule_sub_ptree_fit P Q E F n d' (ord_succ beta) HQ S)) n0) eqn:X; simpl; auto.
  + rewrite neg_w_rule_ptree_formula_true; auto.
  + rewrite neg_w_rule_ptree_formula_true; auto.
  + apply add_left_non_decr.
- simpl. inversion H as [[X1 X2] X3]. case (subst_ind_fit (ptree_formula P) S) eqn:Hfit; simpl; auto. case (ord_ltb (ptree_ord (neg_w_rule_sub_ptree_fit P Q E F n d' (ord_succ beta) HQ S)) o) eqn:X; simpl; auto.
  + apply add_left_non_decr.
  + rewrite neg_w_rule_ptree_formula_true; auto.  apply (ord_trans_inv _ (ord_add beta (ptree_ord P))); auto. apply ltb_asymm. apply ord_lt_ltb. apply add_right_incr. auto. case (ptree_ord P) eqn:ORD.
    * destruct H as [[Y1 Y2] Y3]. rewrite <- ORD. apply neg_w_rule_ptree_ord_zero; auto. 
    * apply IHP. auto. apply zero_lt.
  + apply add_left_non_decr.
- simpl. destruct beta; case (subst_ind_fit f S); auto.
- simpl. inversion H as [[[X1 X2] X3] X4]. destruct S; simpl; auto.
  + apply add_left_non_decr.
  + apply add_left_non_decr.
  + case (subst_ind_fit f0 S1 && subst_ind_fit f S2) eqn:Y.
    * rewrite neg_w_rule_ptree_formula_true. simpl. destruct X4. auto. rewrite X1. simpl. destruct (and_bool_prop _ _ Y) as [Y1 Y2]. rewrite Y1,Y2. auto.
    * apply add_left_non_decr.
- simpl. inversion H as [[[X1 X2] X3] X4]. destruct S; simpl; auto.
  + apply add_left_non_decr.
  + apply add_left_non_decr.
  + destruct S1; simpl; auto.
    * apply add_left_non_decr.
    * apply add_left_non_decr.
    * case (subst_ind_fit f S1_1 && subst_ind_fit f1 S1_2 && subst_ind_fit f0 S2) eqn:Y.
      --  rewrite neg_w_rule_ptree_formula_true. simpl. destruct X4. auto. rewrite X1. simpl. destruct (and_bool_prop _ _ Y) as [Y1 Y2]. destruct (and_bool_prop _ _ Y1) as [Y3 Y4]. rewrite Y2,Y3,Y4. auto.
      --  apply add_left_non_decr.
- simpl. inversion H as [[[X1 X2] X3] X4]. destruct S; simpl; auto.
  + apply add_left_non_decr.
  + apply add_left_non_decr.
  + destruct S1; simpl; auto.
    * apply add_left_non_decr.
    * apply add_left_non_decr.
    * case (subst_ind_fit f0 S1_1 && subst_ind_fit f S1_2 && subst_ind_fit f1 S2) eqn:Y.
      --  rewrite neg_w_rule_ptree_formula_true. simpl. destruct X4. auto. rewrite X1. simpl. destruct (and_bool_prop _ _ Y) as [Y1 Y2]. destruct (and_bool_prop _ _ Y1) as [Y3 Y4]. rewrite Y2,Y3,Y4. auto.
      --  apply add_left_non_decr.
- simpl. inversion H as [[[X1 X2] X3] X4]. destruct S; simpl; auto.
  + apply add_left_non_decr.
  + apply add_left_non_decr.
  + destruct S1; simpl; auto.
    * apply add_left_non_decr.
    * apply add_left_non_decr.
    * destruct S1_1.
      --  apply add_left_non_decr.
      --  apply add_left_non_decr.
      --  case (subst_ind_fit f S1_1_1 && subst_ind_fit f1 S1_1_2 && subst_ind_fit f0 S1_2 && subst_ind_fit f2 S2) eqn:Y.
          ++  rewrite neg_w_rule_ptree_formula_true. simpl. destruct X4. auto. rewrite X1. simpl. destruct (and_bool_prop _ _ Y) as [Y1 Y3]. destruct (and_bool_prop _ _ Y1) as [Y2 Y4]. destruct (and_bool_prop _ _ Y2) as [Y5 Y6]. rewrite Y3,Y4,Y5,Y6. auto.
          ++  apply add_left_non_decr.
- simpl. inversion H as [[[X1 X2] X3] X4]. case (subst_ind_fit f S) eqn:Y.
  + simpl. rewrite neg_w_rule_ptree_formula_true. destruct X4. auto. rewrite X1. simpl. rewrite Y. auto.
  + apply add_left_non_decr.
- simpl. inversion H as [[[X1 X2] X3] X4]. destruct S; simpl; auto.
  + apply add_left_non_decr.
  + apply add_left_non_decr.
  + case (subst_ind_fit f S1 && subst_ind_fit f0 S2) eqn:Y.
    * simpl. rewrite neg_w_rule_ptree_formula_true. destruct X4. auto. rewrite X1. simpl. destruct (and_bool_prop _ _ Y) as [Y1 Y2]. rewrite Y1,Y2. auto.
    * apply add_left_non_decr.
- simpl. inversion H as [[[[X0 X1] X2] X3] X4]. destruct S; simpl; auto.
  + apply add_left_non_decr.
  + apply add_left_non_decr.
  + case (subst_ind_fit f S1 && subst_ind_fit f0 S2) eqn:Y.
    * simpl. rewrite neg_w_rule_ptree_formula_true. rewrite X4. auto. rewrite ord_succ_add_succ.
      --  apply ord_ltb_succ_false. auto. simpl in I. destruct o.
          ++  apply neg_w_rule_ptree_ord_zero; auto.
          ++  apply IHP; auto. destruct X4. apply zero_lt.
      --  destruct HQ as [[[Q1 Q2] Q3] Q4]. apply ord_nf_succ. destruct Q4. apply ptree_ord_nf. auto.
      --  apply ptree_ord_nf. auto.
      --  rewrite X0. destruct (and_bool_prop _ _ Y) as [Y1 Y2]. rewrite Y2. auto.
    * apply add_left_non_decr.
- simpl. inversion H as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. inversion HQ as [[[Q1 Q2] Q3] Q4]. rewrite X7,X8. destruct Q4.
  assert (nf (ord_max (ptree_ord P1) (ptree_ord P2))). apply ord_max_nf; apply ptree_ord_nf; auto.
  rewrite ord_succ_add_succ; try apply ptree_ord_nf; auto. destruct S; simpl; auto; apply ord_ltb_succ_false; apply add_left_non_decr.
- simpl. inversion H as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. inversion HQ as [[[Q1 Q2] Q3] Q4]. rewrite X7,X8.
  assert (nf (ord_max (ptree_ord P1) (ptree_ord P2))). apply ord_max_nf; apply ptree_ord_nf; auto.
  rewrite ord_succ_add_succ; try apply ptree_ord_nf; auto. destruct S; simpl; auto; try destruct S1; simpl; try case (subst_ind_fit f1 S2) eqn:Y; try apply ord_ltb_succ_false; try apply add_left_non_decr;
  repeat rewrite neg_w_rule_ptree_formula_true; auto; try rewrite X1; try rewrite X3; simpl; auto.
  + rewrite ord_max_add_comm. apply ord_max_split_false; auto.
    * simpl in I. destruct o.
      ++  apply neg_w_rule_ptree_ord_zero; auto.
      ++  apply IHP1; auto. destruct X7. apply zero_lt.
    * simpl in I. destruct o0.
      ++  apply neg_w_rule_ptree_ord_zero; auto.
      ++  apply IHP2; auto. destruct X8. apply zero_lt.
  + rewrite ord_max_add_comm. apply ord_max_split_false; auto.
    * simpl in I. destruct o.
      ++  apply neg_w_rule_ptree_ord_zero; auto.
      ++  apply IHP1; auto. destruct X7. apply zero_lt.
    * simpl in I. destruct o0.
      ++  apply neg_w_rule_ptree_ord_zero; auto.
      ++  apply IHP2; auto. destruct X8. apply zero_lt.
- simpl. inversion H as [[[X1 X2] X3] X4]. rewrite X4. destruct S; simpl; auto; rewrite ord_succ_add_succ; try apply ord_ltb_succ_false; try apply add_left_non_decr; try apply ptree_ord_nf; auto.
- simpl. inversion H as [[[X1 X2] X3] X4]. destruct S; simpl; auto.
  + apply add_left_non_decr.
  + apply add_left_non_decr.
  + rewrite X4. simpl in I. rewrite ord_succ_add_succ; try apply ptree_ord_nf; auto.
    destruct S1; simpl; case (subst_ind_fit f0 S2) eqn:Y; simpl; auto; apply ord_ltb_succ_false; try apply add_left_non_decr;
    rewrite neg_w_rule_ptree_formula_true; auto; try rewrite X1; simpl; try rewrite non_target_fit; auto; destruct o.
    * apply neg_w_rule_ptree_ord_zero; auto.
    * apply IHP; auto. destruct X4. apply zero_lt.
    * apply neg_w_rule_ptree_ord_zero; auto.
    * apply IHP; auto. destruct X4. apply zero_lt.
- simpl. inversion H as [[[X1 X2] X3] X4]. rewrite X4. rewrite ord_succ_add_succ; try apply ptree_ord_nf; auto.
  destruct S; simpl; case (eq_f f E); simpl; case (eq_nat n0 n); simpl; auto; apply ord_ltb_succ_false; try apply add_left_non_decr. (* apply ord_max_le_add; apply ptree_ord_nf; auto. *) admit.
(*
  - simpl. inversion H as [[[X1 X2] X3] X4]. inversion HQ as [[[Q1 Q2] Q3] Q4]. rewrite X4. destruct Q4. rewrite ord_succ_add_succ; try apply ptree_ord_nf; auto.
  destruct S; simpl; try destruct S1; simpl; case (eq_f f E); simpl; try case (subst_ind_fit f0 S2) eqn:Y; simpl; case (eq_nat n0 n); simpl; auto; apply ord_ltb_succ_false; try apply add_left_non_decr; rewrite neg_w_rule_ptree_formula_true; auto; try rewrite X1; simpl; auto.
  destruct (ord_semiconnex_bool (ptree_ord Q) (ptree_ord (neg_w_rule_sub_ptree P Q E F n d' (ptree_ord Q) HQ (lor_ind (0) S2)))) as [Y1 | [Y1 |Y1]].
  + rewrite ord_max_lem1; auto.
  + rewrite (ord_max_lem2 _ _ (ltb_asymm _ _ Y1)); auto. apply add_right_non_decr.
  + apply ord_eqb_eq in Y1. destruct Y1. rewrite (ord_max_lem2 _ _ (ord_ltb_irrefl _)); auto. apply add_right_non_decr.
  *)
- admit.
- simpl. destruct (H czero) as [[[X1 X2] X3] X4]. inversion HQ as [[[Q1 Q2] Q3] Q4]. fold valid in *. rewrite X4. destruct S; simpl; auto; rewrite ord_succ_add_succ; try apply ord_ltb_succ_false; try apply add_left_non_decr; try apply ptree_ord_nf; auto.
- simpl. destruct (H czero) as [[[X1 X2] X3] X4]. fold valid in *. destruct S; simpl; auto.
  + apply add_left_non_decr.
  + apply add_left_non_decr.
  + destruct HQ as [[[Q1 Q2] Q3] Q4]. rewrite X4. rewrite ord_succ_add_succ; try apply ptree_ord_nf; auto.
    destruct S1; simpl; case (subst_ind_fit f0 S2) eqn:Y; simpl; auto; apply ord_ltb_succ_false; try apply add_left_non_decr; try apply ord_ltb_irrefl; destruct o.
    * apply neg_w_rule_ptree_ord_zero; auto.
    * apply IHP; auto. destruct X4. apply zero_lt.
    * apply neg_w_rule_ptree_ord_zero; auto.
    * apply IHP; auto. destruct X4. apply zero_lt.
- simpl. inversion H as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. inversion HQ as [[[Q1 Q2] Q3] Q4]. rewrite X7,X8. destruct Q4.
    assert (nf (ord_max (ptree_ord P1) (ptree_ord P2))). apply ord_max_nf; apply ptree_ord_nf; auto.
    rewrite ord_succ_add_succ; try apply ptree_ord_nf; auto. case (subst_ind_fit f S) eqn:Y; simpl; apply ord_ltb_succ_false; try apply add_left_non_decr.
    repeat rewrite neg_w_rule_ptree_formula_true; auto; try rewrite X1; try rewrite X3; simpl; try rewrite Y; try apply non_target_fit.
    rewrite ord_max_add_comm. apply ord_max_split_false; auto. apply add_left_non_decr.
- simpl. inversion H as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. inversion HQ as [[[Q1 Q2] Q3] Q4]. rewrite X7,X8. destruct Q4.
  assert (nf (ord_max (ptree_ord P1) (ptree_ord P2))). apply ord_max_nf; apply ptree_ord_nf; auto.
  rewrite ord_succ_add_succ; try apply ptree_ord_nf; auto. case (subst_ind_fit f0 S) eqn:Y; simpl; apply ord_ltb_succ_false; try apply add_left_non_decr.
  repeat rewrite neg_w_rule_ptree_formula_true; auto; try rewrite X1; try rewrite X3; simpl; auto.
  rewrite ord_max_add_comm. apply ord_max_split_false; auto. apply add_left_non_decr.
- simpl. inversion H as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. inversion HQ as [[[Q1 Q2] Q3] Q4]. rewrite X7,X8. destruct Q4.
  assert (nf (ord_max (ptree_ord P1) (ptree_ord P2))). apply ord_max_nf; apply ptree_ord_nf; auto.
  rewrite ord_succ_add_succ; try apply ptree_ord_nf; auto. destruct S; simpl; auto; try case (subst_ind_fit f S1 && subst_ind_fit f1 S2) eqn:Y; try apply ord_ltb_succ_false; try apply add_left_non_decr;
  repeat rewrite neg_w_rule_ptree_formula_true; auto; try rewrite X1; try rewrite X3; simpl; auto; try destruct (and_bool_prop _ _ Y) as [Y1 Y2]; try rewrite Y1; auto; try apply non_target_fit.
  rewrite ord_max_add_comm. apply ord_max_split_false; auto.
Qed.
*)


(* Now we prove that if we have a valid ptree, performing our
w_rule substitution on it results in a valid ptree *)
(* *)
Lemma neg_w_rule_valid : forall (P Q : ptree) (E F : formula) (n d' : nat) (beta : ord) (H : P_proves Q (lor F (univ n E)) d' beta),
  valid P -> closed F = true -> Nat.max d' (ptree_deg P) < (num_conn E + 2) ->
  forall (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    valid (neg_w_rule_sub_ptree P Q E F n d' beta H S).
Proof.
intros P Q E F n d' beta HQ.
induction P; try intros H HF HD S Hs.

- simpl. inversion H as [H1 H2]. inversion Hs. rewrite H3. assert (Nat.max d' (ptree_deg P) < num_conn E + 2). simpl in HD. lia.
  case (lt_nat (ptree_deg (neg_w_rule_sub_ptree P Q E F n d' beta HQ S)) n0) eqn:X.
  + rewrite neg_w_rule_ptree_formula_true; auto. rewrite X. split.
    * apply lt_nat_decid. auto.
    * apply (IHP H2 HF H0 S H3).
  + rewrite neg_w_rule_ptree_formula_true; auto. rewrite X. apply (IHP H2 HF H0 S H3).

- simpl. inversion H as [[H1 H2] H3]. inversion Hs. rewrite H4.
  rewrite neg_w_rule_ptree_formula_true; auto. case (ord_ltb (ptree_ord (neg_w_rule_sub_ptree P Q E F n d' beta HQ S)) o) eqn:X.
  + repeat split; auto. apply ord_ltb_lt. auto.
  + auto.

- simpl. destruct (subst_ind_fit f S); apply H.

- simpl. simpl in HD. destruct S; inversion Hs. rewrite H1. simpl.
  inversion H as [[[H2 H3] H4] H5]. rewrite H4 in *.
  repeat split; rewrite neg_w_rule_ptree_formula_true; auto.
  + rewrite neg_w_rule_ptree_formula; auto.
    rewrite H2. unfold neg_w_rule_sub_formula.
    rewrite formula_sub_ind_lor; auto. apply (and_bool_symm _ _ H1).
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + apply IHP; auto. rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).

- simpl. simpl in HD. destruct S; try destruct S1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H4 H5] H6] H7]. rewrite H6 in *.
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  repeat split; rewrite neg_w_rule_ptree_formula_true.
  + rewrite neg_w_rule_ptree_formula; auto.
    rewrite H4. unfold neg_w_rule_sub_formula.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H1, H2. auto.
    * simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + apply IHP; auto. rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.

- simpl. simpl in HD. destruct S; try destruct S1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H4 H5] H6] H7]. rewrite H6 in *.
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  repeat split; rewrite neg_w_rule_ptree_formula_true.
  + rewrite neg_w_rule_ptree_formula; auto.
    rewrite H4. unfold neg_w_rule_sub_formula.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H1, H3. auto.
    * simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + apply IHP; auto. rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.

- simpl. simpl in HD. destruct S; try destruct S1; try destruct S1_1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H5 H6] H7] H8]. rewrite H7 in *.
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  destruct (and_bool_prop _ _ H1). clear H1.
  repeat split; rewrite neg_w_rule_ptree_formula_true.
  + rewrite neg_w_rule_ptree_formula; auto.
    rewrite H5. unfold neg_w_rule_sub_formula.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H0,H3. auto.
    * simpl. rewrite H0, H3, H4. auto.
    * simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + apply IHP; auto. rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.

- simpl. simpl in HD. inversion Hs. rewrite H1. inversion H as [[[H2 H3] H4] H5]. rewrite H4 in *.
  repeat split; rewrite neg_w_rule_ptree_formula_true.
  + rewrite neg_w_rule_ptree_formula; auto.
    unfold neg_w_rule_sub_formula. rewrite H2.
    rewrite formula_sub_ind_lor; auto. rewrite H1. auto.
  + rewrite H2. simpl. rewrite H1. auto.
  + apply IHP; auto. rewrite H2. simpl. rewrite H1. auto.
  + rewrite H2. simpl. rewrite H1. auto.

- simpl. simpl in HD. destruct S; inversion Hs. rewrite H1.
  inversion H as [[[H2 H3] H4] H5]. rewrite H4 in *. destruct (and_bool_prop _ _ H1).
  repeat split; rewrite neg_w_rule_ptree_formula_true.
  + rewrite neg_w_rule_ptree_formula; auto.
    unfold neg_w_rule_sub_formula. rewrite H2.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H0. auto.
    * simpl. rewrite H0, H6. auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + apply IHP; auto. rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.

- simpl. simpl in HD. destruct S; inversion Hs. rewrite H1. simpl.
  inversion H as [[[[H2 H3] H4] H5] H6]. rewrite H5 in *. destruct (and_bool_prop _ _ H1).
  repeat split.
  + rewrite neg_w_rule_ptree_formula_true.
    * rewrite neg_w_rule_ptree_formula; auto. rewrite H2. auto.
    * rewrite H2. auto.
  + apply neg_w_rule_sub_formula_closed; auto.
  + rewrite neg_w_rule_ptree_formula_true.
    * apply IHP; auto. rewrite H2. auto.
    * rewrite H2. auto.

- simpl. destruct S; apply H.

- simpl. simpl in HD. assert (Nat.max d' n0 < num_conn E + 2) as HD1. lia. assert (Nat.max d' n1 < num_conn E + 2) as HD2. lia. destruct S; try apply H.
  destruct S1; inversion Hs; rewrite H1; simpl.
  + destruct H as [[[[[[[H2 H3] H4] H5] H6] H7] H8] H9]. rewrite H6,H7 in*.
    repeat split; rewrite neg_w_rule_ptree_formula_true.
    * rewrite neg_w_rule_ptree_formula; auto.
      rewrite H2. unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_lor.
      { simpl. destruct (eq_f f (univ n E)); auto. }
      { rewrite H1. auto. }
    * rewrite H2. simpl. apply H1.
    * apply IHP1; auto. rewrite H2. apply H1.
    * rewrite H2. simpl. apply H1.
    * rewrite neg_w_rule_ptree_formula; auto.
      rewrite H4. unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_lor.
      { simpl. destruct (eq_f f0 (univ n E)); auto. }
      { rewrite H1. auto. }
    * rewrite H4. simpl. apply H1.
    * apply IHP2; auto. rewrite H4. simpl. apply H1.
    * rewrite H4. simpl. apply H1.
  + destruct H as [[[[[[[H2 H3] H4] H5] H6] H7] H8] H9]. rewrite H6,H7 in*.
    repeat split; rewrite neg_w_rule_ptree_formula_true.
    * rewrite neg_w_rule_ptree_formula; auto.
      rewrite H2. unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_lor.
      { simpl. destruct (eq_f f (univ n E)); auto. }
      { rewrite H1. auto. }
    * rewrite H2. simpl. apply H1.
    * apply IHP1; auto. rewrite H2. apply H1.
    * rewrite H2. simpl. apply H1.
    * rewrite neg_w_rule_ptree_formula; auto.
      rewrite H4. unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_lor.
      { simpl. destruct (eq_f f0 (univ n E)); auto. }
      { rewrite H1. auto. }
    * rewrite H4. simpl. apply H1.
    * apply IHP2; auto. rewrite H4. simpl. apply H1.
    * rewrite H4. simpl. apply H1.

- simpl. destruct S; destruct (eq_f f E); apply H.

- simpl. simpl in HD. inversion H as [[[H1 H2] H3] H4]. rewrite H3 in *. destruct S; auto.
  destruct S1; auto; destruct (subst_ind_fit f0 S2) eqn:HS2; simpl;
  repeat split; auto; rewrite neg_w_rule_ptree_formula_true;
  try apply IHP; auto; try rewrite H1; simpl; try rewrite non_target_fit,HS2;
  try rewrite w_rule_ptree_deg; try rewrite w_rule_ptree_ord; auto.
  + rewrite neg_w_rule_ptree_formula; auto. rewrite H1.
    unfold neg_w_rule_sub_formula. simpl. rewrite non_target_fit,HS2.
    simpl. rewrite <- sub_fit_true; auto.
    * rewrite non_target_sub. rewrite <- sub_fit_true; auto.
    * apply non_target_fit.
  + rewrite neg_w_rule_ptree_formula; auto. rewrite H1.
    unfold neg_w_rule_sub_formula. simpl. rewrite non_target_fit,HS2.
    simpl. rewrite <- sub_fit_true; auto.
    * rewrite non_target_sub. rewrite <- sub_fit_true; auto.
    * apply non_target_fit.

- simpl. destruct S; auto; case (eq_f f E) eqn:X; case (eq_nat n0 n) eqn:X1; auto.
  apply f_eq_decid in X. destruct X. apply nat_eq_decid in X1. destruct X1.
  destruct H as [[[X1 X2] X3] X4]. destruct HQ as [[[Y1 Y2 ]Y3] Y4].
  repeat split; simpl; auto.
  + rewrite w_rule_ptree_formula; auto. rewrite Y1. unfold w_rule_sub_formula. simpl.
    rewrite non_target_fit. rewrite eq_nat_refl. rewrite eq_f_refl. simpl. rewrite non_target_sub'. auto. 
  + apply w_rule_valid; auto. rewrite Y1. simpl. rewrite non_target_fit. auto.
  + rewrite w_rule_ptree_ord; auto.

- simpl. simpl in HD. inversion H as [[[X1 X2] X3] X4]. destruct S; auto. destruct S1; simpl; auto; simpl in Hs; rewrite Hs;
  assert (subst_ind_fit (ptree_formula P) (lor_ind (0) S2) = true); try rewrite X1; auto; destruct (eq_f f E) eqn:Y; auto; destruct (eq_nat n0 n) eqn:Y1; auto.
  + repeat split; auto; rewrite neg_w_rule_ptree_formula_true; auto.
    * rewrite neg_w_rule_ptree_formula; auto. rewrite X1. unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_lor; auto. rewrite formula_sub_ind_0; auto.
    * apply IHP; auto. lia.
  + repeat split; auto; rewrite neg_w_rule_ptree_formula_true; auto.
    * rewrite neg_w_rule_ptree_formula; auto. rewrite X1. unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_lor; auto. rewrite formula_sub_ind_0; auto.
    * apply IHP; auto. lia.
  + repeat split; auto; rewrite neg_w_rule_ptree_formula_true; auto.
    * rewrite neg_w_rule_ptree_formula; auto. rewrite X1. unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_lor; auto. rewrite formula_sub_ind_0; auto.
    * apply IHP; auto. lia.
  + repeat split; auto; rewrite neg_w_rule_ptree_formula_true; auto.
    * rewrite neg_w_rule_ptree_formula; auto. rewrite X1. unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_lor; auto. rewrite formula_sub_ind_0; auto.
    * apply IHP; auto. lia.
  + unfold w_rule_invertible_cut_cad. destruct HQ. destruct p. destruct p. unfold "&&". destruct existT as [T [[[HT1 HT2] HT3] HT4]]. repeat split; simpl; auto; try rewrite neg_w_rule_ptree_formula_true; auto.
    * rewrite neg_w_rule_ptree_formula; auto. rewrite X1. apply f_eq_decid in Y. apply nat_eq_decid in Y1. destruct Y,Y1. unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_lor; auto. rewrite formula_sub_ind_0. auto.  
    * apply IHP; auto. lia.
  + repeat split; auto; rewrite neg_w_rule_ptree_formula_true; auto.
    * rewrite neg_w_rule_ptree_formula; auto. rewrite X1. unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_lor; auto. rewrite formula_sub_ind_0; auto.
    * apply IHP; auto. lia.
  + repeat split; auto; rewrite neg_w_rule_ptree_formula_true; auto.
    * rewrite neg_w_rule_ptree_formula; auto. rewrite X1. unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_lor; auto. rewrite formula_sub_ind_0; auto.
    * apply IHP; auto. lia.
  + repeat split; auto; rewrite neg_w_rule_ptree_formula_true; auto.
    * rewrite neg_w_rule_ptree_formula; auto. rewrite X1. unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_lor; auto. rewrite formula_sub_ind_0; auto.
    * apply IHP; auto. lia.

- simpl. destruct S; auto.

- simpl. simpl in HD. destruct S; try apply H. destruct S1; inversion Hs; rewrite H1; simpl; intros t; destruct (H t) as [[[X1 X2] X3] X4]; fold valid in *.
  + repeat split; auto; unfold weak_ord_up; case (ord_ltb (ptree_ord (neg_w_rule_sub_ptree_fit (p t) Q E F n d' beta HQ (lor_ind (non_target f) S2))) (ord_add beta o)) eqn:Y.
    * simpl. rewrite neg_w_rule_ptree_formula_true, neg_w_rule_ptree_formula; auto.
      --  rewrite X1. unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_lor.
          ++ rewrite (non_target_term_sub _ n0 (projT1 t)). rewrite non_target_sub. auto.
          ++ rewrite (non_target_term_sub _ n0 (projT1 t)). rewrite non_target_fit,H1. auto.
      --  rewrite X1. rewrite (non_target_term_sub _ n0 (projT1 t)). simpl. rewrite non_target_fit,H1. auto.
    * simpl. rewrite neg_w_rule_ptree_formula_true, neg_w_rule_ptree_formula; auto.
      --  rewrite X1. unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_lor.
          ++ rewrite (non_target_term_sub _ n0 (projT1 t)). rewrite non_target_sub. auto.
          ++ rewrite (non_target_term_sub _ n0 (projT1 t)). rewrite non_target_fit,H1. auto.
      --  rewrite X1. rewrite (non_target_term_sub _ n0 (projT1 t)). simpl. rewrite non_target_fit,H1. auto.  
    * repeat split; auto.
      --  apply ord_ltb_lt. auto.
      --  rewrite neg_w_rule_ptree_formula_true.
          ++  apply X; auto. lia. rewrite X1. rewrite (non_target_term_sub _ n0 (projT1 t)). simpl. rewrite non_target_fit,H1. auto.
          ++  rewrite X1. rewrite (non_target_term_sub _ n0 (projT1 t)). simpl. rewrite non_target_fit,H1. auto.
      --  apply nf_add. destruct HQ as [[[Q1 Q2] Q3] Q4]. destruct Q4. apply ptree_ord_nf. auto. rewrite X4. apply ptree_ord_nf. auto.
    * rewrite neg_w_rule_ptree_formula_true.
      --  apply X; auto. lia. rewrite X1. rewrite (non_target_term_sub _ n0 (projT1 t)). simpl. rewrite non_target_fit,H1. auto.
      --  rewrite X1. rewrite (non_target_term_sub _ n0 (projT1 t)). simpl. rewrite non_target_fit,H1. auto.
    * simpl. rewrite neg_w_rule_ptree_formula_true.
      --  assert (Nat.max d' (ptree_deg (p t)) < num_conn E + 2). lia. pose proof (neg_w_rule_ptree_deg (p t) Q E F n d' beta HQ X2 H0 (lor_ind (non_target f) S2)). lia.
      --  rewrite X1. simpl. rewrite (non_target_term_sub f n0 (projT1 t)). rewrite non_target_fit. auto.
    * simpl. rewrite neg_w_rule_ptree_formula_true.
      --  assert (Nat.max d' (ptree_deg (p t)) < num_conn E + 2). lia. pose proof (neg_w_rule_ptree_deg (p t) Q E F n d' beta HQ X2 H0 (lor_ind (non_target f) S2)). lia.
      --  rewrite X1. simpl. rewrite (non_target_term_sub f n0 (projT1 t)). rewrite non_target_fit. auto.
    * auto.
    * destruct (ord_semiconnex_bool (ptree_ord (neg_w_rule_sub_ptree_fit (p t) Q E F n d' beta HQ (lor_ind (non_target f) S2))) (ord_add beta o)) as [Y1 | [Y1 | Y1]].
      --  rewrite Y1 in Y. inversion Y.
      --  rewrite neg_w_rule_ptree_formula_true in Y1. rewrite X4 in Y1. rewrite neg_w_rule_ptree_ord in Y1. inversion Y1. auto. rewrite X1. simpl. rewrite (non_target_term_sub f n0 (projT1 t)). rewrite non_target_fit. auto.
      --  apply ord_eqb_eq in Y1. destruct Y1. auto.
  + repeat split; auto; unfold weak_ord_up; case (ord_ltb (ptree_ord (neg_w_rule_sub_ptree_fit (p t) Q E F n d' beta HQ (lor_ind (non_target f) S2))) (ord_add beta o)) eqn:Y.
    * simpl. rewrite neg_w_rule_ptree_formula_true, neg_w_rule_ptree_formula; auto.
      --  rewrite X1. unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_lor. 
          ++  rewrite (non_target_term_sub _ n0 (projT1 t)). rewrite non_target_sub. auto.
          ++  rewrite (non_target_term_sub _ n0 (projT1 t)). rewrite non_target_fit,H1. auto.
      --  rewrite X1. rewrite (non_target_term_sub _ n0 (projT1 t)). simpl. rewrite non_target_fit,H1. auto.
    * simpl. rewrite neg_w_rule_ptree_formula_true, neg_w_rule_ptree_formula; auto.
      --  rewrite X1. unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_lor. 
          ++  rewrite (non_target_term_sub _ n0 (projT1 t)). rewrite non_target_sub. auto.
          ++  rewrite (non_target_term_sub _ n0 (projT1 t)). rewrite non_target_fit,H1. auto.
      --  rewrite X1. rewrite (non_target_term_sub _ n0 (projT1 t)). simpl. rewrite non_target_fit,H1. auto.
    * rewrite neg_w_rule_ptree_formula_true.
      --  repeat split.
          ++  apply ord_ltb_lt. rewrite neg_w_rule_ptree_formula_true in Y. auto. rewrite X1. simpl. rewrite (non_target_term_sub f n0 (projT1 t)). rewrite non_target_fit. apply H1.
          ++  apply X; auto. lia. rewrite X1. rewrite (non_target_term_sub _ n0 (projT1 t)). simpl. rewrite non_target_fit,H1. auto.
          ++  apply nf_add. destruct HQ as [[[Q1 Q2] Q3] Q4]. destruct Q4. apply ptree_ord_nf. auto. rewrite X4. apply ptree_ord_nf. auto.
      --  rewrite X1. rewrite (non_target_term_sub _ n0 (projT1 t)). simpl. rewrite non_target_fit,H1. auto.
    * rewrite neg_w_rule_ptree_formula_true.
      --  apply X; auto. lia. rewrite X1. rewrite (non_target_term_sub _ n0 (projT1 t)). simpl. rewrite non_target_fit,H1. auto.
      --  rewrite X1. rewrite (non_target_term_sub _ n0 (projT1 t)). simpl. rewrite non_target_fit,H1. auto.
    * simpl. rewrite neg_w_rule_ptree_formula_true.
      --  assert (Nat.max d' (ptree_deg (p t)) < num_conn E + 2). lia. pose proof (neg_w_rule_ptree_deg (p t) Q E F n d' beta HQ X2 H0 (lor_ind (non_target f) S2)). lia.
      --  rewrite X1. simpl. rewrite (non_target_term_sub f n0 (projT1 t)). rewrite non_target_fit. auto.
    * simpl. rewrite neg_w_rule_ptree_formula_true.
      --  assert (Nat.max d' (ptree_deg (p t)) < num_conn E + 2). lia. pose proof (neg_w_rule_ptree_deg (p t) Q E F n d' beta HQ X2 H0 (lor_ind (non_target f) S2)). lia.
      --  rewrite X1. simpl. rewrite (non_target_term_sub f n0 (projT1 t)). rewrite non_target_fit. auto.
    * auto.
    * destruct (ord_semiconnex_bool (ptree_ord (neg_w_rule_sub_ptree_fit (p t) Q E F n d' beta HQ (lor_ind (non_target f) S2))) (ord_add beta o)) as [Y1 | [Y1 | Y1]].
      --  rewrite Y1 in Y. inversion Y.
      --  rewrite neg_w_rule_ptree_formula_true in Y1. rewrite X4 in Y1. rewrite neg_w_rule_ptree_ord in Y1. inversion Y1. auto. rewrite X1. simpl. rewrite (non_target_term_sub f n0 (projT1 t)). rewrite non_target_fit. auto.
      --  apply ord_eqb_eq in Y1. destruct Y1. auto.

- clear IHP2. simpl. simpl in HD. assert (Nat.max d' n0 < num_conn E + 2) as HD1. lia. assert (Nat.max d' n1 < num_conn E + 2) as HD2. lia.
  destruct (subst_ind_fit f S) eqn:Heq; try apply H. simpl.
  inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8]. rewrite H5,H6 in*.
  repeat split; auto; rewrite neg_w_rule_ptree_formula_true.
  + rewrite neg_w_rule_ptree_formula; auto.
    rewrite H1. unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_lor.
    * rewrite non_target_sub. auto.
    * rewrite Heq, non_target_fit. auto.
  + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + apply IHP1; auto. rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.

- clear IHP1. simpl. simpl in HD. assert (Nat.max d' n0 < num_conn E + 2) as HD1. lia. assert (Nat.max d' n1 < num_conn E + 2) as HD2. lia.
  destruct (subst_ind_fit f0 S) eqn:Heq; try apply H. simpl.
  inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8]. rewrite H5,H6 in *.
  repeat split; auto; rewrite neg_w_rule_ptree_formula_true.
  + rewrite neg_w_rule_ptree_formula; auto.
    rewrite H3. unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_lor.
    * rewrite non_target_sub. auto.
    * rewrite Heq, non_target_fit. auto.
  + rewrite H3. simpl. auto.
  + apply IHP2; auto. rewrite H3. simpl. auto.
  + rewrite H3. simpl. auto.

- simpl. simpl in HD. assert (Nat.max d' n0 < num_conn E + 2) as HD1. lia. assert (Nat.max d' n1 < num_conn E + 2) as HD2. lia.
  inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8]. rewrite H5,H6 in *.
  destruct S; try inversion Hs. rewrite H9.
  destruct (and_bool_prop _ _ H9) as [H10 H11].
  simpl. repeat split; rewrite neg_w_rule_ptree_formula_true.
  + rewrite neg_w_rule_ptree_formula; auto.
    rewrite H1. unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_lor.
    * rewrite non_target_sub. auto.
    * rewrite H10, non_target_fit. auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + apply IHP1; auto. rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite neg_w_rule_ptree_formula; auto.
    rewrite H3. unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_lor.
    * rewrite non_target_sub. auto.
    * rewrite H11, non_target_fit. auto.
  + rewrite H3. simpl. auto.
  + apply IHP2; auto. rewrite H3. simpl. auto.
  + rewrite H3. simpl. auto.
Qed.