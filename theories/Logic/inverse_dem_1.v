Add LoadPath "theories/Casteran" as Ordering.
Add LoadPath "theories/Maths" as Maths_Facts.
Add LoadPath "theories/Logic" as Systems.

From Maths_Facts Require Import naturals.
From Maths_Facts Require Import ordinals.

From Systems Require Import definitions.
From Systems Require Import fol.
From Systems Require Import proof_trees.
From Systems Require Import substitute.

Definition demorgan1_sub_formula (A E F : formula) (S : subst_ind) : formula :=
  formula_sub_ind A (neg (lor E F)) (neg E) S.

Lemma demorgan1_sub_formula_closed : forall (A : formula),
  closed A = true ->
  forall (E F : formula) (S : subst_ind),
    closed (demorgan1_sub_formula A E F S) = true.
Proof.
intros. unfold demorgan1_sub_formula. apply formula_sub_ind_closed; auto.
simpl. intros. destruct (and_bool_prop _ _ H0). auto.
Qed.

Fixpoint demorgan1_sub_ptree_fit
  (P : ptree) (E F : formula) (S : subst_ind) : ptree :=
match P, S with
| deg_up d P', _ => deg_up d (demorgan1_sub_ptree_fit P' E F S)

| ord_up alpha P', _ => ord_up alpha (demorgan1_sub_ptree_fit P' E F S)

| node A, _ => P

| exchange_ab A B d alpha P', lor_ind S_B S_A =>
    exchange_ab
      (demorgan1_sub_formula A E F S_A)
      (demorgan1_sub_formula B E F S_B)
      d alpha
      (demorgan1_sub_ptree_fit P' E F (lor_ind S_A S_B))

| exchange_cab C0 A B d alpha P', lor_ind (lor_ind S_C S_B) S_A =>
    exchange_cab
      (demorgan1_sub_formula C0 E F S_C)
      (demorgan1_sub_formula A E F S_A)
      (demorgan1_sub_formula B E F S_B)
      d alpha
      (demorgan1_sub_ptree_fit P' E F (lor_ind (lor_ind S_C S_A) S_B))

| exchange_abd A B D d alpha P', lor_ind (lor_ind S_B S_A) S_D =>
    exchange_abd
      (demorgan1_sub_formula A E F S_A)
      (demorgan1_sub_formula B E F S_B)
      (demorgan1_sub_formula D E F S_D)
      d alpha
      (demorgan1_sub_ptree_fit P' E F (lor_ind (lor_ind S_A S_B) S_D))

| exchange_cabd C0 A B D d alpha P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D =>
    exchange_cabd
      (demorgan1_sub_formula C0 E F S_C)
      (demorgan1_sub_formula A E F S_A)
      (demorgan1_sub_formula B E F S_B)
      (demorgan1_sub_formula D E F S_D)
      d alpha
      (demorgan1_sub_ptree_fit P' E F (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D))

| contraction_a A d alpha P', _ =>
    contraction_a
      (demorgan1_sub_formula A E F S)
      d alpha
      (demorgan1_sub_ptree_fit P' E F (lor_ind S S))

| contraction_ad A D d alpha P', lor_ind S_A S_D =>
    contraction_ad
      (demorgan1_sub_formula A E F S_A)
      (demorgan1_sub_formula D E F S_D)
      d alpha
      (demorgan1_sub_ptree_fit P' E F (lor_ind (lor_ind S_A S_A) S_D))

| weakening_ad A D d alpha P', lor_ind S_A S_D =>
    weakening_ad
      (demorgan1_sub_formula A E F S_A)
      (demorgan1_sub_formula D E F S_D)
      d alpha
      (demorgan1_sub_ptree_fit P' E F S_D)

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, _ =>
    (match eq_f A E, eq_f B F, S with
    | true, true, (1) =>
      (match eq_nat d1 (ptree_deg P) with
      | true => ord_up (ptree_ord P) P1
      | false => deg_up (ptree_deg P) (ord_up (ptree_ord P) P1)
      end)
    | _, _, _ => P
    end)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_AB S_D =>
    (match eq_f A E, eq_f B F, S_AB with
    | true, true, (1) =>
      (match eq_nat d1 (ptree_deg P) with
      | true =>
          ord_up
            (ptree_ord P)
            (demorgan1_sub_ptree_fit P1 E F (lor_ind (non_target (neg A)) S_D))
      | false =>
          deg_up
            (ptree_deg P)
              (ord_up
                (ptree_ord P)
                (demorgan1_sub_ptree_fit
                  P1 E F
                  (lor_ind (non_target (neg A)) S_D)))
      end)
    | _, _, _ =>
        demorgan_abd
          A B
          (demorgan1_sub_formula D E F S_D)
          d1 d2 alpha1 alpha2
          (demorgan1_sub_ptree_fit P1 E F (lor_ind (non_target (neg A)) S_D))
          (demorgan1_sub_ptree_fit P2 E F (lor_ind (non_target (neg B)) S_D))
    end)

| negation_a A d alpha P', _ => P

| negation_ad A D d alpha P', lor_ind S_A S_D =>
    negation_ad
      A
      (demorgan1_sub_formula D E F S_D)
      d alpha
      (demorgan1_sub_ptree_fit P' E F (lor_ind (non_target A) S_D))

| quantification_a A n t d alpha P', _ => P

| quantification_ad A D n t d alpha P', lor_ind S_A S_D =>
    quantification_ad
      A
      (demorgan1_sub_formula D E F S_D)
      n t d alpha
      (demorgan1_sub_ptree_fit P' E F (lor_ind (0) S_D))

| w_rule_a A n d alpha g, _ => P

| w_rule_ad A D n d alpha g, lor_ind S_A S_D =>
    w_rule_ad
      A
      (demorgan1_sub_formula D E F S_D)
      n d alpha
      (fun (t : c_term) =>
          demorgan1_sub_ptree_fit (g t) E F (lor_ind (non_target A) S_D))

| cut_ca C0 A d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ca
      (demorgan1_sub_formula C0 E F S)
      A d1 d2 alpha1 alpha2
      (demorgan1_sub_ptree_fit P1 E F (lor_ind S (non_target A)))
      P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ad
      A
      (demorgan1_sub_formula D E F S)
      d1 d2 alpha1 alpha2
      P1
      (demorgan1_sub_ptree_fit P2 E F (lor_ind (0) S))

| cut_cad C0 A D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_D =>
    cut_cad
      (demorgan1_sub_formula C0 E F S_C)
      A
      (demorgan1_sub_formula D E F S_D)
      d1 d2 alpha1 alpha2
      (demorgan1_sub_ptree_fit P1 E F (lor_ind S_C (non_target A)))
      (demorgan1_sub_ptree_fit P2 E F (lor_ind (0) S_D))

| _, _ => P
end.

Fixpoint demorgan1_sub_ptree
  (P : ptree) (E F : formula) (S : subst_ind) : ptree :=
match subst_ind_fit (ptree_formula P) S with
| false => P
| true => demorgan1_sub_ptree_fit P E F S
end.


(* First, we must prove that demorgan1_sub_ptree simply changes the base formula
of an ptree the way we expect with demorgan1_sub_formula *)
(* *)
Lemma demorgan1_ptree_formula_aux' :
  forall (P : ptree) (E F : formula) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
    demorgan1_sub_ptree P E F S = P.
Proof. intros. unfold demorgan1_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma demorgan1_ptree_formula_aux :
  forall (P : ptree) (E F : formula) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
      ptree_formula (demorgan1_sub_ptree P E F S) =
      demorgan1_sub_formula (ptree_formula P) E F S.
Proof.
intros. rewrite demorgan1_ptree_formula_aux'.
- unfold demorgan1_sub_formula. rewrite sub_fit_false. auto. apply H.
- apply H.
Qed.

Lemma demorgan1_ptree_formula_true :
  forall (P : ptree) (E F : formula) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    demorgan1_sub_ptree_fit P E F S = demorgan1_sub_ptree P E F S.
Proof. intros. unfold demorgan1_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma demorgan1_ptree_formula' : forall (P : ptree) (E F : formula),
  valid P ->
  forall (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    ptree_formula (demorgan1_sub_ptree P E F S) =
    demorgan1_sub_formula (ptree_formula P) E F S.
Proof.
intros P E F.
induction P; try intros H S Hs.

- simpl in Hs. simpl. rewrite Hs. simpl.
  rewrite (demorgan1_ptree_formula_true _ _ _ _ Hs).
  destruct H as [H1 H2]. apply (IHP H2). auto.

- simpl in Hs. simpl. rewrite Hs. simpl.
  rewrite (demorgan1_ptree_formula_true _ _ _ _ Hs).
  destruct H as [[H1 H2] H3]. apply (IHP H2). auto.

- simpl. inversion H.
  destruct (axiom_atomic _ H1); destruct H0; rewrite H0;
  unfold demorgan1_sub_formula; simpl; destruct S; auto.

- simpl.
  destruct S; inversion Hs; rewrite H1; simpl; unfold demorgan1_sub_formula.
  rewrite formula_sub_ind_lor; auto.

- simpl.
  destruct S; try destruct S1; inversion Hs; rewrite H1;
  simpl; unfold demorgan1_sub_formula.
  rewrite formula_sub_ind_lor, formula_sub_ind_lor; auto.
  apply (and_bool_prop _ _ H1).

- simpl.
  destruct S; try destruct S1; inversion Hs; rewrite H1;
  simpl; unfold demorgan1_sub_formula.
  rewrite formula_sub_ind_lor, formula_sub_ind_lor; auto.
  apply (and_bool_prop _ _ H1).

- simpl. destruct S; simpl.
  + unfold demorgan1_sub_formula. auto.
  + unfold demorgan1_sub_formula. auto.
  + destruct S1; try destruct S1_1; inversion Hs.
    rewrite H1. simpl. unfold demorgan1_sub_formula.
    destruct (and_bool_prop _ _ H1). destruct (and_bool_prop _ _ H0).
    repeat rewrite formula_sub_ind_lor; auto.

- simpl. inversion Hs. rewrite H1. auto.

- simpl. destruct S; inversion Hs.
  rewrite H1. simpl. unfold demorgan1_sub_formula.
  rewrite formula_sub_ind_lor. auto. apply H1.

- simpl. destruct S; auto. inversion Hs. rewrite H1. simpl.
  unfold demorgan1_sub_formula. rewrite formula_sub_ind_lor. auto. apply H1.

- simpl. destruct S; auto; destruct (eq_f f E) eqn:HE.
  + destruct (eq_f f0 F) eqn:HF; simpl;
    unfold demorgan1_sub_formula; rewrite formula_sub_ind_0; auto.
  + simpl. unfold demorgan1_sub_formula. rewrite formula_sub_ind_0. auto.
  + destruct (eq_f f0 F) eqn:HF.
    * inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
      clear IHP1. clear IHP2.
      case (eq_nat n (Init.Nat.max n n0)) eqn:Hn;
      simpl; rewrite H1; unfold demorgan1_sub_formula; simpl; rewrite HE,HF;
      simpl; rewrite (f_eq_decid _ _ HE); auto.
    * simpl. unfold demorgan1_sub_formula. simpl. rewrite HE,HF. auto.
  + simpl. unfold demorgan1_sub_formula. simpl. rewrite HE. auto.

- simpl. destruct S; auto.
  destruct S1; auto.
  + destruct (eq_f f E) eqn:HE; destruct (eq_f f0 F) eqn:HF;
    destruct (subst_ind_fit f1 S2) eqn:HS2; simpl; unfold demorgan1_sub_formula;
    simpl; rewrite HE,HF,HS2; auto; rewrite sub_fit_true; auto.
  + destruct (eq_f f E) eqn:HE.
    * destruct (eq_f f0 F) eqn:HF.
      { destruct (subst_ind_fit f1 S2) eqn:HS2.
        { clear IHP2. simpl.
          inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
          rewrite demorgan1_ptree_formula_true; auto.
          { case (eq_nat n (Init.Nat.max n n0)) eqn:Hn;
            simpl; rewrite IHP1; auto; rewrite H1; auto;
            unfold demorgan1_sub_formula; simpl; rewrite HE,HF,HS2;
            destruct (eq_f f (lor E F)); rewrite (f_eq_decid _ _ HE); auto. }
          { rewrite H1. auto. } }
        { simpl. unfold demorgan1_sub_formula. simpl. rewrite HE,HF,HS2. auto. } }
      { destruct (subst_ind_fit f1 S2) eqn:HS2; simpl;
        unfold demorgan1_sub_formula; simpl; rewrite HE,HF,HS2; auto;
        rewrite sub_fit_true; auto. }
    * destruct (eq_f f0 F) eqn:HF; destruct (subst_ind_fit f1 S2) eqn:HS2; simpl;
        unfold demorgan1_sub_formula; simpl; rewrite HE,HF,HS2; auto;
        rewrite sub_fit_true; auto.

- simpl. destruct S; auto.

- simpl. destruct S; auto. destruct S1; auto;
  destruct (subst_ind_fit f0 S2) eqn:HS2; simpl; unfold demorgan1_sub_formula;
  simpl; rewrite HS2; auto; rewrite sub_fit_true; auto.

- simpl. destruct S; simpl; unfold demorgan1_sub_formula; auto.

- simpl. destruct S.
  + simpl. unfold demorgan1_sub_formula. simpl. auto.
  + simpl. unfold demorgan1_sub_formula. simpl. auto.
  + destruct S1; inversion Hs; rewrite H1; simpl; unfold demorgan1_sub_formula.
    * rewrite formula_sub_ind_lor; auto.
    * simpl. rewrite H1. rewrite sub_fit_true; auto.

- intros. simpl. destruct S; simpl; unfold demorgan1_sub_formula; auto.

- intros. simpl. destruct S; try destruct S1; inversion H0;
  rewrite H2; unfold demorgan1_sub_formula; rewrite formula_sub_ind_lor; auto.

- simpl. inversion Hs. rewrite H1. auto.

- simpl. inversion Hs. rewrite H1. auto.

- simpl. destruct S; inversion Hs.
  rewrite H1. simpl. unfold demorgan1_sub_formula.
  rewrite formula_sub_ind_lor; auto.
Qed.


Lemma demorgan1_ptree_formula : forall (P : ptree) (E F : formula),
  valid P ->
  forall (S : subst_ind),
    ptree_formula (demorgan1_sub_ptree P E F S) =
    demorgan1_sub_formula (ptree_formula P) E F S.
Proof.
intros. destruct (subst_ind_fit (ptree_formula P) S) eqn:Hs.
- apply demorgan1_ptree_formula'. apply X. apply Hs.
- apply demorgan1_ptree_formula_aux. apply Hs.
Qed.





(* Second, we must prove that demorgan1_sub_ptree does not change the degree
of an ptree. *)
(* *)
Lemma demorgan1_ptree_deg : forall (P : ptree) (E F : formula),
  valid P ->
  forall (S : subst_ind), ptree_deg (demorgan1_sub_ptree P E F S) = ptree_deg P.
Proof.
intros P E F H. induction P; intros S.
- simpl. case (subst_ind_fit (ptree_formula P) S); auto.
- simpl. case (subst_ind_fit (ptree_formula P) S) eqn:Hfit; auto. simpl.
  rewrite (demorgan1_ptree_formula_true _ _ _ _ Hfit).
  apply IHP. inversion H. destruct X. auto.
- simpl. case (subst_ind_fit f S); auto.
- simpl.
  destruct S; auto. case (subst_ind_fit f0 S1 && subst_ind_fit f S2); auto.
- simpl. destruct S; auto. destruct S1; auto.
  case (subst_ind_fit f S1_1 && subst_ind_fit f1 S1_2 && subst_ind_fit f0 S2);
  auto.
- simpl. destruct S; auto. destruct S1; auto.
  case (subst_ind_fit f0 S1_1 && subst_ind_fit f S1_2 && subst_ind_fit f1 S2);
  auto.
- simpl. destruct S; auto. destruct S1; auto. destruct S1_1; auto.
  case (subst_ind_fit f S1_1_1 && subst_ind_fit f1 S1_1_2 &&
        subst_ind_fit f0 S1_2 && subst_ind_fit f2 S2); auto.
- simpl. destruct (subst_ind_fit f S); auto.
- simpl.
  destruct S; auto. destruct (subst_ind_fit f S1 && subst_ind_fit f0 S2); auto.
- simpl.
  destruct S; auto. destruct (subst_ind_fit f S1 && subst_ind_fit f0 S2); auto.
- simpl. destruct S; auto.
  + case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
  + inversion H as [[[[[H1 H2] H3] H4] H5] H6].
    case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
    case (eq_nat n (Init.Nat.max n n0)) eqn:Hn;
    simpl; auto; rewrite <- (nat_eq_decid _ _ Hn); auto.
- simpl. destruct S; auto.
  destruct S1; auto; destruct (subst_ind_fit f1 S2) eqn:HS2; auto; simpl.
  + case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
  + inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
    case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
    case (eq_nat n (Init.Nat.max n n0)) eqn:Hn;
    simpl; auto; rewrite <- (nat_eq_decid _ _ Hn); auto;
    rewrite demorgan1_ptree_formula_true;
    try rewrite IHP1; auto; rewrite H1; simpl; auto.
- simpl. destruct S; auto.
- simpl. destruct S; auto.
  destruct S1; auto; destruct (subst_ind_fit f0 S2); auto.
- simpl. destruct S; auto.
- simpl.
  destruct S; auto; destruct S1; auto; destruct (subst_ind_fit f0 S2); auto.
- simpl. destruct S; auto.
- simpl.
  destruct S; auto; destruct S1; auto; destruct (subst_ind_fit f0 S2); auto.
- simpl. destruct (subst_ind_fit f S); auto.
- simpl. destruct (subst_ind_fit f0 S); auto.
- simpl.
  destruct S; auto. destruct (subst_ind_fit f S1 && subst_ind_fit f1 S2); auto.
Qed.



Lemma demorgan1_ptree_ord : forall (P : ptree) (E F : formula),
  valid P ->
  forall (S : subst_ind), ptree_ord (demorgan1_sub_ptree P E F S) = ptree_ord P.
Proof.
intros P E F H. induction P; intros S.
- simpl. case (subst_ind_fit (ptree_formula P) S) eqn:Hfit; auto. simpl.
  rewrite (demorgan1_ptree_formula_true _ _ _ _ Hfit).
  apply IHP. inversion H. auto.
- simpl. case (subst_ind_fit (ptree_formula P) S); auto.
- simpl. case (subst_ind_fit f S); auto.
- simpl.
  destruct S; auto. case (subst_ind_fit f0 S1 && subst_ind_fit f S2); auto.
- simpl. destruct S; auto. destruct S1; auto.
  case (subst_ind_fit f S1_1 && subst_ind_fit f1 S1_2 && subst_ind_fit f0 S2);
  auto.
- simpl. destruct S; auto. destruct S1; auto.
  case (subst_ind_fit f0 S1_1 && subst_ind_fit f S1_2 && subst_ind_fit f1 S2);
  auto.
- simpl. destruct S; auto. destruct S1; auto. destruct S1_1; auto.
  case (subst_ind_fit f S1_1_1 && subst_ind_fit f1 S1_1_2 &&
        subst_ind_fit f0 S1_2 && subst_ind_fit f2 S2); auto.
- simpl. destruct (subst_ind_fit f S); auto.
- simpl.
  destruct S; auto. destruct (subst_ind_fit f S1 && subst_ind_fit f0 S2); auto.
- simpl.
  destruct S; auto. destruct (subst_ind_fit f S1 && subst_ind_fit f0 S2); auto.
- simpl. destruct S; auto.
  + case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
  + inversion H as [[[[[H1 H2] H3] H4] H5] H6].
    case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
    case (eq_nat n (Init.Nat.max n n0)) eqn:Hn;
    case (ord_eqb o (ord_succ (ord_max o o0))) eqn:Ho; simpl; auto;
    rewrite <- (ord_eqb_eq _ _ Ho); auto.
- simpl. destruct S; auto.
  destruct S1; auto; destruct (subst_ind_fit f1 S2) eqn:HS2; auto; simpl.
  + case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
  + inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
    case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
    case (eq_nat n (Init.Nat.max n n0)) eqn:Hn;
    simpl; auto.
- simpl. destruct S; auto.
- simpl. destruct S; auto.
  destruct S1; auto; destruct (subst_ind_fit f0 S2); auto.
- simpl. destruct S; auto.
- simpl.
  destruct S; auto; destruct S1; auto; destruct (subst_ind_fit f0 S2); auto.
- simpl. destruct S; auto.
- simpl.
  destruct S; auto; destruct S1; auto; destruct (subst_ind_fit f0 S2); auto.
- simpl. destruct (subst_ind_fit f S); auto.
- simpl. destruct (subst_ind_fit f0 S); auto.
- simpl.
  destruct S; auto. destruct (subst_ind_fit f S1 && subst_ind_fit f1 S2); auto.
Qed.


(* Now we prove that if we have a valid ptree, performing our
double negation substitution on it results in a valid ptree *)
(* *)
Lemma demorgan1_valid : forall (P : ptree) (E F : formula),
  valid P ->
  forall (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    valid (demorgan1_sub_ptree P E F S).
Proof.
intros P E F. induction P; try intros H S Hs.

- simpl. inversion H as [H1 H2]. inversion Hs. rewrite H3.
  rewrite demorgan1_ptree_formula_true; auto. split.
  + rewrite demorgan1_ptree_deg; auto.
  + apply (IHP H2 S H3).

- simpl. inversion H as [[H1 H2] H3]. inversion Hs. rewrite H4.
  rewrite demorgan1_ptree_formula_true; auto. split.
  + rewrite demorgan1_ptree_ord; auto.
  + auto.

- simpl. destruct (subst_ind_fit f S); apply H.

- simpl. destruct S; inversion Hs. rewrite H1. simpl.
  inversion H as [[[H2 H3] H4] H5].
  repeat split; rewrite demorgan1_ptree_formula_true.
  + rewrite demorgan1_ptree_formula; auto.
    rewrite H2. unfold demorgan1_sub_formula.
    rewrite formula_sub_ind_lor; auto. apply (and_bool_symm _ _ H1).
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + apply IHP. apply H. rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + rewrite demorgan1_ptree_deg; auto.
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + rewrite demorgan1_ptree_ord; auto.
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).

- simpl. destruct S; try destruct S1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H4 H5] H6] H7].
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  repeat split; rewrite demorgan1_ptree_formula_true.
  + rewrite demorgan1_ptree_formula; auto.
    rewrite H4. unfold demorgan1_sub_formula.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H1, H2. auto.
    * simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + apply IHP; auto. rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite demorgan1_ptree_deg; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite demorgan1_ptree_ord; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.

- simpl. destruct S; try destruct S1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H4 H5] H6] H7].
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  repeat split; rewrite demorgan1_ptree_formula_true.
  + rewrite demorgan1_ptree_formula; auto.
    rewrite H4. unfold demorgan1_sub_formula.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H1, H3. auto.
    * simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + apply IHP; auto. rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite demorgan1_ptree_deg; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite demorgan1_ptree_ord; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.

- simpl. destruct S; try destruct S1; try destruct S1_1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H5 H6] H7] H8].
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  destruct (and_bool_prop _ _ H1). clear H1.
  repeat split; rewrite demorgan1_ptree_formula_true.
  + rewrite demorgan1_ptree_formula; auto.
    rewrite H5. unfold demorgan1_sub_formula.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H0,H3. auto.
    * simpl. rewrite H0, H3, H4. auto.
    * simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + apply IHP; auto. rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite demorgan1_ptree_deg; auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite demorgan1_ptree_ord; auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.

- simpl. inversion Hs. rewrite H1. inversion H as [[[H2 H3] H4] H5].
  repeat split; rewrite demorgan1_ptree_formula_true.
  + rewrite demorgan1_ptree_formula; auto.
    unfold demorgan1_sub_formula. rewrite H2.
    rewrite formula_sub_ind_lor; auto. rewrite H1. auto.
  + rewrite H2. simpl. rewrite H1. auto.
  + apply IHP. apply H. rewrite H2. simpl. rewrite H1. auto.
  + rewrite H2. simpl. rewrite H1. auto.
  + rewrite demorgan1_ptree_deg; auto.
  + rewrite H2. simpl. rewrite H1. auto.
  + rewrite demorgan1_ptree_ord; auto.
  + rewrite H2. simpl. rewrite H1. auto.

- simpl. destruct S; inversion Hs. rewrite H1.
  inversion H as [[[H2 H3] H4] H5]. destruct (and_bool_prop _ _ H1).
  repeat split; rewrite demorgan1_ptree_formula_true.
  + rewrite demorgan1_ptree_formula; auto.
    unfold demorgan1_sub_formula. rewrite H2.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H0. auto.
    * simpl. rewrite H0, H6. auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + apply IHP. apply H. rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite demorgan1_ptree_deg; auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite demorgan1_ptree_ord; auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.

- simpl. destruct S; inversion Hs. rewrite H1. simpl.
  inversion H as [[[[H2 H3] H4] H5] H6]. destruct (and_bool_prop _ _ H1).
  repeat split.
  + rewrite demorgan1_ptree_formula_true.
    * rewrite demorgan1_ptree_formula; auto. rewrite H2. auto.
    * rewrite H2. auto.
  + apply demorgan1_sub_formula_closed. auto.
  + rewrite demorgan1_ptree_formula_true.
    * apply IHP; auto. rewrite H2. auto.
    * rewrite H2. auto.
  + rewrite demorgan1_ptree_formula_true.
    * rewrite demorgan1_ptree_deg; auto.
    * rewrite H2. auto.
  + rewrite demorgan1_ptree_formula_true.
    * rewrite demorgan1_ptree_ord; auto.
    * rewrite H2. auto.

- simpl. inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  destruct S; auto; destruct (eq_f f E); destruct (eq_f f0 F);
  simpl; repeat split; auto.
  case (eq_nat n (Init.Nat.max n n0)) eqn:Hn;
  simpl; repeat split; auto.
  + rewrite <- H7. apply ord_max_succ_l.
  + apply ord_succ_nf. apply ord_max_nf.
    * rewrite H7. apply ptree_ord_nf. auto.
    * rewrite H8. apply ptree_ord_nf. auto.
  + rewrite <- H5. apply max_lem1. auto.
  + rewrite <- H7. apply ord_max_succ_l.
  + apply ord_succ_nf. apply ord_max_nf.
    * rewrite H7. apply ptree_ord_nf. auto.
    * rewrite H8. apply ptree_ord_nf. auto.
  
- simpl. inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  destruct S; auto.
  destruct S1; auto; destruct (subst_ind_fit f1 S2) eqn:HS2; simpl.
  + destruct (eq_f f E) eqn:HE; destruct (eq_f f0 F) eqn:HF;
    simpl; repeat split; auto; rewrite demorgan1_ptree_formula_true;
    try rewrite demorgan1_ptree_deg; try rewrite demorgan1_ptree_ord;
    try rewrite demorgan1_ptree_formula;
    try apply IHP1; try apply IHP2; try rewrite H1; try rewrite H3;
    auto; unfold demorgan1_sub_formula; simpl; try rewrite HS2;
    try destruct (eq_f f0 (lor E F)); try destruct (eq_f f (lor E F));
    try rewrite sub_fit_true; auto;
    case (eq_nat n (Init.Nat.max n n0)) eqn:Hn;
    simpl; repeat split; auto;
    try apply IHP1; auto; try rewrite H1; auto;
    try rewrite demorgan1_ptree_ord; auto;
    try rewrite <- H7; try apply ord_max_lt1; auto;
    try rewrite demorgan1_ptree_deg; auto; try rewrite <- H5; try apply max_lem1; auto;
    try apply ord_max_nf; try rewrite H7; try rewrite H8; try apply ptree_ord_nf; auto.
  + repeat split; auto.
  + destruct (eq_f f E) eqn:HE; destruct (eq_f f0 F) eqn:HF;
    simpl; repeat split; auto; rewrite demorgan1_ptree_formula_true;
    try rewrite demorgan1_ptree_deg; try rewrite demorgan1_ptree_ord;
    try rewrite demorgan1_ptree_formula;
    try apply IHP1; try apply IHP2; try rewrite H1; try rewrite H3;
    auto; unfold demorgan1_sub_formula; simpl; try rewrite HS2;
    try destruct (eq_f f0 (lor E F)); try destruct (eq_f f (lor E F));
    try rewrite sub_fit_true; auto;
    case (eq_nat n (Init.Nat.max n n0)) eqn:Hn;
    simpl; repeat split; auto;
    try apply IHP1; auto; try rewrite H1; auto;
    try rewrite demorgan1_ptree_ord; auto;
    try rewrite <- H7; try apply ord_max_lt1; try apply ord_max_succ_l; auto;
    try rewrite demorgan1_ptree_deg; auto; try rewrite <- H5; try apply max_lem1; auto;
    try apply ord_succ_nf; try apply ord_max_nf; try rewrite H7; try rewrite H8; try apply ptree_ord_nf; auto.
  + repeat split; auto.

- simpl. destruct S; auto.

- simpl. inversion H as [[[H1 H2] H3] H4]. destruct S; auto.
  destruct S1; auto; destruct (subst_ind_fit f0 S2) eqn:HS2; simpl;
  repeat split; auto; rewrite demorgan1_ptree_formula_true;
  try apply IHP; auto; try rewrite H1; simpl; try rewrite non_target_fit,HS2;
  try rewrite demorgan1_ptree_deg; try rewrite demorgan1_ptree_ord; auto.
  + rewrite demorgan1_ptree_formula; auto. rewrite H1.
    unfold demorgan1_sub_formula. simpl. rewrite non_target_fit,HS2.
    simpl. rewrite <- sub_fit_true; auto.
    * rewrite non_target_sub. rewrite <- sub_fit_true; auto.
    * apply non_target_fit.
  + rewrite demorgan1_ptree_formula; auto. rewrite H1.
    unfold demorgan1_sub_formula. simpl. rewrite non_target_fit,HS2.
    simpl. rewrite <- sub_fit_true; auto.
    * rewrite non_target_sub. rewrite <- sub_fit_true; auto.
    * apply non_target_fit.

- simpl. destruct S; apply H.

- simpl. destruct S; try apply H. inversion H as [[[H0 H1] H2] H3].
  destruct S1; inversion Hs; rewrite H5; simpl.
  + repeat split; auto.
    * rewrite demorgan1_ptree_formula_true, demorgan1_ptree_formula; auto.
      { rewrite H0. unfold demorgan1_sub_formula.
        { rewrite formula_sub_ind_lor. simpl.
          { destruct (eq_f (substitution f n (projT1 c))); auto. }
          { simpl. apply H5. } } }
      { rewrite H0. simpl. apply H5. }
    * rewrite demorgan1_ptree_formula_true.
      { apply IHP; auto. rewrite H0. simpl. apply H5. }
      { rewrite H0. simpl. apply H5. }
    * rewrite demorgan1_ptree_formula_true.
      { rewrite demorgan1_ptree_deg; auto. }
      { rewrite H0. simpl. auto. }
    * rewrite demorgan1_ptree_formula_true.
      { rewrite demorgan1_ptree_ord; auto. }
      { rewrite H0. simpl. auto. }
  + repeat split; auto.
    * rewrite demorgan1_ptree_formula_true, demorgan1_ptree_formula; auto.
      { rewrite H0. unfold demorgan1_sub_formula.
        { rewrite formula_sub_ind_lor. simpl.
          { destruct (eq_f (substitution f n (projT1 c))); auto. }
          { simpl. apply H5. } } }
      { rewrite H0. simpl. apply H5. }
    * rewrite demorgan1_ptree_formula_true.
      { apply IHP; auto. rewrite H0. simpl. apply H5. }
      { rewrite H0. simpl. apply H5. }
    * rewrite demorgan1_ptree_formula_true.
      { rewrite demorgan1_ptree_deg; auto. }
      { rewrite H0. simpl. auto. }
    * rewrite demorgan1_ptree_formula_true.
      { rewrite demorgan1_ptree_ord; auto. }
      { rewrite H0. simpl. auto. }

- intros. simpl. destruct S; apply H.

- rename H into H0. rename X into H. rename Hs into H1.
  simpl. destruct S; try apply H0. destruct S1; inversion H1.
  + rewrite H3. simpl. intros. destruct (valid_w_rule_ad _ _ _ _ _ _ H0 t) as [[[H4 H5] H6] H7].
    repeat split.
    * rewrite demorgan1_ptree_formula_true, demorgan1_ptree_formula; auto.
      { rewrite H4. unfold demorgan1_sub_formula. rewrite formula_sub_ind_lor.
        { rewrite (non_target_term_sub f n (projT1 t)).
          rewrite non_target_sub. auto. }
        { rewrite (non_target_term_sub f n (projT1 t)).
          rewrite non_target_fit. apply H3. } }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
        rewrite non_target_fit. apply H3. }
    * rewrite demorgan1_ptree_formula_true.
      { apply H. apply H5. rewrite H4. simpl.
        rewrite (non_target_term_sub f n (projT1 t)).
        rewrite non_target_fit. apply H3. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
        rewrite non_target_fit. apply H3. }
    * rewrite demorgan1_ptree_formula_true.
      { rewrite demorgan1_ptree_deg; auto. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
        rewrite non_target_fit. rewrite H3. auto. }
    * rewrite demorgan1_ptree_formula_true.
      { rewrite demorgan1_ptree_ord; auto. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
        rewrite non_target_fit. rewrite H3. auto. }
  + rewrite H3. simpl. intros. destruct (valid_w_rule_ad _ _ _ _ _ _ H0 t) as [[[H4 H5] H6] H7].
    repeat split.
    * rewrite demorgan1_ptree_formula_true, demorgan1_ptree_formula; auto.
      { rewrite H4. unfold demorgan1_sub_formula. rewrite formula_sub_ind_lor.
        { rewrite (non_target_term_sub f n (projT1 t)).
          rewrite non_target_sub. auto. }
        { rewrite (non_target_term_sub f n (projT1 t)).
          rewrite non_target_fit. apply H3. } }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
        rewrite non_target_fit. apply H3. }
    * rewrite demorgan1_ptree_formula_true.
      { apply H. apply H5. rewrite H4. simpl.
        rewrite (non_target_term_sub f n (projT1 t)).
        rewrite non_target_fit. apply H3. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
        rewrite non_target_fit. apply H3. }
    * rewrite demorgan1_ptree_formula_true.
      { rewrite demorgan1_ptree_deg; auto. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
        rewrite non_target_fit. rewrite H3. auto. }
    * rewrite demorgan1_ptree_formula_true.
      { rewrite demorgan1_ptree_ord; auto. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
        rewrite non_target_fit. rewrite H3. auto. }
  - clear IHP2. simpl. destruct (subst_ind_fit f S) eqn:Heq; try apply H. simpl.
    inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
    repeat split; auto; rewrite demorgan1_ptree_formula_true.
    + rewrite demorgan1_ptree_formula; auto.
      rewrite H1. unfold demorgan1_sub_formula. rewrite formula_sub_ind_lor.
      * rewrite non_target_sub. auto.
      * rewrite Heq, non_target_fit. auto.
    + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
    + apply IHP1; auto. rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
    + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
    + rewrite demorgan1_ptree_deg; auto.
    + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
    + rewrite demorgan1_ptree_ord; auto.
    + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.

- clear IHP1. simpl. destruct (subst_ind_fit f0 S) eqn:Heq; try apply H. simpl.
  inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  repeat split; auto; rewrite demorgan1_ptree_formula_true.
  + rewrite demorgan1_ptree_formula; auto.
    rewrite H3. unfold demorgan1_sub_formula. rewrite formula_sub_ind_lor.
    * rewrite non_target_sub. auto.
    * rewrite Heq, non_target_fit. auto.
  + rewrite H3. simpl. auto.
  + apply IHP2; auto. rewrite H3. simpl. auto.
  + rewrite H3. simpl. auto.
  + rewrite demorgan1_ptree_deg; auto.
  + rewrite H3. simpl. auto.
  + rewrite demorgan1_ptree_ord; auto.
  + rewrite H3. simpl. auto.

- simpl. inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  destruct S; try inversion Hs. rewrite H9.
  destruct (and_bool_prop _ _ H9) as [H10 H11].
  simpl. repeat split; rewrite demorgan1_ptree_formula_true.
  + rewrite demorgan1_ptree_formula; auto.
    rewrite H1. unfold demorgan1_sub_formula. rewrite formula_sub_ind_lor.
    * rewrite non_target_sub. auto.
    * rewrite H10, non_target_fit. auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + apply IHP1; auto. rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite demorgan1_ptree_formula; auto.
    rewrite H3. unfold demorgan1_sub_formula. rewrite formula_sub_ind_lor.
    * rewrite non_target_sub. auto.
    * rewrite H11, non_target_fit. auto.
  + rewrite H3. simpl. auto.
  + apply IHP2; auto. rewrite H3. simpl. auto.
  + rewrite H3. simpl. auto.
  + rewrite demorgan1_ptree_deg; auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite demorgan1_ptree_deg; auto.
  + rewrite H3. simpl. auto.
  + rewrite demorgan1_ptree_ord; auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite demorgan1_ptree_ord; auto.
  + rewrite H3. simpl. auto.
Qed.



(* We finally show that if the formulas ~~A and/or ~~A \/ D are provable,
so are the formulas A and/or A \/ D *)
(* *)
Lemma demorgan1_invertible_a :
  forall (A B : formula) (d : nat) (alpha : ord),
  provable (neg (lor A B)) d alpha -> provable (neg A) d alpha.
Proof.
unfold provable. intros A B d alpha H. destruct H as [t [[[Ht1 Ht2] Ht3] Ht4]].
exists (demorgan1_sub_ptree t A B (1)). unfold P_proves. repeat split.
- rewrite demorgan1_ptree_formula; auto. rewrite Ht1.
  unfold demorgan1_sub_formula. simpl. repeat rewrite eq_f_refl. auto.
- apply demorgan1_valid; auto. rewrite Ht1. auto.
- rewrite demorgan1_ptree_deg; auto.
- rewrite demorgan1_ptree_ord; auto.
Qed.

Lemma demorgan1_invertible_ad :
  forall (A B D : formula) (d : nat) (alpha : ord),
  provable (lor (neg (lor A B)) D) d alpha -> provable (lor (neg A) D) d alpha.
Proof.
unfold provable. intros A B D d alpha H. destruct H as [t [[[Ht1 Ht2] Ht3] Ht4]].
exists (demorgan1_sub_ptree t A B (lor_ind (1) (non_target D))).
unfold P_proves. repeat split.
- rewrite demorgan1_ptree_formula; auto. rewrite Ht1.
  unfold demorgan1_sub_formula. simpl. rewrite non_target_fit.
  repeat rewrite eq_f_refl. simpl. rewrite <- sub_fit_true.
  + rewrite non_target_sub. auto.
  + apply non_target_fit.
- apply demorgan1_valid; auto. rewrite Ht1. simpl. apply non_target_fit.
- rewrite demorgan1_ptree_deg; auto.
- rewrite demorgan1_ptree_ord; auto.
Qed.
