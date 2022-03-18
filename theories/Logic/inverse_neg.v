Add LoadPath "theories/Casteran" as Ordering.
Add LoadPath "theories/Maths" as Maths_Facts.
Add LoadPath "theories/Logic" as Systems.

From Maths_Facts Require Import naturals.
From Maths_Facts Require Import ordinals.

From Systems Require Import definitions.
From Systems Require Import fol.
From Systems Require Import proof_trees.
From Systems Require Import substitute.


Definition dub_neg_sub_formula (A E : formula) (S : subst_ind) : formula :=
  formula_sub_ind A (neg (neg E)) E S.

Lemma dub_neg_sub_formula_closed : forall (A : formula),
  closed A = true ->
  forall (E : formula) (S : subst_ind),
    closed (dub_neg_sub_formula A E S) = true.
Proof.
intros. unfold dub_neg_sub_formula. apply formula_sub_ind_closed; auto.
Qed.


Fixpoint dub_neg_sub_ptree_fit
  (P : ptree) (E : formula) (S : subst_ind) : ptree :=
match P, S with
| deg_up d P', _ => deg_up d (dub_neg_sub_ptree_fit P' E S)

| ord_up alpha P', _ => ord_up alpha (dub_neg_sub_ptree_fit P' E S)

| node A, _ => P

| exchange_ab A B d alpha P', lor_ind S_B S_A =>
    exchange_ab
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula B E S_B)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind S_A S_B))

| exchange_cab C0 A B d alpha P', lor_ind (lor_ind S_C S_B) S_A =>
    exchange_cab
      (dub_neg_sub_formula C0 E S_C)
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula B E S_B)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind (lor_ind S_C S_A) S_B))

| exchange_abd A B D d alpha P', lor_ind (lor_ind S_B S_A) S_D =>
    exchange_abd
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula B E S_B)
      (dub_neg_sub_formula D E S_D)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind (lor_ind S_A S_B) S_D))

| exchange_cabd C0 A B D d alpha P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D =>
    exchange_cabd
      (dub_neg_sub_formula C0 E S_C)
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula B E S_B)
      (dub_neg_sub_formula D E S_D)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D))

| contraction_a A d alpha P', _ =>
    contraction_a
      (dub_neg_sub_formula A E S)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind S S))

| contraction_ad A D d alpha P', lor_ind S_A S_D =>
    contraction_ad
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula D E S_D)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind (lor_ind S_A S_A) S_D))

| weakening_ad A D d alpha P', lor_ind S_A S_D =>
    weakening_ad
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula D E S_D)
      d alpha
      (dub_neg_sub_ptree_fit P' E S_D)

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, _ => P

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_AB S_D =>
    demorgan_abd
      A B (dub_neg_sub_formula D E S_D) d1 d2 alpha1 alpha2
      (dub_neg_sub_ptree_fit P1 E (lor_ind (0) S_D))
      (dub_neg_sub_ptree_fit P2 E (lor_ind (0) S_D))

| negation_a A d alpha P', _ =>
    (match eq_f A E, S with
    | true, (1) => ord_up (ord_succ alpha) P'
    | _, _ => P
    end)

| negation_ad A D d alpha P', lor_ind S_A S_D =>
    (match eq_f A E, S_A with
    | true, (1) => ord_up (ord_succ alpha) (dub_neg_sub_ptree_fit P' E (lor_ind (non_target A) S_D))
    | _, _ => 
        negation_ad
          A
          (dub_neg_sub_formula D E S_D)
          d alpha
          (dub_neg_sub_ptree_fit P' E (lor_ind (non_target A) S_D))
    end)

| quantification_a A n t d alpha P', _ => P

| quantification_ad A D n t d alpha P', lor_ind S_A S_D =>
    quantification_ad
      A
      (dub_neg_sub_formula D E S_D)
      n t d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind (0) S_D))


| w_rule_a A n d alpha g, _ => P

| w_rule_ad A D n d alpha g, lor_ind S_A S_D =>
    w_rule_ad
      A
      (dub_neg_sub_formula D E S_D)
      n
      d alpha
      (fun (n : nat) =>
          dub_neg_sub_ptree_fit (g n) E (lor_ind (non_target A) S_D))

| cut_ca C0 A d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ca
      (dub_neg_sub_formula C0 E S)
      A d1 d2 alpha1 alpha2
      (dub_neg_sub_ptree_fit P1 E (lor_ind S (non_target A)))
      P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ad
      A (dub_neg_sub_formula D E S) d1 d2 alpha1 alpha2
      P1
      (dub_neg_sub_ptree_fit P2 E (lor_ind (0) S))

| cut_cad C0 A D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_D =>
    cut_cad
      (dub_neg_sub_formula C0 E S_C)
      A (dub_neg_sub_formula D E S_D) d1 d2 alpha1 alpha2
      (dub_neg_sub_ptree_fit P1 E (lor_ind S_C (non_target A)))
      (dub_neg_sub_ptree_fit P2 E (lor_ind (0) S_D))

| _, _ => P
end.

Fixpoint dub_neg_sub_ptree (P : ptree) (E : formula) (S : subst_ind) : ptree :=
match subst_ind_fit (ptree_formula P) S with
| false => P
| true => dub_neg_sub_ptree_fit P E S
end.


(* First, we must prove that dub_neg_sub_ptree simply changes the base formula
of an ptree the way we expect with dub_neg_sub_formula *)
(* *)
Lemma dub_neg_ptree_formula_aux' :
  forall (P : ptree) (E : formula) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
    dub_neg_sub_ptree P E S = P.
Proof. intros. unfold dub_neg_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma dub_neg_ptree_formula_aux :
  forall (P : ptree) (E : formula) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
      ptree_formula (dub_neg_sub_ptree P E S) =
      dub_neg_sub_formula (ptree_formula P) E S.
Proof.
intros. rewrite dub_neg_ptree_formula_aux'.
- unfold dub_neg_sub_formula. rewrite sub_fit_false. auto. apply H.
- apply H.
Qed.

Lemma dub_neg_ptree_formula_true :
  forall (P : ptree) (E : formula) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    dub_neg_sub_ptree_fit P E S = dub_neg_sub_ptree P E S.
Proof. intros. unfold dub_neg_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma dub_neg_ptree_formula' : forall (P : ptree) (E : formula),
  valid P ->
  forall (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    ptree_formula (dub_neg_sub_ptree P E S) =
    dub_neg_sub_formula (ptree_formula P) E S.
Proof.
intros P E.
induction P; try intros H S Hs.

- simpl in Hs. simpl. rewrite Hs. simpl.
  rewrite (dub_neg_ptree_formula_true _ _ _ Hs).
  destruct H as [H1 H2]. apply (IHP H2). auto.

- simpl in Hs. simpl. rewrite Hs. simpl.
  rewrite (dub_neg_ptree_formula_true _ _ _ Hs).
  destruct H as [[H1 H2] H3]. apply (IHP H2). auto.

- simpl. inversion H.
  destruct (axiom_atomic _ H1); destruct H0; rewrite H0;
  unfold dub_neg_sub_formula; simpl; destruct S; auto.

- simpl.
  destruct S; inversion Hs; rewrite H1; simpl; unfold dub_neg_sub_formula.
  rewrite formula_sub_ind_lor; auto.

- simpl.
  destruct S; try destruct S1; inversion Hs; rewrite H1;
  simpl; unfold dub_neg_sub_formula.
  rewrite formula_sub_ind_lor, formula_sub_ind_lor; auto.
  apply (and_bool_prop _ _ H1).

- simpl.
  destruct S; try destruct S1; inversion Hs; rewrite H1;
  simpl; unfold dub_neg_sub_formula.
  rewrite formula_sub_ind_lor, formula_sub_ind_lor; auto.
  apply (and_bool_prop _ _ H1).

- simpl. destruct S; simpl.
  + unfold dub_neg_sub_formula. auto.
  + unfold dub_neg_sub_formula. auto.
  + destruct S1; try destruct S1_1; inversion Hs.
    rewrite H1. simpl. unfold dub_neg_sub_formula.
    destruct (and_bool_prop _ _ H1). destruct (and_bool_prop _ _ H0).
    repeat rewrite formula_sub_ind_lor; auto.

- simpl. inversion Hs. rewrite H1. auto.

- simpl. destruct S; inversion Hs.
  rewrite H1. simpl. unfold dub_neg_sub_formula.
  rewrite formula_sub_ind_lor. auto. apply H1.

- simpl. destruct S; auto. inversion Hs. rewrite H1. simpl.
  unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor. auto. apply H1.

- simpl. destruct S; auto.

- simpl. destruct S.
  + inversion Hs.
  + inversion Hs.
  + destruct S1; inversion Hs; rewrite H1; simpl; unfold dub_neg_sub_formula;
    rewrite formula_sub_ind_lor; auto; apply H1.

- simpl. destruct (eq_f f E) eqn:Heq; destruct S.
  + simpl. unfold dub_neg_sub_formula. rewrite formula_sub_ind_0. auto.
  + unfold dub_neg_sub_formula. simpl. inversion H as [[[H1 H2] H3] H4].
    rewrite H1. rewrite (f_eq_decid _ _ Heq). rewrite eq_f_refl. auto.
  + inversion Hs.
  + simpl. unfold dub_neg_sub_formula. rewrite formula_sub_ind_0. auto.
  + unfold dub_neg_sub_formula. simpl. rewrite Heq. auto.
  + inversion Hs.

- simpl. destruct (eq_f f E) eqn:Heq; destruct S.
  + inversion Hs.
  + inversion Hs.
  + destruct S1.
    * apply (subst_ind_fit_lor) in Hs. destruct (and_bool_prop _ _ Hs).
      rewrite H1. simpl. unfold dub_neg_sub_formula.
      rewrite formula_sub_ind_lor, formula_sub_ind_0. auto. apply Hs.
    * inversion Hs. rewrite H1. simpl. inversion H as [[[H2 H3] H4] H5].
      rewrite dub_neg_ptree_formula_true.
      { rewrite IHP; auto.
        { rewrite H2. unfold dub_neg_sub_formula.
          rewrite non_target_sub_lor. simpl. rewrite H1. rewrite Heq.
          rewrite sub_fit_true; auto. rewrite (f_eq_decid _ _ Heq); auto. }
        { rewrite H2. simpl. rewrite non_target_fit, H1. auto. } }
      { rewrite H2. simpl. rewrite non_target_fit, H1. auto. }
    * simpl. inversion Hs.
  + inversion Hs.
  + inversion Hs.
  + destruct S1.
    * apply (subst_ind_fit_lor) in Hs. destruct (and_bool_prop _ _ Hs).
      rewrite H1. simpl. unfold dub_neg_sub_formula.
      rewrite formula_sub_ind_lor, formula_sub_ind_0. auto. apply Hs.
    * inversion Hs. rewrite H1. simpl. unfold dub_neg_sub_formula.
      rewrite formula_sub_ind_lor; auto. simpl. rewrite Heq. auto.
    * simpl. inversion Hs.

- simpl. destruct S; simpl; unfold dub_neg_sub_formula; auto.

- simpl. destruct S.
  + simpl. unfold dub_neg_sub_formula. simpl. auto.
  + simpl. unfold dub_neg_sub_formula. simpl. auto.
  + destruct S1; inversion Hs; rewrite H1; simpl; unfold dub_neg_sub_formula.
    * rewrite formula_sub_ind_lor; auto.
    * simpl. rewrite H1. rewrite sub_fit_true; auto.

- intros. simpl. destruct S; simpl; unfold dub_neg_sub_formula; auto.

- intros. simpl. destruct S; try destruct S1; inversion H0;
  rewrite H2; unfold dub_neg_sub_formula; rewrite formula_sub_ind_lor; auto.

- simpl. inversion Hs. rewrite H1. auto.

- simpl. inversion Hs. rewrite H1. auto.

- simpl. destruct S; inversion Hs.
  rewrite H1. simpl. unfold dub_neg_sub_formula.
  rewrite formula_sub_ind_lor; auto.
Qed.


Lemma dub_neg_ptree_formula : forall (P : ptree) (E : formula),
  valid P ->
  forall (S : subst_ind),
    ptree_formula (dub_neg_sub_ptree P E S) =
    dub_neg_sub_formula (ptree_formula P) E S.
Proof.
intros. destruct (subst_ind_fit (ptree_formula P) S) eqn:Hs.
- apply dub_neg_ptree_formula'. apply X. apply Hs.
- apply dub_neg_ptree_formula_aux. apply Hs.
Qed.





(* Second, we must prove that dub_neg_sub_ptree does not change the degree
of an ptree. *)
(* *)
Lemma dub_neg_ptree_deg : forall (P : ptree) (E : formula),
  valid P ->
  forall (S : subst_ind), ptree_deg (dub_neg_sub_ptree P E S) = ptree_deg P.
Proof.
intros P E H. induction P; intros S.
- simpl. case (subst_ind_fit (ptree_formula P) S); auto.
- simpl. case (subst_ind_fit (ptree_formula P) S) eqn:Hfit; auto. simpl.
  rewrite (dub_neg_ptree_formula_true _ _ _ Hfit).
  apply IHP. inversion H. destruct X as [X1 X2]. auto.
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
- simpl. destruct S; auto. destruct S1; destruct (subst_ind_fit f1 S2); auto.
- simpl. destruct S; auto; destruct (eq_f f E); auto.
  inversion H as [[H1 H2] H3]. auto.
- simpl. destruct S; auto.
  destruct S1; destruct (subst_ind_fit f0 S2) eqn:HS2;
  destruct (eq_f f E); auto.
  simpl. inversion H as [[[H1 H2] H3] H4]. rewrite H3.
  rewrite dub_neg_ptree_formula_true.
  + apply (IHP H2 (lor_ind (non_target f) S2)).
  + rewrite H1. simpl. rewrite HS2,non_target_fit. auto.
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


(* Third, we must prove that dub_neg_sub_ptree does not change the ordinal
of an ptree. *)
(* *)
Lemma dub_neg_ptree_ord : forall (P : ptree) (E : formula),
  valid P ->
  forall (S : subst_ind), (ptree_ord (dub_neg_sub_ptree P E S)) = (ptree_ord P).
Proof.
intros P E H. induction P; intros S.
- simpl. case (subst_ind_fit (ptree_formula P) S) eqn:Hfit; simpl; auto.
  rewrite (dub_neg_ptree_formula_true _ _ _ Hfit).
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
- simpl. destruct S; auto. destruct S1; destruct (subst_ind_fit f1 S2); auto.
- simpl. destruct S; destruct (eq_f f E); auto.
- simpl. destruct S; auto; destruct S1; destruct (subst_ind_fit f0 S2) eqn:HS2;
  destruct (eq_f f E); auto.
- simpl. destruct S; auto.
- simpl. destruct S; auto; destruct S1; auto; destruct (subst_ind_fit f0 S2); auto.
- simpl. destruct S; auto.
- simpl. destruct S; auto; destruct S1; auto; destruct (subst_ind_fit f0 S2); auto.
- simpl. destruct (subst_ind_fit f S); auto.
- simpl. destruct (subst_ind_fit f0 S); auto.
- simpl. destruct S; auto. destruct (subst_ind_fit f S1 && subst_ind_fit f1 S2); auto.
Qed.

(* Now we prove that if we have a valid ptree, performing our
double negation substitution on it results in a valid ptree *)
(* *)
Lemma dub_neg_valid : forall (P : ptree) (E : formula),
  valid P ->
  forall (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    valid (dub_neg_sub_ptree P E S).
Proof.
intros P E.
induction P; try intros H S Hs.

- simpl. inversion H as [H1 H2]. inversion Hs. rewrite H3.
  rewrite dub_neg_ptree_formula_true; auto. split.
  + rewrite dub_neg_ptree_deg; auto.
  + apply (IHP H2 S H3).

- simpl. inversion H as [[H1 H2] H3]. inversion Hs. rewrite H4.
  rewrite dub_neg_ptree_formula_true; auto. repeat split.
  + rewrite (dub_neg_ptree_ord _ E H2 S). apply H1.
  + auto.
  + apply H3.

- simpl. destruct (subst_ind_fit f S); apply H.

- simpl. destruct S; inversion Hs. rewrite H1. simpl.
  inversion H as [[[H2 H3] H4] H5].
  repeat split; rewrite dub_neg_ptree_formula_true.
  + rewrite dub_neg_ptree_formula; auto.
    rewrite H2. unfold dub_neg_sub_formula.
    rewrite formula_sub_ind_lor; auto. apply (and_bool_symm _ _ H1).
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + apply IHP. apply H. rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + rewrite dub_neg_ptree_deg; auto.
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + rewrite (dub_neg_ptree_ord _ E H3 (lor_ind S2 S1)). apply H5.
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).

- simpl. destruct S; try destruct S1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H4 H5] H6] H7].
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  repeat split; rewrite dub_neg_ptree_formula_true.
  + rewrite dub_neg_ptree_formula; auto.
    rewrite H4. unfold dub_neg_sub_formula.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H1, H2. auto.
    * simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + apply IHP; auto. rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite dub_neg_ptree_deg; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite dub_neg_ptree_ord; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.

- simpl. destruct S; try destruct S1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H4 H5] H6] H7].
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  repeat split; rewrite dub_neg_ptree_formula_true.
  + rewrite dub_neg_ptree_formula; auto.
    rewrite H4. unfold dub_neg_sub_formula.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H1, H3. auto.
    * simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + apply IHP; auto. rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite dub_neg_ptree_deg; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite dub_neg_ptree_ord; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.

- simpl. destruct S; try destruct S1; try destruct S1_1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H5 H6] H7] H8].
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  destruct (and_bool_prop _ _ H1). clear H1.
  repeat split; rewrite dub_neg_ptree_formula_true.
  + rewrite dub_neg_ptree_formula; auto.
    rewrite H5. unfold dub_neg_sub_formula.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H0,H3. auto.
    * simpl. rewrite H0, H3, H4. auto.
    * simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + apply IHP; auto. rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite dub_neg_ptree_deg; auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite dub_neg_ptree_ord; auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.

- simpl. inversion Hs. rewrite H1. inversion H as [[[H2 H3] H4] H5].
  repeat split; rewrite dub_neg_ptree_formula_true.
  + rewrite dub_neg_ptree_formula; auto.
    unfold dub_neg_sub_formula. rewrite H2.
    rewrite formula_sub_ind_lor; auto. rewrite H1. auto.
  + rewrite H2. simpl. rewrite H1. auto.
  + apply IHP. apply H. rewrite H2. simpl. rewrite H1. auto.
  + rewrite H2. simpl. rewrite H1. auto.
  + rewrite dub_neg_ptree_deg; auto.
  + rewrite H2. simpl. rewrite H1. auto.
  + rewrite dub_neg_ptree_ord; auto.
  + rewrite H2. simpl. rewrite H1. auto.

- simpl. destruct S; inversion Hs. rewrite H1.
  inversion H as [[[H2 H3] H4] H5]. destruct (and_bool_prop _ _ H1).
  repeat split; rewrite dub_neg_ptree_formula_true.
  + rewrite dub_neg_ptree_formula; auto.
    unfold dub_neg_sub_formula. rewrite H2.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H0. auto.
    * simpl. rewrite H0, H6. auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + apply IHP. apply H. rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite dub_neg_ptree_deg; auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite dub_neg_ptree_ord; auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.

- simpl. destruct S; inversion Hs. rewrite H1. simpl.
  inversion H as [[[[H2 H3] H4] H5] H6]. destruct (and_bool_prop _ _ H1).
  repeat split.
  + rewrite dub_neg_ptree_formula_true.
    * rewrite dub_neg_ptree_formula; auto. rewrite H2. auto.
    * rewrite H2. auto.
  + apply dub_neg_sub_formula_closed. auto.
  + rewrite dub_neg_ptree_formula_true.
    * apply IHP; auto. rewrite H2. auto.
    * rewrite H2. auto.
  + rewrite dub_neg_ptree_formula_true.
    * rewrite dub_neg_ptree_deg; auto.
    * rewrite H2. auto.
  + rewrite dub_neg_ptree_formula_true.
    * rewrite dub_neg_ptree_ord; auto.
    * rewrite H2. auto.

- simpl. destruct S; apply H.

- simpl. destruct S; try apply H.
  destruct S1; inversion Hs; rewrite H1; simpl.
  + destruct H as [[[[[[[H2 H3] H4] H5] H6] H7] H8] H9].
    repeat split; rewrite dub_neg_ptree_formula_true.
    * rewrite dub_neg_ptree_formula; auto.
      rewrite H2. unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
      { simpl. destruct (eq_f f (neg E)); auto. }
      { rewrite H1. auto. }
    * rewrite H2. simpl. apply H1.
    * apply IHP1; auto. rewrite H2. apply H1.
    * rewrite H2. simpl. apply H1.
    * rewrite dub_neg_ptree_formula; auto.
      rewrite H4. unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
      { simpl. destruct (eq_f f0 (neg E)); auto. }
      { rewrite H1. auto. }
    * rewrite H4. simpl. apply H1.
    * apply IHP2; auto. rewrite H4. simpl. apply H1.
    * rewrite H4. simpl. apply H1.
    * rewrite dub_neg_ptree_deg; auto.
    * rewrite H2. simpl. apply H1.
    * rewrite dub_neg_ptree_deg; auto.
    * rewrite H4. simpl. apply H1.
    * rewrite dub_neg_ptree_ord; auto.
    * rewrite H2. simpl. apply H1.
    * rewrite dub_neg_ptree_ord; auto.
    * rewrite H4. simpl. apply H1.
  + destruct H as [[[[[[[H2 H3] H4] H5] H6] H7] H8] H9].
    repeat split; rewrite dub_neg_ptree_formula_true.
    * rewrite dub_neg_ptree_formula; auto.
      rewrite H2. unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
      { simpl. destruct (eq_f f (neg E)); auto. }
      { rewrite H1. auto. }
    * rewrite H2. simpl. apply H1.
    * apply IHP1; auto. rewrite H2. apply H1.
    * rewrite H2. simpl. apply H1.
    * rewrite dub_neg_ptree_formula; auto.
      rewrite H4. unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
      { simpl. destruct (eq_f f0 (neg E)); auto. }
      { rewrite H1. auto. }
    * rewrite H4. simpl. apply H1.
    * apply IHP2; auto. rewrite H4. simpl. apply H1.
    * rewrite H4. simpl. apply H1.
    * rewrite dub_neg_ptree_deg; auto.
    * rewrite H2. simpl. apply H1.
    * rewrite dub_neg_ptree_deg; auto.
    * rewrite H4. simpl. apply H1.
    * rewrite dub_neg_ptree_ord; auto.
    * rewrite H2. simpl. apply H1.
    * rewrite dub_neg_ptree_ord; auto.
    * rewrite H4. simpl. apply H1.

- simpl. destruct S; destruct (eq_f f E); try apply H. simpl. inversion H. rewrite H0. destruct X as [[H1 H2] H3]. repeat split; auto. apply ord_succ_monot. apply ord_succ_nf. apply ptree_ord_nf. apply H2.

- simpl. inversion H as [[[H2 H3] H4] H5]. destruct S; try apply H.
  destruct S1; inversion Hs; rewrite H1; simpl.
  + destruct (eq_f f E).
    * simpl. repeat split.
      { rewrite dub_neg_ptree_formula_true, dub_neg_ptree_formula; auto.
        { rewrite H2. unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
          { rewrite non_target_sub. auto. }
          { rewrite non_target_fit, H1. auto. } }
        { rewrite H2. simpl. rewrite non_target_fit, H1. auto. } }
      { rewrite dub_neg_ptree_formula_true; try (apply (IHP H3));
        rewrite H2; simpl; rewrite non_target_fit, H1; auto. }
      { rewrite dub_neg_ptree_formula_true.
        { rewrite dub_neg_ptree_deg; auto. }
        { rewrite H2. simpl. rewrite non_target_fit, H1. auto. } }
      { rewrite dub_neg_ptree_formula_true.
        { rewrite dub_neg_ptree_ord; auto. }
        { rewrite H2. simpl. rewrite non_target_fit, H1. auto. } }
    * simpl. repeat split.
      { rewrite dub_neg_ptree_formula_true, dub_neg_ptree_formula; auto.
        { rewrite H2. unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
          { rewrite non_target_sub. auto. }
          { rewrite non_target_fit, H1. auto. } }
        { rewrite H2. simpl. rewrite non_target_fit, H1. auto. } }
      { rewrite dub_neg_ptree_formula_true; try (apply (IHP H3));
        rewrite H2; simpl; rewrite non_target_fit, H1; auto. }
      { rewrite dub_neg_ptree_formula_true.
        { rewrite dub_neg_ptree_deg; auto. }
        { rewrite H2. simpl. rewrite non_target_fit, H1. auto. } }
      { rewrite dub_neg_ptree_formula_true.
        { rewrite dub_neg_ptree_ord; auto. }
        { rewrite H2. simpl. rewrite non_target_fit, H1. auto. } }
  + destruct (eq_f f E). 
    * simpl. repeat split.
      { rewrite H5. rewrite dub_neg_ptree_formula_true.
        { rewrite dub_neg_ptree_ord. apply ord_succ_monot. apply H3. }
        { rewrite H2. simpl. rewrite non_target_fit, H1. auto. }
        }
      { rewrite dub_neg_ptree_formula_true; try (apply (IHP H3)); rewrite H2; simpl; rewrite non_target_fit, H1; auto. }
      { rewrite H5. apply ord_succ_nf. apply ptree_ord_nf. apply H3. }
    * simpl. repeat split.
      { rewrite dub_neg_ptree_formula_true, dub_neg_ptree_formula; auto.
        { rewrite H2. unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
          { rewrite non_target_sub. auto. }
          { rewrite non_target_fit, H1. auto. } }
        { rewrite H2. simpl. rewrite non_target_fit, H1. auto. } }
      { rewrite dub_neg_ptree_formula_true; try (apply (IHP H3));
        rewrite H2; simpl; rewrite non_target_fit, H1; auto. }
      { rewrite dub_neg_ptree_formula_true.
        { rewrite dub_neg_ptree_deg; auto. }
        { rewrite H2. simpl. rewrite non_target_fit, H1. auto. } }
      { rewrite dub_neg_ptree_formula_true.
        { rewrite dub_neg_ptree_ord; auto. }
        { rewrite H2. simpl. rewrite non_target_fit, H1. auto. } }

- simpl. destruct S; apply H.

- simpl. destruct S; try apply H. inversion H as [[[[H0 H1] H2] H3] H4].
  destruct S1; inversion Hs; rewrite H6; simpl.
  + repeat split; auto.
    * rewrite dub_neg_ptree_formula_true, dub_neg_ptree_formula; auto.
      { rewrite H0. unfold dub_neg_sub_formula.
        { rewrite formula_sub_ind_lor. simpl.
          { destruct (eq_f (substitution f n t)); auto. }
          { simpl. apply H6. } } }
      { rewrite H0. simpl. apply H6. }
    * rewrite dub_neg_ptree_formula_true.
      { apply IHP; auto. rewrite H0. simpl. apply H6. }
      { rewrite H0. simpl. apply H6. }
    * rewrite dub_neg_ptree_formula_true.
      { rewrite dub_neg_ptree_deg; auto. }
      { rewrite H0. simpl. auto. }
    * rewrite dub_neg_ptree_formula_true.
      { rewrite dub_neg_ptree_ord; auto. }
      { rewrite H0. simpl. auto. }
  + repeat split; auto.
    * rewrite dub_neg_ptree_formula_true, dub_neg_ptree_formula; auto.
      { rewrite H0. unfold dub_neg_sub_formula.
        { rewrite formula_sub_ind_lor. simpl.
          { destruct (eq_f (substitution f n t)); auto. }
          { simpl. apply H6. } } }
      { rewrite H0. simpl. apply H6. }
    * rewrite dub_neg_ptree_formula_true.
      { apply IHP; auto. rewrite H0. simpl. apply H6. }
      { rewrite H0. simpl. apply H6. }
    * rewrite dub_neg_ptree_formula_true.
      { rewrite dub_neg_ptree_deg; auto. }
      { rewrite H0. simpl. auto. }
    * rewrite dub_neg_ptree_formula_true.
      { rewrite dub_neg_ptree_ord; auto. }
      { rewrite H0. simpl. auto. }

- intros. simpl. destruct S; apply H.

- rename H into H0. rename X into H. rename Hs into H1.
  simpl. destruct S; try apply H0. destruct S1; inversion H1.
  + rewrite H3. simpl. intros. destruct (valid_w_rule_ad _ _ _ _ _ _ H0 m) as [[[H4 H5] H6] H7].
    repeat split.
    * rewrite dub_neg_ptree_formula_true, dub_neg_ptree_formula; auto.
      { rewrite H4. unfold dub_neg_sub_formula.
        rewrite formula_sub_ind_lor;
        rewrite (non_target_term_sub f n (represent m)).
        { rewrite non_target_sub. auto. }
        { rewrite non_target_fit. apply H3. } }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
    * rewrite dub_neg_ptree_formula_true.
      { apply H. apply H5. rewrite H4. simpl.
        rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
    * rewrite dub_neg_ptree_formula_true.
      { rewrite dub_neg_ptree_deg; auto. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. rewrite H3. auto. }
    * rewrite dub_neg_ptree_formula_true.
      { rewrite dub_neg_ptree_ord; auto. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. rewrite H3. auto. }
  + rewrite H3. simpl. intros. destruct (valid_w_rule_ad _ _ _ _ _ _ H0 m) as [[[H4 H5] H6] H7].
    repeat split.
    * rewrite dub_neg_ptree_formula_true, dub_neg_ptree_formula; auto.
      { rewrite H4. unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
        { rewrite (non_target_term_sub f n (represent m)).
          rewrite non_target_sub. auto. }
        { rewrite (non_target_term_sub f n (represent m)).
          rewrite non_target_fit. apply H3. } }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
    * rewrite dub_neg_ptree_formula_true.
      { apply H. apply H5. rewrite H4. simpl.
        rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
    * rewrite dub_neg_ptree_formula_true.
      { rewrite dub_neg_ptree_deg; auto. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. rewrite H3. auto. }
    * rewrite dub_neg_ptree_formula_true.
      { rewrite dub_neg_ptree_ord; auto. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. rewrite H3. auto. }
- clear IHP2. simpl. destruct (subst_ind_fit f S) eqn:Heq; try apply H. simpl.
  inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  repeat split; auto; rewrite dub_neg_ptree_formula_true.
  + rewrite dub_neg_ptree_formula; auto.
    rewrite H1. unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
    * rewrite non_target_sub. auto.
    * rewrite Heq, non_target_fit. auto.
  + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + apply IHP1; auto. rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + rewrite dub_neg_ptree_deg; auto.
  + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + rewrite dub_neg_ptree_ord; auto.
  + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.

- clear IHP1. simpl. destruct (subst_ind_fit f0 S) eqn:Heq; try apply H. simpl.
  inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  repeat split; auto; rewrite dub_neg_ptree_formula_true.
  + rewrite dub_neg_ptree_formula; auto.
    rewrite H3. unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
    * rewrite non_target_sub. auto.
    * rewrite Heq, non_target_fit. auto.
  + rewrite H3. simpl. auto.
  + apply IHP2; auto. rewrite H3. simpl. auto.
  + rewrite H3. simpl. auto.
  + rewrite dub_neg_ptree_deg; auto.
  + rewrite H3. simpl. auto.
  + rewrite dub_neg_ptree_ord; auto.
  + rewrite H3. simpl. auto.

- simpl. inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  destruct S; try inversion Hs. rewrite H9.
  destruct (and_bool_prop _ _ H9) as [H10 H11].
  simpl. repeat split; rewrite dub_neg_ptree_formula_true.
  + rewrite dub_neg_ptree_formula; auto.
    rewrite H1. unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
    * rewrite non_target_sub. auto.
    * rewrite H10, non_target_fit. auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + apply IHP1; auto. rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite dub_neg_ptree_formula; auto.
    rewrite H3. unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
    * rewrite non_target_sub. auto.
    * rewrite H11, non_target_fit. auto.
  + rewrite H3. simpl. auto.
  + apply IHP2; auto. rewrite H3. simpl. auto.
  + rewrite H3. simpl. auto.
  + rewrite dub_neg_ptree_deg; auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite dub_neg_ptree_deg; auto.
  + rewrite H3. simpl. auto.
  + rewrite dub_neg_ptree_ord; auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite dub_neg_ptree_ord; auto.
  + rewrite H3. simpl. auto.
Qed.





(* We finally show that if the formulas ~~A and/or ~~A \/ D are provable,
so are the formulas A and/or A \/ D *)
(* *)
Lemma double_negation_invertible_a :
  forall (A : formula) (d : nat) (alpha : ord),
  provable (neg (neg A)) d alpha -> provable A d alpha.
Proof.
unfold provable. intros A d alpha H. destruct H as [t [[[Ht1 Ht2] Ht3] Ht4]].
exists (dub_neg_sub_ptree t A (1)). unfold P_proves. repeat split.
- rewrite dub_neg_ptree_formula; auto.
  rewrite Ht1. unfold dub_neg_sub_formula. simpl. rewrite eq_f_refl. auto.
- apply dub_neg_valid; auto. rewrite Ht1. auto.
- rewrite dub_neg_ptree_deg; auto.
- rewrite dub_neg_ptree_ord; auto.
Qed.

Lemma double_negation_invertible_ad :
  forall (A D : formula) (d : nat) (alpha : ord),
  provable (lor (neg (neg A)) D) d alpha -> provable (lor A D) d alpha.
Proof.
unfold provable. intros A D d alpha H. destruct H as [t [[[Ht1 Ht2] Ht3] Ht4]].
exists (dub_neg_sub_ptree t A (lor_ind (1) (non_target D))).
unfold P_proves. repeat split.
- rewrite dub_neg_ptree_formula; auto.
  rewrite Ht1. unfold dub_neg_sub_formula. simpl. rewrite eq_f_refl.
  rewrite non_target_fit. rewrite non_target_sub'. auto.
- apply dub_neg_valid; auto. rewrite Ht1. simpl. rewrite non_target_fit. auto.
- rewrite dub_neg_ptree_deg; auto.
- rewrite dub_neg_ptree_ord; auto.
Qed.