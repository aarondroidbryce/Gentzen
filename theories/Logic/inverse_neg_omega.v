Add LoadPath "theories/Casteran" as Ordering.
Add LoadPath "theories/Maths" as Maths_Facts.
Add LoadPath "theories/Logic" as Systems.

Require Import Program Arith.

From Maths_Facts Require Import naturals.
From Maths_Facts Require Import lists.
From Maths_Facts Require Import ordinals.

From Systems Require Import definitions.
From Systems Require Import fol.
From Systems Require Import PA_omega.
From Systems Require Import proof_trees.
From Systems Require Import substitute.
Require Import Lia.
Require Import Coq.Logic.Eqdep_dec.



Definition neg_w_rule_sub_formula
  (A B : formula) (n : nat) (t : term) (S : subst_ind) : formula :=
  formula_sub_ind A (neg (univ n B)) (neg (substitution B n t)) S.

Lemma neg_w_rule_sub_formula_closed : forall (A : formula),
  closed A = true ->
  forall (B : formula) (n : nat) (t : term) (S : subst_ind), closed_t t = true ->
    closed (neg_w_rule_sub_formula A B n t S) = true.
Proof.
intros. unfold neg_w_rule_sub_formula. apply formula_sub_ind_closed; auto.
intros. apply (closed_univ_sub B n H1 t). auto.
Qed.

Fixpoint neg_w_rule_sub_ptree_fit
  (P : ptree) (E : formula) (n : nat) (t : term) (S : subst_ind) : ptree :=
match P , S with
| deg_up d P', _ => deg_up d (neg_w_rule_sub_ptree_fit P' E n t S)

| ord_up alpha P', _ => ord_up alpha (neg_w_rule_sub_ptree_fit P' E n t S)

| node A, _ => P

| exchange_ab A B d alpha P', lor_ind S_B S_A =>
    exchange_ab
      (neg_w_rule_sub_formula A E n t S_A)
      (neg_w_rule_sub_formula B E n t S_B)
      d alpha
      (neg_w_rule_sub_ptree_fit P' E n t (lor_ind S_A S_B))

| exchange_cab C0 A B d alpha P', lor_ind (lor_ind S_C S_B) S_A =>
    exchange_cab
      (neg_w_rule_sub_formula C0 E n t S_C)
      (neg_w_rule_sub_formula A E n t S_A)
      (neg_w_rule_sub_formula B E n t S_B)
      d alpha
      (neg_w_rule_sub_ptree_fit P' E n t (lor_ind (lor_ind S_C S_A) S_B))

| exchange_abd A B D d alpha P', lor_ind (lor_ind S_B S_A) S_D =>
    exchange_abd
      (neg_w_rule_sub_formula A E n t S_A)
      (neg_w_rule_sub_formula B E n t S_B)
      (neg_w_rule_sub_formula D E n t S_D)
      d alpha
      (neg_w_rule_sub_ptree_fit P' E n t (lor_ind (lor_ind S_A S_B) S_D))

| exchange_cabd C0 A B D d alpha P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D =>
    exchange_cabd
      (neg_w_rule_sub_formula C0 E n t S_C)
      (neg_w_rule_sub_formula A E n t S_A)
      (neg_w_rule_sub_formula B E n t S_B)
      (neg_w_rule_sub_formula D E n t S_D)
      d alpha
      (neg_w_rule_sub_ptree_fit
        P' E n t
        (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D))

| contraction_a A d alpha P', _ =>
    contraction_a
      (neg_w_rule_sub_formula A E n t S)
      d alpha
      (neg_w_rule_sub_ptree_fit P' E n t (lor_ind S S))

| contraction_ad A D d alpha P', lor_ind S_A S_D =>
    contraction_ad
      (neg_w_rule_sub_formula A E n t S_A)
      (neg_w_rule_sub_formula D E n t S_D)
      d alpha
      (neg_w_rule_sub_ptree_fit P' E n t (lor_ind (lor_ind S_A S_A) S_D))

| weakening_ad A D d alpha P', lor_ind S_A S_D =>
    weakening_ad
      (neg_w_rule_sub_formula A E n t S_A)
      (neg_w_rule_sub_formula D E n t S_D)
      d alpha
      (neg_w_rule_sub_ptree_fit P' E n t S_D)

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, _ => P

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_AB S_D =>
    demorgan_abd
      A B
      (neg_w_rule_sub_formula D E n t S_D)
      d1 d2 alpha1 alpha2
      (neg_w_rule_sub_ptree_fit P1 E n t (lor_ind (0) S_D))
      (neg_w_rule_sub_ptree_fit P2 E n t (lor_ind (0) S_D))

| negation_a A d alpha P', _ => P

| negation_ad A D d alpha P', lor_ind S_A S_D =>
    negation_ad
      A
      (neg_w_rule_sub_formula D E n t S_D)
      d alpha
      (neg_w_rule_sub_ptree_fit P' E n t (lor_ind (non_target A) S_D))

| quantification_a A k r d alpha P', _ =>
    (match eq_f A E, eq_nat k n, eq_term t r, S with
          | true, true, true, (1) => (ord_up (ord_succ alpha) P')
          | _,_,_,_ => P
      end)

| quantification_ad A D k r d alpha P', lor_ind S_A S_D =>
    (match eq_f A E, eq_nat k n, eq_term t r, S_A with
    | true, true, true, (1) => (ord_up (ord_succ alpha) P')
    | _, _, _, _ => quantification_ad
        A
        (neg_w_rule_sub_formula D E n t S_D)
        k t d alpha
        (neg_w_rule_sub_ptree_fit P' E n t (lor_ind (0) S_D))
    end)

| w_rule_a A k d alpha g, _ => P

| w_rule_ad A D k d alpha g, lor_ind S_A S_D => 
    w_rule_ad
      A
      (neg_w_rule_sub_formula D E n t S_D)
      k d alpha (fun p => 
      (neg_w_rule_sub_ptree_fit (g p) E n t (S_D)))

| cut_ca C0 A d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ca
      (neg_w_rule_sub_formula C0 E n t S)
      A d1 d2 alpha1 alpha2
      (neg_w_rule_sub_ptree_fit P1 E n t (lor_ind S (non_target A)))
      P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ad
      A
      (neg_w_rule_sub_formula D E n t S)
      d1 d2 alpha1 alpha2
      P1
      (neg_w_rule_sub_ptree_fit P2 E n t (lor_ind (0) S))

| cut_cad C0 A D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_D =>
    cut_cad
      (neg_w_rule_sub_formula C0 E n t S_C)
      A
      (neg_w_rule_sub_formula D E n t S_D)
      d1 d2 alpha1 alpha2
      (neg_w_rule_sub_ptree_fit P1 E n t (lor_ind S_C (non_target A)))
      (neg_w_rule_sub_ptree_fit P2 E n t (lor_ind (0) S_D))

| _, _ => P
end.

Definition neg_w_rule_sub_ptree
  (P : ptree) (E : formula) (n : nat) (t : term) (S : subst_ind) : ptree :=
match subst_ind_fit (ptree_formula P) S with
| false => P
| true => neg_w_rule_sub_ptree_fit P E n t S
end.

Fixpoint neg_w_rule_trace
  (P : ptree) (S : subst_ind) : subst_ind :=
match P , S with
| deg_up d P', _ => neg_w_rule_trace P' S

| ord_up alpha P', _ => neg_w_rule_trace P' S

| quantification_ad A D k r d alpha P', lor_ind S_A S_D => match (subst_ind_fit D S_D) with
    | true => lor_ind S_A (non_target D)
    | false => S
    end

| _,_ => S
end.

Lemma neg_w_rule_simp : forall (P : ptree) (E : formula) (n : nat) (t : term) (S : subst_ind), subst_ind_fit (ptree_formula P) S = true -> neg_w_rule_sub_ptree P E n t S = neg_w_rule_sub_ptree_fit P E n t S .
Proof.
intros. unfold neg_w_rule_sub_ptree. rewrite H. auto.
Qed.
(* First, we must prove that w_rule_sub_ptree simply changes the base formula
of an ptree the way we expect with w_rule_sub_formula *)
(* *)
Lemma neg_w_rule_ptree_formula_aux' :
  forall (P : ptree) (E : formula) (n : nat) (t : term) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
    neg_w_rule_sub_ptree P E n t S = P.
Proof. intros. unfold neg_w_rule_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma neg_w_rule_ptree_formula_aux :
  forall (P : ptree) (E : formula) (n : nat) (t : term) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
      ptree_formula (neg_w_rule_sub_ptree P E n t S) =
      neg_w_rule_sub_formula (ptree_formula P) E n t S.
Proof.
intros. rewrite neg_w_rule_ptree_formula_aux'.
- unfold neg_w_rule_sub_formula. rewrite sub_fit_false. auto. apply H.
- apply H.
Qed.

Lemma neg_w_rule_ptree_formula_true :
  forall (P : ptree) (E : formula) (n : nat) (t : term) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    neg_w_rule_sub_ptree_fit P E n t S = neg_w_rule_sub_ptree P E n t S.
Proof. intros. unfold neg_w_rule_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma neg_w_rule_trace_fits : forall P S, subst_ind_fit (ptree_formula P) S = true -> subst_ind_fit (ptree_formula P) (neg_w_rule_trace P S) = true.
Proof.
intros P. induction P; auto.
intros. simpl. destruct S; inversion H. destruct S1; inversion H; rewrite H2; rewrite non_target_fit; auto.
Qed.

Lemma neg_w_rule_trace_fits_not : forall P S, subst_ind_fit (ptree_formula P) S = false -> subst_ind_fit (ptree_formula P) (neg_w_rule_trace P S) = false.
Proof.
intros P. induction P; auto.
intros. simpl. destruct S; auto. destruct S1; inversion H; try rewrite H1; try rewrite H1; auto. case (subst_ind_fit f0 S2); auto.
Qed.

Lemma neg_w_rule_ptree_formula' : forall (P : ptree) (E : formula) (n : nat),
  valid P ->
  forall (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    {t : term & closed_t t = true /\ ptree_formula (neg_w_rule_sub_ptree P E n t (neg_w_rule_trace P S)) = neg_w_rule_sub_formula (ptree_formula P) E n t (neg_w_rule_trace P S)}.
Proof.
intros P E n.
induction P; try intros H S Hs; unfold neg_w_rule_trace; fold neg_w_rule_trace.

- unfold neg_w_rule_sub_ptree. simpl. rewrite neg_w_rule_trace_fits; auto. destruct H as [H1 H2]. simpl in Hs. simpl. destruct (IHP H2 S Hs) as [r [Hc Hr]]. exists r; auto. rewrite neg_w_rule_ptree_formula_true; auto. rewrite neg_w_rule_trace_fits; auto.

- unfold neg_w_rule_sub_ptree. simpl. rewrite neg_w_rule_trace_fits; auto. destruct H as [[H1 H2] H3]. simpl in Hs. simpl. destruct (IHP H2 S Hs) as [r [Hc Hr]]. exists r; auto. rewrite neg_w_rule_ptree_formula_true; auto. rewrite neg_w_rule_trace_fits; auto.

- exists zero; auto. simpl. inversion H. destruct (axiom_atomic _ H); destruct H0; rewrite H0;
  unfold neg_w_rule_sub_formula; simpl; destruct S; auto.

- exists zero; auto. simpl. destruct S; inversion Hs; rewrite neg_w_rule_simp; simpl; auto; unfold neg_w_rule_sub_formula.
  rewrite formula_sub_ind_lor; auto.

- exists zero; auto. simpl. destruct S; try destruct S1; inversion Hs; rewrite neg_w_rule_simp; simpl; auto; unfold neg_w_rule_sub_formula.
  rewrite formula_sub_ind_lor, formula_sub_ind_lor; auto.
  apply (and_bool_prop _ _ H1).

- exists zero; auto. simpl. destruct S; try destruct S1; inversion Hs; rewrite neg_w_rule_simp; simpl; auto;
  unfold neg_w_rule_sub_formula.
  rewrite formula_sub_ind_lor, formula_sub_ind_lor; auto.
  apply (and_bool_prop _ _ H1).

- exists zero; auto. simpl. destruct S; simpl.
  + unfold neg_w_rule_sub_formula. auto.
  + unfold neg_w_rule_sub_formula. auto.
  + destruct S1; try destruct S1_1; inversion Hs.
    rewrite neg_w_rule_simp; simpl; auto. unfold neg_w_rule_sub_formula.
    destruct (and_bool_prop _ _ H1). destruct (and_bool_prop _ _ H0).
    repeat rewrite formula_sub_ind_lor; auto.

- exists zero; auto. simpl. inversion Hs. rewrite neg_w_rule_simp; simpl; auto.

- exists zero; auto. simpl. destruct S; inversion Hs.
  rewrite neg_w_rule_simp; simpl; auto. unfold neg_w_rule_sub_formula.
  rewrite formula_sub_ind_lor. auto. apply H1.

- exists zero; auto. simpl. destruct S; auto. inversion Hs. rewrite neg_w_rule_simp; simpl; auto.
  unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_lor. auto. apply H1.

- exists zero; auto. simpl. destruct S; auto.

- exists zero; auto. simpl. destruct S.
  + inversion Hs.
  + inversion Hs.
  + destruct S1; inversion Hs; rewrite neg_w_rule_simp; simpl; auto; unfold neg_w_rule_sub_formula;
    rewrite formula_sub_ind_lor; auto; apply H1.

- exists zero; auto. simpl. destruct (eq_f f E) eqn:Heq; destruct S.
  + simpl. unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_0. auto.
  + unfold neg_w_rule_sub_formula. simpl. inversion H as [[[H1 H2] H3] H4]. auto.
  + inversion Hs.
  + simpl. unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_0. auto.
  + unfold neg_w_rule_sub_formula. simpl. auto.
  + inversion Hs.

- exists zero; auto. simpl. destruct (eq_f f E) eqn:Heq; destruct S.
  + inversion Hs.
  + inversion Hs.
  + destruct S1.
    * apply (subst_ind_fit_lor) in Hs. destruct (and_bool_prop _ _ Hs).
    rewrite neg_w_rule_simp; simpl; auto. unfold neg_w_rule_sub_formula.
      rewrite formula_sub_ind_lor, formula_sub_ind_0. auto. apply Hs.
    * inversion Hs. rewrite neg_w_rule_simp; simpl; auto. inversion H as [[[H2 H3] H4] H5].
      unfold neg_w_rule_sub_formula. simpl. rewrite H1. rewrite sub_fit_true; auto.
    * simpl. inversion Hs.
  + inversion Hs.
  + inversion Hs.
  + destruct S1.
    * apply (subst_ind_fit_lor) in Hs. destruct (and_bool_prop _ _ Hs).
      rewrite neg_w_rule_simp; simpl; auto. unfold neg_w_rule_sub_formula.
      rewrite formula_sub_ind_lor, formula_sub_ind_0. auto. apply Hs.
    * inversion Hs. rewrite neg_w_rule_simp; simpl; auto. unfold neg_w_rule_sub_formula.
      rewrite formula_sub_ind_lor; auto.
    * simpl. inversion Hs.

- simpl. destruct H as [[[[X1 X2] X3] X4] X5]. case (eq_f f E) eqn:Y; case (eq_nat n0 n) eqn:Y1.
  + exists t; auto. apply f_eq_decid in Y. destruct Y. apply nat_eq_decid in Y1. destruct Y1. destruct S.
    * rewrite neg_w_rule_simp; auto. unfold neg_w_rule_sub_formula. unfold formula_sub_ind. unfold subst_ind_fit. unfold formula_sub_ind_fit. rewrite eq_f_refl. unfold neg_w_rule_sub_ptree_fit. rewrite eq_f_refl. rewrite eq_nat_refl. rewrite eq_term_refl. simpl. auto.
    * rewrite neg_w_rule_simp; auto. unfold neg_w_rule_sub_formula. unfold formula_sub_ind. unfold subst_ind_fit. unfold formula_sub_ind_fit. rewrite eq_f_refl. unfold neg_w_rule_sub_ptree_fit. rewrite eq_f_refl. rewrite eq_nat_refl. rewrite eq_term_refl. simpl. auto.
    * inversion Hs.
  + exists zero; auto. destruct S; rewrite neg_w_rule_simp; simpl; auto; unfold neg_w_rule_sub_formula; simpl; try rewrite Y; try rewrite Y1; auto.
  + exists zero; auto. destruct S; rewrite neg_w_rule_simp; simpl; auto; unfold neg_w_rule_sub_formula; simpl; try rewrite Y; try rewrite Y1;  auto.
  + exists zero; auto. destruct S; rewrite neg_w_rule_simp; simpl; auto; unfold neg_w_rule_sub_formula; simpl; try rewrite Y; try rewrite Y1;  auto.

- simpl. destruct H as [[[[X1 X2] X3] X4] X5]. case (eq_f f E) eqn:Y; case (eq_nat n0 n) eqn:Y1.
  + exists t; split; auto. apply f_eq_decid in Y. destruct Y. apply nat_eq_decid in Y1. destruct Y1. destruct S.
    * rewrite neg_w_rule_simp; auto.
    * rewrite neg_w_rule_simp; auto. 
    * assert (subst_ind_fit f0 S2 = true) as Z. destruct S1; inversion Hs; auto. rewrite Z. rewrite neg_w_rule_simp; auto. unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_lor; auto. destruct S1; inversion Hs.
      --  repeat rewrite sub_fit_true; auto; try rewrite non_target_fit; auto. simpl. rewrite eq_f_refl. rewrite eq_nat_refl. rewrite eq_term_refl. simpl. unfold neg_w_rule_sub_formula. rewrite sub_fit_true; auto; rewrite non_target_fit. auto.
      --  repeat rewrite sub_fit_true; auto; try rewrite non_target_fit; auto. simpl. rewrite eq_f_refl. rewrite eq_nat_refl. rewrite eq_term_refl. simpl. rewrite X1. rewrite non_target_sub'. auto.
      --  rewrite non_target_fit. destruct S1; inversion Hs; auto.
      --  simpl. rewrite non_target_fit. destruct S1; inversion Hs; try rewrite H0; auto.
  + exists zero; auto. destruct S.
    * simpl. unfold neg_w_rule_sub_formula. simpl. auto.
    * simpl. unfold neg_w_rule_sub_formula. simpl. auto.
    * assert (subst_ind_fit f0 S2 = true) as Z. destruct S1; inversion Hs; auto. rewrite Z. destruct S1; inversion Hs; rewrite neg_w_rule_simp; simpl; auto; try rewrite non_target_fit; auto; unfold neg_w_rule_sub_formula; rewrite Y,Y1; simpl; rewrite Y,Y1; simpl; rewrite non_target_fit; try rewrite H0; try rewrite sub_fit_true; try rewrite non_target_fit; auto.
  + exists zero; auto. destruct S.
    * simpl. unfold neg_w_rule_sub_formula. simpl. auto.
    * simpl. unfold neg_w_rule_sub_formula. simpl. auto.
    * destruct S1; inversion Hs; rewrite neg_w_rule_simp; simpl; auto; try rewrite non_target_fit; auto; unfold neg_w_rule_sub_formula;  try rewrite Y,Y1; simpl; try rewrite non_target_fit; auto; try rewrite Y,Y1; simpl; try rewrite H0; try rewrite sub_fit_true; try rewrite non_target_fit; auto.
  + exists zero; auto. destruct S.
    * simpl. unfold neg_w_rule_sub_formula. simpl. auto.
    * simpl. unfold neg_w_rule_sub_formula. simpl. auto.
    * assert (subst_ind_fit f0 S2 = true) as Z. destruct S1; inversion Hs; auto. rewrite Z. destruct S1; inversion Hs; rewrite neg_w_rule_simp; simpl; auto; try rewrite non_target_fit; auto; unfold neg_w_rule_sub_formula; simpl; try rewrite non_target_fit; auto; try rewrite Y,Y1; simpl; try rewrite Y,Y1; simpl; try rewrite H0; rewrite sub_fit_true; try rewrite non_target_fit; auto.

- exists zero; auto. intros. simpl. destruct S; auto.

- exists zero; auto. intros. simpl. destruct S; auto. destruct S1; auto. 
  + destruct (subst_ind_fit f0 S2) eqn:HS2; rewrite neg_w_rule_simp; simpl; auto.
    * unfold neg_w_rule_sub_formula. simpl. rewrite HS2. rewrite sub_fit_true; auto.
    * unfold neg_w_rule_sub_formula. simpl. rewrite HS2. rewrite sub_fit_false; auto.
  + destruct (subst_ind_fit f0 S2) eqn:HS2; rewrite neg_w_rule_simp; simpl; auto.
    * unfold neg_w_rule_sub_formula. simpl. rewrite HS2. rewrite sub_fit_true; auto.
    * unfold neg_w_rule_sub_formula. simpl. rewrite HS2. rewrite sub_fit_false; auto.

- exists zero; auto. simpl. inversion Hs. rewrite neg_w_rule_simp; simpl; auto.

- exists zero; auto. simpl. inversion Hs. rewrite neg_w_rule_simp; simpl; auto. 

- exists zero; auto. simpl. destruct S; inversion Hs. rewrite neg_w_rule_simp; simpl; auto.
  unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_lor; auto.
Qed.


Lemma neg_w_rule_ptree_formula : forall (P : ptree) (E : formula) (n : nat),
  valid P ->
  forall (S : subst_ind),
    {t : term & closed_t t = true /\ ptree_formula (neg_w_rule_sub_ptree P E n t (neg_w_rule_trace P S)) =
    neg_w_rule_sub_formula (ptree_formula P) E n t (neg_w_rule_trace P S)}.
Proof.
intros. destruct (subst_ind_fit (ptree_formula P) S) eqn:Hs.
- apply neg_w_rule_ptree_formula'; auto.
- exists zero; split; auto. apply neg_w_rule_ptree_formula_aux. apply neg_w_rule_trace_fits_not. auto.
Defined.

(* Second, we must prove that w_rule_sub_ptree does not change the degree
of an ptree. *)
(* *)
Lemma neg_w_rule_ptree_deg : forall (P : ptree) (E : formula) (n : nat) (t : term),
  valid P ->
  forall (S : subst_ind), ptree_deg P = ptree_deg (neg_w_rule_sub_ptree P E n t S).
Proof.
intros P E n t H. induction P; intros S; unfold neg_w_rule_sub_ptree.
- simpl. case (subst_ind_fit (ptree_formula P) S); auto.
- simpl. case (subst_ind_fit (ptree_formula P) S) eqn:Hfit; auto. simpl.
  rewrite (neg_w_rule_ptree_formula_true _ _ _ _ _ Hfit).
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
- simpl. destruct S; auto. destruct S1; destruct (subst_ind_fit f1 S2); auto.
- simpl. destruct S; auto.
- simpl. destruct S; auto.
  destruct S1; auto; destruct (subst_ind_fit f0 S2) eqn:HS2; auto.
- simpl. destruct S; case (eq_f f E); case (eq_nat n0 n); case (eq_term t t0); auto. simpl. destruct H as [[X1 X2] X3]. auto.
- simpl. destruct S; auto; destruct S1; auto; case (subst_ind_fit f0 S2) eqn:X; case (eq_f f E); case (eq_nat n0 n); case (eq_term t t0); auto. simpl. destruct H as [[[[X1 X2] X3] X4] X5]. auto.
- simpl. destruct S; auto.
- simpl. destruct S; auto. destruct S1; auto; destruct (subst_ind_fit f0 S2) eqn:HS2; simpl; auto.
- simpl. destruct (subst_ind_fit f S); auto.
- simpl. destruct (subst_ind_fit f0 S); auto.
- simpl. destruct S; auto. destruct (subst_ind_fit f S1 && subst_ind_fit f1 S2); auto.
Qed.


(* Third, we must prove that w_rule_sub_ptree does not change the ordinal
of an ptree. *)
(* *)
Lemma neg_w_rule_ptree_ord : forall (P : ptree) (E : formula) (n : nat) (t : term),
  valid P ->
  forall (S : subst_ind), ptree_ord (neg_w_rule_sub_ptree P E n t S) = ptree_ord P.
Proof.
intros P E n t H. induction P; intros S; unfold neg_w_rule_sub_ptree.
- simpl. case (subst_ind_fit (ptree_formula P) S) eqn:Hfit; auto. simpl.
  rewrite (neg_w_rule_ptree_formula_true _ _ _ _ _ Hfit).
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
- simpl. destruct S; auto; case (eq_f f E); case (eq_nat n0 n); case (eq_term t t0); auto.
- simpl. destruct S; auto. destruct S1; destruct (subst_ind_fit f0 S2) eqn:HS2; auto.
- simpl. destruct S; auto; case (eq_f f E); case (eq_nat n0 n); case (eq_term t t0); auto.
- simpl. destruct S; auto; destruct S1; auto; destruct (subst_ind_fit f0 S2); auto; case (eq_f f E); case (eq_nat n0 n); case (eq_term t t0); auto.
- simpl. destruct S; auto.
- simpl. destruct S; auto. destruct S1; auto; destruct (subst_ind_fit f0 S2) eqn:HS2; simpl; auto.
- simpl. destruct (subst_ind_fit f S); auto.
- simpl. destruct (subst_ind_fit f0 S); auto.
- simpl. destruct S; auto. destruct (subst_ind_fit f S1 && subst_ind_fit f1 S2); auto.
Qed.

(* (neg_w_rule_trace P S) *)

Definition neg_w_rule_counter (P : ptree) (E : formula) (n : nat) (H : valid P) (S : subst_ind) : term := (projT1 (neg_w_rule_ptree_formula P E n H S)).

Lemma neg_w_rule_counter_closed : forall (P : ptree) (E : formula) (n : nat) (H : valid P) (S : subst_ind), closed_t (neg_w_rule_counter P E n H S) = true.
Proof.
intros. unfold neg_w_rule_counter. destruct neg_w_rule_ptree_formula. simpl. destruct a. auto.
Qed.

Lemma neg_w_rule_counter_formula : forall (P : ptree) (E : formula) (n : nat) (H : valid P) (S : subst_ind), ptree_formula (neg_w_rule_sub_ptree P E n (neg_w_rule_counter P E n H S) (neg_w_rule_trace P S)) = neg_w_rule_sub_formula (ptree_formula P) E n (neg_w_rule_counter P E n H S) (neg_w_rule_trace P S).
Proof.
intros. unfold neg_w_rule_counter. destruct neg_w_rule_ptree_formula. simpl. destruct a. auto.
Qed.

(* Now we prove that if we have a valid ptree, performing our
w_rule substitution on it results in a valid ptree *)
(* *)
Lemma neg_w_rule_valid : forall (P : ptree) (E : formula) (n : nat) (H : valid P) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
      valid (neg_w_rule_sub_ptree P E n (neg_w_rule_counter P E n H S) S).
Proof.
intros P E n.
induction P; try intros H S Hs; unfold neg_w_rule_sub_ptree.

- simpl. inversion H as [H1 H2]. inversion Hs. rewrite H3.
  pose proof (IHP H2 S H3) as Ht.
  rewrite neg_w_rule_ptree_formula_true; auto. split; simpl; auto. 
  rewrite <- neg_w_rule_ptree_deg; auto. admit.

- simpl. inversion H as [[H1 H2] H3]. inversion Hs. rewrite H4.
  pose proof (IHP H2 S Hs) as Ht.
  rewrite neg_w_rule_ptree_formula_true; auto. repeat split; simpl; auto. 
  rewrite neg_w_rule_ptree_ord; auto. admit.

- simpl. destruct (subst_ind_fit f S); apply H.

- simpl. destruct S; inversion Hs. rewrite H1.
  inversion H as [[[H2 H3] H4] H5].
  assert (subst_ind_fit (ptree_formula P) (lor_ind S2 S1) = true) as Z. rewrite H2. simpl. apply and_bool_symm; auto.
  pose proof (IHP H3 (lor_ind S2 S1) Z) as Ht.
  rewrite neg_w_rule_ptree_formula_true; auto. repeat split; auto.
  + admit.
  + admit.
  + rewrite <- neg_w_rule_ptree_deg; auto.
  + rewrite neg_w_rule_ptree_ord; auto.

- simpl. destruct S; try destruct S1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H4 H5] H6] H7].
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  repeat split; rewrite neg_w_rule_ptree_formula_true.
  + admit.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + admit.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite <- neg_w_rule_ptree_deg; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite neg_w_rule_ptree_ord; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.

- simpl. destruct S; try destruct S1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H4 H5] H6] H7].
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  repeat split; rewrite neg_w_rule_ptree_formula_true.
  + admit.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + admit.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite <- neg_w_rule_ptree_deg; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite neg_w_rule_ptree_ord; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.

- simpl. destruct S; try destruct S1; try destruct S1_1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H5 H6] H7] H8].
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  destruct (and_bool_prop _ _ H1). clear H1.
  repeat split; rewrite neg_w_rule_ptree_formula_true.
  + admit.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + admit.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite <- neg_w_rule_ptree_deg; auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite neg_w_rule_ptree_ord; auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.

- simpl. inversion Hs. rewrite H1. inversion H as [[[H2 H3] H4] H5].
  repeat split; rewrite neg_w_rule_ptree_formula_true.
  + admit.
  + rewrite H2. simpl. rewrite H1. auto.
  + admit.
  + rewrite H2. simpl. rewrite H1. auto.
  + rewrite <- neg_w_rule_ptree_deg; auto.
  + rewrite H2. simpl. rewrite H1. auto.
  + rewrite neg_w_rule_ptree_ord; auto.
  + rewrite H2. simpl. rewrite H1. auto.

- simpl. destruct S; inversion Hs. rewrite H1.
  inversion H as [[[H2 H3] H4] H5]. destruct (and_bool_prop _ _ H1).
  repeat split; rewrite neg_w_rule_ptree_formula_true.
  + admit.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + admit.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite <- neg_w_rule_ptree_deg; auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite neg_w_rule_ptree_ord; auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.

- simpl. destruct S; inversion Hs. rewrite H1. simpl.
  inversion H as [[[[H2 H3] H4] H5] H6]. destruct (and_bool_prop _ _ H1).
  repeat split; try rewrite neg_w_rule_ptree_formula_true; try rewrite H2; auto.
  + admit.
  + apply neg_w_rule_sub_formula_closed. auto. apply neg_w_rule_counter_closed.
  + admit.
  + rewrite <- neg_w_rule_ptree_deg; auto.
  + rewrite neg_w_rule_ptree_ord; auto.

- simpl. destruct S; apply H.

- simpl. destruct S; try apply H.
  destruct H as [[[[[[[H2 H3] H4] H5] H6] H7] H8] H9].
  assert (subst_ind_fit (ptree_formula P1) (lor_ind (0) S2) = true) as Z. inversion Hs. rewrite H2. destruct S1; simpl; auto. inversion H0.
  assert (subst_ind_fit (ptree_formula P1) (lor_ind (1) S2) = true) as Z1. inversion Hs. rewrite H2. destruct S1; simpl; auto. inversion H0.
  assert (subst_ind_fit (ptree_formula P2) (lor_ind (0) S2) = true) as Z2. inversion Hs. rewrite H4. destruct S1; simpl; auto. inversion H0.
  assert (subst_ind_fit (ptree_formula P2) (lor_ind (1) S2) = true) as Z3. inversion Hs. rewrite H4. destruct S1; simpl; auto. inversion H0.
  destruct S1; inversion Hs; rewrite H0; simpl.
  + repeat split; rewrite neg_w_rule_ptree_formula_true; auto.
    * admit.
    * admit.
    * admit.
    * admit.
    * rewrite H6. rewrite <- neg_w_rule_ptree_deg; auto.
    * rewrite H7. rewrite <- neg_w_rule_ptree_deg; auto.
    * rewrite neg_w_rule_ptree_ord; auto.
    * rewrite neg_w_rule_ptree_ord; auto.
  + repeat split; rewrite neg_w_rule_ptree_formula_true; auto.
    * admit.
    * admit.
    * admit.
    * admit.
    * rewrite H6. rewrite <- neg_w_rule_ptree_deg; auto.
    * rewrite H7. rewrite <- neg_w_rule_ptree_deg; auto.
    * rewrite neg_w_rule_ptree_ord; auto.
    * rewrite neg_w_rule_ptree_ord; auto.

- simpl. destruct S; destruct (eq_f f E); apply H.

- simpl. inversion H as [[[H1 H2] H3] H4]. destruct S; auto.
  destruct S1; auto; destruct (subst_ind_fit f0 S2) eqn:HS2; simpl;
  repeat split; auto; rewrite w_rule_ptree_formula_true;
  try apply IHP; auto; try rewrite H1; simpl; try rewrite non_target_fit,HS2;
  try rewrite w_rule_ptree_deg; try rewrite w_rule_ptree_ord; auto.
  + rewrite w_rule_ptree_formula; auto. rewrite H1.
    unfold w_rule_sub_formula. simpl. rewrite non_target_fit,HS2.
    simpl. rewrite <- sub_fit_true; auto.
    * rewrite non_target_sub. rewrite <- sub_fit_true; auto.
    * apply non_target_fit.
  + rewrite H3. apply w_rule_ptree_deg; auto.
  + rewrite w_rule_ptree_formula; auto. rewrite H1.
    unfold w_rule_sub_formula. simpl. rewrite non_target_fit,HS2.
    simpl. rewrite <- sub_fit_true; auto.
    * rewrite non_target_sub. rewrite <- sub_fit_true; auto.
    * apply non_target_fit.
  + rewrite H3. apply w_rule_ptree_deg; auto.

- simpl. destruct S; auto.

- simpl. destruct S; try apply H. inversion H as [[[[H0 H1] H2] H3] H4].
  destruct S1; inversion Hs; rewrite H6; simpl.
  + repeat split; auto.
    * rewrite w_rule_ptree_formula_true, w_rule_ptree_formula; auto.
      { rewrite H0. unfold w_rule_sub_formula.
        { rewrite formula_sub_ind_lor. simpl.
          { destruct (eq_f (substitution f n t)); auto. }
          { simpl. apply H6. } } }
      { rewrite H0. simpl. apply H6. }
    * rewrite w_rule_ptree_formula_true.
      { apply IHP; auto. rewrite H0. simpl. apply H6. }
      { rewrite H0. simpl. apply H6. }
    * rewrite w_rule_ptree_formula_true.
      { rewrite H3. apply w_rule_ptree_deg; auto. }
      { rewrite H0. simpl. auto. }
    * rewrite w_rule_ptree_formula_true.
      { rewrite w_rule_ptree_ord; auto. }
      { rewrite H0. simpl. auto. }
  + repeat split; auto.
    * rewrite w_rule_ptree_formula_true, w_rule_ptree_formula; auto.
      { rewrite H0. unfold w_rule_sub_formula.
        { rewrite formula_sub_ind_lor. simpl.
          { destruct (eq_f (substitution f n t)); auto. }
          { simpl. apply H6. } } }
      { rewrite H0. simpl. apply H6. }
    * rewrite w_rule_ptree_formula_true.
      { apply IHP; auto. rewrite H0. simpl. apply H6. }
      { rewrite H0. simpl. apply H6. }
    * rewrite w_rule_ptree_formula_true.
      { rewrite H3. apply w_rule_ptree_deg; auto. }
      { rewrite H0. simpl. auto. }
    * rewrite w_rule_ptree_formula_true.
      { rewrite w_rule_ptree_ord; auto. }
      { rewrite H0. simpl. auto. }

- rename f into A. rename p into g. rename n1 into d. rename o into alpha.
  destruct (valid_w_rule_a A n0 d alpha g H m) as [[[H1 H2] H3] H4].
  simpl. destruct S; auto;
  destruct (eq_nat d (ptree_deg (g m))) eqn:HD; destruct (eq_f A E) eqn:HE; auto; destruct (eq_nat n0 n) eqn:Hn; simpl; auto; repeat split; auto.
  rewrite H4. apply omega_exp_incr.
  apply single_nf. rewrite H4. apply (ptree_ord_nf (g m) H2).
  apply leq_type in H3. destruct H3 as [H3 | H3]. auto. rewrite H3 in HD. rewrite eq_nat_refl in HD. inversion HD.
  rewrite H4. apply omega_exp_incr.
  apply single_nf. rewrite H4. apply (ptree_ord_nf (g m) H2).

- rename f into A. rename f0 into D. rename p into g.
  rename n1 into d. rename o into alpha.
  simpl. destruct S; auto. destruct S1; auto.
  + destruct (eq_nat d (ptree_deg (g m))) eqn:HD.
    * destruct (eq_f A E) eqn:HE.
      { destruct (subst_ind_fit D S2) eqn:HS2; simpl.
        { destruct (eq_nat n0 n) eqn:Hn; simpl; intros p;
          destruct (valid_w_rule_ad A D n0 d alpha g H p) as [[[H1 H2] H3] H4].
          { repeat split; rewrite w_rule_ptree_formula_true;
            try rewrite w_rule_ptree_deg; try rewrite w_rule_ptree_ord; auto;
            try rewrite w_rule_ptree_formula; try apply X; auto;
            try rewrite H1; simpl; try rewrite (non_target_term_sub A n0 (represent p));
            try rewrite non_target_fit,HS2; auto;
            unfold w_rule_sub_formula; try rewrite non_target_sub_lor; auto.
            pose proof (w_rule_ptree_deg (g p) E n m H2 (lor_ind (non_target (substitution A n0 (represent p))) S2 )). lia. }
          { repeat split; rewrite w_rule_ptree_formula_true;
          try rewrite w_rule_ptree_deg; try rewrite w_rule_ptree_ord; auto;
          try rewrite w_rule_ptree_formula; try apply X; auto;
          try rewrite H1; simpl; try rewrite (non_target_term_sub A n0 (represent p));
          try rewrite non_target_fit,HS2; auto;
          unfold w_rule_sub_formula; try rewrite non_target_sub_lor; auto.
          pose proof (w_rule_ptree_deg (g p) E n m H2 (lor_ind (non_target (substitution A n0 (represent p))) S2 )). lia. } }
        { destruct (eq_nat n0 n) eqn:Hn; simpl; intros p;
          destruct (valid_w_rule_ad A D n0 d alpha g H p) as [[[H1 H2] H3] H4];
          repeat split; auto. } }
      { destruct (subst_ind_fit D S2) eqn:HS2; simpl; intro p;
        destruct (valid_w_rule_ad A D n0 d alpha g H p) as [[[H1 H2] H3] H4];
        repeat split; auto; rewrite w_rule_ptree_formula_true;
        try rewrite w_rule_ptree_deg; try rewrite w_rule_ptree_ord; auto;
        try rewrite w_rule_ptree_formula; try apply X; auto;
        try rewrite H1; simpl; rewrite (non_target_term_sub A n0 (represent p));
        try rewrite non_target_fit,HS2; auto.
        unfold w_rule_sub_formula. rewrite non_target_sub_lor. auto.
        pose proof (w_rule_ptree_deg (g p) E n m H2 (lor_ind (non_target (substitution A n0 (represent p))) S2 )). lia. }
    * destruct (eq_f A E) eqn:HE.
      { destruct (subst_ind_fit D S2) eqn:HS2; simpl.
        { destruct (eq_nat n0 n) eqn:Hn; simpl; intros p;
          destruct (valid_w_rule_ad A D n0 d alpha g H p) as [[[H1 H2] H3] H4].
          { repeat split; rewrite w_rule_ptree_formula_true;
            try rewrite w_rule_ptree_deg; try rewrite w_rule_ptree_ord; auto;
            try rewrite w_rule_ptree_formula; try apply X; auto;
            try rewrite H1; simpl; try rewrite (non_target_term_sub A n0 (represent p));
            try rewrite non_target_fit,HS2; auto;
            unfold w_rule_sub_formula; try rewrite non_target_sub_lor; auto.
            pose proof (w_rule_ptree_deg (g p) E n m H2 (lor_ind (non_target (substitution A n0 (represent p))) S2 )). lia. }
          { repeat split; rewrite w_rule_ptree_formula_true;
          try rewrite w_rule_ptree_deg; try rewrite w_rule_ptree_ord; auto;
          try rewrite w_rule_ptree_formula; try apply X; auto;
          try rewrite H1; simpl; try rewrite (non_target_term_sub A n0 (represent p));
          try rewrite non_target_fit,HS2; auto;
          unfold w_rule_sub_formula; try rewrite non_target_sub_lor; auto.
          pose proof (w_rule_ptree_deg (g p) E n m H2 (lor_ind (non_target (substitution A n0 (represent p))) S2 )). lia. } }
        { destruct (eq_nat n0 n) eqn:Hn; simpl; intros p;
          destruct (valid_w_rule_ad A D n0 d alpha g H p) as [[[H1 H2] H3] H4];
          repeat split; auto. } }
      { destruct (subst_ind_fit D S2) eqn:HS2; simpl; intro p;
        destruct (valid_w_rule_ad A D n0 d alpha g H p) as [[[H1 H2] H3] H4];
        repeat split; auto; rewrite w_rule_ptree_formula_true;
        try rewrite w_rule_ptree_deg; try rewrite w_rule_ptree_ord; auto;
        try rewrite w_rule_ptree_formula; try apply X; auto;
        try rewrite H1; simpl; rewrite (non_target_term_sub A n0 (represent p));
        try rewrite non_target_fit,HS2; auto.
        unfold w_rule_sub_formula. rewrite non_target_sub_lor. auto.
        pose proof (w_rule_ptree_deg (g p) E n m H2 (lor_ind (non_target (substitution A n0 (represent p))) S2 )). lia. }
  + destruct (eq_nat d (ptree_deg (g m))) eqn:HD.
    * destruct (eq_f A E) eqn:HE.
      { destruct (subst_ind_fit D S2) eqn:HS2.
        { simpl. destruct (eq_nat n0 n) eqn:Hn.
          { destruct (valid_w_rule_ad A D n0 d alpha g H m) as [[[H1 H2] H3] H4].
            unfold valid. fold valid. repeat split.
            { rewrite <- w_rule_simp.
              rewrite (w_rule_ptree_ord (g m) E n m H2 (lor_ind (non_target A) S2)).
              rewrite H4. apply omega_exp_incr. 
              rewrite H1. simpl. rewrite HS2. rewrite (non_target_term_sub _ n0 (represent m)). rewrite non_target_fit. auto. }
            { rewrite w_rule_ptree_formula_true; try apply X; auto;
              rewrite H1; simpl; rewrite (non_target_term_sub A n0 (represent m));
              rewrite non_target_fit,HS2; auto. }
            { rewrite H4. apply single_nf. apply ptree_ord_nf. auto. } }
          { simpl. intro p.
            destruct (valid_w_rule_ad A D n0 d alpha g H p) as [[[H1 H2] H3] H4].
            repeat split; rewrite w_rule_ptree_formula_true;
            try rewrite w_rule_ptree_deg; try rewrite w_rule_ptree_ord; auto;
            try rewrite w_rule_ptree_formula; try apply X; auto;
            try rewrite H1; simpl; rewrite (non_target_term_sub A n0 (represent p));
            try rewrite non_target_fit,HS2; auto.
            unfold w_rule_sub_formula. rewrite non_target_sub_lor. auto. 
            pose proof (w_rule_ptree_deg (g p) E n m H2 (lor_ind (non_target (substitution A n0 (represent p))) S2 )). lia. } }
        { simpl. intro p.
          destruct (valid_w_rule_ad A D n0 d alpha g H p) as [[[H1 H2] H3] H4].
          repeat split; auto. } }
      { destruct (subst_ind_fit D S2) eqn:HS2; simpl; intro p;
        destruct (valid_w_rule_ad A D n0 d alpha g H p) as [[[H1 H2] H3] H4];
        repeat split; auto; rewrite w_rule_ptree_formula_true;
        try rewrite w_rule_ptree_deg; try rewrite w_rule_ptree_ord; auto;
        try rewrite w_rule_ptree_formula; try apply X; auto;
        try rewrite H1; simpl; rewrite (non_target_term_sub A n0 (represent p));
        try rewrite non_target_fit,HS2; auto.
        unfold w_rule_sub_formula. rewrite non_target_sub_lor. auto.
        pose proof (w_rule_ptree_deg (g p) E n m H2 (lor_ind (non_target (substitution A n0 (represent p))) S2 )). lia. }
    * destruct (eq_f A E) eqn:HE.
      { destruct (subst_ind_fit D S2) eqn:HS2.
        { simpl. destruct (eq_nat n0 n) eqn:Hn.
          { destruct (valid_w_rule_ad A D n0 d alpha g H m) as [[[H1 H2] H3] H4].
            apply leq_type in H3. destruct H3 as [H3 | H3].
            { rewrite w_rule_ptree_formula_true.
              { simpl. repeat split.
                { rewrite <- (w_rule_ptree_deg (g m) E n m H2 (lor_ind (non_target A) S2)). auto. }
                { rewrite (w_rule_ptree_ord (g m) E n m H2 (lor_ind (non_target A) S2)).
                  rewrite H4. apply omega_exp_incr. }
                { apply X. auto. rewrite H1. simpl. rewrite (non_target_term_sub A n0 (represent m)).
                  rewrite non_target_fit,HS2. auto. }
                { rewrite H4. apply single_nf. apply ptree_ord_nf. auto. } }
              { rewrite H1. simpl. rewrite (non_target_term_sub A n0 (represent m)).
                rewrite non_target_fit,HS2. auto. } }
            { rewrite H3 in HD. rewrite eq_nat_refl in HD. inversion HD. } }
          { simpl. intro p.
            destruct (valid_w_rule_ad A D n0 d alpha g H p) as [[[H1 H2] H3] H4].
            repeat split; rewrite w_rule_ptree_formula_true;
            try rewrite w_rule_ptree_deg; try rewrite w_rule_ptree_ord; auto;
            try rewrite w_rule_ptree_formula; try apply X; auto;
            try rewrite H1; simpl; rewrite (non_target_term_sub A n0 (represent p));
            try rewrite non_target_fit,HS2; auto.
            unfold w_rule_sub_formula. rewrite non_target_sub_lor. auto. 
            pose proof (w_rule_ptree_deg (g p) E n m H2 (lor_ind (non_target (substitution A n0 (represent p))) S2 )). lia. } }
        { simpl. intro p.
          destruct (valid_w_rule_ad A D n0 d alpha g H p) as [[[H1 H2] H3] H4].
          repeat split; auto. } }
      { destruct (subst_ind_fit D S2) eqn:HS2; simpl; intro p;
        destruct (valid_w_rule_ad A D n0 d alpha g H p) as [[[H1 H2] H3] H4];
        repeat split; auto; rewrite w_rule_ptree_formula_true;
        try rewrite w_rule_ptree_deg; try rewrite w_rule_ptree_ord; auto;
        try rewrite w_rule_ptree_formula; try apply X; auto;
        try rewrite H1; simpl; rewrite (non_target_term_sub A n0 (represent p));
        try rewrite non_target_fit,HS2; auto.
        unfold w_rule_sub_formula. rewrite non_target_sub_lor. auto.
        pose proof (w_rule_ptree_deg (g p) E n m H2 (lor_ind (non_target (substitution A n0 (represent p))) S2 )). lia. }

- clear IHP2. simpl. destruct (subst_ind_fit f S) eqn:Heq; try apply H. simpl.
  inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  repeat split; auto; rewrite w_rule_ptree_formula_true.
  + rewrite w_rule_ptree_formula; auto.
    rewrite H1. unfold w_rule_sub_formula. rewrite formula_sub_ind_lor.
    * rewrite non_target_sub. auto.
    * rewrite Heq, non_target_fit. auto.
  + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + apply IHP1; auto. rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + rewrite H5. apply w_rule_ptree_deg; auto.
  + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + rewrite w_rule_ptree_ord; auto.
  + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.

- clear IHP1. simpl. destruct (subst_ind_fit f0 S) eqn:Heq; try apply H. simpl.
  inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  repeat split; auto; rewrite w_rule_ptree_formula_true.
  + rewrite w_rule_ptree_formula; auto.
    rewrite H3. unfold w_rule_sub_formula. rewrite formula_sub_ind_lor.
    * rewrite non_target_sub. auto.
    * rewrite Heq, non_target_fit. auto.
  + rewrite H3. simpl. auto.
  + apply IHP2; auto. rewrite H3. simpl. auto.
  + rewrite H3. simpl. auto.
  + rewrite H6. apply w_rule_ptree_deg; auto.
  + rewrite H3. simpl. auto.
  + rewrite w_rule_ptree_ord; auto.
  + rewrite H3. simpl. auto.

- simpl. inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  destruct S; try inversion Hs. rewrite H9.
  destruct (and_bool_prop _ _ H9) as [H10 H11].
  simpl. repeat split; rewrite w_rule_ptree_formula_true.
  + rewrite w_rule_ptree_formula; auto.
    rewrite H1. unfold w_rule_sub_formula. rewrite formula_sub_ind_lor.
    * rewrite non_target_sub. auto.
    * rewrite H10, non_target_fit. auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + apply IHP1; auto. rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite w_rule_ptree_formula; auto.
    rewrite H3. unfold w_rule_sub_formula. rewrite formula_sub_ind_lor.
    * rewrite non_target_sub. auto.
    * rewrite H11, non_target_fit. auto.
  + rewrite H3. simpl. auto.
  + apply IHP2; auto. rewrite H3. simpl. auto.
  + rewrite H3. simpl. auto.
  + rewrite H5. apply w_rule_ptree_deg; auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite H6. apply w_rule_ptree_deg; auto.
  + rewrite H3. simpl. auto.
  + rewrite w_rule_ptree_ord; auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite w_rule_ptree_ord; auto.
  + rewrite H3. simpl. auto.
Qed.




(* We finally show that if the formulas (univ n E) and/or (univ n E) \/ D are provable,
so are the formulas E(m) and/or E(m) \/ D for any m *)
(* *)
Lemma w_rule_invertible_a :
  forall (A : formula) (n m d : nat) (alpha : ord),
  provable (univ n A) d alpha ->
  provable (substitution A n (represent m)) d alpha.
Proof.
unfold provable. intros A n m d alpha H.
destruct H as [t [[[Ht1 Ht2] Ht3] Ht4]].
exists (w_rule_sub_ptree t A n m (1)). unfold P_proves. repeat split.
- rewrite w_rule_ptree_formula; auto. rewrite Ht1. unfold w_rule_sub_formula.
  simpl. rewrite eq_nat_refl,eq_f_refl. auto.
- apply w_rule_valid; auto. rewrite Ht1. auto.
- rewrite <- (w_rule_ptree_deg t); auto.
- rewrite w_rule_ptree_ord; auto.
Qed.

Lemma w_rule_invertible_ad :
  forall (A D : formula) (n m d : nat) (alpha : ord),
  provable (lor (univ n A) D) d alpha ->
  provable (lor (substitution A n (represent m)) D) d alpha.
Proof.
unfold provable. intros A D n m d alpha H.
destruct H as [t [[[Ht1 Ht2] Ht3] Ht4]].
pose proof (w_rule_ptree_deg t A n m Ht2 (lor_ind (1) (non_target D))).
exists (w_rule_sub_ptree t A n m (lor_ind (1) (non_target D))). unfold P_proves. repeat split.
- rewrite w_rule_ptree_formula; auto. rewrite Ht1. unfold w_rule_sub_formula.
  simpl. rewrite eq_nat_refl,eq_f_refl,non_target_fit. simpl.
  rewrite non_target_sub'. auto.
- apply w_rule_valid; auto. rewrite Ht1. simpl. rewrite non_target_fit. auto.
- rewrite <- (w_rule_ptree_deg t); auto.
- rewrite w_rule_ptree_ord; auto.
Qed.
