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

(* Defining vanilla formula substitution on proof trees *)
(* *)
Fixpoint formula_sub_ptree_fit
  (P : ptree) (E F : formula) (S : subst_ind) : ptree :=
match P, S with
| deg_up d P', _ => deg_up d (formula_sub_ptree_fit P' E F S)

| ord_up alpha P', _ => ord_up alpha (formula_sub_ptree_fit P' E F S)

| node A, _ => node (formula_sub_ind_fit A E F S)

| exchange_ab A B d alpha P', lor_ind S_B S_A =>
    exchange_ab
      (formula_sub_ind_fit A E F S_A)
      (formula_sub_ind_fit B E F S_B)
      d alpha
      (formula_sub_ptree_fit P' E F (lor_ind S_A S_B))

| exchange_cab C0 A B d alpha P', lor_ind (lor_ind S_C S_B) S_A =>
    exchange_cab
      (formula_sub_ind_fit C0 E F S_C)
      (formula_sub_ind_fit A E F S_A)
      (formula_sub_ind_fit B E F S_B)
      d alpha
      (formula_sub_ptree_fit P' E F (lor_ind (lor_ind S_C S_A) S_B))

| exchange_abd A B D d alpha P', lor_ind (lor_ind S_B S_A) S_D =>
    exchange_abd
      (formula_sub_ind_fit A E F S_A)
      (formula_sub_ind_fit B E F S_B)
      (formula_sub_ind_fit D E F S_D)
      d alpha
      (formula_sub_ptree_fit P' E F (lor_ind (lor_ind S_A S_B) S_D))

| exchange_cabd C0 A B D d alpha P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D =>
    exchange_cabd
      (formula_sub_ind_fit C0 E F S_C)
      (formula_sub_ind_fit A E F S_A)
      (formula_sub_ind_fit B E F S_B)
      (formula_sub_ind_fit D E F S_D)
      d alpha
      (formula_sub_ptree_fit P' E F (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D))

| contraction_a A d alpha P', _ =>
    contraction_a
      (formula_sub_ind_fit A E F S)
      d alpha
      (formula_sub_ptree_fit P' E F (lor_ind S S))

| contraction_ad A D d alpha P', lor_ind S_A S_D =>
    contraction_ad
      (formula_sub_ind_fit A E F S_A)
      (formula_sub_ind_fit D E F S_D)
      d alpha
      (formula_sub_ptree_fit P' E F (lor_ind (lor_ind S_A S_A) S_D))

| weakening_ad A D d alpha P', lor_ind S_A S_D =>
    weakening_ad
      (formula_sub_ind_fit A E F S_A)
      (formula_sub_ind_fit D E F S_D)
      d alpha
      (formula_sub_ptree_fit P' E F S_D)

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, _ => P

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_AB S_D =>
    demorgan_abd
      A B
      (formula_sub_ind_fit D E F S_D)
      d1 d2 alpha1 alpha2
      (formula_sub_ptree_fit P1 E F (lor_ind (0) S_D))
      (formula_sub_ptree_fit P2 E F (lor_ind (0) S_D))

| negation_a A d alpha P', _ => P

| negation_ad A D d alpha P', lor_ind S_A S_D =>
    negation_ad
      A
      (formula_sub_ind_fit D E F S_D)
      d alpha
      (formula_sub_ptree_fit P' E F (lor_ind (non_target A) S_D))

| quantification_a A n t d alpha P', _ => P

| quantification_ad A D n t d alpha P', lor_ind S_A S_D =>
    quantification_ad
      A
      (formula_sub_ind_fit D E F S_D)
      n t d alpha
      (formula_sub_ptree_fit P' E F (lor_ind (0) S_D))

| w_rule_a A n d alpha g, _ => P

| w_rule_ad A D n d alpha g, lor_ind S_A S_D =>
    w_rule_ad
      A
      (formula_sub_ind_fit D E F S_D)
      n d alpha
      (fun (t : c_term) =>
          formula_sub_ptree_fit (g t) E F (lor_ind (non_target A) S_D))

| cut_ca C0 A d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ca
      (formula_sub_ind_fit C0 E F S)
      A d1 d2 alpha1 alpha2
      (formula_sub_ptree_fit P1 E F (lor_ind S (non_target A)))
      P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ad
      A
      (formula_sub_ind_fit D E F S)
      d1 d2 alpha1 alpha2
      P1
      (formula_sub_ptree_fit P2 E F (lor_ind (0) S))

| cut_cad C0 A D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_D =>
    cut_cad
      (formula_sub_ind_fit C0 E F S_C)
      A
      (formula_sub_ind_fit D E F S_D)
      d1 d2 alpha1 alpha2
      (formula_sub_ptree_fit P1 E F (lor_ind S_C (non_target A)))
      (formula_sub_ptree_fit P2 E F (lor_ind (0) S_D))

| _, _ => P
end.

Fixpoint formula_sub_ptree
  (P : ptree) (E F : formula) (S : subst_ind) : ptree :=
match subst_ind_fit (ptree_formula P) S with
| false => P
| true => formula_sub_ptree_fit P E F S
end.


(* Some preliminary lemmas *)
(* *)
Lemma formula_sub_ptree_formula_aux' :
  forall (P : ptree) (E F : formula) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
    formula_sub_ptree P E F S = P.
Proof. intros. unfold formula_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma formula_sub_ptree_formula_aux :
  forall (P : ptree) (E F : formula) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
      ptree_formula (formula_sub_ptree P E F S) =
      formula_sub_ind (ptree_formula P) E F S.
Proof.
intros. rewrite formula_sub_ptree_formula_aux'.
- unfold formula_sub_ind. rewrite sub_fit_false. auto. apply H.
- apply H.
Qed.

Lemma formula_sub_ptree_formula_true :
  forall (P : ptree) (E F : formula) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    formula_sub_ptree_fit P E F S = formula_sub_ptree P E F S.
Proof. intros. unfold formula_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma formula_sub_ptree_fit_false :
  forall (P : ptree) (E F : formula) (S : subst_ind),
  subst_ind_fit (ptree_formula P) S = false -> 
  formula_sub_ptree P E F S = P.
Proof. intros. unfold formula_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma formula_sub_ind_fit_closed : forall (A B C : formula),
  closed A = true -> (closed B = true -> closed C = true) ->
  forall (S : subst_ind),
    subst_ind_fit A S = true ->
    closed (formula_sub_ind_fit A B C S) = true.
Proof.
intros. destruct (closed (formula_sub_ind A B C S)) eqn:HC.
- rewrite sub_fit_true in HC; auto.
- rewrite formula_sub_ind_closed in HC; auto. inversion HC.
Qed.

Lemma sub_fit_neq_atom :
  forall (a : atomic_formula) (E F : formula) (S : subst_ind),
  eq_f (atom a) E = false ->
  formula_sub_ind_fit (atom a) E F S = atom a.
Proof. intros. unfold formula_sub_ind_fit. destruct S; rewrite H; auto. Qed.

Lemma sub_fit_neq_neg : forall (a : atomic_formula) (E F : formula) (S : subst_ind),
  eq_f (neg (atom a)) E = false ->
  formula_sub_ind_fit (neg (atom a)) E F S = neg (atom a).
Proof. intros. unfold formula_sub_ind_fit. destruct S; rewrite H; auto. Qed.




(*
###############################################################################
Section 10.1: Here we show that for any incorrect atomic formula a,
we can validly replace the formula (atom a) with any formula C in a proof tree.
Consequently, if C \/ (atom a) is provable, so is C \/ C.
###############################################################################
*)

(* First, we must prove that formula_sub_ptree simply changes the base formula
of an ptree the way we expect with formula_sub_ind *)
(* *)
Lemma formula_sub_ptree_formula_atom' :
  forall (P : ptree) (a : atomic_formula) (F : formula),
  valid P ->
  forall (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    ptree_formula (formula_sub_ptree P (atom a) F S) =
    formula_sub_ind (ptree_formula P) (atom a) F S.
Proof.
intros P a F.
induction P; try intros H S Hs.

- simpl in Hs. simpl. rewrite Hs. simpl.
  rewrite (formula_sub_ptree_formula_true _ _ _ _ Hs).
  destruct H as [H1 H2]. apply (IHP H2). auto.

- simpl in Hs. simpl. rewrite Hs. simpl.
  rewrite (formula_sub_ptree_formula_true _ _ _ _ Hs).
  destruct H as [[H1 H2] H3]. apply (IHP H2). auto.

- simpl. inversion H.
  destruct (axiom_atomic _ H1); destruct H0; rewrite H0;
  unfold formula_sub_ind; simpl; destruct S; auto.

- simpl. destruct S; auto. inversion Hs. rewrite H1. simpl. auto.

- simpl. destruct S; auto. destruct S1; auto.
  inversion Hs. rewrite H1. simpl. auto.

- simpl. destruct S; auto. destruct S1; auto.
  inversion Hs. rewrite H1. simpl. auto.

- simpl. destruct S; auto. destruct S1; auto. destruct S1_1; auto.
  inversion Hs. rewrite H1. simpl. auto.

- simpl. destruct (subst_ind_fit f S) eqn:HS.
  + simpl. rewrite sub_fit_true; auto.
  + simpl. rewrite sub_fit_false; auto.

- simpl. destruct S; auto. inversion Hs. rewrite H1. simpl. auto.

- simpl. destruct S; auto. inversion Hs. rewrite H1. simpl. auto.

- simpl. destruct S; auto.

- simpl. destruct S; auto.
  destruct S1; auto; inversion Hs; rewrite H1; simpl; auto.

- simpl. destruct S; auto.

- simpl. destruct S; auto.
  destruct S1; auto; inversion Hs; rewrite H1; simpl; auto.

- simpl. destruct S; auto.

- simpl. destruct S; auto.
  destruct S1; auto; inversion Hs; rewrite H1; simpl; auto.

- simpl. destruct S; auto.

- intros Hv S Hs. simpl. destruct S; auto.
  destruct S1; auto; inversion Hs; rewrite H1; simpl; auto.

- simpl. destruct (subst_ind_fit f S) eqn:HS.
  + simpl. rewrite sub_fit_true; auto.
  + simpl. rewrite sub_fit_false; auto.

- simpl. destruct (subst_ind_fit f0 S) eqn:HS.
  + simpl. rewrite sub_fit_true; auto.
  + simpl. rewrite sub_fit_false; auto.

- simpl. destruct S; auto. inversion Hs. rewrite H1. simpl. auto.
Qed.

Lemma formula_sub_ptree_formula_atom :
  forall (P : ptree) (a : atomic_formula) (F : formula),
  valid P ->
  forall (S : subst_ind),
    ptree_formula (formula_sub_ptree P (atom a) F S) =
    formula_sub_ind (ptree_formula P) (atom a) F S.
Proof.
intros. destruct (subst_ind_fit (ptree_formula P) S) eqn:Hs.
- apply formula_sub_ptree_formula_atom'; auto.
- apply formula_sub_ptree_formula_aux. apply Hs.
Qed.

Lemma formula_sub_ptree_formula_atom_fit :
  forall (P : ptree) (a : atomic_formula) (F : formula),
  valid P ->
  forall (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    ptree_formula (formula_sub_ptree P (atom a) F S) =
    formula_sub_ind_fit (ptree_formula P) (atom a) F S.
Proof.
intros. rewrite formula_sub_ptree_formula_atom'; auto.
rewrite sub_fit_true; auto.
Qed.


(* Second, we must prove that formula_sub_ptree does not change the degree
of an ptree. *)
(* *)
Lemma formula_sub_ptree_deg_atom :
  forall (P : ptree) (a : atomic_formula) (F : formula),
  valid P ->
  forall (S : subst_ind),
    ptree_deg (formula_sub_ptree P (atom a) F S) = ptree_deg P.
Proof.
intros P a F H. induction P; intros S.
- simpl. case (subst_ind_fit (ptree_formula P) S); auto.
- simpl. case (subst_ind_fit (ptree_formula P) S) eqn:Hfit; auto. simpl.
  rewrite (formula_sub_ptree_formula_true _ _ _ _ Hfit).
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
  destruct S1; destruct (subst_ind_fit f0 S2) eqn:HS2; auto.
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


(* Third, we must prove that formula_sub_ptree does not change the ordinal
of an ptree. *)
(* *)
Lemma formula_sub_ptree_ord_atom :
  forall (P : ptree) (a : atomic_formula) (F : formula),
  valid P ->
  forall (S : subst_ind),
    ptree_ord (formula_sub_ptree P (atom a) F S) = ptree_ord P.
Proof.
intros P a F H. induction P; intros S.
- simpl. case (subst_ind_fit (ptree_formula P) S) eqn:Hfit; auto. simpl.
  rewrite (formula_sub_ptree_formula_true _ _ _ _ Hfit).
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
- simpl. destruct S; auto.
- simpl. destruct S; auto.
  destruct S1; destruct (subst_ind_fit f0 S2) eqn:HS2; auto.
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
formula substitution on it results in a valid ptree *)
(* *)
Lemma formula_sub_valid_atom :
  forall (P : ptree) (a : atomic_formula) (F : formula),
    valid P ->
    PA_omega_axiom (atom a) = false ->
    closed F =true ->
    forall (S : subst_ind),
      subst_ind_fit (ptree_formula P) S = true ->
      valid (formula_sub_ptree P (atom a) F S).
Proof.
intros P a F.
induction P; try intros H Ha HF S Hs.

- simpl. inversion H as [H1 H2]. inversion Hs. rewrite H3.
  rewrite formula_sub_ptree_formula_true; auto. split.
  + rewrite formula_sub_ptree_deg_atom; auto.
  + apply (IHP H2 Ha HF S H3).

- simpl. inversion H as [[H1 H2] H3]. inversion Hs. rewrite H4.
  rewrite formula_sub_ptree_formula_true; auto. split.
  + rewrite formula_sub_ptree_ord_atom; auto.
  + auto.

- simpl. inversion Hs. rewrite H1. simpl. destruct (eq_f f (atom a)) eqn:Hf.
  + inversion H. apply f_eq_decid in Hf.
    rewrite Hf in H2. rewrite H2 in Ha. inversion Ha.
  + inversion H. destruct (axiom_atomic _ H2) as [[a' Ha'] | [a' Ha']].
    * rewrite Ha'. rewrite Ha' in Hf. rewrite sub_fit_neq_atom; auto.
    * rewrite Ha'. rewrite Ha' in Hf. rewrite sub_fit_neq_neg; auto.

- simpl. destruct S; inversion Hs. rewrite H1. simpl.
  inversion H as [[[H2 H3] H4] H5].
  repeat split; rewrite formula_sub_ptree_formula_true.
  + rewrite formula_sub_ptree_formula_atom_fit; auto; rewrite H2; simpl; auto.
    apply and_bool_symm. auto.
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + apply IHP; auto. rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + rewrite formula_sub_ptree_deg_atom; auto.
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + rewrite formula_sub_ptree_ord_atom; auto.
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).

- simpl. destruct S; try destruct S1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H4 H5] H6] H7].
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  repeat split; rewrite formula_sub_ptree_formula_true.
  + rewrite formula_sub_ptree_formula_atom_fit; auto; rewrite H4; simpl; auto.
    rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + apply IHP; auto. rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite formula_sub_ptree_deg_atom; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite formula_sub_ptree_ord_atom; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.

- simpl. destruct S; try destruct S1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H4 H5] H6] H7].
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  repeat split; rewrite formula_sub_ptree_formula_true.
  + rewrite formula_sub_ptree_formula_atom_fit; auto; rewrite H4; simpl; auto.
    rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + apply IHP; auto. rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite formula_sub_ptree_deg_atom; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite formula_sub_ptree_ord_atom; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.

- simpl. destruct S; try destruct S1; try destruct S1_1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H5 H6] H7] H8].
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  destruct (and_bool_prop _ _ H1). clear H1.
  repeat split; rewrite formula_sub_ptree_formula_true.
  + rewrite formula_sub_ptree_formula_atom_fit; auto; rewrite H5; simpl; auto.
    rewrite H0, H2, H3, H4. auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + apply IHP; auto. rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite formula_sub_ptree_deg_atom; auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite formula_sub_ptree_ord_atom; auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.

- simpl. inversion Hs. rewrite H1. inversion H as [[[H2 H3] H4] H5].
  repeat split; rewrite formula_sub_ptree_formula_true.
  + rewrite formula_sub_ptree_formula_atom_fit; auto; rewrite H2; simpl; auto.
    rewrite H1. auto.
  + rewrite H2. simpl. rewrite H1. auto.
  + apply IHP; auto. rewrite H2. simpl. rewrite H1. auto.
  + rewrite H2. simpl. rewrite H1. auto.
  + rewrite formula_sub_ptree_deg_atom; auto.
  + rewrite H2. simpl. rewrite H1. auto.
  + rewrite formula_sub_ptree_ord_atom; auto.
  + rewrite H2. simpl. rewrite H1. auto.

- simpl. destruct S; inversion Hs. rewrite H1.
  inversion H as [[[H2 H3] H4] H5]. destruct (and_bool_prop _ _ H1).
  repeat split; rewrite formula_sub_ptree_formula_true.
  + rewrite formula_sub_ptree_formula_atom_fit; auto. rewrite H2. simpl. auto.
    rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + apply IHP; auto. rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite formula_sub_ptree_deg_atom; auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite formula_sub_ptree_ord_atom; auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.

- simpl. destruct S; inversion Hs. rewrite H1. simpl.
  inversion H as [[[[H2 H3] H4] H5] H6]. destruct (and_bool_prop _ _ H1).
  repeat split.
  + rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_formula_atom_fit; auto; rewrite H2; auto.
    * rewrite H2. auto.
  + apply formula_sub_ind_fit_closed; auto.
  + rewrite formula_sub_ptree_formula_true.
    * apply IHP; auto. rewrite H2. auto.
    * rewrite H2. auto.
  + rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_deg_atom; auto.
    * rewrite H2. auto.
  + rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_ord_atom; auto.
    * rewrite H2. auto.

- simpl. destruct S; apply H.

- simpl. destruct S; try apply H.
  destruct S1; inversion Hs; rewrite H1; simpl.
  + destruct H as [[[[[[[H2 H3] H4] H5] H6] H7] H8] H9].
    repeat split; rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_formula_atom_fit; auto; rewrite H2; simpl; auto.
    * rewrite H2. simpl. apply H1.
    * apply IHP1; auto. rewrite H2. apply H1.
    * rewrite H2. simpl. apply H1.
    * rewrite formula_sub_ptree_formula_atom_fit; auto; rewrite H4; simpl; auto.
    * rewrite H4. simpl. apply H1.
    * apply IHP2; auto. rewrite H4. simpl. apply H1.
    * rewrite H4. simpl. apply H1.
    * rewrite formula_sub_ptree_deg_atom; auto.
    * rewrite H2. simpl. apply H1.
    * rewrite formula_sub_ptree_deg_atom; auto.
    * rewrite H4. simpl. apply H1.
    * rewrite formula_sub_ptree_ord_atom; auto.
    * rewrite H2. simpl. apply H1.
    * rewrite formula_sub_ptree_ord_atom; auto.
    * rewrite H4. simpl. apply H1.
  + destruct H as [[[[[[[H2 H3] H4] H5] H6] H7] H8] H9].
    repeat split; rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_formula_atom_fit; auto; rewrite H2; simpl; auto.
    * rewrite H2. simpl. apply H1.
    * apply IHP1; auto. rewrite H2. apply H1.
    * rewrite H2. simpl. apply H1.
    * rewrite formula_sub_ptree_formula_atom_fit; auto; rewrite H4; simpl; auto.
    * rewrite H4. simpl. apply H1.
    * apply IHP2; auto. rewrite H4. simpl. apply H1.
    * rewrite H4. simpl. apply H1.
    * rewrite formula_sub_ptree_deg_atom; auto.
    * rewrite H2. simpl. apply H1.
    * rewrite formula_sub_ptree_deg_atom; auto.
    * rewrite H4. simpl. apply H1.
    * rewrite formula_sub_ptree_ord_atom; auto.
    * rewrite H2. simpl. apply H1.
    * rewrite formula_sub_ptree_ord_atom; auto.
    * rewrite H4. simpl. apply H1.

- simpl. destruct S; auto.

- simpl. inversion H as [[[H2 H3] H4] H5]. destruct S; auto.
  destruct S1; auto.
  + inversion Hs. rewrite H1. simpl.
    repeat split; rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_formula_atom_fit; auto; rewrite H2; simpl.
      { rewrite non_target_sub'. auto. }
      { rewrite non_target_fit, H1. auto. }
    * rewrite H2. simpl. rewrite non_target_fit, H1. auto.
    * apply IHP; auto. rewrite H2. simpl. rewrite non_target_fit, H1. auto.
    * rewrite H2. simpl. rewrite non_target_fit, H1. auto.
    * rewrite formula_sub_ptree_deg_atom; auto.
    * rewrite H2. simpl. rewrite non_target_fit, H1. auto.
    * rewrite formula_sub_ptree_ord_atom; auto.
    * rewrite H2. simpl. rewrite non_target_fit, H1. auto.
  + inversion Hs. rewrite H1. simpl.
    repeat split; rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_formula_atom_fit; auto; rewrite H2; simpl.
      { rewrite non_target_sub'. auto. }
      { rewrite non_target_fit, H1. auto. }
    * rewrite H2. simpl. rewrite non_target_fit, H1. auto.
    * apply IHP; auto. rewrite H2. simpl. rewrite non_target_fit, H1. auto.
    * rewrite H2. simpl. rewrite non_target_fit, H1. auto.
    * rewrite formula_sub_ptree_deg_atom; auto.
    * rewrite H2. simpl. rewrite non_target_fit, H1. auto.
    * rewrite formula_sub_ptree_ord_atom; auto.
    * rewrite H2. simpl. rewrite non_target_fit, H1. auto.

- simpl. destruct S; auto.

- simpl. destruct S; auto. inversion H as [[[H0 H1] H2] H3].
  destruct S1; inversion Hs; rewrite H5; simpl.
  + repeat split; auto; rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_formula_atom_fit;
      auto; rewrite H0; simpl; auto.
    * rewrite H0. simpl. apply H5.
    * apply IHP; auto. rewrite H0. simpl. apply H5.
    * rewrite H0. simpl. apply H5.
    * rewrite formula_sub_ptree_deg_atom; auto.
    * rewrite H0. simpl. auto.
    * rewrite formula_sub_ptree_ord_atom; auto.
    * rewrite H0. simpl. auto.
  + repeat split; auto; rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_formula_atom_fit;
      auto; rewrite H0; simpl; auto.
    * rewrite H0. simpl. apply H5.
    * apply IHP; auto. rewrite H0. simpl. apply H5.
    * rewrite H0. simpl. apply H5.
    * rewrite formula_sub_ptree_deg_atom; auto.
    * rewrite H0. simpl. auto.
    * rewrite formula_sub_ptree_ord_atom; auto.
    * rewrite H0. simpl. auto.

- intros. simpl. destruct S; auto.

- rename H into H0. rename X into H. rename Hs into H1.
  simpl. destruct S; auto. destruct S1; inversion H1.
  + rewrite H3. simpl. intros. destruct (valid_w_rule_ad _ _ _ _ _ _ H0 t) as [[[H4 H5] H6] H7].
    repeat split; rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_formula_atom_fit; auto; rewrite H4; simpl;
      rewrite (non_target_term_sub f n (projT1 t)).
      { rewrite non_target_sub'. auto. }
      { rewrite non_target_fit. auto. }
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
      rewrite non_target_fit. apply H3.
    * apply H; auto. rewrite H4. simpl.
      rewrite (non_target_term_sub f n (projT1 t)).
      rewrite non_target_fit. apply H3.
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
      rewrite non_target_fit. apply H3.
    * rewrite formula_sub_ptree_deg_atom; auto.
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
        rewrite non_target_fit. rewrite H3. auto.
    * rewrite formula_sub_ptree_ord_atom; auto.
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
      rewrite non_target_fit. rewrite H3. auto.
  + rewrite H3. simpl. intros. destruct (valid_w_rule_ad _ _ _ _ _ _ H0 t) as [[[H4 H5] H6] H7].
    repeat split; rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_formula_atom_fit; auto; rewrite H4; simpl;
      rewrite (non_target_term_sub f n (projT1 t)).
      { rewrite non_target_sub'. auto. }
      { rewrite non_target_fit. auto. }
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
      rewrite non_target_fit. apply H3.
    * apply H; auto. rewrite H4. simpl.
      rewrite (non_target_term_sub f n (projT1 t)).
      rewrite non_target_fit. apply H3.
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
      rewrite non_target_fit. apply H3.
    * rewrite formula_sub_ptree_deg_atom; auto.
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
        rewrite non_target_fit. rewrite H3. auto.
    * rewrite formula_sub_ptree_ord_atom; auto.
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
      rewrite non_target_fit. rewrite H3. auto.
- clear IHP2. simpl. destruct (subst_ind_fit f S) eqn:Heq; auto. simpl.
  inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  repeat split; auto; rewrite formula_sub_ptree_formula_true.
  + rewrite formula_sub_ptree_formula_atom_fit; auto; rewrite H1; simpl.
    { rewrite non_target_sub'. auto. }
    { rewrite non_target_fit, Heq. auto. }
  + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + apply IHP1; auto. rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + rewrite formula_sub_ptree_deg_atom; auto.
  + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + rewrite formula_sub_ptree_ord_atom; auto.
  + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.

- clear IHP1. simpl. destruct (subst_ind_fit f0 S) eqn:Heq; auto. simpl.
  inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  repeat split; auto; rewrite formula_sub_ptree_formula_true.
  + rewrite formula_sub_ptree_formula_atom_fit; auto; rewrite H3; simpl; auto.
  + rewrite H3. simpl. auto.
  + apply IHP2; auto. rewrite H3. simpl. auto.
  + rewrite H3. simpl. auto.
  + rewrite formula_sub_ptree_deg_atom; auto.
  + rewrite H3. simpl. auto.
  + rewrite formula_sub_ptree_ord_atom; auto.
  + rewrite H3. simpl. auto.

- simpl. inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  destruct S; try inversion Hs. rewrite H9.
  destruct (and_bool_prop _ _ H9) as [H10 H11].
  simpl. repeat split; rewrite formula_sub_ptree_formula_true.
  + rewrite formula_sub_ptree_formula_atom_fit; auto; rewrite H1; simpl.
    { rewrite non_target_sub'. auto. }
    { rewrite non_target_fit, H10. auto. }
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + apply IHP1; auto. rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite formula_sub_ptree_formula_atom_fit; auto; rewrite H3; simpl; auto.
  + rewrite H3. simpl. auto.
  + apply IHP2; auto. rewrite H3. simpl. auto.
  + rewrite H3. simpl. auto.
  + rewrite formula_sub_ptree_deg_atom; auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite formula_sub_ptree_deg_atom; auto.
  + rewrite H3. simpl. auto.
  + rewrite formula_sub_ptree_ord_atom; auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite formula_sub_ptree_ord_atom; auto.
  + rewrite H3. simpl. auto.
Qed.


(* We finally show that if the C \/ (atom a) is provable
where 'a' is incorrect, then C \/ C is provable. *)
(* *)
Lemma atom_sub_valid :
  forall (C : formula) (a : atomic_formula) (d : nat) (alpha : ord),
  PA_omega_axiom (atom a) = false ->
  provable (lor C (atom a)) d alpha ->
  provable (lor C C) d alpha.
Proof.
unfold provable. intros C a d alpha Ha H. destruct H as [P [[[HP1 HP2] HP3] HP4]].
exists (formula_sub_ptree P (atom a) C (lor_ind (non_target C) (1))).
unfold P_proves. repeat split.
- rewrite formula_sub_ptree_formula_atom; auto. rewrite HP1.
  unfold formula_sub_ind. simpl. rewrite non_target_fit. simpl.
  rewrite eq_atom_refl. rewrite non_target_sub'. auto.
- apply formula_sub_valid_atom; auto.
  + pose proof (provable_closed' P (lor C (atom a)) HP2 HP1).
    simpl in H. destruct (and_bool_prop _ _ H). auto.
  + rewrite HP1. simpl. rewrite non_target_fit. auto.
- rewrite formula_sub_ptree_deg_atom; auto.
- rewrite formula_sub_ptree_ord_atom; auto.
Qed.










(*
###############################################################################
Section 10.2: Here we show that for any correct atomic formula a, we can
validly replace the formula (neg (atom a)) with any formula C in a proof tree.
Consequently, if C \/ (neg (atom a)) is provable, so is C \/ C.
###############################################################################
*)

(* First, we must prove that formula_sub_ptree simply changes the base formula
of an ptree the way we expect with formula_sub_ind *)
(* *)
Lemma formula_sub_ptree_formula_neg' :
  forall (P : ptree) (a : atomic_formula) (F : formula),
  valid P ->
  forall (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    ptree_formula (formula_sub_ptree P (neg (atom a)) F S) =
    formula_sub_ind (ptree_formula P) (neg (atom a)) F S.
Proof.
intros P a F.
induction P; try intros H S Hs.

- simpl in Hs. simpl. rewrite Hs. simpl.
  rewrite (formula_sub_ptree_formula_true _ _ _ _ Hs).
  destruct H as [H1 H2]. apply (IHP H2). auto.

- simpl in Hs. simpl. rewrite Hs. simpl.
  rewrite (formula_sub_ptree_formula_true _ _ _ _ Hs).
  destruct H as [[H1 H2] H3]. apply (IHP H2). auto.

- simpl. inversion H.
  destruct (axiom_atomic _ H1); destruct H0; rewrite H0;
  unfold formula_sub_ind; simpl; destruct S; auto.

- simpl. destruct S; auto. inversion Hs. rewrite H1. simpl. auto.

- simpl. destruct S; auto. destruct S1; auto.
  inversion Hs. rewrite H1. simpl. auto.

- simpl. destruct S; auto. destruct S1; auto.
  inversion Hs. rewrite H1. simpl. auto.

- simpl. destruct S; auto. destruct S1; auto. destruct S1_1; auto.
  inversion Hs. rewrite H1. simpl. auto.

- simpl. destruct (subst_ind_fit f S) eqn:HS.
  + simpl. rewrite sub_fit_true; auto.
  + simpl. rewrite sub_fit_false; auto.

- simpl. destruct S; auto. inversion Hs. rewrite H1. simpl. auto.

- simpl. destruct S; auto. inversion Hs. rewrite H1. simpl. auto.

- simpl. destruct S; auto.

- simpl. destruct S; auto.
  destruct S1; auto; inversion Hs; rewrite H1; simpl; auto.

- simpl. destruct S; auto.

- simpl. destruct S; auto.
  destruct S1; auto; inversion Hs; rewrite H1; simpl; auto.

- simpl. destruct S; auto.

- simpl. destruct S; auto.
  destruct S1; auto; inversion Hs; rewrite H1; simpl; auto.

- simpl. destruct S; auto.

- intros Hv S Hs. simpl. destruct S; auto.
  destruct S1; auto; inversion Hs; rewrite H1; simpl; auto.

- simpl. destruct (subst_ind_fit f S) eqn:HS.
  + simpl. rewrite sub_fit_true; auto.
  + simpl. rewrite sub_fit_false; auto.

- simpl. destruct (subst_ind_fit f0 S) eqn:HS.
  + simpl. rewrite sub_fit_true; auto.
  + simpl. rewrite sub_fit_false; auto.

- simpl. destruct S; auto. inversion Hs. rewrite H1. simpl. auto.
Qed.

Lemma formula_sub_ptree_formula_neg :
  forall (P : ptree) (a : atomic_formula) (F : formula),
  valid P ->
  forall (S : subst_ind),
    ptree_formula (formula_sub_ptree P (neg (atom a)) F S) =
    formula_sub_ind (ptree_formula P) (neg (atom a)) F S.
Proof.
intros. destruct (subst_ind_fit (ptree_formula P) S) eqn:Hs.
- apply formula_sub_ptree_formula_neg'; auto.
- apply formula_sub_ptree_formula_aux. apply Hs.
Qed.

Lemma formula_sub_ptree_formula_neg_fit :
  forall (P : ptree) (a : atomic_formula) (F : formula),
  valid P ->
  forall (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    ptree_formula (formula_sub_ptree P (neg (atom a)) F S) =
    formula_sub_ind_fit (ptree_formula P) (neg (atom a)) F S.
Proof.
intros. rewrite formula_sub_ptree_formula_neg'; auto.
rewrite sub_fit_true; auto.
Qed.


(* Second, we must prove that formula_sub_ptree does not change the degree
of an ptree. *)
(* *)
Lemma formula_sub_ptree_deg_neg :
  forall (P : ptree) (a : atomic_formula) (F : formula),
  valid P ->
  forall (S : subst_ind),
    ptree_deg (formula_sub_ptree P (neg (atom a)) F S) = ptree_deg P.
Proof.
intros P a F H. induction P; intros S.
- simpl. case (subst_ind_fit (ptree_formula P) S); auto.
- simpl. case (subst_ind_fit (ptree_formula P) S) eqn:Hfit; auto. simpl.
  rewrite (formula_sub_ptree_formula_true _ _ _ _ Hfit).
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
  destruct S1; destruct (subst_ind_fit f0 S2) eqn:HS2; auto.
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


(* Third, we must prove that formula_sub_ptree does not change the ordinal
of an ptree. *)
(* *)
Lemma formula_sub_ptree_ord_neg :
  forall (P : ptree) (a : atomic_formula) (F : formula),
  valid P ->
  forall (S : subst_ind),
    ptree_ord (formula_sub_ptree P (neg (atom a)) F S) = ptree_ord P.
Proof.
intros P a F H. induction P; intros S.
- simpl. case (subst_ind_fit (ptree_formula P) S) eqn:Hfit; auto. simpl.
  rewrite (formula_sub_ptree_formula_true _ _ _ _ Hfit).
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
- simpl. destruct S; auto.
- simpl. destruct S; auto.
  destruct S1; destruct (subst_ind_fit f0 S2) eqn:HS2; auto.
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
formula substitution on it results in a valid ptree *)
(* *)
Lemma formula_sub_valid_neg :
  forall (P : ptree) (a : atomic_formula) (F : formula),
    valid P ->
    PA_omega_axiom (neg (atom a)) = false ->
    closed F =true ->
    forall (S : subst_ind),
      subst_ind_fit (ptree_formula P) S = true ->
      valid (formula_sub_ptree P (neg (atom a)) F S).
Proof.
intros P a F.
induction P; try intros H Ha HF S Hs.

- simpl. inversion H as [H1 H2]. inversion Hs. rewrite H3.
  rewrite formula_sub_ptree_formula_true; auto. split.
  + rewrite formula_sub_ptree_deg_neg; auto.
  + apply (IHP H2 Ha HF S H3).

- simpl. inversion H as [[H1 H2] H3]. inversion Hs. rewrite H4.
  rewrite formula_sub_ptree_formula_true; auto. split.
  + rewrite formula_sub_ptree_ord_neg; auto.
  + auto.

- simpl. inversion Hs. rewrite H1. simpl.
  destruct (eq_f f (neg (atom a))) eqn:Hf.
  + inversion H. apply f_eq_decid in Hf.
    rewrite Hf in H2. rewrite H2 in Ha. inversion Ha.
  + inversion H. destruct (axiom_atomic _ H2) as [[a' Ha'] | [a' Ha']].
    * rewrite Ha'. simpl. auto.
    * rewrite H2. rewrite Ha'. rewrite Ha' in Hf. inversion Hf.
      simpl. rewrite H3. rewrite Ha' in H2. auto.

- simpl. destruct S; inversion Hs. rewrite H1. simpl.
  inversion H as [[[H2 H3] H4] H5].
  repeat split; rewrite formula_sub_ptree_formula_true.
  + rewrite formula_sub_ptree_formula_neg_fit; auto; rewrite H2; simpl; auto.
    apply and_bool_symm. auto.
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + apply IHP; auto. rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + rewrite formula_sub_ptree_deg_neg; auto.
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + rewrite formula_sub_ptree_ord_neg; auto.
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).

- simpl. destruct S; try destruct S1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H4 H5] H6] H7].
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  repeat split; rewrite formula_sub_ptree_formula_true.
  + rewrite formula_sub_ptree_formula_neg_fit; auto; rewrite H4; simpl; auto.
    rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + apply IHP; auto. rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite formula_sub_ptree_deg_neg; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite formula_sub_ptree_ord_neg; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.

- simpl. destruct S; try destruct S1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H4 H5] H6] H7].
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  repeat split; rewrite formula_sub_ptree_formula_true.
  + rewrite formula_sub_ptree_formula_neg_fit; auto; rewrite H4; simpl; auto.
    rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + apply IHP; auto. rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite formula_sub_ptree_deg_neg; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite formula_sub_ptree_ord_neg; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.

- simpl. destruct S; try destruct S1; try destruct S1_1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H5 H6] H7] H8].
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  destruct (and_bool_prop _ _ H1). clear H1.
  repeat split; rewrite formula_sub_ptree_formula_true.
  + rewrite formula_sub_ptree_formula_neg_fit; auto; rewrite H5; simpl; auto.
    rewrite H0, H2, H3, H4. auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + apply IHP; auto. rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite formula_sub_ptree_deg_neg; auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite formula_sub_ptree_ord_neg; auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.

- simpl. inversion Hs. rewrite H1. inversion H as [[[H2 H3] H4] H5].
  repeat split; rewrite formula_sub_ptree_formula_true.
  + rewrite formula_sub_ptree_formula_neg_fit; auto; rewrite H2; simpl; auto.
    rewrite H1. auto.
  + rewrite H2. simpl. rewrite H1. auto.
  + apply IHP; auto. rewrite H2. simpl. rewrite H1. auto.
  + rewrite H2. simpl. rewrite H1. auto.
  + rewrite formula_sub_ptree_deg_neg; auto.
  + rewrite H2. simpl. rewrite H1. auto.
  + rewrite formula_sub_ptree_ord_neg; auto.
  + rewrite H2. simpl. rewrite H1. auto.

- simpl. destruct S; inversion Hs. rewrite H1.
  inversion H as [[[H2 H3] H4] H5]. destruct (and_bool_prop _ _ H1).
  repeat split; rewrite formula_sub_ptree_formula_true.
  + rewrite formula_sub_ptree_formula_neg_fit; auto. rewrite H2. simpl. auto.
    rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + apply IHP; auto. rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite formula_sub_ptree_deg_neg; auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite formula_sub_ptree_ord_neg; auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.

- simpl. destruct S; inversion Hs. rewrite H1. simpl.
  inversion H as [[[[H2 H3] H4] H5] H6]. destruct (and_bool_prop _ _ H1).
  repeat split.
  + rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_formula_neg_fit; auto; rewrite H2; auto.
    * rewrite H2. auto.
  + apply formula_sub_ind_fit_closed; auto.
  + rewrite formula_sub_ptree_formula_true.
    * apply IHP; auto. rewrite H2. auto.
    * rewrite H2. auto.
  + rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_deg_neg; auto.
    * rewrite H2. auto.
  + rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_ord_neg; auto.
    * rewrite H2. auto.

- simpl. destruct S; apply H.

- simpl. destruct S; try apply H.
  destruct S1; inversion Hs; rewrite H1; simpl.
  + destruct H as [[[[[[[H2 H3] H4] H5] H6] H7] H8] H9].
    repeat split; rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_formula_neg_fit; auto; rewrite H2; simpl; auto.
      case (eq_f f (atom a)); auto.
    * rewrite H2. simpl. apply H1.
    * apply IHP1; auto. rewrite H2. apply H1.
    * rewrite H2. simpl. apply H1.
    * rewrite formula_sub_ptree_formula_neg_fit; auto; rewrite H4; simpl; auto.
      case (eq_f f0 (atom a)); auto.
    * rewrite H4. simpl. apply H1.
    * apply IHP2; auto. rewrite H4. simpl. apply H1.
    * rewrite H4. simpl. apply H1.
    * rewrite formula_sub_ptree_deg_neg; auto.
    * rewrite H2. simpl. apply H1.
    * rewrite formula_sub_ptree_deg_neg; auto.
    * rewrite H4. simpl. apply H1.
    * rewrite formula_sub_ptree_ord_neg; auto.
    * rewrite H2. simpl. apply H1.
    * rewrite formula_sub_ptree_ord_neg; auto.
    * rewrite H4. simpl. apply H1.
  + destruct H as [[[[[[[H2 H3] H4] H5] H6] H7] H8] H9].
    repeat split; rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_formula_neg_fit; auto; rewrite H2; simpl; auto.
      case (eq_f f (atom a)); auto.
    * rewrite H2. simpl. apply H1.
    * apply IHP1; auto. rewrite H2. apply H1.
    * rewrite H2. simpl. apply H1.
    * rewrite formula_sub_ptree_formula_neg_fit; auto; rewrite H4; simpl; auto.
      case (eq_f f0 (atom a)); auto.
    * rewrite H4. simpl. apply H1.
    * apply IHP2; auto. rewrite H4. simpl. apply H1.
    * rewrite H4. simpl. apply H1.
    * rewrite formula_sub_ptree_deg_neg; auto.
    * rewrite H2. simpl. apply H1.
    * rewrite formula_sub_ptree_deg_neg; auto.
    * rewrite H4. simpl. apply H1.
    * rewrite formula_sub_ptree_ord_neg; auto.
    * rewrite H2. simpl. apply H1.
    * rewrite formula_sub_ptree_ord_neg; auto.
    * rewrite H4. simpl. apply H1.

- simpl. destruct S; auto.

- simpl. inversion H as [[[H2 H3] H4] H5]. destruct S; auto.
  destruct S1; auto.
  + inversion Hs. rewrite H1. simpl.
    repeat split; rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_formula_neg_fit; auto; rewrite H2; simpl.
      { rewrite non_target_sub'. auto. }
      { rewrite non_target_fit, H1. auto. }
    * rewrite H2. simpl. rewrite non_target_fit, H1. auto.
    * apply IHP; auto. rewrite H2. simpl. rewrite non_target_fit, H1. auto.
    * rewrite H2. simpl. rewrite non_target_fit, H1. auto.
    * rewrite formula_sub_ptree_deg_neg; auto.
    * rewrite H2. simpl. rewrite non_target_fit, H1. auto.
    * rewrite formula_sub_ptree_ord_neg; auto.
    * rewrite H2. simpl. rewrite non_target_fit, H1. auto.
  + inversion Hs. rewrite H1. simpl.
    repeat split; rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_formula_neg_fit; auto; rewrite H2; simpl.
      { rewrite non_target_sub'. auto. }
      { rewrite non_target_fit, H1. auto. }
    * rewrite H2. simpl. rewrite non_target_fit, H1. auto.
    * apply IHP; auto. rewrite H2. simpl. rewrite non_target_fit, H1. auto.
    * rewrite H2. simpl. rewrite non_target_fit, H1. auto.
    * rewrite formula_sub_ptree_deg_neg; auto.
    * rewrite H2. simpl. rewrite non_target_fit, H1. auto.
    * rewrite formula_sub_ptree_ord_neg; auto.
    * rewrite H2. simpl. rewrite non_target_fit, H1. auto.

- simpl. destruct S; auto.

- simpl. destruct S; auto. inversion H as [[[H0 H1] H2] H3].
  destruct S1; inversion Hs; rewrite H5; simpl.
  + repeat split; auto; rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_formula_neg_fit; auto; rewrite H0; simpl; auto.
      case (eq_f (substitution f n (projT1 c)) (atom a)); auto.
    * rewrite H0. simpl. apply H5.
    * apply IHP; auto. rewrite H0. simpl. apply H5.
    * rewrite H0. simpl. apply H5.
    * rewrite formula_sub_ptree_deg_neg; auto.
    * rewrite H0. simpl. auto.
    * rewrite formula_sub_ptree_ord_neg; auto.
    * rewrite H0. simpl. auto.
  + repeat split; auto; rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_formula_neg_fit; auto; rewrite H0; simpl; auto.
      case (eq_f (substitution f n (projT1 c)) (atom a)); auto.
    * rewrite H0. simpl. apply H5.
    * apply IHP; auto. rewrite H0. simpl. apply H5.
    * rewrite H0. simpl. apply H5.
    * rewrite formula_sub_ptree_deg_neg; auto.
    * rewrite H0. simpl. auto.
    * rewrite formula_sub_ptree_ord_neg; auto.
    * rewrite H0. simpl. auto.

- intros. simpl. destruct S; auto.

- rename H into H0. rename X into H. rename Hs into H1.
  simpl. destruct S; auto. destruct S1; inversion H1.
  + rewrite H3. simpl. intros. destruct (valid_w_rule_ad _ _ _ _ _ _ H0 t) as [[[H4 H5] H6] H7].
    repeat split; rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_formula_neg_fit; auto; rewrite H4; simpl;
      rewrite (non_target_term_sub f n (projT1 t)).
      { rewrite non_target_sub'. auto. }
      { rewrite non_target_fit. auto. }
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
      rewrite non_target_fit. apply H3.
    * apply H; auto. rewrite H4. simpl.
      rewrite (non_target_term_sub f n (projT1 t)).
      rewrite non_target_fit. apply H3.
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
      rewrite non_target_fit. apply H3.
    * rewrite formula_sub_ptree_deg_neg; auto.
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
        rewrite non_target_fit. rewrite H3. auto.
    * rewrite formula_sub_ptree_ord_neg; auto.
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
      rewrite non_target_fit. rewrite H3. auto.
  + rewrite H3. simpl. intros. destruct (valid_w_rule_ad _ _ _ _ _ _ H0 t) as [[[H4 H5] H6] H7].
    repeat split; rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_formula_neg_fit; auto; rewrite H4; simpl;
      rewrite (non_target_term_sub f n (projT1 t)).
      { rewrite non_target_sub'. auto. }
      { rewrite non_target_fit. auto. }
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
      rewrite non_target_fit. apply H3.
    * apply H; auto. rewrite H4. simpl.
      rewrite (non_target_term_sub f n (projT1 t)).
      rewrite non_target_fit. apply H3.
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
      rewrite non_target_fit. apply H3.
    * rewrite formula_sub_ptree_deg_neg; auto.
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
        rewrite non_target_fit. rewrite H3. auto.
    * rewrite formula_sub_ptree_ord_neg; auto.
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
      rewrite non_target_fit. rewrite H3. auto.
- clear IHP2. simpl. destruct (subst_ind_fit f S) eqn:Heq; auto. simpl.
  inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  repeat split; auto; rewrite formula_sub_ptree_formula_true.
  + rewrite formula_sub_ptree_formula_neg_fit; auto; rewrite H1; simpl.
    { rewrite non_target_sub'. auto. }
    { rewrite non_target_fit, Heq. auto. }
  + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + apply IHP1; auto. rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + rewrite formula_sub_ptree_deg_neg; auto.
  + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + rewrite formula_sub_ptree_ord_neg; auto.
  + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.

- clear IHP1. simpl. destruct (subst_ind_fit f0 S) eqn:Heq; auto. simpl.
  inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  repeat split; auto; rewrite formula_sub_ptree_formula_true.
  + rewrite formula_sub_ptree_formula_neg_fit; auto; rewrite H3; simpl; auto.
    case (eq_f f (atom a)); auto.
  + rewrite H3. simpl. auto.
  + apply IHP2; auto. rewrite H3. simpl. auto.
  + rewrite H3. simpl. auto.
  + rewrite formula_sub_ptree_deg_neg; auto.
  + rewrite H3. simpl. auto.
  + rewrite formula_sub_ptree_ord_neg; auto.
  + rewrite H3. simpl. auto.

- simpl. inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  destruct S; try inversion Hs. rewrite H9.
  destruct (and_bool_prop _ _ H9) as [H10 H11].
  simpl. repeat split; rewrite formula_sub_ptree_formula_true.
  + rewrite formula_sub_ptree_formula_neg_fit; auto; rewrite H1; simpl.
    { rewrite non_target_sub'. auto. }
    { rewrite non_target_fit, H10. auto. }
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + apply IHP1; auto. rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite formula_sub_ptree_formula_neg_fit; auto; rewrite H3; simpl; auto.
    case (eq_f f0 (atom a)); auto.
  + rewrite H3. simpl. auto.
  + apply IHP2; auto. rewrite H3. simpl. auto.
  + rewrite H3. simpl. auto.
  + rewrite formula_sub_ptree_deg_neg; auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite formula_sub_ptree_deg_neg; auto.
  + rewrite H3. simpl. auto.
  + rewrite formula_sub_ptree_ord_neg; auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite formula_sub_ptree_ord_neg; auto.
  + rewrite H3. simpl. auto.
Qed.


(* We finally show that if the C \/ (neg (atom a)) is provable
where 'a' is correct, then C \/ C is provable. *)
(* *)
Lemma neg_sub_valid :
  forall (D : formula) (a : atomic_formula) (d : nat) (alpha : ord),
  PA_omega_axiom (neg (atom a)) = false ->
  provable (lor (neg (atom a)) D) d alpha ->
  provable (lor D D) d alpha.
Proof.
unfold provable. intros D a d alpha Ha H. destruct H as [P [[[HP1 HP2] HP3] HP4]].
exists (formula_sub_ptree P (neg (atom a)) D (lor_ind (1) (non_target D))).
unfold P_proves. repeat split.
- rewrite formula_sub_ptree_formula_neg; auto. rewrite HP1.
  unfold formula_sub_ind. simpl. rewrite non_target_fit. simpl.
  rewrite eq_atom_refl. rewrite non_target_sub'. auto.
- apply formula_sub_valid_neg; auto.
  + pose proof (provable_closed' P (lor (neg (atom a)) D) HP2 HP1).
    simpl in H. destruct (and_bool_prop _ _ H). auto.
  + rewrite HP1. simpl. rewrite non_target_fit. auto.
- rewrite formula_sub_ptree_deg_neg; auto.
- rewrite formula_sub_ptree_ord_neg; auto.
Qed.

