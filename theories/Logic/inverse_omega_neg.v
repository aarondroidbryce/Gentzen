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
Require Import Lia.


Lemma w_rule_invertible_a :
  forall (P : ptree) (A : formula) (n d : nat) (alpha : ord),
  (P_proves P (neg (univ n A)) d alpha ->
  { t : term & provable (substitution (neg A) n t) d alpha}) * (forall B, P_proves P (lor (neg (univ n A)) B) d alpha ->
  { t : term & provable (lor (substitution (neg A) n t) B) d alpha}).
Proof.
unfold provable. intros P. induction P; intros A m d alpha; split.
- intros [[[Ht1 Ht2] Ht3] Ht4]. destruct Ht2. simpl in Ht3. apply IHP; repeat split; auto. lia.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. destruct Ht2. simpl in Ht3. apply IHP; repeat split; auto. lia.
- intros [[[Ht1 Ht2] Ht3] Ht4]. destruct Ht2 as [[Ht2a Ht2b] Ht2c]. simpl in Ht3,Ht4.
  assert (P_proves P (neg (univ m A)) d (ptree_ord P)). repeat split; auto.
  destruct (IHP A m d (ptree_ord P)) as [IP1 IP2]. destruct (IP1 X) as [p [P1 [[[HP1 HP2] HP3] HP4]]]. exists p. exists (ord_up alpha P1). destruct Ht4,HP4. repeat split; auto.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. destruct Ht2 as [[Ht2a Ht2b] Ht2c]. simpl in Ht3,Ht4.
  assert (P_proves P (lor (neg (univ m A)) B) d (ptree_ord P)). repeat split; auto.
  destruct (IHP A m d (ptree_ord P)) as [IP1 IP2]. destruct (IP2 B X) as [p [P1 [[[HP1 HP2] HP3] HP4]]]. exists p. exists (ord_up alpha P1). destruct Ht4,HP4. repeat split; auto.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. rewrite Ht1 in Ht2. inversion Ht2.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. rewrite Ht1 in Ht2. inversion Ht2.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. 
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. destruct H0,H1. destruct Ht2 as [[[[Ht2a Ht2b] Ht2c] Ht2d] Ht2e]. simpl in Ht3,Ht4. exists t. simpl in Ht4. exists (ord_up (ord_succ o) P). rewrite Ht2e. repeat split; simpl; auto. apply ord_succ_monot. apply ord_succ_nf. apply ptree_ord_nf. auto. lia. rewrite <- Ht2e. auto.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. destruct H0,H1,H2. destruct Ht2 as [[[[Ht2a Ht2b] Ht2c] Ht2d] Ht2e]. simpl in Ht3,Ht4. exists t. simpl in Ht4. exists (ord_up (ord_succ o) P). rewrite Ht2e. repeat split; simpl; auto. apply ord_succ_monot. apply ord_succ_nf. apply ptree_ord_nf. auto. lia. rewrite <- Ht2e. auto. 
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
Admitted.

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



Definition neg_w_rule_sub_formula
  (A E : formula) (n m : nat) (S : subst_ind) : formula :=
  formula_sub_ind A (neg (univ n E)) (substitution (neg E) n (represent m)) S.

Lemma neg_w_rule_sub_formula_closed : forall (A : formula),
  closed A = true ->
  forall (E : formula) (n m : nat) (S : subst_ind),
    closed (neg_w_rule_sub_formula A E n m S) = true.
Proof.
intros. unfold neg_w_rule_sub_formula. apply formula_sub_ind_closed; auto.
intros. apply (closed_univ_sub E n H0 (represent m)). apply repr_closed.
Qed.


Fixpoint neg_w_rule_sub_ptree_fit
  (P : ptree) (E : formula) (n m : nat) (S : subst_ind) : ptree :=
match P, S with
| deg_up d P', _ => deg_up d (neg_w_rule_sub_ptree_fit P' E n m S)

| ord_up alpha P', _ => ord_up alpha (neg_w_rule_sub_ptree_fit P' E n m S)

| node A, _ => P

| exchange_ab A B d alpha P', lor_ind S_B S_A =>
    exchange_ab
      (neg_w_rule_sub_formula A E n m S_A)
      (neg_w_rule_sub_formula B E n m S_B)
      d alpha
      (neg_w_rule_sub_ptree_fit P' E n m (lor_ind S_A S_B))

| exchange_cab C0 A B d alpha P', lor_ind (lor_ind S_C S_B) S_A =>
    exchange_cab
      (neg_w_rule_sub_formula C0 E n m S_C)
      (neg_w_rule_sub_formula A E n m S_A)
      (neg_w_rule_sub_formula B E n m S_B)
      d alpha
      (neg_w_rule_sub_ptree_fit P' E n m (lor_ind (lor_ind S_C S_A) S_B))

| exchange_abd A B D d alpha P', lor_ind (lor_ind S_B S_A) S_D =>
    exchange_abd
      (neg_w_rule_sub_formula A E n m S_A)
      (neg_w_rule_sub_formula B E n m S_B)
      (neg_w_rule_sub_formula D E n m S_D)
      d alpha
      (neg_w_rule_sub_ptree_fit P' E n m (lor_ind (lor_ind S_A S_B) S_D))

| exchange_cabd C0 A B D d alpha P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D =>
    exchange_cabd
      (neg_w_rule_sub_formula C0 E n m S_C)
      (neg_w_rule_sub_formula A E n m S_A)
      (neg_w_rule_sub_formula B E n m S_B)
      (neg_w_rule_sub_formula D E n m S_D)
      d alpha
      (neg_w_rule_sub_ptree_fit
        P' E n m
        (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D))

| contraction_a A d alpha P', _ =>
    contraction_a
      (neg_w_rule_sub_formula A E n m S)
      d alpha
      (neg_w_rule_sub_ptree_fit P' E n m (lor_ind S S))

| contraction_ad A D d alpha P', lor_ind S_A S_D =>
    contraction_ad
      (neg_w_rule_sub_formula A E n m S_A)
      (neg_w_rule_sub_formula D E n m S_D)
      d alpha
      (neg_w_rule_sub_ptree_fit P' E n m (lor_ind (lor_ind S_A S_A) S_D))

| weakening_ad A D d alpha P', lor_ind S_A S_D =>
    weakening_ad
      (neg_w_rule_sub_formula A E n m S_A)
      (neg_w_rule_sub_formula D E n m S_D)
      d alpha
      (neg_w_rule_sub_ptree_fit P' E n m S_D)

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, _ => P

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_AB S_D =>
    demorgan_abd
      A B
      (neg_w_rule_sub_formula D E n m S_D)
      d1 d2 alpha1 alpha2
      (neg_w_rule_sub_ptree_fit P1 E n m (lor_ind (0) S_D))
      (neg_w_rule_sub_ptree_fit P2 E n m (lor_ind (0) S_D))

| negation_a A d alpha P', _ => P

| negation_ad A D d alpha P', lor_ind S_A S_D =>
    negation_ad
      A
      (neg_w_rule_sub_formula D E n m S_D)
      d alpha
      (neg_w_rule_sub_ptree_fit P' E n m (lor_ind (non_target A) S_D))

| quantification_a A k t d alpha P', _ =>
    (match eq_f A E, eq_nat k n, S with
    | true, true, (1) => ord_up (ord_succ alpha) P'
    | _, _ , _ => P
    end)    

| quantification_ad A D k t d alpha P', lor_ind S_A S_D =>
    quantification_ad
      A
      (neg_w_rule_sub_formula D E n m S_D)
      k t d alpha
      (neg_w_rule_sub_ptree_fit P' E n m (lor_ind (0) S_D))

| w_rule_a A k d alpha g, _ => P

| w_rule_ad A D k d alpha g, lor_ind S_A S_D => P

| cut_ca C0 A d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ca
      (neg_w_rule_sub_formula C0 E n m S)
      A d1 d2 alpha1 alpha2
      (neg_w_rule_sub_ptree_fit P1 E n m (lor_ind S (non_target A)))
      P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ad
      A
      (neg_w_rule_sub_formula D E n m S)
      d1 d2 alpha1 alpha2
      P1
      (neg_w_rule_sub_ptree_fit P2 E n m (lor_ind (0) S))

| cut_cad C0 A D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_D =>
    cut_cad
      (neg_w_rule_sub_formula C0 E n m S_C)
      A
      (neg_w_rule_sub_formula D E n m S_D)
      d1 d2 alpha1 alpha2
      (neg_w_rule_sub_ptree_fit P1 E n m (lor_ind S_C (non_target A)))
      (neg_w_rule_sub_ptree_fit P2 E n m (lor_ind (0) S_D))

| _, _ => P
end.

Definition neg_w_rule_sub_ptree
  (P : ptree) (E : formula) (n m : nat) (S : subst_ind) : ptree :=
match subst_ind_fit (ptree_formula P) S with
| false => P
| true => neg_w_rule_sub_ptree_fit P E n m S
end.

Lemma neg_w_rule_simp : forall (P : ptree) (E : formula) (n m : nat) (S : subst_ind), subst_ind_fit (ptree_formula P) S = true -> neg_w_rule_sub_ptree P E n m S = neg_w_rule_sub_ptree_fit P E n m S .
Proof.
intros. unfold neg_w_rule_sub_ptree. rewrite H. auto.
Qed.
(* First, we must prove that w_rule_sub_ptree simply changes the base formula
of an ptree the way we expect with w_rule_sub_formula *)
(* *)
Lemma neg_w_rule_ptree_formula_aux' :
  forall (P : ptree) (E : formula) (n m : nat) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
    neg_w_rule_sub_ptree P E n m S = P.
Proof. intros. unfold neg_w_rule_sub_ptree. rewrite H; auto. Qed.

Lemma neg_w_rule_ptree_formula_aux :
  forall (P : ptree) (E : formula) (n m : nat) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
      ptree_formula (neg_w_rule_sub_ptree P E n m S) =
      neg_w_rule_sub_formula (ptree_formula P) E n m S.
Proof.
intros. rewrite neg_w_rule_ptree_formula_aux'.
- unfold neg_w_rule_sub_formula. rewrite sub_fit_false. auto. apply H.
- apply H.
Qed.

Lemma neg_w_rule_ptree_formula_true :
  forall (P : ptree) (E : formula) (n m : nat) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    neg_w_rule_sub_ptree_fit P E n m S = neg_w_rule_sub_ptree P E n m S.
Proof. intros. unfold neg_w_rule_sub_ptree. rewrite H; auto. Qed.

Lemma neg_w_rule_ptree_formula' : forall (P : ptree) (E : formula) (n : nat),
  valid P ->
  forall (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true -> {m : nat &
    ptree_formula (neg_w_rule_sub_ptree P E n m S) =
    neg_w_rule_sub_formula (ptree_formula P) E n m S}.
Proof.
intros P E n.
induction P; try intros H S Hs.

- simpl. unfold neg_w_rule_sub_ptree. rewrite Hs. simpl. simpl in Hs.
  destruct H as [H1 H2]. destruct (IHP H2 _ Hs) as [m Hm]. rewrite <- (neg_w_rule_ptree_formula_true _ _ _ _ _ Hs) in Hm.
  exists m. auto.

- simpl. unfold neg_w_rule_sub_ptree. rewrite Hs. simpl. simpl in Hs. 
  destruct H as [[H1 H2] H3]. destruct (IHP H2 _ Hs) as [m Hm]. rewrite <- (neg_w_rule_ptree_formula_true _ _ _ _ _ Hs) in Hm.
  exists m. auto.  

- simpl. exists 0. inversion H.
  destruct (axiom_atomic _ H1); destruct H0; rewrite H0;
  unfold neg_w_rule_sub_formula; simpl; destruct S; auto.

- simpl. exists 0. unfold neg_w_rule_sub_ptree. rewrite Hs. simpl.
  destruct S; inversion Hs. simpl. unfold neg_w_rule_sub_formula.
  rewrite formula_sub_ind_lor; auto.

- simpl. exists 0. unfold neg_w_rule_sub_ptree. rewrite Hs.
  destruct S; try destruct S1; inversion Hs;
  simpl; unfold neg_w_rule_sub_formula.
  rewrite formula_sub_ind_lor, formula_sub_ind_lor; auto.
  apply (and_bool_prop _ _ H1).

- simpl. exists 0. unfold neg_w_rule_sub_ptree. rewrite Hs.
  destruct S; try destruct S1; inversion Hs;
  simpl; unfold neg_w_rule_sub_formula.
  rewrite formula_sub_ind_lor, formula_sub_ind_lor; auto.
  apply (and_bool_prop _ _ H1).

- simpl. exists 0. unfold neg_w_rule_sub_ptree. rewrite Hs. destruct S; simpl.
  + unfold neg_w_rule_sub_formula. auto.
  + unfold neg_w_rule_sub_formula. auto.
  + destruct S1; try destruct S1_1; inversion Hs.
   simpl. unfold neg_w_rule_sub_formula.
    destruct (and_bool_prop _ _ H1). destruct (and_bool_prop _ _ H0).
    repeat rewrite formula_sub_ind_lor; auto.

- simpl. exists 0. unfold neg_w_rule_sub_ptree. rewrite Hs. auto.

- simpl. exists 0. unfold neg_w_rule_sub_ptree. rewrite Hs. destruct S; inversion Hs.
  simpl. unfold neg_w_rule_sub_formula.
  rewrite formula_sub_ind_lor. auto. apply H1.

- simpl. exists 0. unfold neg_w_rule_sub_ptree. rewrite Hs. destruct S; auto. inversion Hs. simpl.
  unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_lor. auto. apply H1.

- simpl. exists 0. destruct S; auto.

- simpl. exists 0. destruct S.
  + inversion Hs.
  + inversion Hs.
  + unfold neg_w_rule_sub_ptree. rewrite Hs. destruct S1; inversion Hs; simpl; unfold neg_w_rule_sub_formula;
    rewrite formula_sub_ind_lor; auto; apply H1.

- simpl. exists 0. destruct (eq_f f E) eqn:Heq; destruct S.
  + simpl. unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_0. auto.
  + unfold neg_w_rule_sub_formula. simpl. inversion H as [[[H1 H2] H3] H4]. auto.
  + inversion Hs.
  + simpl. unfold neg_w_rule_sub_formula. rewrite formula_sub_ind_0. auto.
  + unfold neg_w_rule_sub_formula. simpl. auto.
  + inversion Hs.

- simpl. exists 0. destruct (eq_f f E) eqn:Heq; destruct S.
  + inversion Hs.
  + inversion Hs.
  + unfold neg_w_rule_sub_ptree. rewrite Hs. destruct S1.
    * apply (subst_ind_fit_lor) in Hs. destruct (and_bool_prop _ _ Hs).
      simpl. unfold neg_w_rule_sub_formula.
      rewrite formula_sub_ind_lor, formula_sub_ind_0. auto. apply Hs.
    * inversion Hs. simpl. inversion H as [[[H2 H3] H4] H5].
      unfold neg_w_rule_sub_formula. simpl. rewrite H1. rewrite sub_fit_true; auto.
    * simpl. inversion Hs.
  + inversion Hs.
  + inversion Hs.
  + unfold neg_w_rule_sub_ptree. rewrite Hs. destruct S1.
    * apply (subst_ind_fit_lor) in Hs. destruct (and_bool_prop _ _ Hs).
      simpl. unfold neg_w_rule_sub_formula.
      rewrite formula_sub_ind_lor, formula_sub_ind_0. auto. apply Hs.
    * inversion Hs. simpl. unfold neg_w_rule_sub_formula.
      rewrite formula_sub_ind_lor; auto.
    * simpl. inversion Hs.

- simpl. exists n0. unfold neg_w_rule_sub_ptree. rewrite Hs. destruct S; simpl; unfold neg_w_rule_sub_formula; simpl; case (eq_f f E); case (eq_nat n0 n); simpl; auto. destruct H as [[[[X1 X2] X3] X4] X5]. auto. admit.
  

- simpl. destruct S.
  + simpl. unfold w_rule_sub_formula. simpl. auto.
  + simpl. unfold w_rule_sub_formula. simpl. auto.
  + destruct S1; inversion Hs; rewrite H1; simpl; unfold w_rule_sub_formula.
    * rewrite formula_sub_ind_lor; auto.
    * simpl. rewrite H1. rewrite sub_fit_true; auto.

- intros. simpl. destruct S; auto.
  + destruct (eq_f f E) eqn:HE; destruct (eq_nat n0 n) eqn:Hn; simpl;
    unfold w_rule_sub_formula; simpl; rewrite Hn,HE; auto;
    simpl; case_eq (eq_nat n1 (ptree_deg (p m))); intros; simpl; auto.
  + case_eq (eq_nat n1 (ptree_deg (p m)));
    destruct (eq_f f E) eqn:HE; destruct (eq_nat n0 n) eqn:Hn; simpl;
    try unfold w_rule_sub_formula; simpl; try rewrite Hn,HE; auto;
    rename f into A; rename p into g; rename n1 into d; rename o into alpha;
    simpl; destruct (valid_w_rule_a A n0 d alpha g X m) as [[[Hg1 Hg2] Hg3] Hg4];
    unfold w_rule_sub_formula; simpl; rewrite Hg1;
    rewrite (f_eq_decid _ _ HE),(nat_eq_decid _ _ Hn); auto.

- intros. simpl. destruct S; auto. destruct S1; auto.
  + destruct (eq_nat n1 (ptree_deg (p m))) eqn:HD.
    * destruct (subst_ind_fit f0 S2) eqn:HS2; simpl.
      { destruct (eq_f f E) eqn:HE.
        { destruct (eq_nat n0 n) eqn:Hn.
          { simpl. unfold w_rule_sub_formula. simpl. rewrite HS2,Hn,HE. simpl.
            rewrite sub_fit_true; auto. }
          { simpl. unfold w_rule_sub_formula. simpl. rewrite HS2,Hn,HE. simpl.
            rewrite sub_fit_true; auto. } }
        { destruct (eq_nat n0 n) eqn:Hn.
          { simpl. unfold w_rule_sub_formula. simpl. rewrite HS2,Hn,HE. simpl.
            rewrite sub_fit_true; auto. }
          { simpl. unfold w_rule_sub_formula. simpl. rewrite HS2,Hn,HE. simpl.
            rewrite sub_fit_true; auto. } } }
      { destruct (eq_f f E) eqn:HE.
        { destruct (eq_nat n0 n) eqn:Hn.
          { simpl. unfold w_rule_sub_formula. simpl. rewrite HS2. auto. }
          { simpl. unfold w_rule_sub_formula. simpl. rewrite HS2. auto. } }
        { destruct (eq_nat n0 n) eqn:Hn.
          { simpl. unfold w_rule_sub_formula. simpl. rewrite HS2. auto. }
          { simpl. unfold w_rule_sub_formula. simpl. rewrite HS2. auto. } } }
    * destruct (subst_ind_fit f0 S2) eqn:HS2; simpl.
    { destruct (eq_f f E) eqn:HE.
      { destruct (eq_nat n0 n) eqn:Hn.
        { simpl. unfold w_rule_sub_formula. simpl. rewrite HS2,Hn,HE. simpl.
          rewrite sub_fit_true; auto. }
        { simpl. unfold w_rule_sub_formula. simpl. rewrite HS2,Hn,HE. simpl.
          rewrite sub_fit_true; auto. } }
      { destruct (eq_nat n0 n) eqn:Hn.
        { simpl. unfold w_rule_sub_formula. simpl. rewrite HS2,Hn,HE. simpl.
          rewrite sub_fit_true; auto. }
        { simpl. unfold w_rule_sub_formula. simpl. rewrite HS2,Hn,HE. simpl.
          rewrite sub_fit_true; auto. } } }
    { destruct (eq_f f E) eqn:HE.
      { destruct (eq_nat n0 n) eqn:Hn.
        { simpl. unfold w_rule_sub_formula. simpl. rewrite HS2. auto. }
        { simpl. unfold w_rule_sub_formula. simpl. rewrite HS2. auto. } }
      { destruct (eq_nat n0 n) eqn:Hn.
        { simpl. unfold w_rule_sub_formula. simpl. rewrite HS2. auto. }
        { simpl. unfold w_rule_sub_formula. simpl. rewrite HS2. auto. } } }
  + destruct (eq_nat n1 (ptree_deg (p m))) eqn:HD.
    * rename f into A. rename f0 into D. rename p into g.
      rename n1 into d. rename o into alpha. simpl.
      destruct (valid_w_rule_ad A D n0 d alpha g X m) as [[[Hg1 Hg2] Hg3] Hg4].
      destruct (subst_ind_fit D S2) eqn:HS2; simpl;
      destruct (eq_f A E) eqn:HE; destruct (eq_nat n0 n) eqn:Hn; simpl;
      unfold w_rule_sub_formula; simpl; rewrite HS2; auto;
      rewrite Hn,HE; simpl; try rewrite sub_fit_true; auto.
      rewrite w_rule_ptree_formula_true.
      { rewrite (H m Hg2 (lor_ind (non_target A) S2)).
        { rewrite Hg1. unfold w_rule_sub_formula. rewrite formula_sub_ind_lor.
          { rewrite <- sub_fit_true; auto.
            rewrite (f_eq_decid _ _ HE),(nat_eq_decid _ _ Hn). simpl.
            rewrite (non_target_term_sub E n (represent m)).
            rewrite non_target_sub. auto. }
          { rewrite (non_target_term_sub A n0 (represent m)).
            rewrite non_target_fit,HS2. auto. } }
        { rewrite Hg1. rewrite (non_target_term_sub A n0 (represent m)).
          simpl. rewrite non_target_fit,HS2. auto. } }
      { rewrite Hg1. rewrite (non_target_term_sub A n0 (represent m)).
        simpl. rewrite non_target_fit,HS2. auto. }
    * rename f into A. rename f0 into D. rename p into g.
      rename n1 into d. rename o into alpha. simpl.
      destruct (valid_w_rule_ad A D n0 d alpha g X m) as [[[Hg1 Hg2] Hg3] Hg4].
      destruct (subst_ind_fit D S2) eqn:HS2; simpl;
      destruct (eq_f A E) eqn:HE; destruct (eq_nat n0 n) eqn:Hn; simpl;
      unfold w_rule_sub_formula; simpl; rewrite HS2; auto;
      rewrite Hn,HE; simpl; try rewrite sub_fit_true; auto.
      rewrite w_rule_ptree_formula_true.
      { rewrite (H m Hg2 (lor_ind (non_target A) S2)).
        { rewrite Hg1. unfold w_rule_sub_formula. rewrite formula_sub_ind_lor.
          { rewrite <- sub_fit_true; auto.
            rewrite (f_eq_decid _ _ HE),(nat_eq_decid _ _ Hn). simpl.
            rewrite (non_target_term_sub E n (represent m)).
            rewrite non_target_sub. auto. }
          { rewrite (non_target_term_sub A n0 (represent m)).
            rewrite non_target_fit,HS2. auto. } }
        { rewrite Hg1. rewrite (non_target_term_sub A n0 (represent m)).
          simpl. rewrite non_target_fit,HS2. auto. } }
      { rewrite Hg1. rewrite (non_target_term_sub A n0 (represent m)).
        simpl. rewrite non_target_fit,HS2. auto. }

- simpl. inversion Hs. rewrite H1. auto.

- simpl. inversion Hs. rewrite H1. auto.

- simpl. destruct S; inversion Hs.
  rewrite H1. simpl. unfold w_rule_sub_formula.
  rewrite formula_sub_ind_lor; auto.
Qed.


Lemma w_rule_ptree_formula : forall (P : ptree) (E : formula) (n m : nat),
  valid P ->
  forall (S : subst_ind),
    ptree_formula (w_rule_sub_ptree P E n m S) =
    w_rule_sub_formula (ptree_formula P) E n m S.
Proof.
intros. destruct (subst_ind_fit (ptree_formula P) S) eqn:Hs.
- apply w_rule_ptree_formula'. apply X. apply Hs.
- apply w_rule_ptree_formula_aux. apply Hs.
Qed.





(* Second, we must prove that w_rule_sub_ptree does not change the degree
of an ptree. *)
(* *)
Lemma w_rule_ptree_deg : forall (P : ptree) (E : formula) (n m : nat),
  valid P ->
  forall (S : subst_ind), ptree_deg P = ptree_deg (w_rule_sub_ptree P E n m S).
Proof.
intros P E n m H. induction P; intros S.
- simpl. case (subst_ind_fit (ptree_formula P) S); auto.
- simpl. case (subst_ind_fit (ptree_formula P) S) eqn:Hfit; auto. simpl.
  rewrite (w_rule_ptree_formula_true _ _ _ _ _ Hfit).
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
- simpl. destruct S; auto.
- simpl.
  destruct S; auto; destruct S1; auto; destruct (subst_ind_fit f0 S2); auto.
- simpl. destruct S; destruct (eq_f f E) eqn:HE; destruct (eq_nat n0 n); auto;
  rename f into A; rename p into g; rename n1 into d; rename o into alpha;
  destruct (eq_nat d (ptree_deg (g m))) eqn:X1; intros; auto. apply nat_eq_decid. auto. 
- simpl. destruct S; auto.
  destruct S1; auto; destruct (subst_ind_fit f0 S2) eqn:HS2; simpl;
  destruct (eq_f f E) eqn:HE; destruct (eq_nat n0 n) eqn:Hn; auto;
  destruct (eq_nat n1 (ptree_deg (p m))) eqn:X1; auto.
  rename f into A. rename f0 into D. rename p into g.
  rename n1 into d. rename o into alpha.
  simpl. destruct (valid_w_rule_ad A D n0 d alpha g H m) as [[[Hg1 Hg2] Hg3] Hg4].
  rewrite w_rule_ptree_formula_true.
  + pose proof (H0 m Hg2 (lor_ind (non_target A) S2)). rewrite <- H1. apply nat_eq_decid. auto.
  + rewrite Hg1. simpl. rewrite (non_target_term_sub A n0 (represent m)).
    rewrite non_target_fit,HS2. auto.
- simpl. destruct (subst_ind_fit f S); auto.
- simpl. destruct (subst_ind_fit f0 S); auto.
- simpl.
  destruct S; auto. destruct (subst_ind_fit f S1 && subst_ind_fit f1 S2); auto.
Qed.


(* Third, we must prove that w_rule_sub_ptree does not change the ordinal
of an ptree. *)
(* *)
Lemma w_rule_ptree_ord : forall (P : ptree) (E : formula) (n m : nat),
  valid P ->
  forall (S : subst_ind), ptree_ord (w_rule_sub_ptree P E n m S) = ptree_ord P.
Proof.
intros P E n m H. induction P; intros S.
- simpl. case (subst_ind_fit (ptree_formula P) S) eqn:Hfit; auto. simpl.
  rewrite (w_rule_ptree_formula_true _ _ _ _ _ Hfit).
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
- simpl. destruct S; destruct (eq_f f E) eqn:HE; destruct (eq_nat n0 n); auto;
  destruct (eq_nat n1 (ptree_deg (p m))) eqn:X1; auto;
  rename f into A; rename p into g; rename n1 into d; rename o into alpha;
  simpl; destruct (valid_w_rule_a A n0 d alpha g H m) as [[[Hg1 Hg2] Hg3] Hg4]; auto.
- simpl. destruct S; auto.
  destruct S1; auto; destruct (subst_ind_fit f0 S2) eqn:HS2; simpl;
  destruct (eq_f f E) eqn:HE; destruct (eq_nat n0 n) eqn:Hn; auto;
  destruct (eq_nat n1 (ptree_deg (p m))) eqn:X1; auto;
  rename f into A; rename f0 into D; rename p into g;
  rename n1 into d; rename o into alpha;
  simpl; destruct (valid_w_rule_ad A D n0 d alpha g H m) as [[[Hg1 Hg2] Hg3] Hg4];
  rewrite w_rule_ptree_formula_true.
- simpl. destruct (subst_ind_fit f S); auto.
- simpl. destruct (subst_ind_fit f0 S); auto.
- simpl. destruct S; auto. destruct (subst_ind_fit f S1 && subst_ind_fit f1 S2); auto.
Qed.


(* Now we prove that if we have a valid ptree, performing our
w_rule substitution on it results in a valid ptree *)
(* *)
Lemma w_rule_valid : forall (P : ptree) (E : formula) (n m : nat),
  valid P ->
  forall (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    valid (w_rule_sub_ptree P E n m S).
Proof.
intros P E n m.
induction P; try intros H S Hs.

- simpl. inversion H as [H1 H2]. inversion Hs. rewrite H3.
  rewrite w_rule_ptree_formula_true; auto. split.
  + pose proof (w_rule_ptree_deg P E n m H2 S). lia.
  + apply (IHP H2 S H3).

- simpl. inversion H as [[H1 H2] H3]. inversion Hs. rewrite H4.
  rewrite w_rule_ptree_formula_true; auto. split.
  + rewrite w_rule_ptree_ord; auto.
  + auto.

- simpl. destruct (subst_ind_fit f S); apply H.

- simpl. destruct S; inversion Hs. rewrite H1. simpl.
  inversion H as [[[H2 H3] H4] H5].
  repeat split; rewrite w_rule_ptree_formula_true.
  + rewrite w_rule_ptree_formula; auto.
    rewrite H2. unfold w_rule_sub_formula.
    rewrite formula_sub_ind_lor; auto. apply (and_bool_symm _ _ H1).
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + apply IHP. apply H. rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + rewrite H4. apply (w_rule_ptree_deg P E n m H3 ( lor_ind S2 S1 )).
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + rewrite w_rule_ptree_ord; auto.
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).

- simpl. destruct S; try destruct S1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H4 H5] H6] H7].
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  repeat split; rewrite w_rule_ptree_formula_true.
  + rewrite w_rule_ptree_formula; auto.
    rewrite H4. unfold w_rule_sub_formula.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H1, H2. auto.
    * simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + apply IHP; auto. rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite H6. apply w_rule_ptree_deg; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite w_rule_ptree_ord; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.

- simpl. destruct S; try destruct S1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H4 H5] H6] H7].
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  repeat split; rewrite w_rule_ptree_formula_true.
  + rewrite w_rule_ptree_formula; auto.
    rewrite H4. unfold w_rule_sub_formula.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H1, H3. auto.
    * simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + apply IHP; auto. rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite H6. apply w_rule_ptree_deg; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite w_rule_ptree_ord; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.

- simpl. destruct S; try destruct S1; try destruct S1_1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H5 H6] H7] H8].
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  destruct (and_bool_prop _ _ H1). clear H1.
  repeat split; rewrite w_rule_ptree_formula_true.
  + rewrite w_rule_ptree_formula; auto.
    rewrite H5. unfold w_rule_sub_formula.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H0,H3. auto.
    * simpl. rewrite H0, H3, H4. auto.
    * simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + apply IHP; auto. rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite H7. apply w_rule_ptree_deg; auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite w_rule_ptree_ord; auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.

- simpl. inversion Hs. rewrite H1. inversion H as [[[H2 H3] H4] H5].
  repeat split; rewrite w_rule_ptree_formula_true.
  + rewrite w_rule_ptree_formula; auto.
    unfold w_rule_sub_formula. rewrite H2.
    rewrite formula_sub_ind_lor; auto. rewrite H1. auto.
  + rewrite H2. simpl. rewrite H1. auto.
  + apply IHP. apply H. rewrite H2. simpl. rewrite H1. auto.
  + rewrite H2. simpl. rewrite H1. auto.
  + rewrite H4. apply w_rule_ptree_deg; auto.
  + rewrite H2. simpl. rewrite H1. auto.
  + rewrite w_rule_ptree_ord; auto.
  + rewrite H2. simpl. rewrite H1. auto.

- simpl. destruct S; inversion Hs. rewrite H1.
  inversion H as [[[H2 H3] H4] H5]. destruct (and_bool_prop _ _ H1).
  repeat split; rewrite w_rule_ptree_formula_true.
  + rewrite w_rule_ptree_formula; auto.
    unfold w_rule_sub_formula. rewrite H2.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H0. auto.
    * simpl. rewrite H0, H6. auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + apply IHP. apply H. rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite H4. apply w_rule_ptree_deg; auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite w_rule_ptree_ord; auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.

- simpl. destruct S; inversion Hs. rewrite H1. simpl.
  inversion H as [[[[H2 H3] H4] H5] H6]. destruct (and_bool_prop _ _ H1).
  repeat split.
  + rewrite w_rule_ptree_formula_true.
    * rewrite w_rule_ptree_formula; auto. rewrite H2. auto.
    * rewrite H2. auto.
  + apply w_rule_sub_formula_closed. auto.
  + rewrite w_rule_ptree_formula_true.
    * apply IHP; auto. rewrite H2. auto.
    * rewrite H2. auto.
  + rewrite w_rule_ptree_formula_true.
    * rewrite H5. apply w_rule_ptree_deg; auto.
    * rewrite H2. auto.
  + rewrite w_rule_ptree_formula_true.
    * rewrite w_rule_ptree_ord; auto.
    * rewrite H2. auto.

- simpl. destruct S; apply H.

- simpl. destruct S; try apply H.
  destruct S1; inversion Hs; rewrite H1; simpl.
  + destruct H as [[[[[[[H2 H3] H4] H5] H6] H7] H8] H9].
    repeat split; rewrite w_rule_ptree_formula_true.
    * rewrite w_rule_ptree_formula; auto.
      rewrite H2. unfold w_rule_sub_formula. rewrite formula_sub_ind_lor.
      { simpl. destruct (eq_f f (neg E)); auto. }
      { rewrite H1. auto. }
    * rewrite H2. simpl. apply H1.
    * apply IHP1; auto. rewrite H2. apply H1.
    * rewrite H2. simpl. apply H1.
    * rewrite w_rule_ptree_formula; auto.
      rewrite H4. unfold w_rule_sub_formula. rewrite formula_sub_ind_lor.
      { simpl. destruct (eq_f f0 (neg E)); auto. }
      { rewrite H1. auto. }
    * rewrite H4. simpl. apply H1.
    * apply IHP2; auto. rewrite H4. simpl. apply H1.
    * rewrite H4. simpl. apply H1.
    * rewrite H6. apply w_rule_ptree_deg; auto.
    * rewrite H2. simpl. apply H1.
    * rewrite H7. apply w_rule_ptree_deg; auto.
    * rewrite H4. simpl. apply H1.
    * rewrite w_rule_ptree_ord; auto.
    * rewrite H2. simpl. apply H1.
    * rewrite w_rule_ptree_ord; auto.
    * rewrite H4. simpl. apply H1.
  + destruct H as [[[[[[[H2 H3] H4] H5] H6] H7] H8] H9].
    repeat split; rewrite w_rule_ptree_formula_true.
    * rewrite w_rule_ptree_formula; auto.
      rewrite H2. unfold w_rule_sub_formula. rewrite formula_sub_ind_lor.
      { simpl. destruct (eq_f f (neg E)); auto. }
      { rewrite H1. auto. }
    * rewrite H2. simpl. apply H1.
    * apply IHP1; auto. rewrite H2. apply H1.
    * rewrite H2. simpl. apply H1.
    * rewrite w_rule_ptree_formula; auto.
      rewrite H4. unfold w_rule_sub_formula. rewrite formula_sub_ind_lor.
      { simpl. destruct (eq_f f0 (neg E)); auto. }
      { rewrite H1. auto. }
    * rewrite H4. simpl. apply H1.
    * apply IHP2; auto. rewrite H4. simpl. apply H1.
    * rewrite H4. simpl. apply H1.
    * rewrite H6. apply w_rule_ptree_deg; auto.
    * rewrite H2. simpl. apply H1.
    * rewrite H7. apply w_rule_ptree_deg; auto.
    * rewrite H4. simpl. apply H1.
    * rewrite w_rule_ptree_ord; auto.
    * rewrite H2. simpl. apply H1.
    * rewrite w_rule_ptree_ord; auto.
    * rewrite H4. simpl. apply H1.

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
  provable (neg (univ n A)) d alpha ->
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
