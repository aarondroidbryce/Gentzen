Add LoadPath "theories/Casteran" as Ordering.
Add LoadPath "theories/Maths" as Maths_Facts.
Add LoadPath "theories/Logic" as Systems.

Require Import Lia.
Require Import Nat.
Require Import Wellfounded.
From Maths_Facts Require Import naturals.
From Maths_Facts Require Import lists.
From Maths_Facts Require Import ordinals.
From Systems Require Import definitions.
From Systems Require Import fol.
From Systems Require Import PA_omega.
Notation "b1 && b2" := (andb b1 b2).
Notation "b1 || b2" := (orb b1 b2).
Notation eq_nat := Nat.eqb.

Definition impl (A B : formula) := (lor (neg A) B).
Notation "A1 ~> A2" := (impl A1 A2) (at level 60).
Notation "t # s" := (atom (equ t s)) (at level 80).

Inductive Peano_Theorems : formula -> Type :=
| FOL1 : forall (A B : formula), Peano_Theorems  (A ~> (B ~> A))
| FOL2 : forall (A B C : formula), Peano_Theorems ((A ~> (B ~> C)) ~> ((A ~> B) ~> (A ~> C)))
| FOL3 : forall (A B : formula), Peano_Theorems ((neg A ~> neg B) ~> ((neg A ~> B) ~> A))
| FOL4 : forall (A : formula) (n : nat) (t : term), closed_t t = true -> Peano_Theorems (lor (neg(univ n A)) (substitution A n t))
| FOL5 : forall (A B : formula) (n : nat), member n (free_list A) = false -> Peano_Theorems ((univ n (A ~> B)) ~> (A ~> (univ n B)))
| MP : forall (A B : formula), Peano_Theorems (A ~> B) -> Peano_Theorems A -> Peano_Theorems B
| UG : forall (A : formula) (n : nat), member n (free_list A) = true -> Peano_Theorems A -> Peano_Theorems (univ n A)
| equ_trans : forall (t s r : term), Peano_Theorems  ((t # s) ~> ((s # r) ~> (t # r)))
| equ_succ : forall (t s : term),  Peano_Theorems ((t # s) ~> ((succ t) # (succ s)))
| non_zero : forall (t : term), Peano_Theorems (neg (zero # (succ t)))
| succ_equ : forall (t s : term),  Peano_Theorems ((succ t # succ s) ~> (t # s))
| pl0 : forall (t : term), Peano_Theorems ((plus t zero) # t)
| plS : forall (t s : term), Peano_Theorems ((plus t (succ s)) # (succ (plus t s)))
| ml0 : forall (t : term), Peano_Theorems ((times t zero) # zero)
| mlS : forall (t s : term), Peano_Theorems ((times t (succ s)) # (plus (times t s) t))
| induct : forall (A : formula) (n : nat), Peano_Theorems (substitution A n zero ~> ((univ n (A ~> (substitution A n (succ (var n))))) ~> (univ n A))).


Fixpoint inductive_chain (A : formula) (n m : nat) : formula :=
match m with
| 0 => neg ((substitution A n (represent 0)) ~> (substitution A n (succ (represent 0))))
| (S m') => (lor (inductive_chain A n m') (neg ((substitution A n (represent (S m'))) ~> (substitution A n (succ (represent (S m')))))))
end.

Definition inductive_implication (A : formula) (n m : nat) : formula :=
match m with
| 0 => (lor (substitution A n (represent m)) (neg (substitution A n (represent 0))))
| S m' => lor (lor (inductive_chain A n m') (substitution A n (represent m))) (neg (substitution A n (represent 0)))
end.

Lemma ind_imp_closed : forall A n m, free_list A = [n] -> closed (inductive_chain A n m) = true.
Proof.
intros. induction m.
- simpl. rewrite closed_univ_sub; auto. rewrite closed_univ_sub; auto. simpl. rewrite H. rewrite eq_nat_refl. destruct (closed A); auto. simpl. rewrite H. rewrite eq_nat_refl. destruct (closed A); auto.
- simpl. rewrite IHm. rewrite closed_univ_sub; simpl; auto. rewrite closed_univ_sub; simpl; auto. rewrite H. rewrite eq_nat_refl. destruct (closed A); auto. apply repr_closed. rewrite H. rewrite eq_nat_refl. destruct (closed A); auto. apply repr_closed.
Qed.

Lemma ind_imp_closed' : forall A n m, closed A = true -> closed (inductive_chain A n m) = true.
Proof.
intros. induction m.
- simpl. repeat rewrite closed_subst_eq; auto. rewrite H. auto.
- simpl. rewrite IHm. repeat rewrite closed_subst_eq; auto. rewrite H. auto.
Qed.

Lemma inductive_implication_theorem_aux : forall A n m, free_list A = [n] -> PA_omega_theorem (inductive_implication A n m) 0 (ord_add (w_tower (S (num_conn A + num_conn A))) (nat_ord (3 * (S m)))).
intros. induction m.
- apply (ord_incr _ _ (ord_succ (w_tower (num_conn A + num_conn A)))).
  + apply exchange1. assert (num_conn A = num_conn (substitution A n zero)). rewrite num_conn_sub. auto. rewrite H0. apply LEM. rewrite closed_univ_sub; auto. simpl. case (closed A); auto. rewrite H. rewrite eq_nat_refl. auto.
  + apply (lt_trans _ _ _ (w_tower_succ _)). apply add_right_incr_corr. simpl. apply zero_lt.
  + apply nf_add. apply w_tower_nf. apply nf_nat.
- assert ((ord_add (w_tower (S (num_conn A + num_conn A))) (nat_ord (3 * S (S m)))) = (ord_succ (ord_max (ord_succ (ord_succ (ord_add (w_tower (S (num_conn A + num_conn A))) (nat_ord (3 * (S m)))))) (ord_succ (ord_succ (w_tower (num_conn A + num_conn A))))))).
  { simpl. assert (ord_ltb Zero (w_tower (num_conn A + num_conn A)) = true). destruct (num_conn A); auto. rewrite (ltb_asymm _ _ H0). rewrite (ord_lt_ne _ _ H0). assert ((ord_max (ord_succ (ord_succ (cons (w_tower (num_conn A + num_conn A)) 0 (cons Zero (m + S (m + S (m + 0))) Zero)))) (ord_succ (ord_succ (w_tower (num_conn A + num_conn A))))) = (ord_succ (ord_succ (cons (w_tower (num_conn A + num_conn A)) 0 (cons Zero (m + S (m + S (m + 0))) Zero))))).
    apply ord_max_lem2. apply ltb_asymm. apply ord_lt_ltb. apply ord_lt_succ. apply ord_lt_succ. apply ord_lt_self. rewrite H1. simpl. case (w_tower (num_conn A + num_conn A)) eqn:X. destruct (num_conn A); inversion X. simpl. repeat rewrite plus_n_Sm. auto. }
  rewrite H0.
  + destruct m.
    * unfold inductive_implication. unfold inductive_chain. unfold "~>". apply associativity2. assert (max 0 0 = 0). lia. destruct H1. apply demorgan2. 
      --  apply negation2. apply associativity1. apply exchange3. apply associativity2. apply weakening. apply closed_univ_sub_repr. simpl. rewrite H. rewrite eq_nat_refl. destruct (closed A); auto. auto.
      --  apply associativity1. apply exchange1. apply weakening. apply closed_univ_sub; auto. simpl. rewrite H. rewrite eq_nat_refl. destruct (closed A); auto. simpl. assert (num_conn A = num_conn (substitution A n (succ zero))). rewrite num_conn_sub. auto. rewrite H1. apply LEM. rewrite closed_univ_sub; simpl; auto. rewrite H. rewrite eq_nat_refl. destruct (closed A); auto. 
    * unfold inductive_implication in *. unfold inductive_chain. fold inductive_chain. unfold "~>". apply exchange4. apply exchange2. apply exchange1. assert (max 0 0 = 0). lia. destruct H1. apply demorgan2.
      --  apply negation2. apply exchange1. apply exchange2. apply exchange4. apply exchange2. apply exchange1. apply weakening. apply closed_univ_sub_repr. simpl. rewrite H. rewrite eq_nat_refl. destruct (closed A); auto. auto. 
      --  apply exchange1. apply exchange4. apply exchange2. apply associativity2. apply weakening. simpl. rewrite ind_imp_closed; auto. apply closed_univ_sub; auto. simpl. rewrite H. rewrite eq_nat_refl. destruct (closed A); auto. simpl. assert (num_conn A = num_conn (substitution A n (succ (succ (represent m))))). rewrite num_conn_sub. auto. rewrite H1. apply LEM. rewrite closed_univ_sub; simpl; auto. rewrite H. rewrite eq_nat_refl. destruct (closed A); auto. apply repr_closed.
Qed.

Lemma inductive_implication_theorem_aux' : forall A n m, closed A = true -> PA_omega_theorem (inductive_implication A n m) 0 (ord_add (w_tower (S (num_conn A + num_conn A))) (nat_ord (3 * (S m)))).
intros. induction m.
- apply (ord_incr _ _ (ord_succ (w_tower (num_conn A + num_conn A)))).
  + apply exchange1. assert (num_conn A = num_conn (substitution A n zero)). rewrite num_conn_sub. auto. rewrite H0. apply LEM. rewrite closed_univ_sub; auto. simpl. rewrite H. auto.
  + apply (lt_trans _ _ _ (w_tower_succ _)). apply add_right_incr_corr. simpl. apply zero_lt.
  + apply nf_add. apply w_tower_nf. apply nf_nat.
- assert ((ord_add (w_tower (S (num_conn A + num_conn A))) (nat_ord (3 * S (S m)))) = (ord_succ (ord_max (ord_succ (ord_succ (ord_add (w_tower (S (num_conn A + num_conn A))) (nat_ord (3 * (S m)))))) (ord_succ (ord_succ (w_tower (num_conn A + num_conn A))))))).
  { simpl. assert (ord_ltb Zero (w_tower (num_conn A + num_conn A)) = true). destruct (num_conn A); auto. rewrite (ltb_asymm _ _ H0). rewrite (ord_lt_ne _ _ H0). assert ((ord_max (ord_succ (ord_succ (cons (w_tower (num_conn A + num_conn A)) 0 (cons Zero (m + S (m + S (m + 0))) Zero)))) (ord_succ (ord_succ (w_tower (num_conn A + num_conn A))))) = (ord_succ (ord_succ (cons (w_tower (num_conn A + num_conn A)) 0 (cons Zero (m + S (m + S (m + 0))) Zero))))).
    apply ord_max_lem2. apply ltb_asymm. apply ord_lt_ltb. apply ord_lt_succ. apply ord_lt_succ. apply ord_lt_self. rewrite H1. simpl. case (w_tower (num_conn A + num_conn A)) eqn:X. destruct (num_conn A); inversion X. simpl. repeat rewrite plus_n_Sm. auto. }
  rewrite H0.
  + destruct m.
    * unfold inductive_implication. unfold inductive_chain. unfold "~>". apply associativity2. assert (max 0 0 = 0). lia. destruct H1. apply demorgan2. 
      --  apply negation2. apply associativity1. apply exchange3. apply associativity2. apply weakening. apply closed_univ_sub_repr. simpl. rewrite H. auto. auto.
      --  apply associativity1. apply exchange1. apply weakening. apply closed_univ_sub; auto. simpl. rewrite H. auto. simpl. assert (num_conn A = num_conn (substitution A n (succ zero))). rewrite num_conn_sub. auto. rewrite H1. apply LEM. rewrite closed_univ_sub; simpl; auto. rewrite H. auto. 
    * unfold inductive_implication in *. unfold inductive_chain. fold inductive_chain. unfold "~>". apply exchange4. apply exchange2. apply exchange1. assert (max 0 0 = 0). lia. destruct H1. apply demorgan2.
      --  apply negation2. apply exchange1. apply exchange2. apply exchange4. apply exchange2. apply exchange1. apply weakening. apply closed_univ_sub_repr. simpl. rewrite H. auto. auto. 
      --  apply exchange1. apply exchange4. apply exchange2. apply associativity2. apply weakening. simpl. rewrite ind_imp_closed'; auto. apply closed_univ_sub; auto. simpl. rewrite H. auto. simpl. assert (num_conn A = num_conn (substitution A n (succ (succ (represent m))))). rewrite num_conn_sub. auto. rewrite H1. apply LEM. rewrite closed_univ_sub; simpl; auto. rewrite H. auto. apply repr_closed.
Qed.

Lemma inductive_implication_theorem : forall A n m, free_list A = [n] -> PA_omega_theorem (inductive_implication A n m) 0 (w_tower (S (S (num_conn A + num_conn A)))).
intros. refine (ord_incr _ _ (ord_add (w_tower (S (num_conn A + num_conn A))) (nat_ord (3 * (S m)))) _ _ _ (w_tower_nf _)). apply inductive_implication_theorem_aux. auto.
simpl. assert (ord_ltb Zero (w_tower (num_conn A + num_conn A)) = true). destruct (num_conn A); auto. rewrite (ltb_asymm _ _ H0). rewrite (ord_lt_ne _ _ H0). apply head_lt. apply ord_lt_self. 
Qed.

Lemma inductive_implication_theorem' : forall A n m, closed A = true -> PA_omega_theorem (inductive_implication A n m) 0 (w_tower (S (S (num_conn A + num_conn A)))).
intros. refine (ord_incr _ _ (ord_add (w_tower (S (num_conn A + num_conn A))) (nat_ord (3 * (S m)))) _ _ _ (w_tower_nf _)). apply inductive_implication_theorem_aux'. auto.
simpl. assert (ord_ltb Zero (w_tower (num_conn A + num_conn A)) = true). destruct (num_conn A); auto. rewrite (ltb_asymm _ _ H0). rewrite (ord_lt_ne _ _ H0). apply head_lt. apply ord_lt_self. 
Qed.

Lemma induction_iterate : forall (A : formula) (n m : nat) (t : term), PA_omega_theorem (lor (lor (lor (inductive_chain A n (S m)) (substitution A n t)) (neg (substitution A n zero))) (neg (univ n (lor (neg A) (substitution A n (succ (var n))))))) 0 (w_tower (S (S (num_conn A + num_conn A)))) -> PA_omega_theorem (lor (lor (lor (inductive_chain A n m) (substitution A n t)) (neg (substitution A n zero))) (neg (univ n (lor (neg A) (substitution A n (succ (var n))))))) 0 (ord_succ (w_tower (S (S (num_conn A + num_conn A))))).
Proof.
intros. apply exchange1. apply contraction2. apply associativity2. apply (quantification2 _ _ _ (represent (S m))). apply repr_closed. unfold inductive_chain in H. fold inductive_chain in H. unfold "~>" in H.
simpl in H. simpl. repeat apply associativity1. apply exchange1. apply associativity1. apply associativity1. apply exchange4. apply associativity2. apply exchange3. apply associativity1. apply exchange4. apply associativity2. apply exchange2.
apply associativity1. apply exchange2. apply exchange4. apply exchange2. apply exchange4. apply associativity1. apply exchange4. apply exchange2. apply exchange4. rewrite sub_succ_self. auto. 
Qed.

Lemma induction_iterate_general : forall (A : formula) (n m : nat) (t : term) (alpha : ord), PA_omega_theorem (lor (lor (lor (inductive_chain A n (S m)) (substitution A n t)) (neg (substitution A n zero))) (neg (univ n (lor (neg A) (substitution A n (succ (var n))))))) 0 alpha -> PA_omega_theorem (lor (lor (lor (inductive_chain A n m) (substitution A n t)) (neg (substitution A n zero))) (neg (univ n (lor (neg A) (substitution A n (succ (var n))))))) 0 (ord_succ alpha).
Proof.
intros. apply exchange1. apply contraction2. apply associativity2. apply (quantification2 _ _ _ (represent (S m))). apply repr_closed. unfold inductive_chain in H. fold inductive_chain in H. unfold "~>" in H.
simpl in H. simpl. repeat apply associativity1. apply exchange1. apply associativity1. apply associativity1. apply exchange4. apply associativity2. apply exchange3. apply associativity1. apply exchange4. apply associativity2. apply exchange2.
apply associativity1. apply exchange2. apply exchange4. apply exchange2. apply exchange4. apply associativity1. apply exchange4. apply exchange2. apply exchange4. rewrite sub_succ_self. auto.
Qed.

Lemma induction_terminate : forall (A : formula) (n m : nat) (t : term) (alpha : ord), PA_omega_theorem (lor (lor (lor (inductive_chain A n (S m)) (substitution A n t)) (neg (substitution A n zero))) (neg (univ n (lor (neg A) (substitution A n (succ (var n))))))) 0 alpha -> PA_omega_theorem (lor (lor (lor (inductive_chain A n 0) (substitution A n t)) (neg (substitution A n zero))) (neg (univ n (lor (neg A) (substitution A n (succ (var n))))))) 0 (ord_add alpha (nat_ord (S m))).
Proof.
intros A n m. induction m; intros. 
- rewrite ord_add_succ_nat_succ_add. rewrite ord_add_zero. apply (induction_iterate_general _ _ _ _ _ H). apply (ord_nf _ _ _ H).
- pose proof (IHm _ _ (induction_iterate_general _ _ _ _ _ H)). rewrite ord_add_succ_nat_succ_add. auto. apply (ord_nf _ _ _ H).
Qed.

Lemma induction_final : forall (A : formula) (n m : nat) (t : term) (alpha : ord), PA_omega_theorem (lor (lor (lor (inductive_chain A n (S m)) (substitution A n t)) (neg (substitution A n zero))) (neg (univ n (lor (neg A) (substitution A n (succ (var n))))))) 0 alpha -> PA_omega_theorem (lor (lor (substitution A n t) (neg (substitution A n zero))) (neg (univ n (lor (neg A) (substitution A n (succ (var n))))))) 0 (ord_succ (ord_add alpha (nat_ord (S m)))).
Proof.
intros. pose proof (induction_terminate _ _ _ _ _ H). unfold inductive_chain in H0. unfold "~>" in H0. apply exchange1. apply contraction2. apply associativity2. apply (quantification2 _ _ _ (represent 0)). apply repr_closed. simpl.
rewrite sub_succ_self. apply associativity1. apply associativity1. apply exchange4. apply exchange2. auto.
Qed.

Lemma induction_aux : forall A n m, free_list A = [n] -> PA_omega_theorem (lor (lor (substitution A n (represent m)) (neg (substitution A n zero))) (neg (univ n (lor (neg A) (substitution A n (succ (var n))))))) 0 (w_tower (S (S (S (num_conn A + num_conn A))))).
Proof.
intros. pose proof (inductive_implication_theorem _ _  m H). apply (ord_incr _ _  (ord_succ (ord_add (ord_succ (ord_succ (w_tower (S (S (num_conn A + num_conn A)))))) (nat_ord (S m))))).
- destruct m.
  + apply exchange1. apply weakening; auto. simpl. case (closed A) eqn:X; auto.
    * rewrite closed_free_list in H; auto. inversion H.
    * simpl. rewrite H. rewrite (free_list_sub_self_eq _ _ (var n)); auto. simpl. rewrite eq_nat_refl. auto.
    * apply exchange1. apply (ord_incr _ _ (ord_succ (w_tower (num_conn A + num_conn A)))). rewrite <- (num_conn_sub _ n zero). apply LEM. apply closed_univ_sub. simpl. rewrite H. rewrite eq_nat_refl. destruct (closed A); auto. auto. rewrite ord_add_one_succ. apply ord_lt_succ. simpl. apply (lt_trans _ _ _ (omega_exp_incr _)). apply head_lt. apply ord_lt_self. repeat apply ord_succ_nf. apply w_tower_nf. apply nf_add. repeat apply ord_succ_nf. apply w_tower_nf. apply nf_nat. 
  + unfold inductive_implication in H0. unfold represent in H0. fold represent in H0. apply induction_final. auto. unfold inductive_chain. fold inductive_chain. apply associativity2. apply associativity2. apply associativity2. apply exchange3. apply associativity1. apply exchange4. apply associativity2. apply exchange3. apply weakening.
    * simpl. repeat rewrite closed_univ_sub; auto; try apply repr_closed; simpl; rewrite H; rewrite eq_nat_refl; destruct (closed A); auto.
    * repeat apply associativity1. apply exchange1. apply weakening; auto. simpl. rewrite (free_list_sub_self _ _ (var n)). rewrite H. simpl. rewrite eq_nat_refl. case (closed A); case (closed (substitution A n (succ (var n)))); auto. rewrite H. simpl. rewrite eq_nat_refl. auto.
- simpl. apply head_lt. apply ord_lt_self.
- apply w_tower_nf. 
Qed.

Lemma induction_aux' : forall A n m, closed A = true -> PA_omega_theorem (lor (substitution A n (represent m)) (lor (neg (substitution A n zero)) (neg (univ n (lor (neg A) (substitution A n (succ (var n)))))))) 0 (w_tower (S (S (S (num_conn A + num_conn A))))).
Proof.
intros. pose proof (inductive_implication_theorem' _ n m H). apply (ord_incr _ _  (ord_succ (ord_add (ord_succ (ord_succ (w_tower (S (S (num_conn A + num_conn A)))))) (nat_ord (S m))))).
- destruct m.
  + apply exchange1. apply exchange3. apply associativity2. apply weakening; auto. simpl. rewrite closed_subst_eq; auto. rewrite H. simpl. auto. unfold inductive_implication in H0. repeat rewrite closed_subst_eq; auto. rewrite closed_subst_eq in H0; auto. rewrite ord_add_one_succ. apply exchange1. apply (ord_incr _ _ _ _ H0). simpl. apply tail_lt. apply zero_lt. repeat apply ord_succ_nf. apply w_tower_nf. repeat apply ord_succ_nf. apply w_tower_nf.
  + repeat rewrite closed_subst_eq; auto. apply associativity1. apply exchange1. apply weakening. simpl. rewrite H. simpl. auto. apply exchange1. apply (ord_incr _ _ _ _ (LEM _ H)). apply (lt_trans _ _ _ (w_tower_succ _)). simpl. apply ord_lt_self. apply nf_add. repeat apply ord_succ_nf. apply w_tower_nf. apply nf_nat.
-  simpl. apply head_lt. apply ord_lt_self.
- apply w_tower_nf. 
Qed.

Lemma PA_omega_to_PA : forall A, closed A = true -> Peano_Theorems A -> {d : nat & {alpha : ord & PA_omega_theorem A d alpha}}.
Proof.
intros. induction H0.
- inversion H. apply and_bool_prop in H1. destruct H1. apply and_bool_prop in H1. destruct H1. clear H2. pose (LEM A H0). exists 0. exists (ord_succ (ord_succ (w_tower (num_conn A + num_conn A)))). unfold "~>".
  apply associativity1. apply exchange2. apply exchange1. apply weakening. auto. auto.
- inversion H. apply and_bool_prop in H1. destruct H1. clear H1. apply and_bool_prop in H0. destruct H0. apply and_bool_prop in H1. destruct H1. unfold "~>". exists (max (max 0 0) (num_conn (neg B))). exists (ord_succ (ord_max (ord_succ (w_tower (num_conn (lor (neg A) B) + num_conn (lor (neg A) B)))) ((ord_succ (w_tower (num_conn (lor (neg A) (lor (neg B) C)) + num_conn (lor (neg A) (lor (neg B) C)))))))).
  assert (closed (lor (neg A) B) = true). simpl; try rewrite H0,H1; auto. pose proof (LEM _ H3).
  assert (closed (lor (neg A) (lor (neg B) C)) = true). simpl; try rewrite H0,H1,H2; auto. pose proof (LEM _ H5). 
  apply associativity1. apply associativity1. apply exchange2. apply exchange3. apply exchange2. apply exchange3. apply exchange1. apply exchange3. apply exchange2.
  apply exchange3. apply exchange4. apply associativity2. apply associativity2. apply contraction2. apply associativity1. apply exchange4. apply exchange2. apply associativity2. apply (cut3 _ B).
  + apply exchange2. apply exchange1. auto. 
  + apply exchange1. apply exchange4. apply exchange2. apply exchange4. apply exchange3. apply associativity2. apply exchange1. apply associativity2. apply exchange3. apply exchange1. apply associativity2. auto. 
- inversion H. apply and_bool_prop in H1. destruct H1. clear H1. apply and_bool_prop in H0. destruct H0. unfold "~>". exists (max 0 (max 0 0)). exists (ord_succ (ord_max (ord_succ (ord_succ (ord_succ (w_tower (num_conn (A) + num_conn (A)))))) ((ord_succ (ord_max (ord_succ (ord_succ (ord_succ (w_tower (num_conn A + num_conn A))))) (ord_succ (ord_succ (w_tower (num_conn (neg B) + num_conn (neg B)))))))))). apply demorgan2.
  + apply associativity1. apply exchange2. apply exchange1. apply weakening. simpl. rewrite H0. rewrite H1. auto. apply negation2. apply LEM. auto.
  + apply exchange1. apply associativity2. apply demorgan2.
    * apply negation2. apply associativity1. apply exchange1. apply weakening. simpl. auto. apply LEM. auto.
    * apply associativity1. apply exchange3. apply associativity2. apply weakening. auto. apply exchange1. apply LEM. auto.
- inversion H. apply and_bool_prop in H1. destruct H1. exists 0. exists (ord_succ (ord_succ (w_tower (num_conn (substitution A n t) + num_conn (substitution A n t))))). apply (quantification2 _ _ _ t). auto. apply LEM. auto.
- unfold "~>". exists 0. exists (cons (ord_succ (ord_succ (w_tower (num_conn (lor (neg A) B) + num_conn (lor (neg A) B))))) 0 Zero). apply associativity1. apply exchange1. apply w_rule2. intros. apply exchange1. apply associativity2. apply (quantification2 _ _ _ (represent m)). apply repr_closed.
  unfold substitution. fold substitution. rewrite closed_subst_eq_aux; auto. assert (num_conn (lor (neg A) B) = num_conn (lor (neg A) (substitution B n (represent m)))). simpl. rewrite num_conn_sub. auto. rewrite H0. apply LEM. 
  unfold "~>" in H. apply closed_lor in H. destruct H. apply closed_lor in H1. destruct H1. simpl. simpl in H1. rewrite H1. simpl. apply closed_univ_sub_repr. auto.  
- 
admit.
- assert (closed A = false). case (closed A) eqn:X; auto. rewrite (closed_free_list _ X) in e. inversion e. assert ((free_list A) = [n]). inversion H. rewrite H1 in H3. destruct (free_list A). inversion e. apply and_bool_prop in H3. destruct H3. apply nat_eq_decid in H2. destruct H2. apply eq_list_decid in H3. rewrite H3. auto.
  exists 0. exists (cons Zero 0 Zero). apply w_rule1. intros. admit. 
- case (correct_a (equ t s)) eqn:X. 
  + unfold "~>". unfold "~>" in H. apply closed_lor in H. destruct H. apply closed_lor in H0. destruct H0. inversion H1. apply and_bool_prop in H3. destruct H3. pose (atom (equ (var 0) r)).
    assert ((substitution f 0 t) = (atom (equ t r))). simpl. rewrite closed_subst_eq_t; auto. assert ((substitution f 0 s) = (atom (equ s r))). simpl. rewrite closed_subst_eq_t; auto.
    exists 0. exists (ord_succ (ord_succ (w_tower (num_conn (atom (equ s t)))))). apply weakening. apply correct_closed. auto. rewrite <- H4. rewrite <- H5. apply LEM_term.
    unfold correct_a in *. unfold correctness in *. destruct (correct_eval _ _ X). destruct (eval s). inversion H7. destruct (eval t). inversion H6. case (eq_nat (S n0) (S n)) eqn:Y. apply eq_nat_symm in Y. rewrite Y. auto. inversion X. simpl. rewrite closed_free_list_t; auto.
  + unfold "~>". apply closed_lor in H. destruct H. unfold closed in H. exists 0. exists (ord_succ Zero). apply exchange1. apply weakening. auto. apply axiom. simpl. destruct (correctness_decid _ H). rewrite e in X. inversion X. auto.
- case (correct_a (equ t s)) eqn:X. 
  + unfold "~>". apply closed_lor in H. destruct H. unfold closed in H. exists 0. exists (ord_succ Zero). apply weakening. auto. apply axiom. simpl.
    unfold correct_a in *. unfold correctness in *. destruct (correct_eval _ _ X). simpl. destruct (eval s). inversion H2. destruct (eval t). inversion H1. simpl. simpl in X. rewrite X. auto.
  + unfold "~>". apply closed_lor in H. destruct H. unfold closed in H. exists 0. exists (ord_succ Zero). apply exchange1. apply weakening. auto. apply axiom. simpl. destruct (correctness_decid _ H). rewrite e in X. inversion X. auto.
- exists 0. exists Zero. apply axiom. simpl. destruct (correctness_decid _ H); auto. unfold correct_a in *. unfold correctness in *. simpl in *. destruct (eval t); inversion e.
- case (correct_a (equ t s)) eqn:X. 
  + unfold "~>". apply closed_lor in H. destruct H. unfold closed in H. exists 0. exists (ord_succ Zero). apply weakening. auto. apply axiom. simpl.
    unfold correct_a in *. unfold correctness in *. destruct (correct_eval _ _ X). simpl. destruct (eval s). inversion H2. destruct (eval t). inversion H1. simpl. simpl in X. rewrite X. auto.
  + unfold "~>". apply closed_lor in H. destruct H. unfold closed in H. exists 0. exists (ord_succ Zero). apply exchange1. apply weakening. auto. apply axiom. simpl. destruct (correctness_decid _ H); auto.
    unfold correct_a in *. unfold correctness in *. simpl in *. destruct (eval t). inversion e. destruct (eval s). inversion e. simpl in *. rewrite X in e. inversion e.
- exists 0. exists Zero. apply axiom. simpl. destruct (correctness_decid _ H); auto. unfold incorrect_a in e. unfold correct_a. unfold correctness in *. simpl in *. destruct (eval t). inversion e. simpl in *. rewrite plus_n_0. rewrite eq_nat_refl. auto.
- exists 0. exists Zero. apply axiom. simpl. destruct (correctness_decid _ H); auto. unfold incorrect_a in e. unfold correct_a. unfold correctness in *. simpl in *. destruct (eval t). inversion e. destruct (eval s). inversion e. simpl in *. rewrite plus_n_Sm. rewrite eq_nat_refl. auto.
- exists 0. exists Zero. apply axiom. simpl. destruct (correctness_decid _ H); auto. unfold incorrect_a in e. unfold correct_a. unfold correctness in *. simpl in *. destruct (eval t). inversion e. simpl in *. rewrite mult_0_r. rewrite eq_nat_refl. auto.
- exists 0. exists Zero. apply axiom. simpl. destruct (correctness_decid _ H); auto. unfold incorrect_a in e. unfold correct_a. unfold correctness in *. simpl in *. destruct (eval t). inversion e. destruct (eval s). inversion e. assert ((S (n * S n0)) = (S (n * n0 + n))). lia. rewrite H0. rewrite eq_nat_refl. auto.
- case (closed A) eqn:X.
  + unfold "~>". exists 0. exists (cons (w_tower (S (S (S (num_conn A + num_conn A))))) 0 Zero). apply associativity1. apply exchange1. apply w_rule2. intros. apply induction_aux'. auto.
  + assert ((free_list A) = [n]). unfold "~>" in H. apply closed_lor in H. destruct H. apply closed_lor in H0. destruct H0. simpl in H1. rewrite X in H1. destruct (free_list A). inversion H1. apply and_bool_prop in H1. destruct H1. apply nat_eq_decid in H1. destruct H1. apply eq_list_decid in H2. rewrite H2. auto.
    unfold "~>". exists 0. exists (cons (w_tower (S (S (S (num_conn A + num_conn A))))) 0 Zero). apply associativity1. apply exchange1. apply w_rule2. intros. apply associativity1. apply induction_aux. auto.
Admitted.

Lemma PA_omega_to_PA_closed : forall A t, closed_t t = true -> Peano_Theorems A -> {d : nat & {alpha : ord & PA_omega_theorem (closure A t) d alpha}}.
Proof.
intros. induction H0.
- pose proof (closure_closed A _ H).
inversion H. apply and_bool_prop in H1. destruct H1. apply and_bool_prop in H1. destruct H1. clear H2. pose (LEM A H0). exists 0. exists (ord_succ (ord_succ (w_tower (num_conn A + num_conn A)))). unfold "~>".
  apply associativity1. apply exchange2. apply exchange1. apply weakening. auto. auto.
- inversion H. apply and_bool_prop in H1. destruct H1. clear H1. apply and_bool_prop in H0. destruct H0. apply and_bool_prop in H1. destruct H1. unfold "~>". exists (max (max 0 0) (num_conn (neg B))). exists (ord_succ (ord_max (ord_succ (w_tower (num_conn (lor (neg A) B) + num_conn (lor (neg A) B)))) ((ord_succ (w_tower (num_conn (lor (neg A) (lor (neg B) C)) + num_conn (lor (neg A) (lor (neg B) C)))))))).
  assert (closed (lor (neg A) B) = true). simpl; try rewrite H0,H1; auto. pose proof (LEM _ H3).
  assert (closed (lor (neg A) (lor (neg B) C)) = true). simpl; try rewrite H0,H1,H2; auto. pose proof (LEM _ H5). 
  apply associativity1. apply associativity1. apply exchange2. apply exchange3. apply exchange2. apply exchange3. apply exchange1. apply exchange3. apply exchange2.
  apply exchange3. apply exchange4. apply associativity2. apply associativity2. apply contraction2. apply associativity1. apply exchange4. apply exchange2. apply associativity2. apply (cut3 _ B).
  + apply exchange2. apply exchange1. auto. 
  + apply exchange1. apply exchange4. apply exchange2. apply exchange4. apply exchange3. apply associativity2. apply exchange1. apply associativity2. apply exchange3. apply exchange1. apply associativity2. auto. 
- inversion H. apply and_bool_prop in H1. destruct H1. clear H1. apply and_bool_prop in H0. destruct H0. unfold "~>". exists (max 0 (max 0 0)). exists (ord_succ (ord_max (ord_succ (ord_succ (ord_succ (w_tower (num_conn (A) + num_conn (A)))))) ((ord_succ (ord_max (ord_succ (ord_succ (ord_succ (w_tower (num_conn A + num_conn A))))) (ord_succ (ord_succ (w_tower (num_conn (neg B) + num_conn (neg B)))))))))). apply demorgan2.
  + apply associativity1. apply exchange2. apply exchange1. apply weakening. simpl. rewrite H0. rewrite H1. auto. apply negation2. apply LEM. auto.
  + apply exchange1. apply associativity2. apply demorgan2.
    * apply negation2. apply associativity1. apply exchange1. apply weakening. simpl. auto. apply LEM. auto.
    * apply associativity1. apply exchange3. apply associativity2. apply weakening. auto. apply exchange1. apply LEM. auto.
- inversion H. apply and_bool_prop in H1. destruct H1. exists 0. exists (ord_succ (ord_succ (w_tower (num_conn (substitution A n t) + num_conn (substitution A n t))))). apply (quantification2 _ _ _ t). auto. apply LEM. auto.
- unfold "~>". exists 0. exists (cons (ord_succ (ord_succ (w_tower (num_conn (lor (neg A) B) + num_conn (lor (neg A) B))))) 0 Zero). apply associativity1. apply exchange1. apply w_rule2. intros. apply exchange1. apply associativity2. apply (quantification2 _ _ _ (represent m)). apply repr_closed.
  unfold substitution. fold substitution. rewrite closed_subst_eq_aux; auto. assert (num_conn (lor (neg A) B) = num_conn (lor (neg A) (substitution B n (represent m)))). simpl. rewrite num_conn_sub. auto. rewrite H0. apply LEM. 
  unfold "~>" in H. apply closed_lor in H. destruct H. apply closed_lor in H1. destruct H1. simpl. simpl in H1. rewrite H1. simpl. apply closed_univ_sub_repr. auto.  
- 
admit.
- assert (closed A = false). case (closed A) eqn:X; auto. rewrite (closed_free_list _ X) in e. inversion e. assert ((free_list A) = [n]). inversion H. rewrite H1 in H3. destruct (free_list A). inversion e. apply and_bool_prop in H3. destruct H3. apply nat_eq_decid in H2. destruct H2. apply eq_list_decid in H3. rewrite H3. auto.
  exists 0. exists (cons Zero 0 Zero). apply w_rule1. intros. admit. 
- case (correct_a (equ t s)) eqn:X. 
  + unfold "~>". unfold "~>" in H. apply closed_lor in H. destruct H. apply closed_lor in H0. destruct H0. inversion H1. apply and_bool_prop in H3. destruct H3. pose (atom (equ (var 0) r)).
    assert ((substitution f 0 t) = (atom (equ t r))). simpl. rewrite closed_subst_eq_t; auto. assert ((substitution f 0 s) = (atom (equ s r))). simpl. rewrite closed_subst_eq_t; auto.
    exists 0. exists (ord_succ (ord_succ (w_tower (num_conn (atom (equ s t)))))). apply weakening. apply correct_closed. auto. rewrite <- H4. rewrite <- H5. apply LEM_term.
    unfold correct_a in *. unfold correctness in *. destruct (correct_eval _ _ X). destruct (eval s). inversion H7. destruct (eval t). inversion H6. case (eq_nat (S n0) (S n)) eqn:Y. apply eq_nat_symm in Y. rewrite Y. auto. inversion X. simpl. rewrite closed_free_list_t; auto.
  + unfold "~>". apply closed_lor in H. destruct H. unfold closed in H. exists 0. exists (ord_succ Zero). apply exchange1. apply weakening. auto. apply axiom. simpl. destruct (correctness_decid _ H). rewrite e in X. inversion X. auto.
- case (correct_a (equ t s)) eqn:X. 
  + unfold "~>". apply closed_lor in H. destruct H. unfold closed in H. exists 0. exists (ord_succ Zero). apply weakening. auto. apply axiom. simpl.
    unfold correct_a in *. unfold correctness in *. destruct (correct_eval _ _ X). simpl. destruct (eval s). inversion H2. destruct (eval t). inversion H1. simpl. simpl in X. rewrite X. auto.
  + unfold "~>". apply closed_lor in H. destruct H. unfold closed in H. exists 0. exists (ord_succ Zero). apply exchange1. apply weakening. auto. apply axiom. simpl. destruct (correctness_decid _ H). rewrite e in X. inversion X. auto.
- exists 0. exists Zero. apply axiom. simpl. destruct (correctness_decid _ H); auto. unfold correct_a in *. unfold correctness in *. simpl in *. destruct (eval t); inversion e.
- case (correct_a (equ t s)) eqn:X. 
  + unfold "~>". apply closed_lor in H. destruct H. unfold closed in H. exists 0. exists (ord_succ Zero). apply weakening. auto. apply axiom. simpl.
    unfold correct_a in *. unfold correctness in *. destruct (correct_eval _ _ X). simpl. destruct (eval s). inversion H2. destruct (eval t). inversion H1. simpl. simpl in X. rewrite X. auto.
  + unfold "~>". apply closed_lor in H. destruct H. unfold closed in H. exists 0. exists (ord_succ Zero). apply exchange1. apply weakening. auto. apply axiom. simpl. destruct (correctness_decid _ H); auto.
    unfold correct_a in *. unfold correctness in *. simpl in *. destruct (eval t). inversion e. destruct (eval s). inversion e. simpl in *. rewrite X in e. inversion e.
- exists 0. exists Zero. apply axiom. simpl. destruct (correctness_decid _ H); auto. unfold incorrect_a in e. unfold correct_a. unfold correctness in *. simpl in *. destruct (eval t). inversion e. simpl in *. rewrite plus_n_0. rewrite eq_nat_refl. auto.
- exists 0. exists Zero. apply axiom. simpl. destruct (correctness_decid _ H); auto. unfold incorrect_a in e. unfold correct_a. unfold correctness in *. simpl in *. destruct (eval t). inversion e. destruct (eval s). inversion e. simpl in *. rewrite plus_n_Sm. rewrite eq_nat_refl. auto.
- exists 0. exists Zero. apply axiom. simpl. destruct (correctness_decid _ H); auto. unfold incorrect_a in e. unfold correct_a. unfold correctness in *. simpl in *. destruct (eval t). inversion e. simpl in *. rewrite mult_0_r. rewrite eq_nat_refl. auto.
- exists 0. exists Zero. apply axiom. simpl. destruct (correctness_decid _ H); auto. unfold incorrect_a in e. unfold correct_a. unfold correctness in *. simpl in *. destruct (eval t). inversion e. destruct (eval s). inversion e. assert ((S (n * S n0)) = (S (n * n0 + n))). lia. rewrite H0. rewrite eq_nat_refl. auto.
- case (closed A) eqn:X.
  + unfold "~>". exists 0. exists (cons (w_tower (S (S (S (num_conn A + num_conn A))))) 0 Zero). apply associativity1. apply exchange1. apply w_rule2. intros. apply induction_aux'. auto.
  + assert ((free_list A) = [n]). unfold "~>" in H. apply closed_lor in H. destruct H. apply closed_lor in H0. destruct H0. simpl in H1. rewrite X in H1. destruct (free_list A). inversion H1. apply and_bool_prop in H1. destruct H1. apply nat_eq_decid in H1. destruct H1. apply eq_list_decid in H2. rewrite H2. auto.
    unfold "~>". exists 0. exists (cons (w_tower (S (S (S (num_conn A + num_conn A))))) 0 Zero). apply associativity1. apply exchange1. apply w_rule2. intros. apply associativity1. apply induction_aux. auto.
Admitted.