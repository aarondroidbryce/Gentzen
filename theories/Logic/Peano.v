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

Inductive Peano_Theorems_Base : formula -> nat -> ord -> Type :=
| FOL1 : forall (A B : formula), Peano_Theorems_Base (A ~> (B ~> A)) 0 (ord_succ (ord_succ (nat_ord (num_conn A + num_conn A))))
| FOL2 : forall (A B C : formula), Peano_Theorems_Base ((A ~> (B ~> C)) ~> ((A ~> B) ~> (A ~> C))) (num_conn (neg B)) (ord_succ (ord_max (ord_succ (nat_ord (num_conn (lor (neg A) B) + num_conn (lor (neg A) B)))) ((ord_succ (nat_ord (num_conn (lor (neg A) (lor (neg B) C)) + num_conn (lor (neg A) (lor (neg B) C))))))))
| FOL3 : forall (A B : formula), Peano_Theorems_Base ((neg A ~> neg B) ~> ((neg A ~> B) ~> A)) 0 (ord_succ (ord_max (ord_succ (ord_succ (ord_succ (nat_ord (num_conn (A) + num_conn (A)))))) ((ord_succ (ord_max (ord_succ (ord_succ (ord_succ (nat_ord (num_conn A + num_conn A))))) (ord_succ (ord_succ (nat_ord (num_conn (neg B) + num_conn (neg B))))))))))
| FOL4 : forall (A : formula) (n : nat) (t : term), closed_t t = true -> Peano_Theorems_Base (lor (neg(univ n A)) (substitution A n t)) 0 (ord_succ (ord_succ (nat_ord (num_conn (substitution A n t) + num_conn (substitution A n t)))))
| FOL5 : forall (A B : formula) (n : nat), member n (free_list A) = false -> Peano_Theorems_Base ((univ n (A ~> B)) ~> (A ~> (univ n B))) 0 (ord_succ (ord_succ (ord_succ (nat_ord (num_conn (lor (neg A) B) + num_conn (lor (neg A) B))))))
| MP : forall (A B : formula) (n m : nat) (alpha beta : ord), Peano_Theorems_Base (A ~> B) n alpha -> Peano_Theorems_Base A m beta -> Peano_Theorems_Base B (max (max m n) (num_conn (neg A))) (ord_succ (ord_succ (ord_max beta alpha)))
| UG : forall (A : formula) (n m : nat) (alpha : ord), Peano_Theorems_Base A m alpha -> Peano_Theorems_Base (univ n A) m (ord_succ alpha) 
| equ_trans : forall (t s r : term), Peano_Theorems_Base  ((t # s) ~> ((s # r) ~> (t # r))) 0 (ord_succ (ord_succ (nat_ord (num_conn (atom (equ s t))))))
| equ_succ : forall (t s : term),  Peano_Theorems_Base ((t # s) ~> ((succ t) # (succ s))) 0 (ord_succ Zero)
| non_zero : forall (t : term), Peano_Theorems_Base (neg (zero # (succ t))) 0 Zero
| succ_equ : forall (t s : term),  Peano_Theorems_Base ((succ t # succ s) ~> (t # s)) 0 (ord_succ Zero)
| pl0 : forall (t : term), Peano_Theorems_Base ((plus t zero) # t) 0 Zero
| plS : forall (t s : term), Peano_Theorems_Base ((plus t (succ s)) # (succ (plus t s))) 0 Zero
| ml0 : forall (t : term), Peano_Theorems_Base ((times t zero) # zero) 0 Zero
| mlS : forall (t s : term), Peano_Theorems_Base ((times t (succ s)) # (plus (times t s) t)) 0 Zero
| induct : forall (A : formula) (n : nat), Peano_Theorems_Base (substitution A n zero ~> ((univ n (A ~> (substitution A n (succ (var n))))) ~> (univ n A))) (num_conn A + 1) (ord_succ (ord_succ (cons (nat_ord 1) 1 Zero))).

Inductive Peano_Theorems_Implication : formula -> nat -> ord -> Type :=
| I_FOL1 : forall (A B : formula), Peano_Theorems_Implication (A ~> (B ~> A)) 0 (ord_succ (ord_succ (nat_ord (num_conn A + num_conn A))))
| I_FOL2 : forall (A B C : formula), Peano_Theorems_Implication ((A ~> (B ~> C)) ~> ((A ~> B) ~> (A ~> C))) (num_conn (neg B)) (ord_succ (ord_max (ord_succ (nat_ord (num_conn (lor (neg A) B) + num_conn (lor (neg A) B)))) ((ord_succ (nat_ord (num_conn (lor (neg A) (lor (neg B) C)) + num_conn (lor (neg A) (lor (neg B) C))))))))
| I_FOL3 : forall (A B : formula), Peano_Theorems_Implication ((neg A ~> neg B) ~> ((neg A ~> B) ~> A)) 0 (ord_succ (ord_max (ord_succ (ord_succ (ord_succ (nat_ord (num_conn (A) + num_conn (A)))))) ((ord_succ (ord_max (ord_succ (ord_succ (ord_succ (nat_ord (num_conn A + num_conn A))))) (ord_succ (ord_succ (nat_ord (num_conn (neg B) + num_conn (neg B))))))))))
| I_FOL4 : forall (A : formula) (n : nat) (t : term), closed_t t = true -> Peano_Theorems_Implication (lor (neg(univ n A)) (substitution A n t)) 0 (ord_succ (ord_succ (nat_ord (num_conn (substitution A n t) + num_conn (substitution A n t)))))
| I_FOL5 : forall (A B : formula) (n : nat), member n (free_list A) = false -> Peano_Theorems_Implication ((univ n (A ~> B)) ~> (A ~> (univ n B))) 0 (ord_succ (ord_succ (ord_succ (nat_ord (num_conn (lor (neg A) B) + num_conn (lor (neg A) B))))))
| I_MP : forall (A B : formula) (n m : nat) (alpha beta : ord), Peano_Theorems_Implication (A ~> B) n alpha -> Peano_Theorems_Implication A m beta -> Peano_Theorems_Implication B (max (max m n) (num_conn (neg A))) (ord_succ (ord_succ (ord_max beta alpha)))
| I_UG : forall (A : formula) (n m : nat) (alpha : ord), Peano_Theorems_Implication A m alpha -> (forall t, closed_t t = true -> Peano_Theorems_Implication (substitution A n t) m alpha) -> Peano_Theorems_Implication (univ n A) m (ord_succ alpha) 
| I_equ_trans : forall (t s r : term), Peano_Theorems_Implication  ((t # s) ~> ((s # r) ~> (t # r))) 0 (ord_succ (ord_succ (nat_ord (num_conn (atom (equ s t))))))
| I_equ_succ : forall (t s : term),  Peano_Theorems_Implication ((t # s) ~> ((succ t) # (succ s))) 0 (ord_succ Zero)
| I_non_zero : forall (t : term), Peano_Theorems_Implication (neg (zero # (succ t))) 0 Zero
| I_succ_equ : forall (t s : term),  Peano_Theorems_Implication ((succ t # succ s) ~> (t # s)) 0 (ord_succ Zero)
| I_pl0 : forall (t : term), Peano_Theorems_Implication ((plus t zero) # t) 0 Zero
| I_plS : forall (t s : term), Peano_Theorems_Implication ((plus t (succ s)) # (succ (plus t s))) 0 Zero
| I_ml0 : forall (t : term), Peano_Theorems_Implication ((times t zero) # zero) 0 Zero
| I_mlS : forall (t s : term), Peano_Theorems_Implication ((times t (succ s)) # (plus (times t s) t)) 0 Zero
| I_induct : forall (A : formula) (n : nat), Peano_Theorems_Implication (substitution A n zero ~> ((univ n (A ~> (substitution A n (succ (var n))))) ~> (univ n A))) (num_conn A + 1) (ord_succ (ord_succ (cons (nat_ord 1) 1 Zero))).

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

Lemma inductive_implication_theorem_aux : forall A n m, free_list A = [n] -> PA_omega_theorem (inductive_implication A n m) 0 (ord_add (nat_ord (S (num_conn A + num_conn A))) (nat_ord (3 * (S m)))).
intros. induction m.
- apply (ord_incr _ _ (ord_succ (nat_ord (num_conn A + num_conn A)))).
  + apply exchange1. assert (num_conn A = num_conn (substitution A n zero)). rewrite num_conn_sub. auto. rewrite H0. apply LEM. rewrite closed_univ_sub; auto. simpl. case (closed A); auto. rewrite H. rewrite eq_nat_refl. auto.
  + rewrite <- ord_add_nat. rewrite ord_succ_nat. apply nat_ord_lt. lia.
  + apply nf_add; apply nf_nat.
- assert ((ord_add (nat_ord (S (num_conn A + num_conn A))) (nat_ord (3 * S (S m)))) = (ord_succ (ord_max (ord_succ (ord_succ (ord_add (nat_ord (S (num_conn A + num_conn A))) (nat_ord (3 * (S m)))))) (ord_succ (ord_succ (nat_ord (num_conn A + num_conn A))))))).
  { repeat rewrite <- ord_add_nat. repeat rewrite ord_max_succ_succ. rewrite ord_max_lem2. repeat rewrite ord_succ_nat. unfold mul. simpl. rewrite plus_n_0. repeat rewrite plus_n_Sm. auto. apply ltb_asymm. apply ord_lt_ltb. apply nat_ord_lt. lia. }
  rewrite H0. destruct m.
  + unfold inductive_implication. unfold inductive_chain. unfold "~>". apply associativity2. assert (max 0 0 = 0). lia. destruct H1. apply demorgan2. 
    *  apply negation2. apply associativity1. apply exchange3. apply associativity2. apply weakening. apply closed_univ_sub_repr. simpl. rewrite H. rewrite eq_nat_refl. destruct (closed A); auto. auto.
    *  apply associativity1. apply exchange1. apply weakening. apply closed_univ_sub; auto. simpl. rewrite H. rewrite eq_nat_refl. destruct (closed A); auto. simpl. assert (num_conn A = num_conn (substitution A n (succ zero))). rewrite num_conn_sub. auto. rewrite H1. apply LEM. rewrite closed_univ_sub; simpl; auto. rewrite H. rewrite eq_nat_refl. destruct (closed A); auto. 
  + unfold inductive_implication in *. unfold inductive_chain. fold inductive_chain. unfold "~>". apply exchange4. apply exchange2. apply exchange1. assert (max 0 0 = 0). lia. destruct H1. apply demorgan2.
    * apply negation2. apply exchange1. apply exchange2. apply exchange4. apply exchange2. apply exchange1. apply weakening. apply closed_univ_sub_repr. simpl. rewrite H. rewrite eq_nat_refl. destruct (closed A); auto. auto. 
    * apply exchange1. apply exchange4. apply exchange2. apply associativity2. apply weakening. simpl. rewrite ind_imp_closed; auto. apply closed_univ_sub; auto. simpl. rewrite H. rewrite eq_nat_refl. destruct (closed A); auto. simpl. assert (num_conn A = num_conn (substitution A n (succ (succ (represent m))))). rewrite num_conn_sub. auto. rewrite H1. apply LEM. rewrite closed_univ_sub; simpl; auto. rewrite H. rewrite eq_nat_refl. destruct (closed A); auto. apply repr_closed.
Qed.

Lemma inductive_implication_theorem_aux' : forall A n m, closed A = true -> PA_omega_theorem (inductive_implication A n m) 0 (ord_add (nat_ord (S (num_conn A + num_conn A))) (nat_ord (3 * (S m)))).
intros. induction m.
- apply (ord_incr _ _ (ord_succ (nat_ord (num_conn A + num_conn A)))).
  + apply exchange1. assert (num_conn A = num_conn (substitution A n zero)). rewrite num_conn_sub. auto. rewrite H0. apply LEM. rewrite closed_univ_sub; auto. simpl. rewrite H. auto.
  + rewrite <- ord_succ_nat. apply add_right_incr_corr. apply zero_lt.
  + apply nf_add; apply nf_nat.
- assert ((ord_add (nat_ord (S (num_conn A + num_conn A))) (nat_ord (3 * S (S m)))) = (ord_succ (ord_max (ord_succ (ord_succ (ord_add (nat_ord (S (num_conn A + num_conn A))) (nat_ord (3 * (S m)))))) (ord_succ (ord_succ (nat_ord (num_conn A + num_conn A))))))).
  { repeat rewrite <- ord_add_nat. repeat rewrite ord_max_succ_succ. rewrite ord_max_lem2. repeat rewrite ord_succ_nat. unfold mul. simpl. rewrite plus_n_0. repeat rewrite plus_n_Sm. auto. apply ltb_asymm. apply ord_lt_ltb. apply nat_ord_lt. lia. }
  rewrite H0. destruct m.
  + unfold inductive_implication. unfold inductive_chain. unfold "~>". apply associativity2. assert (max 0 0 = 0). lia. destruct H1. apply demorgan2. 
    * apply negation2. apply associativity1. apply exchange3. apply associativity2. apply weakening. apply closed_univ_sub_repr. simpl. rewrite H. auto. auto.
    * apply associativity1. apply exchange1. apply weakening. apply closed_univ_sub; auto. simpl. rewrite H. auto. simpl. assert (num_conn A = num_conn (substitution A n (succ zero))). rewrite num_conn_sub. auto. rewrite H1. apply LEM. rewrite closed_univ_sub; simpl; auto. rewrite H. auto. 
  + unfold inductive_implication in *. unfold inductive_chain. fold inductive_chain. unfold "~>". apply exchange4. apply exchange2. apply exchange1. assert (max 0 0 = 0). lia. destruct H1. apply demorgan2.
    * apply negation2. apply exchange1. apply exchange2. apply exchange4. apply exchange2. apply exchange1. apply weakening. apply closed_univ_sub_repr. simpl. rewrite H. auto. auto. 
    * apply exchange1. apply exchange4. apply exchange2. apply associativity2. apply weakening. simpl. rewrite ind_imp_closed'; auto. apply closed_univ_sub; auto. simpl. rewrite H. auto. simpl. assert (num_conn A = num_conn (substitution A n (succ (succ (represent m))))). rewrite num_conn_sub. auto. rewrite H1. apply LEM. rewrite closed_univ_sub; simpl; auto. rewrite H. auto. apply repr_closed.
Qed.

Lemma inductive_implication_theorem : forall A n (c : c_term), free_list A = [n] -> PA_omega_theorem (inductive_implication A n (value c)) 0 (cons (nat_ord 1) 0 Zero).
intros. refine (ord_incr _ _ (ord_add (nat_ord (S (num_conn A + num_conn A))) (nat_ord (3 * (S (value c))))) _ _ _ (single_nf _ _ (nf_nat _))). apply inductive_implication_theorem_aux. auto.
repeat rewrite <- ord_add_nat. apply nat_lt_omega. apply zero_lt.
Qed.

Lemma inductive_implication_theorem' : forall A n (c : c_term), closed A = true -> PA_omega_theorem (inductive_implication A n (value c)) 0 (cons (nat_ord 1) 0 Zero).
intros. refine (ord_incr _ _ (ord_add (nat_ord (S (num_conn A + num_conn A))) (nat_ord (3 * (S (value c))))) _ _ _ (single_nf _ _ (nf_nat _))). apply inductive_implication_theorem_aux'. auto.
repeat rewrite <- ord_add_nat. apply nat_lt_omega. apply zero_lt.
Qed.

Lemma induction_iterate : forall (A : formula) (n m : nat) (t : term), PA_omega_theorem (lor (lor (lor (inductive_chain A n (S m)) (substitution A n t)) (neg (substitution A n zero))) (neg (univ n (lor (neg A) (substitution A n (succ (var n))))))) 0 (nat_ord (S (S (num_conn A + num_conn A)))) -> PA_omega_theorem (lor (lor (lor (inductive_chain A n m) (substitution A n t)) (neg (substitution A n zero))) (neg (univ n (lor (neg A) (substitution A n (succ (var n))))))) 0 (ord_succ (nat_ord (S (S (num_conn A + num_conn A))))).
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

Lemma induction_final : forall (A : formula) (n m : nat) (t : term) (alpha : ord),
    PA_omega_theorem (lor (lor (lor (inductive_chain A n (S m)) (substitution A n t)) (neg (substitution A n zero))) (neg (univ n (lor (neg A) (substitution A n (succ (var n))))))) 0 alpha ->
        PA_omega_theorem (lor (lor (substitution A n t) (neg (substitution A n zero))) (neg (univ n (lor (neg A) (substitution A n (succ (var n))))))) 0 (ord_succ (ord_add alpha (nat_ord (S m)))).
Proof.
intros. pose proof (induction_terminate _ _ _ _ _ H). unfold inductive_chain in H0. unfold "~>" in H0. apply exchange1. apply contraction2. apply associativity2. apply (quantification2 _ _ _ (represent 0)). apply repr_closed. simpl.
rewrite sub_succ_self. apply associativity1. apply associativity1. apply exchange4. apply exchange2. auto.
Qed.


Lemma induction_aux : forall A n (c : c_term), free_list A = [n] -> PA_omega_theorem (lor (lor (substitution A n (represent (value c))) (neg (substitution A n zero))) (neg (univ n (lor (neg A) (substitution A n (succ (var n))))))) 0 (cons (nat_ord 1) 1 Zero).
Proof.
intros. pose proof (inductive_implication_theorem _ _  c H). destruct (value c) eqn:V.
- apply (ord_incr _ _  (ord_succ (ord_add (ord_succ (ord_succ (nat_ord (S (S (num_conn A + num_conn A)))))) (nat_ord (S 0))))).
  +  apply exchange1. apply weakening; auto. simpl. case (closed A) eqn:X; auto.
    * rewrite closed_free_list in H; auto. inversion H.
    * simpl. rewrite H. rewrite (free_list_sub_self_eq _ _ (var n)); auto. simpl. rewrite eq_nat_refl. auto.
    * apply exchange1. apply (ord_incr _ _ (ord_succ (nat_ord (num_conn A + num_conn A)))). rewrite <- (num_conn_sub _ n zero). apply LEM. apply closed_univ_sub. simpl. rewrite H. rewrite eq_nat_refl. destruct (closed A); auto. auto. rewrite ord_add_one_succ. repeat rewrite ord_succ_nat. apply nat_ord_lt. lia. repeat apply ord_succ_nf. apply nf_nat. apply nf_add; repeat apply ord_succ_nf; apply nf_nat. 
  + simpl. apply head_lt. apply ord_lt_self.
  + apply single_nf. apply nf_nat.
- apply (ord_incr _ _  (ord_succ (ord_add (ord_succ (ord_succ (cons (nat_ord 1) 0 Zero))) (nat_ord (S n0))))).
  + unfold inductive_implication in *. unfold represent in *. fold represent in *. apply induction_final. unfold inductive_chain. fold inductive_chain. apply associativity2. apply associativity2. apply exchange2. apply exchange1. apply weakening.
    * simpl. repeat rewrite closed_univ_sub; auto; try apply repr_closed; simpl; rewrite H; rewrite eq_nat_refl; destruct (closed A); auto.
    * apply associativity1. apply associativity1. apply exchange1. apply weakening; auto. simpl. rewrite (free_list_sub_self _ _ (var n)). rewrite H. simpl. rewrite eq_nat_refl. case (closed A); case (closed (substitution A n (succ (var n)))); auto. rewrite H. simpl. rewrite eq_nat_refl. auto.
  + simpl. apply coeff_lt. lia.
  + apply single_nf. apply nf_nat. 
Qed.

Lemma induction_aux' : forall A n (c : c_term), closed A = true -> PA_omega_theorem (lor (substitution A n (projT1 c)) (lor (neg (substitution A n zero)) (neg (univ n (lor (neg A) (substitution A n (succ (var n)))))))) 0 (cons (nat_ord 1) 1 Zero).
Proof.
intros. pose proof (inductive_implication_theorem' _ n c H). apply (ord_incr _ _  (ord_succ (cons (nat_ord 1) 0 Zero))). 
- destruct (value c).
  + apply exchange1. apply exchange3. apply associativity2. apply weakening; auto. simpl. rewrite closed_subst_eq; auto. rewrite H. simpl. auto. unfold inductive_implication in H0. repeat rewrite closed_subst_eq; auto. rewrite closed_subst_eq in H0; auto. apply exchange1. auto.
  + repeat rewrite closed_subst_eq; auto. apply associativity1. apply exchange1. apply weakening. simpl. rewrite H. simpl. auto. apply exchange1. apply (ord_incr _ _ _ _ (LEM _ H)). rewrite ord_succ_nat. apply nat_lt_omega. apply zero_lt. apply single_nf. apply nf_nat.
-  apply coeff_lt. lia.
- apply single_nf. apply nf_nat. 
Qed.


Lemma PA_closed_PA_omega : forall A d alpha, Peano_Theorems_Implication A d alpha -> (forall t, closed_t t = true -> PA_omega_theorem (closure A t) d alpha).
Proof.
intros A d alpha H0. induction H0.
- intros. pose proof (closure_closed (A ~> (B ~> A)) _ H). unfold "~>" in *. rewrite closure_lor in *; auto. rewrite closure_lor in *; auto. inversion H0. apply and_bool_prop in H2. destruct H2. apply and_bool_prop in H2. destruct H2. clear H1. pose (LEM (closure A t) H3). unfold "~>".
  apply associativity1. apply exchange2. apply exchange1. apply weakening. auto. rewrite <- num_conn_closure_eq in p. rewrite closure_neg; auto.
- intros. pose proof (closure_closed ((A ~> (B ~> C)) ~> ((A ~> B) ~> (A ~> C))) _ H). unfold "~>" in *. rewrite closure_lor in *; auto. rewrite closure_neg in *; auto. rewrite closure_lor in *; auto. rewrite closure_lor in *; auto. rewrite closure_lor in *; auto. rewrite closure_lor in *; auto. rewrite closure_neg in *; auto. rewrite closure_neg in *; auto. rewrite closure_neg in *; auto. rewrite closure_lor in *; auto. rewrite closure_neg in *; auto.
  inversion H0. apply and_bool_prop in H2. destruct H2. apply and_bool_prop in H2. destruct H2. 
  pose proof (closure_closed (lor (neg A) B) _ H). pose proof (LEM _ H4).
  pose proof (closure_closed (lor (neg A) (lor (neg B) C)) _ H). pose proof (LEM _ H6).
  apply associativity1. apply associativity1. apply exchange2. apply exchange3. apply exchange2. apply exchange3. apply exchange1. apply exchange3. apply exchange2.
  apply exchange3. apply exchange4. apply associativity2. apply associativity2. apply contraction2. apply associativity1. apply exchange4. apply exchange2. apply associativity2. rewrite (num_conn_closure_eq _ t). rewrite (closure_neg B); auto. assert ((max (max 0 0) (num_conn (neg (closure B t)))) = num_conn (neg (closure B t))) as Z. auto. rewrite <- Z. apply (cut3 _ (closure B t)).
  + apply exchange2. apply exchange1. rewrite <- num_conn_closure_eq in H5. rewrite closure_lor in H5; auto. rewrite closure_neg in H5; auto.
  + apply exchange1. apply exchange4. apply exchange2. apply exchange4. apply exchange3. apply associativity2. apply exchange1. apply associativity2. apply exchange3. apply exchange1. apply associativity2.
    rewrite closure_lor in H7; auto. rewrite closure_lor in H7; auto. rewrite closure_neg in H7; auto. rewrite closure_neg in H7; auto.
    rewrite (num_conn_closure_eq _ t). rewrite closure_lor; auto. rewrite closure_lor; auto. rewrite closure_neg; auto. rewrite closure_neg; auto.
- intros. pose proof (closure_closed ((neg A ~> neg B) ~> ((neg A ~> B) ~> A)) _ H). unfold "~>" in *. rewrite closure_lor in *; auto. rewrite closure_lor in *; auto. rewrite closure_neg in *; auto. rewrite closure_neg in *; auto. rewrite closure_lor in *; auto. rewrite closure_lor in *; auto. rewrite closure_neg in *; auto. rewrite closure_neg in *; auto. rewrite closure_neg in *; auto.
  inversion H0. apply and_bool_prop in H2. destruct H2. clear H2. apply and_bool_prop in H1. destruct H1. assert (0 = max 0 (max 0 0)). auto. rewrite H3. apply demorgan2.
  + apply associativity1. apply exchange2. apply exchange1. apply weakening. simpl. rewrite H1. rewrite H2. auto. apply negation2. rewrite (num_conn_closure_eq _ t). apply LEM. auto.
  + apply exchange1. apply associativity2. apply demorgan2.
    * apply negation2. apply associativity1. apply exchange1. apply weakening. simpl. auto. rewrite (num_conn_closure_eq _ t). apply LEM. auto.
    * apply associativity1. apply exchange3. apply associativity2. apply weakening. auto. apply exchange1. rewrite (num_conn_closure_eq _ t). rewrite closure_neg; auto. apply LEM. auto.
- intros. rewrite closure_lor; auto. rewrite closure_neg; auto. rewrite closure_univ; auto. apply (quantification2 _ _ _ t). auto. rewrite (num_conn_closure_eq _ t0). rewrite <- (closure_subst _ t0); auto.  apply LEM.
  apply free_list_closed. apply (free_list_univ_sub _ _ _ _ e). apply closed_free_list. rewrite <- closure_univ; auto. rewrite closure_closed; auto.
- intros. unfold "~>". rewrite (num_conn_closure_eq _ t).
  rewrite closure_lor in *; auto. rewrite closure_lor in *; auto. rewrite closure_neg in *; auto. rewrite closure_neg in *; auto. rewrite closure_lor in *; auto.  rewrite closure_neg in *; auto. rewrite closure_univ in *; auto. rewrite closure_univ in *; auto.
  apply associativity1. apply exchange1. apply w_rule2. intros. apply exchange1. apply associativity2. apply (quantification2 _ _ _ t0); auto. rewrite (closure_subst (lor (neg A) B)); auto.
  + unfold substitution. fold substitution. rewrite closed_subst_eq_aux; auto. rewrite closure_subst; auto. rewrite closure_lor; auto. rewrite closure_neg; auto.
    assert (num_conn (lor (neg (closure A t)) (closure B t)) = num_conn (lor (neg (closure A t)) (closure (substitution B n t0) t))). simpl. repeat rewrite <- num_conn_closure_eq. rewrite num_conn_sub. auto.
    rewrite H1. apply LEM. simpl. rewrite closure_closed; auto. rewrite closure_closed; auto.
- intros. pose proof (IHPeano_Theorems_Implication2 _ H) as P1. pose proof (IHPeano_Theorems_Implication1 _ H) as P2.
  unfold "~>" in *. rewrite closure_lor in P2; auto. rewrite closure_neg in P2; auto. rewrite (num_conn_closure_eq _ t). rewrite closure_neg; auto. apply cut2; auto.
- intros. rewrite closure_univ; auto. apply w_rule1. intros. rewrite closure_subst; auto.
- intros. case (correct_a (equ (closure_t t t0) (closure_t s t0))) eqn:X. 
  + unfold "~>". rewrite closure_lor; auto. rewrite closure_lor; auto. rewrite closure_neg; auto. rewrite closure_neg; auto. pose (atom (equ (var 0) (closure_type_t r t0 (free_list_t r)))).
    assert (substitution f 0 (closure_t t t0) = closure (atom (equ t r)) t0). simpl. rewrite closure_type_equiv; auto. rewrite closed_subst_eq_t; auto. apply closure_closed_t. auto.
    assert (substitution f 0 (closure_t s t0) = closure (atom (equ s r)) t0). simpl. rewrite closure_type_equiv; auto. rewrite closed_subst_eq_t; auto. apply closure_closed_t. auto.
    apply weakening. rewrite <- closure_neg; auto. rewrite closure_closed; auto. rewrite <- H0. rewrite <- H1. apply LEM_term.
    unfold correct_a in *. unfold correctness in *. destruct (correct_eval _ _ X). destruct (eval (closure_t s t0)). inversion H3. destruct (eval (closure_t t t0)). inversion H2. case (eq_nat (S n0) (S n)) eqn:Y. apply eq_nat_symm in Y. rewrite Y. auto. inversion X. simpl. rewrite closed_free_list_t; auto. apply closure_closed_t. auto.
  + apply (ord_incr _ _ (ord_succ Zero)). unfold "~>". rewrite closure_lor; auto. rewrite closure_lor; auto. rewrite closure_neg; auto. rewrite closure_neg; auto. apply exchange1. apply weakening. simpl. rewrite closure_closed; auto. rewrite closure_closed; auto. apply axiom.
    simpl. destruct (correctness_decid (equ (closure_t t t0) (closure_t s t0))). simpl. rewrite closure_closed_t; auto. rewrite closure_closed_t; auto. rewrite e in X. inversion X. rewrite closure_type_equiv; auto.
    apply ord_lt_succ. apply zero_lt. apply ord_succ_nf. apply ord_succ_nf. apply nf_nat.
- intros. case (correct_a (equ (closure_t t t0) (closure_t s t0))) eqn:X. 
  + unfold "~>". rewrite closure_lor; auto. rewrite closure_neg; auto. 
    apply weakening. apply closure_closed; auto. apply axiom. rewrite closure_type_equiv; auto. simpl.
    unfold correct_a in *. unfold correctness in *. destruct (correct_eval _ _ X). rewrite closure_t_succ. rewrite closure_t_succ. simpl. destruct (eval (closure_t s t0)). inversion H1. destruct (eval (closure_t t t0)). inversion H0. simpl. simpl in X. rewrite X. auto.
  + unfold "~>". rewrite closure_lor; auto. rewrite closure_neg; auto. apply exchange1. apply weakening. apply closure_closed. auto. apply axiom. simpl. 
    destruct (correctness_decid (equ (closure_t t t0) (closure_t s t0))). simpl. rewrite closure_closed_t; auto. rewrite closure_closed_t; auto. rewrite e in X. inversion X. rewrite closure_type_equiv; auto.
- intros. apply axiom. simpl. rewrite closure_neg; auto. rewrite closure_type_equiv; auto. simpl. rewrite closure_closed_id_t; auto. destruct (correctness_decid (equ zero (closure_t (succ t) t0))); simpl; auto. rewrite closure_closed_t; auto. unfold correct_a in *. unfold correctness in *. rewrite closure_t_succ in *; auto. simpl in *. destruct (eval (closure_t t t0)); inversion e. 
- intros. case (correct_a (equ (closure_t t t0) (closure_t s t0))) eqn:X. 
  + unfold "~>". rewrite closure_lor; auto. rewrite closure_neg; auto. rewrite closure_type_equiv; auto. rewrite closure_type_equiv; auto. rewrite closure_t_succ. rewrite closure_t_succ. apply weakening. simpl. rewrite closure_closed_t; auto. rewrite closure_closed_t; auto. apply axiom. simpl. auto.
  + unfold "~>". rewrite closure_lor; auto. rewrite closure_neg; auto. rewrite closure_type_equiv; auto. rewrite closure_type_equiv; auto. rewrite closure_t_succ. rewrite closure_t_succ. apply exchange1. apply weakening. simpl. rewrite closure_closed_t; auto. rewrite closure_closed_t; auto. apply axiom. simpl.
    destruct (correctness_decid (equ (closure_t t t0) (closure_t s t0))); auto. simpl. rewrite closure_closed_t; auto. rewrite closure_closed_t; auto. rewrite X in e. inversion e.
    unfold incorrect_a in *. unfold correct_a in *. unfold correctness in *. simpl in *. destruct (eval (closure_t t t0)). inversion e. destruct (eval (closure_t s t0)). inversion e. simpl in *. case (eq_nat n n0) eqn:X1; inversion X. auto.
- intros. apply axiom. rewrite closure_type_equiv; auto. rewrite closure_t_plus; auto. simpl. rewrite (closure_closed_id_t zero); auto. destruct (correctness_decid (equ (plus (closure_t t t0) zero) (closure_t t t0))); simpl; auto. rewrite closure_closed_t; auto. unfold correct_a in *. unfold incorrect_a in *. unfold correctness in *. simpl in *. destruct (eval (closure_t t t0)); try rewrite plus_n_0 in *; inversion e. repeat rewrite eq_nat_refl. auto.
- intros. apply axiom. rewrite closure_type_equiv; auto. rewrite closure_t_plus; auto. simpl. rewrite closure_t_succ; auto. rewrite closure_t_succ; auto. rewrite closure_t_plus; auto. destruct (correctness_decid (equ (plus (closure_t t t0) (succ (closure_t s t0))) (succ (plus (closure_t t t0) (closure_t s t0))))); simpl; auto. repeat rewrite closure_closed_t; auto. unfold correct_a in *. unfold incorrect_a in *. unfold correctness in *. simpl in *. destruct (eval (closure_t t t0)); inversion e. destruct (eval (closure_t s t0)); inversion e. simpl in *. repeat rewrite plus_n_Sm. repeat rewrite eq_nat_refl. auto.
- intros. apply axiom. rewrite closure_type_equiv; auto. rewrite closure_t_times; auto. rewrite (closure_closed_id_t zero); auto. simpl. destruct (correctness_decid (equ (times (closure_t t t0) zero) zero)); simpl; auto. rewrite closure_closed_t; auto. unfold incorrect_a in e. unfold correct_a. unfold correctness in *. simpl in *. destruct (eval (closure_t t t0)). inversion e. simpl in *. rewrite mult_0_r. rewrite eq_nat_refl. auto.
- intros. apply axiom. rewrite closure_type_equiv; auto. rewrite closure_t_times; auto. rewrite closure_t_plus; auto. rewrite closure_t_times; auto. rewrite closure_t_succ; auto. simpl. destruct (correctness_decid (equ (times (closure_t t t0) (succ (closure_t s t0))) (plus (times (closure_t t t0) (closure_t s t0)) (closure_t t t0)))); simpl; auto. repeat rewrite closure_closed_t; auto. unfold incorrect_a in e. unfold correct_a. unfold correctness in *. simpl in *. destruct (eval (closure_t t t0)). inversion e. destruct (eval (closure_t s t0)). inversion e. assert ((S (n * S n0)) = (S (n * n0 + n))). lia. rewrite H0. rewrite eq_nat_refl. auto.
- intros. unfold "~>". repeat rewrite closure_lor; auto. repeat rewrite closure_neg; auto. repeat rewrite closure_univ; auto. rewrite <- closure_subst; auto. rewrite closure_type_lor; auto. rewrite closure_neg_list; auto. rewrite closure_type_sub_remove; auto. case (closed (closure_type A t (free_list (univ n A)))) eqn:X.
  + apply associativity1. apply exchange1. apply w_rule2. intros c Hc.
    assert ( (free_list (univ n (lor (neg A) (substitution A n (succ (var n)))))) = free_list (univ n A)).
    { simpl. case (member n (free_list A)) eqn:Y. rewrite free_list_sub_self; auto. rewrite remove_dups_concat_self. rewrite <- free_list_remove_dups. auto. rewrite closed_subst_eq_aux; auto. rewrite remove_dups_concat_self. rewrite <- free_list_remove_dups. auto. }
    rewrite H0. refine (ord_incr _ _ _ _ (deg_incr _ _ _ _ (induction_aux' _ _ (closing c Hc) X) _) _ _). lia. apply ord_succ_monot. apply ord_succ_nf. apply single_nf. apply nf_nat.
  + assert (free_list (closure_type A t (free_list (univ n A))) = [n]). simpl. destruct (free_list_univ_closure A _ n H); auto. apply free_list_closed in H0. rewrite H0 in X. inversion X.
    apply associativity1. apply exchange1. apply w_rule2. intros c Hc. apply associativity1.
    assert ( (free_list (univ n (lor (neg A) (substitution A n (succ (var n)))))) = free_list (univ n A)).
    { simpl. case (member n (free_list A)) eqn:Y. rewrite free_list_sub_self; auto. rewrite remove_dups_concat_self. rewrite <- free_list_remove_dups. auto. rewrite closed_subst_eq_aux; auto. rewrite remove_dups_concat_self. rewrite <- free_list_remove_dups. auto. }
    rewrite H1. pose proof (induction_aux _ _ (closing c Hc) H0). pose proof (LEM_term (closure_type A t (free_list (univ n A))) n _ _ (cterm_equiv_correct (closing c Hc)) H0). apply associativity2.
    apply exchange1. apply associativity1 in H2. apply exchange1 in H2.
    assert ((max (max 0 0) (num_conn (neg (substitution (closure_type A t (free_list (univ n A))) n (represent (value (closing c Hc))))))) = (num_conn A + 1)).
    { simpl. rewrite num_conn_sub. rewrite <- num_conn_closure_eq_list. rewrite plus_n_1. auto. }             
    assert ((ord_max (cons (nat_ord 1) 1 Zero) (ord_succ (nat_ord (num_conn (closure_type A t (free_list (univ n A))) + num_conn (closure_type A t (free_list (univ n A))))))) = (cons (nat_ord 1) 1 Zero)).
    { rewrite ord_max_lem2; auto. apply ltb_asymm. rewrite ord_succ_nat. refine (ord_ltb_trans _ (cons (nat_ord 1) 0 Zero) _ (ord_lt_ltb _ _ (nat_lt_omega _ _ (zero_lt _ _ _))) (ord_lt_ltb _ _ _)). apply coeff_lt. lia. }
    rewrite <- H4 at 1. rewrite <- H5. apply (cut3 _ _ _ _ _ _ _ H2 H3).
Qed.

Lemma PA_Base_equiv : forall (A : formula) (d n : nat) (alpha : ord) (t : term), closed_t t = true -> Peano_Theorems_Base A d alpha -> Peano_Theorems_Base (substitution A n t) d alpha.
Proof.
intros. induction H0.
- unfold "~>". rewrite <- (num_conn_sub _ n t). apply FOL1.
- unfold "~>". unfold substitution. fold substitution. unfold num_conn. fold num_conn. rewrite <- (num_conn_sub A n t). rewrite <- (num_conn_sub B n t). rewrite <- (num_conn_sub C n t). apply FOL2.
- unfold "~>". unfold substitution. fold substitution. unfold num_conn. fold num_conn. rewrite <- (num_conn_sub A n t). rewrite <- (num_conn_sub B n t). apply FOL3.
- unfold "~>". unfold substitution. fold substitution. unfold num_conn. fold num_conn. case (eq_nat n0 n) eqn:X.
  + apply nat_eq_decid in X. destruct X. rewrite closed_subst_eq_aux. apply FOL4; auto. rewrite subst_remove; auto. apply remove_not_member.
  + rewrite substitution_order; auto. rewrite num_conn_sub. rewrite <- (num_conn_sub A n t). rewrite <- (num_conn_sub (substitution A n t) n0 t0). apply FOL4; auto. apply eq_nat_symm'. auto.
- unfold "~>". unfold substitution. fold substitution. unfold num_conn. fold num_conn. case (eq_nat n0 n) eqn:X.
  + apply nat_eq_decid in X. destruct X. rewrite closed_subst_eq_aux; auto. apply FOL5. auto.
  + rewrite <- (num_conn_sub A n t). rewrite <- (num_conn_sub B n t). apply FOL5. rewrite subst_remove; auto. apply remove_member_false. auto.
- unfold "~>" in *. simpl in IHPeano_Theorems_Base1. unfold num_conn. fold num_conn. rewrite <- (num_conn_sub A n t). apply MP; auto.
- simpl. case (eq_nat n0 n) eqn:X.
  + apply nat_eq_decid in X. destruct X. apply UG. auto.
  + apply UG. auto.
- simpl. apply equ_trans.
- simpl. apply equ_succ.
- simpl. apply non_zero.
- simpl. apply succ_equ.
- simpl. apply pl0.
- simpl. apply plS.
- simpl. apply ml0.
- simpl. apply mlS.
- unfold "~>". unfold substitution. fold substitution. case (eq_nat n0 n) eqn:X.
  + apply nat_eq_decid in X. destruct X. rewrite closed_subst_eq_aux. apply induct. rewrite subst_remove; auto. apply remove_not_member.
  + rewrite (substitution_order _ _ _ zero); auto. rewrite (weak_substitution_order _ _ _ (succ (var n0))); auto. rewrite <- (num_conn_sub A n t). apply induct. simpl. rewrite X. auto. rewrite closed_free_list_t; auto. apply eq_nat_symm'. auto. apply eq_nat_symm'. auto.
Qed.

Lemma PA_Implication_equiv : forall (A : formula) (d n : nat) (alpha : ord) (t : term), closed_t t = true -> Peano_Theorems_Implication A d alpha -> Peano_Theorems_Implication (substitution A n t) d alpha.
Proof.
intros. induction H0.
- unfold "~>". rewrite <- (num_conn_sub _ n t). apply I_FOL1.
- unfold "~>". unfold substitution. fold substitution. unfold num_conn. fold num_conn. rewrite <- (num_conn_sub A n t). rewrite <- (num_conn_sub B n t). rewrite <- (num_conn_sub C n t). apply I_FOL2.
- unfold "~>". unfold substitution. fold substitution. unfold num_conn. fold num_conn. rewrite <- (num_conn_sub A n t). rewrite <- (num_conn_sub B n t). apply I_FOL3.
- unfold "~>". unfold substitution. fold substitution. unfold num_conn. fold num_conn. case (eq_nat n0 n) eqn:X.
  + apply nat_eq_decid in X. destruct X. rewrite closed_subst_eq_aux. apply I_FOL4; auto. rewrite subst_remove; auto. apply remove_not_member.
  + rewrite substitution_order; auto. rewrite num_conn_sub. rewrite <- (num_conn_sub A n t). rewrite <- (num_conn_sub (substitution A n t) n0 t0). apply I_FOL4; auto. apply eq_nat_symm'. auto.
- unfold "~>". unfold substitution. fold substitution. unfold num_conn. fold num_conn. case (eq_nat n0 n) eqn:X.
  + apply nat_eq_decid in X. destruct X. rewrite closed_subst_eq_aux; auto. apply I_FOL5. auto.
  + rewrite <- (num_conn_sub A n t). rewrite <- (num_conn_sub B n t). apply I_FOL5. rewrite subst_remove; auto. apply remove_member_false. auto.
- unfold "~>" in *. simpl in IHPeano_Theorems_Implication1. unfold num_conn. fold num_conn. rewrite <- (num_conn_sub A n t). apply I_MP; auto.
- simpl. case (eq_nat n0 n) eqn:X.
  + apply nat_eq_decid in X. destruct X. apply I_UG. auto. intros. auto.
  + apply I_UG. auto. intros. rewrite weak_substitution_order; auto. rewrite closed_free_list_t; auto. rewrite closed_free_list_t; auto.
- simpl. apply I_equ_trans.
- simpl. apply I_equ_succ.
- simpl. apply I_non_zero.
- simpl. apply I_succ_equ.
- simpl. apply I_pl0.
- simpl. apply I_plS.
- simpl. apply I_ml0.
- simpl. apply I_mlS.
- unfold "~>". unfold substitution. fold substitution. case (eq_nat n0 n) eqn:X.
  + apply nat_eq_decid in X. destruct X. rewrite closed_subst_eq_aux. apply I_induct. rewrite subst_remove; auto. apply remove_not_member.
  + rewrite (substitution_order _ _ _ zero); auto. rewrite (weak_substitution_order _ _ _ (succ (var n0))); auto. rewrite <- (num_conn_sub A n t). apply I_induct. simpl. rewrite X. auto. rewrite closed_free_list_t; auto. apply eq_nat_symm'. auto. apply eq_nat_symm'. auto.
Qed.

Lemma PA_Base_equiv_PA_Implication : forall (A : formula) (d : nat) (alpha : ord), Peano_Theorems_Base A d alpha -> Peano_Theorems_Implication A d alpha.
Proof.
intros. induction H.
- apply I_FOL1.
- apply I_FOL2.
- apply I_FOL3.
- apply I_FOL4; auto.
- apply I_FOL5; auto.
- apply I_MP; auto. 
- apply I_UG. auto. intros. apply PA_Implication_equiv; auto. 
- apply I_equ_trans.
- apply I_equ_succ.
- apply I_non_zero.
- apply I_succ_equ.
- apply I_pl0.
- apply I_plS.
- apply I_ml0.
- apply I_mlS.
- apply I_induct.
Qed.

Lemma PA_Base_closed_PA_omega : forall A d alpha, Peano_Theorems_Base A d alpha -> (forall t, closed_t t = true -> PA_omega_theorem (closure A t) d alpha).
Proof.
intros. apply PA_closed_PA_omega; auto. apply PA_Base_equiv_PA_Implication. auto. 
Qed.