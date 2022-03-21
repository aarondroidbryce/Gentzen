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

Definition associativity_1' (P : ptree) : ptree :=
match ptree_formula P, ptree_deg P, ptree_ord P with
| lor (lor C0 A) B, d, alpha =>
    exchange_ab
      (lor A B) C0 d alpha
      (exchange_cab
        A C0 B d alpha
        (exchange_abd C0 A B d alpha P))

| _, _, _ => P
end.

Definition associativity_2' (P : ptree) : ptree :=
match ptree_formula P, ptree_deg P, ptree_ord P with
| lor C0 (lor A B), d, alpha =>
    exchange_abd
      A C0 B d alpha
      (exchange_cab
        A B C0 d alpha
        (exchange_ab C0 (lor A B) d alpha P))

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

Fixpoint within_f (A B : formula) : subst_ind :=
match eq_f A B with
| true => target A
| false => match A with
  | lor C D => lor_ind (within_f C B) (within_f D B)
  | _ => non_target A
  end
end.

Fixpoint contains_f (A B : formula) : bool :=
match eq_f A B with
| true => true
| false => match A with
  | lor C D => (contains_f C B) || (contains_f D B)
  | _ => false
  end
end.

Lemma target_fits : forall f, subst_ind_fit f (target f) = true.
Proof.
intros f. induction f; simpl; auto. rewrite IHf1,IHf2. auto.
Qed.

Lemma within_fits : forall f g, subst_ind_fit f (within_f f g) = true.
Proof.
intros f. induction f.
- intros. unfold within_f. case (eq_f (atom a) g) eqn:X. unfold target. auto. apply non_target_fit.
- intros. unfold within_f. case (eq_f (neg f) g) eqn:X. unfold target. auto. apply non_target_fit.
- intros. unfold within_f. fold within_f. case (eq_f (lor f1 f2) g) eqn:X. apply target_fits. unfold subst_ind_fit. fold subst_ind_fit. rewrite IHf1,IHf2. auto.
- intros. unfold within_f. case (eq_f (univ n f) g) eqn:X. unfold target. auto. apply non_target_fit.
Qed.

Lemma not_contain_non_tatget : forall A B, contains_f A B = false -> within_f A B = non_target A.
Proof.
intros. induction A.
- unfold within_f. unfold contains_f in H. case (eq_f (atom a) B) eqn:X. inversion H. auto.
- unfold within_f. unfold contains_f in H. case (eq_f (neg A) B) eqn:X. inversion H. auto.
- unfold within_f. fold within_f. unfold contains_f in H. fold contains_f in H. case (eq_f (lor A1 A2) B) eqn:X. inversion H. case (contains_f A1 B) eqn:X1. inversion H. case (contains_f A2 B) eqn:X2. inversion H. rewrite IHA1,IHA2; auto.
- unfold within_f. unfold contains_f in H. case (eq_f (univ n A) B) eqn:X. inversion H. auto.
Qed. 

Lemma contains_symm : forall A B C, eq_f (lor A B) C = false -> contains_f (lor A B) C = true -> contains_f (lor B A) C = true.
Proof. 
intros. unfold contains_f in *. fold contains_f in *. rewrite H in H0. apply or_bool_prop in H0. destruct H0; rewrite H0; case (eq_f (lor B A) C); auto. case (contains_f B C); auto.
Qed.

Lemma contains_swap_end : forall A B C D, eq_f (lor (lor A B) C) D = false -> eq_f (lor A B) D = false -> contains_f (lor (lor A B) C) D = true -> contains_f (lor (lor A C) B) D = true.
Proof. 
intros. unfold contains_f in *. fold contains_f in *. rewrite H in H1. rewrite H0 in H1. apply or_bool_prop in H1. destruct H1. apply or_bool_prop in H1. destruct H1.
rewrite H1. case (eq_f (lor (lor A C) B) D); case (eq_f (lor A C) D); auto.
rewrite H1. case (eq_f (lor (lor A C) B) D); case (eq_f (lor A C) D); case (contains_f A D); case (contains_f C D); auto.
rewrite H1. case (eq_f (lor (lor A C) B) D); case (eq_f (lor A C) D); case (contains_f A D); case (contains_f B D); auto.
Qed.

Lemma contains_swap_start : forall A B C D, eq_f (lor (lor A B) C) D = false -> eq_f (lor A B) D = false -> contains_f (lor (lor A B) C) D = true -> contains_f (lor (lor B A) C) D = true.
Proof. 
intros. unfold contains_f in *. fold contains_f in *. rewrite H in H1. rewrite H0 in H1. apply or_bool_prop in H1. destruct H1. apply or_bool_prop in H1. destruct H1;
rewrite H1; case (eq_f (lor (lor B A) C) D); case (eq_f (lor B A) D); case (contains_f A D); case (contains_f B D); case (contains_f C D); auto.
rewrite H1; case (eq_f (lor (lor B A) C) D); case (eq_f (lor B A) D); case (contains_f A D); case (contains_f B D); case (contains_f C D); auto.
Qed.

Lemma contains_swap_mid : forall A B C D E, eq_f (lor (lor (lor A B) C) D) E = false -> eq_f (lor (lor A B) C) E = false -> eq_f (lor A B) E = false -> contains_f (lor (lor (lor A B) C) D) E = true -> contains_f (lor (lor (lor A C) B) D) E = true.
Proof. 
intros. unfold contains_f in *. fold contains_f in *. rewrite H in H2. rewrite H0 in H2. rewrite H1 in H2. apply or_bool_prop in H2. destruct H2. apply or_bool_prop in H2. destruct H2. apply or_bool_prop in H2. destruct H2;
rewrite H2; case (eq_f (lor (lor (lor A C) B) D) E); case (eq_f (lor (lor A C) B) E); case (eq_f (lor A C) E); case (contains_f A E); case (contains_f B E); case (contains_f C E); case (contains_f D E); auto.
rewrite H2; case (eq_f (lor (lor (lor A C) B) D) E); case (eq_f (lor (lor A C) B) E); case (eq_f (lor A C) E); case (contains_f A E); case (contains_f B E); case (contains_f C E); case (contains_f D E); auto.
rewrite H2; case (eq_f (lor (lor (lor A C) B) D) E); case (eq_f (lor (lor A C) B) E); case (eq_f (lor A C) E); case (contains_f A E); case (contains_f B E); case (contains_f C E); case (contains_f D E); auto.
Qed.

Lemma contains_contract : forall A B, eq_f (lor A A) B = false -> contains_f (lor A A) B = true -> contains_f A B = true.
Proof.
intros. unfold contains_f in H0. fold contains_f in H0. rewrite H in H0. apply or_bool_prop in H0; destruct H0; auto.
Qed.

Lemma contains_weaken : forall A B C, contains_f A C = true -> contains_f (lor A B) C = true.
Proof.
intros. unfold contains_f. fold contains_f. rewrite H. case (eq_f (lor A B) C); auto.
Qed.

Lemma contains_closed : forall A B, closed A = true -> contains_f A B = true -> closed B = true.
Proof.
intros A. induction A.
- intros. unfold contains_f in H0. case (eq_f (atom a) B) eqn:Y. apply f_eq_decid in Y. destruct Y. auto. inversion H0.
- intros. unfold contains_f in H0. case (eq_f (neg A) B) eqn:Y. apply f_eq_decid in Y. destruct Y. auto. inversion H0.
- intros. unfold contains_f in H0. fold contains_f in H0. case (eq_f (lor A1 A2) B) eqn:Y. apply f_eq_decid in Y. destruct Y. auto. simpl in H. apply and_bool_prop in H. destruct H. apply or_bool_prop in H0. destruct H0; auto.
- intros. unfold contains_f in H0. case (eq_f (univ n A) B) eqn:Y. apply f_eq_decid in Y. destruct Y. auto. inversion H0.
Qed.

Definition neg_invert (alpha : ord ) : Type := forall (P : ptree) (A B : formula) (n d : nat),
      contains_f A (neg (univ n B)) = true -> (P_proves P A d alpha ->
            { t : term & provable (formula_sub_ind A (neg (univ n B)) (substitution (neg B) n t) (within_f A (neg (univ n B)))) d alpha}).

Lemma w_rule_invertible_a : forall (P : ptree) (A B : formula) (n d : nat) (alpha : ord),
      contains_f A (neg (univ n B)) = true -> (P_proves P A d alpha ->
            { t : term & provable (formula_sub_ind A (neg (univ n B)) (substitution (neg B) n t) (within_f A (neg (univ n B)))) d alpha & closed_t t = true}).
Proof.
unfold provable. induction P; intros A B m d alpha C [[[Ht1 Ht2] Ht3] Ht4].
- destruct Ht2. simpl in Ht3. apply IHP; repeat split; auto. lia.
- destruct Ht2 as [[Ht2a Ht2b] Ht2c]. simpl in Ht1,Ht3,Ht4. destruct Ht4.
  assert (P_proves P A (ptree_deg P) (ptree_ord P)). repeat split; auto. destruct (IHP A B m (ptree_deg P) (ptree_ord P) C X)as [p [P1 [[[HP1 HP2] HP3] HP4]]]. exists p; auto. exists (ord_up o P1). destruct HP4. repeat split; simpl; auto. lia.
- unfold contains_f in C. destruct A; inversion C. case (eq_f (neg A) (neg (univ m B))) eqn:X. inversion X. apply f_eq_decid in H1. rewrite H1 in *. simpl in Ht1. rewrite Ht1 in Ht2. inversion Ht2. inversion C. simpl in Ht1. rewrite Ht1 in Ht2. inversion Ht2.
- simpl in Ht1,Ht3,Ht4. destruct Ht2 as [[[Ht2a Ht2b] Ht2c] Ht2d]. destruct Ht1,Ht4.
  assert (P_proves P (lor f f0) (ptree_deg P) (ptree_ord P)). repeat split; auto. assert (eq_f (lor f0 f) (neg (univ m B)) = false) as X0. auto.
  destruct (IHP (lor f f0) B m (ptree_deg P) (ptree_ord P) (contains_symm _ _ _ X0 C) X)as [p [P1 [[[HP1 HP2] HP3] HP4]]]. exists p; auto. exists (exchange_ab (formula_sub_ind f (neg (univ m B)) (substitution (neg B) m p) (within_f f (neg (univ m B)))) (formula_sub_ind f0 (neg (univ m B)) (substitution (neg B) m p) (within_f f0 (neg (univ m B)))) (ptree_deg P1) o P1). destruct HP4. repeat split; simpl; auto.
  rewrite within_fits. rewrite within_fits. simpl. rewrite sub_fit_true. rewrite sub_fit_true. auto. apply within_fits. apply within_fits. rewrite <- formula_sub_ind_lor. auto. rewrite within_fits. apply within_fits. lia.
- simpl in Ht1,Ht3,Ht4. destruct Ht2 as [[[Ht2a Ht2b] Ht2c] Ht2d]. destruct Ht1,Ht4.
  assert (P_proves P (lor (lor f f0) f1) (ptree_deg P) (ptree_ord P)). repeat split; auto. assert (eq_f (lor (lor f f1) f0) (neg (univ m B)) = false) as X0. auto. assert (eq_f (lor f0 f) (neg (univ m B)) = false) as X1. auto.
  destruct (IHP (lor (lor f f0) f1) B m (ptree_deg P) (ptree_ord P) (contains_swap_end _ _ _ _ X0 X1 C) X)as [p [P1 [[[HP1 HP2] HP3] HP4]]]. exists p; auto. exists (exchange_cab (formula_sub_ind f (neg (univ m B)) (substitution (neg B) m p) (within_f f (neg (univ m B)))) (formula_sub_ind f0 (neg (univ m B)) (substitution (neg B) m p) (within_f f0 (neg (univ m B)))) (formula_sub_ind f1 (neg (univ m B)) (substitution (neg B) m p) (within_f f1 (neg (univ m B)))) (ptree_deg P1) o P1). destruct HP4. repeat split; simpl; auto.
  repeat rewrite within_fits. simpl. repeat rewrite sub_fit_true. auto. apply within_fits. apply within_fits. apply within_fits. repeat rewrite <- formula_sub_ind_lor. auto. unfold subst_ind_fit. fold subst_ind_fit. repeat rewrite within_fits. auto. repeat rewrite within_fits. auto. lia.
- simpl in Ht1,Ht3,Ht4. destruct Ht2 as [[[Ht2a Ht2b] Ht2c] Ht2d]. destruct Ht1,Ht4.
  assert (P_proves P (lor (lor f f0) f1) (ptree_deg P) (ptree_ord P)). repeat split; auto. assert (eq_f (lor (lor f0 f) f1) (neg (univ m B)) = false) as X0. auto. assert (eq_f (lor f0 f) (neg (univ m B)) = false) as X1. auto.
  destruct (IHP (lor (lor f f0) f1) B m (ptree_deg P) (ptree_ord P) (contains_swap_start _ _ _ _ X0 X1 C) X)as [p [P1 [[[HP1 HP2] HP3] HP4]]]. exists p; auto. exists (exchange_abd (formula_sub_ind f (neg (univ m B)) (substitution (neg B) m p) (within_f f (neg (univ m B)))) (formula_sub_ind f0 (neg (univ m B)) (substitution (neg B) m p) (within_f f0 (neg (univ m B)))) (formula_sub_ind f1 (neg (univ m B)) (substitution (neg B) m p) (within_f f1 (neg (univ m B)))) (ptree_deg P1) o P1). destruct HP4. repeat split; simpl; auto.
  repeat rewrite within_fits. simpl. repeat rewrite sub_fit_true. auto. apply within_fits. apply within_fits. apply within_fits. repeat rewrite <- formula_sub_ind_lor. auto. unfold subst_ind_fit. fold subst_ind_fit. repeat rewrite within_fits. auto. repeat rewrite within_fits. auto. lia.
- simpl in Ht1,Ht3,Ht4. destruct Ht2 as [[[Ht2a Ht2b] Ht2c] Ht2d]. destruct Ht1,Ht4.
  assert (P_proves P (lor (lor (lor f f0) f1) f2) (ptree_deg P) (ptree_ord P)). repeat split; auto. assert (eq_f (lor (lor (lor f f1) f0) f2) (neg (univ m B)) = false) as X0. auto. assert (eq_f (lor (lor f f1) f0) (neg (univ m B)) = false) as X1. auto. assert (eq_f (lor f f1) (neg (univ m B)) = false) as X2. auto.
  destruct (IHP (lor (lor (lor f f0) f1) f2) B m (ptree_deg P) (ptree_ord P) (contains_swap_mid _ _ _ _ _ X0 X1 X2 C) X)as [p [P1 [[[HP1 HP2] HP3] HP4]]]. exists p; auto. exists (exchange_cabd (formula_sub_ind f (neg (univ m B)) (substitution (neg B) m p) (within_f f (neg (univ m B)))) (formula_sub_ind f0 (neg (univ m B)) (substitution (neg B) m p) (within_f f0 (neg (univ m B)))) (formula_sub_ind f1 (neg (univ m B)) (substitution (neg B) m p) (within_f f1 (neg (univ m B)))) (formula_sub_ind f2 (neg (univ m B)) (substitution (neg B) m p) (within_f f2 (neg (univ m B)))) (ptree_deg P1) o P1). destruct HP4. repeat split; simpl; auto.
  repeat rewrite within_fits. simpl. repeat rewrite sub_fit_true. auto. apply within_fits. apply within_fits. apply within_fits. apply within_fits. repeat rewrite <- formula_sub_ind_lor. auto. unfold subst_ind_fit. fold subst_ind_fit. repeat rewrite within_fits. auto. unfold subst_ind_fit. fold subst_ind_fit. repeat rewrite within_fits. auto. repeat rewrite within_fits. auto. lia.
- simpl in Ht1,Ht3,Ht4. destruct Ht2 as [[[Ht2a Ht2b] Ht2c] Ht2d]. destruct Ht1,Ht4.
  assert (P_proves P (lor f f) (ptree_deg P) (ptree_ord P)). repeat split; auto.
  destruct (IHP (lor f f) B m (ptree_deg P) (ptree_ord P) (contains_weaken  _ f _ C) X) as [p [P1 [[[HP1 HP2] HP3] HP4]]]. exists p; auto. exists (contraction_a (formula_sub_ind f (neg (univ m B)) (substitution (neg B) m p) (within_f f (neg (univ m B)))) (ptree_deg P1) o P1). destruct HP4. repeat split; simpl; auto.
  rewrite <- formula_sub_ind_lor. auto. rewrite within_fits. auto. lia.
- simpl in Ht1,Ht3,Ht4. destruct Ht2 as [[[Ht2a Ht2b] Ht2c] Ht2d]. destruct Ht1,Ht4.
  assert (P_proves P (lor (lor f f) f0) (ptree_deg P) (ptree_ord P)). repeat split; auto. assert (eq_f (lor (lor f f0) f) (neg (univ m B)) = false) as X0. auto. assert (eq_f (lor f f0) (neg (univ m B)) = false) as X1. auto.
  destruct (IHP (lor (lor f f) f0) B m (ptree_deg P) (ptree_ord P) (contains_swap_end _ _ _ _ X0 X1 (contains_weaken  _ f _ C)) X) as [p [P1 [[[HP1 HP2] HP3] HP4]]]. exists p; auto. exists (contraction_ad (formula_sub_ind f (neg (univ m B)) (substitution (neg B) m p) (within_f f (neg (univ m B)))) (formula_sub_ind f0 (neg (univ m B)) (substitution (neg B) m p) (within_f f0 (neg (univ m B)))) (ptree_deg P1) o P1). destruct HP4. repeat split; simpl; auto.
  rewrite <- formula_sub_ind_lor. auto. repeat rewrite within_fits. auto. repeat rewrite <- formula_sub_ind_lor. auto. simpl. repeat rewrite within_fits. auto. repeat rewrite within_fits. auto. lia.
- simpl in Ht1,Ht3,Ht4. destruct Ht2 as [[[[Ht2a Ht2b] Ht2c] Ht2d] Ht2e]. destruct Ht1. simpl in C. apply or_bool_prop in C. case (contains_f f0 (neg (univ m B))) eqn:Y.
  + assert (P_proves P f0 (ptree_deg P) (ptree_ord P)). repeat split; auto.
  destruct (IHP f0 B m (ptree_deg P) (ptree_ord P) Y X) as [p [P1 [[[HP1 HP2] HP3] HP4]]]. exists p; auto. exists (weakening_ad (formula_sub_ind f (neg (univ m B)) (substitution (neg B) m p) (within_f f (neg (univ m B)))) (formula_sub_ind f0 (neg (univ m B)) (substitution (neg B) m p) (within_f f0 (neg (univ m B)))) (ptree_deg P1) o P1). destruct HP4. repeat split; simpl; auto.
  rewrite <- formula_sub_ind_lor. auto. repeat rewrite within_fits. auto. apply formula_sub_ind_closed; auto. intros. apply closed_univ_sub; auto. lia.
  + exists (represent 0); auto. exists (weakening_ad (formula_sub_ind f (neg (univ m B)) (substitution (neg B) m (represent 0)) (within_f f (neg (univ m B)))) f0 n o P). repeat split; auto.
    simpl. rewrite (not_contain_non_tatget f0); auto. rewrite non_target_fit. repeat rewrite within_fits. simpl. rewrite non_target_sub'. rewrite sub_fit_true. auto. apply within_fits.  inversion C; inversion H. rewrite H. pose (contains_closed _ _ Ht2b H). apply formula_sub_ind_closed; auto. intros. apply closed_univ_sub; auto.
- admit.
- admit.
- simpl in Ht1,Ht3,Ht4. destruct Ht2 as [[[Ht2a Ht2b] Ht2c] Ht2d]. destruct Ht1,Ht4. simpl in C. inversion C.
- simpl in Ht1,Ht3,Ht4. destruct Ht2 as [[[Ht2a Ht2b] Ht2c] Ht2d]. destruct Ht1,Ht4. simpl in C.  
  assert (P_proves P (lor f f0) (ptree_deg P) (ptree_ord P)). repeat split; auto. assert (eq_f (lor f0 f) (neg (univ m B)) = false) as X0. auto.
  destruct (IHP (lor f f0) B m (ptree_deg P) (ptree_ord P) (contains_symm _ _ _ X0 (contains_weaken _ _ _ C)) X) as [p [P1 [[[HP1 HP2] HP3] HP4]]]. case (contains_f f (neg (univ m B))) eqn:Y.
  + exists p; auto. exists (negation_ad f (formula_sub_ind f0 (neg (univ m B)) (substitution (neg B) m p) (within_f f0 (neg (univ m B)))) (ptree_deg P1) o P1). destruct HP4. repeat split; simpl; auto.
    rewrite within_fits. rewrite sub_fit_true; auto. apply within_fits. auto. repeat rewrite within_fits. auto. admit. lia.
  + exists p; auto. exists (negation_ad f (formula_sub_ind f0 (neg (univ m B)) (substitution (neg B) m p) (within_f f0 (neg (univ m B)))) (ptree_deg P1) o P1). destruct HP4. repeat split; simpl; auto.
    rewrite within_fits. rewrite sub_fit_true; auto. apply within_fits. simpl in HP1. repeat rewrite within_fits in HP1. simpl in HP1. rewrite not_contain_non_tatget in HP1; auto. rewrite <- sub_fit_true in HP1. rewrite <- sub_fit_true in HP1. rewrite non_target_sub in HP1. auto. apply within_fits. apply non_target_fit. lia.

- admit.
- admit.
- simpl in Ht1,Ht3,Ht4. destruct Ht1,Ht4. inversion C.
- simpl in Ht1,Ht3,Ht4. destruct Ht1,Ht4. inversion C. simpl in Ht2. admit.
- simpl in Ht1,Ht3,Ht4. destruct Ht2 as [[[[[[[Ht2a Ht2b] Ht2c] Ht2d] Ht2e] Ht2f] Ht2g] Ht2h]. destruct Ht1,Ht4.
  assert (P_proves P1 (lor f f0) (ptree_deg P1) (ptree_ord P1)). repeat split; auto. assert (P_proves P2 (neg f0) (ptree_deg P2) (ptree_ord P2)). repeat split; auto.
  
  assert (eq_f (lor (lor f f0) f) (neg (univ m B)) = false) as X0. auto. assert (eq_f (lor f f0) (neg (univ m B)) = false) as X1. auto.
  destruct (IHP (lor (lor f f) f0) B m (ptree_deg P) (ptree_ord P) (contains_swap_end _ _ _ _ X0 X1 (contains_weaken  _ f _ C)) X) as [p [P1 [[[HP1 HP2] HP3] HP4]]]. exists p; auto. exists (contraction_ad (formula_sub_ind f (neg (univ m B)) (substitution (neg B) m p) (within_f f (neg (univ m B)))) (formula_sub_ind f0 (neg (univ m B)) (substitution (neg B) m p) (within_f f0 (neg (univ m B)))) (ptree_deg P1) o P1). destruct HP4. repeat split; simpl; auto.
  rewrite <- formula_sub_ind_lor. auto. repeat rewrite within_fits. auto. repeat rewrite <- formula_sub_ind_lor. auto. simpl. repeat rewrite within_fits. auto. repeat rewrite within_fits. auto. lia.

- admit.
- admit.
Admitted.


Lemma w_rule_invertible_a :
  forall (P : ptree) (A : formula) (n d : nat) (alpha : ord),
  (P_proves P (neg (univ n A)) d alpha ->
  { t : term & provable (substitution (neg A) n t) d alpha}) * (forall B, P_proves P (lor (neg (univ n A)) B) d alpha ->
  { t : term & provable (lor (substitution (neg A) n t) B) d alpha}) * (forall B, P_proves P (lor B (neg (univ n A))) d alpha ->
  { t : term & provable (lor B (substitution (neg A) n t)) d alpha}) * (forall B C, P_proves P (lor (lor B (neg (univ n A))) C) d alpha ->
  { t : term & provable (lor (lor B (substitution (neg A) n t)) C) d alpha}) * (forall B C, P_proves P (lor C (lor B (neg (univ n A)))) d alpha ->
  { t : term & provable (lor C (lor B (substitution (neg A) n t))) d alpha}) * (forall B C D, P_proves P (lor (lor C (lor B (neg (univ n A)))) D) d alpha ->
  { t : term & provable (lor (lor C (lor B (substitution (neg A) n t))) D) d alpha}).
Proof.
unfold provable. intros P. induction P; intros A m d alpha.
- repeat split.
  + intros [[[Ht1 Ht2] Ht3] Ht4]. destruct Ht2. simpl in Ht3. apply IHP; repeat split; auto. lia.
  + intros B [[[Ht1 Ht2] Ht3] Ht4]. destruct Ht2. simpl in Ht3. apply IHP; repeat split; auto. lia.
  + intros B [[[Ht1 Ht2] Ht3] Ht4]. destruct Ht2. simpl in Ht3. apply IHP; repeat split; auto. lia.
  + intros B C [[[Ht1 Ht2] Ht3] Ht4]. destruct Ht2. simpl in Ht3. apply IHP; repeat split; auto. lia.
  + intros B C [[[Ht1 Ht2] Ht3] Ht4]. destruct Ht2. simpl in Ht3. apply IHP; repeat split; auto. lia.
  + intros B C D [[[Ht1 Ht2] Ht3] Ht4]. destruct Ht2. simpl in Ht3. apply IHP; repeat split; auto. lia.
- repeat split.
  + intros [[[Ht1 Ht2] Ht3] Ht4]. destruct Ht2 as [[Ht2a Ht2b] Ht2c]. simpl in Ht3,Ht4.
    assert (P_proves P (neg (univ m A)) d (ptree_ord P)). repeat split; auto.
    destruct (IHP A m d (ptree_ord P)) as [[[[[IP1 IP2] IP3] IP4] IP5] IP6]. destruct (IP1 X) as [p [P1 [[[HP1 HP2] HP3] HP4]]]. exists p. exists (ord_up alpha P1). destruct Ht4,HP4. repeat split; auto.
  + intros B [[[Ht1 Ht2] Ht3] Ht4]. destruct Ht2 as [[Ht2a Ht2b] Ht2c]. simpl in Ht3,Ht4.
    assert (P_proves P (lor (neg (univ m A)) B) d (ptree_ord P)). repeat split; auto.
    destruct (IHP A m d (ptree_ord P)) as [[[[[IP1 IP2] IP3] IP4] IP5] IP6]. destruct (IP2 B X) as [p [P1 [[[HP1 HP2] HP3] HP4]]]. exists p. exists (ord_up alpha P1). destruct Ht4,HP4. repeat split; auto.
  + intros B [[[Ht1 Ht2] Ht3] Ht4]. destruct Ht2 as [[Ht2a Ht2b] Ht2c]. simpl in Ht3,Ht4.
    assert (P_proves P (lor B (neg (univ m A))) d (ptree_ord P)). repeat split; auto.
    destruct (IHP A m d (ptree_ord P)) as [[[[[IP1 IP2] IP3] IP4] IP5] IP6]. destruct (IP3 B X) as [p [P1 [[[HP1 HP2] HP3] HP4]]]. exists p. exists (ord_up alpha P1). destruct Ht4,HP4. repeat split; auto.
  + intros B C [[[Ht1 Ht2] Ht3] Ht4]. destruct Ht2 as [[Ht2a Ht2b] Ht2c]. simpl in Ht3,Ht4.
    assert (P_proves P (lor (lor B (neg (univ m A))) C) d (ptree_ord P)). repeat split; auto.
    destruct (IHP A m d (ptree_ord P)) as [[[[[IP1 IP2] IP3] IP4] IP5] IP6]. destruct (IP4 B C X) as [p [P1 [[[HP1 HP2] HP3] HP4]]]. exists p. exists (ord_up alpha P1). destruct Ht4,HP4. repeat split; auto.
  + intros B C [[[Ht1 Ht2] Ht3] Ht4]. destruct Ht2 as [[Ht2a Ht2b] Ht2c]. simpl in Ht3,Ht4.
    assert (P_proves P (lor C (lor B (neg (univ m A)))) d (ptree_ord P)). repeat split; auto.
    destruct (IHP A m d (ptree_ord P)) as [[[[[IP1 IP2] IP3] IP4] IP5] IP6]. destruct (IP5 B C X) as [p [P1 [[[HP1 HP2] HP3] HP4]]]. exists p. exists (ord_up alpha P1). destruct Ht4,HP4. repeat split; auto.
  + intros B C D [[[Ht1 Ht2] Ht3] Ht4]. destruct Ht2 as [[Ht2a Ht2b] Ht2c]. simpl in Ht3,Ht4.
    assert (P_proves P (lor (lor C (lor B (neg (univ m A)))) D) d (ptree_ord P)). repeat split; auto.
    destruct (IHP A m d (ptree_ord P)) as [[[[[IP1 IP2] IP3] IP4] IP5] IP6]. destruct (IP6 B C D X) as [p [P1 [[[HP1 HP2] HP3] HP4]]]. exists p. exists (ord_up alpha P1). destruct Ht4,HP4. repeat split; auto.
- repeat split.
  + intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. rewrite Ht1 in Ht2. inversion Ht2.
  + intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. rewrite Ht1 in Ht2. inversion Ht2.
  + intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. rewrite Ht1 in Ht2. inversion Ht2.
  + intros B C [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. rewrite Ht1 in Ht2. inversion Ht2.
  + intros B C [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. rewrite Ht1 in Ht2. inversion Ht2.
  + intros B C D [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. rewrite Ht1 in Ht2. inversion Ht2.
- repeat split.
  + intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
  + intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1,Ht3,Ht4. destruct Ht2 as [[[Ht2a Ht2b] Ht2c] Ht2d]. inversion Ht1. rewrite H0,H1 in *.
    assert (P_proves P (lor B (neg (univ m A))) d (ptree_ord P)). repeat split; auto. lia.
    destruct (IHP A m d (ptree_ord P)) as [[[[[IP1 IP2] IP3] IP4] IP5] IP6]. destruct (IP3 B X) as [p [P1 [[[HP1 HP2] HP3] HP4]]]. exists p. exists (exchange_ab B (substitution (neg A) m p) (ptree_deg P1) o P1). destruct Ht4,HP4. repeat split; auto.
  + intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1,Ht3,Ht4. destruct Ht2 as [[[Ht2a Ht2b] Ht2c] Ht2d]. inversion Ht1. rewrite H0,H1 in *.
    assert (P_proves P (lor (neg (univ m A)) B) d (ptree_ord P)). repeat split; auto. lia.
    destruct (IHP A m d (ptree_ord P)) as [[[[[IP1 IP2] IP3] IP4] IP5] IP6]. destruct (IP2 B X) as [p [P1 [[[HP1 HP2] HP3] HP4]]]. exists p. exists (exchange_ab (substitution (neg A) m p) B (ptree_deg P1) o P1). destruct Ht4,HP4. repeat split; auto.
  + intros B C [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1,Ht3,Ht4. destruct Ht2 as [[[Ht2a Ht2b] Ht2c] Ht2d]. inversion Ht1. rewrite H0,H1 in *.
    assert (P_proves P (lor C (lor B (neg (univ m A)))) d (ptree_ord P)). repeat split; auto. lia.
    destruct (IHP A m d (ptree_ord P)) as [[[[[IP1 IP2] IP3] IP4] IP5] IP6]. destruct (IP5 B C X) as [p [P1 [[[HP1 HP2] HP3] HP4]]]. exists p. exists (exchange_ab C (lor B (substitution (neg A) m p)) (ptree_deg P1) o P1). destruct Ht4,HP4. repeat split; simpl; auto.
  + intros B C [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1,Ht3,Ht4. destruct Ht2 as [[[Ht2a Ht2b] Ht2c] Ht2d]. inversion Ht1. rewrite H0,H1 in *.
    assert (P_proves P (lor (lor B (neg (univ m A))) C) d (ptree_ord P)). repeat split; auto. lia.
    destruct (IHP A m d (ptree_ord P)) as [[[[[IP1 IP2] IP3] IP4] IP5] IP6]. destruct (IP4 B C X) as [p [P1 [[[HP1 HP2] HP3] HP4]]]. exists p. exists (exchange_ab (lor B (substitution (neg A) m p)) C (ptree_deg P1) o P1). destruct Ht4,HP4. repeat split; simpl; auto. 
  + intros B C D [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1,Ht3,Ht4. destruct Ht2 as [[[Ht2a Ht2b] Ht2c] Ht2d]. inversion Ht1. rewrite H0,H1 in *. 
    assert (P_proves P (lor (lor B (neg (univ m A))) C) d (ptree_ord P)). repeat split; auto. lia.
    destruct (IHP A m d (ptree_ord P)) as [[[[[IP1 IP2] IP3] IP4] IP5] IP6]. destruct (IP4 B C X) as [p [P1 [[[HP1 HP2] HP3] HP4]]]. exists p. exists (exchange_ab (lor B (substitution (neg A) m p)) C (ptree_deg P1) o P1). destruct Ht4,HP4. repeat split; simpl; auto. 
    
- repeat split.
  + intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
  + intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
  + intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1,Ht3,Ht4. inversion Ht1. rewrite H1 in *. destruct Ht2 as [[[Ht2a Ht2b] Ht2c] Ht2d].
    assert (P_proves P (lor (lor f (neg (univ m A))) f1) d (ptree_ord P)). repeat split; auto. lia.
    destruct (IHP A m d (ptree_ord P)) as [[[[IP1 IP2] IP3] IP4] IP5]. destruct (IP4 f f1 X) as [p [P1 [[[HP1 HP2] HP3] HP4]]]. exists p. exists (exchange_abd f1 f (substitution (neg A) m p) (ptree_deg P1) o (associativity_2' (exchange_ab (lor f (substitution (neg A) m p)) f1 (ptree_deg P1) o P1))). destruct Ht4,HP4. repeat split; simpl; auto.  
  + intros B C [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1,Ht3,Ht4. inversion Ht1. rewrite H0,H1,H2 in *. destruct Ht2 as [[[Ht2a Ht2b] Ht2c] Ht2d].
    assert (P_proves P (lor (lor B C) (neg (univ m A))) d (ptree_ord P)). repeat split; auto. lia.
    destruct (IHP A m d (ptree_ord P)) as [[[[IP1 IP2] IP3] IP4] IP5]. destruct (IP3 (lor B C) X) as [p [P1 [[[HP1 HP2] HP3] HP4]]]. exists p. exists (exchange_cab B C (substitution (neg A) m p) (ptree_deg P1) o P1). destruct Ht4,HP4. repeat split; simpl; auto.  
  + intros B C [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1,Ht3,Ht4. inversion Ht1. rewrite H1 in *. destruct Ht2 as [[[Ht2a Ht2b] Ht2c] Ht2d].
    assert (P_proves P (lor (lor B C) (neg (univ m A))) d (ptree_ord P)). repeat split; auto. lia.
    destruct (IHP A m d (ptree_ord P)) as [[[[IP1 IP2] IP3] IP4] IP5]. destruct (IP3 (lor B C) X) as [p [P1 [[[HP1 HP2] HP3] HP4]]]. exists p. exists (exchange_cab B C (substitution (neg A) m p) (ptree_deg P1) o P1). destruct Ht4,HP4. repeat split; simpl; auto.  

- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. 
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. 
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. destruct H0,H1. destruct Ht2 as [[[[Ht2a Ht2b] Ht2c] Ht2d] Ht2e]. simpl in Ht3,Ht4. exists t. simpl in Ht4. exists (ord_up (ord_succ o) P). rewrite Ht2e. repeat split; simpl; auto. apply ord_succ_monot. apply ord_succ_nf. apply ptree_ord_nf. auto. lia. rewrite <- Ht2e. auto.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. destruct H0,H1,H2. destruct Ht2 as [[[[Ht2a Ht2b] Ht2c] Ht2d] Ht2e]. simpl in Ht3,Ht4. exists t. simpl in Ht4. exists (ord_up (ord_succ o) P). rewrite Ht2e. repeat split; simpl; auto. apply ord_succ_monot. apply ord_succ_nf. apply ptree_ord_nf. auto. lia. rewrite <- Ht2e. auto. 
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. rewrite H0,H1 in *. destruct Ht2 as [[[[Ht2a Ht2b] Ht2c] Ht2d] Ht2e]. simpl in Ht3,Ht4.
  assert (P_proves P (lor (neg (substitution f n t)) (neg (univ m A))) d (ptree_ord P)). repeat split; auto. lia.
  destruct (IHP A m d (ptree_ord P)) as [[IP1 IP2] IP3]. destruct (IP3 (neg (substitution f n t)) X) as [p [P1 [[[HP1 HP2] HP3] HP4]]]. exists p. exists (quantification_ad f (neg (substitution A m p)) n t (ptree_deg P1) o P1). repeat split; simpl; auto. rewrite H0. auto. destruct HP4. auto.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
- intros [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1.
- intros B [[[Ht1 Ht2] Ht3] Ht4]. simpl in Ht1. inversion Ht1. admit.
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
