Add LoadPath "theories/Casteran" as Ordering.
Add LoadPath "theories/Maths" as Maths_Facts.
Add LoadPath "theories/Logic" as Systems.

From Maths_Facts Require Import naturals.
From Maths_Facts Require Import ordinals.
From Maths_Facts Require Import lists.
From Systems Require Import definitions.
From Systems Require Import fol.
From Systems Require Import PA_omega.
Require Import Lia.

Inductive ptree : Type :=
| deg_up : nat -> ptree -> ptree

| ord_up : ord -> ptree -> ptree

| node : formula -> ptree


| exchange_ab : formula -> formula -> nat -> ord -> ptree -> ptree

| exchange_cab : formula -> formula -> formula -> nat -> ord -> ptree -> ptree

| exchange_abd : formula -> formula -> formula -> nat -> ord -> ptree -> ptree

| exchange_cabd :
    formula -> formula -> formula -> formula -> nat -> ord -> ptree -> ptree

| contraction_a : formula -> nat -> ord -> ptree -> ptree

| contraction_ad : formula -> formula -> nat -> ord -> ptree -> ptree


| weakening_ad : formula -> formula -> nat -> ord -> ptree -> ptree

| demorgan_ab :
    formula -> formula ->  nat -> nat -> ord -> ord ->
    ptree -> ptree -> ptree

| demorgan_abd :
    formula -> formula -> formula -> nat -> nat -> ord -> ord ->
    ptree -> ptree -> ptree

| negation_a : formula -> nat -> ord -> ptree -> ptree

| negation_ad : formula -> formula -> nat -> ord -> ptree -> ptree



| quantification_a : formula -> nat -> c_term -> nat -> ord -> ptree -> ptree

| quantification_ad :
    formula -> formula -> nat -> c_term -> nat -> ord -> ptree -> ptree

| w_rule_a : formula -> nat -> nat -> ord -> (c_term -> ptree) -> ptree

| w_rule_ad :
    formula -> formula -> nat -> nat -> ord -> (c_term -> ptree) -> ptree

| cut_ca :
    formula -> formula ->  nat -> nat -> ord -> ord ->
    ptree -> ptree -> ptree

| cut_ad :
    formula -> formula ->  nat -> nat -> ord -> ord ->
    ptree -> ptree -> ptree

| cut_cad :
    formula -> formula -> formula -> nat -> nat -> ord -> ord ->
    ptree -> ptree -> ptree.


Fixpoint ptree_formula (P : ptree) : formula :=
match P with
| deg_up d P' => ptree_formula P'

| ord_up alpha P' => ptree_formula P'

| node A => A


| exchange_ab A B d alpha P' => lor B A

| exchange_cab C A B d alpha P' => lor (lor C B) A

| exchange_abd A B D d alpha P' => lor (lor B A) D

| exchange_cabd C A B D d alpha P' => lor (lor (lor C B) A) D

| contraction_a A d alpha P' => A

| contraction_ad A D d alpha P' => lor A D


| weakening_ad A D d alpha P' => lor A D

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2 => neg (lor A B)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2 => lor (neg (lor A B)) D

| negation_a A d alpha P' => neg (neg A)

| negation_ad A D d alpha P' => lor (neg (neg A)) D

| quantification_a A n t d alpha P' => neg (univ n A)

| quantification_ad A D n t d alpha P' => lor (neg (univ n A)) D

| w_rule_a A n d alpha g => univ n A

| w_rule_ad A D n d alpha g => lor (univ n A) D


| cut_ca C A d1 d2 alpha1 alpha2 P1 P2 => C

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 => D

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2 => lor C D

end.


Fixpoint ptree_deg (P : ptree) : nat :=
match P with
| deg_up d P' => d

| ord_up alpha P' => ptree_deg P'

| node A => 0


| exchange_ab A B d alpha P' => d

| exchange_cab E A B d alpha P' => d

| exchange_abd A B D d alpha P' => d

| exchange_cabd E A B D d alpha P' => d

| contraction_a A d alpha P' => d

| contraction_ad A D d alpha P' => d


| weakening_ad A D d alpha P' => d

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2 => max d1 d2

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2 => max d1 d2

| negation_a A d alpha P' => d

| negation_ad A D d alpha P' => d

| quantification_a A n t d alpha P' => d

| quantification_ad A D n t d alpha P' => d

| w_rule_a A n d alpha g => d

| w_rule_ad A D n d alpha g => d


| cut_ca E A d1 d2 alpha1 alpha2 P1 P2 => max (max d1 d2) (num_conn (neg A))

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 => max (max d1 d2) (num_conn (neg A))

| cut_cad E A D d1 d2 alpha1 alpha2 P1 P2 => max (max d1 d2) (num_conn (neg A))

end.


Fixpoint ptree_ord (P : ptree) : ord :=
match P with
| deg_up d P' => ptree_ord P'

| ord_up alpha P' => alpha

| node A => Zero


| exchange_ab A B d alpha P' => alpha

| exchange_cab E A B d alpha P' => alpha

| exchange_abd A B D d alpha P' => alpha

| exchange_cabd E A B D d alpha P' => alpha

| contraction_a A d alpha P' => alpha

| contraction_ad A D d alpha P' => alpha

| weakening_ad A D d alpha P' => (ord_succ alpha)

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2 => ord_succ (ord_max alpha1 alpha2)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2 => ord_succ (ord_max alpha1 alpha2)

| negation_a A d alpha P' => ord_succ alpha

| negation_ad A D d alpha P' => ord_succ alpha

| quantification_a A n t d alpha P' => ord_succ alpha

| quantification_ad A D n t d alpha P' => ord_succ alpha

| w_rule_a A n d alpha g => ord_succ alpha

| w_rule_ad A D n d alpha g => ord_succ alpha

| cut_ca E A d1 d2 alpha1 alpha2 P1 P2 => ord_succ (ord_max alpha1 alpha2)

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 => ord_succ (ord_max alpha1 alpha2)

| cut_cad E A D d1 d2 alpha1 alpha2 P1 P2 => ord_succ (ord_max alpha1 alpha2)

end.


Fixpoint valid (P : ptree) : Type :=
match P with
| deg_up d P' => (d > ptree_deg P') * (valid P')

| ord_up alpha P' => (ord_lt (ptree_ord P') alpha) * (valid P') * (nf alpha)

| node A => PA_omega_axiom A = true


| exchange_ab A B d alpha P' =>
    (ptree_formula P' = lor A B) * (valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| exchange_cab E A B d alpha P' =>
    (ptree_formula P' = lor (lor E A) B) * (valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| exchange_abd A B D d alpha P' =>
    (ptree_formula P' = lor (lor A B) D) * (valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| exchange_cabd E A B D d alpha P' =>
    (ptree_formula P' = lor (lor (lor E A) B) D) * (valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| contraction_a A d alpha P' =>
    (ptree_formula P' = lor A A) * (valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| contraction_ad A D d alpha P' =>
    (ptree_formula P' = lor (lor A A) D) * (valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')


| weakening_ad A D d alpha P' =>
    (ptree_formula P' = D) * (closed A = true) * (valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2 =>
    (ptree_formula P1 = neg A) * (valid P1) *
    (ptree_formula P2 = neg B) * (valid P2) *
    (d1 = ptree_deg P1) * (d2 = ptree_deg P2) *
    (alpha1 = ptree_ord P1) * (alpha2 = ptree_ord P2)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2 =>
    (ptree_formula P1 = lor (neg A) D) * (valid P1) *
    (ptree_formula P2 = lor (neg B) D) * (valid P2) *
    (d1 = ptree_deg P1) * (d2 = ptree_deg P2) *
    (alpha1 = ptree_ord P1) * (alpha2 = ptree_ord P2)

| negation_a A d alpha P' =>
    (ptree_formula P' = A) * (valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| negation_ad A D d alpha P' =>
    (ptree_formula P' = lor A D) * (valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')


| quantification_a A n t d alpha P' =>
    (ptree_formula P' = neg (substitution A n (projT1 t))) * (valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| quantification_ad A D n t d alpha P' =>
    (ptree_formula P' = lor (neg (substitution A n (projT1 t))) D) * (valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| w_rule_a A n d alpha g => (forall (t : c_term),
    (ptree_formula (g t) = substitution A n (projT1 t)) *
    (valid (g t)) * (d >= ptree_deg (g t)) * (alpha = ptree_ord (g t)))

| w_rule_ad A D n d alpha g => (forall (t : c_term),
    (ptree_formula (g t) = lor (substitution A n (projT1 t)) D) *
    (valid (g t)) * (d >= ptree_deg (g t)) * (alpha = ptree_ord (g t)))


| cut_ca E A d1 d2 alpha1 alpha2 P1 P2 =>
    (ptree_formula P1 = lor E A) * (valid P1) *
    (ptree_formula P2 = neg A) * (valid P2) *
    (d1 = ptree_deg P1) * (d2 = ptree_deg P2) *
    (alpha1 = ptree_ord P1) * (alpha2 = ptree_ord P2)

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 =>
    (ptree_formula P1 = A) * (valid P1) *
    (ptree_formula P2 = lor (neg A) D) * (valid P2) *
    (d1 = ptree_deg P1) * (d2 = ptree_deg P2) *
    (alpha1 = ptree_ord P1) * (alpha2 = ptree_ord P2)

| cut_cad E A D d1 d2 alpha1 alpha2 P1 P2 =>
    (ptree_formula P1 = lor E A) * (valid P1) *
    (ptree_formula P2 = lor (neg A) D) * (valid P2) *
    (d1 = ptree_deg P1) * (d2 = ptree_deg P2) *
    (alpha1 = ptree_ord P1) * (alpha2 = ptree_ord P2)

end.

(* Proof trees are equivalent to theorems *)
(* *)
Definition P_proves (P : ptree) (A : formula) (d : nat) (alpha : ord) : Type :=
  (ptree_formula P = A) * (valid P) *
  (d >= ptree_deg P) * (ptree_ord P = alpha).

Definition provable (A : formula) (d : nat) (alpha : ord) : Type :=
  {P : ptree & P_proves P A d alpha}.

Lemma provable_theorem : forall (A : formula) (d : nat) (alpha : ord),
  PA_omega_theorem A d alpha -> provable A d alpha.
Proof.
intros. unfold provable.
induction H; try destruct IHPA_omega_theorem as [P [[[HP1 HP2] HP3] HP4]].
- exists (deg_up d' P). repeat split; auto. lia.
- exists (ord_up beta P). repeat split; auto. rewrite HP4. auto.
- exists (node A). repeat split. apply e. auto.
- exists (exchange_ab A B (ptree_deg P) alpha P). repeat split; auto.
- exists (exchange_cab C A B (ptree_deg P) alpha P). repeat split; auto.
- exists (exchange_abd A B D (ptree_deg P) alpha P). repeat split; auto.
- exists (exchange_cabd C A B D (ptree_deg P) alpha P). repeat split; auto.
- exists (contraction_a A (ptree_deg P) alpha P). repeat split; auto.
- exists (contraction_ad A D (ptree_deg P) alpha P). repeat split; auto.
- exists (weakening_ad A D (ptree_deg P) alpha P). repeat split; auto.
- destruct IHPA_omega_theorem1 as [P [[[HP1 HP2] HP3] HP4]].
  destruct IHPA_omega_theorem2 as [P' [[[HP'1 HP'2] HP'3] HP'4]].
  exists (demorgan_ab A B (ptree_deg P) (ptree_deg P') alpha1 alpha2 P P'). repeat split; auto. simpl. lia.
- destruct IHPA_omega_theorem1 as [P [[[HP1 HP2] HP3] HP4]].
  destruct IHPA_omega_theorem2 as [P' [[[HP'1 HP'2] HP'3] HP'4]].
  exists (demorgan_abd A B D (ptree_deg P) (ptree_deg P') alpha1 alpha2 P P'). repeat split; auto. simpl. lia.
- exists (negation_a A (ptree_deg P) alpha P). repeat split; auto.
- exists (negation_ad A D (ptree_deg P) alpha P). repeat split; auto.
- exists (quantification_a A n (closing t e) (ptree_deg P) alpha P). repeat split; auto.
- exists (quantification_ad A D n (closing t e) (ptree_deg P) alpha P). repeat split; auto.
- exists (w_rule_a A n d alpha (fun t => projT1(X (projT1 t) (projT2 t)))).
  repeat split; unfold projT1.
  + destruct (X (projT1 t)) as [P [[[HP1 HP2] HP3] HP4]]; auto.
  + destruct (X (projT1 t)) as [P [[[HP1 HP2] HP3] HP4]]; auto.
  + destruct (X (projT1 t)) as [P [[[HP1 HP2] HP3] HP4]]; auto.
  + destruct (X (projT1 t)) as [P [[[HP1 HP2] HP3] HP4]]; auto.  
  + simpl. auto.
- unfold P_proves in X.
  exists (w_rule_ad A D n d alpha (fun t => (projT1 (X (projT1 t) (projT2 t))))).
  repeat split; unfold projT1.
  + destruct (X (projT1 t)) as [P [[[HP1 HP2] HP3] HP4]]; auto.
  + destruct (X (projT1 t)) as [P [[[HP1 HP2] HP3] HP4]]; auto.
  + destruct (X (projT1 t)) as [P [[[HP1 HP2] HP3] HP4]]; auto.
  + destruct (X (projT1 t)) as [P [[[HP1 HP2] HP3] HP4]]; auto.  
  + simpl. auto.
- destruct IHPA_omega_theorem1 as [P [[[HP1 HP2] HP3] HP4]].
  destruct IHPA_omega_theorem2 as [P' [[[HP'1 HP'2] HP'3] HP'4]].
  exists (cut_ca C A (ptree_deg P) (ptree_deg P') alpha1 alpha2 P P'). repeat split; auto. simpl. lia.
- destruct IHPA_omega_theorem1 as [P [[[HP1 HP2] HP3] HP4]].
  destruct IHPA_omega_theorem2 as [P' [[[HP'1 HP'2] HP'3] HP'4]].
  exists (cut_ad A D (ptree_deg P) (ptree_deg P') alpha1 alpha2 P P'). repeat split; auto. simpl. lia.
- destruct IHPA_omega_theorem1 as [P [[[HP1 HP2] HP3] HP4]].
  destruct IHPA_omega_theorem2 as [P' [[[HP'1 HP'2] HP'3] HP'4]].
  exists (cut_cad C A D (ptree_deg P) (ptree_deg P') alpha1 alpha2 P P'). repeat split; auto. simpl. lia.
Qed.


Lemma valid_w_rule_a :
  forall (A : formula) (n d : nat) (alpha : ord) (g : c_term -> ptree),
  valid (w_rule_a A n d alpha g) ->
  (forall (t : c_term),
    (ptree_formula (g t) = substitution A n (projT1 t)) *
    valid (g t) * (d >= ptree_deg (g t)) * (alpha = ptree_ord (g t))).
Proof.
intros. destruct (X t) as [[[H1 H2] H3] H4]. fold valid in H2.
repeat split; auto.
Qed.

Lemma valid_w_rule_ad :
  forall (A D : formula) (n d : nat) (alpha : ord) (g : c_term -> ptree),
  valid (w_rule_ad A D n d alpha g) ->
  (forall (t : c_term),
    (ptree_formula (g t) = lor (substitution A n (projT1 t)) D) *
    valid (g t) * (d >= ptree_deg (g t)) * (alpha = ptree_ord (g t))).
Proof.
intros. destruct (X t) as [[[H1 H2] H3] H4]. fold valid in H2.
repeat split; auto.
Qed.

Lemma theorem_provable' : forall (t : ptree),
  valid t -> PA_omega_theorem (ptree_formula t) (ptree_deg t) (ptree_ord t).
Proof.
intros t H. induction t.
- inversion H. simpl. apply (deg_incr _ (ptree_deg t)); auto.
- inversion H. destruct X as [X1 X2]. simpl. apply (ord_incr _ _ (ptree_ord t)); auto. 
- inversion H. simpl. apply axiom. auto.
- inversion H as [[[H0 H1] H2] H3]. simpl. apply exchange1.
  rewrite H0 in IHt. rewrite H2,H3. apply IHt. auto.
- inversion H as [[[H0 H1] H2] H3]. simpl. apply exchange2.
  rewrite H0 in IHt. rewrite H2,H3. apply IHt. auto.
- inversion H as [[[H0 H1] H2] H3]. simpl. apply exchange3.
  rewrite H0 in IHt. rewrite H2,H3. apply IHt. auto.
- inversion H as [[[H0 H1] H2] H3]. simpl. apply exchange4.
  rewrite H0 in IHt. rewrite H2,H3. apply IHt. auto.
- inversion H as [[[H0 H1] H2] H3]. simpl. apply contraction1.
  rewrite H0 in IHt. rewrite H2,H3. apply IHt. auto.
- inversion H as [[[H0 H1] H2] H3]. simpl. apply contraction2.
  rewrite H0 in IHt. rewrite H2,H3. apply IHt. auto.
- inversion H as [[[[H0 H1] H2] H3] H4]. simpl. apply weakening; auto.
  rewrite H0 in IHt. rewrite H3,H4. apply IHt. auto.
- inversion H as [[[[[[[H0 H1] H2] H3] H4] H5] H6] H7]. simpl.
  rewrite H0 in IHt1. rewrite H2 in IHt2. apply demorgan1.
  + rewrite H4,H6. apply IHt1. auto.
  + rewrite H5,H7. apply IHt2. auto.
- inversion H as [[[[[[[H0 H1] H2] H3] H4] H5] H6] H7]. simpl.
  rewrite H0 in IHt1. rewrite H2 in IHt2. apply demorgan2.
  + rewrite H4,H6. apply IHt1. auto.
  + rewrite H5,H7. apply IHt2. auto.
- inversion H as [[[H0 H1] H2] H3]. simpl. apply negation1.
  rewrite H0 in IHt. rewrite H2,H3. apply IHt. auto.
- inversion H as [[[H0 H1] H2] H3]. simpl. apply negation2.
  rewrite H0 in IHt. rewrite H2,H3. apply IHt. auto.
- inversion H as [[[H0 H1] H2] H3]. simpl.
  apply (quantification1 _ _ (projT1 c) _ _ (projT2 c)); auto.
  rewrite H0 in IHt. rewrite H2,H3. apply IHt. auto.
- inversion H as [[[H0 H1] H2] H3]. simpl.
  apply (quantification2 _ _ _ (projT1 c) _ _ (projT2 c)); auto.
  rewrite H0 in IHt. rewrite H2,H3. apply IHt. auto.
- rename p into g. rename f into A. rename n0 into d.
  apply w_rule1. intros t Ht. 
  destruct (valid_w_rule_a A n d o g H (closing t Ht)) as [[[Hg1 Hg2] Hg3] Hg4]. simpl in Hg1.
  rewrite <- Hg1. rewrite Hg4. pose proof (X (closing t Ht) Hg2). simpl. apply (deg_monot _ (ptree_deg (g (closing t Ht)))); auto.
- rename f into A. rename f0 into D. rename p into g. rename n0 into d.
  apply w_rule2. intros t Ht.
  destruct (valid_w_rule_ad A D n d o g H (closing t Ht)) as [[[Hg1 Hg2] Hg3] Hg4]. simpl in Hg1.
  rewrite <- Hg1. rewrite Hg4. pose proof (X (closing t Ht) Hg2). simpl. apply (deg_monot _ (ptree_deg (g (closing t Ht)))); auto.
- inversion H as [[[[[[[H0 H1] H2] H3] H4] H5] H6] H7]. simpl.
  rewrite H0 in IHt1. rewrite H2 in IHt2. apply cut1.
  + rewrite H4,H6. apply IHt1. auto.
  + rewrite H5,H7. apply IHt2. auto.
- inversion H as [[[[[[[H0 H1] H2] H3] H4] H5] H6] H7]. simpl.
  rewrite H0 in IHt1. rewrite H2 in IHt2. apply cut2.
  + rewrite H4,H6. apply IHt1. auto.
  + rewrite H5,H7. apply IHt2. auto.
- inversion H as [[[[[[[H0 H1] H2] H3] H4] H5] H6] H7]. simpl.
  rewrite H0 in IHt1. rewrite H2 in IHt2. apply cut3.
  + rewrite H4,H6. apply IHt1. auto.
  + rewrite H5,H7. apply IHt2. auto.
Qed.

Lemma theorem_provable : forall (A : formula) (d : nat) (alpha : ord),
  provable A d alpha -> PA_omega_theorem A d alpha.
Proof.
intros A d alpha H. unfold provable in H. destruct H as [t [[[H1 H2] H3] H4]].
apply leq_type in H3. destruct H3 as [H3 | H3].
- assert (valid (deg_up d t)). simpl. auto.
  assert (ptree_formula (deg_up d t) = A) as X1. auto.
  assert (ptree_ord (deg_up d t) = alpha) as X2. auto.
  assert (ptree_deg (deg_up d t) = d) as X3. auto.
  rewrite <- X1, <- X2, <- X3.
  apply theorem_provable'. auto.
- rewrite <- H1, <- H4. rewrite H3.
  apply theorem_provable'. auto.
Qed.

Lemma ptree_ord_nf : forall (P : ptree), valid P -> nf (ptree_ord P).
Proof.
intros.
pose proof (theorem_provable' _ X).
apply (ord_nf _ _ _ H).
Qed.

(* Some basic examples *)
Definition f_exmp : formula := (atom (equ zero zero)).
Definition ptree_exmp : ptree := node f_exmp.
Lemma ptree_exmp_valid : valid ptree_exmp. Proof. simpl. auto. Qed.

Lemma provable_exmp : provable (atom (equ zero zero)) 0 Zero.
Proof. unfold provable. exists ptree_exmp. repeat split. auto. Qed.

Lemma exchange_provable : forall (A B : formula) (d : nat) (alpha : ord),
  provable (lor A B) d alpha -> provable (lor B A) d alpha.
Proof.
unfold provable. intros A B d alpha H. destruct H as [P [[[H1 H2] H3] H4]].
exists (exchange_ab A B (ptree_deg P) alpha P). repeat split; auto.
Qed.


(* Show that PA_omega proves the associativity laws *)
(* *)
Lemma associativity_1 : forall (C A B : formula) (d : nat) (alpha : ord),
  provable (lor (lor C A) B) d alpha -> provable (lor C (lor A B)) d alpha.
Proof.
unfold provable. intros C A B d alpha H. destruct H as [P [[[H1 H2] H3] H4]].
exists (exchange_ab
        (lor A B) C (ptree_deg P) alpha
        (exchange_cab
          A C B (ptree_deg P) alpha
          (exchange_abd C A B (ptree_deg P) alpha P))).
repeat split; auto.
Qed.

Lemma associativity_2 : forall (C A B : formula) (d : nat) (alpha : ord),
  provable (lor C (lor A B)) d alpha -> provable (lor (lor C A) B) d alpha.
Proof.
unfold provable. intros C A B d alpha H. destruct H as [P [[[H1 H2] H3] H4]].
exists (exchange_abd
          A C B (ptree_deg P) alpha
          (exchange_cab
            A B C (ptree_deg P) alpha
            (exchange_ab C (lor A B) (ptree_deg P) alpha P))).
repeat split; auto.
Qed.



(* We will need these properties in the next section *)
(* *)
Lemma axiom_atomic : forall (A : formula),
  PA_omega_axiom A = true ->
    (exists (a : atomic_formula), A = atom a) \/
    (exists (a : atomic_formula), A = neg (atom a)).
Proof.
intros.
destruct A; try inversion H.
- left. exists a. auto.
- right. destruct A; try inversion H.
  + exists a. auto.
Qed.

Lemma axiom_correct : forall (A : formula),
  PA_omega_axiom A = true ->
    (exists (a : atomic_formula), A = atom a /\ correct_a a = true) \/
    (exists (a : atomic_formula), A = neg (atom a) /\ incorrect_a a = true).
Proof.
intros.
destruct A; try inversion H.
- left. exists a. auto.
- right. destruct A; try inversion H.
  + exists a. auto.
Qed.

Lemma axiom_closed : forall (A : formula),
  PA_omega_axiom A = true -> closed A = true.
Proof.
intros.
apply axiom_correct in H. destruct H.
- destruct H as [ a [ HA Ha] ]. rewrite HA. unfold closed.
  apply correct_closed. apply Ha.
- destruct H as [ a [ HA Ha] ]. rewrite HA. unfold closed.
  apply incorrect_closed. apply Ha.
Qed.

Lemma subst_one_var_free : forall (A : formula) (n : nat) (t : term),
  closed_t t = true ->
  closed (substitution A n t) = true ->
  free_list A = [n] \/ free_list A = [].
Proof.
intros.
pose proof (subst_remove A n t H).
apply closed_free_list in H0. rewrite H0 in H1. symmetry in H1.
rewrite free_list_remove_dups in H1. apply remove_n_dups_empty in H1.
destruct H1.
- left. rewrite free_list_remove_dups. apply H1.
- right. rewrite free_list_remove_dups. apply H1.
Qed.


Lemma theorem_closed : forall (A : formula) (d : nat) (alpha : ord),
  PA_omega_theorem A d alpha -> closed A = true.
Proof.
intros. induction H; auto.
- apply axiom_closed. auto.
- inversion IHPA_omega_theorem. simpl.
  rewrite H1. apply and_bool_symm. apply H1.
- inversion IHPA_omega_theorem. simpl.
  rewrite H1. destruct (and_bool_prop _ _ H1). destruct (and_bool_prop _ _ H0).
  rewrite H2,H3,H4. auto.
- inversion IHPA_omega_theorem. simpl.
  rewrite H1. destruct (and_bool_prop _ _ H1). destruct (and_bool_prop _ _ H0).
  rewrite H2,H3,H4. auto.
- inversion IHPA_omega_theorem. simpl.
  rewrite H1. destruct (and_bool_prop _ _ H1). destruct (and_bool_prop _ _ H0).
  destruct (and_bool_prop _ _ H3). rewrite H2,H4,H5,H6. auto.
- inversion IHPA_omega_theorem. rewrite H1.
  destruct (and_bool_prop _ _ H1). rewrite H0. auto.
- inversion IHPA_omega_theorem. simpl. rewrite H1.
  destruct (and_bool_prop _ _ H1). destruct (and_bool_prop _ _ H0).
  rewrite H2,H3. auto.
- simpl. rewrite e,IHPA_omega_theorem. auto.
- inversion IHPA_omega_theorem1. inversion IHPA_omega_theorem2. simpl.
  rewrite H2,H3. auto.
- inversion IHPA_omega_theorem1. inversion IHPA_omega_theorem2. simpl.
  destruct (and_bool_prop _ _ H2). destruct (and_bool_prop _ _ H3).
  rewrite H1,H4,H5. auto.
- inversion IHPA_omega_theorem. simpl.
  destruct (subst_one_var_free _ _ _ e H1).
  + case_eq (closed A); intros.
    * rewrite H1. auto.
    * rewrite H0. rewrite eq_nat_refl. rewrite H1. auto.
  + apply free_list_closed in H0. rewrite H1. rewrite H0. auto.
- inversion IHPA_omega_theorem. simpl.
  destruct (and_bool_prop _ _ H1). rewrite H2.
  destruct (subst_one_var_free _ _ _ e H0).
  + case_eq (closed A); intros.
    * rewrite H0. auto.
    * rewrite H3. rewrite eq_nat_refl. rewrite H0. auto.
  + apply free_list_closed in H3. rewrite H3. rewrite H0. auto.
- destruct (subst_one_var_free A n zero (repr_closed 0) (H zero (repr_closed 0))); simpl.
  + case_eq (closed A); intros; auto. rewrite H0. rewrite eq_nat_refl. auto.
  + apply free_list_closed in H0. rewrite H0. auto.
- pose proof (H zero (repr_closed 0)). simpl in H0. destruct (and_bool_prop _ _ H0).
  assert (closed (lor (univ n A) D) = closed (univ n A) && closed D). { auto. }
  rewrite H3. rewrite H2.
  destruct (subst_one_var_free A n (represent 0) (repr_closed 0) H1); simpl.
  + case_eq (closed A); intros; auto. rewrite H4. rewrite eq_nat_refl. auto.
  + apply free_list_closed in H4. rewrite H4. auto.
- inversion IHPA_omega_theorem1. destruct (and_bool_prop _ _ H2).
  rewrite H2,H1. auto.
- inversion IHPA_omega_theorem2. destruct (and_bool_prop _ _ H2).
  rewrite H2,H3. auto.
- inversion IHPA_omega_theorem1. inversion IHPA_omega_theorem2. simpl.
  destruct (and_bool_prop _ _ H2). destruct (and_bool_prop _ _ H3).
  rewrite H1,H4,H6. auto.
Qed.


Lemma provable_closed : forall (A : formula) (d : nat) (alpha : ord),
  provable A d alpha -> closed A = true.
Proof.
intros. apply (theorem_closed _ d alpha). apply theorem_provable. auto.
Qed.

Lemma provable_closed' : forall (P : ptree) (A : formula),
  valid P -> ptree_formula P = A -> closed A = true.
Proof.
intros. pose (ptree_deg P) as d. pose (ptree_ord P) as alpha.
apply (provable_closed _ d alpha). unfold provable. exists P.
unfold P_proves. repeat split; auto.
Qed.