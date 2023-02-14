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

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 => ord_succ (ord_succ (ord_max alpha1 alpha2))

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
  (d >= ptree_deg P) * (alpha = ptree_ord P).

Definition provable (A : formula) (d : nat) (alpha : ord) : Type :=
  {P : ptree & P_proves P A d alpha}.

Lemma provable_theorem : forall (A : formula) (d : nat) (alpha : ord),
  PA_omega_theorem A d alpha -> provable A d alpha.
Proof.
intros A d alpha T. unfold provable.
induction T; try destruct IHT as [P [[[PF PV] PD] PO]].
- exists (deg_up d' P). repeat split; auto. lia.
- exists (ord_up beta P). repeat split; auto. rewrite <- PO. auto.
- exists (node A). repeat split. apply e. auto.
- exists (exchange_ab A B (ptree_deg P) alpha P). repeat split; auto.
- exists (exchange_cab C A B (ptree_deg P) alpha P). repeat split; auto.
- exists (exchange_abd A B D (ptree_deg P) alpha P). repeat split; auto.
- exists (exchange_cabd C A B D (ptree_deg P) alpha P). repeat split; auto.
- exists (contraction_a A (ptree_deg P) alpha P). repeat split; auto.
- exists (contraction_ad A D (ptree_deg P) alpha P). repeat split; auto.
- exists (weakening_ad A D (ptree_deg P) alpha P). repeat split; auto.
- destruct IHT1 as [P1 [[[P1F P1V] P1D] P1H]].
  destruct IHT2 as [P2 [[[P2F P2V] P2D] P2H]].
  exists (demorgan_ab A B (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; auto. simpl. lia.
- destruct IHT1 as [P1 [[[P1F P1V] P1D] P1H]].
  destruct IHT2 as [P2 [[[P2F P2V] P2D] P2H]].
  exists (demorgan_abd A B D (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; auto. simpl. lia.
- exists (negation_a A (ptree_deg P) alpha P). repeat split; auto.
- exists (negation_ad A D (ptree_deg P) alpha P). repeat split; auto.
- exists (quantification_a A n c (ptree_deg P) alpha P). repeat split; auto.
- exists (quantification_ad A D n c (ptree_deg P) alpha P). repeat split; auto.
- exists (w_rule_a A n d alpha (fun c => projT1(X c))).
  repeat split; try destruct (X t) as [P [[[HP1 HP2] HP3] HP4]]; auto.
- unfold P_proves in X.
  exists (w_rule_ad A D n d alpha (fun c => (projT1 (X c)))).
  repeat split; try destruct (X t) as [P [[[HP1 HP2] HP3] HP4]]; auto.
- destruct IHT1 as [P1 [[[P1F P1V] P1D] P1H]].
  destruct IHT2 as [P2 [[[P2F P2V] P2D] P2H]].
  exists (cut_ca C A (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; auto. simpl. lia.
- destruct IHT1 as [P1 [[[P1F P1V] P1D] P1H]].
  destruct IHT2 as [P2 [[[P2F P2V] P2D] P2H]].
  exists (cut_ad A D (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; auto. simpl. lia.
- destruct IHT1 as [P1 [[[P1F P1V] P1D] P1H]].
  destruct IHT2 as [P2 [[[P2F P2V] P2D] P2H]].
  exists (cut_cad C A D (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; auto. simpl. lia.
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

Lemma theorem_provable' : forall (P : ptree),
  valid P -> PA_omega_theorem (ptree_formula P) (ptree_deg P) (ptree_ord P).
Proof.
intros P PV. induction P;
(try inversion PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1H] P2H]) ||
(try inversion PV as [[[PF PV'] PD] PH]); simpl;
try rewrite P1F in IHP1; try rewrite P2F in IHP2;
try rewrite P1D,P2D,P1H,P2H;
try rewrite PF in IHP; try rewrite PD,PH.

- inversion PV as [LT PV']. apply (deg_incr _ (ptree_deg P) _ _ (IHP PV') LT).
- inversion PV as [[LT PV'] N]. simpl. apply (ord_incr _ _ (ptree_ord P) _ (IHP PV') LT N). 
- inversion PV as [AX]. apply axiom. apply AX.
- apply exchange1. apply IHP. apply PV'.
- apply exchange2. apply IHP. apply PV'.
- apply exchange3. apply IHP. apply PV'.
- apply exchange4. apply IHP. apply PV'.
- apply contraction1. apply IHP. apply PV'.
- apply contraction2. apply IHP. apply PV'.
- destruct PF as [PF CF]. apply weakening.
  + apply CF.
  + rewrite <- PF. apply IHP. apply PV'.
- apply demorgan1.
  + apply IHP1. apply P1V.
  + apply IHP2. apply P2V.
- apply demorgan2.
  + apply IHP1. apply P1V.
  + apply IHP2. apply P2V.
- apply negation1. apply IHP. apply PV'.
- apply negation2. apply IHP. apply PV'.
- apply (quantification1 _ _ c). apply IHP. apply PV'.
- apply (quantification2 _ _ _ c). apply IHP. apply PV'.
- apply w_rule1. intros c.
  destruct (PV c) as [[[PF PV'] PD] PH].
  fold valid in PV'.
  rewrite <- PF. rewrite PH.
  apply (deg_monot _ _ _ _ PD).
  apply X. apply PV'.
- apply w_rule2. intros c.
  destruct (PV c) as [[[PF PV'] PD] PH].
  fold valid in PV'.
  rewrite <- PF. rewrite PH.
  apply (deg_monot _ _ _ _ PD).
  apply X. apply PV'.
- apply cut1.
  + apply IHP1. apply P1V.
  + apply IHP2. apply P2V.
- apply cut2.
  + apply IHP1. apply P1V.
  + apply IHP2. apply P2V.
- apply cut3.
  + apply IHP1. apply P1V.
  + apply IHP2. apply P2V.
Qed.

Lemma theorem_provable : forall (A : formula) (d : nat) (alpha : ord),
  provable A d alpha -> PA_omega_theorem A d alpha.
Proof.
intros A d alpha H. unfold provable in H. destruct H as [t [[[H1 H2] H3] H4]].
apply nat_ge_case_type in H3. destruct H3 as [H3 | H3].
- assert (valid (deg_up d t)). simpl. auto.
  assert (ptree_formula (deg_up d t) = A) as X1. auto.
  assert (ptree_ord (deg_up d t) = alpha) as X2. auto.
  assert (ptree_deg (deg_up d t) = d) as X3. auto.
  rewrite <- X1, <- X2, <- X3.
  apply theorem_provable'. auto.
- rewrite <- H1, H4. rewrite H3.
  apply theorem_provable'. auto.
Qed.

Lemma ptree_ord_nf : forall (P : ptree), valid P -> nf (ptree_ord P).
Proof.
intros.
pose proof (theorem_provable' _ X).
apply (ord_nf _ _ _ X0).
Qed.

Lemma ptree_ord_nf_hyp : forall (alpha : ord) (P : ptree), alpha = ptree_ord P -> valid P -> nf alpha.
Proof.
intros.
rewrite H.
apply ptree_ord_nf.
apply X.
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
intros A d alpha T. induction T; auto;
try inversion IHT as [C1];
try destruct (and_bool_prop _ _ IHT1) as [C1 C2];
try destruct (and_bool_prop _ _ IHT2) as [C3 C4];
try destruct (and_bool_prop _ _ C1) as [C2 C3];
try destruct (and_bool_prop _ _ C2) as [C4 C5];
try destruct (and_bool_prop _ _ C4) as [C6 C7];
simpl in *; fold closed in *;
try rewrite C1; try rewrite C2; try rewrite C3; try rewrite C4;
try rewrite C5; try rewrite C6; try rewrite C7; try rewrite e;
try rewrite IHT1; try rewrite IHT2; auto.

- apply axiom_closed. auto.

- destruct (subst_one_var_free _ _ _ (projT2 c) IHT) as [LIST | LIST].
  + case (closed A) eqn:X.
    * reflexivity.
    * rewrite LIST. rewrite nat_eqb_refl. rewrite list_eqb_refl. auto.
  + apply free_list_closed in LIST. rewrite LIST. reflexivity.

- destruct (subst_one_var_free _ _ _ (projT2 c) C2) as [LIST | LIST].
  + case (closed A) eqn:X.
    * reflexivity.
    * rewrite LIST. rewrite nat_eqb_refl. rewrite list_eqb_refl. auto.
  + apply free_list_closed in LIST. rewrite LIST. reflexivity.

- destruct (subst_one_var_free A n zero (repr_closed 0) (H czero)) as [LIST | LIST]; simpl.
  + case (closed A) eqn:X; auto. rewrite LIST. rewrite nat_eqb_refl. auto.
  + apply free_list_closed in LIST. rewrite LIST. auto.

- pose proof (H czero). simpl in H0. destruct (and_bool_prop _ _ H0).
  rewrite H2.
  destruct (subst_one_var_free A n zero (repr_closed 0) H1) as [LIST | LIST]; simpl.
  + case (closed A) eqn:X; auto. rewrite LIST. rewrite nat_eqb_refl. auto.
  + apply free_list_closed in LIST. rewrite LIST. auto.

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