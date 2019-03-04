Require Import Omega.
Require Import Lia.
Notation "b1 && b2" := (andb b1 b2).
Notation "b1 || b2" := (orb b1 b2).

(*
###############################################################################
Section 1: Basic Facts about natural numbers and lists of numbers that we will
need later.
###############################################################################
*)


(* Some propositional propositions *)
(* *)
Lemma and_bool_symm : forall (b1 b2 : bool),
  b1 && b2 = true -> b2 && b1 = true.
Proof. intros. case_eq b1; case_eq b2; intros; rewrite H0,H1 in H; auto. Qed.

Lemma and_bool_prop : forall (b1 b2 : bool),
  b1 && b2 = true -> b1 = true /\ b2 = true.
Proof. intros. case_eq b1; case_eq b2; intros; rewrite H0,H1 in H; auto. Qed.


(* Basic properties of natural numbers *)
(* *)
Lemma eq_refl : forall (n : nat), n = n. Proof. auto. Qed.

Lemma leq_refl : forall (n : nat), n <= n. Proof. auto. Qed.

Lemma addends_leq : forall (m n p : nat), n + m = p -> n <= p /\ m <= p.
Proof. intros. omega. Qed.

Lemma beq_nat_refl : forall (n : nat), beq_nat n n = true.
Proof.
intros. induction n as [| n IH].
- auto.
- simpl. apply IH.
Qed.

Fixpoint bgeq_nat (n m : nat) : bool :=
match (n, m) with
| (0, 0) => true
| (S n', 0) => true
| (0, S m') => false
| (S n', S m') => bgeq_nat n' m'
end.

Lemma succ_geq : forall (n : nat), bgeq_nat (S n) n = true.
Proof.
intros. induction n.
- auto.
- rewrite <- IHn. auto.
Qed.

Definition lt_nat (n m : nat) : bool := (bgeq_nat m n) && negb (beq_nat n m).

Lemma lt_nat_irrefl : forall (n : nat), lt_nat n n = false.
Proof.
intros.
induction n.
- auto.
- rewrite <- IHn. auto.
Qed.

Lemma succ_beq : forall (n : nat), beq_nat n (S n) = false.
Proof.
intros. induction n.
- auto.
- rewrite <- IHn. auto.
Qed.

Definition nat_lt_aux' (n : nat) :=
  forall (m : nat), n < m -> lt_nat n m = true.

Lemma nat_lt_aux : forall (n : nat), nat_lt_aux' n.
Proof.
intros.
induction n.
- unfold nat_lt_aux'. intros. destruct m.
  + inversion H.
  + auto.
- unfold nat_lt_aux'. intros. destruct m.
  + inversion H.
  + unfold nat_lt_aux' in IHn.
    assert (n < m). { omega. }
    specialize IHn with m. apply IHn in H0.
    simpl. 
    inversion H. unfold lt_nat. rewrite (succ_geq (S n)). simpl.
    rewrite (succ_beq n). auto.
    unfold lt_nat. simpl.
    unfold lt_nat in H0. apply H0.
Qed.

Definition nat_beq_eq_nice (n : nat) :=
  forall (m : nat), beq_nat n m = true -> n = m.

Lemma nat_beq_eq' : forall (n : nat), nat_beq_eq_nice n.
Proof.
intros.
induction n.
- unfold nat_beq_eq_nice. intros. destruct m.
  + auto.
  + inversion H.
- unfold nat_beq_eq_nice. intros. destruct m.
  + inversion H.
  + simpl in H. unfold nat_beq_eq_nice in IHn. specialize IHn with m.
    apply IHn in H. rewrite H. auto.
Qed.

Lemma nat_beq_eq : forall (n m : nat), beq_nat n m = true -> n = m.
Proof. intros. apply (nat_beq_eq' n). auto. Qed.

Definition nat_trans (n : nat) := forall (m p : nat),
  lt_nat n m = true -> lt_nat m p = true -> lt_nat n p = true.

Lemma lt_nat_trans : forall (n : nat), nat_trans n.
Proof.
intros.
induction n.
- unfold nat_trans. intros. destruct p.
  + destruct m. 
    * inversion H.
    * inversion H0.
  + auto.
- unfold nat_trans. intros. destruct p.
  + destruct m.
    * inversion H.
    * inversion H0.
  + destruct m.
    * inversion H.
    * unfold nat_trans in IHn. specialize IHn with m p.
      assert (lt_nat n p = true).
      { apply IHn.
        { rewrite <- H. auto. }
        { rewrite <- H0. auto. } }
      rewrite <- H1. auto.
Qed.

Lemma lt_nat_asymm : forall (n m : nat),
  lt_nat n m = true -> ~(lt_nat m n = true).
Proof.
intros. unfold not. intros.
pose proof (lt_nat_trans n).
unfold nat_trans in H1.
specialize H1 with m n.
assert (lt_nat n n = true). { apply H1. apply H. apply H0. }
rewrite (lt_nat_irrefl n) in H2.
inversion H2.
Qed.

Lemma mult_right_incr_aux_aux : forall (n m p : nat),
  n < m -> n + p * (S n) < m + p * (S m).
Proof. intros. induction p; lia. Qed.

Lemma mult_left_incr_aux_aux : forall (n m p : nat),
  n < m -> p + n * (S p) < p + m * (S p).
Proof. intros. induction p; lia. Qed.

Lemma minus_n_0 : forall (n : nat), n - 0 = n.
Proof. intros. omega. Qed.

Lemma plus_n_0 : forall n:nat,
  n + 0 = n.
Proof.
intros n.
induction n as [| n' IH].
- auto.
- simpl.
  rewrite IH.
  auto.
Qed.

Lemma plus_n_1 : forall n:nat,
  n + 1 = S n.
Proof.
intros n.
induction n as [| n' IH].
- auto.
- simpl.
  rewrite IH.
  auto.
Qed.

Lemma plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
intros m n.
induction m as [| m' IH].
- auto.
- simpl.
  rewrite IH.
  auto.
Qed.

Lemma nat_exp_monot_lem : forall (n : nat), S n < 2 ^ n + 2 ^ n.
Proof.
intros.
induction n.
- auto.
- simpl. rewrite plus_n_0. lia.
Qed.

Lemma plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
intros m n.
induction m as [| m' IH].
- simpl.
  rewrite <- plus_n_O.
  auto.
- induction n as [| n' IHn].
  + simpl.
    rewrite <- plus_n_O.
    auto.
  + simpl.
    rewrite IH.
    simpl.
    rewrite plus_n_Sm.
    auto.
Qed.

Lemma plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
intros n m p.
induction n as [| n IHn].
- simpl.
  auto.
- simpl.
  rewrite IHn.
  auto.
Qed.

Lemma mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
intros n.
induction n as [| n' IH].
- auto.
- simpl.
  rewrite IH.
  auto.
Qed.

Lemma mult_1_r : forall (n : nat), n * 1 = n.
Proof.
intros n.
induction n as [| n' IH].
- auto.
- simpl. rewrite IH. auto.
Qed.

Lemma nat_semiconnex : forall (m n : nat), m < n \/ n < m \/ m = n.
Proof. intros. omega. Qed.

Lemma nat_transitive : forall (n n' n'' : nat), n < n' -> n' < n'' -> n < n''.
Proof. intros. omega. Qed.



(* Basic properties of lists and lists of nats *)
(* *)

Inductive list (X : Type) : Type :=
| nil : list X
| constr : X -> list X -> list X.

Arguments nil {X}.
Arguments constr {X} _ _.
Notation "x :: l" := (constr x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (constr x .. (constr y nil) ..).

Fixpoint concat {X : Type} (l_1 l_2 : list X) : list X :=
match l_1 with
| nil => l_2
| n :: l_1' => n :: (concat l_1' l_2)
end.

Fixpoint beq_list (l1 l2 : list nat) : bool :=
match l1,l2 with
| [],[] => true
| m :: l1',[] => false
| [], n :: l2' => false
| m :: l1', n :: l2' => beq_nat m n && beq_list l1' l2'
end.

Definition beq_list_eq_nice (l1 : list nat) :=
  forall (l2 : list nat), beq_list l1 l2 = true -> l1 = l2.

Lemma beq_list_eq' : forall (l1 : list nat), beq_list_eq_nice l1.
Proof.
intros. induction l1.
- unfold beq_list_eq_nice. intros. destruct l2; auto. inversion H.
- unfold beq_list_eq_nice. intros. destruct l2.
  + inversion H.
  + simpl in H. destruct (and_bool_prop _ _ H).
    unfold beq_list_eq_nice in IHl1. rewrite (IHl1 l2 H1).
    rewrite (nat_beq_eq _ _ H0). auto.
Qed.

Lemma beq_list_eq : forall (l1 l2 : list nat),
  beq_list l1 l2 = true -> l1 = l2.
Proof. intros. apply (beq_list_eq' l1). auto. Qed.

Fixpoint remove (n : nat) (l : list nat) : list nat :=
match l with
| nil => nil
| m :: l' => (match (beq_nat m n) with
                true => remove n l'
              | false => m :: (remove n l')
              end)
end.

Fixpoint member (n : nat) (l : list nat) : bool :=
match l with
| nil => false
| m :: l' => (match (beq_nat m n) with
                true => true
              | false => member n l'
              end)
end.

Fixpoint remove_dups (l : list nat) : list nat :=
match l with
| [] => []
| n :: l' => n :: (remove n (remove_dups l'))
end.

Lemma remove_concat : forall (n : nat) (l1 l2 : list nat),
  remove n (concat l1 l2) = concat (remove n l1) (remove n l2).
Proof.
intros.
induction l1; auto.
simpl. case_eq (beq_nat x n); intros.
- apply IHl1.
- rewrite IHl1. auto.
Qed.

Lemma concat_empty : forall (X : Type) (l1 l2 : list X),
  concat l1 l2 = [] -> l1 = [] /\ l2 = [].
Proof.
intros. split.
- destruct l1; auto. inversion H.
- destruct l2; auto. destruct l1; inversion H.
Qed.

Lemma remove_dups_empty : forall (l : list nat), remove_dups l = [] -> l = [].
Proof. intros. destruct l. auto. inversion H. Qed.

Lemma remove_order : forall (l : list nat) (n m : nat),
  remove n (remove m l) = remove m (remove n l).
Proof.
intros. induction l; auto.
destruct (beq_nat x n) eqn:Hn; destruct (beq_nat x m) eqn:Hm; simpl;
rewrite Hn; rewrite Hm; auto; simpl.
- rewrite Hn. apply IHl.
- rewrite Hm. apply IHl.
- rewrite Hn, Hm. rewrite IHl. auto.
Qed.

Lemma remove_twice : forall (l : list nat) (n : nat),
  remove n (remove n l) = remove n l.
Proof.
intros. induction l; auto.
destruct (beq_nat x n) eqn:Hn; simpl; rewrite Hn; auto.
simpl. rewrite Hn. rewrite IHl. auto.
Qed.

Lemma remove_dups_order : forall (l : list nat) (n : nat),
  remove n (remove_dups l) = remove_dups (remove n l).
Proof.
intros. induction l; auto.
case_eq (beq_nat x n); intros.
- assert (remove n (x :: l) = remove n l). { simpl. rewrite H. auto. }
  rewrite H0. rewrite <- IHl. pose proof (nat_beq_eq x n H).
  case (member x l); simpl; rewrite H; rewrite H1; rewrite remove_twice; auto.
- assert (remove n (x :: l) = x :: remove n l). { simpl. rewrite H. auto. }
  rewrite H0.
  case (member x l); intros; simpl;
  rewrite H; rewrite <- IHl; rewrite remove_order; auto.
Qed.

Lemma remove_n_n : forall (l : list nat) (n : nat),
  remove n (remove_dups (n :: l)) = remove n (remove_dups l).
Proof.
intros.
rewrite remove_dups_order.
simpl. rewrite beq_nat_refl.
rewrite <- remove_dups_order. auto.
Qed.

Lemma remove_n_dups_empty : forall (l : list nat) (n : nat),
  remove n (remove_dups l) = [] -> remove_dups l = [n] \/ remove_dups l = [].
Proof.
intros. induction l; auto.
destruct (beq_nat x n) eqn:Hn.
- simpl in H. rewrite Hn in H.
  pose proof (nat_beq_eq x n Hn) as Hx. rewrite Hx in H.
  rewrite remove_twice in H. apply IHl in H. destruct H.
  + simpl. left. rewrite H. rewrite Hx. simpl. rewrite beq_nat_refl. auto.
  + destruct IHl. 
    * rewrite H. auto.
    * rewrite H in H0. inversion H0.
    * left. simpl. rewrite H. rewrite Hx. auto.
- simpl in H. rewrite Hn in H. rewrite remove_order in H. inversion H.
Qed.

Lemma remove_dups_twice : forall (l : list nat),
  remove_dups (remove_dups l) = remove_dups l.
Proof.
intros. induction l; auto.
simpl. rewrite remove_dups_order. rewrite remove_twice.
rewrite <- remove_dups_order. rewrite IHl. auto.
Qed.

Lemma beq_nat_symm : forall (n m : nat),
  beq_nat m n = true -> beq_nat n m = true.
Proof. intros. apply nat_beq_eq in H. rewrite H. apply beq_nat_refl. Qed.

Lemma beq_nat_symm' : forall (n m : nat),
  beq_nat m n = false -> beq_nat n m = false.
Proof.
intros. case_eq (beq_nat n m); intros; auto.
apply beq_nat_symm in H0. rewrite H0 in H. inversion H.
Qed.

Lemma member_remove' : forall (l : list nat) (m n : nat),
  beq_nat m n = false ->
  member n l = true ->
  member n (remove m l) = true.
Proof.
intros.
induction l; auto.
inversion H0. case_eq (beq_nat x n); intros.
- apply nat_beq_eq in H1. rewrite H1. simpl. apply beq_nat_symm' in H.
  rewrite H. simpl. rewrite beq_nat_refl. auto.
- rewrite H1 in H2. simpl. rewrite H2. apply IHl in H2.
  case_eq (beq_nat x m); intros.
  + apply H2.
  + simpl. rewrite H1. apply H2.
Qed.

Lemma member_remove : forall (l : list nat) (m n : nat),
  beq_nat m n = false ->
  member n (remove m l) = false ->
  member n l = false.
Proof.
intros.
case_eq (member n l); intros.
- rewrite (member_remove' _ _ _ H H1) in H0. inversion H0.
- auto.
Qed.

Lemma member_remove_dups : forall (l : list nat) (n : nat),
  member n (remove_dups l) = false -> member n l = false.
Proof.
intros. induction l; auto.
simpl. simpl in H. destruct (beq_nat x n) eqn:Hn.
- inversion H.
- apply IHl. apply (member_remove _ x _ Hn), H.
Qed.

Lemma member_concat' : forall (l1 l2 : list nat) (n : nat),
  member n (concat l1 l2) = true ->
  member n l1 = true \/ member n l2 = true.
Proof.
intros. induction l1.
- right. apply H.
- simpl in H. simpl. destruct (beq_nat x n) eqn:Hx.
  + left. auto.
  + destruct (IHl1 H).
    * left. apply H0.
    * right. apply H0.
Qed.

Lemma member_concat : forall (l1 l2 : list nat) (n : nat),
  member n (concat l1 l2) = false ->
  member n l1 = false /\ member n l2 = false.
Proof.
intros. induction l1; auto.
simpl. case_eq (beq_nat x n); intros; simpl in H; rewrite H0 in H.
- inversion H.
- apply (IHl1 H).
Qed.

Lemma member_remove_dups_concat : forall (l1 l2 : list nat) (n : nat),
  member n (remove_dups (concat l1 l2)) = false ->
  member n l1 = false /\ member n l2 = false.
Proof.
intros.
apply member_concat.
apply member_remove_dups.
apply H.
Qed.

Lemma concat_member : forall (l l' : list nat) (n : nat),
  member n l = true -> member n (concat l l') = true.
Proof.
intros. destruct (member n (concat l l')) eqn:Hn; auto.
destruct (member_concat _ _ _ Hn). rewrite H0 in H. inversion H.
Qed.

Lemma remove_dups_member : forall (l : list nat) (n : nat),
  member n l = true -> member n (remove_dups l) = true.
Proof.
intros. destruct (member n (remove_dups l)) eqn:Hn; auto.
apply member_remove_dups in Hn. rewrite Hn in H. inversion H.
Qed.

Fixpoint repeated_element_n (l : list nat) (n : nat) : bool :=
match l with
| [] => true
| m :: l' => beq_nat m n && repeated_element_n l' n
end.

Lemma remove_dups_repeated_element : forall (l : list nat) (n : nat),
  repeated_element_n l n = true ->
  remove_dups l = [n] \/ l = [].
Proof.
intros. induction l; auto.
left. inversion H.
destruct (and_bool_prop _ _ H1).
destruct (IHl H2).
- simpl. rewrite H3. rewrite (nat_beq_eq _ _ H0).
  simpl. rewrite beq_nat_refl. auto.
- rewrite H3. rewrite (nat_beq_eq _ _ H0). auto.
Qed.

Lemma remove_dups_repeated_element' : forall (l : list nat) (n : nat),
  remove_dups l = [n] ->
  repeated_element_n l n = true.
Proof.
intros. induction l; auto.
simpl. inversion H. destruct (remove_n_dups_empty _ _ H2).
- rewrite beq_nat_refl, IHl; auto.
- rewrite beq_nat_refl. apply remove_dups_empty in H0. rewrite H0. auto.
Qed.

Lemma repeated_element_n_concat_aux : forall (l1 l2 : list nat) (m n : nat),
  repeated_element_n (concat l1 (m :: l2)) n = true ->
  beq_nat m n && repeated_element_n l2 n = true.
Proof.
intros. induction l1; simpl in H.
- apply H.
- apply IHl1. destruct (and_bool_prop _ _ H). apply H1.
Qed.

Lemma repeated_element_n_concat : forall (l1 l2 : list nat) (n : nat),
  repeated_element_n (concat l1 l2) n = true ->
  repeated_element_n l1 n = true /\ repeated_element_n l2 n = true.
Proof.
intros. split.
- induction l1; auto.
  simpl. simpl in H. destruct (and_bool_prop _ _ H).
  rewrite H0, (IHl1 H1). auto.
- induction l2; auto. simpl.
  apply (repeated_element_n_concat_aux l1 l2 x n), H.
Qed.














































































(*
###############################################################################
Section 2: Basic Facts about ordinals under epsilon_0.
###############################################################################
*)


(* We borrows Pierre Casteran's definition of ordinals, which can be found at
http://www.labri.fr/perso/casteran/, under "Ordinal notations and rpo".
The file that we borrow from is EPSILON0.v, in the epsilon0 folder.
In this framework, cons a n b represents  omega^a *(S n)  + b *)
(* *)
Inductive ord : Set :=
  Zero : ord
| cons : ord -> nat -> ord -> ord.

Inductive ord_lt : ord -> ord -> Prop :=
|  zero_lt : forall a n b, Zero < cons a n b
|  head_lt :
    forall a a' n n' b b', a < a' ->
                           cons a n b < cons a' n' b'
|  coeff_lt : forall a n n' b b', (n < n')%nat ->
                                 cons a n b < cons a n' b'
|  tail_lt : forall a n b b', b < b' ->
                             cons a n b < cons a n b'
where "o < o'" := (ord_lt o o') : cantor_scope.

Open Scope cantor_scope.

Definition leq (alpha beta : ord) := alpha = beta \/ alpha < beta.
Notation "alpha <= beta" := (leq alpha beta) : cantor_scope.

Definition semiconnex (alpha : ord) :=
  forall (beta : ord), alpha < beta \/ beta < alpha \/ alpha = beta.


Lemma ordinal_semiconnex : forall (alpha : ord), semiconnex alpha.
Proof.
intros alpha.
induction alpha.
- unfold semiconnex.
  induction beta.
  + right. right. auto.
  + left. apply zero_lt.
- unfold semiconnex.
  unfold semiconnex in IHalpha1.
  unfold semiconnex in IHalpha2.
  induction beta.
  + right. left. apply zero_lt.
  + destruct (IHalpha1 beta1).
    * left. apply head_lt. apply H.
    * destruct H.
      { right. left. apply head_lt. apply H. }
      { destruct (nat_semiconnex n n0).
        { left. rewrite H. apply coeff_lt. apply H0. }
        { destruct H0.
          { right. left. rewrite H. apply coeff_lt. apply H0. }
          { destruct (IHalpha2 beta2).
            { left. rewrite H. rewrite H0. apply tail_lt. apply H1. }
            { destruct H1.
              { right. left. rewrite H. rewrite H0. apply tail_lt. apply H1. }
              { right. right. rewrite H. rewrite H0. rewrite H1. auto. }}}}}
Qed.

Lemma ord_semiconnex : forall (alpha beta : ord),
  alpha < beta \/ beta < alpha \/ alpha = beta.
Proof. intros. apply (ordinal_semiconnex alpha). Qed.


Definition transitive (alpha : ord) := forall (beta gamma : ord),
  (beta < gamma -> alpha < beta -> alpha < gamma).

Lemma cons_lt_aux : forall (a a' b b' : ord) (n n' : nat),
  cons a n b < cons a' n' b' ->
  (a < a' \/ (a = a' /\ lt n n') \/ (a = a' /\ n = n' /\ b < b')).
Proof.
intros.
inversion H.
- left. apply H1.
- right. left. split.
  + auto.
  + apply H1.
- right. right. split.
  + auto.
  + split.
    * auto.
    * apply H1.
Qed.


Lemma lt_trans' : forall (alpha : ord), transitive alpha.
Proof.
intros.
induction alpha as [| a IHa n b IHb].
- unfold transitive.
  intros.
  destruct gamma as [| a'' n'' b''].
  + inversion H.
  + apply zero_lt.
- unfold transitive.
  intros.
  destruct beta as [| a' n' b'].
  + inversion H0.
  + destruct gamma as [| a'' n'' b''].
    * inversion H.
    * apply cons_lt_aux in H0. apply cons_lt_aux in H.
      { destruct H0. 
        { destruct H.
          { unfold transitive in IHa. specialize IHa with a' a''.
          apply head_lt. apply IHa. apply H. apply H0. }
        { destruct H.
          { unfold transitive in IHa. specialize IHa with a' a''.
            apply head_lt. destruct H. rewrite H in H0. apply H0. }
          { apply head_lt. unfold transitive in IHa. specialize IHa with a' a''.
            destruct H. rewrite <- H. apply H0. } } }
        destruct H0.
        { destruct H0. rewrite H0. destruct H.
          { apply head_lt. apply H. }
          { destruct H.
            { destruct H. rewrite <- H. apply coeff_lt.
              pose proof (nat_transitive n n' n''). apply H3. apply H1. apply H2. }
            { destruct H. destruct H2. rewrite H. rewrite <- H2.
              apply coeff_lt. apply H1. } } }
            destruct H. destruct H0. rewrite H0. apply head_lt. apply H.
            destruct H. destruct H. destruct H0. destruct H2.
            rewrite H0. rewrite H. rewrite H2. apply coeff_lt. apply H1.

            destruct H. destruct H. destruct H0. destruct H0.
            rewrite H. rewrite H0. destruct H1. rewrite H1.
            apply tail_lt. unfold transitive in IHb. specialize IHb with b' b''.
            apply IHb. apply H3. apply H2. }
Qed.


Lemma lt_trans : forall (alpha beta gamma : ord),
  alpha < beta -> beta < gamma -> alpha < gamma.
Proof.
intros.
pose proof (lt_trans' alpha).
unfold transitive in H1.
specialize H1 with beta gamma.
apply H1.
apply H0.
apply H.
Qed.

Lemma lt_irrefl : forall (alpha : ord), ~ (alpha < alpha).
Proof.
intros alpha H.
induction alpha as [Zero | a IHa n b IHb].
- inversion H.
- inversion H.
  + apply IHa. apply H1.
  + omega.
  + apply IHb. apply H1.
Qed.

Lemma lt_asymm : forall (alpha beta : ord),
  alpha < beta -> ~(beta < alpha).
Proof.
intros. intros H0.
pose proof (lt_trans alpha beta alpha H H0).
apply (lt_irrefl alpha H1).
Qed.





(* Here we define Cantor Normal Form, or more accurately, we copy
Pierre Casteran's definition *)
(* *)
Inductive nf : ord -> Prop :=
| zero_nf : nf Zero
| single_nf : forall a n, nf a ->  nf (cons a n Zero)
| cons_nf : forall a n a' n' b, a' < a ->
                             nf a ->
                             nf (cons a' n' b)->
                             nf (cons a n (cons a' n' b)).
Hint Resolve zero_nf single_nf cons_nf : ord.

Definition e0 : Type := {a : ord | nf a}.

Check cons Zero O (cons Zero O Zero).

Lemma Zero_nf : nf Zero.
Proof. apply zero_nf. Qed.

Check exist nf Zero Zero_nf.
Check exist.
Check exist nf.

Definition lt_e0 (alpha beta : e0) : Prop :=
  match (alpha, beta) with
  | (exist _ alpha' _, exist _ beta' _) => alpha' < beta'
  end.

Definition leq_e0 (alpha beta : e0) : Prop := lt_e0 alpha beta \/ alpha = beta.
Definition gt_e0 (alpha beta : e0) : Prop := lt_e0 beta alpha.
Definition geq_e0 (alpha beta : e0) : Prop := leq_e0 beta alpha.

Definition nat_ord (n : nat) : ord :=
  match n with
  | O => Zero
  | S n' => cons Zero n' Zero
  end.


(* defining boolean equality and less than, assuming normal form. *)
(* *)
Fixpoint ord_eqb (alpha beta : ord) : bool :=
match (alpha, beta) with
| (Zero, Zero) => true
| (_, Zero) => false
| (Zero, _) => false
| (cons a n b, cons a' n' b') =>
    (match (ord_eqb a a') with
    | false => false
    | true =>
        (match (beq_nat n n') with
        | false => false
        | true => ord_eqb b b'
        end)
    end)
end.


Fixpoint ord_ltb (alpha beta : ord) : bool :=
match alpha, beta with
| Zero, Zero => false
| _, Zero => false
| Zero, _ => true
| cons a n b, cons a' n' b' =>
    (match (ord_ltb a a', ord_eqb a a') with
    | (true, _) => true
    | (_, false) => false
    | (_, true) =>
        (match (lt_nat n n', lt_nat n' n) with
        | (true, _) => true
        | (_, true) => false
        | (_, _) => ord_ltb b b'
        end)
    end)
end.

Lemma ord_eqb_refl : forall (alpha : ord), ord_eqb alpha alpha = true.
Proof.
intros.
induction alpha.
- auto.
- simpl. rewrite IHalpha1. rewrite beq_nat_refl. rewrite IHalpha2. auto.
Qed.

Definition ord_lt_ltb_aux' (alpha : ord) :=
  forall (beta : ord), alpha < beta -> ord_ltb alpha beta = true.

Lemma ord_lt_ltb_aux :
  forall (alpha : ord), ord_lt_ltb_aux' alpha.
Proof.
intros.
induction alpha.
- unfold ord_lt_ltb_aux'.
  intros.
  destruct beta.
  + inversion H.
  + simpl. auto.
- unfold ord_lt_ltb_aux'.
  intros.
  destruct beta.
  + inversion H.
  + inversion H.
    * unfold ord_lt_ltb_aux' in IHalpha1. simpl.
      specialize IHalpha1 with beta1.
      apply IHalpha1 in H1.
      rewrite H1. auto.
    * simpl. case (ord_ltb beta1 beta1). auto. simpl.
      assert (ord_eqb beta1 beta1 = true). { apply (ord_eqb_refl beta1). }
      rewrite H7.
      assert (lt_nat n n0 = true). { apply (nat_lt_aux n). apply H1. }
      rewrite H8. auto.
    * unfold ord_lt_ltb_aux' in IHalpha2. simpl.
      specialize IHalpha2 with beta2.
      case (ord_ltb beta1 beta1). auto.
      assert (ord_eqb beta1 beta1 = true). { apply (ord_eqb_refl beta1). }
      rewrite H7.
      case (lt_nat n0 n0). auto.
      apply IHalpha2. apply H1.
Qed.

Lemma ord_lt_ltb : forall (alpha beta : ord),
  alpha < beta -> ord_ltb alpha beta = true.
Proof.
intros.
apply ord_lt_ltb_aux.
apply H.
Qed.

Lemma ltb_trans_aux : forall (a a' b b' : ord) (n n' : nat),
  ord_ltb (cons a n b) (cons a' n' b') = true ->
  (ord_ltb a a' = true \/ (ord_eqb a a' = true /\ lt_nat n n' = true) \/
  (ord_eqb a a' = true /\ n = n' /\ ord_ltb b b' = true)).
Proof.
intros.
inversion H.
case_eq (ord_ltb a a').
- auto.
- intros. rewrite H0 in H1. case_eq (ord_eqb a a').
  + intros. right. rewrite H2 in H1. case_eq (lt_nat n n').
    * intros. rewrite H3 in H1. auto.
    * intros. rewrite H3 in H1. case_eq (lt_nat n' n).
      { intros. rewrite H4 in H1. inversion H1. }
      { intros. rewrite H4 in H1. right. split. rewrite H1. auto. split.
        { pose proof (nat_semiconnex n n'). destruct H5.
          { pose proof (nat_lt_aux n). unfold nat_lt_aux' in H6.
            specialize H6 with n'. apply H6 in H5. rewrite H5 in H3.
            inversion H3. }
          { destruct H5.
            { pose proof (nat_lt_aux n'). unfold nat_lt_aux' in H6.
              specialize H6 with n. apply H6 in H5. rewrite H5 in H4.
              inversion H4. }
            { apply H5. } } }
        { auto. } }
  + intros. left. auto.
Qed.

Definition ord_eqb_eq_aux' (alpha : ord) := forall (beta : ord),
  ord_eqb alpha beta = true -> alpha = beta.

Lemma ord_eqb_eq_aux : forall (alpha : ord), ord_eqb_eq_aux' alpha.
Proof.
intros.
induction alpha.
- unfold ord_eqb_eq_aux'. intros. destruct beta.
  + auto.
  + inversion H.
- unfold ord_eqb_eq_aux'. intros. destruct beta.
  + inversion H.
  + inversion H.
    * case_eq (ord_eqb alpha1 beta1).
      { intros. unfold ord_eqb_eq_aux' in IHalpha1. specialize IHalpha1 with beta1.
        assert (alpha1 = beta1). { apply IHalpha1. apply H0. } rewrite H2.
        case_eq (beq_nat n n0).
        { intros. assert (n = n0). { apply (nat_beq_eq n n0 H3). } rewrite H4.
          case_eq (ord_eqb alpha2 beta2).
          { intros. assert (alpha2 = beta2). { apply IHalpha2. apply H5. }
            rewrite H6. auto. }
          { intros. rewrite H0 in H1. rewrite H3 in H1. rewrite H5 in H1.
            inversion H1. } }
        { intros. rewrite H0 in H1. rewrite H3 in H1. inversion H1. } }
      { intros. rewrite H0 in H1. inversion H1. }
Qed.

Lemma ord_eqb_eq : forall (alpha beta : ord),
  ord_eqb alpha beta = true -> alpha = beta.
Proof. intros. apply ord_eqb_eq_aux. apply H. Qed.

Lemma ord_eqb_symm : forall (alpha beta : ord),
  ord_eqb alpha beta = ord_eqb beta alpha.
Proof.
intros.
case_eq (ord_eqb alpha beta).
- intros. apply ord_eqb_eq in H. rewrite H. rewrite ord_eqb_refl. auto.
- case_eq (ord_eqb beta alpha).
  + intros. apply ord_eqb_eq in H. rewrite H in H0.
    rewrite ord_eqb_refl in H0. auto.
  + auto.
Qed.



Definition ord_ltb_trans_aux' (alpha : ord) := forall (beta gamma : ord),
  ord_ltb beta gamma = true -> ord_ltb alpha beta = true ->
  ord_ltb alpha gamma = true.



Lemma ord_ltb_trans_aux : forall (alpha : ord), ord_ltb_trans_aux' alpha.
Proof.
intros.
induction alpha as [| a IHa n b IHb].
- unfold ord_ltb_trans_aux'.
  intros.
  destruct gamma as [| a'' n'' b''].
  + destruct beta as [| a' n' b'].
    * inversion H.
    * inversion H.
  + auto.
- unfold ord_ltb_trans_aux'.
  intros.
  destruct beta as [| a' n' b'].
  + inversion H0.
  + destruct gamma as [| a'' n'' b''].
    * inversion H.
    * destruct (ltb_trans_aux a a' b b' n n' H0).
      { destruct (ltb_trans_aux a' a'' b' b'' n' n'' H).
        { unfold ord_ltb_trans_aux' in IHa. specialize IHa with a' a''.
          assert (ord_ltb a a'' = true). { apply IHa. apply H2. apply H1. }
          simpl. rewrite H3. auto. }
        { destruct H2. destruct H2. assert (a' = a'').
          { apply (ord_eqb_eq a' a''). apply H2. }
          { simpl. rewrite <- H4. rewrite H1. auto. }
          { destruct H2. destruct H3. assert (a' = a'').
            { apply (ord_eqb_eq a' a''). apply H2. }
            simpl. rewrite <- H5. rewrite H1. auto. } } }
      { destruct H1. destruct H1.
        assert (a = a'). { apply (ord_eqb_eq a a'). apply H1. }
        { destruct (ltb_trans_aux a' a'' b' b'' n' n'' H).
          { rewrite H3. simpl. rewrite H4. auto. }
          { destruct H4. destruct H4.
            { assert (a' = a''). { apply (ord_eqb_eq a' a''). apply H4. }
              simpl. case (ord_ltb a a''). auto.
              rewrite H3. rewrite H6. rewrite (ord_eqb_refl a'').
              assert (lt_nat n n'' = true).
              { apply (lt_nat_trans n n' n'' H2 H5). }
              rewrite H7. auto. }
            { destruct H4. destruct H5. simpl. case (ord_ltb a a''). auto.
              assert (a' = a''). { apply (ord_eqb_eq a' a''). apply H4. }
              rewrite H3. rewrite H7. rewrite (ord_eqb_refl a'').
              rewrite <- H5. rewrite H2. auto. } } }
      { destruct H1. destruct H2.
        destruct (ltb_trans_aux a' a'' b' b'' n' n'' H).
        assert (a = a'). { apply (ord_eqb_eq a a'). apply H1. }
        { simpl. rewrite H5. rewrite H4. auto. }
        { destruct H4. destruct H4.
          assert (a = a'). { apply (ord_eqb_eq a a'). apply H1. }
          assert (a' = a''). { apply (ord_eqb_eq a' a''). apply H4. }
          { simpl. case (ord_ltb a a''). auto. rewrite H6. rewrite H7.
            rewrite (ord_eqb_refl a''). rewrite H2. rewrite H5. auto. }
          { destruct H4. destruct H5. simpl. case (ord_ltb a a''). auto.
            assert (a = a'). { apply (ord_eqb_eq a a'). apply H1. }
            assert (a' = a''). { apply (ord_eqb_eq a' a''). apply H4. }
            rewrite H7. rewrite H8. rewrite (ord_eqb_refl a'').
            case (lt_nat n n''). auto. rewrite H2. rewrite H5.
            rewrite (lt_nat_irrefl n''). unfold ord_ltb_trans_aux' in IHb.
            specialize IHb with b' b''. apply IHb. apply H6. apply H3. } } } }
Qed.

Lemma ord_ltb_trans : forall (alpha beta gamma : ord),
  ord_ltb alpha beta = true -> ord_ltb beta gamma = true ->
  ord_ltb alpha gamma = true.
Proof. intros. apply (ord_ltb_trans_aux alpha beta gamma H0 H). Qed.


Lemma ord_ltb_irrefl : forall (alpha : ord), ord_ltb alpha alpha = false.
Proof.
intros.
induction alpha.
- auto.
- simpl.
  rewrite IHalpha1.
  rewrite (ord_eqb_refl alpha1).
  rewrite (lt_nat_irrefl n).
  rewrite IHalpha2.
  auto.
Qed.


Lemma ltb_asymm' : forall (alpha beta : ord),
  ord_ltb alpha beta = true -> ~(ord_ltb beta alpha = true).
Proof.
unfold not. intros.
pose proof (ord_ltb_trans alpha beta alpha H H0).
rewrite (ord_ltb_irrefl alpha) in H1.
inversion H1.
Qed.


Lemma ord_ltb_lt : forall (alpha beta : ord),
  ord_ltb alpha beta = true -> alpha < beta.
Proof.
intros.
pose proof (ordinal_semiconnex alpha).
unfold semiconnex in H0.
specialize H0 with beta.
destruct H0.
- apply H0.
- destruct H0.
  + apply ord_lt_ltb in H0. apply (ltb_asymm' alpha beta) in H. contradiction.
  + rewrite H0 in H. rewrite (ord_ltb_irrefl beta) in H. inversion H.
Qed.

Lemma ltb_asymm_aux : forall (alpha beta : ord),
  ~ (alpha < beta) -> ord_ltb alpha beta = false.
Proof.
intros. unfold not in H.
case_eq (ord_ltb alpha beta).
- intros. apply (ord_ltb_lt alpha beta) in H0. apply H in H0. inversion H0.
- auto.
Qed.

Lemma ltb_asymm : forall (alpha beta : ord),
  ord_ltb alpha beta = true -> ord_ltb beta alpha = false.
Proof.
intros.
apply ltb_asymm_aux.
apply lt_asymm.
apply ord_ltb_lt.
apply H.
Qed.

Lemma ltb_asymm2 : forall (alpha beta : ord),
  ord_ltb alpha beta = true -> ord_eqb alpha beta = false.
Proof.
intros.
case_eq (ord_eqb alpha beta).
- intros. apply ord_eqb_eq in H0. rewrite H0 in H.
  rewrite ord_ltb_irrefl in H. auto.
- auto.
Qed.


Lemma ord_semiconnex_bool : forall (alpha beta : ord),
  ord_ltb alpha beta = true \/ ord_ltb beta alpha = true \/
  ord_eqb alpha beta = true.
Proof.
intros.
pose proof (ordinal_semiconnex alpha).
unfold semiconnex in H.
specialize H with beta.
inversion H.
- left. apply ord_lt_ltb. apply H0.
- inversion H0.
  + right. left. apply ord_lt_ltb. apply H1.
  + right. right. rewrite H1. apply ord_eqb_refl.
Qed.




(* ord_add, ord_mult, and ord_exp will all assume normal form.
ord_2_exp is based on Pierre Casteran's more general definition of ordinal
exponentiation, restricted to when the base is 2. *)
(* *)
Fixpoint ord_add (alpha beta : ord) : ord :=
match alpha, beta with
| _, Zero => alpha
| Zero, _ => beta
| cons a n b, cons a' n' b' =>
    (match (ord_ltb a a') with
    | true => beta
    | false =>
      (match (ord_eqb a a') with
      | true => cons a' (n + n' + 1) b'
      | false => cons a n (ord_add b beta)
      end)
    end)
end.

Fixpoint ord_mult (alpha beta : ord) : ord :=
match alpha, beta with
| _, Zero => Zero
| Zero, _ => Zero
| cons a n b, cons Zero n' b' => cons a ((S n) * (S n') - 1) b
| cons a n b, cons a' n' b' => cons (ord_add a a') n' (ord_mult alpha b')
end.

Fixpoint ord_2_exp (alpha : ord) : ord :=
match alpha with
| Zero => cons Zero 0 Zero

| cons Zero n' _ => nat_ord (2 ^ (S n'))

| cons (cons Zero n Zero) 0 Zero =>
      cons (cons (cons Zero n Zero) 0 Zero) 0 Zero

| cons (cons a n b) n' b' =>
    ord_mult
      (cons (cons (cons a n b) n' Zero) 0 Zero)
      (ord_2_exp b')
end.




(* Here we show that addition and multiplication for ordinal numbers
agrees with the usual definitions for natural numbers *)
(* *)
Lemma ord_add_zero : forall (alpha : ord), ord_add alpha Zero = alpha.
Proof. intros. destruct alpha; auto. Qed.

Lemma ord_zero_add : forall (alpha : ord), ord_add Zero alpha = alpha.
Proof. intros. destruct alpha; auto. Qed.

Lemma ord_add_nat : forall (n m : nat),
  nat_ord (n + m) = ord_add (nat_ord n) (nat_ord m).
Proof.
intros n m.
induction m as [| m' IH].
- rewrite ord_add_zero.
  rewrite plus_n_0.
  auto.
- induction n as [| n' IHn].
  + simpl.
    auto.
  + simpl.
    rewrite <- (plus_n_1 m').
    rewrite plus_assoc.
    auto.
Qed.

Lemma nat_ord_0 : nat_ord 0 = Zero.
Proof. simpl. auto. Qed.


(* Some miscellaneous lemmas about ordinals *)
(* *)
Lemma nf_scalar : forall (a b : ord) (n n' : nat),
  nf (cons a n b) -> nf (cons a n' b).
Proof.
intros a b n n' H.
inversion H.
- apply single_nf. apply H1.
- apply cons_nf.
  + apply H3.
  + apply H4.
  + apply H5.
Qed.

Lemma nf_hered_third : forall (a b : ord) (n : nat),
  nf (cons a n b) -> nf b.
Proof.
intros a b n H.
destruct b as [Zero | a' n' b'].
- apply Zero_nf.
- destruct b' as [Zero | a'' n'' b''].
  + apply single_nf. inversion H. inversion H7. apply H9.
  + inversion H. apply H7.
Qed.

Lemma nf_hered_first : forall (a b : ord) (n : nat),
  nf (cons a n b) -> nf a.
Proof.
intros a b n H.
destruct b as [Zero | a' n' b'].
- inversion H. apply H1.
- inversion H. apply H6.
Qed.

Lemma zero_minimal : forall (alpha : ord), ~ (alpha < Zero).
intros alpha.
destruct alpha as [Zero | a n b].
- apply lt_irrefl.
- intros H. inversion H.
Qed.

Lemma nf_cons_decr' : forall (a a' b b' : ord) (n n' : nat),
  nf (cons a n (cons a' n' b')) -> cons a' n' b' < cons a n b.
Proof.
intros a a' b b' n n' H.
inversion H.
apply head_lt.
apply H3.
Qed.

Lemma nf_cons_decr : forall (a b : ord) (n : nat),
  nf (cons a n b) -> b < cons a n Zero.
Proof.
intros.
inversion H.
- apply zero_lt.
- apply head_lt.
  apply H3.
Qed.

Lemma cons_monot : forall (a b : ord) (n : nat),
  cons a 0 Zero <= cons a n b.
Proof.
intros a b n.
destruct n.
- destruct b as [Zero | a'' n'' b''].
  + unfold leq. left. auto.
  + unfold leq. right. apply tail_lt. apply zero_lt.
- unfold leq. right. apply coeff_lt. omega.
Qed.


Lemma omega_exp_incr : forall (a : ord), a < cons a 0 Zero.
Proof.
intros a.
induction a as [Zero | a' IHa' n' b' IHb'].
- apply zero_lt.
- apply head_lt.
  assert (cons a' 0 Zero <= cons a' n' b').
  { apply cons_monot. }
  inversion H.
  + rewrite <- H0. apply IHa'.
  + apply (lt_trans a' (cons a' 0 Zero) (cons a' n' b') IHa' H0).
Qed.

Lemma omega_exp_incr' : forall (a b : ord) (n : nat), a < cons a n b.
Proof.
intros a b n.
pose proof (omega_exp_incr a).
pose proof (cons_monot a b n).
destruct H0.
- rewrite H0 in H. apply H.
- apply (lt_trans a (cons a 0 Zero) (cons a n b) H H0).
Qed.



(* Carry over the ordinal arithmetic results to the e0 type *)
(* *)
Definition e0_ord (alpha : e0) : ord :=
match alpha with
| exist _ alpha' pf => alpha'
end.

Lemma nf_nat : forall (n : nat), nf (nat_ord n).
Proof.
induction n.
- unfold nat_ord.
  apply Zero_nf.
- unfold nat_ord.
  apply single_nf.
  apply Zero_nf.
Qed.

Definition nat_e0 (n : nat) : e0 := exist nf (nat_ord n) (nf_nat n).

Definition e0_eq (alpha : e0) (beta : e0) : bool :=
  ord_eqb (e0_ord alpha) (e0_ord beta).

Definition e0_lt (alpha : e0) (beta : e0) : bool :=
  ord_ltb (e0_ord alpha) (e0_ord beta).

Lemma nf_add_aux2 : forall (a a' a'' b b' b'' : ord) (n n' n'' : nat),
  cons a n b = ord_add (cons a' n' b') (cons a'' n'' b'') -> (a = a' \/ a = a'').
Proof.
intros a a' a'' b b' b'' n n' n''.
simpl.
case (ord_ltb a' a'').
- intros H. inversion H. right. auto.
- case (ord_eqb a' a'').
  + intros H. inversion H. right. auto.
  + intros H. inversion H. left. auto.
Qed.

Definition nf_add_aux' (alpha : ord) :=
  forall (beta : ord), nf alpha -> nf beta -> nf (ord_add alpha beta).

Lemma nf_add_aux : forall (alpha : ord), nf_add_aux' alpha.
Proof.
intros.
induction alpha.
- unfold nf_add_aux'.
  intros.
  simpl.
  destruct beta.
  + simpl. apply zero_nf.
  + apply H0.
- unfold nf_add_aux'.
  intros.
  simpl.
  destruct beta.
  + apply H.
  + remember (ord_ltb alpha1 beta1) as c1.
    case c1 as [T | F].
    * apply H0.
    * remember (ord_eqb alpha1 beta1) as c2.
      case c2 as [T | F].
      { apply (nf_scalar beta1 beta2 n0 (n + n0 + 1)). apply H0. }
      { assert (ord_ltb beta1 alpha1 = true).
        { pose proof (ord_semiconnex_bool alpha1 beta1). destruct H1.
          { rewrite H1 in Heqc1. inversion Heqc1. }
          { destruct H1. 
            { apply H1. }
            { rewrite <- Heqc2 in H1. inversion H1. } } }
        remember (ord_add alpha2 (cons beta1 n0 beta2)) as A.
        destruct A.
        { apply single_nf. inversion H. apply H3. apply H6. }
        { apply cons_nf.
          { destruct alpha2 as [| a'' n'' b''].
            { simpl in HeqA. assert (A1 = beta1). { inversion HeqA. auto. }
              rewrite H2. apply (ord_ltb_lt _ _ H1). }
            { destruct (ordinal_semiconnex a'' beta1).
              { apply (nf_add_aux2 A1 a'' beta1 A2 b'' beta2 n1 n'' n0) in HeqA.
                destruct HeqA.
                { rewrite H3. inversion H. apply H7. }
                { rewrite H3. apply (ord_ltb_lt _ _ H1). } }
              { apply (nf_add_aux2 A1 a'' beta1 A2 b'' beta2 n1 n'' n0) in HeqA.
                destruct HeqA.
                { rewrite H3. inversion H. apply H7. }
                { rewrite H3. apply (ord_ltb_lt _ _ H1). } } } }
          { inversion H. apply H3. apply H6. }
          { rewrite HeqA. unfold nf_add_aux' in IHalpha2.
            specialize IHalpha2 with (cons beta1 n0 beta2). apply IHalpha2.
            inversion H. apply Zero_nf. apply H7. apply H0. } } }
Qed.

Lemma nf_add : forall (alpha beta : ord),
  nf alpha -> nf beta -> nf (ord_add alpha beta).
Proof. intros. apply (nf_add_aux alpha). apply H. apply H0. Qed.

Lemma nf_multy_aux : forall (a a' b b' : ord) (n n' : nat),
  Zero < a' ->
  ord_mult (cons a n b) (cons a' n' b') =
  cons (ord_add a a') n' (ord_mult (cons a n b) b').
Proof.
intros.
simpl.
case_eq a'; intros.
- rewrite H0 in H. inversion H.
- auto.
Qed.


Definition add_right_nice (gamma : ord) := forall (alpha beta : ord),
  alpha < beta -> ord_add gamma alpha < ord_add gamma beta.

Definition add_right_nice2 (alpha gamma : ord) := forall (beta : ord),
  alpha < beta -> ord_add gamma alpha < ord_add gamma beta.


Lemma add_right_incr_aux : forall (gamma : ord), add_right_nice gamma.
Proof.
intros.
induction gamma as [| gamma1 IHgamma1 n_gamma gamma2 IHgamma2].
- unfold add_right_nice. intros. repeat rewrite ord_zero_add. apply H.
- unfold add_right_nice. intros. destruct alpha as [| alpha1 n_alpha alpha2].
  + rewrite ord_add_zero. destruct beta as [| beta1 n_beta beta2].
    * inversion H.
    * simpl.
      destruct (ord_semiconnex_bool gamma1 beta1) as [ H0 | [ H0 | H0 ] ].
      { rewrite H0. apply head_lt. apply (ord_ltb_lt _ _ H0). }
      { rewrite (ltb_asymm _ _ H0).
        rewrite ord_eqb_symm. rewrite (ltb_asymm2 _ _ H0).
        apply tail_lt. rewrite <- (ord_add_zero gamma2).
        assert (ord_add (ord_add gamma2 Zero) (cons beta1 n_beta beta2) =
                ord_add gamma2 (cons beta1 n_beta beta2)).
        { rewrite ord_add_zero. auto. } rewrite H1.
        unfold add_right_nice in IHgamma2.
        apply (IHgamma2 Zero (cons beta1 n_beta beta2) H). }
      { apply ord_eqb_eq in H0. rewrite H0.
        rewrite ord_ltb_irrefl. rewrite ord_eqb_refl. apply coeff_lt. omega. }

  + destruct beta as [| beta1 n_beta beta2].
    * inversion H.
    * simpl.
      destruct (ord_semiconnex_bool gamma1 alpha1) as [ a1 | [ a2 | a3 ] ].
      { rewrite a1.
        destruct (ord_semiconnex_bool gamma1 beta1) as [ b1 | [ b2 | b3 ] ].
        { rewrite b1. apply H. }
        { pose proof (ord_ltb_trans _ _ _ b2 a1). apply ord_ltb_lt in H0.
          inversion H.
          { apply (lt_asymm _ _ H2) in H0. contradiction. }
          { rewrite H5 in H0. apply lt_irrefl in H0. contradiction. }
          { rewrite H5 in H0. apply lt_irrefl in H0. contradiction. } }
        { apply (ord_eqb_eq gamma1 beta1) in b3. rewrite b3 in a1.
          apply ord_ltb_lt in a1. inversion H.
          { apply lt_asymm in a1. contradiction. }
          { rewrite H4 in a1. apply lt_irrefl in a1. contradiction. }
          { rewrite H4 in a1. apply lt_irrefl in a1. contradiction. } } }

      { rewrite (ltb_asymm alpha1 gamma1 a2).
        rewrite (ord_eqb_symm gamma1 alpha1).
        rewrite (ltb_asymm2 alpha1 gamma1 a2).
        destruct (ord_semiconnex_bool gamma1 beta1) as [ b1 | [ b2 | b3 ] ].
        { rewrite b1. apply head_lt. apply ord_ltb_lt. apply b1. }
        { rewrite (ltb_asymm beta1 gamma1 b2).
          rewrite (ord_eqb_symm gamma1 beta1).
          rewrite (ltb_asymm2 beta1 gamma1 b2).
          apply tail_lt.
          unfold add_right_nice in IHgamma2.
          apply IHgamma2. apply H. }
        { apply ord_eqb_eq in b3. rewrite b3. rewrite ord_ltb_irrefl.
          rewrite ord_eqb_refl. apply coeff_lt. omega. } }

      { apply ord_eqb_eq in a3. rewrite a3. 
        rewrite ord_ltb_irrefl. rewrite ord_eqb_refl.
        destruct (ord_semiconnex_bool gamma1 beta1) as [ b1 | [ b2 | b3 ] ].
        { rewrite a3 in b1. rewrite b1. apply head_lt.
          apply (ord_ltb_lt _ _ b1). }
        { rewrite a3 in b2. apply ord_ltb_lt in b2. inversion H.
          { apply lt_asymm in b2. contradiction. }
          { rewrite H4 in b2. apply lt_irrefl in b2. contradiction. }
          { rewrite H4 in b2. apply lt_irrefl in b2. contradiction. } }
        { apply ord_eqb_eq in b3. rewrite <- a3. rewrite b3.
          rewrite ord_ltb_irrefl. rewrite ord_eqb_refl.
          rewrite <- a3 in H. rewrite b3 in H. inversion H.
          { apply lt_irrefl in H1. contradiction. }
          { apply coeff_lt. lia. }
          { apply tail_lt. apply H1. } } }
Qed.

Lemma add_right_incr : forall (alpha beta gamma : ord),
  beta < gamma -> ord_add alpha beta < ord_add alpha gamma.
Proof. apply add_right_incr_aux. Qed.

Lemma add_right_incr_corr : forall (alpha beta : ord),
  Zero < beta -> alpha < ord_add alpha beta.
Proof.
intros.
pose proof (add_right_incr alpha Zero beta H).
rewrite (ord_add_zero alpha) in H0.
apply H0.
Qed.

Definition mult_right_nice (gamma : ord) := 
  gamma = Zero \/ forall (alpha beta : ord),
  alpha < beta -> nf beta -> ord_mult gamma alpha < ord_mult gamma beta.

Definition mult_right_nice2 (alpha gamma : ord) := 
  gamma = Zero \/ forall (beta : ord),
  alpha < beta -> nf beta -> ord_mult gamma alpha < ord_mult gamma beta.

Lemma mult_right_incr_aux : forall (gamma : ord), mult_right_nice gamma.
Proof.
intros.
induction gamma as [| gamma1 IHgamma1 n_gamma gamma2 IHgamma2].
- unfold mult_right_nice. left. auto.
- assert (forall (alpha : ord), mult_right_nice2 alpha
              (cons gamma1 n_gamma gamma2)).
  { intros. induction alpha as [| alpha1 IHalpha1 n_alpha alpha2 IHalpha2].
    { unfold mult_right_nice2. right. intros.
      destruct beta as [| beta1 n_beta beta2].
      { inversion H. }
      { destruct beta1.
        { simpl. destruct gamma1.
          { unfold nat_ord. apply zero_lt. }
          { apply zero_lt. } }
        { simpl. apply zero_lt. } } }
    { unfold mult_right_nice2. right. intros beta H nf_beta.
      destruct beta as [| beta1 n_beta beta2].
      { inversion H. }
      { destruct alpha1.
        { destruct beta1.
          { assert (beta2 = Zero). { inversion nf_beta. auto. inversion H3. }
            rewrite H0 in H. inversion H.
            { inversion H2. }
            { simpl. apply coeff_lt.
              rewrite minus_n_0. rewrite minus_n_0.
              apply mult_right_incr_aux_aux. apply H2. }
            { inversion H2. } }
          { simpl. apply head_lt. apply add_right_incr_corr. apply zero_lt. } }
        { destruct beta1.
          { inversion H. inversion H1. }
          { rewrite nf_multy_aux. rewrite nf_multy_aux.
            { inversion H.
              { apply head_lt. apply add_right_incr. apply H1. }
              { apply coeff_lt. apply H1. }
              { apply tail_lt. unfold mult_right_nice2 in IHalpha2.
                inversion IHalpha2.
                { inversion H9. }
                { apply (H9 beta2).
                  { apply H1. }
                  { apply (nf_hered_third _ _ _ nf_beta). } } } }
            { apply zero_lt. }
            { apply zero_lt. } } } } } }
  unfold mult_right_nice. right. intros alpha. unfold mult_right_nice2 in H.
  specialize H with alpha. destruct H. inversion H. apply H.
Qed.

Lemma mult_left_zero : forall (alpha : ord), ord_mult Zero alpha = Zero.
Proof. intros. destruct alpha; auto. Qed.

Lemma mult_right_incr : forall (alpha beta gamma : ord),
  alpha < beta -> Zero < gamma -> nf beta ->
  ord_mult gamma alpha < ord_mult gamma beta.
Proof.
intros.
pose proof (mult_right_incr_aux gamma).
unfold mult_right_nice in H2.
destruct H2.
- rewrite H2 in H0. inversion H0.
- apply (H2 _ _ H H1).
Qed.



Definition nf_mult_aux' (alpha : ord) := forall (beta : ord),
  nf alpha -> nf beta -> nf (ord_mult alpha beta).

Lemma nf_mult_aux : forall (alpha : ord), nf_mult_aux' alpha.
Proof.
intros.
induction alpha as [| a IHa n b IHb].
- unfold nf_mult_aux'. intros. destruct beta as [| a' n' b'].
  + auto.
  + auto.
- unfold nf_mult_aux'. intros. induction beta as [| a' IHa' n' b' IHb'].
  + auto.
  + assert (nf (cons (ord_add a a') n' (ord_mult (cons a n b) b'))).
    { assert (nf (ord_add a a')).
      { apply nf_add.
        { inversion H. apply H2. apply H5. }
        { inversion H0. apply H2. apply H5. } }
    { assert (ord_mult (cons a n b) b' < ord_mult (cons a n b) (cons a' n' Zero)).
      { apply mult_right_incr. apply nf_cons_decr.
        { apply H0. }
        { apply zero_lt. }
        { apply single_nf. apply (nf_hered_first _ _ _ H0). } }
      case_eq (ord_mult (cons a n b) b').
      { intros. apply single_nf. apply H1. }
      { intros a'' n'' b'' H3. apply cons_nf.
        { destruct b' as [| b1 n_b b2].
          { unfold ord_mult in H3. inversion H3. }
          { destruct b1 as [| b1' n_b' b2'].
            { simpl in H3. inversion H3. inversion H0.
              apply add_right_incr_corr. apply H10. }
           { rewrite nf_multy_aux in H3.
              { inversion H3. inversion H0.
                apply add_right_incr. apply H10. }
              { apply zero_lt. } } } }
      { apply nf_add.
        apply (nf_hered_first a b n H).
        apply (nf_hered_first a' b' n' H0). }
      { rewrite <- H3. apply IHb'. apply (nf_hered_third _ _ _ H0). } } } }
    destruct a' as [| a'' n'' b''].
    { simpl. apply (nf_scalar _ _ _ _ H). }
    { rewrite nf_multy_aux. apply H1. apply zero_lt. }
Qed.

Lemma nf_mult : forall (alpha beta : ord),
  nf alpha -> nf beta -> nf (ord_mult alpha beta).
Proof. intros. apply (nf_mult_aux alpha). apply H. apply H0. Qed.




Lemma one_right_mult_ident : forall (alpha : ord),
  alpha = ord_mult alpha (nat_ord 1).
Proof.
intros.
induction alpha as [| alpha1 IHalpha1 n_alpha alpha2 IHalpha2].
- auto.
- simpl. assert (n_alpha * 1 - 0 = n_alpha). { omega. } rewrite H. auto.
Qed.

Lemma ord_mult_monot : forall (alpha beta : ord),
  nat_ord 1 < beta -> nf beta -> Zero < alpha -> alpha < ord_mult alpha beta.
Proof.
intros.
destruct alpha as [| a n b].
- inversion H1.
- pose proof (mult_right_incr (nat_ord 1) beta (cons a n b) H H1 H0).
  rewrite <- one_right_mult_ident in H2.
  apply H2.
Qed.

Lemma ord_mult_nonzero : forall (alpha beta : ord),
  Zero < alpha -> Zero < beta -> nf beta -> Zero < ord_mult alpha beta.
Proof.
intros.
pose proof (mult_right_incr Zero beta alpha H0 H H1).
assert (Zero = ord_mult alpha Zero). { unfold ord_mult. case alpha; auto. }
rewrite H3.
apply H2.
Qed.


Lemma nf_2_exp : forall (alpha : ord), nf alpha -> nf (ord_2_exp alpha).
Proof.
intros alpha nf_alpha.
induction alpha as [| alpha1 IHalpha1 n_alpha alpha2 IHalpha2].
- simpl. apply single_nf. apply zero_nf.
- destruct alpha1 as [| a' n' b'].
  + simpl. apply nf_nat.
  + destruct a' as [| a'' n'' b''].
    * simpl. assert (b' = Zero).
      { apply nf_hered_first in nf_alpha. inversion nf_alpha.
        auto. inversion H2. }
      rewrite H. case n_alpha.
      { case_eq alpha2; intros.
        { repeat apply single_nf. apply zero_nf. }
        { rewrite <- H0. apply nf_mult.
          { repeat apply single_nf. apply zero_nf. }
          { apply IHalpha2. apply (nf_hered_third _ _ _ nf_alpha). } } }
      { intros. apply nf_mult.
        { repeat apply single_nf. apply zero_nf. }
        { apply IHalpha2. apply (nf_hered_third _ _ _ nf_alpha). } }
    * simpl. apply nf_mult.
      { apply single_nf, single_nf. apply (nf_hered_first _ _ _ nf_alpha). }
      { apply IHalpha2. apply (nf_hered_third _ _ _ nf_alpha). }
Qed.

Lemma nat_ord_eq : forall (n m : nat), (n < m)%nat -> nat_ord n < nat_ord m.
Proof.
intros.
induction n; destruct m.
- inversion H.
- simpl. apply zero_lt.
- inversion H.
- simpl. apply coeff_lt. omega.
Qed.




Lemma exp_geq_1 : forall (b : ord), nf b -> Zero < ord_2_exp b.
Proof.
intros b nf_b.
induction b as [| a' IHa' n' b' IHb'].
- simpl. apply zero_lt.
- destruct a' as [| a'' n'' b''].
  + simpl. assert (Zero = nat_ord 0). { auto. } rewrite H.
    apply nat_ord_eq. rewrite plus_n_0.
    pose proof (nat_exp_monot_lem n'). omega.
  + destruct a'' as [| a''' n''' b'''].
    * simpl. assert (b'' = Zero).
      { apply nf_hered_first in nf_b. inversion nf_b. auto. inversion H2. }
      rewrite H. case n'.
      { case_eq b'; intros.
        { apply zero_lt. }
        { rewrite <- H0. apply nf_hered_third in nf_b. apply ord_mult_nonzero.
          { apply zero_lt. }
          { apply (IHb' nf_b). }
          { apply (nf_2_exp _ nf_b). } } }
      { intros. apply nf_hered_third in nf_b. apply ord_mult_nonzero.
        { apply zero_lt. }
        { apply (IHb' nf_b). }
        { apply (nf_2_exp _ nf_b). } }
    * simpl. apply nf_hered_third in nf_b. apply ord_mult_nonzero.
      { apply zero_lt. }
      { apply (IHb' nf_b). }
      { apply (nf_2_exp _ nf_b). }
Qed.

Lemma ord_mult_exp_monot_aux1 : forall (beta : ord),
  Zero < beta -> (beta = nat_ord 1 \/ nat_ord 1 < beta).
Proof.
intros.
destruct (ord_semiconnex (nat_ord 1) beta).
- right. apply H0.
- destruct H0.
  + simpl in H0. inversion H0.
    { rewrite H1 in H. apply lt_irrefl in H. contradiction. }
    { inversion H3. }
    { inversion H3. }
    { inversion H3. }
  + left. auto.
Qed.

Lemma ord_mult_exp_monot_aux2 : forall (alpha beta : ord), nf beta ->
  (beta = nat_ord 1 \/ nat_ord 1 < beta) -> alpha <= ord_mult alpha beta.
Proof.
intros alpha beta nf_beta H.
unfold leq.
destruct H.
- left. rewrite H. rewrite <- one_right_mult_ident. auto.
- destruct alpha as [| a n b].
  + left. unfold ord_mult. case beta; auto.
  + right. apply ord_mult_monot. apply H. apply nf_beta. apply zero_lt.
Qed.


Lemma ord_mult_exp_monot' : forall (alpha b : ord),
  nf b -> alpha <= ord_mult alpha (ord_2_exp b).
Proof.
intros.
pose proof (exp_geq_1).
pose proof (ord_mult_exp_monot_aux1).
apply ord_mult_exp_monot_aux2.
- apply (nf_2_exp _ H).
- apply ord_mult_exp_monot_aux1.
  apply exp_geq_1.
  apply H.
Qed.

Lemma ord_mult_exp_monot : forall (alpha beta b : ord),
  nf b -> alpha < beta -> alpha < ord_mult beta (ord_2_exp b).
Proof.
intros.
pose proof (ord_mult_exp_monot' beta b H).
destruct H1.
- rewrite <- H1. apply H0.
- apply (lt_trans _ _ _ H0 H1).
Qed.


Lemma ord_2_exp_fp : forall (alpha : ord), nf alpha ->
  alpha < ord_2_exp alpha \/ alpha = cons (nat_ord 1) 0 Zero.
Proof.
intros alpha nf_alpha.
induction alpha as [| a IHa n b IHb].
- left. simpl. apply zero_lt.
- destruct a as [| a' n' b'].
  + left. assert (b = Zero). { inversion nf_alpha. auto. inversion H2. }
    rewrite H. simpl.
    simpl. assert (cons Zero n Zero = nat_ord (S n)). { auto. }
    rewrite H0. apply nat_ord_eq. rewrite plus_n_0.
    apply nat_exp_monot_lem.
  + simpl. destruct a' as [| a'' n'' b''].
    * destruct b' as [| a''' n''' b'''].
      { destruct n.
        { case_eq b; intros.
          { destruct n'.
            { right. auto. }
            { left. apply head_lt, head_lt, zero_lt. } }
          { left. rewrite <- H. apply ord_mult_exp_monot.
            { apply (nf_hered_third _ _ _ nf_alpha). }
            { repeat apply head_lt. apply zero_lt. } } }
        { left. apply ord_mult_exp_monot.
          { apply (nf_hered_third _ _ _ nf_alpha). }
          { repeat apply head_lt. apply omega_exp_incr'. } } }
      { apply nf_hered_first in nf_alpha. inversion nf_alpha. inversion H2. }
    * left. apply ord_mult_exp_monot.
      { apply (nf_hered_third _ _ _ nf_alpha). }
      { repeat apply head_lt. apply omega_exp_incr'. }
Qed.

Definition e0_pf (alpha : e0) : (nf (e0_ord alpha)) :=
match alpha with
| exist _ alpha' pf => pf
end.

Definition e0_add (alpha beta : e0) : e0 :=
  exist nf (ord_add (e0_ord alpha) (e0_ord beta))
    (nf_add (e0_ord alpha) (e0_ord beta) (e0_pf alpha) (e0_pf beta)).

Definition e0_mult (alpha beta : e0) : e0 :=
  exist nf (ord_mult (e0_ord alpha) (e0_ord beta))
    (nf_mult (e0_ord alpha) (e0_ord beta) (e0_pf alpha) (e0_pf beta)).

Close Scope cantor_scope.














































































(*
###############################################################################
Section 3: FOL machinery. Here we define and prove basic facts about terms
and formulas in first-order logic and the language of PA/PA_omega.
###############################################################################
*)

(* Definition of formulas in the language of PA/PA_omega*)
(* *)
Inductive term : Type :=
| zero : term
| succ : term -> term
| plus : term -> term -> term
| times : term -> term -> term
| var : nat -> term.

Inductive atomic_formula : Type :=
| equ : term -> term -> atomic_formula.

Inductive formula : Type :=
| atom : atomic_formula -> formula
| neg : formula -> formula
| lor : formula -> formula -> formula
| univ : nat -> formula -> formula.



(* Count number of connectives and quantifiers appearing in a formula *)
(* *)
Fixpoint num_conn (a : formula) : nat :=
match a with
| atom a' => 0
| neg a' => S (num_conn a')
| lor a1 a2 => S ((num_conn a1) + (num_conn a2))
| univ n a' => S (num_conn a')
end.



(* Check syntactic equality of formulas *)
(* *)
Fixpoint eq_term (s t : term) : bool :=
match (s, t) with
| (zero, zero) => true
| (succ s', succ t') => eq_term s' t'
| (plus s1 s2, plus t1 t2) => (eq_term s1 t1) && (eq_term s2 t2)
| (times s1 s2, times t1 t2) => (eq_term s1 t1) && (eq_term s2 t2)
| (var m, var n) => beq_nat m n
| (_,_) => false
end.

Compute eq_term zero zero.
Compute eq_term (succ zero) (succ zero).

Fixpoint eq_atom (a b : atomic_formula) : bool :=
match (a, b) with
| (equ s1 s2, equ t1 t2) => (eq_term s1 t1) && (eq_term s2 t2)
end.

Compute eq_atom (equ zero (succ zero)) (equ zero (succ zero)).

Fixpoint eq_f (a b : formula) : bool :=
match (a, b) with
| (atom a', atom b') => eq_atom a' b'
| (neg a', neg b') => eq_f a' b'
| (lor a1 a2, lor b1 b2) => (eq_f a1 b1) && (eq_f a2 b2)
| (univ m a', univ n b') => (beq_nat m n) && (eq_f a' b')
| (_, _) => false
end.

Compute eq_f (atom (equ zero (succ zero))) (atom (equ zero (succ zero))).

Lemma eq_term_refl : forall (t : term), eq_term t t = true.
Proof.
intros t.
induction t.
- auto.
- simpl. apply IHt.
- simpl. rewrite IHt1. apply IHt2.
- simpl. rewrite IHt1. apply IHt2.
- simpl. apply beq_nat_refl.
Qed.

Lemma eq_atom_refl : forall (a : atomic_formula), eq_atom a a = true.
Proof.
intros a.
destruct a as [t1 t2].
unfold eq_atom.
rewrite eq_term_refl.
apply eq_term_refl.
Qed.

Lemma eq_f_refl : forall (a : formula), eq_f a a = true.
Proof.
intros a.
induction a as [a | a IH | a1 IH1 a2 IH2 | n a IH].
- unfold eq_f. apply eq_atom_refl.
- simpl. apply IH.
- simpl. rewrite IH1. apply IH2.
- simpl. rewrite beq_nat_refl. apply IH.
Qed.



(* Given some term t, returns t+1 if the formula is closed, 0 otherwise *)
(* *)
Fixpoint eval (t : term) : nat :=
match t with
| zero => S O
| succ t_1 =>
    (match (eval t_1) with
    | O => O
    | S n => S (S n)
    end)
| plus t_1 t_2 =>
    (match (eval t_1, eval t_2) with
    | (O, O) => O
    | (S n, O) => O
    | (O, S m) => O
    | (S n, S m) => S (n + m)
    end)
| times t_1 t_2 =>
    (match (eval t_1, eval t_2) with
    | (O, O) => O
    | (S n, O) => O
    | (O, S m) => O
    | (S n, S m) => S (n * m)
    end)
| var n => O
end.

Compute eval zero.
Compute eval (var O).
Compute eval (succ zero).
Compute eval (succ (var O)).
Compute eval (plus (succ zero) (var O)).

Inductive ternary : Type :=
  | correct : ternary
  | incorrect : ternary
  | undefined : ternary.

Fixpoint represent (n : nat) : term :=
  match n with
  | O => zero
  | S n' => succ (represent n')
  end.

Compute represent 0.
Compute represent 1.
Compute represent 2.
Compute represent 5.



(* Given some atomic formula a, returns whether the statement is correct,
incorrect, or undefined (i.e. not closed) *)
Definition correctness (a : atomic_formula) : ternary :=
match a with
| equ t_1 t_2 =>
    (match (eval t_1, eval t_2) with
    | (O, O) => undefined
    | (S n, O) => undefined
    | (O, S m) => undefined
    | (S n, S m) =>
        (match (beq_nat (eval t_1) (eval t_2)) with
        | true => correct
        | false => incorrect
        end)
    end)
end.

Compute correctness (equ zero zero).
Compute correctness (equ zero (succ zero)).
Compute correctness (equ (plus (succ zero) (succ zero)) (succ (succ zero))).
Compute correctness (equ zero (var O)).


Definition correct_a (a : atomic_formula) : bool :=
match (correctness a) with
| correct => true
| _ => false
end.

Definition incorrect_a (a : atomic_formula) : bool :=
match (correctness a) with
| incorrect => true
| _ => false
end.



(* Free variable lists *)
(* *)
Fixpoint free_list_t (t : term) : list nat :=
match t with
| zero => nil
| succ t1 => free_list_t t1
| plus t1 t2 => remove_dups (concat (free_list_t t1) (free_list_t t2))
| times t1 t2 => remove_dups (concat (free_list_t t1) (free_list_t t2))
| var n => [n]
end.

Definition free_list_a (a : atomic_formula) : list nat :=
match a with
| equ t1 t2 => remove_dups (concat (free_list_t t1) (free_list_t t2))
end.

Fixpoint free_list (A : formula) : list nat :=
match A with
| atom a => free_list_a a
| neg B => free_list B
| lor B C => remove_dups (concat (free_list B) (free_list C))
| univ n B => remove n (free_list B)
end.





(* Some lemmas about free variable lists we will later use *)
(* *)
Lemma free_list_remove_dups_t : forall (t : term),
  free_list_t t = remove_dups (free_list_t t).
Proof. intros. induction t; auto; simpl; rewrite remove_dups_twice; auto. Qed.

Lemma free_list_remove_dups_a : forall (a : atomic_formula),
  free_list_a a = remove_dups (free_list_a a).
Proof. intros. destruct a. simpl. rewrite remove_dups_twice. auto. Qed.

Lemma free_list_remove_dups : forall (A : formula),
  free_list A = remove_dups (free_list A).
Proof.
intros. induction A; auto; simpl.
- apply free_list_remove_dups_a.
- rewrite remove_dups_twice. auto.
- rewrite <- remove_dups_order. rewrite <- IHA. auto.
Qed.

Lemma free_list_univ_empty : forall (A : formula) (n : nat),
  free_list (univ n A) = [] -> free_list A = [n] \/ free_list A = [].
Proof.
intros. induction A; auto.
- simpl in H. simpl.
  rewrite free_list_remove_dups_a in H.
  rewrite free_list_remove_dups_a.
  apply remove_n_dups_empty. apply H.
- simpl in H. simpl. apply remove_n_dups_empty. apply H.
- assert (free_list (univ n (univ n0 A)) = remove n (free_list (univ n0 A))).
  { auto. } rewrite H0 in H.
  rewrite free_list_remove_dups in H.
  apply remove_n_dups_empty in H.
  rewrite <- free_list_remove_dups in H. apply H.
Qed.


(* Determine if a formula is closed *)
(* *)
Fixpoint closed_t (t : term) : bool :=
match t with
| zero => true
| succ t1 => closed_t t1
| plus t1 t2 => closed_t t1 && closed_t t2
| times t1 t2 => closed_t t1 && closed_t t2
| var n => false
end.

Definition closed_a (a : atomic_formula) : bool :=
  match a with
  | equ t1 t2 => closed_t t1 && closed_t t2
  end.

Fixpoint closed (A : formula) : bool :=
match A with
| atom a => closed_a a
| neg B => closed B
| lor B C => closed B && closed C
| univ n B =>
  (match (closed B) with
   | true => true
   | false =>
    (match free_list B with
    | [] => false
    | m :: l => beq_nat m n && beq_list l []
    end)
  end)
end.

Lemma closed_univ' : forall (B : formula) (n : nat),
  closed (univ n B) = true -> closed B = false -> free_list B = [n].
Proof.
intros.
inversion H.
rewrite H0 in H2.
destruct (free_list B) eqn:HB.
- inversion H2.
- destruct (and_bool_prop _ _ H2).
  apply nat_beq_eq in H1. apply beq_list_eq in H3. rewrite H1, H3. auto.
Qed.

Lemma closed_univ : forall (B : formula) (m : nat),
  closed (univ m B) = true -> closed B = true \/ free_list B = [m].
Proof.
intros. destruct (closed B) eqn:HB.
- left. auto.
- right. apply (closed_univ' _ _ H HB).
Qed.






(* unsure if these lemmas will be necessary/useful *)
(* *)
Lemma free_list_closed_t : forall (t : term),
  free_list_t t = [] -> closed_t t = true.
Proof.
intros.
induction t; auto.
- simpl. simpl in H. apply remove_dups_empty in H.
  destruct (concat_empty _ _ _ H).
  rewrite (IHt1 H0). rewrite (IHt2 H1). auto.
- simpl. simpl in H. apply remove_dups_empty in H.
  destruct (concat_empty _ _ _ H).
  rewrite (IHt1 H0). rewrite (IHt2 H1). auto.
- inversion H.
Qed.

Lemma free_list_closed_a : forall (a : atomic_formula),
  free_list_a a = [] -> closed_a a = true.
Proof.
intros. destruct a as [t1 t2]. simpl. simpl in H.
apply remove_dups_empty in H. destruct (concat_empty _ _ _ H).
rewrite (free_list_closed_t _ H0). rewrite (free_list_closed_t _ H1). auto.
Qed.

Lemma free_list_closed : forall (A : formula),
  free_list A = [] -> closed A = true.
Proof.
intros. induction A; auto; simpl in H.
- simpl. apply free_list_closed_a, H.
- simpl. destruct (concat_empty _ _ _ (remove_dups_empty _ H)).
  rewrite IHA1, IHA2.
  + auto.
  + apply H1.
  + apply H0.
- rewrite free_list_remove_dups in H.
  destruct (remove_n_dups_empty _ _ H).
  + rewrite <- free_list_remove_dups in H0. simpl. destruct (closed A) eqn:HA.
    * auto.
    * rewrite H0. rewrite beq_nat_refl. auto.
  + simpl. rewrite IHA.
    * auto.
    * rewrite <- free_list_remove_dups in H0. auto.
Qed.

Lemma closed_free_list_t : forall (t : term),
  closed_t t = true -> free_list_t t = [].
Proof.
intros.
induction t; auto.
- simpl in H. simpl.
  case_eq (closed_t t1); case_eq (closed_t t2); intros Ht2 Ht1.
  + rewrite (IHt1 Ht1). rewrite (IHt2 Ht2). auto.
  + rewrite Ht1 in H. rewrite Ht2 in H. inversion H.
  + rewrite Ht1 in H. rewrite Ht2 in H. inversion H.
  + rewrite Ht1 in H. rewrite Ht2 in H. inversion H.
- simpl in H. simpl.
  case_eq (closed_t t1); case_eq (closed_t t2); intros Ht2 Ht1.
  + rewrite (IHt1 Ht1). rewrite (IHt2 Ht2). auto.
  + rewrite Ht1 in H. rewrite Ht2 in H. inversion H.
  + rewrite Ht1 in H. rewrite Ht2 in H. inversion H.
  + rewrite Ht1 in H. rewrite Ht2 in H. inversion H.
- inversion H.
Qed.

Lemma closed_free_list_a : forall (a : atomic_formula),
  closed_a a = true -> free_list_a a = [].
Proof.
intros. destruct a as [t1 t2].
simpl. simpl in H.
destruct (and_bool_prop _ _ H).
rewrite (closed_free_list_t _ H0), (closed_free_list_t _ H1). auto.
Qed.

Lemma closed_free_list : forall (A : formula),
  closed A = true -> free_list A = [].
Proof.
intros. induction A; auto; simpl.
- simpl in H. apply closed_free_list_a, H.
- simpl in H. destruct (and_bool_prop _ _ H).
  rewrite (IHA1 H0). rewrite (IHA2 H1). auto.
- destruct (closed_univ _ _ H).
  + rewrite (IHA H0). auto.
  + rewrite H0. simpl. rewrite beq_nat_refl. auto.
Qed.





(* Defining substitution of a term t for all free occurrences of a
   variable x_n in a formula f *)
(* *)
Fixpoint substitution_t (T : term) (n : nat) (t : term) : term :=
match T with
| zero => T
| succ T_1 => succ (substitution_t T_1 n t)
| plus T_1 T_2 => plus (substitution_t T_1 n t) (substitution_t T_2 n t)
| times T_1 T_2 => times (substitution_t T_1 n t) (substitution_t T_2 n t)
| var m =>
    (match (beq_nat m n) with
    | true => t
    | false => T
    end)
end.

Definition substitution_a (a : atomic_formula) (n : nat) (t : term)
  : atomic_formula :=
match a with
  equ t_1 t_2 => equ (substitution_t t_1 n t) (substitution_t t_2 n t)
end.

Fixpoint substitution (A : formula) (n : nat) (t : term) : formula :=
match A with
| atom a => atom (substitution_a a n t)
| neg B => neg (substitution B n t)
| lor B C => lor (substitution B n t) (substitution C n t)
| univ m B => 
    (match (beq_nat m n) with
    | true => A
    | false => univ m (substitution B n t)
    end)
end.








(* this will probably be needed in s=t substitution lemma *)
Lemma subst_remove_t : forall (T t : term) (n : nat),
  closed_t t = true ->
  free_list_t (substitution_t T n t) = remove n (free_list_t T).
Proof.
intros. induction T; auto.
- simpl. rewrite IHT1, IHT2.
  rewrite remove_dups_order. rewrite remove_concat. auto.
- simpl. rewrite IHT1, IHT2.
  rewrite remove_dups_order. rewrite remove_concat. auto.
- simpl. case_eq (beq_nat n0 n); intros; auto.
  apply closed_free_list_t, H.
Qed.

Lemma subst_remove_a : forall (a : atomic_formula) (n : nat) (t : term),
  closed_t t = true ->
  free_list_a (substitution_a a n t) = remove n (free_list_a a).
Proof.
intros. destruct a as [t1 t2]. simpl.
rewrite (subst_remove_t t1 _ _ H). rewrite (subst_remove_t t2 _ _ H).
rewrite remove_dups_order. rewrite remove_concat. auto.
Qed.

Lemma subst_remove : forall (A : formula) (n : nat) (t : term),
  closed_t t = true ->
  free_list (substitution A n t) = remove n (free_list A).
Proof.
intros. induction A; auto; simpl.
- rewrite (subst_remove_a _ _ _ H). auto.
- rewrite IHA1, IHA2.
  rewrite remove_dups_order. rewrite remove_concat. auto.
- destruct (beq_nat n0 n) eqn:Hn.
  + rewrite (nat_beq_eq _ _ Hn). rewrite remove_twice. auto.
  + simpl. rewrite IHA. apply remove_order.
Qed.

Lemma one_var_free_lemma_a : forall (a : atomic_formula) (n : nat) (t : term),
  closed_t t = true ->
  free_list_a a = [n] ->
  closed_a (substitution_a a n t) = true.
Proof.
intros.
apply free_list_closed_a. 
rewrite (subst_remove_a _ _ _ H).
rewrite H0. simpl. rewrite beq_nat_refl. auto.
Qed.

Lemma one_var_free_lemma : forall (A : formula) (n : nat) (t : term),
  closed_t t = true ->
  free_list A = [n] ->
  closed (substitution A n t) = true.
Proof.
intros.
apply free_list_closed.
rewrite (subst_remove _ _ _ H).
rewrite H0. simpl. rewrite beq_nat_refl. auto.
Qed.



(* closed atomic formulas are either correct or incorrect. *)
(* *)
Lemma eval_succ_lemma : forall (s : term), eval (succ s) > 0 -> eval s > 0.
Proof.
intros.
simpl in H.
case_eq (eval s); intros.
- rewrite H0 in H. inversion H.
- omega.
Qed.

Lemma eval_plus_lemma : forall (t1 t2 : term),
  eval (plus t1 t2) > 0 -> eval t1 > 0 /\ eval t2 > 0.
Proof.
intros.
simpl in H.
case_eq (eval t1); case_eq (eval t2); intros;
rewrite H0 in H; rewrite H1 in H; inversion H; split; omega.
Qed.

Lemma eval_times_lemma : forall (t1 t2 : term),
  eval (times t1 t2) > 0 -> eval t1 > 0 /\ eval t2 > 0.
Proof.
intros.
simpl in H.
case_eq (eval t1); case_eq (eval t2); intros;
rewrite H0 in H; rewrite H1 in H; inversion H; split; omega.
Qed.

Lemma eval_closed : forall (t : term), eval t > 0 -> closed_t t = true.
Proof.
intros. induction t; auto.
- simpl. apply IHt. apply eval_succ_lemma. apply H.
- simpl. destruct (eval_plus_lemma _ _ H).
  rewrite (IHt1 H0). rewrite (IHt2 H1). auto.
- simpl. destruct (eval_times_lemma _ _ H).
  rewrite (IHt1 H0). rewrite (IHt2 H1). auto.
- inversion H.
Qed.

Lemma closed_eval : forall (t : term), closed_t t = true -> eval t > 0.
Proof.
intros. induction t; auto.
- simpl in H. apply IHt in H. simpl. destruct (eval t).
  + inversion H.
  + omega.
- simpl in H. case_eq (closed_t t1); case_eq (closed_t t2); intros Ht2 Ht1.
  + simpl. apply IHt1 in Ht1. apply IHt2 in Ht2.
    destruct (eval t1); destruct (eval t2).
    * inversion Ht1.
    * inversion Ht1.
    * inversion Ht2.
    * omega.
  + rewrite Ht1 in H. rewrite Ht2 in H. inversion H.
  + rewrite Ht1 in H. rewrite Ht2 in H. inversion H.
  + rewrite Ht1 in H. rewrite Ht2 in H. inversion H.
- simpl in H. case_eq (closed_t t1); case_eq (closed_t t2); intros Ht2 Ht1.
  + simpl. apply IHt1 in Ht1. apply IHt2 in Ht2.
    destruct (eval t1); destruct (eval t2).
    * inversion Ht1.
    * inversion Ht1.
    * inversion Ht2.
    * lia.
  + rewrite Ht1 in H. rewrite Ht2 in H. inversion H.
  + rewrite Ht1 in H. rewrite Ht2 in H. inversion H.
  + rewrite Ht1 in H. rewrite Ht2 in H. inversion H.
- inversion H.
Qed.

Lemma correctness_decid_aux1 : forall (s t : term),
  closed_t s = true ->
  closed_t t = true ->
  correctness (equ s t) = correct \/ correctness (equ s t) = incorrect.
Proof.
intros s t Hs Ht. apply closed_eval in Hs. apply closed_eval in Ht. simpl.
destruct (eval s); destruct (eval t).
- inversion Hs.
- inversion Hs.
- inversion Ht.
- destruct (beq_nat (S n) (S n0)); auto.
Qed.

Lemma correctness_decid_aux2 : forall (s t : term),
  closed_t s = true ->
  closed_t t = true ->
  correct_a (equ s t) = true \/ incorrect_a (equ s t) = true.
Proof.
intros s t Hs Ht.
destruct (correctness_decid_aux1 _ _ Hs Ht).
- left. unfold correct_a. rewrite H. auto.
- right. unfold incorrect_a. rewrite H. auto.
Qed.

Lemma correctness_decid : forall (a : atomic_formula),
  closed_a a = true ->
  correct_a a = true \/ incorrect_a a = true.
Proof.
intros. destruct a as [t1 t2].
apply correctness_decid_aux2; unfold closed_a in H.
- destruct (closed_t t1); auto.
- destruct (closed_t t2); auto. destruct (closed_t t1); auto.
Qed.






























































































(*
###############################################################################
Section 4: Axioms and Rules of inference of PA_omega
###############################################################################
*)

(* Axioms of PA_omega *)
(* *)
Definition PA_omega_axiom (a : formula) : bool :=
match a with
| atom a' => correct_a a'
| neg (atom a') => incorrect_a a'
| _ => false
end.




(* A theorem of PA_omega is either an axiom, or the result of applying a rule
    of inference to another theorem *)
(* *)
Inductive PA_omega_theorem : formula -> Prop :=
| axiom : forall (A : formula),
    PA_omega_axiom A = true ->
    PA_omega_theorem A



| exchange1 : forall (A B : formula),
    PA_omega_theorem (lor A B) ->
    PA_omega_theorem (lor B A)

| exchange2 : forall (C A B : formula),
    PA_omega_theorem (lor (lor C A) B) ->
    PA_omega_theorem (lor (lor C B) A)

| exchange3 : forall (A B D : formula),
    PA_omega_theorem (lor (lor A B) D) ->
    PA_omega_theorem (lor (lor B A) D)

| exchange4 : forall (C A B D : formula),
    PA_omega_theorem (lor (lor (lor C A) B) D) ->
    PA_omega_theorem (lor (lor (lor C B) A) D)

| contraction1 : forall (A : formula),
    PA_omega_theorem (lor A A) ->
    PA_omega_theorem A

| contraction2 : forall (A D : formula),
    PA_omega_theorem (lor A (lor A D)) ->
    PA_omega_theorem (lor A D)



| weakening : forall (A D : formula),
    closed A = true ->
    PA_omega_theorem D ->
    PA_omega_theorem (lor A D)

| demorgan1 : forall (A B : formula),
    PA_omega_theorem (neg A) ->
    PA_omega_theorem (neg B) ->
    PA_omega_theorem (neg (lor A B))

| demorgan2 : forall (A B D : formula),
    PA_omega_theorem (lor (neg A) D) ->
    PA_omega_theorem (lor (neg B) D) ->
    PA_omega_theorem (lor (neg (lor A B)) D)

| negation1 : forall (A : formula),
    PA_omega_theorem A ->
    PA_omega_theorem (neg (neg A))

| negation2 : forall (A D : formula),
    PA_omega_theorem (lor A D) ->
    PA_omega_theorem (lor (neg (neg A)) D)

| quantification1 : forall (A : formula) (n : nat) (t : term),
    closed_t t = true ->
    PA_omega_theorem (neg (substitution A n t)) ->
    PA_omega_theorem (neg (univ n A))

| quantification2 : forall (A D : formula) (n : nat) (t : term),
    closed_t t = true ->
    PA_omega_theorem (lor (neg (substitution A n t)) D) ->
    PA_omega_theorem (lor (neg (univ n A)) D)


| w_rule1 : forall (A : formula) (n : nat)
  (g : forall (m : nat),
      PA_omega_theorem (substitution A n (represent m))),
  PA_omega_theorem (univ n A)

| w_rule2 : forall (A D : formula) (n : nat)
  (g : forall (m : nat),
    PA_omega_theorem (lor (substitution A n (represent m)) D)),
  PA_omega_theorem (lor (univ n A) D)



| cut1 : forall (C A : formula),
    PA_omega_theorem (lor C A) ->
    PA_omega_theorem (neg A) ->
    PA_omega_theorem C

| cut2 : forall (A D : formula),
    PA_omega_theorem A ->
    PA_omega_theorem (lor (neg A) D) ->
    PA_omega_theorem D

| cut3 : forall (C A D : formula),
    PA_omega_theorem (lor C A) ->
    PA_omega_theorem (lor (neg A) D) ->
    PA_omega_theorem (lor C D).





(* Extended example of using the w_rule to show "forall x (x = x)"
   is a theorem of PA_omega *)
(* *)
Lemma equ_refl_aux1 : forall (t : term),
  eval t > 0 -> correctness (equ t t) = correct.
Proof.
intros.
case_eq (eval t); intros.
- rewrite H0 in H. inversion H.
- unfold correctness. rewrite H0. rewrite beq_nat_refl. auto.
Qed.

Lemma equ_refl_aux2 : forall (t : term),
  eval t > 0 -> correct_a (equ t t) = true.
Proof.
intros.
pose proof (equ_refl_aux1 t H).
unfold correct_a. rewrite H0. auto.
Qed.

Lemma eval_represent : forall (n : nat),
  eval (represent n) > 0.
Proof.
intros.
induction n.
- auto.
- simpl. case_eq (eval (represent n)); intros.
  + rewrite H in IHn. inversion IHn.
  + omega.
Qed.

Lemma equ_refl : forall (m : nat),
  PA_omega_theorem (atom (equ (represent m) (represent m))).
Proof.
intros.
apply axiom.
simpl.
apply equ_refl_aux2.
apply eval_represent.
Qed.

Lemma w_rule_exmp : forall (n : nat),
  PA_omega_theorem (univ n (atom (equ (var n) (var n)))).
Proof.
intros.
apply w_rule1. simpl. rewrite beq_nat_refl.
apply equ_refl.
Qed.




(* Show that PA_omega proves the associativity laws *)
(* *)
Lemma associativity1 : forall (c a b : formula),
  PA_omega_theorem (lor (lor c a) b) ->
  PA_omega_theorem (lor c (lor a b)).
Proof.
intros.
apply exchange3 in H.
apply exchange2 in H.
apply exchange1 in H.
apply H.
Qed.

Lemma associativity2 : forall (c a b : formula),
  PA_omega_theorem (lor c (lor a b)) ->
  PA_omega_theorem (lor (lor c a) b).
Proof.
intros.
apply exchange1 in H.
apply exchange2 in H.
apply exchange3 in H.
apply H.
Qed.


(* Other miscellaneous lemmas we will need in the next section. *)
(* *)
Lemma correct_correctness : forall (a : atomic_formula),
  correct_a a = true -> correctness a = correct.
Proof.
intros. unfold correct_a in H.
case_eq (correctness a); auto; intros; rewrite H0 in H; inversion H.
Qed.

Lemma incorrect_correctness : forall (a : atomic_formula),
  incorrect_a a = true -> correctness a = incorrect.
Proof.
intros. unfold incorrect_a in H.
case_eq (correctness a); auto; intros; rewrite H0 in H; inversion H.
Qed.

Lemma correct_eval : forall (s t : term),
  correct_a (equ s t) = true -> eval s > 0 /\ eval t > 0.
Proof.
intros.
assert (correctness (equ s t) = correct).
{ apply correct_correctness. apply H. }
unfold correct_a in H.
rewrite H0 in H.
unfold correctness in H0.
case_eq (eval s); case_eq (eval t); intros;
rewrite H1 in H0; rewrite H2 in H0; inversion H0;
split; omega.
Qed.

Lemma incorrect_eval : forall (s t : term),
  incorrect_a (equ s t) = true -> eval s > 0 /\ eval t > 0.
Proof.
intros.
assert (correctness (equ s t) = incorrect).
{ apply incorrect_correctness. apply H. }
unfold incorrect_a in H.
rewrite H0 in H.
unfold correctness in H0.
case_eq (eval s); case_eq (eval t); intros;
rewrite H1 in H0; rewrite H2 in H0; inversion H0;
split; omega.
Qed.

Lemma correct_closed : forall (a : atomic_formula),
  correct_a a = true -> closed_a a = true.
Proof.
intros. case_eq a. intros t1 t2 Ha. rewrite Ha in H. clear Ha. simpl.
destruct (correct_eval _ _ H).
apply eval_closed in H0. rewrite H0.
apply eval_closed in H1. rewrite H1. auto.
Qed.

Lemma incorrect_closed : forall (a : atomic_formula),
  incorrect_a a = true -> closed_a a = true.
Proof.
intros. case_eq a. intros t1 t2 Ha. rewrite Ha in H. clear Ha. simpl.
destruct (incorrect_eval _ _ H).
apply eval_closed in H0. rewrite H0.
apply eval_closed in H1. rewrite H1. auto.
Qed.

Lemma subst_closed_t : forall (n : nat) (T s t : term),
  closed_t t = true ->
  closed_t (substitution_t T n s) = true ->
  closed_t (substitution_t T n t) = true.
Proof.
intros. induction T; auto.
- simpl. simpl in H0.
  case_eq (closed_t (substitution_t T1 n s)); intros HT1;
  case_eq (closed_t (substitution_t T2 n s)); intros HT2.
  + rewrite (IHT1 HT1). rewrite (IHT2 HT2). auto.
  + rewrite HT1 in H0. rewrite HT2 in H0. inversion H0.
  + rewrite HT1 in H0. rewrite HT2 in H0. inversion H0.
  + rewrite HT1 in H0. rewrite HT2 in H0. inversion H0.
- simpl. simpl in H0.
  case_eq (closed_t (substitution_t T1 n s)); intros HT1;
  case_eq (closed_t (substitution_t T2 n s)); intros HT2.
  + rewrite (IHT1 HT1). rewrite (IHT2 HT2). auto.
  + rewrite HT1 in H0. rewrite HT2 in H0. inversion H0.
  + rewrite HT1 in H0. rewrite HT2 in H0. inversion H0.
  + rewrite HT1 in H0. rewrite HT2 in H0. inversion H0.
- case_eq (beq_nat n0 n); intros; simpl; rewrite H1.
  + apply H.
  + simpl in H0. rewrite H1 in H0. inversion H0.
Qed.

Lemma incorrect_subst_closed : forall (a : atomic_formula) (n : nat) (s t : term),
  closed_t t = true ->
  incorrect_a (substitution_a a n s) = true ->
  closed_a (substitution_a a n t) = true.
Proof.
intros.
case_eq a. intros t1 t2 Ha. rewrite Ha in H0. clear Ha. simpl.
apply incorrect_closed in H0. simpl in H0.
case_eq (closed_t (substitution_t t1 n s)); intros Ht1;
case_eq (closed_t (substitution_t t2 n s)); intros Ht2; auto.
- rewrite (subst_closed_t n t1 s t H Ht1).
  rewrite (subst_closed_t n t2 s t H Ht2). auto.
- rewrite Ht1 in H0. rewrite Ht2 in H0. inversion H0.
- rewrite Ht1 in H0. rewrite Ht2 in H0. inversion H0.
- rewrite Ht1 in H0. rewrite Ht2 in H0. inversion H0.
Qed.

Lemma closed_lor : forall (B C : formula),
  closed (lor B C) = true -> closed B = true /\ closed C = true.
Proof.
intros. simpl in H. split.
- case_eq (closed B); case_eq (closed C); intros; auto;
  rewrite H0 in H; rewrite H1 in H; inversion H.
- case_eq (closed B); case_eq (closed C); intros; auto;
  rewrite H0 in H; rewrite H1 in H; inversion H.
Qed.

Lemma closed_subst_eq_aux_t : forall (T : term) (n : nat) (t : term),
  member n (free_list_t T) = false -> substitution_t T n t = T.
Proof.
intros.
induction T; auto.
- apply IHT in H. simpl. rewrite H. auto.
- simpl. simpl in H. destruct (member_remove_dups_concat _ _ _ H).
  rewrite IHT1, IHT2.
  + auto.
  + apply H1.
  + apply H0.
- simpl. simpl in H. destruct (member_remove_dups_concat _ _ _ H).
  rewrite IHT1, IHT2.
  + auto.
  + apply H1.
  + apply H0.
- simpl in H. simpl. case_eq (beq_nat n0 n); intros.
  + rewrite H0 in H. inversion H.
  + auto.
Qed.

Lemma closed_subst_eq_aux_a : forall (a : atomic_formula) (n : nat) (t : term),
  member n (free_list_a a) = false -> substitution_a a n t = a.
Proof.
intros. destruct a as [t1 t2]. simpl. simpl in H.
destruct (member_remove_dups_concat _ _ _ H).
rewrite (closed_subst_eq_aux_t t1 n t), (closed_subst_eq_aux_t t2 n t).
- auto.
- apply H1.
- apply H0.
Qed.

Lemma closed_subst_eq_aux : forall (A : formula) (n : nat) (t : term),
  member n (free_list A) = false -> substitution A n t = A.
Proof.
intros.
induction A.
- simpl. rewrite closed_subst_eq_aux_a; auto.
- simpl in H. simpl. rewrite (IHA H). auto.
- simpl. simpl in H. destruct (member_remove_dups_concat _ _ _ H).
  rewrite IHA1, IHA2.
  + auto.
  + apply H1.
  + apply H0.
- simpl. case_eq (beq_nat n0 n); intros; auto.
  simpl in H. rewrite IHA. 
  + auto.
  + apply (member_remove _ _ _ H0 H).
Qed.


Lemma closed_subst_eq_t : forall (n : nat) (T t : term),
  closed_t T = true -> substitution_t T n t = T.
Proof.
intros.
apply closed_subst_eq_aux_t.
apply closed_free_list_t in H.
rewrite H. auto.
Qed.

Lemma closed_subst_eq_a : forall (a : atomic_formula) (n : nat) (t : term),
  closed_a a = true -> substitution_a a n t = a.
Proof.
intros.
apply closed_subst_eq_aux_a.
apply closed_free_list_a in H.
rewrite H. auto.
Qed.

Lemma closed_subst_eq : forall (A : formula) (n : nat) (t : term),
  closed A = true -> substitution A n t = A.
Proof.
intros.
apply closed_subst_eq_aux.
apply closed_free_list in H.
rewrite H. auto.
Qed.

Lemma closed_sub_theorem : forall (A : formula) (n : nat) (t : term),
  closed A = true ->
  PA_omega_theorem A ->
  PA_omega_theorem (substitution A n t).
Proof. intros. rewrite closed_subst_eq. apply H0. apply H. Qed.

Lemma closed_univ_sub : forall (B : formula) (n : nat),
  closed (univ n B) = true ->
  (forall (t : term), closed_t t = true -> closed (substitution B n t) = true).
Proof.
intros.
destruct (closed_univ B n H).
- rewrite (closed_subst_eq _ _ _ H1). apply H1.
- apply free_list_closed. rewrite (subst_remove B n t H0).
  rewrite H1. simpl. rewrite beq_nat_refl. auto.
Qed.

Lemma closed_univ_sub_repr : forall (B : formula) (n : nat),
  closed (univ n B) = true ->
  (forall (m : nat), closed (substitution B n (represent m)) = true).
Proof.
intros.
apply closed_univ_sub.
- apply H.
- apply eval_closed, eval_represent.
Qed.

Lemma free_list_lor : forall (B C : formula) (n : nat),
  free_list (lor B C) = [n] ->
  (free_list B = [n] \/ closed B = true) /\
  (free_list C = [n] \/ closed C = true).
Proof.
intros. simpl in H.
apply remove_dups_repeated_element' in H.
destruct (repeated_element_n_concat _ _ _ H) as [HB HC]. split.
- destruct (remove_dups_repeated_element _ _ HB) as [HB' | HB'].
  + left. rewrite free_list_remove_dups. apply HB'.
  + right. apply free_list_closed, HB'.
- destruct (remove_dups_repeated_element _ _ HC) as [HC' | HC'].
  + left. rewrite free_list_remove_dups. apply HC'.
  + right. apply free_list_closed, HC'.
Qed.

Lemma substitution_order_t : forall (T : term) (m n : nat) (s t : term),
  closed_t s = true ->
  closed_t t = true ->
  beq_nat m n = false ->
  substitution_t (substitution_t T n s) m t =
  substitution_t (substitution_t T m t) n s.
Proof.
intros T m n s t Hs Ht Hmn. induction T; auto; simpl.
- rewrite IHT. auto.
- rewrite IHT1, IHT2. auto.
- rewrite IHT1, IHT2. auto.
- destruct (beq_nat n0 n) eqn:Hn.
  + rewrite <- (nat_beq_eq _ _ Hn) in Hmn. rewrite (beq_nat_symm' _ _ Hmn).
    simpl. rewrite Hn. apply closed_subst_eq_t, Hs.
  + destruct (beq_nat n0 m) eqn:Hm; simpl; rewrite Hm.
    * symmetry. apply closed_subst_eq_t, Ht.
    * rewrite Hn. auto.
Qed.

Lemma substitution_order_a :
  forall (a : atomic_formula) (m n : nat) (s t : term),
  closed_t s = true ->
  closed_t t = true ->
  beq_nat m n = false ->
  substitution_a (substitution_a a n s) m t =
  substitution_a (substitution_a a m t) n s.
Proof.
intros a m n s t Hs Ht Hmn. destruct a as [t1 t2]. simpl.
rewrite (substitution_order_t _ _ _ _ _ Hs Ht Hmn).
rewrite (substitution_order_t _ _ _ _ _ Hs Ht Hmn). auto.
Qed.

Lemma substitution_order : forall (B : formula) (m n : nat) (s t : term),
  closed_t s = true ->
  closed_t t = true ->
  beq_nat m n = false ->
  substitution (substitution B n s) m t =
  substitution (substitution B m t) n s.
Proof.
intros B m n s t Hs Ht Hmn. induction B; simpl.
- rewrite (substitution_order_a _ _ _ _ _ Hs Ht Hmn). auto.
- rewrite IHB. auto.
- rewrite IHB1, IHB2. auto.
- destruct (beq_nat n0 n) eqn:Hn.
  + apply nat_beq_eq in Hn. rewrite Hn.
    rewrite (beq_nat_symm' _ _ Hmn). simpl.
    rewrite (beq_nat_symm' _ _ Hmn). rewrite beq_nat_refl. auto.
  + destruct (beq_nat n0 m) eqn:Hm; simpl; rewrite Hm, Hn; auto.
    rewrite IHB. auto.
Qed.

Lemma univ_free_var : forall (B : formula) (m n : nat),
  free_list (univ m B) = [n] -> beq_nat m n = false.
Proof.
intros. simpl in H.
destruct (beq_nat m n) eqn:Hm; auto.
apply nat_beq_eq in Hm. rewrite Hm in H.
pose proof (remove_twice (free_list B) n).
rewrite H in H0. simpl in H0. rewrite beq_nat_refl in H0. inversion H0.
Qed.

Lemma free_list_univ_sub :
  forall (B : formula) (m : nat) (t : term) (l : list nat),
  closed_t t = true ->
  free_list (univ m B) = l ->
  free_list (substitution B m t) = l.
Proof. intros. rewrite (subst_remove _ _ _ H). apply H0. Qed.

Lemma repr_closed : forall (m : nat), closed_t (represent m) = true.
Proof. intros. apply eval_closed, eval_represent. Qed.

Lemma correct_closed_t : forall (s t : term),
  correct_a (equ s t) = true -> closed_t s = true /\ closed_t t = true.
Proof.
intros.
destruct (correct_eval _ _ H). split; apply eval_closed.
apply H0. apply H1.
Qed.
































(*
###############################################################################
Section 5: Here we prove that PA_omega proves the Law of Excluded Middle (LEM),
and a certain generalization: if s,t are closed terms that evaluate to the
same value, and A is a formula with exactly one free variable, then PA_omega
proves ~A(s) \/ A(t). We will need these results in the next section.
###############################################################################
*)


Lemma LEM_atomic : forall (a : atomic_formula),
  closed_a a = true -> PA_omega_theorem (lor (neg (atom a)) (atom a)).
Proof.
intros.
destruct (correctness_decid a H).
- apply weakening.
  + apply H.
  + apply axiom. apply H0.
- apply exchange1. apply weakening.
  + apply H.
  + apply axiom. apply H0.
Qed.

(*
The logical structure of the inductive argument here is rather subtle
when fully formalized; P1,P2,P3 are meant to break this up. We ultimately want
to prove (forall A, P1 A), but our main task will be to show (forall n, P3 n)
by strong induction on n, the number of connectives.
*)
(* *)
Definition P1 (A : formula) : Prop :=
  closed A = true -> PA_omega_theorem (lor (neg A) A).

Definition P2 (A : formula) (n : nat) : Prop :=
  num_conn A = n -> P1 A.

Definition P3 (m : nat) : Prop :=
  forall (A : formula), P2 A m.

Lemma P3_strongind_aux :
  P3 0 ->
  (forall n,
    ((forall m, m <= n -> P3 m) -> P3 (S n))) ->
  forall n, (forall m, ((m <= n) -> P3 m)).
Proof.
induction n as [| n' IHn' ].
- intros. inversion H1. apply H.
- intros. inversion H1.
  + apply H0. apply IHn'.
  + apply IHn'. apply H3.
Qed.

Lemma P3_strongind :
  P3 0 ->
  (forall n,
    ((forall m, m <= n -> P3 m) -> P3 (S n))) ->
  forall n, P3 n.
Proof. intros. apply (P3_strongind_aux H H0 n n). auto. Qed.

Lemma P3_0 : P3 0.
Proof.
unfold P3, P2. intros.
destruct A as [a | | | ].
- unfold P1. apply LEM_atomic.
- inversion H.
- inversion H.
- inversion H.
Qed.

Lemma num_conn_lor : forall (B C : formula) (n : nat),
  num_conn (lor B C) = S n -> num_conn B <= n /\ num_conn C <= n.
Proof. intros. apply addends_leq. inversion H. auto. Qed.

Lemma strong_weak_ind : forall (P : nat -> Prop),
  (forall n, (forall m, m <= n -> P(m))) ->
  (forall n, P n).
Proof. intros. apply (H n n (leq_refl n)). Qed.

Lemma LEM_univ : forall (B : formula) (n m : nat),
  closed (substitution B n (represent m)) = true ->
  PA_omega_theorem (lor (neg (substitution B n (represent m)))
                             (substitution B n (represent m))) ->
  PA_omega_theorem (lor (substitution B n (represent m)) (neg (univ n B))).
Proof.
intros.
apply exchange1.
apply (quantification2 _ _ _ (represent m)).
- apply eval_closed. apply eval_represent.
- apply H0.
Qed.



Lemma num_conn_sub : forall (B : formula) (m : nat) (t : term),
  num_conn (substitution B m t) = num_conn B.
Proof.
intros.
induction B; auto; simpl.
- rewrite IHB. auto.
- rewrite IHB1, IHB2. auto.
- destruct (beq_nat n m).
  + auto.
  + simpl. rewrite IHB. auto.
Qed.


Lemma P3_inductive : forall n, (forall m, m <= n -> P3 m) -> P3 (S n).
Proof.
unfold P3,P2,P1. intros.
destruct A as [a | B | B C | m B].
- inversion H0.
- inversion H0. pose proof (H n (le_refl n) B H3 H1).
  apply negation2. apply exchange1. apply H2.
- destruct (closed_lor _ _ H1) as [HB HC].
  destruct (num_conn_lor _ _ _ H0) as [HB' HC'].
  apply demorgan2.
  + apply associativity1. apply exchange1. apply weakening.
    * apply HC.
    * apply (H (num_conn B) HB' B (eq_refl (num_conn B)) HB).
  + apply associativity1. apply exchange2. apply exchange1. apply weakening.
    * apply HB.
    * apply (H (num_conn C) HC' C (eq_refl (num_conn C)) HC).
- apply exchange1. inversion H0. pose proof (H n (le_refl n)).
  apply w_rule2. intros k. apply (LEM_univ B m k).
  + apply closed_univ_sub.
    * apply H1.
    * apply eval_closed, eval_represent.
  + apply H2.
    * rewrite num_conn_sub. apply H3.
    * apply closed_univ_sub.
      { apply H1. }
      { apply eval_closed, eval_represent. }
Qed.

Lemma P3_lemma : forall n, P3 n.
Proof. apply P3_strongind. apply P3_0. apply P3_inductive. Qed.

Lemma P2_lemma : forall (n : nat) (A : formula), P2 A n.
Proof. apply P3_lemma. Qed.

Lemma P1_lemma : forall (A : formula), P1 A.
Proof.
intros.
pose proof (P2_lemma).
unfold P2 in H.
apply (H (num_conn A) A). auto.
Qed.

Lemma LEM : forall (A : formula),
  closed A = true -> PA_omega_theorem (lor (neg A) A).
Proof. apply P1_lemma. Qed.







(*
Now we show a slight generalization of LEM that we will call LEM_term:
if closed terms s and t are equal, and formula A has only one free variable,
then PA_omega proves (lor (neg A(s)) A(t)). First we handle the atomic case.
*)
(* *)
Lemma LEM_term_atomic_aux1 : forall (T s t : term) (n : nat),
  eval s = eval t -> eval (substitution_t T n s) = eval (substitution_t T n t).
Proof.
intros.
induction T.
- auto.
- assert (substitution_t (succ T) n s = succ (substitution_t T n s)). { auto. }
  assert (substitution_t (succ T) n t = succ (substitution_t T n t)). { auto. }
  rewrite H0. rewrite H1. case_eq (eval (substitution_t T n s));
  intros; simpl; rewrite <- IHT; rewrite H2; auto.
- assert (eval (substitution_t (plus T1 T2) n s) =
          eval (plus (substitution_t T1 n s) (substitution_t T2 n s))). { auto. }
  assert (eval (substitution_t (plus T1 T2) n t) =
          eval (plus (substitution_t T1 n t) (substitution_t T2 n t))). { auto. }
  rewrite H0. rewrite H1. case_eq (eval (substitution_t T1 n s));
  intros; simpl; rewrite <- IHT1; rewrite <- IHT2; rewrite H2; auto.
- assert (eval (substitution_t (times T1 T2) n s) =
          eval (times (substitution_t T1 n s) (substitution_t T2 n s))). { auto. }
  assert (eval (substitution_t (times T1 T2) n t) =
          eval (times (substitution_t T1 n t) (substitution_t T2 n t))). { auto. }
  rewrite H0. rewrite H1. case_eq (eval (substitution_t T1 n s));
  intros; simpl; rewrite <- IHT1; rewrite <- IHT2; rewrite H2; auto.
- simpl. case (beq_nat n0 n). apply H. auto.
Qed.

Lemma LEM_term_atomic_aux2 : forall (a : atomic_formula) (s t : term) (n : nat),
  eval s = eval t ->
  correctness (substitution_a a n s) = correct ->
  correctness (substitution_a a n t) = correct.
Proof.
intros.
case_eq a.
intros t1 t2 H1.
rewrite H1 in H0.
unfold substitution_a in H0.
unfold substitution_a.
pose proof (LEM_term_atomic_aux1 t1 s t n H) as Ht1.
pose proof (LEM_term_atomic_aux1 t2 s t n H) as Ht2.
case_eq (eval (substitution_t t1 n t));
case_eq (eval (substitution_t t2 n t)); intros;
unfold correctness in H0;
rewrite Ht1 in H0; rewrite Ht2 in H0;
rewrite H2 in H0; rewrite H3 in H0; inversion H0.
simpl. rewrite H2. rewrite H3. auto.
Qed.

Lemma LEM_term_atomic_aux3 : forall (s t : term),
  correct_a (equ s t) = true -> eval s = eval t.
Proof.
intros s t.
unfold correct_a.
unfold correctness.
case_eq (eval s); case_eq (eval t); intros.
- auto.
- inversion H1.
- inversion H1.
- case_eq (beq_nat (S n0) (S n)).
  + apply nat_beq_eq.
  + intros. rewrite H2 in H1. inversion H1.
Qed.

Lemma equ_symm : forall (s t : term),
  correct_a (equ s t) = true -> correct_a (equ t s) = true.
Proof.
intros.
pose proof (LEM_term_atomic_aux3 _ _ H) as Hst.
destruct (correct_eval s t H).
unfold correct_a, correctness.
case_eq (eval t); case_eq (eval s); intros.
- rewrite H2 in H0. inversion H0.
- rewrite H3 in H1. inversion H1.
- rewrite H2 in H0. inversion H0.
- rewrite <- H2. rewrite <- H3. rewrite Hst. rewrite beq_nat_refl. auto.
Qed.

Lemma LEM_term_atomic' : forall (s t : term) (a : atomic_formula) (n : nat),
  correct_a (equ s t) = true ->
  PA_omega_axiom (substitution (atom a) n s) = true ->
  PA_omega_axiom (substitution (atom a) n t) = true.
Proof.
simpl. intros.
assert (eval s = eval t). { apply LEM_term_atomic_aux3. apply H. }
assert (correctness (substitution_a a n s) = correct).
{ unfold correct_a in H0.
  case_eq (correctness (substitution_a a n s)); intros;
  rewrite H2 in H0; inversion H0; auto. }
pose proof (LEM_term_atomic_aux2 a s t n H1 H2).
unfold correct_a.
rewrite H3. auto.
Qed.

Lemma LEM_term_atomic :
  forall (a : atomic_formula) (n : nat) (s t : term),
    correct_a (equ s t) = true ->
    free_list_a a = [n] ->
    PA_omega_theorem (lor (neg (atom (substitution_a a n s)))
                          (atom (substitution_a a n t))).
Proof.
intros a n s t H Ha.
destruct (correctness_decid (substitution_a a n s)).
- apply one_var_free_lemma_a.
  + simpl in H. apply eval_closed. destruct (correct_eval s t H). apply H0.
  + apply Ha.
- pose proof (correct_closed _ H0) as HC.
  pose proof (LEM_term_atomic' s t a n H). apply H1 in H0.
  apply axiom in H0. unfold substitution in H0. apply weakening.
  + simpl. apply HC.
  + apply H0.
- apply exchange1. apply weakening.
  + simpl. apply (incorrect_subst_closed a n s t).
    * apply eval_closed. destruct (correct_eval s t H). apply H2.
    * apply H0.
  + apply axiom. apply H0.
Qed.


(*
The inductive proof here is quite similar with LEM, and Q1,Q2,Q3
are meant to break this up. *)
(* *)
Definition Q1 (A : formula) : Prop := forall (n : nat) (s t : term),
  correct_a (equ s t) = true ->
  free_list A = [n] ->
  PA_omega_theorem (lor (neg (substitution A n s)) (substitution A n t)).

Definition Q2 (A : formula) (n : nat) : Prop := num_conn A = n -> Q1 A.

Definition Q3 (m : nat) : Prop := forall (A : formula), Q2 A m.

Lemma Q3_strongind_aux :
  Q3 0 ->
  (forall n,
    ((forall m, m <= n -> Q3 m) -> Q3 (S n))) ->
  forall n, (forall m, ((m <= n) -> Q3 m)).
Proof.
induction n as [| n' IHn' ].
- intros. inversion H1. apply H.
- intros. inversion H1.
  + apply H0. apply IHn'.
  + apply IHn'. apply H3.
Qed.

Lemma Q3_strongind :
  Q3 0 ->
  (forall n,
    ((forall m, m <= n -> Q3 m) -> Q3 (S n))) ->
  forall n, Q3 n.
Proof. intros. apply (Q3_strongind_aux H H0 n n). auto. Qed.

Lemma Q3_0 : Q3 0.
Proof.
unfold Q3, Q2. intros.
destruct A as [a | | | ].
- unfold Q1. apply LEM_term_atomic.
- inversion H.
- inversion H.
- inversion H.
Qed.


Lemma Q3_inductive : forall n, (forall m, m <= n -> Q3 m) -> Q3 (S n).
Proof.
unfold Q3,Q2, Q1. intros.
destruct A as [| B | B C | m B].
- inversion H0.
- inversion H0. simpl. apply negation2. apply exchange1.
  apply (H n (le_refl n) B H4 n0 t s).
  + apply equ_symm,H1.
  + apply H2.
- destruct (free_list_lor B C n0 H2) as [HB HC].
  destruct (num_conn_lor _ _ _ H0) as [HB' HC'].
  destruct (correct_closed_t _ _ H1) as [Hs Ht].
  simpl. apply demorgan2.
  + apply associativity1. apply exchange1. apply weakening.
    * destruct HC as [HC | HC].
      { apply (one_var_free_lemma _ _ _ Ht HC). }
      { rewrite closed_subst_eq; apply HC. }
    * destruct HB as [HB | HB].
      { apply (H (num_conn B) HB' B (eq_refl (num_conn B)) n0 s t H1 HB). }
      { rewrite closed_subst_eq, closed_subst_eq; auto. apply LEM, HB. }
  + apply associativity1. apply exchange2. apply exchange1. apply weakening.
    * destruct HB as [HB | HB].
      { apply (one_var_free_lemma _ _ _ Ht HB). }
      { rewrite closed_subst_eq; apply HB. }
    * destruct HC as [HC | HC].
      { apply (H (num_conn C) HC' C (eq_refl (num_conn C)) n0 s t H1 HC). }
      { rewrite closed_subst_eq, closed_subst_eq; auto. apply LEM, HC. }
- apply exchange1. inversion H0.
  simpl. pose proof (univ_free_var _ _ _ H2) as Heq. rewrite Heq.
  apply w_rule2. intros. apply exchange1.
  apply (quantification2 _ _ _ (represent m0)).
  + apply repr_closed.
  + destruct (correct_closed_t _ _ H1) as [Hs Ht].
    rewrite (substitution_order B m n0 s _ Hs (repr_closed m0) Heq).
    rewrite (substitution_order B m n0 t _ Ht (repr_closed m0) Heq).
    apply (H n (le_refl n) (substitution B m (represent m0))).
    * rewrite num_conn_sub. apply H4.
    * apply H1.
    * apply free_list_univ_sub. apply repr_closed. apply H2.
Qed.

Lemma Q3_lemma : forall n, Q3 n.
Proof. apply Q3_strongind. apply Q3_0. apply Q3_inductive. Qed.

Lemma Q2_lemma : forall (n : nat) (A : formula), Q2 A n.
Proof. apply Q3_lemma. Qed.

Lemma Q1_lemma : forall (A : formula), Q1 A.
Proof.
intros.
pose proof (Q2_lemma).
unfold Q2 in H.
apply (H (num_conn A) A). auto.
Qed.

Lemma LEM_term : forall (A : formula) (n : nat) (s t : term),
  correct_a (equ s t) = true ->
  free_list A = [n] ->
  PA_omega_theorem (lor (neg (substitution A n s)) (substitution A n t)).
Proof. apply Q1_lemma. Qed.






































































(*
###############################################################################
Section 6: Here we will set up the axioms and rules of inference of PA.
###############################################################################
*)























































(*
###############################################################################
Section 7: Here we will prove that if PA proves some A, then so does PA_omega.
###############################################################################
*)


























































(*
###############################################################################
Section 8: Proof trees (currently w/o ordinal assignments) for PA_omega proofs.
###############################################################################
*)

(*
Defining formula trees, which are proof trees without the ordinals/degrees.
*)
(* *)

Inductive ftree : Type :=
| node : formula -> ftree


| exchange_ab : formula -> formula -> ftree -> ftree

| exchange_cab : formula -> formula -> formula -> ftree -> ftree

| exchange_abd : formula -> formula -> formula -> ftree -> ftree

| exchange_cabd : formula -> formula -> formula -> formula -> ftree -> ftree

| contraction_a : formula -> ftree -> ftree

| contraction_ad : formula -> formula -> ftree -> ftree


| weakening_ad : formula -> formula -> ftree -> ftree

| demorgan_ab : formula -> formula -> ftree -> ftree -> ftree

| demorgan_abd : formula -> formula -> formula -> ftree -> ftree -> ftree

| negation_a : formula -> ftree -> ftree

| negation_ad : formula -> formula -> ftree -> ftree



| quantification_a : formula -> nat -> term -> ftree -> ftree

| quantification_ad : formula -> formula -> nat -> term -> ftree -> ftree

| w_rule_a : formula -> nat -> (nat -> ftree) -> ftree

| w_rule_ad : formula -> formula -> nat -> (nat -> ftree) -> ftree

| cut_ca : formula -> formula -> ftree -> ftree -> ftree

| cut_ad : formula -> formula -> ftree -> ftree -> ftree

| cut_cad : formula -> formula -> formula -> ftree -> ftree -> ftree.



Fixpoint ftree_formula (P : ftree) : formula :=
match P with
| node A => A


| exchange_ab A B P' => lor B A

| exchange_cab C A B P' => lor (lor C B) A

| exchange_abd A B D P' => lor (lor B A) D

| exchange_cabd C A B D P' => lor (lor (lor C B) A) D

| contraction_a A P' => A

| contraction_ad A D P' => lor A D


| weakening_ad A D P' => lor A D

| demorgan_ab A B Q1 Q2 => neg (lor A B)

| demorgan_abd A B D Q1 Q2 => lor (neg (lor A B)) D

| negation_a A P' => neg (neg A)

| negation_ad A D P' => lor (neg (neg A)) D

| quantification_a A n t P' => neg (univ n A)

| quantification_ad A D n t P' => lor (neg (univ n A)) D

| w_rule_a A n g => univ n A

| w_rule_ad A D n g => lor (univ n A) D


| cut_ca C A Q1 Q2 => C

| cut_ad A D Q1 Q2 => D

| cut_cad C A D Q1 Q2 => lor C D

end.



Fixpoint valid (P : ftree) : Prop :=
match P with
| node A => PA_omega_axiom A = true

| exchange_ab A B P' => ftree_formula P' = lor A B /\ valid P'

| exchange_cab C A B P' => ftree_formula P' = lor (lor C A) B /\ valid P'

| exchange_abd A B D P' => ftree_formula P' = lor (lor A B) D /\ valid P'

| exchange_cabd C A B D P' =>
    ftree_formula P' = lor (lor (lor C A) B) D /\ valid P'

| contraction_a A P' => ftree_formula P' = lor A A /\ valid P'

| contraction_ad A D P' => ftree_formula P' = lor (lor A A) D /\ valid P'


| weakening_ad A D P' => ftree_formula P' = D /\ closed A = true /\ valid P'

| demorgan_ab A B Q1 Q2 =>
    ftree_formula Q1 = neg A /\ valid Q1 /\
    ftree_formula Q2 = neg B /\ valid Q2

| demorgan_abd A B D Q1 Q2 =>
    ftree_formula Q1 = lor (neg A) D /\ valid Q1 /\
    ftree_formula Q2 = lor (neg B) D /\ valid Q2

| negation_a A P' => ftree_formula P' = A /\ valid P'

| negation_ad A D P' => ftree_formula P' = lor A D /\ valid P'


| quantification_a A n t P' =>
    ftree_formula P' = neg (substitution A n t) /\
    closed_t t = true /\ valid P'

| quantification_ad A D n t P' =>
    ftree_formula P' = lor (neg (substitution A n t)) D /\
    closed_t t = true /\ valid P'

(* w_rule will also need condition on max degree of the (g m)'s *)
| w_rule_a A n g => forall (m : nat),
    ftree_formula (g m) = substitution A n (represent m) /\ valid (g m)

| w_rule_ad A D n g => forall (m : nat),
    ftree_formula (g m) = lor (substitution A n (represent m)) D /\ valid (g m)


| cut_ca C A Q1 Q2 =>
    ftree_formula Q1 = lor C A /\ valid Q1 /\
    ftree_formula Q2 = neg A /\ valid Q2

| cut_ad A D Q1 Q2 =>
    ftree_formula Q1 = A /\ valid Q1 /\
    ftree_formula Q2 = lor (neg A) D /\ valid Q2

| cut_cad C A D Q1 Q2 =>
    ftree_formula Q1 = lor C A /\ valid Q1 /\
    ftree_formula Q2 = lor (neg A) D /\ valid Q2


end.


(* some basic examples *)
Definition f_exmp : formula := (atom (equ zero zero)).
Definition ftree_exmp : ftree := node f_exmp.
Lemma ftree_exmp_valid : valid ftree_exmp. Proof. simpl. auto. Qed.

Definition provable (A : formula) : Prop :=
  exists (t : ftree), ftree_formula t = A /\ valid t.

Lemma provable_exmp : provable (atom (equ zero zero)).
Proof.
unfold provable. eapply ex_intro. instantiate (1:=ftree_exmp). split.
- auto.
- apply ftree_exmp_valid.
Qed.

Lemma exchange_provable : forall (A B : formula),
  provable (lor A B) -> provable (lor B A).
Proof.
unfold provable. intros. destruct H as [t H].
eapply ex_intro. instantiate (1:= exchange_ab A B t). split.
- auto.
- simpl. apply H.
Qed.


(* Show that PA_omega proves the associativity laws *)
(* *)



Lemma associativity_1 : forall (C A B : formula),
  provable (lor (lor C A) B) -> provable (lor C (lor A B)).
Proof.
unfold provable. intros. destruct H as [t H].
eapply ex_intro.
instantiate (1:= exchange_ab (lor A B) C
                  (exchange_cab A C B
                    (exchange_abd C A B t))).
simpl. auto.
Qed.


Lemma associativity_2 : forall (c a b : formula),
  provable (lor c (lor a b)) ->
  provable (lor (lor c a) b).
Proof.
Admitted.

(* Proof trees equivalent to theorems *)
(* *)
Lemma provable_theorem : forall (A : formula),
  PA_omega_theorem A -> provable A.
Proof.
Admitted.

Lemma theorem_provable : forall (A : formula),
  provable A -> PA_omega_theorem A.
Proof.
Admitted.


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

Lemma theorem_closed : forall (A : formula),
  PA_omega_theorem A -> closed A = true.
Proof.
intros. induction H.
- apply axiom_closed. apply H.
- inversion IHPA_omega_theorem. simpl.
  rewrite H1. apply and_bool_symm. apply H1.
Admitted.

Lemma provable_closed : forall (A : formula),
  provable A -> closed A = true.
Proof. intros. apply theorem_closed. apply theorem_provable. apply H. Qed.

Lemma provable_closed' : forall (P : ftree) (A : formula),
  valid P -> ftree_formula P = A -> closed A = true.
Proof.
intros. apply provable_closed. unfold provable. exists P.
split. apply H0. apply H.
Qed.


(* Boolean equality on formulas implies actual equality *)
(* *)
Definition term_beq_eq_nice (t : term) : Prop := forall (s : term),
  eq_term s t = true -> s = t.

Lemma term_beq_eq' : forall (t : term), term_beq_eq_nice t.
Proof.
intros. induction t; unfold term_beq_eq_nice; intros; destruct s; inversion H.
- auto.
- unfold term_beq_eq_nice in IHt. rewrite (IHt s H1). auto.
- destruct (and_bool_prop _ _ H1).
  unfold term_beq_eq_nice in IHt1. rewrite (IHt1 s1 H0).
  unfold term_beq_eq_nice in IHt2. rewrite (IHt2 s2 H2). auto.
- destruct (and_bool_prop _ _ H1).
  unfold term_beq_eq_nice in IHt1. rewrite (IHt1 s1 H0).
  unfold term_beq_eq_nice in IHt2. rewrite (IHt2 s2 H2). auto.
- rewrite (nat_beq_eq _ _ H1). auto.
Qed.

Lemma term_beq_eq : forall (s t : term),
  eq_term s t = true -> s = t.
Proof. intros. apply term_beq_eq'. apply H. Qed.

Lemma atom_beq_eq : forall (a b : atomic_formula),
  eq_atom a b = true -> a = b.
Proof.
intros. destruct a,b. inversion H. destruct (and_bool_prop _ _ H1).
apply term_beq_eq in H0. apply term_beq_eq in H2. rewrite H0, H2. auto.
Qed.

Definition f_beq_eq_nice (A : formula) : Prop := forall (B : formula),
  eq_f A B = true -> A = B.

Lemma f_beq_eq' : forall (A : formula), f_beq_eq_nice A.
Proof.
intros. induction A; unfold f_beq_eq_nice; intros; destruct B; inversion H.
- apply atom_beq_eq in H1. rewrite H1. auto.
- unfold f_beq_eq_nice in IHA. rewrite (IHA B H1). auto.
- destruct (and_bool_prop _ _ H1).
  unfold term_beq_eq_nice in IHA1. rewrite (IHA1 B1 H0).
  unfold term_beq_eq_nice in IHA2. rewrite (IHA2 B2 H2). auto.
- destruct (and_bool_prop _ _ H1).
  unfold f_beq_eq_nice in IHA. rewrite (IHA B H2), (nat_beq_eq _ _ H0). auto.
Qed.

Lemma f_beq_eq : forall (A B : formula), eq_f A B = true -> A = B.
Proof. intros. apply f_beq_eq'. apply H. Qed.



(* Some lemmas about the w_rule we will use later *)
(* *)
Lemma valid_w_rule_a' :
  forall (P : ftree) (A : formula) (n : nat) (g : nat -> ftree),
  P = (w_rule_a A n g) ->
  valid P ->
  forall (m : nat),
    ftree_formula (g m) = substitution A n (represent m) /\ valid (g m).
Proof.
intros.
unfold valid in H0. rewrite H in H0.
fold valid in H0. apply H0.
Qed.

Lemma valid_w_rule_a : forall (A : formula) (n : nat) (g : nat -> ftree),
  valid (w_rule_a A n g) ->
  forall (m : nat),
    ftree_formula (g m) = substitution A n (represent m) /\ valid (g m).
Proof. intros. apply (valid_w_rule_a' (w_rule_a A n g)). auto. apply H. Qed.

Lemma valid_w_rule_ad' :
  forall (P : ftree) (A D : formula) (n : nat) (g : nat -> ftree),
  P = (w_rule_ad A D n g) ->
  valid P ->
  forall (m : nat),
    ftree_formula (g m) =
    lor (substitution A n (represent m)) D /\ valid (g m).
Proof.
intros.
unfold valid in H0. rewrite H in H0.
fold valid in H0. apply H0.
Qed.

Lemma valid_w_rule_ad : forall (A D : formula) (n : nat) (g : nat -> ftree),
  valid (w_rule_ad A D n g) ->
  forall (m : nat),
    ftree_formula (g m) =
    lor (substitution A n (represent m)) D /\ valid (g m).
Proof.
intros.
apply (valid_w_rule_ad' (w_rule_ad A D n g)).
auto. apply H.
Qed.





(*
(* Proofs in PA_omega, except restricted with some n denoting the highest
    degree of any cut, and some ordinal assignment e0 *)
(* *)
Inductive PA_omega_proves : formula -> nat -> e0 -> Prop :=
| greater_degree : forall (a : formula) (n m : nat) (alpha : e0),
    PA_omega_proves a n alpha ->
    m > n ->
    PA_omega_proves a m alpha

| greater_ordinal : forall (a : formula) (n : nat) (alpha beta : e0),
    PA_omega_proves a n alpha ->
    gt_e0 beta alpha ->
    PA_omega_proves a n beta



| axiom' : forall (a : formula),
    PA_omega_axiom a = true ->
    PA_omega_proves a 0 (exist nf Zero Zero_nf)



| exchange1' : forall (a b : formula) (n : nat) (alpha : e0),
    PA_omega_proves (lor a b) n alpha ->
    PA_omega_proves (lor b a) n alpha.

*)





















































(*
###############################################################################
Section 9: Invertibility lemmas: We show that double negation, DeMorgan,
and the w_rule are invertible, e.g. if PA_omega proves ~~A \/ D, then it also
proves A \/ D. Essentially we need to substitute A for ~~A in the proof tree
~~A \/ D, though we need to introduce some machinery to handle these
substitutions properly.
###############################################################################
*)


(* Defining substitution indicators, which will control exactly where in a
formula substitutions will be made *)
(* *)
Inductive subst_ind : Type :=
| ind_0 : subst_ind
| ind_1 : subst_ind
| lor_ind : subst_ind -> subst_ind -> subst_ind.

Notation "(0)" := ind_0.
Notation "(1)" := ind_1.
Notation "( x y )" := (lor_ind x y).

Fixpoint non_target (A : formula) : subst_ind :=
match A with
| lor B C => lor_ind (non_target B) (non_target C)
| _ => (0)
end.

Fixpoint target (A : formula) : subst_ind :=
match A with
| lor B C => lor_ind (target B) (target C)
| _ => (1)
end.

(* replace E with F at certain places in a formula A *)
Fixpoint subst_ind_fit (A : formula) (S : subst_ind) : bool :=
match (A, S) with
| (lor B C, lor_ind S_B S_C) =>
    subst_ind_fit B S_B && subst_ind_fit C S_C
| (_, lor_ind _ _) => false
| (lor _ _, _) => false
| (_, _) => true
end.

Fixpoint formula_sub_ind_fit (A E F : formula) (S : subst_ind) : formula :=
match A with
| lor B C =>
  (match S with
  | lor_ind S1 S2 => lor (formula_sub_ind_fit B E F S1)
                         (formula_sub_ind_fit C E F S2)
  | _ => A
  end)
| _ =>
  (match (eq_f A E, S) with
  | (true, (1)) => F
  | _ => A
  end)
end.

Fixpoint formula_sub_ind (A E F : formula) (S : subst_ind) : formula :=
match (subst_ind_fit A S) with
| false => A
| true => formula_sub_ind_fit A E F S
end.

Lemma sub_fit_true : forall (A E F : formula) (S : subst_ind),
  subst_ind_fit A S = true ->
  formula_sub_ind A E F S = formula_sub_ind_fit A E F S.
Proof. intros. unfold formula_sub_ind. destruct A; rewrite H; auto. Qed.

Lemma sub_fit_false : forall (A E F : formula) (S : subst_ind),
  subst_ind_fit A S = false ->
  formula_sub_ind A E F S = A.
Proof. intros. unfold formula_sub_ind. destruct A; rewrite H; auto. Qed.

Lemma formula_sub_ind_fit_0 : forall (A B C : formula),
  formula_sub_ind_fit A B C (0) = A.
Proof.
intros.
destruct A.
- simpl. destruct B; auto. destruct (eq_atom a a0); auto.
- simpl. destruct B; auto. destruct (eq_f A B); auto.
- auto.
- simpl. destruct B; auto. destruct (beq_nat n n0 && eq_f A B); auto.
Qed.

Lemma formula_sub_ind_0 : forall (A B C : formula),
  formula_sub_ind A B C (0) = A.
Proof.
intros. case (subst_ind_fit A (0)) eqn:HA.
- unfold formula_sub_ind.
  destruct A; rewrite HA; rewrite formula_sub_ind_fit_0; auto.
- apply sub_fit_false. apply HA.
Qed.

Lemma formula_sub_ind_lor : forall (A B C D : formula) (S_A S_B : subst_ind),
  subst_ind_fit A S_A && subst_ind_fit B S_B = true ->
  formula_sub_ind (lor A B) C D (lor_ind S_A S_B) = 
  lor (formula_sub_ind A C D S_A) (formula_sub_ind B C D S_B).
Proof.
intros. simpl. rewrite H. unfold formula_sub_ind.
destruct (and_bool_prop _ _ H) as [HA HB].
destruct A; destruct B; rewrite HA, HB; auto.
Qed.

Lemma subst_ind_fit_lor : forall (B C : formula) (S_B S_C : subst_ind),
  subst_ind_fit (lor B C) (lor_ind S_B S_C) = true ->
  subst_ind_fit B S_B && subst_ind_fit C S_C = true.
Proof. intros. apply H. Qed.

Lemma non_target_fit : forall (A : formula),
  subst_ind_fit A (non_target A) = true.
Proof. intros. induction A; auto. simpl. rewrite IHA1, IHA2. auto. Qed.

Lemma non_target_sub' : forall (A C D : formula),
  formula_sub_ind_fit A C D (non_target A) = A.
Proof.
intros. induction A.
- unfold non_target. unfold formula_sub_ind_fit.
  destruct (eq_f (atom a) C); auto.
- unfold non_target. unfold formula_sub_ind_fit.
  destruct (eq_f (neg A) C); auto.
- simpl. rewrite IHA1, IHA2. auto.
- simpl. destruct C; auto. destruct (beq_nat n n0 && eq_f A C); auto.
Qed.

Lemma non_target_sub : forall (A C D : formula),
  formula_sub_ind A C D (non_target A) = A.
Proof.
intros. induction A.
- unfold non_target. apply formula_sub_ind_0.
- unfold non_target. apply formula_sub_ind_0.
- simpl. rewrite non_target_fit, non_target_fit. simpl.
  repeat rewrite non_target_sub'. auto.
- unfold non_target. apply formula_sub_ind_0.
Qed.

Lemma non_target_sub_lor : forall (A B C D : formula) (S : subst_ind),
  formula_sub_ind (lor A B) C D (lor_ind (non_target A) S) =
  lor A (formula_sub_ind B C D S).
Proof.
intros. simpl.
destruct (subst_ind_fit B S) eqn:HB; rewrite non_target_fit; simpl.
- rewrite non_target_sub', sub_fit_true. auto. apply HB.
- rewrite sub_fit_false. auto. apply HB.
Qed.







(* some miscellaneous lemmas about formulas we will need *)
(* *)

(*
Lemma sub_ind_term_sub : forall (A : formula) (n : nat) (t : term),
  non_target A = non_target (substitution A n t).
Admitted.
*)

Lemma non_target_term_sub : forall (A : formula) (n : nat) (t : term),
  non_target A = non_target (substitution A n t).
Proof.
intros. induction A; auto; simpl.
- rewrite IHA1, IHA2. auto.
- destruct (beq_nat n0 n); auto.
Qed.

Lemma formula_sub_ind_closed : forall (A T U : formula),
  closed A = true -> closed U = true ->
  forall (S : subst_ind), closed (formula_sub_ind A T U S) = true.
Proof.
intros A T U. induction A; intros; unfold formula_sub_ind.
- destruct (subst_ind_fit (atom a) S); try apply H.
  simpl. destruct T; try apply H.
  destruct (eq_atom a a0); try apply H.
  destruct S; try apply H. apply H0.
- destruct (subst_ind_fit (neg A) S); try apply H.
  simpl. destruct T; try apply H.
  destruct (eq_f A T); try apply H.
  destruct S; try apply H. apply H0.
- destruct (subst_ind_fit (lor A1 A2) S) eqn:Hs; try apply H. simpl.
  destruct S; try apply H. simpl.
  inversion H. destruct (and_bool_prop _ _ H2).
  inversion Hs. destruct (and_bool_prop _ _ H5).
  clear H. clear Hs. clear H2. clear H5.
  rewrite <- (sub_fit_true _ _ _ _ H4).
  rewrite <- (sub_fit_true _ _ _ _ H6).
  rewrite (IHA1 H1 H0 S1). rewrite (IHA2 H3 H0 S2).
  rewrite H1, H3. auto.
- destruct (subst_ind_fit (univ n A) S); try apply H.
  simpl. destruct T; try apply H.
  destruct (beq_nat n n0 && eq_f A T); try apply H.
  destruct S; try apply H. apply H0.
Qed.








(* Defining double negation substitution in an ftree. First, we define replace
~~E with E at certain places in a formula (given a substitution indicator).
Applyying this operation to an entire ftree, we change the substitution
indicator as the structure of the formula(s) change as we move up the ftree. *)
(*  *)
Definition dub_neg_sub_formula (A E : formula) (S : subst_ind) : formula :=
  formula_sub_ind A (neg (neg E)) E S.

Fixpoint dub_neg_sub_ftree
  (P : ftree) (E : formula) (S : subst_ind) : ftree :=
match (P, S) with
| (node A, _) => P

| (exchange_ab A B P', lor_ind S_B S_A) =>
    exchange_ab
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula B E S_B)
      (dub_neg_sub_ftree P' E (lor_ind S_A S_B))

| (exchange_cab C A B P', lor_ind (lor_ind S_C S_B) S_A) =>
    exchange_cab
      (dub_neg_sub_formula C E S_C)
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula B E S_B)
      (dub_neg_sub_ftree P' E (lor_ind (lor_ind S_C S_A) S_B))

| (exchange_abd A B D P', lor_ind (lor_ind S_B S_A) S_D) =>
    exchange_abd
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula B E S_B)
      (dub_neg_sub_formula D E S_D)
      (dub_neg_sub_ftree P' E (lor_ind (lor_ind S_A S_B) S_D))

| (exchange_cabd C A B D P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D) =>
    exchange_cabd
      (dub_neg_sub_formula C E S_C)
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula B E S_B)
      (dub_neg_sub_formula D E S_D)
      (dub_neg_sub_ftree P' E (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D))

| (contraction_a A P', _) =>
    contraction_a
      (dub_neg_sub_formula A E S)
      (dub_neg_sub_ftree P' E (lor_ind S S))

| (contraction_ad A D P', lor_ind S_A S_D) =>
    contraction_ad
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula D E S_D)
      (dub_neg_sub_ftree P' E (lor_ind (lor_ind S_A S_A) S_D))

| (weakening_ad A D P', lor_ind S_A S_D) =>
    weakening_ad
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula D E S_D)
      (dub_neg_sub_ftree P' E S_D)

| (demorgan_ab A B Q1 Q2, _) =>
    demorgan_ab A B Q1 Q2

| (demorgan_abd A B D Q1 Q2, lor_ind S_AB S_D) =>
    demorgan_abd
      A B
      (dub_neg_sub_formula D E S_D)
      (dub_neg_sub_ftree Q1 E (lor_ind (0) S_D))
      (dub_neg_sub_ftree Q2 E (lor_ind (0) S_D))

| (negation_a A P', _) =>
    (match (eq_f A E, S) with
    | (true, (1)) => P'
    | _ => P
    end)

| (negation_ad A D P', lor_ind S_A S_D) =>
    (match (eq_f A E, S_A) with
    | (true, (1)) => dub_neg_sub_ftree P' E (lor_ind (non_target A) S_D)
    | _ => 
        negation_ad
          A
          (dub_neg_sub_formula D E S_D)
          (dub_neg_sub_ftree P' E (lor_ind (non_target A) S_D))
    end)

| (quantification_a A n t P', _) => P

| (quantification_ad A D n t P', lor_ind S_A S_D) =>
    quantification_ad
      A
      (dub_neg_sub_formula D E S_D)
      n t
      (dub_neg_sub_ftree P' E (lor_ind (0) S_D))

| (w_rule_a A n g, _) => P

| (w_rule_ad A D n g, lor_ind S_A S_D) =>
    w_rule_ad
      A
      (dub_neg_sub_formula D E S_D)
      n
      (fun (n : nat) => dub_neg_sub_ftree (g n) E (lor_ind (non_target A) S_D))

| (cut_ca C A Q1 Q2, _) =>
    cut_ca
      (dub_neg_sub_formula C E S)
      A
      (dub_neg_sub_ftree Q1 E (lor_ind S (non_target A)))
      Q2

| (cut_ad A D Q1 Q2, _) =>
    cut_ad
      A
      (dub_neg_sub_formula D E S)
      Q1
      (dub_neg_sub_ftree Q2 E (lor_ind (0) S))

| (cut_cad C A D Q1 Q2, lor_ind S_C S_D) =>
    cut_cad
      (dub_neg_sub_formula C E S_C)
      A
      (dub_neg_sub_formula D E S_D)
      (dub_neg_sub_ftree Q1 E (lor_ind S_C (non_target A)))
      (dub_neg_sub_ftree Q2 E (lor_ind (0) S_D))

| _ => P
end.

Fixpoint dub_neg_sub_ftree' (P : ftree) (E : formula) (S : subst_ind) : ftree :=
match (subst_ind_fit (ftree_formula P) S) with
| false => P
| true => dub_neg_sub_ftree P E S
end.





(* First, we must prove that dub_neg_sub_ftree' simply changes the base formula
of an ftree the way we expect with dub_neg_sub_formula *)
(* *)
Lemma dub_neg_ftree_formula_aux' :
  forall (P : ftree) (E : formula) (S : subst_ind),
    subst_ind_fit (ftree_formula P) S = false ->
    dub_neg_sub_ftree' P E S = P.
Proof. intros. unfold dub_neg_sub_ftree'. destruct P; rewrite H; auto. Qed.

Lemma dub_neg_ftree_formula_aux :
  forall (P : ftree) (E : formula) (S : subst_ind),
    subst_ind_fit (ftree_formula P) S = false ->
      ftree_formula (dub_neg_sub_ftree' P E S) =
      dub_neg_sub_formula (ftree_formula P) E S.
Proof.
intros. rewrite dub_neg_ftree_formula_aux'.
- unfold dub_neg_sub_formula. rewrite sub_fit_false. auto. apply H.
- apply H.
Qed.

Lemma dub_neg_ftree_formula_true :
  forall (P : ftree) (E : formula) (S : subst_ind),
    subst_ind_fit (ftree_formula P) S = true ->
    dub_neg_sub_ftree P E S = dub_neg_sub_ftree' P E S.
Proof. intros. unfold dub_neg_sub_ftree'. destruct P; rewrite H; auto. Qed.


Lemma dub_neg_ftree_formula' : forall (P : ftree) (E : formula),
  valid P ->
  forall (S : subst_ind),
    subst_ind_fit (ftree_formula P) S = true ->
    ftree_formula (dub_neg_sub_ftree' P E S) =
    dub_neg_sub_formula (ftree_formula P) E S.
Proof.
intros P E.
induction P; try intros H S Hs.

- simpl. inversion H.
  destruct (axiom_atomic _ H1); destruct H0; rewrite H0;
  unfold dub_neg_sub_formula; simpl; destruct S; auto.

- simpl. destruct S.
  + simpl. unfold dub_neg_sub_formula. auto.
  + simpl. unfold dub_neg_sub_formula. auto.
  + inversion Hs. rewrite H1. simpl. unfold dub_neg_sub_formula.
    rewrite formula_sub_ind_lor. auto. apply H1.

- simpl. destruct S.
  + simpl. unfold dub_neg_sub_formula. auto.
  + simpl. unfold dub_neg_sub_formula. auto.
  + destruct S1; inversion Hs.
    rewrite H1. simpl.
    unfold dub_neg_sub_formula.
    rewrite formula_sub_ind_lor, formula_sub_ind_lor. auto.
    * apply (and_bool_prop _ _ H1).
    * apply Hs.

- simpl. destruct S.
  + simpl. unfold dub_neg_sub_formula. auto.
  + simpl. unfold dub_neg_sub_formula. auto.
  + destruct S1; inversion Hs.
    rewrite H1. simpl. unfold dub_neg_sub_formula.
    repeat rewrite formula_sub_ind_lor. auto.
    * apply (and_bool_prop _ _ H1).
    * apply Hs.

- simpl. destruct S.
  + simpl. unfold dub_neg_sub_formula. auto.
  + simpl. unfold dub_neg_sub_formula. auto.
  + destruct S1.
    * inversion Hs.
    * inversion Hs.
    * destruct S1_1; inversion Hs.
      rewrite H1. simpl. unfold dub_neg_sub_formula.
      repeat rewrite formula_sub_ind_lor. auto.
      { destruct (and_bool_prop _ _ H1). destruct (and_bool_prop _ _ H0).
        apply H3. }
      { simpl. apply (and_bool_prop _ _ H1). }
      { simpl. apply H1. }

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
  + unfold dub_neg_sub_formula. simpl. inversion H. rewrite H0.
    rewrite (f_beq_eq _ _ Heq). rewrite eq_f_refl. auto.
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
    * inversion Hs. rewrite H1. simpl.
      rewrite dub_neg_ftree_formula_true.
      { rewrite IHP.
        { inversion H. rewrite H0. unfold dub_neg_sub_formula.
          rewrite non_target_sub_lor. simpl. rewrite H1. rewrite Heq.
          rewrite sub_fit_true. rewrite (f_beq_eq _ _ Heq). auto. apply H1. }
        { apply H. }
        { inversion H. rewrite H0. simpl. rewrite non_target_fit, H1. auto. } }
      { inversion H. rewrite H0. simpl. rewrite non_target_fit, H1. auto. }
    * simpl. inversion Hs.
  + inversion Hs.
  + inversion Hs.
  + destruct S1.
    * apply (subst_ind_fit_lor) in Hs. destruct (and_bool_prop _ _ Hs).
      rewrite H1. simpl. unfold dub_neg_sub_formula.
      rewrite formula_sub_ind_lor, formula_sub_ind_0. auto. apply Hs.
    * inversion Hs. rewrite H1. simpl. unfold dub_neg_sub_formula.
      rewrite formula_sub_ind_lor.
      { simpl. rewrite Heq. auto. }
      { apply Hs. }
    * simpl. inversion Hs.

- simpl. destruct S.
  + simpl. unfold dub_neg_sub_formula. simpl. auto.
  + simpl. unfold dub_neg_sub_formula. simpl. auto.
  + inversion Hs.

- simpl. destruct S.
  + simpl. unfold dub_neg_sub_formula. simpl. auto.
  + simpl. unfold dub_neg_sub_formula. simpl. auto.
  + destruct S1.
      { simpl. inversion Hs. rewrite H1. simpl. unfold dub_neg_sub_formula.
        rewrite formula_sub_ind_lor. auto. apply Hs. }
      { inversion Hs. rewrite H1. simpl. unfold dub_neg_sub_formula.
        simpl. rewrite H1. rewrite sub_fit_true. auto. apply H1. }
      { inversion Hs. }

- intros. simpl. destruct S; simpl; unfold dub_neg_sub_formula; auto.

- intros. simpl. destruct S.
  + inversion H1.
  + inversion H1.
  + destruct S1; inversion H1.
    * rewrite H3. simpl. unfold dub_neg_sub_formula.
      rewrite formula_sub_ind_lor. auto. apply H1.
    * rewrite H3. simpl. unfold dub_neg_sub_formula.
      rewrite formula_sub_ind_lor. auto. apply H1.

- simpl. inversion Hs. rewrite H1. auto.

- simpl. inversion Hs. rewrite H1. auto.

- simpl. destruct S; inversion Hs.
  rewrite H1. simpl. unfold dub_neg_sub_formula.
  rewrite formula_sub_ind_lor. auto. apply H1.
Qed.

Lemma dub_neg_ftree_formula : forall (P : ftree) (E : formula),
  valid P ->
  forall (S : subst_ind),
    ftree_formula (dub_neg_sub_ftree' P E S) =
    dub_neg_sub_formula (ftree_formula P) E S.
Proof.
intros. destruct (subst_ind_fit (ftree_formula P) S) eqn:Hs.
- apply dub_neg_ftree_formula'. apply H. apply Hs.
- apply dub_neg_ftree_formula_aux. apply Hs.
Qed.









(* Now we prove that if we have a valid ftree, replacing performing our
double negation substitution to it results in a valid ftree *)
(* *)
Lemma dub_neg_valid : forall (P : ftree) (E : formula),
  closed E = true -> valid P ->
  forall (S : subst_ind),
    subst_ind_fit (ftree_formula P) S = true ->
    valid (dub_neg_sub_ftree' P E S).
Proof.
intros P E HE.
induction P; try intros H S Hs.

- simpl. destruct (subst_ind_fit f S); apply H.

- simpl. destruct S; inversion Hs.
  rewrite H1. simpl. split.
  + rewrite dub_neg_ftree_formula_true.
    * rewrite dub_neg_ftree_formula.
      { inversion H. rewrite H0. unfold dub_neg_sub_formula.
        rewrite formula_sub_ind_lor. auto. apply (and_bool_symm _ _ H1). }
      { apply H. }
    * inversion H. rewrite H0. simpl. apply (and_bool_symm _ _ H1).
  + rewrite dub_neg_ftree_formula_true.
    * apply IHP. apply H.
      inversion H. rewrite H0. simpl. apply (and_bool_symm _ _ H1).
    * inversion H. rewrite H0. simpl. apply (and_bool_symm _ _ H1).

- simpl. destruct S.
  + inversion Hs.
  + inversion Hs.
  + destruct S1; inversion Hs.
    rewrite H1. simpl. split.
    * rewrite dub_neg_ftree_formula_true.
      { rewrite dub_neg_ftree_formula.
        { inversion H. rewrite H0. unfold dub_neg_sub_formula.
          repeat rewrite formula_sub_ind_lor.
          { auto. }
          { destruct (and_bool_prop _ _ H1). destruct (and_bool_prop _ _ H3).
            rewrite H4, H5. auto. }
          { destruct (and_bool_prop _ _ H1). destruct (and_bool_prop _ _ H3).
            simpl. rewrite H4, H5, H6. auto. } }
        { apply H. } }
      { inversion H. rewrite H0. simpl.
        destruct (and_bool_prop _ _ H1). destruct (and_bool_prop _ _ H3).
        rewrite H4, H5, H6. auto. }
    * rewrite dub_neg_ftree_formula_true.
      { apply IHP. apply H.
        inversion H. rewrite H0. simpl.
        destruct (and_bool_prop _ _ H1). destruct (and_bool_prop _ _ H3).
        rewrite H4, H5, H6. auto. }
      { inversion H. rewrite H0. simpl.
        destruct (and_bool_prop _ _ H1). destruct (and_bool_prop _ _ H3).
        rewrite H4, H5, H6. auto. }

- simpl. destruct S.
  + inversion Hs.
  + inversion Hs.
  + destruct S1; inversion Hs.
    rewrite H1. simpl. split.
    * rewrite dub_neg_ftree_formula_true.
      { rewrite dub_neg_ftree_formula.
        { inversion H. rewrite H0. unfold dub_neg_sub_formula.
          repeat rewrite formula_sub_ind_lor.
          { auto. }
          { destruct (and_bool_prop _ _ H1). destruct (and_bool_prop _ _ H3).
            rewrite H5, H6. auto. }
          { destruct (and_bool_prop _ _ H1). destruct (and_bool_prop _ _ H3).
            simpl. rewrite H4, H5, H6. auto. } }
        { apply H. } }
      { inversion H. rewrite H0. simpl.
        destruct (and_bool_prop _ _ H1). destruct (and_bool_prop _ _ H3).
        rewrite H4, H5, H6. auto. }
    * rewrite dub_neg_ftree_formula_true.
      { apply IHP. apply H.
        inversion H. rewrite H0. simpl.
        destruct (and_bool_prop _ _ H1). destruct (and_bool_prop _ _ H3).
        rewrite H4, H5, H6. auto. }
      { inversion H. rewrite H0. simpl.
        destruct (and_bool_prop _ _ H1). destruct (and_bool_prop _ _ H3).
        rewrite H4, H5, H6. auto. }

- simpl. destruct S.
  + inversion Hs.
  + inversion Hs.
  + destruct S1.
    * inversion Hs.
    * inversion Hs.
    * destruct S1_1; inversion Hs.
      rewrite H1. simpl. split.
      { rewrite dub_neg_ftree_formula_true.
        { rewrite dub_neg_ftree_formula.
          { inversion H. rewrite H0. unfold dub_neg_sub_formula.
            destruct (and_bool_prop _ _ H1). clear H1.
            destruct (and_bool_prop _ _ H3). clear H3.
            destruct (and_bool_prop _ _ H1). clear H1.
            repeat rewrite formula_sub_ind_lor.
            { auto. }
            { rewrite H3,H5. auto. }
            { simpl. rewrite H3, H5, H6. auto. }
            { simpl. rewrite H3, H4, H5, H6. auto. } }
          { apply H. } }
        { inversion H. rewrite H0. simpl.
          destruct (and_bool_prop _ _ H1). clear H1.
          destruct (and_bool_prop _ _ H3). clear H3.
          destruct (and_bool_prop _ _ H1). clear H1.
          rewrite H3, H4, H5, H6. auto. } }
        { destruct (and_bool_prop _ _ H1). clear H1.
          destruct (and_bool_prop _ _ H0). clear H0.
          destruct (and_bool_prop _ _ H1). clear H1.
          rewrite dub_neg_ftree_formula_true.
          { apply IHP. apply H.
            inversion H. rewrite H1. simpl. rewrite H0, H2, H3, H4. auto. }
          { inversion H. rewrite H1. simpl. rewrite H0, H2, H3, H4. auto. } }

- simpl. inversion Hs. rewrite H1. split.
  + rewrite dub_neg_ftree_formula_true.
    * rewrite dub_neg_ftree_formula.
      { unfold dub_neg_sub_formula.
        inversion H. rewrite H0. rewrite formula_sub_ind_lor; auto.
        rewrite H1. auto. }
      { inversion H. apply H2. }
    * inversion H. rewrite H0. simpl. rewrite H1. auto.
  + rewrite dub_neg_ftree_formula_true.
    * apply IHP. apply H. inversion H. rewrite H0. simpl. rewrite H1. auto.
    * inversion H. rewrite H0. simpl. rewrite H1. auto.

- simpl. destruct S; inversion Hs.
  rewrite H1. split.
  + rewrite dub_neg_ftree_formula_true.
    * rewrite dub_neg_ftree_formula.
      { unfold dub_neg_sub_formula.
        inversion H. rewrite H0.
        destruct (and_bool_prop _ _ H1).
        repeat rewrite formula_sub_ind_lor; auto.
        { rewrite H3. auto. }
        { simpl. rewrite H3, H4. auto. } }
      { inversion H. apply H2. }
    * inversion H. rewrite H0. simpl.
      destruct (and_bool_prop _ _ H1). rewrite H3, H4. auto.
  + rewrite dub_neg_ftree_formula_true.
    * apply IHP. apply H. inversion H. rewrite H0. simpl.
      destruct (and_bool_prop _ _ H1). rewrite H3, H4. auto.
    * inversion H. rewrite H0. simpl.
      destruct (and_bool_prop _ _ H1). rewrite H3, H4. auto.

- simpl. destruct S; inversion Hs. rewrite H1. simpl. repeat split.
  + rewrite dub_neg_ftree_formula_true.
    * rewrite dub_neg_ftree_formula. inversion H. rewrite H0. auto. apply H.
    * inversion H. rewrite H0. destruct (and_bool_prop _ _ H1). apply H4.
  + apply formula_sub_ind_closed.
    { destruct H as [ H2 [ H3 H4 ] ]. apply H3. }
    { apply HE. }
  + rewrite dub_neg_ftree_formula_true.
    { apply IHP. 
      { apply H. }
      { inversion H. rewrite H0. destruct (and_bool_prop _ _ H1). apply H4. } }
    { inversion H. rewrite H0. destruct (and_bool_prop _ _ H1). apply H4. }

- simpl. destruct S; apply H.

- simpl. destruct S; try apply H.
  destruct S1; inversion Hs; rewrite H1; simpl.
  + repeat split.
    * rewrite dub_neg_ftree_formula_true, dub_neg_ftree_formula.
      { destruct H as [ H2 [ H3 [ H4 H5 ] ] ]. rewrite H2.
        unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
        { simpl. destruct (eq_f f (neg E)); auto. }
        { rewrite H1. auto. } }
      { apply H. }
      { destruct H as [ H2 [ H3 [ H4 H5 ] ] ]. rewrite H2. simpl. apply H1. }
    * rewrite dub_neg_ftree_formula_true.
      { apply IHP1. apply H.
        destruct H as [ H2 [ H3 [ H4 H5 ] ] ]. rewrite H2. simpl. apply H1. }
      { destruct H as [ H2 [ H3 [ H4 H5 ] ] ]. rewrite H2. simpl. apply H1. }
    * rewrite dub_neg_ftree_formula_true, dub_neg_ftree_formula.
      { destruct H as [ H2 [ H3 [ H4 H5 ] ] ]. rewrite H4.
        unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
        { simpl. destruct (eq_f f0 (neg E)); auto. }
        { rewrite H1. auto. } }
      { apply H. }
      { destruct H as [ H2 [ H3 [ H4 H5 ] ] ]. rewrite H4. simpl. apply H1. }
    * rewrite dub_neg_ftree_formula_true.
      { apply IHP2. apply H.
        destruct H as [ H2 [ H3 [ H4 H5 ] ] ]. rewrite H4. simpl. apply H1. }
      { destruct H as [ H2 [ H3 [ H4 H5 ] ] ]. rewrite H4. simpl. apply H1. }
  + repeat split.
    * rewrite dub_neg_ftree_formula_true, dub_neg_ftree_formula.
      { destruct H as [ H2 [ H3 [ H4 H5 ] ] ]. rewrite H2.
        unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
        { simpl. destruct (eq_f f (neg E)); auto. }
        { rewrite H1. auto. } }
      { apply H. }
      { destruct H as [ H2 [ H3 [ H4 H5 ] ] ]. rewrite H2. simpl. apply H1. }
    * rewrite dub_neg_ftree_formula_true.
      { apply IHP1. apply H.
        destruct H as [ H2 [ H3 [ H4 H5 ] ] ]. rewrite H2. simpl. apply H1. }
      { destruct H as [ H2 [ H3 [ H4 H5 ] ] ]. rewrite H2. simpl. apply H1. }
    * rewrite dub_neg_ftree_formula_true, dub_neg_ftree_formula.
      { destruct H as [ H2 [ H3 [ H4 H5 ] ] ]. rewrite H4.
        unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
        { simpl. destruct (eq_f f0 (neg E)); auto. }
        { rewrite H1. auto. } }
      { apply H. }
      { destruct H as [ H2 [ H3 [ H4 H5 ] ] ]. rewrite H4. simpl. apply H1. }
    * rewrite dub_neg_ftree_formula_true.
      { apply IHP2. apply H.
        destruct H as [ H2 [ H3 [ H4 H5 ] ] ]. rewrite H4. simpl. apply H1. }
      { destruct H as [ H2 [ H3 [ H4 H5 ] ] ]. rewrite H4. simpl. apply H1. }

- simpl. destruct S; destruct (eq_f f E); apply H.

- simpl. destruct S.
  + destruct (eq_f f E); apply H.
  + destruct (eq_f f E); apply H.
  + destruct S1; inversion Hs; rewrite H1; simpl.
    * destruct (eq_f f E).
      { simpl. split.
        { rewrite dub_neg_ftree_formula_true, dub_neg_ftree_formula.
          { inversion H. rewrite H0.
            unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
            { rewrite non_target_sub. auto. }
            { rewrite non_target_fit, H1. auto. } }
          { apply H. }
        { inversion H. rewrite H0. simpl. rewrite non_target_fit, H1. auto. } }
      { inversion H. rewrite dub_neg_ftree_formula_true. apply (IHP H2).
        { rewrite H0. simpl. rewrite non_target_fit, H1. auto. }
        { rewrite H0. simpl. rewrite non_target_fit, H1. auto. } } }
      { simpl. split.
        { rewrite dub_neg_ftree_formula_true, dub_neg_ftree_formula.
          { inversion H. rewrite H0.
            unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
            { rewrite non_target_sub. auto. }
            { rewrite non_target_fit, H1. auto. } }
          { apply H. }
        { inversion H. rewrite H0. simpl. rewrite non_target_fit, H1. auto. } }
      { inversion H. rewrite dub_neg_ftree_formula_true. apply (IHP H2).
        { rewrite H0. simpl. rewrite non_target_fit, H1. auto. }
        { rewrite H0. simpl. rewrite non_target_fit, H1. auto. } } }
    * destruct (eq_f f E).
      { inversion H. rewrite dub_neg_ftree_formula_true.
        { apply IHP.
          { apply H. }
          { rewrite H0. simpl. rewrite non_target_fit, H1. auto. } }
        { rewrite H0. simpl. rewrite non_target_fit, H1. auto. } }
      { simpl. inversion H. split.
        { rewrite dub_neg_ftree_formula_true, dub_neg_ftree_formula.
          { rewrite H0. unfold dub_neg_sub_formula.
            rewrite formula_sub_ind_lor. rewrite non_target_sub. auto.
            rewrite non_target_fit, H1. auto. }
          { apply H. }
          { rewrite H0. simpl. rewrite non_target_fit, H1. auto. } }
      { rewrite dub_neg_ftree_formula_true. apply IHP. apply H.
        { rewrite H0. simpl. rewrite non_target_fit, H1. auto. }
        { rewrite H0. simpl. rewrite non_target_fit, H1. auto. } } }

- simpl. destruct S; apply H.

- simpl. destruct S; try apply H. inversion H as [H0 [H1 H2]].
  destruct S1; inversion Hs; rewrite H4; simpl.
  + repeat split.
    * rewrite dub_neg_ftree_formula_true, dub_neg_ftree_formula.
      { rewrite H0. unfold dub_neg_sub_formula.
        { rewrite formula_sub_ind_lor. simpl.
          { destruct (eq_f (substitution f n t)); auto. }
          { simpl. apply H4. } } }
      { apply H. }
      { rewrite H0. simpl. apply H4. }
    * apply H1.
    * rewrite dub_neg_ftree_formula_true. apply IHP. apply H.
      { rewrite H0. simpl. apply H4. }
      { rewrite H0. simpl. apply H4. }
  + repeat split.
    * rewrite dub_neg_ftree_formula_true, dub_neg_ftree_formula.
      { rewrite H0. unfold dub_neg_sub_formula.
        { rewrite formula_sub_ind_lor. simpl.
          { destruct (eq_f (substitution f n t)); auto. }
          { simpl. apply H4. } } }
      { apply H. }
      { rewrite H0. simpl. apply H4. }
    * apply H1.
    * rewrite dub_neg_ftree_formula_true. apply IHP. apply H.
      { rewrite H0. simpl. apply H4. }
      { rewrite H0. simpl. apply H4. }

- intros. simpl. destruct S; apply H0.

- intros. simpl. destruct S; try apply H0.
  destruct S1.
  + inversion H1. rewrite H3. simpl. intros.
    destruct (valid_w_rule_ad _ _ _ _ H0 m). split.
    * rewrite dub_neg_ftree_formula_true, dub_neg_ftree_formula.
      { rewrite H2. unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
        { rewrite (non_target_term_sub f n (represent m)).
          rewrite non_target_sub. auto. }
        { rewrite (non_target_term_sub f n (represent m)).
          rewrite non_target_fit. apply H3. } }
      { apply H4. }
      { rewrite H2. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
    * rewrite dub_neg_ftree_formula_true.
      { apply H. apply H4. rewrite H2. simpl.
        rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
      { rewrite H2. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
  + inversion H1. rewrite H3. simpl. intros.
    destruct (valid_w_rule_ad _ _ _ _ H0 m). split.
    * rewrite dub_neg_ftree_formula_true, dub_neg_ftree_formula.
      { rewrite H2. unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
        { rewrite (non_target_term_sub f n (represent m)).
          rewrite non_target_sub. auto. }
        { rewrite (non_target_term_sub f n (represent m)).
          rewrite non_target_fit. apply H3. } }
      { apply H4. }
      { rewrite H2. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
    * rewrite dub_neg_ftree_formula_true.
      { apply H. apply H4. rewrite H2. simpl.
        rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
      { rewrite H2. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
  + simpl. intros. apply (valid_w_rule_ad _ _ _ _ H0 m).

- simpl. destruct (subst_ind_fit f S) eqn:Heq; try apply H.
  simpl. inversion H as [H1 [H2 [H3 H4]]]. repeat split.
  + rewrite dub_neg_ftree_formula_true, dub_neg_ftree_formula.
    * simpl. rewrite H1. unfold dub_neg_sub_formula.
      rewrite formula_sub_ind_lor. rewrite non_target_sub. auto.
      rewrite Heq, non_target_fit. auto.
    * apply H2.
    * rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + rewrite dub_neg_ftree_formula_true.
    * apply IHP1. apply H2.
      rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
    * rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + apply H3.
  + apply H4.

- simpl. destruct (subst_ind_fit f0 S) eqn:Heq; try apply H.
  simpl. inversion H as [H1 [H2 [H3 H4]]]. repeat split.
  + apply H1.
  + apply H2.
  + rewrite dub_neg_ftree_formula_true, dub_neg_ftree_formula.
    * simpl. rewrite H3. unfold dub_neg_sub_formula.
      rewrite formula_sub_ind_lor. rewrite formula_sub_ind_0. auto.
      rewrite Heq, non_target_fit. auto.
    * apply H4.
    * rewrite H3. simpl. apply Heq.
  + rewrite dub_neg_ftree_formula_true.
    * apply IHP2. apply H4.
      rewrite H3. simpl. apply Heq.
    * rewrite H3. simpl. apply Heq.

- simpl. inversion H as [H1 [H2 [H3 H4]]]. destruct S; try inversion Hs.
  rewrite H5. simpl. repeat split.
  + rewrite dub_neg_ftree_formula_true, dub_neg_ftree_formula.
    * simpl. rewrite H1. unfold dub_neg_sub_formula.
      rewrite formula_sub_ind_lor. rewrite non_target_sub. auto.
      destruct (and_bool_prop _ _ H5). rewrite H0, non_target_fit. auto.
    * apply H2.
    * rewrite H1. simpl.
      destruct (and_bool_prop _ _ H5). rewrite H0, non_target_fit. auto.
  + rewrite dub_neg_ftree_formula_true.
    * apply IHP1. apply H2.
      rewrite H1. simpl.
      destruct (and_bool_prop _ _ H5). rewrite H0, non_target_fit. auto.
    * rewrite H1. simpl.
      destruct (and_bool_prop _ _ H5). rewrite H0, non_target_fit. auto.
  + rewrite dub_neg_ftree_formula_true, dub_neg_ftree_formula.
    * simpl. rewrite H3. unfold dub_neg_sub_formula.
      rewrite formula_sub_ind_lor. rewrite formula_sub_ind_0. auto.
      destruct (and_bool_prop _ _ H5). apply H6.
    * apply H4.
    * rewrite H3. simpl. destruct (and_bool_prop _ _ H5). apply H6.
  + rewrite dub_neg_ftree_formula_true.
    * apply IHP2. apply H4.
      rewrite H3. simpl. destruct (and_bool_prop _ _ H5). apply H6.
    * rewrite H3. simpl. destruct (and_bool_prop _ _ H5). apply H6.
Qed.



(* We finally show that if the formulas ~~A and/or ~~A \/ D are provable,
so are the formulas A and/or A \/ D *)
(* *)
Lemma double_negation_invertible_a : forall (A : formula),
  provable (neg (neg A)) -> provable A.
Proof.
unfold provable.
intros. destruct H as [t [H Ht]].
eapply ex_intro.
instantiate (1:= dub_neg_sub_ftree' t A (1)). split.
- simpl. rewrite dub_neg_ftree_formula.
  + rewrite H. unfold dub_neg_sub_formula. simpl. rewrite eq_f_refl. auto.
  + apply Ht.
- apply dub_neg_valid.
  + pose proof (provable_closed' t (neg (neg A)) Ht H). inversion H0. auto.
  + apply Ht.
  + rewrite H. auto.
Qed.

Lemma double_negation_invertible_ad : forall (A D : formula),
  provable (lor (neg (neg A)) D) -> provable (lor A D).
Proof.
unfold provable.
intros. destruct H as [t [H Ht]].
eapply ex_intro.
instantiate (1:= dub_neg_sub_ftree' t A (lor_ind (1) (non_target D))). split.
- simpl. rewrite dub_neg_ftree_formula.
  + rewrite H. unfold dub_neg_sub_formula. simpl. rewrite eq_f_refl.
    rewrite non_target_fit. rewrite non_target_sub'. auto.
  + apply Ht.
- apply dub_neg_valid.
  + pose proof (provable_closed' t (lor (neg (neg A)) D) Ht H).
    simpl in H0. apply (and_bool_prop _ _ H0).
  + apply Ht.
  + rewrite H. simpl. apply non_target_fit.
Qed.



















































(*
###############################################################################
Section 10: Cut-elimination in PA_omega.
###############################################################################
*)






































































(*
###############################################################################
Section 11: The consistency of PA
###############################################################################
*)








