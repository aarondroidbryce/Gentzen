Add LoadPath "theories/Maths" as Maths_Facts.
Add LoadPath "theories/Logic" as Systems.

Require Import Lia.
Require Import Nat.
From Maths_Facts Require Import naturals.
From Systems Require Import definitions.
Notation "b1 && b2" := (andb b1 b2).
Notation "b1 || b2" := (orb b1 b2).
Notation eq_nat := Nat.eqb.

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

Fixpoint eq_list (l1 l2 : list nat) : bool :=
match l1,l2 with
| [],[] => true
| m :: l1',[] => false
| [], n :: l2' => false
| m :: l1', n :: l2' => eq_nat m n && eq_list l1' l2'
end.

Definition eq_list_decid_nice (l1 : list nat) :=
  forall (l2 : list nat), eq_list l1 l2 = true -> l1 = l2.

Lemma eq_list_decid' : forall (l1 : list nat), eq_list_decid_nice l1.
Proof.
intros. induction l1.
- unfold eq_list_decid_nice. intros. destruct l2; auto. inversion H.
- unfold eq_list_decid_nice. intros. destruct l2.
  + inversion H.
  + simpl in H. destruct (and_bool_prop _ _ H).
    unfold eq_list_decid_nice in IHl1. rewrite (IHl1 l2 H1).
    rewrite (nat_eq_decid _ _ H0). auto.
Qed.

Lemma eq_list_decid : forall (l1 l2 : list nat),
  eq_list l1 l2 = true -> l1 = l2.
Proof. intros. apply (eq_list_decid' l1). auto. Qed.

Fixpoint remove (n : nat) (l : list nat) : list nat :=
match l with
| nil => nil
| m :: l' =>
  (match eq_nat m n with
  | true => remove n l'
  | false => m :: (remove n l')
  end)
end.

Fixpoint member (n : nat) (l : list nat) : bool :=
match l with
| nil => false
| m :: l' => 
  (match eq_nat m n with
  | true => true
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
simpl. case_eq (eq_nat x n); intros.
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
destruct (eq_nat x n) eqn:Hn; destruct (eq_nat x m) eqn:Hm; simpl;
rewrite Hn; rewrite Hm; auto; simpl.
- rewrite Hn. apply IHl.
- rewrite Hm. apply IHl.
- rewrite Hn, Hm. rewrite IHl. auto.
Qed.

Lemma remove_twice : forall (l : list nat) (n : nat),
  remove n (remove n l) = remove n l.
Proof.
intros. induction l; auto.
destruct (eq_nat x n) eqn:Hn; simpl; rewrite Hn; auto.
simpl. rewrite Hn. rewrite IHl. auto.
Qed.

Lemma remove_dups_order : forall (l : list nat) (n : nat),
  remove n (remove_dups l) = remove_dups (remove n l).
Proof.
intros. induction l; auto.
case_eq (eq_nat x n); intros.
- assert (remove n (x :: l) = remove n l). { simpl. rewrite H. auto. }
  rewrite H0. rewrite <- IHl. pose proof (nat_eq_decid x n H).
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
simpl. rewrite eq_nat_refl.
rewrite <- remove_dups_order. auto.
Qed.

Lemma remove_n_dups_empty : forall (l : list nat) (n : nat),
  remove n (remove_dups l) = [] -> remove_dups l = [n] \/ remove_dups l = [].
Proof.
intros. induction l; auto.
destruct (eq_nat x n) eqn:Hn.
- simpl in H. rewrite Hn in H.
  pose proof (nat_eq_decid x n Hn) as Hx. rewrite Hx in H.
  rewrite remove_twice in H. apply IHl in H. destruct H.
  + simpl. left. rewrite H. rewrite Hx. simpl. rewrite eq_nat_refl. auto.
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

Lemma member_remove' : forall (l : list nat) (m n : nat),
  eq_nat m n = false ->
  member n l = true ->
  member n (remove m l) = true.
Proof.
intros.
induction l; auto.
inversion H0. case_eq (eq_nat x n); intros.
- apply nat_eq_decid in H1. rewrite H1. simpl. apply eq_nat_symm' in H.
  rewrite H. simpl. rewrite eq_nat_refl. auto.
- rewrite H1 in H2. simpl. rewrite H2. apply IHl in H2.
  case_eq (eq_nat x m); intros.
  + apply H2.
  + simpl. rewrite H1. apply H2.
Qed.

Lemma member_remove : forall (l : list nat) (m n : nat),
  eq_nat m n = false ->
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
simpl. simpl in H. destruct (eq_nat x n) eqn:Hn.
- inversion H.
- apply IHl. apply (member_remove _ x _ Hn), H.
Qed.

Lemma member_concat' : forall (l1 l2 : list nat) (n : nat),
  member n (concat l1 l2) = true ->
  member n l1 = true \/ member n l2 = true.
Proof.
intros. induction l1.
- right. apply H.
- simpl in H. simpl. destruct (eq_nat x n) eqn:Hx.
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
simpl. case_eq (eq_nat x n); intros; simpl in H; rewrite H0 in H.
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
| m :: l' => eq_nat m n && repeated_element_n l' n
end.

Lemma remove_dups_repeated_element : forall (l : list nat) (n : nat),
  repeated_element_n l n = true ->
  sum (remove_dups l = [n]) (l = []).
Proof.
intros. induction l; auto.
left. inversion H.
destruct (and_bool_prop _ _ H1).
destruct (IHl H2) as [H3 | H3].
- simpl. rewrite H3. rewrite (nat_eq_decid _ _ H0).
  simpl. rewrite eq_nat_refl. auto.
- rewrite H3. rewrite (nat_eq_decid _ _ H0). auto.
Qed.

Lemma remove_dups_repeated_element' : forall (l : list nat) (n : nat),
  remove_dups l = [n] ->
  repeated_element_n l n = true.
Proof.
intros. induction l; auto.
simpl. inversion H. destruct (remove_n_dups_empty _ _ H2).
- rewrite eq_nat_refl, IHl; auto.
- rewrite eq_nat_refl. apply remove_dups_empty in H0. rewrite H0. auto.
Qed.

Lemma repeated_element_n_concat_aux : forall (l1 l2 : list nat) (m n : nat),
  repeated_element_n (concat l1 (m :: l2)) n = true ->
  eq_nat m n && repeated_element_n l2 n = true.
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

Lemma concat_empty_left : forall (l : list nat), concat [] l = l.
Proof.
auto.
Qed.

Lemma concat_empty_right : forall (l : list nat), concat l [] = l.
Proof.
intros. induction l; simpl; auto. rewrite IHl. auto.
Qed.

Lemma remove_dup_single_right : forall l1 l2 m, remove_dups (concat l1 l2) = [m] -> remove_dups l2 = [m] \/ remove_dups l2 = [].
Proof.
intros. pose proof (remove_dups_repeated_element' _ _ H). pose proof (repeated_element_n_concat _ _ _ H0). destruct H1. destruct (remove_dups_repeated_element _ _ H2); auto. rewrite e. auto.
Qed.

Lemma remove_dup_single_left : forall l1 l2 m, remove_dups (concat l1 l2) = [m] -> remove_dups l1 = [m] \/ remove_dups l1 = [].
Proof.
intros. pose proof (remove_dups_repeated_element' _ _ H). pose proof (repeated_element_n_concat _ _ _ H0). destruct H1. destruct (remove_dups_repeated_element _ _ H1); auto. rewrite e. auto.
Qed.

Lemma remove_not_in : forall l n, eq_list (remove n l) [n] = false.
Proof.
intros. induction l. auto. simpl. case (eq_nat x n) eqn:X. auto. simpl. rewrite X. auto.
Qed. 

Lemma remove_not_member : forall l n, member n (remove n l) = false.
Proof.
intros. induction l. auto. simpl. case (eq_nat x n) eqn:X. auto. simpl. rewrite X. auto.
Qed. 

Lemma member_remove_true : forall l n m, member n (remove m l) = true -> member n l = true.
Proof.
intros. induction l; inversion H. rewrite H1. simpl. case (eq_nat x n) eqn:X; auto. case (eq_nat x m) eqn:X1; auto. simpl in H1. rewrite X in H1. auto.
Qed.

Lemma member_remove_dups_true : forall l n, member n (remove_dups l) = true -> member n l = true.
Proof.
intros. induction l; inversion H. simpl. case (eq_nat x n) eqn:X; auto. rewrite H1. apply IHl. apply (member_remove_true _ _ x). auto.
Qed.  