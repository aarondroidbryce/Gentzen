Add LoadPath "theories/Maths" as Maths_Facts.
Add LoadPath "theories/Logic" as Systems.

Require Import Lia.
Require Import Nat.

From Maths_Facts Require Import naturals.
From Systems Require Import definitions.

Open Scope bool_scope.

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

Fixpoint list_eqb (l1 l2 : list nat) : bool :=
match l1,l2 with
| [],[] => true
| m :: l1',[] => false
| [], n :: l2' => false
| m :: l1', n :: l2' => nat_eqb m n && list_eqb l1' l2'
end.

(*
Lemma eq_list_symm :
  forall l1 l2,
      eq_list l1 l2 = eq_list l2 l1.
Proof.
induction l1.
- destruct l2;
  reflexivity.
- destruct l2.
  + reflexivity.
  + unfold eq_list; fold eq_list.
    rewrite IHl1.
    rewrite nat_eqb_symm.
    reflexivity.
Qed.
*)

Lemma list_eqb_eq :
    forall (l1 l2 : list nat),
        list_eqb l1 l2 = true ->
            l1 = l2.
Proof.
induction l1;
intros l2 EQ.
- destruct l2.
  + reflexivity. 
  + inversion EQ.
- destruct l2.
  + inversion EQ.
  + unfold list_eqb in EQ; fold list_eqb in EQ.
    destruct (and_bool_prop _ _ EQ) as [EQ1 EQ2].
    rewrite (IHl1 l2 EQ2).
    rewrite (nat_eqb_eq _ _ EQ1).
    reflexivity.
Qed.

(*
Lemma list_ne_cons : forall (l1 : list nat) (n : nat), eq_list l1 (n :: l1) = false.
Proof.
intros l1 n.
induction l1.
- unfold eq_list.
  reflexivity.
- unfold eq_list. fold eq_list.
  case (eq_nat x n) eqn:X1.
  + apply nat_eqb_eq in X1.
    destruct X1.
    rewrite IHl1.
    unfold "&&".
    reflexivity.
  + unfold "&&".
    reflexivity.
Qed.
*)
Lemma list_eqb_refl :
    forall (l : list nat),
        list_eqb l l = true.
Proof.
induction l.
- reflexivity.
- unfold list_eqb; fold list_eqb.
  rewrite nat_eqb_refl.
  apply IHl.
Qed.

(*
Lemma eq_list_decid_conv :
  forall (l1 l2 : list nat),
    eq_list l1 l2 = false -> l1 <> l2.
Proof.
unfold "<>".
intros l1 l2 NEQ EQ.
destruct EQ.
rewrite eq_list_refl in NEQ.
inversion NEQ.
Qed.
*)

Fixpoint remove (n : nat) (l : list nat) : list nat :=
match l with
| nil => nil
| m :: l' =>
  (match nat_eqb m n with
  | true => remove n l'
  | false => m :: (remove n l')
  end)
end.

Fixpoint member (n : nat) (l : list nat) : bool :=
match l with
| nil => false
| m :: l' => 
  (match nat_eqb m n with
  | true => true
  | false => member n l'
  end)
end.

Fixpoint remove_dups (l : list nat) : list nat :=
match l with
| [] => []
| n :: l' => n :: (remove n (remove_dups l'))
end.

Lemma remove_concat :
    forall (n : nat) (l1 l2 : list nat),
        remove n (concat l1 l2) = concat (remove n l1) (remove n l2).
Proof.
intros n l1 l2.
induction l1.
- reflexivity.
- unfold concat.
  unfold remove.
  fold @concat.
  fold remove.
  case (nat_eqb x n) eqn:EQ.
  + apply IHl1.
  + rewrite IHl1.
    reflexivity.
Qed.

Lemma empty_concat_split_empty :
    forall (X : Type) (l1 l2 : list X),
        concat l1 l2 = [] -> l1 = [] /\ l2 = [].
Proof.
intros X l1 l2 CL.
split;
destruct l1;
destruct l2;
try reflexivity;
inversion CL.
Qed.


Lemma remove_dups_empty :
    forall (l : list nat),
        remove_dups l = [] -> l = [].
Proof.
intros l lE.
destruct l.
- reflexivity.
- inversion lE.
Qed.


Lemma remove_comm :
    forall (l : list nat) (n m : nat),
        remove n (remove m l) = remove m (remove n l).
Proof.
intros l n m.
induction l.
- reflexivity.
- destruct (nat_eqb x n) eqn:EQn;
  destruct (nat_eqb x m) eqn:EQm;
  unfold remove;
  rewrite EQn;
  rewrite EQm;
  try rewrite EQn;
  fold remove;
  rewrite IHl;
  reflexivity.
Qed.

Lemma remove_idem :
    forall (l : list nat) (n : nat),
        remove n (remove n l) = remove n l.
Proof.
intros l n.
induction l.
- reflexivity.
- unfold remove.
  case (nat_eqb x n) eqn:EQn;
  try rewrite EQn;
  fold remove;
  rewrite IHl;
  reflexivity.
Qed.

Lemma remove_dups_order :
    forall (l : list nat) (n : nat),
        remove n (remove_dups l) = remove_dups (remove n l).
Proof.
intros l n.
induction l.
- reflexivity.
- case (nat_eqb x n) eqn:EQ;
  unfold remove_dups; fold remove_dups;
  unfold remove; fold remove;
  rewrite EQ.
  + apply nat_eqb_eq in EQ.
    destruct EQ.
    rewrite remove_idem.
    apply IHl.
  + rewrite remove_comm.
    rewrite IHl.
    reflexivity.
Qed.

(*
Lemma remove_n_n :
    forall (l : list nat) (n : nat),
        remove n (remove_dups (n :: l)) = remove n (remove_dups l).
Proof.
intros l n.
rewrite remove_dups_order.
unfold remove; fold remove.
rewrite nat_eqb_refl.
rewrite <- remove_dups_order.
reflexivity.
Qed. *)

Lemma remove_n_dups_empty :
    forall (l : list nat) (n : nat),
        remove n (remove_dups l) = [] ->
            remove_dups l = [n] \/ remove_dups l = [].
Proof.
intros l n RlE.
induction l.
- right.
  reflexivity.
- case (nat_eqb x n) eqn:EQ.
  + unfold remove_dups; fold remove_dups.
    rewrite remove_dups_order in *.
    unfold remove in *; fold remove in *.
    rewrite EQ in RlE.
    apply nat_eqb_eq in EQ.
    destruct EQ.
    rewrite RlE.
    left.
    reflexivity.
  + rewrite remove_dups_order in *.
    unfold remove in *; fold remove in *.
    rewrite EQ in RlE.
    inversion RlE.
Qed.

Lemma remove_dups_twice : forall (l : list nat),
  remove_dups (remove_dups l) = remove_dups l.
Proof.
intros. induction l; auto.
simpl. rewrite remove_dups_order. rewrite remove_idem.
rewrite <- remove_dups_order. rewrite IHl. auto.
Qed.

Lemma member_remove' : forall (l : list nat) (m n : nat),
  nat_eqb m n = false ->
  member n l = true ->
  member n (remove m l) = true.
Proof.
intros.
induction l; auto.
inversion H0. case_eq (nat_eqb x n); intros.
- apply nat_eqb_eq in H1. rewrite H1. simpl. rewrite nat_eqb_symm in H.
  rewrite H. simpl. rewrite nat_eqb_refl. auto.
- rewrite H1 in H2. simpl. rewrite H2. apply IHl in H2.
  case_eq (nat_eqb x m); intros.
  + apply H2.
  + simpl. rewrite H1. apply H2.
Qed.

Lemma member_remove : forall (l : list nat) (m n : nat),
  nat_eqb m n = false ->
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
simpl. simpl in H. destruct (nat_eqb x n) eqn:Hn.
- inversion H.
- apply IHl. apply (member_remove _ x _ Hn), H.
Qed.

Lemma member_concat' : forall (l1 l2 : list nat) (n : nat),
  member n (concat l1 l2) = true ->
  member n l1 = true \/ member n l2 = true.
Proof.
intros. induction l1.
- right. apply H.
- simpl in H. simpl. destruct (nat_eqb x n) eqn:Hx.
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
simpl. case_eq (nat_eqb x n); intros; simpl in H; rewrite H0 in H.
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
| m :: l' => nat_eqb m n && repeated_element_n l' n
end.

Lemma remove_dups_repeated_element : forall (l : list nat) (n : nat),
  repeated_element_n l n = true ->
  sum (remove_dups l = [n]) (l = []).
Proof.
intros. induction l; auto.
left. inversion H.
destruct (and_bool_prop _ _ H1).
destruct (IHl H2) as [H3 | H3].
- simpl. rewrite H3. rewrite (nat_eqb_eq _ _ H0).
  simpl. rewrite nat_eqb_refl. auto.
- rewrite H3. rewrite (nat_eqb_eq _ _ H0). auto.
Qed.

Lemma remove_dups_repeated_element' : forall (l : list nat) (n : nat),
  remove_dups l = [n] ->
  repeated_element_n l n = true.
Proof.
intros. induction l; auto.
simpl. inversion H. destruct (remove_n_dups_empty _ _ H2).
- rewrite nat_eqb_refl, IHl; auto.
- rewrite nat_eqb_refl. destruct l.
  + reflexivity.
  + inversion H0.
Qed.

Lemma repeated_element_n_concat_aux : forall (l1 l2 : list nat) (m n : nat),
  repeated_element_n (concat l1 (m :: l2)) n = true ->
  nat_eqb m n && repeated_element_n l2 n = true.
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

Lemma remove_not_in : forall l n, list_eqb (remove n l) [n] = false.
Proof.
intros. induction l. auto. simpl. case (nat_eqb x n) eqn:X. auto. simpl. rewrite X. auto.
Qed. 

Lemma remove_not_member : forall l n, member n (remove n l) = false.
Proof.
intros. induction l. auto. simpl. case (nat_eqb x n) eqn:X. auto. simpl. rewrite X. auto.
Qed. 

Lemma member_remove_true : forall l n m, member n (remove m l) = true -> member n l = true.
Proof.
intros. induction l; inversion H. rewrite H1. simpl. case (nat_eqb x n) eqn:X; auto. case (nat_eqb x m) eqn:X1; auto. simpl in H1. rewrite X in H1. auto.
Qed.

Lemma remove_member_false : forall l n m, member n l = false -> member n (remove m l) = false.
Proof.
intros. case (nat_eqb n m) eqn:X.
- apply nat_eqb_eq in X. destruct X. apply remove_not_member.
- induction l. auto. simpl. inversion H. case (nat_eqb x n) eqn:X1; auto. inversion H1. rewrite H1. case (nat_eqb x m) eqn:X2; auto. simpl. rewrite X1. auto.
Qed.

Lemma member_remove_dups_true : forall l n, member n (remove_dups l) = true -> member n l = true.
Proof.
intros. induction l; inversion H. simpl. case (nat_eqb x n) eqn:X; auto. rewrite H1. apply IHl. apply (member_remove_true _ _ x). auto.
Qed.  

Lemma remove_dups_concat_self : forall L, remove_dups (concat L L) = remove_dups L.
Proof.
intros. induction L. auto. simpl. rewrite <- IHL. rewrite remove_dups_order. rewrite remove_dups_order. rewrite remove_concat. rewrite remove_concat. simpl. rewrite nat_eqb_refl. auto.
Qed.

Lemma remove_dups_double_cons_ne : forall n m l, remove_dups (n :: m :: l) = n :: m :: l -> nat_eqb m n = false.
Proof.
intros. unfold remove_dups in H. fold remove_dups in H. inversion H. induction l; case (nat_eqb m n) eqn:X; auto. inversion H1.
apply nat_eqb_eq in X. destruct X. rewrite remove_idem in H1. pose proof (remove_not_member (remove_dups (x :: l)) m). rewrite H1 in H0. simpl in H0. rewrite nat_eqb_refl in H0. inversion H0.
Qed.

Lemma remove_idem_not_mem : forall l n, remove n l = l -> member n l = false.
Proof.
intros. induction l. auto. simpl in *. case (nat_eqb x n) eqn:X.
- apply nat_eqb_eq in X. destruct X. pose proof (remove_not_member l x). rewrite H in H0. simpl in H0. rewrite nat_eqb_refl in H0. inversion H0.
- inversion H. rewrite H1. rewrite IHl; auto.
Qed.

Lemma remove_not_mem_idem : forall l n, member n l = false -> remove n l = l.
Proof.
intros. induction l. auto. simpl in *. case (nat_eqb x n) eqn:X. inversion H. rewrite IHl; auto.
Qed.

Lemma remove_dups_idem_remove_false : forall l n, remove_dups (n :: l) = n :: l -> member n l = false.
Proof.
intros. induction l. auto. simpl. rewrite (remove_dups_double_cons_ne _ _ _ H). apply remove_idem_not_mem.
inversion H. rewrite (remove_dups_double_cons_ne _ _ _ H) in H1. inversion H1. rewrite remove_idem. auto.
Qed.

Lemma not_mem_dupes : forall l n, member n l = false -> member n (remove_dups l) = false.
Proof.
intros. induction l. auto. simpl in *. case (nat_eqb x n) eqn:X. inversion H. apply remove_member_false. apply IHl. auto.
Qed.

Lemma remove_dups_idem_remove_triv : forall l n, remove_dups (n :: l) = n :: l -> remove n (n :: l) = l.
Proof.
intros. inversion H. rewrite H1. rename H1 into Z. induction l; simpl; rewrite nat_eqb_refl; auto.
rewrite (remove_dups_double_cons_ne _ _ _ H). rewrite remove_not_mem_idem. auto. pose proof (remove_dups_idem_remove_false _ _ H). simpl in H0. case (nat_eqb x n) eqn:X. inversion H0. auto.
Qed.

Lemma remove_idem_tail : forall l n, remove_dups (n :: l) = n :: l -> remove_dups l = l.
Proof.
intros. inversion H. rewrite H1. rewrite remove_not_mem_idem in H1. auto. pose proof (remove_dups_idem_remove_false _ _ H). case (member n (remove_dups l)) eqn:X; auto. rewrite (member_remove_dups_true _ _ X) in H0. inversion H0.
Qed.

Lemma member_split : forall l n, member n l = true -> exists l1 l2, l = concat l1 (n :: l2).
Proof.
intros. induction l. inversion H. simpl in H. case (nat_eqb x n) eqn:X.
- apply nat_eqb_eq in X. destruct X. exists [], l. auto.
- destruct (IHl H) as [l1 [l2 HL]]. exists (x :: l1), l2. rewrite HL. auto.
Qed.

Lemma member_split_first : forall l n, member n l = true -> exists l1 l2, l = concat l1 (n :: l2) /\ member n l1 = false.
Proof.
intros. induction l. inversion H. simpl in H. case (nat_eqb x n) eqn:X.
- apply nat_eqb_eq in X. destruct X. exists [], l. auto.
- destruct (IHl H) as [l1 [l2 [HL1 Hl2]]]. exists (x :: l1), l2. split. rewrite HL1. auto. simpl. rewrite X. auto.
Qed.

Lemma split_member : forall l1 l2 n, member n (concat l1 (n :: l2)) = true.
Proof.
intros l1. induction l1. intros. simpl. rewrite nat_eqb_refl. auto. intros. simpl. case (nat_eqb x n); auto.
Qed.