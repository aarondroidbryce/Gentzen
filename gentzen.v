Require Import Lia.
Require Import Nat.
Require Import Coq.Init.Wf.
Notation "b1 && b2" := (andb b1 b2).
Notation "b1 || b2" := (orb b1 b2).
Notation eq_nat := Nat.eqb.


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

Lemma or_bool_symm : forall (b1 b2 : bool),
  b1 || b2 = true -> b2 || b1 = true.
Proof. intros. case_eq b1; case_eq b2; intros; rewrite H0,H1 in H; auto. Qed.

Lemma or_bool_prop : forall (b1 b2 : bool),
  b1 || b2 = true -> b1 = true \/ b2 = true.
Proof. intros. case_eq b1; case_eq b2; intros; rewrite H0,H1 in H; auto. Qed.


(* Basic properties of natural numbers *)
(* *)
Lemma eq_refl : forall (n : nat), n = n. Proof. auto. Qed.

Lemma eq_succ : forall (n m : nat), S n = S m <-> n = m. Proof. intros. split; auto. Qed.

Lemma leq_refl : forall (n : nat), n <= n. Proof. auto. Qed.

Lemma addends_leq : forall (m n p : nat), n + m = p -> n <= p /\ m <= p.
Proof. intros. lia. Qed.

Lemma eq_nat_refl : forall (n : nat), eq_nat n n = true.
Proof.
intros. induction n as [| n IH].
- auto.
- simpl. apply IH.
Qed.

Fixpoint geq_nat (n m : nat) : bool :=
match n, m with
| 0, 0 => true
| S n', 0 => true
| 0, S m' => false
| S n', S m' => geq_nat n' m'
end.

Lemma geq_type : forall n m, geq_nat n m = true -> n = m \/ n > m.
Proof. induction n. intros. inversion H. destruct m. auto. inversion H1. intros. inversion H. destruct m. lia. pose (IHn _ H1). lia. Qed. 

Lemma succ_geq : forall (n : nat), geq_nat (S n) n = true.
Proof.
intros. induction n.
- auto.
- rewrite <- IHn. auto.
Qed.

Definition lt_nat (n m : nat) : bool := geq_nat m n && negb (eq_nat n m).

Lemma lt_nat_irrefl : forall (n : nat), lt_nat n n = false.
Proof.
intros.
induction n.
- auto.
- rewrite <- IHn. auto.
Qed.

Lemma succ_not_eq : forall (n : nat), eq_nat n (S n) = false.
Proof.
intros. induction n.
- auto.
- rewrite <- IHn. auto.
Qed.


Definition lt_nat_decid_nice (n : nat) :=
  forall (m : nat), lt_nat n m = true -> n < m.

Lemma lt_nat_decid' : forall (n : nat), lt_nat_decid_nice n.
Proof.
intros.
induction n.
- unfold lt_nat_decid_nice. intros. destruct m.
  + inversion H.
  + lia.
- unfold lt_nat_decid_nice. intros. destruct m.
  + inversion H.
  + unfold lt_nat_decid_nice in IHn.
    assert (lt_nat n m = true). case_eq (lt_nat n m); intros; auto.
    * unfold lt_nat in H,H0. simpl in H. rewrite H0 in H. auto.
    * apply IHn in H0. lia.
Qed.

Lemma lt_nat_decid : forall (n m : nat), lt_nat n m = true -> n < m.
Proof. intros. apply lt_nat_decid'. apply H. Qed.

Definition lt_nat_decid_conv_nice (n : nat) :=
  forall (m : nat), n < m -> lt_nat n m = true.

Lemma lt_nat_decid_conv' : forall (n : nat), lt_nat_decid_conv_nice n.
Proof.
intros.
induction n.
- unfold lt_nat_decid_conv_nice. intros. destruct m.
  + inversion H.
  + auto.
- unfold lt_nat_decid_conv_nice. intros. destruct m.
  + inversion H.
  + unfold lt_nat_decid_nice in IHn.
    assert (n < m). { lia. }
    apply IHn in H0. simpl.
    inversion H. unfold lt_nat. rewrite (succ_geq (S n)). simpl.
    rewrite (succ_not_eq n). auto.
    unfold lt_nat. simpl.
    unfold lt_nat in H0. apply H0.
Qed.

Lemma lt_nat_decid_conv : forall (n m : nat), n < m -> lt_nat n m = true.
Proof. intros. apply lt_nat_decid_conv'. apply H. Qed.



Definition nat_eq_decid_nice (n : nat) :=
  forall (m : nat), eq_nat n m = true -> n = m.

Lemma nat_eq_decid' : forall (n : nat), nat_eq_decid_nice n.
Proof.
intros.
induction n.
- unfold nat_eq_decid_nice. intros. destruct m.
  + auto.
  + inversion H.
- unfold nat_eq_decid_nice. intros. destruct m.
  + inversion H.
  + simpl in H. unfold nat_eq_decid_nice in IHn. specialize IHn with m.
    apply IHn in H. rewrite H. auto.
Qed.

Lemma nat_eq_decid : forall (n m : nat), eq_nat n m = true -> n = m.
Proof. intros. apply (nat_eq_decid' n). auto. Qed.

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

Lemma mult_right_incr'_aux : forall (n m p : nat),
  n < m -> n + p * (S n) < m + p * (S m).
Proof. intros. induction p; lia. Qed.

Lemma mult_left_incr_aux_aux : forall (n m p : nat),
  n < m -> p + n * (S p) < p + m * (S p).
Proof. intros. induction p; lia. Qed.

Lemma minus_n_0 : forall (n : nat), n - 0 = n.
Proof. intros. lia. Qed.

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

Lemma nat_exp_monot_lem : forall (n : nat), S n < (2 ^ n) + (2 ^ n).
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

Lemma mult1_r : forall (n : nat), n * 1 = n.
Proof.
intros n.
induction n as [| n' IH].
- auto.
- simpl. rewrite IH. auto.
Qed.


(* Our proof of nat_semiconnex_type is heavily based on the ideas here:
cs.stackexchange.com/questions/18765/theorem-proofs-in-coq *)
Lemma nat_semiconnex : forall (m n : nat), m < n \/ n < m \/ m = n.
Proof. intros. lia. Qed.

Lemma nat_transitive : forall (n n' n'' : nat), n < n' -> n' < n'' -> n < n''.
Proof. intros. lia. Qed.

Lemma leq_prop_sum_aux : forall (m n : nat),
  m = S n \/ m <= n -> (eq_nat m (S n) || eq_nat m n || lt_nat m n) = true.
Proof.
intros. destruct H.
- rewrite <- H. rewrite eq_nat_refl. auto.
- assert (m = n \/ m < n). { lia. } destruct H0.
  + rewrite H0. rewrite eq_nat_refl. case (eq_nat n (S n)); auto.
  + rewrite (lt_nat_decid_conv _ _ H0).
    case (eq_nat m (S n)); case (eq_nat m n); auto.
Qed.

Lemma leq_prop_sum : forall (m n : nat),
  m = S n \/ m <= n -> (m = S n) + (m <= n).
Proof.
intros. pose proof (leq_prop_sum_aux _ _ H).
case_eq (eq_nat m (S n)); case_eq (eq_nat m n); case_eq (lt_nat m n); intros.
- left. apply nat_eq_decid in H3. auto.
- left. apply nat_eq_decid in H3. auto.
- left. apply nat_eq_decid in H3. auto.
- left. apply nat_eq_decid in H3. auto.
- right. apply nat_eq_decid in H2. rewrite H2. auto.
- right. apply nat_eq_decid in H2. rewrite H2. auto.
- right. assert (m < n). { apply (lt_nat_decid _ _ H1). } lia.
- rewrite H1,H2,H3 in H0. inversion H0.
Qed.

Lemma nat_semiconnex_bool : forall (m n : nat), 
  lt_nat m n = true \/ lt_nat n m = true \/ eq_nat m n = true.
Proof.
intros.
destruct (nat_semiconnex m n) as [H | [H | H]].
- left. apply lt_nat_decid_conv. auto.
- right. left. apply lt_nat_decid_conv. auto.
- right. right. rewrite H. apply eq_nat_refl.
Qed.

Definition less (m n : nat) := { z : nat & S (z + m) = n}.

Lemma less_le : forall (m n : nat), less m n -> m < n.
Proof. intros. destruct H as [p H]. lia. Qed.

Theorem nat_semiconnex_type_aux : forall (m n : nat),
  (less n m) + (n = m) + (less m n).
Proof.
intros.
induction n.
- destruct m.
  + left. right. auto.
  + left. left. exists m. lia.
- destruct m.
  + right. exists n. lia.
  + destruct IHn as [[IHn | IHn] | IHn].
    * destruct IHn as [p H]. destruct p.
      { left. right. lia. }
      { left. left. exists p. lia. }
    * right. exists 0. lia.
    * right. destruct IHn as [p H]. exists (S p). lia.
Qed.

Lemma nat_semiconnex_type : forall (m n : nat), (m > n) + (m = n) + (n > m).
Proof.
intros. destruct (nat_semiconnex_type_aux m n) as [[H | H] | H]; auto.
- left. left. apply less_le. auto.
- right. apply less_le. auto.
Qed.

Lemma leq_type : forall (m n : nat), m >= n -> (m > n) + (m = n).
Proof.
intros. destruct (nat_semiconnex_type m n) as [[Hm | Hm] | Hm]; auto. lia.
Qed.

Lemma max_n_n : forall (n : nat), max n n = n.
Proof. intros. lia. Qed.

Lemma max_m_n : forall (m n n' : nat), m >= max n n' -> m >= n /\ m >= n'.
Proof. intros. lia. Qed.

Lemma max_lem1 : forall (m n : nat), eq_nat n (max n m) = false -> max n m > n.
Proof.
intros. destruct (nat_semiconnex m n) as [H0 | [H0 | H0]].
- assert (n = max n m). { lia. }
  rewrite <- H1 in H. rewrite eq_nat_refl in H. inversion H.
- lia.
- rewrite H0 in H. simpl in H. rewrite max_n_n in H.
  rewrite eq_nat_refl in H. inversion H.
Qed.

Lemma max_lem2 : forall (m n : nat), eq_nat m (max n m) = false -> max n m > m.
Proof.
intros. destruct (nat_semiconnex m n) as [H0 | [H0 | H0]].
- lia.
- assert (m = max n m). { lia. }
  rewrite <- H1 in H. rewrite eq_nat_refl in H. inversion H.
- rewrite H0 in H. simpl in H. rewrite max_n_n in H.
  rewrite eq_nat_refl in H. inversion H.
Qed.

Lemma max_split1 : forall (n m : nat), eq_nat n (max n m) = false -> max n m = m.
Proof.
intros n. induction n.
- auto.
- intros. destruct m. rewrite eq_nat_refl in H. inversion H. simpl in H. simpl. apply eq_succ. apply IHn. auto.
Qed.

Lemma max_split2 : forall (m n : nat), eq_nat m (max n m) = false -> max n m = n.
Proof.
intros m. induction m.
- intros. destruct n; auto.
- intros. destruct n. rewrite eq_nat_refl in H. inversion H. simpl in H. simpl. apply eq_succ. apply IHm. auto. 
Qed.


Lemma max_0 : forall (m n : nat), max m n = 0 -> m = 0 /\ n = 0.
Proof. intros. lia. Qed.

Lemma max_simp0 : forall (n : nat), (max n 0) = n.
Proof.
intros n. induction n; auto.
Qed.


Lemma max_succ_0 : forall (m n : nat), max m (S n) = 0 -> False.
Proof. intros. lia. Qed.


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

Lemma eq_nat_symm : forall (n m : nat),
  eq_nat m n = true -> eq_nat n m = true.
Proof. intros. apply nat_eq_decid in H. rewrite H. apply eq_nat_refl. Qed.

Lemma eq_nat_symm' : forall (n m : nat),
  eq_nat m n = false -> eq_nat n m = false.
Proof.
intros. case_eq (eq_nat n m); intros; auto.
apply eq_nat_symm in H0. rewrite H0 in H. inversion H.
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














































































(*
###############################################################################
Section 2: Basic Facts about ordinals under epsilon_0.
###############################################################################
*)


(* We borrows Pierre Casteran's definition of ordinals, which can be found at
www.labri.fr/perso/casteran, under "Ordinal notations and rpo".
The file that we borrow from is EPSILON0.v, in the epsilon0 folder.
In this framework, cons a n b represents  omega^a *(S n)  + b *)
(* *)

Inductive ord : Set :=
| Zero : ord
| cons : ord -> nat -> ord -> ord.


(*Inductive ord : Set :=
| cls : ord
| opn : ord -> ord -> ord.

Require Import List.
Import ListNotations.*)



Declare Scope cantor_scope.

(*Fixpoint is_tower (alpha : ord) : bool :=
  match alpha with
  | cls => false
  | opn cls cls =>true
  | opn a cls => is_tower a
  | _ => false
  end.

Fixpoint depth (alpha : ord) : nat :=
match alpha with
| cls => 0
| opn cls cls => 1
| opn cls a => depth a
| opn a b => max ((depth a) + 1) (depth b)
end.

Fixpoint deepest (alpha : ord) : list ord :=
  match alpha with
  | cls => []
  | opn a b => match eqb (depth alpha) ((depth a) + 1) with
      | true => match eqb (depth alpha) (depth b) with
          | true => (opn a cls) :: deepest b
          | false => [ opn a cls ]
          end
      | false => deepest b
      end
  end.

Theorem deepest_good : forall (alpha : ord), forall beta, In beta (deepest alpha) -> depth beta = depth alpha.
Proof.
intros alpha. induction alpha.
- intros. inversion H.
- intros. unfold deepest in H. fold deepest in H. case (eq_nat (depth (opn alpha1 alpha2)) (depth alpha1 + 1)) eqn: X.
  + case (eq_nat (depth (opn alpha1 alpha2)) (depth alpha2)) eqn: X1.
    * apply nat_eq_decid in X. unfold depth in X. fold depth in X. unfold depth in X1. fold depth in X1. unfold depth. fold depth. destruct alpha1.
      { simpl in X. destruct H. rewrite X. destruct H. auto. destruct alpha2; auto. simpl in H. inversion H. }
      { apply nat_eq_decid in X1. destruct H. destruct H. rewrite X. apply max_simp0. rewrite X1. apply IHalpha2. auto. }
    * unfold depth in X. fold depth in X. unfold depth in X1. fold depth in X1. unfold depth. fold depth. destruct H. destruct H. destruct alpha1. destruct alpha2. auto.
      rewrite eq_nat_refl in X1. inversion X1. apply nat_eq_decid in X. rewrite X. apply max_simp0. inversion H.
  + unfold depth in X. fold depth in X. unfold depth. fold depth. destruct alpha1.
    * destruct alpha2. simpl in H. inversion H. apply IHalpha2. auto.
    * rewrite (max_split1 _ _ (eq_nat_symm' _ _ X)). apply IHalpha2. auto.
Qed.


(*
Fixpoint remove_deep (alpha : ord) : ord :=
  match alpha with 
  | cls => cls
  | opn cls cls => cls
  | opn cls a => opn cls (remove_deep a)
  | opn a b => match ltb (depth a) (depth b) with
      | true => opn a (remove_deep b)
      | false => opn (remove_deep a) b
      end
  end.
  
Theorem rem_dp_wk: forall (alpha : ord), depth (remove_deep alpha) <= depth alpha.
Proof.
intros. induction alpha.
- simpl. auto.
- induction alpha1.
  + induction alpha2; simpl; auto.
  + unfold remove_deep. fold remove_deep. case (ltb (depth (opn alpha1_1 alpha1_2)) (depth alpha2)) eqn:H; simpl; lia.
Qed.
*)

Fixpoint size (alpha : ord) : nat :=
match alpha with
| cls => 2
| opn a b => size a + size b
end.



Fixpoint ord_lt (alpha beta : ord) : bool :=
  match ltb (depth alpha) (depth beta) with
  | true => true
  | false => match ltb (depth beta) (depth alpha) with
      | true => false
      | false => 


match alpha, beta with
| cls, cls => false
| cls, _ => true
| _ , cls => false
| opn cls b, opn cls b' => ord_lt b b'
| opn cls b, opn (opn c' d') b' => ord_lt b b' \/ ord_lt (opn c' d') \/ 

| opn a b, opn a' cls => match b with
    | cls => ord_lt a a'
    | opn c d => ord_lt a a' 
    
    
    
    && ord_lt b a' && ( (ltb (depth a) (depth a') && ltb (depth b) (depth a')) \/ (leb (depth a) (depth a') && leb (depth b) (depth a') && ) )
    end
| opn a b, _ => false
end.
*)

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

(*

Fixpoint depth (alpha : ord) : nat :=
match alpha with 
| Zero => 0
| cons a n b => max ((depth a) + 1) (depth b)
end.

Declare Scope cantor_scope.

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

*)

Definition leq (alpha beta : ord) := alpha = beta \/ alpha < beta.
Notation "alpha <= beta" := (leq alpha beta) : cantor_scope.


(* The ord_lt relation does not fully correspond to the usual < relation on
ordinals. In particular, coeff_lt allows us to show (e.g.) 3 + 4 < 5. However,
its other 3 constructors are accurate, and this will allow us to define a fully
accurate Cantor normal form further down. In the meantime, we prove some basic
order-theoretic properties about ord_lt. *)
(* *)
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
  + lia.
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
| cons_nf : forall a n a' n' b,
    a' < a -> nf a -> nf (cons a' n' b) -> nf (cons a n (cons a' n' b)).

Lemma Zero_nf : nf Zero. Proof. apply zero_nf. Qed.

Definition nat_ord (n : nat) : ord :=
  match n with
  | O => Zero
  | S n' => cons Zero n' Zero
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

Fixpoint ord_eqb (alpha beta : ord) : bool :=
match alpha, beta with
| Zero, Zero => true
| _, Zero => false
| Zero, _ => false
| cons a n b, cons a' n' b' =>
    (match ord_eqb a a' with
    | false => false
    | true =>
        (match eq_nat n n' with
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
    (match ord_ltb a a', ord_eqb a a' with
    | true, _ => true
    | _, false => false
    | _, true =>
        (match lt_nat n n', lt_nat n' n with
        | true, _ => true
        | _, true => false
        | _, _ => ord_ltb b b'
        end)
    end)
end.

Fixpoint nfbool (alpha : ord) : bool := 
match alpha with
  | Zero => true
  | cons a n b => match b with
    | Zero => true
    | cons a' n' b' => (ord_ltb a' a) && nfbool a && nfbool b
  end
end.

(*
Definition cantor := { value : ord | nf value }.

Definition cantor_to_ord (alpha : cantor) : ord := match alpha with | exist _ a _ => a end.

Coercion cantor_to_ord : cantor >-> ord.

Inductive cantor_lt : cantor -> cantor -> Prop :=
|  czero_lt : forall a n b F, cantor_lt (exist _ Zero zero_nf) (exist _ (cons a n b) F)
|  chead_lt :
    forall a a' n n' b b' F F', a < a' ->
                           cantor_lt (exist _ (cons a n b) F) (exist _ (cons a' n' b') F')
|  ccoeff_lt : forall a n n' b b' F F', (n < n')%nat ->
                                 cantor_lt (exist _ (cons a n b) F) (exist _ (cons a n' b') F')
|  ctail_lt : forall a n b b' F F', b < b' ->
                             cantor_lt (exist _ (cons a n b) F) (exist _ (cons a n b') F').

Theorem cantor_implies_ord: forall alpha beta F F', cantor_lt (exist _ alpha F) (exist _ beta F') -> ord_lt alpha beta.
Proof.
intros. induction alpha.
- induction beta.
  + inversion H.
  + apply zero_lt.
- inversion H.
  + destruct H0,H2,H3,H4. apply head_lt. auto.
  + destruct H0,H2,H3,H4. apply coeff_lt. auto.
  + destruct H0,H2,H3,H4. apply tail_lt. auto.
Qed.

Definition cantor_cons (alpha beta : cantor) (n : nat) (H : cantor_lt beta alpha ) : cantor :=
  match alpha, beta with
  | (exist _ a _), (exist _ Zero _) => exist _ (cons a n Zero) (single_nf _ _ _)
  | (exist _ a F), (exist _ (cons a' n' b') F') => exist _ (cons a n (cons a' n' b')) (cons_nf a n a' n' b' (cantor_implies_ord _ _ F F' H) F F')
  end.


Theorem tests : forall (alpha : cantor), nf alpha.
Proof.
intros. destruct alpha. auto.
Qed.

*)

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

(* Defining boolean equality and less than, assuming normal form *)
(* *)

(*
Fixpoint cantor_eqb (alpha beta : cantor) : bool :=
match alpha, beta with
| exist _ Zero _, exist _ Zero _ => true
| _, exist _ Zero _ => false
| exist _ Zero _, _ => false
| exist _ (cons a n b) F, exist _ (cons a' n' b') F' =>
    (match cantor_eqb (exist _ a (nf_hered_first _ _ _ F)) (exist _ a' (nf_hered_first _ _ _ F')) with
    | false => false
    | true =>
        (match eq_nat n n' with
        | false => false
        | true => cantor_eqb (exist _ b (nf_hered_third _ _ _ F)) (exist _ b' (nf_hered_third _ _ _ F'))
        end)
    end)
end.



Fixpoint cantor_ltb (alpha beta : cantor) : bool :=
match alpha, beta with
| exist _ Zero _, exist _ Zero _ => false
| _, exist _ Zero _ => false
| exist _ Zero _, _ => true
| exist _ (cons a n b) _, exist _ (cons a' n' b') _ =>
    (match cantor_ltb (exist _ a _) (exist _ a' _), ord_eqb a a' with
    | true, _ => true
    | _, false => false
    | _, true =>
        (match lt_nat n n', lt_nat n' n with
        | true, _ => true
        | _, true => false
        | _, _ => ord_ltb b b'
        end)
    end)
end.

*)

(* Order-theoretic properties of these boolean relations *)
(* *)
Lemma ord_eqb_refl : forall (alpha : ord), ord_eqb alpha alpha = true.
Proof.
intros.
induction alpha.
- auto.
- simpl. rewrite IHalpha1. rewrite eq_nat_refl. rewrite IHalpha2. auto.
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
      assert (lt_nat n n0 = true). { apply (lt_nat_decid_conv n). apply H1. }
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
Proof. intros. apply ord_lt_ltb_aux. apply H. Qed.

Lemma ltb_trans_aux : forall (a a' b b' : ord) (n n' : nat),
  ord_ltb (cons a n b) (cons a' n' b') = true ->
  (ord_ltb a a' = true \/ (ord_eqb a a' = true /\ lt_nat n n' = true) \/
  (ord_eqb a a' = true /\ n = n' /\ ord_ltb b b' = true)).
Proof.
intros.
inversion H.
case_eq (ord_ltb a a'); auto.
intros. rewrite H0 in H1. case_eq (ord_eqb a a').
- intros. right. rewrite H2 in H1. case_eq (lt_nat n n').
  + intros. rewrite H3 in H1. auto.
  + intros. rewrite H3 in H1. case_eq (lt_nat n' n).
    * intros. rewrite H4 in H1. inversion H1.
    * intros. rewrite H4 in H1. right. split. rewrite H1. auto. split; auto.
      destruct (nat_semiconnex n n').
      { apply lt_nat_decid_conv in H5. rewrite H5 in H3. inversion H3. }
      { destruct H5; auto.
        apply lt_nat_decid_conv in H5. rewrite H5 in H4. inversion H4. }
- intros. left. auto.
Qed.

Definition ord_eqb_eq_aux' (alpha : ord) := forall (beta : ord),
  ord_eqb alpha beta = true -> alpha = beta.

Lemma ord_eqb_eq_aux : forall (alpha : ord), ord_eqb_eq_aux' alpha.
Proof.
intros. induction alpha.
- unfold ord_eqb_eq_aux'. intros. destruct beta; auto. inversion H.
- unfold ord_eqb_eq_aux'. intros. destruct beta; inversion H.
  + case_eq (ord_eqb alpha1 beta1); intros.
    * unfold ord_eqb_eq_aux' in IHalpha1. specialize IHalpha1 with beta1.
      assert (alpha1 = beta1). { apply IHalpha1. apply H0. } rewrite H2.
      case_eq (eq_nat n n0).
      { intros. assert (n = n0). { apply (nat_eq_decid n n0 H3). } rewrite H4.
        case_eq (ord_eqb alpha2 beta2).
        { intros. assert (alpha2 = beta2). { apply IHalpha2. apply H5. }
          rewrite H6. auto. }
        { intros. rewrite H0 in H1. rewrite H3 in H1. rewrite H5 in H1.
          inversion H1. } }
      { intros. rewrite H0 in H1. rewrite H3 in H1. inversion H1. }
    * rewrite H0 in H1. inversion H1.
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

Lemma ord_ltb_neb : forall (alpha beta: ord), ord_ltb alpha beta = true -> ord_eqb alpha beta = false.
Proof.
intros.
case (ord_eqb alpha beta) eqn:H1. apply ord_eqb_eq in H1. destruct H1. rewrite ord_ltb_irrefl in H. inversion H. auto.
Qed.

Fixpoint belongs (alpha beta : ord) : bool :=
match alpha with
| Zero => true
| cons a n b => match beta with
    | Zero => false
    | cons a' n' b' => belongs alpha a' || belongs alpha b' || (belongs a a' && belongs b b' && (geq_nat n' n))
    end
end.

Lemma ord_lt_self : forall alpha n beta, alpha < cons alpha n beta.
Proof.
induction alpha.
- intros. apply zero_lt.
- intros. apply head_lt. apply IHalpha1.
Qed.

Lemma ord_lt_first : forall alpha beta n gamma, alpha < beta -> alpha < cons beta n gamma.
Proof.
induction alpha.
- intros. apply zero_lt.
- induction beta.
  + intros. inversion H.
  + intros. apply head_lt. inversion H.
    * apply IHalpha1. auto.
    * apply ord_lt_self.
    * destruct H4. apply ord_lt_self.
Qed.

Lemma ord_lt_third : forall alpha beta n, alpha < beta -> alpha < cons beta n alpha.
Proof.
induction alpha.
- intros. apply zero_lt.
- induction beta.
  + intros. inversion H.
  + intros. apply head_lt. inversion H.
    * apply ord_lt_first. auto.
    * apply ord_lt_self.
    * destruct H4. apply ord_lt_self.
Qed.

Lemma ord_lt_third_nf : forall alpha beta n, nf (cons beta n alpha) -> alpha < cons beta n alpha.
Proof.
induction alpha.
- intros. apply zero_lt.
- induction beta.
  + intros. inversion H. inversion H3.
  + intros. apply head_lt. inversion H. auto.
Qed.

Lemma nf_less_belong : forall alpha beta, nf alpha -> nf beta -> belongs alpha beta = true -> ord_lt alpha beta \/ alpha = beta.
Proof.
intros alpha. induction alpha.
- intros beta. induction beta.
  + intros. right. reflexivity.
  + intros. left. apply zero_lt.
- induction beta. intros. inversion H1. intros. inversion H1. apply or_bool_prop in H3. destruct H3.
  + apply or_bool_prop in H2. destruct H2.
  * destruct (IHbeta1 H (nf_hered_first _ _ _ H0) H2). 
    { left. apply ord_lt_first. auto. }
    { destruct H3. left. apply ord_lt_self. }
  * destruct (IHbeta2 H (nf_hered_third _ _ _ H0) H2). 
    { left. apply (lt_trans _ beta2 _ H3). apply ord_lt_third_nf. auto. }
    { destruct H3. left. apply ord_lt_third_nf. auto. }
  + apply and_bool_prop in H2. destruct H2. apply and_bool_prop in H2. destruct H2. destruct (IHalpha1 _ (nf_hered_first _ _ _ H) (nf_hered_first _ _ _ H0) H2).
    * left. apply head_lt. auto.
    * destruct H5. apply geq_type in H3. destruct H3.
      { destruct H3. destruct (IHalpha2 _ (nf_hered_third _ _ _ H) (nf_hered_third _ _ _ H0) H4).
        { left. apply tail_lt. auto. }
        { destruct H3. right. auto. } }
      { left. apply coeff_lt. lia. }
Qed.

Definition swap (alpha : ord) : ord :=
match alpha with
| Zero => Zero
| cons a n b => match b with
    | Zero => cons a n Zero
    | cons a' n' b' => cons a' n' (cons a n b)
    end
end.

Fixpoint sort (alpha : ord) : ord :=
match alpha with
| Zero => Zero
| cons a n b => match b with
    | Zero => cons (sort a) n Zero
    | cons a' n' b' => match ord_ltb (sort a) (sort a') with
        | true => cons (sort a') n' (cons (sort a) n (sort b'))
        | false => match ord_eqb (sort a) (sort a') with
            | true => cons (sort a) (S (n + n')) (sort b')
            | false => cons (sort a) n (sort b)
            end 
        end
    end
end.

Fixpoint sorting (n : nat) (alpha : ord) : ord :=
match n with
| 0 => alpha
| S m => sorting m (sort alpha)
end.

Fixpoint size (alpha : ord) : nat :=
match alpha with 
| Zero => 0
| cons a n b => S(size a + size b)
end.

Arguments sort : simpl nomatch.

Lemma sort_type : forall alpha beta gamma n m, sort (cons alpha n (cons beta m gamma)) = cons (sort alpha) n (sort (cons beta m gamma)) \/ sort (cons alpha n (cons beta m gamma)) = cons (sort alpha) (S (n + m)) (sort gamma) \/ sort (cons alpha n (cons beta m gamma)) = cons (sort beta) m (cons (sort alpha) n (sort gamma)).
Proof.
intros. unfold sort. fold sort. case (ord_ltb (sort alpha) (sort beta)); auto. case (ord_eqb (sort alpha) (sort beta)); auto.
Qed.

Lemma sort_case1 : forall alpha beta gamma n m, ord_ltb (sort alpha) (sort beta) = true -> sort (cons alpha n (cons beta m gamma)) = cons (sort beta) m (cons (sort alpha) n (sort gamma)).
Proof.
intros.
unfold sort. fold sort. rewrite H. auto.
Qed.

Lemma sort_case2 : forall alpha beta gamma n m, ord_eqb (sort alpha) (sort beta) = true -> sort (cons alpha n (cons beta m gamma)) = cons (sort alpha) (S (n + m)) (sort gamma).
Proof.
intros. unfold sort. fold sort. rewrite H. apply ord_eqb_eq in H. destruct H. rewrite ord_ltb_irrefl. auto.
Qed.

Lemma sort_case3 : forall alpha beta gamma n m, ord_ltb (sort beta) (sort alpha) = true -> sort (cons alpha n (cons beta m gamma)) = cons (sort alpha) n (sort (cons beta m gamma)).
Proof.
intros. unfold sort. fold sort. rewrite (ltb_asymm _ _ H). rewrite ord_eqb_symm. rewrite (ord_ltb_neb _ _ H). destruct gamma; auto.
Qed.

Lemma sort_not_less : forall alpha, ord_ltb (sort alpha) alpha = false.
Proof.
intros. induction alpha.
- auto.
- assert (ord_ltb alpha1 (sort alpha1) = true \/ ord_eqb alpha1 (sort alpha1) = true).
  { destruct (ord_semiconnex_bool alpha1 (sort alpha1)) as [H | [H | H]]; auto. rewrite IHalpha1 in H. inversion H. }
  assert (ord_ltb alpha2 (sort alpha2) = true \/ ord_eqb alpha2 (sort alpha2) = true).
  { destruct (ord_semiconnex_bool alpha2 (sort alpha2)) as [H1 | [H1 | H1]]; auto. rewrite IHalpha2 in H1. inversion H1. }
  destruct H.
  + destruct alpha2.
    * apply ltb_asymm. apply ord_lt_ltb. apply head_lt. apply ord_ltb_lt. auto.
    * unfold sort. fold sort. apply ltb_asymm. apply ord_lt_ltb. case (ord_ltb (sort alpha1) (sort alpha2_1)) eqn:X.
      { apply head_lt. apply (lt_trans _ (sort alpha1)). apply ord_ltb_lt. auto. apply ord_ltb_lt. auto. }
      { case (ord_eqb (sort alpha1) (sort alpha2_1)) eqn:X1; apply head_lt; apply ord_ltb_lt; auto. }
  + apply ord_eqb_eq in H. unfold sort. fold sort. induction alpha2.
    * destruct H. apply ord_ltb_irrefl.
    * case (ord_ltb (sort alpha1) (sort alpha2_1)) eqn:Y.
      { destruct H. apply ltb_asymm. apply ord_lt_ltb. apply head_lt. apply ord_ltb_lt. apply Y. }
      { case (ord_eqb (sort alpha1) (sort alpha2_1)) eqn:Y1.
        { destruct H. apply ltb_asymm. apply ord_lt_ltb. apply coeff_lt. lia. }
        { destruct H. destruct H0.
          { apply ltb_asymm. apply ord_lt_ltb. apply tail_lt. apply ord_ltb_lt. auto. }
          { apply ord_eqb_eq in H. destruct H. apply ord_ltb_irrefl. } } }
Qed.      

Lemma sort_idempotent_triv : forall alpha, sort (sort (alpha)) = alpha -> sort alpha = alpha.
Proof.
intros. destruct (ord_semiconnex_bool (sort alpha) alpha) as [H1 | [H1 | H1]].
- rewrite sort_not_less in H1. inversion H1.
- rewrite <- H in H1 at 1. rewrite sort_not_less in H1. inversion H1.
- apply ord_eqb_eq in H1. apply H1.
Qed.

Lemma plus_succ_ne : forall n m, ~(S(n + m) = n).
Proof.
intros. lia.
Qed.

Lemma ord_eq_type : forall alpha1 alpha2 beta1 beta2 n1 n2, (cons alpha1 n1 beta1) = cons alpha2 n2 beta2 -> alpha1 = alpha2 /\ n1 = n2 /\ beta1 = beta2.
Proof.
intros. inversion H. auto.
Qed.

Lemma sort_triv_nf : forall alpha, sort alpha = alpha -> nf alpha.
Proof.  
intros. induction alpha.
- apply zero_nf.
- unfold sort in H. fold sort in H. destruct alpha2.
  + inversion H. apply single_nf. rewrite H1. apply IHalpha1. apply H1.
  + case (ord_ltb (sort alpha1) (sort alpha2_1)) eqn:X.
    * inversion H. pose (sort_idempotent_triv _ H3). rewrite e in *. destruct H1,H2,H4. rewrite e in X. rewrite ord_ltb_irrefl in X. inversion X.
    * case (ord_eqb (sort alpha1) (sort alpha2_1)) eqn:X1.
      { inversion H. pose (plus_succ_ne n n0). contradiction. }
      { pose (ord_eq_type _ _ _ _ _ _ H). destruct a as [Y1 [Y2 Y3]].
        apply cons_nf.
        { destruct (ord_semiconnex_bool (sort alpha2_1) (sort alpha1)) as [Y | [Y | Y]].
          { rewrite Y1 in Y. destruct (ord_semiconnex_bool (sort alpha2_1) alpha2_1) as [Z | [Z | Z]].
            { rewrite sort_not_less in Z. inversion Z. }
            { apply ord_ltb_lt. apply (ord_ltb_trans _ (sort alpha2_1)); auto. }
            { apply ord_eqb_eq in Z. destruct Z. apply ord_ltb_lt. auto. } }
          { rewrite Y in X. inversion X. }
          { rewrite ord_eqb_symm in Y. rewrite Y in X1. inversion X1. } }
        { apply IHalpha1. auto. }
        { apply IHalpha2. auto. } }
Qed.

Lemma sort_nf_triv : forall alpha, nf alpha -> sort alpha = alpha.
Proof.
intros. induction alpha.
- auto.
- induction alpha2.
  + simpl. inversion H.  rewrite (IHalpha1 H1). auto.
  + inversion H. destruct H0,H1,H2,H4,H5. unfold sort. fold sort. rewrite (IHalpha1 H6). pose (IHalpha2 H7). unfold sort in e. fold sort in e. destruct b.
      * inversion e. rewrite H1. rewrite H1. apply ord_lt_ltb in H3. pose (ltb_asymm _ _ H3). rewrite e0. pose (ord_ltb_neb _ _ H3). rewrite ord_eqb_symm. rewrite e1. auto.
      * inversion H7. destruct H0,H1,H2,H5,H8. rewrite ord_eqb_symm in e. case (ord_ltb (sort a0) (sort a'0)) eqn:X.
        { inversion e. pose (sort_idempotent_triv _ H5). rewrite e0 in *. destruct H1. apply ord_lt_ltb in H4. rewrite ord_ltb_irrefl in H4. inversion H4. }
        { case (ord_eqb (sort a'0) (sort a0)) eqn:X1.
          { inversion e. pose (plus_succ_ne n0 n'0). contradiction. }
          { pose (ord_eq_type _ _ _ _ _ _ e). destruct a1 as [Y1 [Y2 Y3]]. rewrite Y1 in *. case (ord_ltb a a0) eqn:Z.
            { apply ord_lt_ltb in H3. apply ltb_asymm in H3. rewrite H3 in Z. inversion Z. }
            { case (ord_eqb a a0) eqn:Z1.
              { apply ord_eqb_eq in Z1. destruct Z1. apply lt_irrefl in H3. inversion H3. }
              { rewrite ord_eqb_symm. rewrite X1. rewrite Y3. auto. } } } }
Qed.

Lemma sorting_single : forall n alpha m, sorting n (cons alpha m Zero) = cons (sorting n alpha) m Zero.
Proof.
intros n. induction n.
- intros. auto.
- intros. unfold sorting. fold sorting. apply IHn.
Qed.

Lemma sorting_inverse : forall n alpha, sorting n (sort alpha) = sorting (S n) alpha.
Proof.
intros. auto.
Qed.

Lemma sorting_sort_comm : forall n alpha, sorting (S n) alpha = sort (sorting n alpha).
Proof.
intros n. induction n.
- intros. auto.
- intros. unfold sorting. fold sorting. rewrite <- IHn. auto.
Qed.

Fixpoint wrongness (alpha : ord) : nat :=
match alpha with
| Zero => 0
| cons a n b => match b with
    | Zero => wrongness a
    | cons a' n' b' => match ord_ltb a' a with
        | true => wrongness a + wrongness b
        | false => wrongness a + wrongness b + size b
        end
    end
end.

Lemma wrongness_0_sub : forall alpha n beta, wrongness (cons alpha n beta) = 0 -> wrongness alpha = 0 /\ wrongness beta = 0.
Proof.
unfold wrongness. fold wrongness.
intros. induction beta.
- auto.
- case (ord_ltb beta1 alpha) eqn:X.
  + lia.
  + unfold size in H. fold size in H. rewrite <- plus_n_Sm in H. inversion H.
Qed.

Lemma wrongness_case_1 : forall alpha beta gamma n m, ord_ltb beta alpha = true -> (wrongness (cons alpha n (cons beta m gamma)) = wrongness (alpha) + wrongness (cons beta m gamma)).
Proof.
intros. unfold wrongness. fold wrongness. rewrite H. induction gamma; auto.
Qed.

Lemma wrongness_case_2_ineq : forall alpha beta gamma n m, ord_eqb beta alpha = true -> (wrongness (cons alpha (S (n + m)) gamma) < wrongness (cons alpha n (cons beta m gamma)))%nat.
Proof.
intros. apply ord_eqb_eq in H. destruct H. unfold wrongness. fold wrongness. rewrite ord_ltb_irrefl. unfold size. fold size. destruct gamma.
- lia.
- case (ord_ltb gamma1 beta); lia.
Qed.

Lemma wrongness_case_2 : forall alpha beta gamma n m, ord_eqb beta alpha = true -> wrongness (cons alpha n (cons beta m gamma)) = wrongness (cons alpha (S (n + m)) gamma) + wrongness alpha + size (cons beta m gamma).
Proof.
intros. apply ord_eqb_eq in H. destruct H. unfold wrongness. fold wrongness. rewrite ord_ltb_irrefl. unfold size. fold size. destruct gamma; auto. case (ord_ltb gamma1 beta) eqn:X; lia.
Qed.

Lemma wrongness_case_3 : forall alpha beta gamma n m, ord_ltb alpha beta = true -> wrongness (cons alpha n (cons beta m gamma)) = wrongness (alpha) + wrongness (cons beta m gamma) + size (cons beta m gamma).
Proof.
intros. unfold wrongness. fold wrongness. apply ltb_asymm in H. rewrite H. induction gamma; auto.
Qed.

Lemma wrongness_coeff_inv : forall alpha beta n m, wrongness (cons alpha n beta) = wrongness (cons alpha m beta).
Proof.
intros. auto.
Qed.

Lemma not_wrong_is_nf : forall alpha, wrongness alpha = 0 -> nf alpha.
Proof.
intros. induction alpha.
- apply zero_nf.
- destruct (wrongness_0_sub _ _ _ H). pose (IHalpha1 H0). pose (IHalpha2 H1). destruct alpha2.
  + apply single_nf. auto.
  + apply cons_nf; auto. destruct (ord_semiconnex_bool alpha2_1 alpha1) as [X | [X | X]].
    * apply ord_ltb_lt. auto.
    * rewrite (wrongness_case_3 _ _ _ _ _ X) in H. unfold size in H. fold size in H. rewrite <- plus_n_Sm in H. inversion H.
    * rewrite (wrongness_case_2 _ _ _ _ _ X) in H.  unfold size in H. fold size in H. rewrite <- plus_n_Sm in H. inversion H.
Qed.

Lemma nf_is_not_wrong : forall alpha, nf alpha -> wrongness alpha = 0.
Proof.
intros. induction alpha.
- auto.
- inversion H.
  + simpl. auto.
  + destruct H0,H1,H2. rewrite (wrongness_case_1 _ _ _ _ _ (ord_lt_ltb _ _ H3)). rewrite (IHalpha1 H4). apply (IHalpha2 H5).
Qed.

(*
Lemma wrongness_type : forall alpha n beta, wrongness (cons alpha n beta) = wrongness alpha + wrongness beta \/ wrongness (cons alpha n beta) = S (wrongness alpha + wrongness beta).
Proof.
intros. unfold wrongness. fold wrongness. destruct beta.
- auto.
- case (ord_ltb beta1 alpha); auto.
Qed.

Lemma wrongness_type_proof : forall alpha beta gamma n m, (wrongness (cons alpha n (cons beta m gamma)) = wrongness alpha + wrongness (cons beta m gamma)) \/ (wrongness (cons alpha n (cons beta m gamma)) = S (wrongness alpha + wrongness (cons beta m gamma)) /\ ord_ltb beta alpha = false).
Proof.
intros. unfold wrongness. fold wrongness. case (ord_ltb beta alpha) eqn:X; destruct gamma; try case (ord_ltb gamma1 beta) eqn:X1; auto.
Qed.
*)

(*
Lemma sort_not_confused : forall alpha beta gamma delta, gamma = sort alpha -> delta = sort beta -> ord_ltb gamma delta = true -> ord_ltb alpha beta = true.
Proof.
intros alpha. induction alpha.
- intros. simpl in H. rewrite H in H1. destruct beta.
  + simpl in H0. rewrite H0 in H1. inversion H1.
  + apply ord_lt_ltb. apply zero_lt.
- intros. unfold sort in H. fold sort in H. destruct alpha2.
  + rewrite H in H1. destruct beta.
    * simpl in H0. rewrite H0 in H1. inversion H1.
    * unfold sort in H0. fold sort in H0. destruct beta2.
      { rewrite H0 in H1. simpl in H1. case (ord_ltb (sort alpha1) (sort beta1)) eqn:X.
        { pose (IHalpha1 beta1 (sort alpha1) (sort beta1) (ord_eqb_eq _ _ (ord_eqb_refl _)) (ord_eqb_eq _ _ (ord_eqb_refl _)) X). apply ord_lt_ltb. apply head_lt. apply ord_ltb_lt. exact e. }
        { case (ord_eqb (sort alpha1) (sort beta1)) eqn:X1.
          { case (lt_nat n n0) eqn:X2.
            { case (ord_eqb alpha1 beta1) eqn:X3.
              { apply ord_eqb_eq in X3. destruct X3. apply ord_lt_ltb. apply coeff_lt. apply lt_nat_decid. auto. }
              { admit. } }
            { case (lt_nat n0 n) eqn:X3; inversion H1. } }
          { inversion H1. } } }
          { admit. }
  + admit.

Qed.

Lemma sort_wrong_nf : forall alpha, (wrongness (sort alpha)) = (wrongness alpha) <-> nf alpha.
Proof.
intros. induction alpha.
- split; intros.
  + apply zero_nf.
  + rewrite (sort_nf_triv _ H). auto.
- split; intros.
  + unfold sort in H. fold sort in H. destruct alpha2.
    * simpl in H. apply single_nf. apply IHalpha1. auto.
    * case (ord_ltb (sort alpha1) (sort alpha2_1)) eqn:X.
      { 
        admit. }
      { case (ord_eqb (sort alpha1) (sort alpha2_1)) eqn:X1.
        { inversion H. destruct alpha2_2.
          { unfold sort in H1. fold sort in H1. case (ord_ltb alpha2_1 alpha1) eqn:X2.
            { admit. } admit. } }

        admit. }
  + rewrite (sort_nf_triv _ H). auto.
Admitted.
*)

(*Lemma sort_type : forall alpha beta n, sort (cons alpha n beta) = cons (sort alpha) n (sort beta) \/ *)

Lemma sort_less_wrong_aux : forall alpha beta gamma n m, ord_ltb alpha beta = true -> (wrongness (cons alpha n (cons beta m gamma)) >= wrongness (cons beta m (cons alpha n gamma)))%nat.
Proof.
intros. unfold wrongness. fold wrongness. rewrite H. rewrite (ltb_asymm _ _ H). destruct gamma.
- lia.
- case (ord_ltb gamma1 alpha) eqn:X.
  + rewrite (ord_ltb_trans _ _ _ X H). lia.
  + unfold size. fold size. case (ord_ltb gamma1 beta) eqn:X1; lia.
Qed.

Lemma sort_less_wrong_swap_case : forall alpha beta gamma n m, ord_ltb alpha beta = true -> (wrongness (cons beta m (cons alpha n gamma)) < wrongness (cons alpha n (cons beta m gamma)))%nat.
Proof.
intros. unfold wrongness. fold wrongness. rewrite H. rewrite (ltb_asymm _ _ H). unfold size. fold size. induction gamma.
- lia.
- case (ord_ltb gamma1 alpha) eqn:X.
  + rewrite (ord_ltb_trans _ _ _ X H). lia.
  + case (ord_ltb gamma1 beta) eqn:X1; lia.
Qed.

Lemma wrongness_aux : forall alpha beta gamma n m, ord_ltb (sort beta) (sort alpha) = true -> (wrongness (sort (cons beta m gamma)) < wrongness (cons beta m gamma))%nat -> (wrongness (cons (sort alpha) n (cons (sort beta) m (sort gamma))) >= wrongness (cons (sort alpha) n (sort (cons beta m gamma))))%nat.
Proof.
intros. induction gamma.
- auto.
- destruct (ord_semiconnex_bool (sort beta) (sort gamma1)) as [X | [X | X]].
  + admit.
  + admit.
  + rewrite (sort_case2 _ _ _ _ _ X) in *. rewrite (wrongness_case_1 _ _ _ _ _ H). rewrite (wrongness_case_1 _ _ _ _ _ H).   
Admitted.

(*Lemma weak_wrongness_type : forall alpha n beta, S ((wrongness alpha) + (wrongness beta)) >= wrongness (cons alpha n beta).
Proof.
intros. induction beta.
- simpl. lia.
- unfold size. fold size. destruct (ord_semiconnex_bool beta1 alpha) as [X | [X | X]].
  + rewrite (wrongness_case_1 _ _ _ _ _ X). lia.
  + rewrite (wrongness_case_3 _ _ _ _ _ X). lia.
  + apply ord_eqb_eq in X. destruct X. unfold wrongness. fold wrongness. destruct beta2; case (ord_ltb beta1 beta1) eqn:X; auto. 
Qed.*)
Lemma wrong_last : forall alpha beta gamma delta n m, ord_ltb (cons gamma m delta) beta = false -> ord_ltb gamma alpha = true -> (wrongness beta < wrongness (cons gamma m delta))%nat -> (wrongness (cons alpha n beta) < wrongness (cons alpha n (cons gamma m delta)))%nat.
Proof.
intros. unfold wrongness. fold wrongness. unfold wrongness in H1. fold wrongness in H1. destruct beta.
- case (ord_ltb gamma alpha) eqn:X; lia. 
- case (ord_ltb beta1 alpha) eqn:X; rewrite H0.
  + lia.
  + destruct delta.
    * admit.
    * admit.

Admitted.

Lemma wrong_cons_worse : forall alpha beta n, (wrongness beta <= wrongness (cons alpha n beta))%nat.
Proof.
intros. unfold wrongness. fold wrongness. destruct beta.
- simpl. lia.
- case (ord_ltb beta1 alpha) eqn:X; lia.
Qed.

Lemma sort_less_wrong : forall alpha, (wrongness (sort alpha) < wrongness alpha)%nat \/ nf alpha.
Proof.
intros alpha. induction alpha.
- right. apply zero_nf.
- destruct alpha2.
  + simpl. destruct IHalpha1; auto. right. apply single_nf. auto.
  + destruct (ord_semiconnex_bool (sort alpha1) (sort alpha2_1)) as [X | [X | X]].
    * rewrite (sort_case1 _ _ _ _ _ X). destruct IHalpha1.
      { admit. }
      { destruct IHalpha2.
        { admit. }
        { inversion H0.
          { rewrite (sort_nf_triv _ H) in *. rewrite (sort_nf_triv _ H2) in *.  rewrite (wrongness_case_1 _ _ _ _ _ X).  rewrite (wrongness_case_3 _ _ _ _ _ X). simpl. lia. }
          { destruct H1,H2,H3. rewrite (sort_nf_triv _ H) in *. rewrite (sort_nf_triv _ H6) in *. rewrite (sort_nf_triv _ H5) in *. rewrite (wrongness_case_1 _ _ _ _ _ X).  rewrite (wrongness_case_3 _ _ _ _ _ X).
            rewrite (nf_is_not_wrong _ H5). rewrite (nf_is_not_wrong _ H0). destruct (ord_semiconnex_bool alpha1 a') as [X1 | [X1 | X1]].
            { rewrite (wrongness_case_3 _ _ _ _ _ X1). rewrite (nf_is_not_wrong _ H6). unfold size. fold size. lia. }
            { rewrite (wrongness_case_1 _ _ _ _ _ X1). rewrite (nf_is_not_wrong _ H6). unfold size. fold size. lia. }
            { destruct (ord_eqb_eq _ _ X1). rewrite (wrongness_case_2 _ _ _ _ _ X1). rewrite (wrongness_coeff_inv _ _ (S (n + n')) n'). rewrite (nf_is_not_wrong _ H6). unfold size. fold size. lia. } } } } 
    * rewrite (sort_case3 _ _ _ _ _ X). destruct IHalpha1.
      { destruct IHalpha2.
        { admit. } 
        { inversion H0.
          { destruct H1,H3,H4. rewrite (sort_nf_triv _ H0) in *. rewrite (sort_nf_triv _ H2) in *. rewrite (wrongness_case_1 _ _ _ _ _ X). destruct (ord_semiconnex_bool alpha1 a) as [X1 | [X1 | X1]].
            { rewrite (wrongness_case_3 _ _ _ _ _ X1). lia. }
            { rewrite (wrongness_case_1 _ _ _ _ _ X1). lia. }
            { rewrite ord_eqb_symm in X1. rewrite (wrongness_case_2 _ _ _ _ _ X1). apply ord_eqb_eq in X1. destruct X1. rewrite (wrongness_coeff_inv _ _ n1 (S (n + n1))). lia. } }
          { destruct H1,H2,H3. rewrite (sort_nf_triv _ H0). rewrite (sort_nf_triv _ H5) in X. rewrite (wrongness_case_1 _ _ _ _ _ X). destruct (ord_semiconnex_bool alpha1 a) as [X1 | [X1 | X1]].
            { rewrite (wrongness_case_3 _ _ _ _ _ X1). lia. }
            { rewrite (wrongness_case_1 _ _ _ _ _ X1). lia. }
            { rewrite ord_eqb_symm in X1. rewrite (wrongness_case_2 _ _ _ _ _ X1). apply ord_eqb_eq in X1. destruct X1. rewrite (wrongness_coeff_inv _ _ n1 (S (n + n1))). lia. } } } }
      { destruct IHalpha2.
        { rewrite (sort_nf_triv _ H) in *. pose (sort_not_less alpha2_1). destruct (ord_semiconnex_bool (sort alpha2_1) alpha2_1) as [Y | [Y | Y]].
          { rewrite e in Y. inversion Y. }
          { admit. }
          { apply ord_eqb_eq in Y. rewrite Y in *.  admit. } } 
        { inversion H0.
          { rewrite (sort_nf_triv _ H) in *. rewrite (sort_nf_triv _ H2) in *. right. apply cons_nf; auto. apply ord_ltb_lt. auto. apply single_nf. auto. }
          { rewrite (sort_nf_triv _ H) in *. destruct H3. rewrite (sort_nf_triv _ H0) in *. rewrite (sort_nf_triv _ H5) in *. right. apply cons_nf; auto. apply ord_ltb_lt. auto. } } }
    * rewrite (sort_case2 _ _ _ _ _ X). apply ord_eqb_eq in X. rewrite X in *. rewrite (wrongness_coeff_inv _ _ (S (n + n0)) n0). admit.

    *

    rewrite (wrongness_case_3 _ _ _ _ _ X).
    * rewrite (sort_case2 _ _ _ _ _ X). destruct IHalpha1.
      { left. pose (sort_less_wrong_compact_case (sort alpha1) (sort alpha2_2) n n0). 
      admit. }
      { admit. } 
  destruct (sort_type alpha1 alpha2_1 alpha2_2 n n0) as [H | [H | H]].
    * assert (ord_ltb (sort alpha2_1) (sort alpha1) = true). admit.
      rewrite H. rewrite (wrongness_simpl _ _ _ _ _ H0).

  
  unfold sort. fold sort. destruct (ord_semiconnex_bool (sort alpha1) (sort alpha2_1)) as [X | [X | X]].
    * rewrite X. destruct (leq_type _ _ (sort_less_wrong_aux _ _ (sort alpha2_2) n n0 X)).
      { admit. }
      { rewrite <- e. admit. }
    * rewrite (ltb_asymm _ _ X). rewrite ord_eqb_symm. rewrite (ord_ltb_neb _ _ X). destruct alpha2_2.
      { admit. }
      { admit. }
    * rewrite X. apply ord_eqb_eq in X. rewrite X. rewrite ord_ltb_irrefl. unfold wrongness. fold wrongness.
      assert (Zero < sort)


  + destruct IHalpha1.
    * auto.
    * right. apply single_nf. auto.
  + unfold sort in IHalpha2. fold sort in IHalpha2. destruct alpha2_2.
    * unfold wrongness in IHalpha2. fold wrongness in IHalpha2. admit.
    * 
  
  destruct IHalpha1.
    * destruct IHalpha2.
      { unfold sort in H0. fold sort in H0.
        case (ord_ltb (sort alpha1) (sort alpha2_1)) eqn:X.
        { destruct (wrongness_type_proof (sort alpha2_1) (sort alpha1) (sort alpha2_2) n0 n).
          { rewrite H1. destruct (wrongness_type_proof alpha1 alpha2_1 alpha2_2 n n0).
            { rewrite H2. destruct (wrongness_type (sort alpha1) n (sort alpha2_2)); rewrite H3. 
              destruct (wrongness_type (sort alpha1) n (sort alpha2_2))
            lia. }



          unfold wrongness. fold wrongness. rewrite X. }
        admit. }
      { unfold sort. fold sort. }

  unfold sort. fold sort. unfold wrongness. fold wrongness. unfold sort. fold sort. unfold wrongness. fold wrongness. case (ord_ltb (sort alpha1) (sort alpha2_1)) eqn:X.
    * destruct alpha2_2.
      { case (ord_ltb alpha2_1 alpha1) eqn:X1.
        { destruct IHalpha1.
          { destruct IHalpha2.
            { simpl in H0. simpl. rewrite X. lia. }
            { inversion H0. rewrite (sort_nf_triv _ H2) in *. pose (ord_ltb_trans _ _ _ X X1). rewrite sort_not_less in e. inversion e. } }
          { destruct IHalpha2.
            { simpl in H0. rewrite (sort_nf_triv _ H) in *. simpl. rewrite X. lia. }
            { right. apply cons_nf; auto. apply ord_ltb_lt. auto. } } }
        { destruct IHalpha1.
          { destruct IHalpha2.
            { simpl in H0. simpl. rewrite X. lia. }
            { inversion H0. rewrite (sort_nf_triv _ H2) in *. simpl. rewrite X. lia. } }
          { destruct IHalpha2.
            { simpl in H0. rewrite (sort_nf_triv _ H) in *. simpl. rewrite X. lia. }
            { inversion H0. rewrite (sort_nf_triv _ H) in *. rewrite (sort_nf_triv _ H2) in *. simpl. rewrite X. lia. } } } }
      { 
        admit.

       }
    * case (ord_eqb (sort alpha1) (sort alpha2_1)) eqn:X1.
      { destruct IHalpha1.
        { destruct IHalpha2.
          { admit. }
          { admit. } }
        { destruct IHalpha2.
          { admit. }
          { inversion H0. 
            { rewrite (sort_nf_triv _ H) in *. unfold wrongness. fold wrongness. unfold sort. case (ord_ltb alpha2_1 alpha1) eqn:X2.
              { pose (sort_nf_triv _ H2). rewrite e in *.  apply ord_eqb_eq in X1. destruct X1. rewrite ord_ltb_irrefl in X2. inversion X2. }
              { lia. } }
            { apply ord_eqb_eq in X1. destruct H1,H2,H3. rewrite (sort_nf_triv _ H) in *. rewrite (sort_nf_triv _ H5) in *. destruct X1. unfold wrongness. fold wrongness.
              admit. } 
             } } }
      { unfold wrongness. fold wrongness. unfold sort. fold sort. destruct alpha2_2.
        { assert (ord_ltb (sort alpha2_1) (sort alpha1) = true). { destruct (ord_semiconnex_bool (sort alpha1) (sort alpha2_1)) as [Y | [Y | Y]]; rewrite Y in *. inversion X. auto. inversion X1. } rewrite H. destruct IHalpha1.
          { destruct IHalpha2.
            { simpl in H1. simpl. case (ord_ltb alpha2_1 alpha1) eqn:X2; lia. }
            { inversion H1. simpl. rewrite (sort_nf_triv _ H3). case (ord_ltb alpha2_1 alpha1) eqn:X2; lia. } }
          { destruct IHalpha2.
            { simpl in H1. simpl. rewrite (sort_nf_triv _ H0). case (ord_ltb alpha2_1 alpha1) eqn:X2; lia. }
            { rewrite (sort_nf_triv _ H0) in *. inversion H1. rewrite (sort_nf_triv _ H3) in *. rewrite H. right. apply ord_ltb_lt in H. apply cons_nf; auto. } } }
          { 
            assert (ord_ltb (sort alpha2_1) (sort alpha1) = true). { destruct (ord_semiconnex_bool (sort alpha1) (sort alpha2_1)) as [Y | [Y | Y]]; rewrite Y in *. inversion X. auto. inversion X1. } rewrite H. destruct IHalpha1.

            admit. } }

Qed.

Lemma sorting_works : forall alpha, nf (sorting (size alpha) alpha).
Proof.
intros. induction alpha.
- simpl. apply zero_nf.
- unfold size. fold size. unfold sorting. fold sorting. unfold sort. fold sort. induction alpha2.
  + rewrite plus_n_0. rewrite sorting_single. apply single_nf. rewrite sorting_inverse. rewrite sorting_sort_comm. rewrite (sort_nf_triv _ IHalpha1). auto.
  +    
Qed.

Lemma nat_ref :forall (n : nat), (n <= n)%nat.
Proof.
lia.
Qed.

(*
Fixpoint sorting (alpha : ord) (m : nat) (H : (m >= size alpha)%nat) : ord.
Proof.
destruct alpha. refine Zero.
destruct m. refine Zero.
refine ( match sorting alpha2 (size alpha2) (nat_ref (size alpha2)) with
    | Zero => cons (sorting alpha1 (size alpha1) (nat_ref (size alpha1))) n Zero
    | cons a' n' b' => match ord_ltb a' (sorting alpha1 (size alpha1) (nat_ref (size alpha1))) with
        | true => cons (sorting alpha1 (size alpha1) (nat_ref (size alpha1))) n (sorting alpha2 (size alpha2) (nat_ref(size alpha2)))
        | false => match ord_eqb a' (sorting alpha1 (size alpha1) (nat_ref (size alpha1))) with
            | true => cons a' (n + n') b'
            | false => cons a' n' (sorting (cons (sorting alpha1 (size alpha1) (nat_ref (size alpha1))) n b') m _)
            end
        end
    end).
assert (forall m G , sorting Zero m G = Zero).
{ intros. unfold sorting. admit. }
assert(forall beta m G, (size (sorting (beta) m G) <= size beta)%nat).
{ intros beta. induction beta.
  - intros. rewrite H0. auto.
  - intros. unfold size. fold size.


}
assert(size b' < size alpha2)%nat.
unfold size. fold size. 
admit.
unfold size. fold size.
unfold size in H. fold size in H. destruct (leq_type _ _ (H1 alpha1 (size alpha1) (nat_ref (size alpha1)))). lia. lia.
Admitted.

Fixpoint full_sort (alpha : ord) : ord :=
match alpha with 
| Zero => Zero
| cons a n b => match full_sort b with
    | Zero => cons (full_sort a) n Zero
    | cons a' n' b' => match ord_ltb a' a with
        | true => cons (full_sort a) n (full_sort b)
        | false => cons a' n' (sorting (cons (full_sort a) n (sorting b')))
        end
    end
end.
*)

(*
Theorem sort_big: forall alpha, ord_ltb (full_sort alpha) alpha = false.
Proof.
intros. induction alpha. simpl. auto. simpl. induction (full_sort alpha2).
- induction alpha2.
  + simpl. rewrite IHalpha1. case (ord_eqb (full_sort alpha1) alpha1); auto. rewrite lt_nat_irrefl. auto.
  + inversion IHalpha2.
- case (ord_ltb o1 alpha1) eqn:X.
  + destruct alpha1.
    * apply ord_ltb_lt in X. inversion X.
    * unfold ord_ltb. fold ord_ltb. rewrite IHalpha1. case (ord_eqb (full_sort (cons alpha1_1 n1 alpha1_2)) (cons alpha1_1 n1 alpha1_2)); auto.
      rewrite lt_nat_irrefl. destruct alpha2. auto. inversion IHalpha2.  case (ord_ltb o1 alpha2_1) eqn:X1; auto. case (ord_eqb o1 alpha2_1) eqn:X2; auto.
      case (lt_nat n0 n2) eqn: X3; auto. case (lt_nat n2 n0) eqn: X4; auto. 
  + destruct o2.
    * unfold ord_ltb. fold ord_ltb. rewrite X. case (ord_eqb o1 alpha1); auto. case (lt_nat n0 n) eqn: X1; auto. admit. case (lt_nat n n0) eqn: X2; auto. simpl. destruct alpha2. auto.
      simpl.
    
    rewrite lt_nat_irrefl. destruct alpha2. auto. inversion IHalpha2.  case (ord_ltb o1 alpha2_1) eqn:X1; auto. case (ord_eqb o1 alpha2_1) eqn:X2; auto.
    case (lt_nat n0 n2) eqn: X3; auto. case (lt_nat n2 n0) eqn: X4; auto. 

Qed.


Theorem sort_works : forall gamma alpha beta n, cons alpha n beta = full_sort gamma -> ord_lt beta alpha \/ alpha = Zero.
Proof.
intros gamma. induction gamma.
- intros. simpl in H. inversion H.
- intros. simpl in H. induction (full_sort gamma2).
  + inversion H. induction (full_sort gamma1).
    * auto.
    * left. apply zero_lt.
  + case (ord_ltb o1 gamma1) eqn:X.
    * induction gamma1.
      { apply ord_ltb_lt in X. inversion X. }
      { left. inversion H. destruct (full_sort gamma1_2).
        { }
      
      }
    
    apply ord_eqb_eq in X. inversion H. destruct H0,H2,H3,H4,X. apply (IHgamma2 o1 o1 n1); auto.
    * inversion H. destruct H0. H2,H3,H4. 

Qed.
*)

(*

Fixpoint normalise (alpha : ord) : ord :=
match alpha with 
| Zero => Zero
| cons a n b => match sorting b with
    | Zero => cons (sorting a) n Zero
    | cons a' n' b' => match ord_ltb a' a with
        | true => cons (sorting a) n (sorting b)
        | false => cons a' n' (cons a n b')
        end
    end
end.

Fixpoint compact (alpha : ord) : ord :=
match alpha with
  | Zero => Zero
  | cons a n b => match compact b with
      | Zero => match compact a with
          | Zero => cons Zero n Zero
          | _ => cons (compact a) n Zero
          end
      | (cons a' n' b') => match ord_eqb a' (compact a) with 
          | true => cons (compact a) (n + n') b' 
          | false => cons (compact a) n (compact b)
          end
      end
  end.

Theorem compact_works : forall gamma alpha beta n, cons alpha n beta = compact gamma -> alpha = beta -> alpha = Zero.
Proof.
intros gamma. induction gamma.
- intros. simpl in H. inversion H.
- intros. simpl in H. induction (compact gamma2).
  + induction (compact gamma1).
    * inversion H. auto.
    * inversion H. destruct H0,H2,H3,H4. auto.
  + case (ord_eqb o1 (compact gamma1)) eqn:X.
    *  apply ord_eqb_eq in X. inversion H. destruct H0,H2,H3,H4,X. apply (IHgamma2 o1 o1 n1); auto.
    * inversion H. destruct H0. H2,H3,H4. 

Qed.

(*          | cons a'' n'' b'' => match ord_ltb (normalise a') (normalise a), ord_ltb (normalise b') (normalise a') with
              | true, true => cons (normalise a) n (cons (normalise a') n (normalise b'))
              | true, false => match ord_ltb (normalise b') (normalise a) with
                  | true => cons (normalise a) n (cons (normalise b') n'' (normalise a'))
                  | false => cons (normalise b') n'' (cons (normalise a) n (normalise a'))
                  end
              | false, true => match ord_ltb (normalise b') (normalise a') with
                  | true => cons (normalise a') n' (cons (normalise a) n (normalise b'))
                  | false => cons (normalise a') n' (cons (normalise b') n'' (normalise a))
                  end 
              | false, false => cons (normalise b') n'' (cons (normalise a') n' (normalise a))           
              end
          end
end.
*)



Theorem normalise_works : forall alpha, nf (normalise alpha).
Proof.
intros. induction alpha.
- simpl. apply zero_nf.
- induction alpha2.
  + simpl. apply single_nf. auto.
  + induction alpha2_2.
    * simpl. case (ord_ltb (normalise alpha2_1) (normalise alpha1)) eqn:X.
      { apply cons_nf; auto. apply ord_ltb_lt. auto. }
      { case (ord_eqb (normalise alpha2_1) (normalise alpha1)) eqn:X1.
        { apply single_nf. auto. }
        { apply cons_nf; auto. apply ord_ltb_lt. auto. destruct (ord_semiconnex_bool (normalise alpha1) (normalise alpha2_1)). auto.
          destruct H. rewrite H in X. inversion X. rewrite ord_eqb_symm in H. rewrite H in X1. inversion X1.
          simpl in IHalpha2. apply nf_hered_first in IHalpha2. auto. apply single_nf. auto. } }
    * case (ord_ltb (normalise alpha2_1) (normalise alpha1)) eqn:X.  

Qed.
*)

(* Define ord_add, ord_mult, and ord_exp, which will all assume normal form.
ord_2_exp is based on Pierre Casteran's more general definition of ordinal
exponentiation, restricted to when the base is 2. *)
(* *)
Fixpoint ord_add (alpha beta : ord) : ord :=
match alpha, beta with
| _, Zero => alpha
| Zero, _ => beta
| cons a n b, cons a' n' b' =>
    (match ord_ltb a a' with
    | true => beta
    | false =>
      (match ord_eqb a a' with
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
    ord_mult (cons (cons (cons a n b) n' Zero) 0 Zero) (ord_2_exp b')
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


(* Defining the successor operation for ordinals,
which we will find convenient later *)
(* *)
Fixpoint ord_succ (alpha : ord) : ord :=
match alpha with
| Zero => nat_ord 1
| cons Zero n b => cons Zero (S n) b
| cons a n b => cons a n (ord_succ b)
end.

Lemma ord_succ_monot : forall (alpha : ord), ord_lt alpha (ord_succ alpha).
Proof.
intros.
induction alpha.
- apply zero_lt.
- simpl. destruct alpha1.
  + apply coeff_lt. auto.
  + apply tail_lt. auto.
Qed.

Lemma nf_add_one : forall (alpha : ord),
  nf alpha -> ord_succ alpha = ord_add alpha (cons Zero 0 Zero).
Proof.
intros alpha nf_alpha.
induction alpha as [Zero | a IHa n b IHb].
- simpl. reflexivity.
- destruct a as [Zero | a' n' b'].
  + simpl. assert (S n = n + 0 + 1). { lia. } rewrite H.
    assert (b = Zero).
    { inversion nf_alpha. reflexivity. inversion H3. }
    rewrite H0. reflexivity.
  + simpl. rewrite IHb. reflexivity. inversion nf_alpha.
    * apply Zero_nf.
    * apply H4.
Qed.

Lemma ord_succ_nat : forall (n : nat), ord_succ (nat_ord n) = nat_ord (S n).
Proof.
intros. rewrite nf_add_one.
- assert (cons Zero 0 Zero = nat_ord 1). { auto. } rewrite H.
  rewrite <- ord_add_nat. auto.
  assert (n + 1 = S n). { lia. } rewrite H0. auto.
- apply nf_nat.
Qed.


(* Defining the maximum operation on ordinals *)
(* *)
Fixpoint ord_max (alpha beta : ord) : ord :=
match ord_ltb alpha beta with
| true => beta
| false => alpha
end.

Lemma ord_max_lem1 : forall (alpha beta : ord),
  ord_ltb alpha beta = true -> ord_max alpha beta = beta.
Proof.
intros. destruct alpha; destruct beta; auto; inversion H.
simpl. destruct (ord_ltb alpha1 beta1); auto.
destruct (ord_eqb alpha1 beta1) eqn:Ha; inversion H1.
destruct (lt_nat n n0) eqn:Hn; auto.
destruct (lt_nat n0 n) eqn:Hn0; inversion H1.
destruct (ord_ltb alpha2 beta2); auto. inversion H1.
Qed.

Lemma ord_max_lem2 : forall (alpha beta : ord),
  ord_ltb alpha beta = false -> ord_max alpha beta = alpha.
Proof.
intros. destruct alpha; destruct beta; auto; inversion H.
simpl. destruct (ord_ltb alpha1 beta1); inversion H1.
destruct (ord_eqb alpha1 beta1) eqn:Ha; auto.
destruct (lt_nat n n0) eqn:Hn; inversion H1.
destruct (lt_nat n0 n) eqn:Hn0; auto.
destruct (ord_ltb alpha2 beta2); auto. inversion H1.
Qed.

Lemma ord_max_symm : forall (alpha beta : ord),
  ord_max alpha beta = ord_max beta alpha.
Proof.
intros.
destruct (ord_ltb alpha beta) eqn:H.
- rewrite (ord_max_lem1 _ _ H). symmetry.
  apply ord_max_lem2. apply ltb_asymm. auto.
- destruct (ord_ltb beta alpha) eqn:H0.
  + rewrite (ord_max_lem1 _ _ H0). apply ord_max_lem2. auto.
  + destruct (ord_semiconnex_bool alpha beta) as [H1 | [H1 | H1]].
    { rewrite H1 in H. inversion H. }
    { rewrite H1 in H0. inversion H0. }
    { rewrite (ord_eqb_eq _ _ H1). auto. }
Qed.

Lemma ord_max_succ_l' : forall (alpha beta : ord),
  leq alpha (ord_max alpha beta).
Proof.
intros. destruct alpha.
- destruct beta.
  + simpl. unfold leq. auto.
  + simpl. unfold leq. right. apply zero_lt.
- destruct beta.
  + simpl. unfold leq. auto.
  + simpl. destruct (ord_ltb alpha1 beta1) eqn:H1.
    * unfold leq. right. apply head_lt. apply ord_ltb_lt. auto.
    * destruct (ord_eqb alpha1 beta1) eqn:H2.
      { destruct (lt_nat n n0) eqn:H3.
        { unfold leq. right. rewrite (ord_eqb_eq _ _ H2). apply coeff_lt.
          apply lt_nat_decid. auto. }
        { destruct (lt_nat n0 n) eqn:H4.
          { unfold leq. auto. }
          { rewrite <- (ord_eqb_eq _ _ H2). assert (n = n0) as Hn.
            { destruct (nat_semiconnex_bool n n0) as [H | [H | H]].
              { rewrite H3 in H. inversion H. }
              { rewrite H4 in H. inversion H. }
              { apply nat_eq_decid. auto. } }
            rewrite <- Hn. clear H3. clear H4.
            destruct (ord_ltb alpha2 beta2) eqn:H5.
            { right. apply tail_lt. apply ord_ltb_lt. auto. }
            { left. auto. } } } }
      { unfold leq. auto. }
Qed.

Lemma ord_max_succ_l : forall (alpha beta : ord),
  ord_lt alpha (ord_succ (ord_max alpha beta)).
Proof.
intros. destruct (ord_max_succ_l' alpha beta).
- rewrite <- H. apply ord_succ_monot.
- apply (lt_trans _ (ord_max alpha beta)); auto. apply ord_succ_monot.
Qed.

Lemma ord_max_succ_r' : forall (alpha beta : ord),
  leq beta (ord_max alpha beta).
Proof.
intros. rewrite ord_max_symm. apply ord_max_succ_l'. Qed.

Lemma ord_max_succ_r : forall (alpha beta : ord),
  ord_lt beta (ord_succ (ord_max alpha beta)).
Proof.
intros. destruct (ord_max_succ_r' alpha beta).
- rewrite <- H. apply ord_succ_monot.
- apply (lt_trans _ (ord_max alpha beta)); auto. apply ord_succ_monot.
Qed.

Lemma ord_max_lt1 : forall (alpha beta : ord),
  ord_eqb alpha (ord_max alpha beta) = false ->
  ord_lt alpha (ord_max alpha beta).
Proof.
intros. destruct (ord_max_succ_l' alpha beta); auto.
rewrite <- H0 in H. rewrite ord_eqb_refl in H. inversion H.
Qed.

Lemma ord_max_lt2 : forall (alpha beta : ord),
  ord_eqb beta (ord_max alpha beta) = false ->
  ord_lt beta (ord_max alpha beta).
Proof.
intros. destruct (ord_max_succ_r' alpha beta); auto.
rewrite <- H0 in H. rewrite ord_eqb_refl in H. inversion H.
Qed.


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

(*Lemma nf_hered_third : forall (a b : ord) (n : nat),
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
Qed.*)

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
- unfold leq. right. apply coeff_lt. lia.
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

Lemma nf_add_eq_exp : forall (a a' a'' b b' b'' : ord) (n n' n'' : nat),
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


(* Prove that nf ordinals are closed under addition *)
(* *)
Definition nf_add_nice (alpha : ord) :=
  forall (beta : ord), nf alpha -> nf beta -> nf (ord_add alpha beta).

Lemma nf_add' : forall (alpha : ord), nf_add_nice alpha.
Proof.
intros.
induction alpha.
- unfold nf_add_nice.
  intros.
  simpl.
  destruct beta.
  + simpl. apply zero_nf.
  + apply H0.
- unfold nf_add_nice.
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
              { apply (nf_add_eq_exp A1 a'' beta1 A2 b'' beta2 n1 n'' n0) in HeqA.
                destruct HeqA.
                { rewrite H3. inversion H. apply H7. }
                { rewrite H3. apply (ord_ltb_lt _ _ H1). } }
              { apply (nf_add_eq_exp A1 a'' beta1 A2 b'' beta2 n1 n'' n0) in HeqA.
                destruct HeqA.
                { rewrite H3. inversion H. apply H7. }
                { rewrite H3. apply (ord_ltb_lt _ _ H1). } } } }
          { inversion H. apply H3. apply H6. }
          { rewrite HeqA. unfold nf_add_nice in IHalpha2.
            specialize IHalpha2 with (cons beta1 n0 beta2). apply IHalpha2.
            inversion H. apply Zero_nf. apply H7. apply H0. } } }
Qed.

Lemma nf_add : forall (alpha beta : ord),
  nf alpha -> nf beta -> nf (ord_add alpha beta).
Proof. intros. apply (nf_add' alpha). apply H. apply H0. Qed.


(* Prove that b < c implies a + b < a + c *)
(* *)
Definition add_right_nice (gamma : ord) := forall (alpha beta : ord),
  alpha < beta -> ord_add gamma alpha < ord_add gamma beta.

Lemma add_right_incr' : forall (gamma : ord), add_right_nice gamma.
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
        rewrite ord_ltb_irrefl. rewrite ord_eqb_refl. apply coeff_lt. lia. }

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
          rewrite ord_eqb_refl. apply coeff_lt. lia. } }

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
Proof. apply add_right_incr'. Qed.

Lemma add_right_incr_corr : forall (alpha beta : ord),
  Zero < beta -> alpha < ord_add alpha beta.
Proof.
intros.
pose proof (add_right_incr alpha Zero beta H).
rewrite (ord_add_zero alpha) in H0.
apply H0.
Qed.


(* Prove that b < c implies a * b < a * c (unless a = 0) *)
(* *)
Lemma nf_mult_eval : forall (a a' b b' : ord) (n n' : nat),
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

Definition mult_right_nice (alpha : ord) := 
  alpha = Zero \/ forall (beta gamma : ord),
  beta < gamma -> nf gamma -> ord_mult alpha beta < ord_mult alpha gamma.

Definition mult_right_nice2 (beta alpha : ord) := 
  alpha = Zero \/ forall (gamma : ord),
  beta < gamma -> nf gamma -> ord_mult alpha beta < ord_mult alpha gamma.

Lemma mult_right_incr' : forall (alpha : ord), mult_right_nice alpha.
Proof.
intros.
induction alpha as [| alpha1 IHalpha1 n_alpha alpha2 IHalpha2].
- unfold mult_right_nice. left. auto.
- assert (forall (beta : ord), mult_right_nice2 beta
              (cons alpha1 n_alpha alpha2)).
  { intros. induction beta as [| beta1 IHbeta1 n_beta beta2 IHbeta2].
    { unfold mult_right_nice2. right. intros.
      destruct gamma as [| gamma1 n_gamma gamma2].
      { inversion H. }
      { destruct gamma1.
        { simpl. destruct alpha1.
          { unfold nat_ord. apply zero_lt. }
          { apply zero_lt. } }
        { simpl. apply zero_lt. } } }
    { unfold mult_right_nice2. right. intros gamma H nf_gamma.
      destruct gamma as [| gamma1 n_gamma gamma2].
      { inversion H. }
      { destruct beta1.
        { destruct gamma1.
          { assert (gamma2 = Zero). { inversion nf_gamma. auto. inversion H3. }
            rewrite H0 in H. inversion H.
            { inversion H2. }
            { simpl. apply coeff_lt.
              rewrite minus_n_0. rewrite minus_n_0.
              apply mult_right_incr'_aux. apply H2. }
            { inversion H2. } }
          { simpl. apply head_lt. apply add_right_incr_corr. apply zero_lt. } }
        { destruct gamma1.
          { inversion H. inversion H1. }
          { rewrite nf_mult_eval. rewrite nf_mult_eval.
            { inversion H.
              { apply head_lt. apply add_right_incr. apply H1. }
              { apply coeff_lt. apply H1. }
              { apply tail_lt. unfold mult_right_nice2 in IHbeta2.
                inversion IHbeta2.
                { inversion H9. }
                { apply (H9 gamma2).
                  { apply H1. }
                  { apply (nf_hered_third _ _ _ nf_gamma). } } } }
            { apply zero_lt. }
            { apply zero_lt. } } } } } }
  unfold mult_right_nice. right. intros beta. unfold mult_right_nice2 in H.
  specialize H with beta. destruct H. inversion H. apply H.
Qed.

Lemma mult_right_incr : forall (beta gamma alpha : ord),
  beta < gamma -> Zero < alpha -> nf gamma ->
  ord_mult alpha beta < ord_mult alpha gamma.
Proof.
intros.
pose proof (mult_right_incr' alpha).
unfold mult_right_nice in H2.
destruct H2.
- rewrite H2 in H0. inversion H0.
- apply (H2 _ _ H H1).
Qed.


(* Prove that nf ordinals are closed under multiplication *)
(* *)
Definition nf_mult_nice (alpha : ord) := forall (beta : ord),
  nf alpha -> nf beta -> nf (ord_mult alpha beta).

Lemma nf_mult' : forall (alpha : ord), nf_mult_nice alpha.
Proof.
intros.
induction alpha as [| a IHa n b IHb].
- unfold nf_mult_nice. intros. destruct beta as [| a' n' b'].
  + auto.
  + auto.
- unfold nf_mult_nice. intros. induction beta as [| a' IHa' n' b' IHb'].
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
           { rewrite nf_mult_eval in H3.
              { inversion H3. inversion H0.
                apply add_right_incr. apply H10. }
              { apply zero_lt. } } } }
      { apply nf_add.
        apply (nf_hered_first a b n H).
        apply (nf_hered_first a' b' n' H0). }
      { rewrite <- H3. apply IHb'. apply (nf_hered_third _ _ _ H0). } } } }
    destruct a' as [| a'' n'' b''].
    { simpl. apply (nf_scalar _ _ _ _ H). }
    { rewrite nf_mult_eval. apply H1. apply zero_lt. }
Qed.

Lemma nf_mult : forall (alpha beta : ord),
  nf alpha -> nf beta -> nf (ord_mult alpha beta).
Proof. intros. apply (nf_mult' alpha). apply H. apply H0. Qed.


(* Prove that nf ordinals are closed under 2_exp *)
(* *)
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


(* Prove that no nf ordinal besides w is a fixed point of the map a |-> 2^a *)
(* *)
Lemma one_right_mult_ident : forall (alpha : ord),
  alpha = ord_mult alpha (nat_ord 1).
Proof.
intros.
induction alpha as [| alpha1 IHalpha1 n_alpha alpha2 IHalpha2].
- auto.
- simpl. assert (n_alpha * 1 - 0 = n_alpha). { lia. } rewrite H. auto.
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

Lemma nat_ord_lt : forall (n m : nat), (n < m)%nat -> nat_ord n < nat_ord m.
Proof.
intros.
induction n; destruct m.
- inversion H.
- simpl. apply zero_lt.
- inversion H.
- simpl. apply coeff_lt. lia.
Qed.

Lemma nat_ord_eq : forall (n m : nat), n = m -> nat_ord n = nat_ord m.
Proof. auto. Qed.

Lemma exp_geq_1 : forall (b : ord), nf b -> Zero < ord_2_exp b.
Proof.
intros b nf_b.
induction b as [| a' IHa' n' b' IHb'].
- simpl. apply zero_lt.
- destruct a' as [| a'' n'' b''].
  + simpl. assert (Zero = nat_ord 0). { auto. } rewrite H.
    apply nat_ord_lt. rewrite plus_n_0.
    pose proof (nat_exp_monot_lem n'). lia.
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
(*pose proof (exp_geq_1).
pose proof (ord_mult_exp_monot_aux1).*)
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
    rewrite H0. apply nat_ord_lt. rewrite plus_n_0.
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

Lemma ord_2_exp_fp_true : forall (alpha : ord), nf alpha ->
  alpha < ord_2_exp alpha.
Proof.
intros alpha nf_alpha.
assert (ord_eqb alpha (cons (nat_ord 1) 0 Zero) = true \/ ord_eqb alpha (cons (nat_ord 1) 0 Zero) = false).
{ destruct (ord_eqb alpha (cons (nat_ord 1) 0 Zero)); auto. }
destruct H.
- apply ord_eqb_eq in H. rewrite H. simpl. apply ord_ltb_lt. auto.
- pose proof (ord_2_exp_fp alpha nf_alpha). destruct H0.
  + auto.
  + rewrite H0 in H. inversion H.  
Qed.

Lemma ord_mult_zero_left : forall (alpha : ord), ord_mult Zero alpha = Zero.
Proof.
intros. induction alpha.
- simpl. auto.
- simpl. auto.
Qed.

Lemma ord_mult_zero_right : forall (alpha : ord), ord_mult alpha Zero = Zero.
Proof.
intros. induction alpha.
- simpl. auto.
- simpl. auto.
Qed.

Lemma ord_eq_split : forall alpha1 beta1 alpha2 beta2 n1 n2, alpha1 = alpha2 -> beta1 = beta2 -> n1 = n2 ->  (cons alpha1 n1 beta1) = (cons alpha2 n2 beta2).
Proof.
intros. apply ord_eqb_eq. simpl. rewrite H,H0,H1. repeat rewrite ord_eqb_refl. rewrite eq_nat_refl. auto.
Qed.

Lemma ord_lt_ne : forall beta alpha, ord_ltb alpha beta = true -> ord_eqb alpha beta = false.
Proof.
intros beta.
induction beta.
- intros. induction alpha.
  + inversion H.
  + simpl. auto.
- intros. induction alpha.
  + simpl. auto.
  + inversion H. case (ord_ltb alpha1 beta1) eqn:H2.
    * simpl. rewrite (IHbeta1 _ H2). auto.
    * case (ord_eqb alpha1 beta1) eqn:H3.
      { case (lt_nat n0 n) eqn:H4.
        { simpl. rewrite H3. case (eq_nat n0 n) eqn:H5.
           { apply nat_eq_decid in H5. destruct H5. rewrite lt_nat_irrefl in H4. inversion H4. }
           { auto. }
           }
        { case (lt_nat n n0) eqn:H5.
          { inversion H1. }
          { simpl. rewrite H3. case (eq_nat n0 n) eqn:H6.
            { apply (IHbeta2 _ H1). }
            { auto. }
            }
          }
        }
      { inversion H1. }
Qed.

Lemma ord_add_ne : forall alpha beta gamma n, ord_eqb alpha (ord_add alpha (cons beta n gamma)) = false.
Proof.
intros.
pose proof (add_right_incr alpha _ _ (zero_lt beta n gamma)).
rewrite ord_add_zero in H.
apply ord_lt_ltb in H.
apply ord_lt_ne.
auto.
Qed.

Definition ord_mult_distr_nice (alpha : ord) := forall (beta gamma : ord), nf beta -> nf gamma -> ord_mult alpha (ord_add beta gamma) = ord_add (ord_mult alpha beta) (ord_mult alpha gamma). 

Fixpoint w_tower (n : nat) : ord :=
match n with
| 0 => cons Zero 0 Zero
| S n' => cons (w_tower n') 0 Zero
end.
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
match s, t with
| zero, zero => true
| succ s', succ t' => eq_term s' t'
| plus s1 s2, plus t1 t2 => eq_term s1 t1 && eq_term s2 t2
| times s1 s2, times t1 t2 => eq_term s1 t1 && eq_term s2 t2
| var m, var n => eq_nat m n
| _, _ => false
end.

Fixpoint eq_atom (a b : atomic_formula) : bool :=
match a, b with
| equ s1 s2, equ t1 t2 => eq_term s1 t1 && eq_term s2 t2
end.

Fixpoint eq_f (a b : formula) : bool :=
match a, b with
| atom a', atom b' => eq_atom a' b'
| neg a', neg b' => eq_f a' b'
| lor a1 a2, lor b1 b2 => eq_f a1 b1 && eq_f a2 b2
| univ m a', univ n b' => eq_nat m n && eq_f a' b'
| _, _ => false
end.

Lemma eq_term_refl : forall (t : term), eq_term t t = true.
Proof.
intros t. induction t; auto.
- simpl. rewrite IHt1. apply IHt2.
- simpl. rewrite IHt1. apply IHt2.
- simpl. apply eq_nat_refl.
Qed.

Lemma eq_atom_refl : forall (a : atomic_formula), eq_atom a a = true.
Proof.
intros a. destruct a as [t1 t2].
unfold eq_atom.
rewrite eq_term_refl.
apply eq_term_refl.
Qed.

Lemma eq_f_refl : forall (a : formula), eq_f a a = true.
Proof.
intros a. induction a as [a | a IH | a1 IH1 a2 IH2 | n a IH].
- unfold eq_f. apply eq_atom_refl.
- simpl. apply IH.
- simpl. rewrite IH1. apply IH2.
- simpl. rewrite eq_nat_refl. apply IH.
Qed.


(* Given some term t, returns t+1 if the formula is closed, 0 otherwise *)
(* *)
Fixpoint eval (t : term) : nat :=
match t with
| zero => 1
| succ t1 =>
    (match eval t1 with
    | 0 => 0
    | S n => S (S n)
    end)
| plus t1 t2 =>
    (match eval t1, eval t2 with
    | S n, S m => S (n + m)
    | _, _ => 0
    end)
| times t1 t2 =>
    (match eval t1, eval t2 with
    | S n, S m => S (n * m)
    | _, _ => 0
    end)
| var n => 0
end.

Fixpoint represent (n : nat) : term :=
match n with
| O => zero
| S n' => succ (represent n')
end.


(* Given some atomic formula a, returns whether the statement is correct,
incorrect, or undefined (i.e. not closed) *)
Inductive ternary : Type :=
| correct : ternary
| incorrect : ternary
| undefined : ternary.

Definition correctness (a : atomic_formula) : ternary :=
match a with
| equ t1 t2 =>
    (match eval t1, eval t2 with
    | S n, S m =>
        (match eq_nat (eval t1) (eval t2) with
        | true => correct
        | false => incorrect
        end)
    | _, _ => undefined
    end)
end.

Definition correct_a (a : atomic_formula) : bool :=
match correctness a with
| correct => true
| _ => false
end.

Definition incorrect_a (a : atomic_formula) : bool :=
match correctness a with
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
  (match closed B with
   | true => true
   | false =>
    (match free_list B with
    | [] => false
    | m :: l => eq_nat m n && eq_list l []
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
  apply nat_eq_decid in H1. apply eq_list_decid in H3. rewrite H1, H3. auto.
Qed.

Lemma closed_univ : forall (B : formula) (m : nat),
  closed (univ m B) = true -> closed B = true \/ free_list B = [m].
Proof.
intros. destruct (closed B) eqn:HB.
- left. auto.
- right. apply (closed_univ' _ _ H HB).
Qed.


(* A formula is closed iff its free_list is empty *)
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
    * rewrite H0. rewrite eq_nat_refl. auto.
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
  + rewrite H0. simpl. rewrite eq_nat_refl. auto.
Qed.


(* Closed atomic formulas are either correct or incorrect *)
(* *)
Lemma eval_succ_lemma : forall (s : term), eval (succ s) > 0 -> eval s > 0.
Proof.
intros.
simpl in H.
case_eq (eval s); intros.
- rewrite H0 in H. inversion H.
- lia.
Qed.

Lemma eval_plus_lemma : forall (t1 t2 : term),
  eval (plus t1 t2) > 0 -> eval t1 > 0 /\ eval t2 > 0.
Proof.
intros.
simpl in H.
case_eq (eval t1); case_eq (eval t2); intros;
rewrite H0 in H; rewrite H1 in H; inversion H; split; lia.
Qed.

Lemma eval_times_lemma : forall (t1 t2 : term),
  eval (times t1 t2) > 0 -> eval t1 > 0 /\ eval t2 > 0.
Proof.
intros.
simpl in H.
case_eq (eval t1); case_eq (eval t2); intros;
rewrite H0 in H; rewrite H1 in H; inversion H; split; lia.
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
  + lia.
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
  sum (correctness (equ s t) = correct) (correctness (equ s t) = incorrect).
Proof.
intros s t Hs Ht. apply closed_eval in Hs. apply closed_eval in Ht. simpl.
destruct (eval s); destruct (eval t).
- assert (False). { inversion Hs. } inversion H.
- assert (False). { inversion Hs. } inversion H.
- assert (False). { inversion Ht. } inversion H.
- destruct (eq_nat (S n) (S n0)); auto.
Qed.

Lemma correctness_decid_aux2 : forall (s t : term),
  closed_t s = true ->
  closed_t t = true ->
  sum (correct_a (equ s t) = true) (incorrect_a (equ s t) = true).
Proof.
intros s t Hs Ht.
destruct (correctness_decid_aux1 _ _ Hs Ht) as [H | H].
- left. unfold correct_a. rewrite H. auto.
- right. unfold incorrect_a. rewrite H. auto.
Qed.

Lemma correctness_decid : forall (a : atomic_formula),
  closed_a a = true ->
  sum (correct_a a = true) (incorrect_a a = true).
Proof.
intros. destruct a as [t1 t2].
apply correctness_decid_aux2; unfold closed_a in H.
- destruct (closed_t t1); auto.
- destruct (closed_t t2); auto. destruct (closed_t t1); auto.
Qed.


(* Defining substitution of a term t for all free occurrences of a
   variable x_n in a formula f *)
(* *)
Fixpoint substitution_t (T : term) (n : nat) (t : term) : term :=
match T with
| zero => T
| succ T1 => succ (substitution_t T1 n t)
| plus T1 T2 => plus (substitution_t T1 n t) (substitution_t T2 n t)
| times T1 T2 => times (substitution_t T1 n t) (substitution_t T2 n t)
| var m =>
    (match eq_nat m n with
    | true => t
    | false => T
    end)
end.

Definition substitution_a (a : atomic_formula) (n : nat) (t : term)
  : atomic_formula :=
match a with
  equ t1 t2 => equ (substitution_t t1 n t) (substitution_t t2 n t)
end.

Fixpoint substitution (A : formula) (n : nat) (t : term) : formula :=
match A with
| atom a => atom (substitution_a a n t)
| neg B => neg (substitution B n t)
| lor B C => lor (substitution B n t) (substitution C n t)
| univ m B => 
    (match eq_nat m n with
    | true => A
    | false => univ m (substitution B n t)
    end)
end.


(* If a formula has exactly one free variable x_n, and a closed term t is
substituted in place of that variable, the resulting formula is closed *)
(* *)
Lemma subst_remove_t : forall (T t : term) (n : nat),
  closed_t t = true ->
  free_list_t (substitution_t T n t) = remove n (free_list_t T).
Proof.
intros. induction T; auto.
- simpl. rewrite IHT1, IHT2.
  rewrite remove_dups_order. rewrite remove_concat. auto.
- simpl. rewrite IHT1, IHT2.
  rewrite remove_dups_order. rewrite remove_concat. auto.
- simpl. case_eq (eq_nat n0 n); intros; auto.
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
- destruct (eq_nat n0 n) eqn:Hn.
  + rewrite (nat_eq_decid _ _ Hn). rewrite remove_twice. auto.
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
rewrite H0. simpl. rewrite eq_nat_refl. auto.
Qed.

Lemma one_var_free_lemma : forall (A : formula) (n : nat) (t : term),
  closed_t t = true ->
  free_list A = [n] ->
  closed (substitution A n t) = true.
Proof.
intros.
apply free_list_closed.
rewrite (subst_remove _ _ _ H).
rewrite H0. simpl. rewrite eq_nat_refl. auto.
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
- rewrite (nat_eq_decid _ _ H1). auto.
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

Definition f_eq_decid_nice (A : formula) : Prop := forall (B : formula),
  eq_f A B = true -> A = B.

Lemma f_eq_decid' : forall (A : formula), f_eq_decid_nice A.
Proof.
intros. induction A; unfold f_eq_decid_nice; intros; destruct B; inversion H.
- apply atom_beq_eq in H1. rewrite H1. auto.
- unfold f_eq_decid_nice in IHA. rewrite (IHA B H1). auto.
- destruct (and_bool_prop _ _ H1).
  unfold term_beq_eq_nice in IHA1. rewrite (IHA1 B1 H0).
  unfold term_beq_eq_nice in IHA2. rewrite (IHA2 B2 H2). auto.
- destruct (and_bool_prop _ _ H1).
  unfold f_eq_decid_nice in IHA. rewrite (IHA B H2), (nat_eq_decid _ _ H0). auto.
Qed.

Lemma f_eq_decid : forall (A B : formula), eq_f A B = true -> A = B.
Proof. intros. apply f_eq_decid'. apply H. Qed.














































































































(*
###############################################################################
Section 4: Axioms and Rules of inference of PA_omega
###############################################################################
*)

(* Axioms of PA_omega *)
(* *)
Definition PA_omega_axiom (A : formula) : bool :=
match A with
| atom a => correct_a a
| neg (atom a) => incorrect_a a
| _ => false
end.


(* A theorem of PA_omega is either an axiom, or the result of applying a rule
    of inference to another theorem *)
(* *)
Inductive PA_omega_theorem : formula -> nat -> ord -> Type :=
| deg_incr : forall (A : formula) (d d' : nat) (alpha : ord),
    PA_omega_theorem A d alpha ->
    d' > d ->
    PA_omega_theorem A d' alpha

| ord_incr : forall (A : formula) (d : nat) (alpha beta : ord),
    PA_omega_theorem A d alpha ->
    ord_lt alpha beta -> nf beta ->
    PA_omega_theorem A d beta


| axiom : forall (A : formula),
    PA_omega_axiom A = true ->
    PA_omega_theorem A 0 Zero


| exchange1 : forall (A B : formula) (d : nat) (alpha : ord),
    PA_omega_theorem (lor A B) d alpha ->
    PA_omega_theorem (lor B A) d alpha

| exchange2 : forall (C A B : formula) (d : nat) (alpha : ord),
    PA_omega_theorem (lor (lor C A) B) d alpha ->
    PA_omega_theorem (lor (lor C B) A) d alpha

| exchange3 : forall (A B D : formula) (d : nat) (alpha : ord),
    PA_omega_theorem (lor (lor A B) D) d alpha ->
    PA_omega_theorem (lor (lor B A) D) d alpha

| exchange4 : forall (C A B D : formula) (d : nat) (alpha : ord),
    PA_omega_theorem (lor (lor (lor C A) B) D) d alpha ->
    PA_omega_theorem (lor (lor (lor C B) A) D) d alpha

| contraction1 : forall (A : formula) (d : nat) (alpha : ord),
    PA_omega_theorem (lor A A) d alpha ->
    PA_omega_theorem A d alpha

| contraction2 : forall (A D : formula) (d : nat) (alpha : ord),
    PA_omega_theorem (lor (lor A A) D) d alpha ->
    PA_omega_theorem (lor A D) d alpha



| weakening : forall (A D : formula) (d : nat) (alpha : ord),
    closed A = true ->
    PA_omega_theorem D d alpha ->
    PA_omega_theorem (lor A D) d (ord_succ alpha)

| demorgan1 : forall (A B : formula) (d1 d2 : nat)
                     (alpha1 alpha2 : ord),
    PA_omega_theorem (neg A) d1 alpha1 ->
    PA_omega_theorem (neg B) d2 alpha2 ->
    PA_omega_theorem (neg (lor A B)) (max d1 d2) (ord_succ (ord_max alpha1 alpha2))

| demorgan2 : forall (A B D : formula) (d1 d2 : nat) (alpha1 alpha2 : ord),
    PA_omega_theorem (lor (neg A) D) d1 alpha1 ->
    PA_omega_theorem (lor (neg B) D) d2 alpha2 ->
    PA_omega_theorem (lor (neg (lor A B)) D)
                     (max d1 d2) (ord_succ (ord_max alpha1 alpha2))

| negation1 : forall (A : formula) (d : nat) (alpha : ord),
    PA_omega_theorem A d alpha ->
    PA_omega_theorem (neg (neg A)) d (ord_succ alpha)

| negation2 : forall (A D : formula) (d : nat) (alpha : ord),
    PA_omega_theorem (lor A D) d alpha ->
    PA_omega_theorem (lor (neg (neg A)) D) d (ord_succ alpha)

| quantification1 : forall (A : formula) (n : nat) (t : term)
                           (d : nat) (alpha : ord),
    closed_t t = true ->
    PA_omega_theorem (neg (substitution A n t)) d alpha ->
    PA_omega_theorem (neg (univ n A)) d (ord_succ alpha)

| quantification2 : forall (A D : formula) (n : nat) (t : term)
                           (d : nat) (alpha : ord),
    closed_t t = true ->
    PA_omega_theorem (lor (neg (substitution A n t)) D) d alpha ->
    PA_omega_theorem (lor (neg (univ n A)) D) d (ord_succ alpha)

| w_rule1 : forall (A : formula) (n : nat) (d : nat) (alpha : ord)
  (g : forall (m : nat),
      PA_omega_theorem (substitution A n (represent m)) d alpha),
  PA_omega_theorem (univ n A) d (cons alpha 0 Zero)

| w_rule2 : forall (A D : formula) (n : nat) (d : nat) (alpha : ord)
  (g : forall (m : nat),
    PA_omega_theorem (lor (substitution A n (represent m)) D) d alpha),
  PA_omega_theorem (lor (univ n A) D) d (cons alpha 0 Zero)

| cut1 : forall (C A : formula) (d1 d2 : nat) (alpha1 alpha2 : ord),
    PA_omega_theorem (lor C A) d1 alpha1 ->
    PA_omega_theorem (neg A) d2 alpha2 ->
    PA_omega_theorem C
                     (max (max d1 d2) (num_conn (neg A)))
                     (ord_succ (ord_max alpha1 alpha2))

| cut2 : forall (A D : formula) (d1 d2 : nat) (alpha1 alpha2 : ord),
    PA_omega_theorem A d1 alpha1 ->
    PA_omega_theorem (lor (neg A) D) d2 alpha2 ->
    PA_omega_theorem D
                     (max (max d1 d2) (num_conn (neg A)))
                     (ord_succ (ord_max alpha1 alpha2))

| cut3 : forall (C A D : formula) (d1 d2 : nat) (alpha1 alpha2 : ord),
    PA_omega_theorem (lor C A) d1 alpha1 ->
    PA_omega_theorem (lor (neg A) D) d2 alpha2 ->
    PA_omega_theorem (lor C D)
                     (max (max d1 d2) (num_conn (neg A)))
                     (ord_succ (ord_max alpha1 alpha2)).



(* Extended example of using the w_rule to show "forall x (x = x)"
   is a Cut-free theorem of PA_omega *)
(* *)
Lemma equ_refl_aux1 : forall (t : term),
  eval t > 0 -> correctness (equ t t) = correct.
Proof.
intros.
case_eq (eval t); intros.
- rewrite H0 in H. inversion H.
- unfold correctness. rewrite H0. rewrite eq_nat_refl. auto.
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
  + lia.
Qed.

Lemma equ_refl : forall (m : nat),
  PA_omega_theorem (atom (equ (represent m) (represent m))) 0 Zero.
Proof.
intros.
apply axiom.
simpl.
apply equ_refl_aux2.
apply eval_represent.
Qed.

Lemma w_rule_exmp : forall (n : nat),
  PA_omega_theorem (univ n (atom (equ (var n) (var n)))) 0 (cons Zero 0 Zero).
Proof.
intros. 
apply w_rule1. simpl. rewrite eq_nat_refl. apply equ_refl.
Qed.

(* Show that PA_omega proves the associativity laws *)
(* *)
Lemma associativity1 : forall (C A B : formula) (d : nat) (alpha : ord),
  PA_omega_theorem (lor (lor C A) B) d alpha ->
  PA_omega_theorem (lor C (lor A B)) d alpha.
Proof.
intros.
apply exchange3 in H.
apply exchange2 in H.
apply exchange1 in H.
apply H.
Qed.

Lemma associativity2 : forall (C A B : formula) (d : nat) (alpha : ord),
  PA_omega_theorem (lor C (lor A B)) d alpha ->
  PA_omega_theorem (lor (lor C A) B) d alpha.
Proof.
intros.
apply exchange1 in H.
apply exchange2 in H.
apply exchange3 in H.
apply H.
Qed.


(* Other miscellaneous lemmas we will need in the next section. *)
(* *)
Lemma deg_monot : forall (A : formula) (d d' : nat) (alpha : ord),
  d' >= d -> PA_omega_theorem A d alpha -> PA_omega_theorem A d' alpha.
Proof.
intros. apply leq_type in H. destruct H.
- apply (deg_incr A d d'); auto.
- rewrite e. auto.
Qed.

Lemma ord_succ_nf : forall alpha, nf alpha -> nf (ord_succ alpha).
Proof.
intros. rewrite nf_add_one; auto. apply nf_add; auto.
assert (cons Zero 0 Zero = nat_ord 1); auto.
rewrite H0. apply nf_nat.
Qed.

Lemma ord_max_nf : forall alpha beta, nf alpha -> nf beta -> nf (ord_max alpha beta).
Proof.
intros.
case (ord_ltb alpha beta) eqn:H1.
rewrite (ord_max_lem1 _ _ H1). auto.
rewrite (ord_max_lem2 _ _ H1). auto.
Qed.

Lemma ord_nf : forall (A : formula) (d : nat) (alpha : ord),
  PA_omega_theorem A d alpha -> nf alpha.
Proof.
intros. induction H; try apply ord_succ_nf; try apply ord_max_nf; auto.
- apply zero_nf.
- apply single_nf. apply (H 0).
- apply single_nf. apply (H 0).
Qed.

Lemma ord_monot : forall (A : formula) (d : nat) (alpha beta : ord),
  (((ord_lt alpha beta) /\ (nf beta)) + (alpha = beta)) ->
  PA_omega_theorem A d alpha ->
  PA_omega_theorem A d beta.
Proof.
intros. destruct H.
- destruct a. apply (ord_incr A d alpha); auto.
- rewrite <- e. auto.
Qed.

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
split; lia.
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
split; lia.
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
- case_eq (eq_nat n0 n); intros; simpl; rewrite H1.
  + apply H.
  + simpl in H0. rewrite H1 in H0. inversion H0.
Qed.

Lemma incorrect_subst_closed :
  forall (a : atomic_formula) (n : nat) (s t : term),
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
- simpl in H. simpl. case_eq (eq_nat n0 n); intros.
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
- simpl. case_eq (eq_nat n0 n); intros; auto.
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

Lemma closed_sub_theorem :
  forall (A : formula) (n d : nat) (t : term) (alpha : ord),
  closed A = true ->
  PA_omega_theorem A d alpha ->
  PA_omega_theorem (substitution A n t) d alpha.
Proof. intros. rewrite closed_subst_eq. apply H0. apply H. Qed.

Lemma closed_univ_sub : forall (B : formula) (n : nat),
  closed (univ n B) = true ->
  (forall (t : term), closed_t t = true -> closed (substitution B n t) = true).
Proof.
intros.
destruct (closed_univ B n H).
- rewrite (closed_subst_eq _ _ _ H1). apply H1.
- apply free_list_closed. rewrite (subst_remove B n t H0).
  rewrite H1. simpl. rewrite eq_nat_refl. auto.
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
    ((free_list B = [n]) + (closed B = true)) *
    ((free_list C = [n]) + (closed C = true)).
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
  eq_nat m n = false ->
  substitution_t (substitution_t T n s) m t =
  substitution_t (substitution_t T m t) n s.
Proof.
intros T m n s t Hs Ht Hmn. induction T; auto; simpl.
- rewrite IHT. auto.
- rewrite IHT1, IHT2. auto.
- rewrite IHT1, IHT2. auto.
- destruct (eq_nat n0 n) eqn:Hn.
  + rewrite <- (nat_eq_decid _ _ Hn) in Hmn. rewrite (eq_nat_symm' _ _ Hmn).
    simpl. rewrite Hn. apply closed_subst_eq_t, Hs.
  + destruct (eq_nat n0 m) eqn:Hm; simpl; rewrite Hm.
    * symmetry. apply closed_subst_eq_t, Ht.
    * rewrite Hn. auto.
Qed.

Lemma substitution_order_a :
  forall (a : atomic_formula) (m n : nat) (s t : term),
  closed_t s = true ->
  closed_t t = true ->
  eq_nat m n = false ->
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
  eq_nat m n = false ->
  substitution (substitution B n s) m t =
  substitution (substitution B m t) n s.
Proof.
intros B m n s t Hs Ht Hmn. induction B; simpl.
- rewrite (substitution_order_a _ _ _ _ _ Hs Ht Hmn). auto.
- rewrite IHB. auto.
- rewrite IHB1, IHB2. auto.
- destruct (eq_nat n0 n) eqn:Hn.
  + apply nat_eq_decid in Hn. rewrite Hn.
    rewrite (eq_nat_symm' _ _ Hmn). simpl.
    rewrite (eq_nat_symm' _ _ Hmn). rewrite eq_nat_refl. auto.
  + destruct (eq_nat n0 m) eqn:Hm; simpl; rewrite Hm, Hn; auto.
    rewrite IHB. auto.
Qed.

Lemma univ_free_var : forall (B : formula) (m n : nat),
  free_list (univ m B) = [n] -> eq_nat m n = false.
Proof.
intros. simpl in H.
destruct (eq_nat m n) eqn:Hm; auto.
apply nat_eq_decid in Hm. rewrite Hm in H.
pose proof (remove_twice (free_list B) n).
rewrite H in H0. simpl in H0. rewrite eq_nat_refl in H0. inversion H0.
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

Lemma num_conn_lor : forall (B C : formula) (n : nat),
  num_conn (lor B C) = S n -> num_conn B <= n /\ num_conn C <= n.
Proof. intros. apply addends_leq. inversion H. auto. Qed.

Lemma LEM_univ : forall (B : formula) (n m d : nat) (alpha : ord),
  closed (substitution B n (represent m)) = true ->
  PA_omega_theorem
    (lor (neg (substitution B n (represent m)))
         (substitution B n (represent m)))
    d alpha ->
  PA_omega_theorem
    (lor (substitution B n (represent m)) (neg (univ n B)))
    d (ord_succ alpha).
Proof.
intros. apply exchange1.
apply (quantification2 _ _ _ (represent m)); auto.
apply eval_closed. apply eval_represent.
Qed.

Lemma num_conn_sub : forall (B : formula) (m : nat) (t : term),
  num_conn (substitution B m t) = num_conn B.
Proof.
intros.
induction B; auto; simpl.
- rewrite IHB. auto.
- rewrite IHB1, IHB2. auto.
- destruct (eq_nat n m).
  + auto.
  + simpl. rewrite IHB. auto.
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
  closed_a a = true ->
  PA_omega_theorem (lor (neg (atom a)) (atom a)) 0 (ord_succ Zero).
Proof.
intros.
destruct (correctness_decid a H) as [H0 | H0].
- apply weakening; auto. apply axiom. apply H0.
- apply exchange1. apply weakening; auto. apply axiom. apply H0.
Qed.

(*
The logical structure of the inductive argument here is rather subtle
when fully formalized; P1,P2,P3 are meant to break this up. We ultimately want
to prove (forall A, P1 A), but our main task will be to show (forall n, P3 n)
by strong induction on n, the number of connectives.
*)
(* *)

(*Definition P1 (A : formula) : Type :=
  closed A = true -> {alpha : ord & PA_omega_theorem (lor (neg A) A) 0 alpha & ord_lt alpha (ord_succ (ord_2_exp (nat_ord (num_conn A))))}.
*)

Definition P1 (A : formula) : Type :=
  closed A = true -> PA_omega_theorem (lor (neg A) A) 0 (ord_succ (w_tower ((num_conn A) + (num_conn A)))).

Definition P2 (A : formula) (n : nat) : Type :=
  num_conn A = n -> P1 A.

Definition P3 (n : nat) : Type :=
  forall (A : formula), P2 A n.

Lemma P3_0 : P3 0.
Proof.
unfold P3, P2. intros.
destruct A as [a | | | ].
- unfold P1. intros. apply (ord_incr _ _ (cons Zero 0 Zero)). 
  + apply LEM_atomic. auto.
  + simpl. apply ord_ltb_lt. auto.
  + apply ord_succ_nf. simpl. apply single_nf. apply Zero_nf. 
- inversion H.
- inversion H.
- inversion H.
Qed.

(* Prove strong induction holds for P3, adapted from
pldev.blogspot.com/2012/02/proving-strong-induction-principle-for.html *)
Lemma P3_strongind_aux :
  P3 0 ->
  (forall n,
    ((forall m, m <= n -> P3 m) -> P3 (S n))) ->
  (forall n m, m <= n -> P3 m).
Proof.
induction n as [| n' IHn' ].
- intros m H1. assert (m = 0). { inversion H1. auto. } rewrite H. apply X.
- intros. assert ((m = S n') + (m <= n')). { apply leq_prop_sum. lia. }
  destruct H0 as [H1 | H1].
  + rewrite H1. apply X0. apply IHn'.
  + apply IHn'. apply H1.
Qed.

Lemma P3_strongind :
  P3 0 ->
  (forall n,
    ((forall m, m <= n -> P3 m) -> P3 (S n))) ->
  (forall n, P3 n).
Proof. intros. apply (P3_strongind_aux X X0 n n). auto. Qed.

Lemma ord_lt_succ : forall alpha beta, ord_lt alpha beta -> ord_lt (ord_succ alpha) (ord_succ beta).
Proof.
intros alpha.
induction alpha.
- intros. induction beta. inversion H. apply ord_ltb_lt. destruct beta1; auto.
- intros. induction beta; inversion H.
  + destruct H0,H2,H3,H4,H5,H6. simpl. destruct a.
    * destruct a'.
      { inversion H1. }
      { apply ord_ltb_lt. auto. }
    * destruct a'.
      { inversion H1. }
      { apply ord_ltb_lt. unfold ord_ltb. fold ord_ltb. inversion H1.
        { apply ord_lt_ltb in H2. rewrite H2. auto. }
        { destruct H0,H3,H4,H5,H6,H7. repeat rewrite ord_ltb_irrefl. repeat rewrite ord_eqb_refl. apply lt_nat_decid_conv in H2. rewrite H2. auto. }
        { destruct H0,H3,H4,H5,H6,H7. repeat rewrite ord_ltb_irrefl. repeat rewrite ord_eqb_refl. repeat rewrite lt_nat_irrefl. apply ord_lt_ltb in H2. rewrite H2. auto. }
       } 
  + destruct H0,H2,H3,H4,H5,H6. simpl. destruct a.
    * apply ord_ltb_lt. simpl. assert (lt_nat (S n1) (S n') = true). apply lt_nat_decid_conv. lia. rewrite H0. auto.
    * apply ord_ltb_lt. simpl. repeat rewrite ord_ltb_irrefl. repeat rewrite ord_eqb_refl. repeat rewrite lt_nat_irrefl. repeat rewrite eq_nat_refl. rewrite lt_nat_decid_conv. auto. apply H1.
  + destruct H0,H2,H3,H4,H5,H6. simpl. destruct a.
    * apply ord_ltb_lt. simpl. rewrite lt_nat_irrefl. apply ord_lt_ltb. apply H1.
    * apply ord_ltb_lt. simpl. repeat rewrite ord_ltb_irrefl. repeat rewrite ord_eqb_refl. repeat rewrite lt_nat_irrefl. repeat rewrite eq_nat_refl. apply ord_lt_ltb. apply (IHalpha2 _ H1).
Qed.

Lemma ord_nf_succ : forall alpha, nf (ord_succ alpha) -> nf alpha.
Proof.
intros.
induction alpha.
- apply zero_nf.
- unfold ord_succ in H. fold ord_succ in H. destruct alpha1.
  + apply (nf_scalar _ _ _ _ H).
  + pose proof (IHalpha2 (nf_hered_third _ _ _ H)).
    pose proof (nf_hered_first _ _ _ H).
    destruct alpha2.
    * apply single_nf. apply H1.
    * apply cons_nf. 
      { inversion H. destruct alpha2_1; inversion H5. destruct alpha2_1. apply zero_lt. inversion H4. destruct H9. apply H5. }
      apply H1. apply H0.
Qed.

Lemma w_tower_succ : forall n, ord_lt (ord_succ (w_tower n)) (w_tower (S n)).
Proof.
intros.
destruct n.
- simpl. apply ord_ltb_lt. auto.
- simpl. destruct (w_tower n).
  + apply ord_ltb_lt. auto.
  + apply ord_ltb_lt. unfold ord_ltb. fold ord_ltb. pose proof (omega_exp_incr' o1 o2 n0). apply ord_lt_ltb in H. rewrite H. auto.
Qed.

Lemma w_tower_succ2 : forall n, ord_lt (ord_succ (ord_succ (w_tower n))) (w_tower (S n)).
Proof.
intros.
destruct n.
- simpl. apply ord_ltb_lt. auto.
- simpl. destruct (w_tower n).
  + apply ord_ltb_lt. auto.
  + apply ord_ltb_lt. unfold ord_succ. unfold ord_ltb. fold ord_ltb. pose proof (omega_exp_incr' o1 o2 n0). apply ord_lt_ltb in H. rewrite H. auto.
Qed.

Lemma w_tower_lt : forall n m,  m < n -> ord_lt (w_tower m) (w_tower n).
Proof.
intros n. induction n.
- intros. inversion H.
- intros. inversion H.
  + simpl. apply ord_ltb_lt. destruct (w_tower n). auto. unfold ord_ltb. fold ord_ltb. rewrite (ord_lt_ltb _ _ (omega_exp_incr' o1 o2 n0)). auto.
  + apply ord_ltb_lt. apply (ord_ltb_trans _ _ _ (ord_lt_ltb _ _ (IHn _ H1))). simpl. apply ord_lt_ltb. apply omega_exp_incr.
Qed.

Lemma w_tower_max : forall n m, ord_lt (ord_max (ord_succ (ord_succ (w_tower m))) (ord_succ (ord_succ (w_tower n)))) (w_tower (S (m+n))).
Proof.
intros. case (ord_ltb (ord_succ (ord_succ (w_tower m))) (ord_succ (ord_succ (w_tower n)))) eqn:H.
- rewrite (ord_max_lem1 _ _ H). destruct m.
  + apply w_tower_succ2.
  + apply ord_ltb_lt. apply (ord_ltb_trans _ _ _ (ord_lt_ltb _ _ (w_tower_succ2 _))).
    apply ord_lt_ltb. apply w_tower_lt. lia.
- rewrite (ord_max_lem2 _ _ H). destruct n.
  + rewrite <- plus_n_O. apply w_tower_succ2.
  + apply ord_ltb_lt. apply (ord_ltb_trans _ _ _ (ord_lt_ltb _ _ (w_tower_succ2 _))).
    apply ord_lt_ltb. apply w_tower_lt. lia.
Qed.

Lemma w_tower_nf : forall n, nf (w_tower n).
Proof.
intros. induction n.
- simpl. apply single_nf. apply Zero_nf.
- simpl. apply single_nf. apply IHn.
Qed.

(* The (strong) inductive step for LEM *)
(* *)
Lemma P3_inductive : forall n, (forall m, m <= n -> P3 m) -> P3 (S n).
Proof.
unfold P3,P2,P1. intros.
destruct A as [a | B | B C | m B].
- inversion H0.
- inversion H0. pose proof (H n (leq_refl n) B H3 H1).
  apply (ord_incr _ _ (ord_succ (ord_succ (w_tower ((num_conn B) + (num_conn B)))))).
  + apply negation2. apply exchange1. apply H2.
  + apply ord_lt_succ. unfold num_conn. fold num_conn. destruct (num_conn B).
    * simpl. apply ord_ltb_lt. auto.
    * apply ord_ltb_lt. apply (ord_ltb_trans _ _ _ (ord_lt_ltb _ _ (w_tower_succ _))). apply ord_lt_ltb. apply w_tower_lt. lia.
  + apply ord_succ_nf. apply w_tower_nf.

- destruct (closed_lor _ _ H1) as [HB HC].
  destruct (num_conn_lor _ _ _ H0) as [HB' HC'].
  pose proof (H (num_conn B) HB' B (eq_refl (num_conn B)) HB).
  apply (weakening C _ _ _ HC) in H2. apply exchange1 in H2. apply associativity1 in H2.
  pose proof (H (num_conn C) HC' C (eq_refl (num_conn C)) HC).
  apply (weakening B _ _ _ HB) in H3. apply exchange1 in H3. apply exchange2 in H3. apply associativity1 in H3.
  pose proof (demorgan2 B C (lor B C) 0 0 _ _ H2 H3).
  apply (ord_incr _ _ (ord_succ (ord_max (ord_succ (ord_succ (w_tower ((num_conn B)+ (num_conn B))))) (ord_succ (ord_succ (w_tower ((num_conn C) + (num_conn C)))))))).
  + apply H4.
  + unfold num_conn. fold num_conn. apply ord_lt_succ. apply ord_ltb_lt. apply (ord_ltb_trans _ _ _ (ord_lt_ltb _ _ (w_tower_max _ _))). apply ord_lt_ltb. apply w_tower_lt. lia.
  + apply ord_succ_nf. apply w_tower_nf.

- inversion H0. apply exchange1.
  apply (ord_incr _ _ (w_tower ((num_conn (univ m B))+(num_conn (univ m B))))).
  + unfold num_conn. fold num_conn. rewrite <- plus_n_Sm. apply w_rule2. fold w_tower. intros k.
    destruct H3. pose proof (H _ (leq_refl _) _ (num_conn_sub _ _ _) (closed_univ_sub _ _ H1 _ (eval_closed _ (eval_represent k)))).
    rewrite num_conn_sub in H2. apply (ord_incr _ _ (ord_succ (ord_succ (w_tower ((num_conn B) + (num_conn B)))))).
    * apply exchange1. apply (quantification2 _ _ _ (represent k)). apply repr_closed. apply H2.
    * apply w_tower_succ2.
    * apply w_tower_nf.
  + apply ord_succ_monot.
  + apply ord_succ_nf. apply w_tower_nf.
Qed.

Lemma P3_lemma : forall n, P3 n.
Proof. apply P3_strongind. apply P3_0. apply P3_inductive. Qed.

Lemma P2_lemma : forall (n : nat) (A : formula), P2 A n.
Proof. apply P3_lemma. Qed.

Lemma P1_lemma : forall (A : formula), P1 A.
Proof.
intros.
pose proof P2_lemma.
unfold P2 in X.
apply (X (num_conn A) A). auto.
Qed.

Lemma LEM : forall (A : formula),
  closed A = true ->
  PA_omega_theorem (lor (neg A) A) 0 (ord_succ (w_tower ((num_conn A)+(num_conn A)))).
Proof. intros. apply (P1_lemma A H). Qed.


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
- simpl. case (eq_nat n0 n). apply H. auto.
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
- case_eq (eq_nat (S n0) (S n)).
  + apply nat_eq_decid.
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
- rewrite <- H2. rewrite <- H3. rewrite Hst. rewrite eq_nat_refl. auto.
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
                          (atom (substitution_a a n t)))
                      0 (ord_succ Zero).
Proof.
intros a n s t H Ha.
destruct (correctness_decid (substitution_a a n s)) as [H0 | H0].
- apply one_var_free_lemma_a.
  + simpl in H. apply eval_closed. destruct (correct_eval s t H). apply H0.
  + apply Ha.
- pose proof (correct_closed _ H0) as HC.
  pose proof (LEM_term_atomic' s t a n H). apply H1 in H0.
  apply axiom in H0. unfold substitution in H0.
  apply weakening; auto.
- apply exchange1. apply weakening; auto.
  + simpl. apply (incorrect_subst_closed a n s t); auto.
    apply eval_closed. destruct (correct_eval s t H). apply H2.
  + apply axiom. apply H0.
Qed.


(*
The inductive proof here is quite similar with LEM, and Q1,Q2,Q3
are meant to break this up. *)
(* *)

Definition Q1 (A : formula) : Type := forall (n : nat) (s t : term),
  correct_a (equ s t) = true ->
  free_list A = [n] ->
  PA_omega_theorem (lor (neg (substitution A n s)) (substitution A n t))
                   0 (ord_succ (w_tower ((num_conn A)+(num_conn A)))).

Definition Q2 (A : formula) (n : nat) : Type := num_conn A = n -> Q1 A.

Definition Q3 (m : nat) : Type := forall (A : formula), Q2 A m.

Lemma Q3_strongind_aux :
  Q3 0 ->
  (forall n,
    ((forall m, m <= n -> Q3 m) -> Q3 (S n))) ->
  (forall n m, m <= n -> Q3 m).
Proof.
induction n as [| n' IHn' ].
- intros m H1. assert (m = 0). { inversion H1. auto. } rewrite H. apply X.
- intros. assert ((m = S n') + (m <= n')). { apply leq_prop_sum. lia. }
  destruct H0 as [H1 | H1].
  + rewrite H1. apply X0. apply IHn'.
  + apply IHn'. apply H1.
Qed.

Lemma Q3_strongind :
  Q3 0 ->
  (forall n,
    ((forall m, m <= n -> Q3 m) -> Q3 (S n))) ->
  (forall n, Q3 n).
Proof. intros. apply (Q3_strongind_aux X X0 n n). auto. Qed.

Lemma Q3_0 : Q3 0.
Proof.
unfold Q3, Q2. intros.
destruct A as [a | | | ].
- unfold Q1. intros. apply (ord_incr _ _ (ord_succ Zero)). apply LEM_term_atomic; auto.
  apply ord_lt_succ. apply zero_lt. apply ord_succ_nf. apply w_tower_nf.
- inversion H.
- inversion H.
- inversion H.
Qed.


Lemma Q3_inductive : forall n, (forall m, m <= n -> Q3 m) -> Q3 (S n).
Proof.
unfold Q3,Q2,Q1. intros.
destruct A as [| B | B C | m B].
- inversion H0.
- inversion H0. apply negation2. fold substitution. apply exchange1. unfold num_conn. fold num_conn.
  apply (ord_incr _ _ (ord_succ (w_tower ((num_conn B)+(num_conn B))))).
  apply (H n (leq_refl n) B H4 n0 t s); auto. apply equ_symm,H1.
  apply ord_ltb_lt. apply (ord_ltb_trans _ _ _ (ord_lt_ltb _ _ (w_tower_succ _))). apply ord_lt_ltb. apply w_tower_lt. lia.
  apply single_nf. apply w_tower_nf.
- destruct (free_list_lor B C n0 H2) as [HB HC].
  destruct (num_conn_lor _ _ _ H0) as [HB' HC'].
  destruct (correct_closed_t _ _ H1) as [Hs Ht].
  apply (ord_incr _ _ (ord_succ (ord_max (ord_succ (ord_succ (w_tower ((num_conn B) + (num_conn B))))) (ord_succ (ord_succ (w_tower ((num_conn C)+(num_conn C)))))))).
  + apply (demorgan2 _ _ _ 0 0 (ord_succ (ord_succ (w_tower ((num_conn B) + (num_conn B))))) (ord_succ (ord_succ (w_tower ((num_conn C)+(num_conn C)))))).
    * apply associativity1. apply exchange1. apply weakening.
      { destruct HC as [HC | HC].
        { apply (one_var_free_lemma _ _ _ Ht HC). }
        { rewrite closed_subst_eq; apply HC. }
        }
      { destruct HB as [HB | HB].
        { apply (H (num_conn B) HB' B (eq_refl (num_conn B)) n0 s t H1 HB). }
        { rewrite closed_subst_eq, closed_subst_eq; auto. apply (LEM B HB). }
        }
      * apply associativity1. apply exchange2. apply exchange1. apply weakening.
      { destruct HB as [HB | HB].
        { apply (one_var_free_lemma _ _ _ Ht HB). }
        { rewrite closed_subst_eq; apply HB. }
        }
      { destruct HC as [HC | HC].
        { apply (H (num_conn C) HC' C (eq_refl (num_conn C)) n0 s t H1 HC). }
        { rewrite closed_subst_eq, closed_subst_eq; auto. apply (LEM C HC). }
        }
  + unfold num_conn. fold num_conn. apply ord_lt_succ. apply ord_ltb_lt. apply (ord_ltb_trans _ _ _ (ord_lt_ltb _ _ (w_tower_max _ _))). apply ord_lt_ltb. apply w_tower_lt. lia.
  + apply ord_succ_nf. apply w_tower_nf.
- apply exchange1. inversion H0.
  unfold substitution. fold substitution. pose proof (univ_free_var _ _ _ H2) as Heq. rewrite Heq.
  apply (ord_incr _ _ (w_tower ((num_conn (univ m B))+(num_conn (univ m B))))).
  + apply w_rule2. intros k. apply exchange1. apply (ord_incr _ _ (ord_succ ( ord_succ (w_tower ((num_conn B)+(num_conn B)))))).
    * apply (quantification2 _ _ _ (represent k)).
      { apply repr_closed. }
      { destruct (correct_closed_t _ _ H1) as [Hs Ht].
        rewrite (substitution_order B m n0 s _ Hs (repr_closed k) Heq).
        rewrite (substitution_order B m n0 t _ Ht (repr_closed k) Heq).
        rewrite <- (num_conn_sub B m (represent k)).
        apply (H n (leq_refl n) (substitution B m (represent k))); auto.
        { rewrite num_conn_sub. auto. }
        { apply free_list_univ_sub; auto. apply repr_closed. }
        }
    * unfold num_conn. fold num_conn. fold w_tower. rewrite <- plus_n_Sm. apply w_tower_succ2.
    * apply w_tower_nf.
  + apply ord_succ_monot.
  + apply ord_succ_nf. apply w_tower_nf.
Qed.

Lemma Q3_lemma : forall n, Q3 n.
Proof. apply Q3_strongind. apply Q3_0. apply Q3_inductive. Qed.

Lemma Q2_lemma : forall (n : nat) (A : formula), Q2 A n.
Proof. apply Q3_lemma. Qed.

Lemma Q1_lemma : forall (A : formula), Q1 A.
Proof.
intros.
pose proof (Q2_lemma) as H.
unfold Q2 in H.
apply (H (num_conn A) A). auto.
Qed.

Lemma LEM_term : forall (A : formula) (n : nat) (s t : term),
  correct_a (equ s t) = true ->
  free_list A = [n] ->
  PA_omega_theorem (lor (neg (substitution A n s)) (substitution A n t))
                   0 (ord_succ (w_tower ((num_conn A)+(num_conn A)))).
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
Section 8: Proof trees for PA_omega proofs.
###############################################################################
*)

(* Defining proof trees *)
(* *)
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



| quantification_a : formula -> nat -> term -> nat -> ord -> ptree -> ptree

| quantification_ad :
    formula -> formula -> nat -> term -> nat -> ord -> ptree -> ptree

| w_rule_a : formula -> nat -> nat -> ord -> (nat -> ptree) -> ptree

| w_rule_ad :
    formula -> formula -> nat -> nat -> ord -> (nat -> ptree) -> ptree

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

| exchange_cab C A B d alpha P' => d

| exchange_abd A B D d alpha P' => d

| exchange_cabd C A B D d alpha P' => d

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


| cut_ca C A d1 d2 alpha1 alpha2 P1 P2 => max (max d1 d2) (num_conn (neg A))

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 => max (max d1 d2) (num_conn (neg A))

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2 => max (max d1 d2) (num_conn (neg A))

end.


Fixpoint ptree_ord (P : ptree) : ord :=
match P with
| deg_up d P' => ptree_ord P'

| ord_up alpha P' => alpha

| node A => Zero


| exchange_ab A B d alpha P' => alpha

| exchange_cab C A B d alpha P' => alpha

| exchange_abd A B D d alpha P' => alpha

| exchange_cabd C A B D d alpha P' => alpha

| contraction_a A d alpha P' => alpha

| contraction_ad A D d alpha P' => alpha


| weakening_ad A D d alpha P' => ord_succ alpha

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2 => ord_succ (ord_max alpha1 alpha2)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2 => ord_succ (ord_max alpha1 alpha2)

| negation_a A d alpha P' => ord_succ alpha

| negation_ad A D d alpha P' => ord_succ alpha

| quantification_a A n t d alpha P' => ord_succ alpha

| quantification_ad A D n t d alpha P' => ord_succ alpha

| w_rule_a A n d alpha g => cons alpha 0 Zero

| w_rule_ad A D n d alpha g => cons alpha 0 Zero

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2 => ord_succ (ord_max alpha1 alpha2)

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 => ord_succ (ord_max alpha1 alpha2)

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2 => ord_succ (ord_max alpha1 alpha2)

end.


Fixpoint valid (P : ptree) : Type :=
match P with
| deg_up d P' => (d > ptree_deg P') * (valid P')

| ord_up alpha P' => (ord_lt (ptree_ord P') alpha) * (valid P') * (nf alpha)

| node A => PA_omega_axiom A = true


| exchange_ab A B d alpha P' =>
    (ptree_formula P' = lor A B) * (valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| exchange_cab C A B d alpha P' =>
    (ptree_formula P' = lor (lor C A) B) * (valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| exchange_abd A B D d alpha P' =>
    (ptree_formula P' = lor (lor A B) D) * (valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| exchange_cabd C A B D d alpha P' =>
    (ptree_formula P' = lor (lor (lor C A) B) D) * (valid P') *
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
    (ptree_formula P' = neg (substitution A n t)) *
    (closed_t t = true) * (valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| quantification_ad A D n t d alpha P' =>
    (ptree_formula P' = lor (neg (substitution A n t)) D) *
    (closed_t t = true) * (valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| w_rule_a A n d alpha g => (forall (m : nat),
    (ptree_formula (g m) = substitution A n (represent m)) *
    (valid (g m)) * (d >= ptree_deg (g m)) * (alpha = ptree_ord (g m)))

| w_rule_ad A D n d alpha g => (forall (m : nat),
    (ptree_formula (g m) = lor (substitution A n (represent m)) D) *
    (valid (g m)) * (d >= ptree_deg (g m)) * (alpha = ptree_ord (g m)))


| cut_ca C A d1 d2 alpha1 alpha2 P1 P2 =>
    (ptree_formula P1 = lor C A) * (valid P1) *
    (ptree_formula P2 = neg A) * (valid P2) *
    (d1 = ptree_deg P1) * (d2 = ptree_deg P2) *
    (alpha1 = ptree_ord P1) * (alpha2 = ptree_ord P2)

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 =>
    (ptree_formula P1 = A) * (valid P1) *
    (ptree_formula P2 = lor (neg A) D) * (valid P2) *
    (d1 = ptree_deg P1) * (d2 = ptree_deg P2) *
    (alpha1 = ptree_ord P1) * (alpha2 = ptree_ord P2)

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2 =>
    (ptree_formula P1 = lor C A) * (valid P1) *
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
- exists (quantification_a A n t (ptree_deg P) alpha P). repeat split; auto.
- exists (quantification_ad A D n t (ptree_deg P) alpha P). repeat split; auto.
- unfold P_proves in X.
 exists (w_rule_a A n d alpha (fun m => (projT1 (X m)))).
  repeat split; unfold projT1.
    + destruct (X m) as [P [[[HP1 HP2] HP3] HP4]]; auto.
    + destruct (X m) as [P [[[HP1 HP2] HP3] HP4]]; auto.
    + destruct (X m) as [P [[[HP1 HP2] HP3] HP4]]; auto.
    + destruct (X m) as [P [[[HP1 HP2] HP3] HP4]]; auto.
    + simpl. auto.
- unfold P_proves in X.
  exists (w_rule_ad A D n d alpha (fun m => (projT1 (X m)))).
  repeat split; unfold projT1.
    + destruct (X m) as [P [[[HP1 HP2] HP3] HP4]]; auto.
    + destruct (X m) as [P [[[HP1 HP2] HP3] HP4]]; auto.
    + destruct (X m) as [P [[[HP1 HP2] HP3] HP4]]; auto.
    + destruct (X m) as [P [[[HP1 HP2] HP3] HP4]]; auto.
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
  forall (A : formula) (n d : nat) (alpha : ord) (g : nat -> ptree),
  valid (w_rule_a A n d alpha g) ->
  (forall (m : nat),
    (ptree_formula (g m) = substitution A n (represent m)) *
    valid (g m) * (d >= ptree_deg (g m)) * (alpha = ptree_ord (g m))).
Proof.
intros. destruct (X m) as [[[H1 H2] H3] H4]. fold valid in H2.
repeat split; auto.
Qed.

Lemma valid_w_rule_ad :
  forall (A D : formula) (n d : nat) (alpha : ord) (g : nat -> ptree),
  valid (w_rule_ad A D n d alpha g) ->
  (forall (m : nat),
    (ptree_formula (g m) = lor (substitution A n (represent m)) D) *
    valid (g m) * (d >= ptree_deg (g m)) * (alpha = ptree_ord (g m))).
Proof.
intros. destruct (X m) as [[[H1 H2] H3] H4]. fold valid in H2.
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
- inversion H as [[[[H0 H1] H2] H3] H4]. simpl.
  apply (quantification1 _ _ t); auto.
  rewrite H0 in IHt. rewrite H3,H4. apply IHt. auto.
- inversion H as [[[[H0 H1] H2] H3] H4]. simpl.
  apply (quantification2 _ _ _ t); auto.
  rewrite H0 in IHt. rewrite H3,H4. apply IHt. auto.
- rename p into g. rename f into A. rename n0 into d.
  apply w_rule1. intros m.
  destruct (valid_w_rule_a A n d o g H m) as [[[Hg1 Hg2] Hg3] Hg4].
  rewrite <- Hg1. rewrite Hg4. pose proof (X m Hg2). simpl. apply (deg_monot _ (ptree_deg (g m))); auto.
- rename f into A. rename f0 into D. rename p into g. rename n0 into d.
  apply w_rule2. intros m.
  destruct (valid_w_rule_ad A D n d o g H m) as [[[Hg1 Hg2] Hg3] Hg4].
  rewrite <- Hg1. rewrite Hg4. pose proof (X m Hg2). simpl. apply (deg_monot _ (ptree_deg (g m))); auto.
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
- destruct (subst_one_var_free A n (represent 0) (repr_closed 0) (H 0)); simpl.
  + case_eq (closed A); intros; auto. rewrite H0. rewrite eq_nat_refl. auto.
  + apply free_list_closed in H0. rewrite H0. auto.
- pose proof (H 0). simpl in H0. destruct (and_bool_prop _ _ H0).
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


















































(*
###############################################################################
Section 9: Invertibility lemmas: We show that double negation, DeMorgan,
and the w_rule are invertible, e.g. if PA_omega proves ~~A \/ D, then it also
proves A \/ D. Essentially we need to substitute A for ~~A in the proof tree
~~A \/ D, though we need to introduce some machinery to handle these
substitutions properly.
###############################################################################
*)


(* Defining substitution indicators. When we later define formula substitution,
we will want to take some formula A, and replace any instances of the
subformula E with the formula F. However, we will only want to do this at
certain places in A. Substitution indicators will control this.
For instance, if A is "B \/ (C \/ D)" we might be given a substitution
indicator S that looks like "0 (1 0)" which indicates that we want to
substitute C (if C is E) but leave B,D alone even if they are E. *)
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


(* Replace formula E with formula F at certain places in a formula A *)
(* *)
Fixpoint subst_ind_fit (A : formula) (S : subst_ind) : bool :=
match A, S with
| lor B C, lor_ind S_B S_C =>
    subst_ind_fit B S_B && subst_ind_fit C S_C
| _, lor_ind _ _ => false
| lor _ _, _ => false
| _, _ => true
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
  (match eq_f A E, S with
  | true, (1) => F
  | _, _ => A
  end)
end.

Fixpoint formula_sub_ind (A E F : formula) (S : subst_ind) : formula :=
match subst_ind_fit A S with
| false => A
| true => formula_sub_ind_fit A E F S
end.

(* Some miscellaneous lemmas about formula substitution we will need *)
(* *)
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
- simpl. destruct B; auto. destruct (eq_nat n n0 && eq_f A B); auto.
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
- simpl. destruct C; auto. destruct (eq_nat n n0 && eq_f A C); auto.
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

Lemma non_target_term_sub : forall (A : formula) (n : nat) (t : term),
  non_target A = non_target (substitution A n t).
Proof.
intros. induction A; auto; simpl.
- rewrite IHA1, IHA2. auto.
- destruct (eq_nat n0 n); auto.
Qed.

Lemma formula_sub_ind_closed : forall (A B C : formula),
  closed A = true -> (closed B = true -> closed C = true) ->
  forall (S : subst_ind), closed (formula_sub_ind A B C S) = true.
Proof.
intros A B C. induction A; intros; unfold formula_sub_ind.
- destruct (subst_ind_fit (atom a) S); try apply H.
  simpl. destruct B; try apply H.
  destruct (eq_atom a a0) eqn:Ha; try apply H.
  destruct S; try apply H. apply H0.
  apply atom_beq_eq in Ha. rewrite <- Ha. auto.
- destruct (subst_ind_fit (neg A) S); try apply H.
  simpl. destruct B; try apply H.
  destruct (eq_f A B) eqn:HA; try apply H.
  destruct S; try apply H. apply H0.
  apply f_eq_decid in HA. rewrite <- HA. auto.
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
  simpl. destruct B; try apply H.
  destruct (eq_nat n n0) eqn:Hn; destruct (eq_f A B) eqn:HA; try apply H.
  destruct S; try apply H. apply H0.
  apply f_eq_decid in HA. rewrite <- HA.
  apply nat_eq_decid in Hn. rewrite <- Hn. auto.
Qed.



















(*
###############################################################################
Section 9.1: Here we show invertibility of double negation,
i.e. from a proof of ~~E \/ D we can get a proof of E \/ D.
###############################################################################
*)

(* Defining double negation substitution in an ptree. First, we replace
~~E with E at certain places in a formula (given a substitution indicator).
Applying this operation to an entire ptree, we change the substitution
indicator as the structure of the formula(s) change as we move up the ptree. *)
(* *)
Definition dub_neg_sub_formula (A E : formula) (S : subst_ind) : formula :=
  formula_sub_ind A (neg (neg E)) E S.

Lemma dub_neg_sub_formula_closed : forall (A : formula),
  closed A = true ->
  forall (E : formula) (S : subst_ind),
    closed (dub_neg_sub_formula A E S) = true.
Proof.
intros. unfold dub_neg_sub_formula. apply formula_sub_ind_closed; auto.
Qed.


Fixpoint dub_neg_sub_ptree_fit
  (P : ptree) (E : formula) (S : subst_ind) : ptree :=
match P, S with
| deg_up d P', _ => deg_up d (dub_neg_sub_ptree_fit P' E S)

| ord_up alpha P', _ => ord_up alpha (dub_neg_sub_ptree_fit P' E S)

| node A, _ => P

| exchange_ab A B d alpha P', lor_ind S_B S_A =>
    exchange_ab
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula B E S_B)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind S_A S_B))

| exchange_cab C A B d alpha P', lor_ind (lor_ind S_C S_B) S_A =>
    exchange_cab
      (dub_neg_sub_formula C E S_C)
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula B E S_B)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind (lor_ind S_C S_A) S_B))

| exchange_abd A B D d alpha P', lor_ind (lor_ind S_B S_A) S_D =>
    exchange_abd
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula B E S_B)
      (dub_neg_sub_formula D E S_D)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind (lor_ind S_A S_B) S_D))

| exchange_cabd C A B D d alpha P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D =>
    exchange_cabd
      (dub_neg_sub_formula C E S_C)
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula B E S_B)
      (dub_neg_sub_formula D E S_D)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D))

| contraction_a A d alpha P', _ =>
    contraction_a
      (dub_neg_sub_formula A E S)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind S S))

| contraction_ad A D d alpha P', lor_ind S_A S_D =>
    contraction_ad
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula D E S_D)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind (lor_ind S_A S_A) S_D))

| weakening_ad A D d alpha P', lor_ind S_A S_D =>
    weakening_ad
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula D E S_D)
      d alpha
      (dub_neg_sub_ptree_fit P' E S_D)

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, _ => P

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_AB S_D =>
    demorgan_abd
      A B (dub_neg_sub_formula D E S_D) d1 d2 alpha1 alpha2
      (dub_neg_sub_ptree_fit P1 E (lor_ind (0) S_D))
      (dub_neg_sub_ptree_fit P2 E (lor_ind (0) S_D))

| negation_a A d alpha P', _ =>
    (match eq_f A E, S with
    | true, (1) => ord_up (ord_succ alpha) P'
    | _, _ => P
    end)

| negation_ad A D d alpha P', lor_ind S_A S_D =>
    (match eq_f A E, S_A with
    | true, (1) => ord_up (ord_succ alpha) (dub_neg_sub_ptree_fit P' E (lor_ind (non_target A) S_D))
    | _, _ => 
        negation_ad
          A
          (dub_neg_sub_formula D E S_D)
          d alpha
          (dub_neg_sub_ptree_fit P' E (lor_ind (non_target A) S_D))
    end)

| quantification_a A n t d alpha P', _ => P

| quantification_ad A D n t d alpha P', lor_ind S_A S_D =>
    quantification_ad
      A
      (dub_neg_sub_formula D E S_D)
      n t d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind (0) S_D))


| w_rule_a A n d alpha g, _ => P

| w_rule_ad A D n d alpha g, lor_ind S_A S_D =>
    w_rule_ad
      A
      (dub_neg_sub_formula D E S_D)
      n
      d alpha
      (fun (n : nat) =>
          dub_neg_sub_ptree_fit (g n) E (lor_ind (non_target A) S_D))

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ca
      (dub_neg_sub_formula C E S)
      A d1 d2 alpha1 alpha2
      (dub_neg_sub_ptree_fit P1 E (lor_ind S (non_target A)))
      P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ad
      A (dub_neg_sub_formula D E S) d1 d2 alpha1 alpha2
      P1
      (dub_neg_sub_ptree_fit P2 E (lor_ind (0) S))

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_D =>
    cut_cad
      (dub_neg_sub_formula C E S_C)
      A (dub_neg_sub_formula D E S_D) d1 d2 alpha1 alpha2
      (dub_neg_sub_ptree_fit P1 E (lor_ind S_C (non_target A)))
      (dub_neg_sub_ptree_fit P2 E (lor_ind (0) S_D))

| _, _ => P
end.

Fixpoint dub_neg_sub_ptree (P : ptree) (E : formula) (S : subst_ind) : ptree :=
match subst_ind_fit (ptree_formula P) S with
| false => P
| true => dub_neg_sub_ptree_fit P E S
end.


(* First, we must prove that dub_neg_sub_ptree simply changes the base formula
of an ptree the way we expect with dub_neg_sub_formula *)
(* *)
Lemma dub_neg_ptree_formula_aux' :
  forall (P : ptree) (E : formula) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
    dub_neg_sub_ptree P E S = P.
Proof. intros. unfold dub_neg_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma dub_neg_ptree_formula_aux :
  forall (P : ptree) (E : formula) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
      ptree_formula (dub_neg_sub_ptree P E S) =
      dub_neg_sub_formula (ptree_formula P) E S.
Proof.
intros. rewrite dub_neg_ptree_formula_aux'.
- unfold dub_neg_sub_formula. rewrite sub_fit_false. auto. apply H.
- apply H.
Qed.

Lemma dub_neg_ptree_formula_true :
  forall (P : ptree) (E : formula) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    dub_neg_sub_ptree_fit P E S = dub_neg_sub_ptree P E S.
Proof. intros. unfold dub_neg_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma dub_neg_ptree_formula' : forall (P : ptree) (E : formula),
  valid P ->
  forall (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    ptree_formula (dub_neg_sub_ptree P E S) =
    dub_neg_sub_formula (ptree_formula P) E S.
Proof.
intros P E.
induction P; try intros H S Hs.

- simpl in Hs. simpl. rewrite Hs. simpl.
  rewrite (dub_neg_ptree_formula_true _ _ _ Hs).
  destruct H as [H1 H2]. apply (IHP H2). auto.

- simpl in Hs. simpl. rewrite Hs. simpl.
  rewrite (dub_neg_ptree_formula_true _ _ _ Hs).
  destruct H as [[H1 H2] H3]. apply (IHP H2). auto.

- simpl. inversion H.
  destruct (axiom_atomic _ H1); destruct H0; rewrite H0;
  unfold dub_neg_sub_formula; simpl; destruct S; auto.

- simpl.
  destruct S; inversion Hs; rewrite H1; simpl; unfold dub_neg_sub_formula.
  rewrite formula_sub_ind_lor; auto.

- simpl.
  destruct S; try destruct S1; inversion Hs; rewrite H1;
  simpl; unfold dub_neg_sub_formula.
  rewrite formula_sub_ind_lor, formula_sub_ind_lor; auto.
  apply (and_bool_prop _ _ H1).

- simpl.
  destruct S; try destruct S1; inversion Hs; rewrite H1;
  simpl; unfold dub_neg_sub_formula.
  rewrite formula_sub_ind_lor, formula_sub_ind_lor; auto.
  apply (and_bool_prop _ _ H1).

- simpl. destruct S; simpl.
  + unfold dub_neg_sub_formula. auto.
  + unfold dub_neg_sub_formula. auto.
  + destruct S1; try destruct S1_1; inversion Hs.
    rewrite H1. simpl. unfold dub_neg_sub_formula.
    destruct (and_bool_prop _ _ H1). destruct (and_bool_prop _ _ H0).
    repeat rewrite formula_sub_ind_lor; auto.

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
  + unfold dub_neg_sub_formula. simpl. inversion H as [[[H1 H2] H3] H4].
    rewrite H1. rewrite (f_eq_decid _ _ Heq). rewrite eq_f_refl. auto.
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
    * inversion Hs. rewrite H1. simpl. inversion H as [[[H2 H3] H4] H5].
      rewrite dub_neg_ptree_formula_true.
      { rewrite IHP; auto.
        { rewrite H2. unfold dub_neg_sub_formula.
          rewrite non_target_sub_lor. simpl. rewrite H1. rewrite Heq.
          rewrite sub_fit_true; auto. rewrite (f_eq_decid _ _ Heq); auto. }
        { rewrite H2. simpl. rewrite non_target_fit, H1. auto. } }
      { rewrite H2. simpl. rewrite non_target_fit, H1. auto. }
    * simpl. inversion Hs.
  + inversion Hs.
  + inversion Hs.
  + destruct S1.
    * apply (subst_ind_fit_lor) in Hs. destruct (and_bool_prop _ _ Hs).
      rewrite H1. simpl. unfold dub_neg_sub_formula.
      rewrite formula_sub_ind_lor, formula_sub_ind_0. auto. apply Hs.
    * inversion Hs. rewrite H1. simpl. unfold dub_neg_sub_formula.
      rewrite formula_sub_ind_lor; auto. simpl. rewrite Heq. auto.
    * simpl. inversion Hs.

- simpl. destruct S; simpl; unfold dub_neg_sub_formula; auto.

- simpl. destruct S.
  + simpl. unfold dub_neg_sub_formula. simpl. auto.
  + simpl. unfold dub_neg_sub_formula. simpl. auto.
  + destruct S1; inversion Hs; rewrite H1; simpl; unfold dub_neg_sub_formula.
    * rewrite formula_sub_ind_lor; auto.
    * simpl. rewrite H1. rewrite sub_fit_true; auto.

- intros. simpl. destruct S; simpl; unfold dub_neg_sub_formula; auto.

- intros. simpl. destruct S; try destruct S1; inversion H0;
  rewrite H2; unfold dub_neg_sub_formula; rewrite formula_sub_ind_lor; auto.

- simpl. inversion Hs. rewrite H1. auto.

- simpl. inversion Hs. rewrite H1. auto.

- simpl. destruct S; inversion Hs.
  rewrite H1. simpl. unfold dub_neg_sub_formula.
  rewrite formula_sub_ind_lor; auto.
Qed.


Lemma dub_neg_ptree_formula : forall (P : ptree) (E : formula),
  valid P ->
  forall (S : subst_ind),
    ptree_formula (dub_neg_sub_ptree P E S) =
    dub_neg_sub_formula (ptree_formula P) E S.
Proof.
intros. destruct (subst_ind_fit (ptree_formula P) S) eqn:Hs.
- apply dub_neg_ptree_formula'. apply X. apply Hs.
- apply dub_neg_ptree_formula_aux. apply Hs.
Qed.





(* Second, we must prove that dub_neg_sub_ptree does not change the degree
of an ptree. *)
(* *)
Lemma dub_neg_ptree_deg : forall (P : ptree) (E : formula),
  valid P ->
  forall (S : subst_ind), ptree_deg (dub_neg_sub_ptree P E S) = ptree_deg P.
Proof.
intros P E H. induction P; intros S.
- simpl. case (subst_ind_fit (ptree_formula P) S); auto.
- simpl. case (subst_ind_fit (ptree_formula P) S) eqn:Hfit; auto. simpl.
  rewrite (dub_neg_ptree_formula_true _ _ _ Hfit).
  apply IHP. inversion H. destruct X as [X1 X2]. auto.
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
- simpl. destruct S; auto; destruct (eq_f f E); auto.
  inversion H as [[H1 H2] H3]. auto.
- simpl. destruct S; auto.
  destruct S1; destruct (subst_ind_fit f0 S2) eqn:HS2;
  destruct (eq_f f E); auto.
  simpl. inversion H as [[[H1 H2] H3] H4]. rewrite H3.
  rewrite dub_neg_ptree_formula_true.
  + apply (IHP H2 (lor_ind (non_target f) S2)).
  + rewrite H1. simpl. rewrite HS2,non_target_fit. auto.
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


(* Third, we must prove that dub_neg_sub_ptree does not change the ordinal
of an ptree. *)
(* *)
Lemma dub_neg_ptree_ord : forall (P : ptree) (E : formula),
  valid P ->
  forall (S : subst_ind), (ptree_ord (dub_neg_sub_ptree P E S)) = (ptree_ord P).
Proof.
intros P E H. induction P; intros S.
- simpl. case (subst_ind_fit (ptree_formula P) S) eqn:Hfit; simpl; auto.
  rewrite (dub_neg_ptree_formula_true _ _ _ Hfit).
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
- simpl. destruct S; destruct (eq_f f E); auto.
- simpl. destruct S; auto; destruct S1; destruct (subst_ind_fit f0 S2) eqn:HS2;
  destruct (eq_f f E); auto.
- simpl. destruct S; auto.
- simpl. destruct S; auto; destruct S1; auto; destruct (subst_ind_fit f0 S2); auto.
- simpl. destruct S; auto.
- simpl. destruct S; auto; destruct S1; auto; destruct (subst_ind_fit f0 S2); auto.
- simpl. destruct (subst_ind_fit f S); auto.
- simpl. destruct (subst_ind_fit f0 S); auto.
- simpl. destruct S; auto. destruct (subst_ind_fit f S1 && subst_ind_fit f1 S2); auto.
Qed.

(* Now we prove that if we have a valid ptree, performing our
double negation substitution on it results in a valid ptree *)
(* *)
Lemma dub_neg_valid : forall (P : ptree) (E : formula),
  valid P ->
  forall (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    valid (dub_neg_sub_ptree P E S).
Proof.
intros P E.
induction P; try intros H S Hs.

- simpl. inversion H as [H1 H2]. inversion Hs. rewrite H3.
  rewrite dub_neg_ptree_formula_true; auto. split.
  + rewrite dub_neg_ptree_deg; auto.
  + apply (IHP H2 S H3).

- simpl. inversion H as [[H1 H2] H3]. inversion Hs. rewrite H4.
  rewrite dub_neg_ptree_formula_true; auto. repeat split.
  + rewrite (dub_neg_ptree_ord _ E H2 S). apply H1.
  + auto.
  + apply H3.

- simpl. destruct (subst_ind_fit f S); apply H.

- simpl. destruct S; inversion Hs. rewrite H1. simpl.
  inversion H as [[[H2 H3] H4] H5].
  repeat split; rewrite dub_neg_ptree_formula_true.
  + rewrite dub_neg_ptree_formula; auto.
    rewrite H2. unfold dub_neg_sub_formula.
    rewrite formula_sub_ind_lor; auto. apply (and_bool_symm _ _ H1).
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + apply IHP. apply H. rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + rewrite dub_neg_ptree_deg; auto.
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + rewrite (dub_neg_ptree_ord _ E H3 (lor_ind S2 S1)). apply H5.
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).

- simpl. destruct S; try destruct S1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H4 H5] H6] H7].
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  repeat split; rewrite dub_neg_ptree_formula_true.
  + rewrite dub_neg_ptree_formula; auto.
    rewrite H4. unfold dub_neg_sub_formula.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H1, H2. auto.
    * simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + apply IHP; auto. rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite dub_neg_ptree_deg; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite dub_neg_ptree_ord; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.

- simpl. destruct S; try destruct S1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H4 H5] H6] H7].
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  repeat split; rewrite dub_neg_ptree_formula_true.
  + rewrite dub_neg_ptree_formula; auto.
    rewrite H4. unfold dub_neg_sub_formula.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H1, H3. auto.
    * simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + apply IHP; auto. rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite dub_neg_ptree_deg; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite dub_neg_ptree_ord; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.

- simpl. destruct S; try destruct S1; try destruct S1_1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H5 H6] H7] H8].
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  destruct (and_bool_prop _ _ H1). clear H1.
  repeat split; rewrite dub_neg_ptree_formula_true.
  + rewrite dub_neg_ptree_formula; auto.
    rewrite H5. unfold dub_neg_sub_formula.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H0,H3. auto.
    * simpl. rewrite H0, H3, H4. auto.
    * simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + apply IHP; auto. rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite dub_neg_ptree_deg; auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite dub_neg_ptree_ord; auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.

- simpl. inversion Hs. rewrite H1. inversion H as [[[H2 H3] H4] H5].
  repeat split; rewrite dub_neg_ptree_formula_true.
  + rewrite dub_neg_ptree_formula; auto.
    unfold dub_neg_sub_formula. rewrite H2.
    rewrite formula_sub_ind_lor; auto. rewrite H1. auto.
  + rewrite H2. simpl. rewrite H1. auto.
  + apply IHP. apply H. rewrite H2. simpl. rewrite H1. auto.
  + rewrite H2. simpl. rewrite H1. auto.
  + rewrite dub_neg_ptree_deg; auto.
  + rewrite H2. simpl. rewrite H1. auto.
  + rewrite dub_neg_ptree_ord; auto.
  + rewrite H2. simpl. rewrite H1. auto.

- simpl. destruct S; inversion Hs. rewrite H1.
  inversion H as [[[H2 H3] H4] H5]. destruct (and_bool_prop _ _ H1).
  repeat split; rewrite dub_neg_ptree_formula_true.
  + rewrite dub_neg_ptree_formula; auto.
    unfold dub_neg_sub_formula. rewrite H2.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H0. auto.
    * simpl. rewrite H0, H6. auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + apply IHP. apply H. rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite dub_neg_ptree_deg; auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite dub_neg_ptree_ord; auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.

- simpl. destruct S; inversion Hs. rewrite H1. simpl.
  inversion H as [[[[H2 H3] H4] H5] H6]. destruct (and_bool_prop _ _ H1).
  repeat split.
  + rewrite dub_neg_ptree_formula_true.
    * rewrite dub_neg_ptree_formula; auto. rewrite H2. auto.
    * rewrite H2. auto.
  + apply dub_neg_sub_formula_closed. auto.
  + rewrite dub_neg_ptree_formula_true.
    * apply IHP; auto. rewrite H2. auto.
    * rewrite H2. auto.
  + rewrite dub_neg_ptree_formula_true.
    * rewrite dub_neg_ptree_deg; auto.
    * rewrite H2. auto.
  + rewrite dub_neg_ptree_formula_true.
    * rewrite dub_neg_ptree_ord; auto.
    * rewrite H2. auto.

- simpl. destruct S; apply H.

- simpl. destruct S; try apply H.
  destruct S1; inversion Hs; rewrite H1; simpl.
  + destruct H as [[[[[[[H2 H3] H4] H5] H6] H7] H8] H9].
    repeat split; rewrite dub_neg_ptree_formula_true.
    * rewrite dub_neg_ptree_formula; auto.
      rewrite H2. unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
      { simpl. destruct (eq_f f (neg E)); auto. }
      { rewrite H1. auto. }
    * rewrite H2. simpl. apply H1.
    * apply IHP1; auto. rewrite H2. apply H1.
    * rewrite H2. simpl. apply H1.
    * rewrite dub_neg_ptree_formula; auto.
      rewrite H4. unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
      { simpl. destruct (eq_f f0 (neg E)); auto. }
      { rewrite H1. auto. }
    * rewrite H4. simpl. apply H1.
    * apply IHP2; auto. rewrite H4. simpl. apply H1.
    * rewrite H4. simpl. apply H1.
    * rewrite dub_neg_ptree_deg; auto.
    * rewrite H2. simpl. apply H1.
    * rewrite dub_neg_ptree_deg; auto.
    * rewrite H4. simpl. apply H1.
    * rewrite dub_neg_ptree_ord; auto.
    * rewrite H2. simpl. apply H1.
    * rewrite dub_neg_ptree_ord; auto.
    * rewrite H4. simpl. apply H1.
  + destruct H as [[[[[[[H2 H3] H4] H5] H6] H7] H8] H9].
    repeat split; rewrite dub_neg_ptree_formula_true.
    * rewrite dub_neg_ptree_formula; auto.
      rewrite H2. unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
      { simpl. destruct (eq_f f (neg E)); auto. }
      { rewrite H1. auto. }
    * rewrite H2. simpl. apply H1.
    * apply IHP1; auto. rewrite H2. apply H1.
    * rewrite H2. simpl. apply H1.
    * rewrite dub_neg_ptree_formula; auto.
      rewrite H4. unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
      { simpl. destruct (eq_f f0 (neg E)); auto. }
      { rewrite H1. auto. }
    * rewrite H4. simpl. apply H1.
    * apply IHP2; auto. rewrite H4. simpl. apply H1.
    * rewrite H4. simpl. apply H1.
    * rewrite dub_neg_ptree_deg; auto.
    * rewrite H2. simpl. apply H1.
    * rewrite dub_neg_ptree_deg; auto.
    * rewrite H4. simpl. apply H1.
    * rewrite dub_neg_ptree_ord; auto.
    * rewrite H2. simpl. apply H1.
    * rewrite dub_neg_ptree_ord; auto.
    * rewrite H4. simpl. apply H1.

- simpl. destruct S; destruct (eq_f f E); try apply H. simpl. inversion H. rewrite H0. destruct X as [[H1 H2] H3]. repeat split; auto. apply ord_succ_monot. apply ord_succ_nf. apply ptree_ord_nf. apply H2.

- simpl. inversion H as [[[H2 H3] H4] H5]. destruct S; try apply H.
  destruct S1; inversion Hs; rewrite H1; simpl.
  + destruct (eq_f f E).
    * simpl. repeat split.
      { rewrite dub_neg_ptree_formula_true, dub_neg_ptree_formula; auto.
        { rewrite H2. unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
          { rewrite non_target_sub. auto. }
          { rewrite non_target_fit, H1. auto. } }
        { rewrite H2. simpl. rewrite non_target_fit, H1. auto. } }
      { rewrite dub_neg_ptree_formula_true; try (apply (IHP H3));
        rewrite H2; simpl; rewrite non_target_fit, H1; auto. }
      { rewrite dub_neg_ptree_formula_true.
        { rewrite dub_neg_ptree_deg; auto. }
        { rewrite H2. simpl. rewrite non_target_fit, H1. auto. } }
      { rewrite dub_neg_ptree_formula_true.
        { rewrite dub_neg_ptree_ord; auto. }
        { rewrite H2. simpl. rewrite non_target_fit, H1. auto. } }
    * simpl. repeat split.
      { rewrite dub_neg_ptree_formula_true, dub_neg_ptree_formula; auto.
        { rewrite H2. unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
          { rewrite non_target_sub. auto. }
          { rewrite non_target_fit, H1. auto. } }
        { rewrite H2. simpl. rewrite non_target_fit, H1. auto. } }
      { rewrite dub_neg_ptree_formula_true; try (apply (IHP H3));
        rewrite H2; simpl; rewrite non_target_fit, H1; auto. }
      { rewrite dub_neg_ptree_formula_true.
        { rewrite dub_neg_ptree_deg; auto. }
        { rewrite H2. simpl. rewrite non_target_fit, H1. auto. } }
      { rewrite dub_neg_ptree_formula_true.
        { rewrite dub_neg_ptree_ord; auto. }
        { rewrite H2. simpl. rewrite non_target_fit, H1. auto. } }
  + destruct (eq_f f E). 
    * simpl. repeat split.
      { rewrite H5. rewrite dub_neg_ptree_formula_true.
        { rewrite dub_neg_ptree_ord. apply ord_succ_monot. apply H3. }
        { rewrite H2. simpl. rewrite non_target_fit, H1. auto. }
        }
      { rewrite dub_neg_ptree_formula_true; try (apply (IHP H3)); rewrite H2; simpl; rewrite non_target_fit, H1; auto. }
      { rewrite H5. apply ord_succ_nf. apply ptree_ord_nf. apply H3. }
    * simpl. repeat split.
      { rewrite dub_neg_ptree_formula_true, dub_neg_ptree_formula; auto.
        { rewrite H2. unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
          { rewrite non_target_sub. auto. }
          { rewrite non_target_fit, H1. auto. } }
        { rewrite H2. simpl. rewrite non_target_fit, H1. auto. } }
      { rewrite dub_neg_ptree_formula_true; try (apply (IHP H3));
        rewrite H2; simpl; rewrite non_target_fit, H1; auto. }
      { rewrite dub_neg_ptree_formula_true.
        { rewrite dub_neg_ptree_deg; auto. }
        { rewrite H2. simpl. rewrite non_target_fit, H1. auto. } }
      { rewrite dub_neg_ptree_formula_true.
        { rewrite dub_neg_ptree_ord; auto. }
        { rewrite H2. simpl. rewrite non_target_fit, H1. auto. } }

- simpl. destruct S; apply H.

- simpl. destruct S; try apply H. inversion H as [[[[H0 H1] H2] H3] H4].
  destruct S1; inversion Hs; rewrite H6; simpl.
  + repeat split; auto.
    * rewrite dub_neg_ptree_formula_true, dub_neg_ptree_formula; auto.
      { rewrite H0. unfold dub_neg_sub_formula.
        { rewrite formula_sub_ind_lor. simpl.
          { destruct (eq_f (substitution f n t)); auto. }
          { simpl. apply H6. } } }
      { rewrite H0. simpl. apply H6. }
    * rewrite dub_neg_ptree_formula_true.
      { apply IHP; auto. rewrite H0. simpl. apply H6. }
      { rewrite H0. simpl. apply H6. }
    * rewrite dub_neg_ptree_formula_true.
      { rewrite dub_neg_ptree_deg; auto. }
      { rewrite H0. simpl. auto. }
    * rewrite dub_neg_ptree_formula_true.
      { rewrite dub_neg_ptree_ord; auto. }
      { rewrite H0. simpl. auto. }
  + repeat split; auto.
    * rewrite dub_neg_ptree_formula_true, dub_neg_ptree_formula; auto.
      { rewrite H0. unfold dub_neg_sub_formula.
        { rewrite formula_sub_ind_lor. simpl.
          { destruct (eq_f (substitution f n t)); auto. }
          { simpl. apply H6. } } }
      { rewrite H0. simpl. apply H6. }
    * rewrite dub_neg_ptree_formula_true.
      { apply IHP; auto. rewrite H0. simpl. apply H6. }
      { rewrite H0. simpl. apply H6. }
    * rewrite dub_neg_ptree_formula_true.
      { rewrite dub_neg_ptree_deg; auto. }
      { rewrite H0. simpl. auto. }
    * rewrite dub_neg_ptree_formula_true.
      { rewrite dub_neg_ptree_ord; auto. }
      { rewrite H0. simpl. auto. }

- intros. simpl. destruct S; apply H.

- rename H into H0. rename X into H. rename Hs into H1.
  simpl. destruct S; try apply H0. destruct S1; inversion H1.
  + rewrite H3. simpl. intros. destruct (valid_w_rule_ad _ _ _ _ _ _ H0 m) as [[[H4 H5] H6] H7].
    repeat split.
    * rewrite dub_neg_ptree_formula_true, dub_neg_ptree_formula; auto.
      { rewrite H4. unfold dub_neg_sub_formula.
        rewrite formula_sub_ind_lor;
        rewrite (non_target_term_sub f n (represent m)).
        { rewrite non_target_sub. auto. }
        { rewrite non_target_fit. apply H3. } }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
    * rewrite dub_neg_ptree_formula_true.
      { apply H. apply H5. rewrite H4. simpl.
        rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
    * rewrite dub_neg_ptree_formula_true.
      { rewrite dub_neg_ptree_deg; auto. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. rewrite H3. auto. }
    * rewrite dub_neg_ptree_formula_true.
      { rewrite dub_neg_ptree_ord; auto. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. rewrite H3. auto. }
  + rewrite H3. simpl. intros. destruct (valid_w_rule_ad _ _ _ _ _ _ H0 m) as [[[H4 H5] H6] H7].
    repeat split.
    * rewrite dub_neg_ptree_formula_true, dub_neg_ptree_formula; auto.
      { rewrite H4. unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
        { rewrite (non_target_term_sub f n (represent m)).
          rewrite non_target_sub. auto. }
        { rewrite (non_target_term_sub f n (represent m)).
          rewrite non_target_fit. apply H3. } }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
    * rewrite dub_neg_ptree_formula_true.
      { apply H. apply H5. rewrite H4. simpl.
        rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
    * rewrite dub_neg_ptree_formula_true.
      { rewrite dub_neg_ptree_deg; auto. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. rewrite H3. auto. }
    * rewrite dub_neg_ptree_formula_true.
      { rewrite dub_neg_ptree_ord; auto. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. rewrite H3. auto. }
- clear IHP2. simpl. destruct (subst_ind_fit f S) eqn:Heq; try apply H. simpl.
  inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  repeat split; auto; rewrite dub_neg_ptree_formula_true.
  + rewrite dub_neg_ptree_formula; auto.
    rewrite H1. unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
    * rewrite non_target_sub. auto.
    * rewrite Heq, non_target_fit. auto.
  + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + apply IHP1; auto. rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + rewrite dub_neg_ptree_deg; auto.
  + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + rewrite dub_neg_ptree_ord; auto.
  + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.

- clear IHP1. simpl. destruct (subst_ind_fit f0 S) eqn:Heq; try apply H. simpl.
  inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  repeat split; auto; rewrite dub_neg_ptree_formula_true.
  + rewrite dub_neg_ptree_formula; auto.
    rewrite H3. unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
    * rewrite non_target_sub. auto.
    * rewrite Heq, non_target_fit. auto.
  + rewrite H3. simpl. auto.
  + apply IHP2; auto. rewrite H3. simpl. auto.
  + rewrite H3. simpl. auto.
  + rewrite dub_neg_ptree_deg; auto.
  + rewrite H3. simpl. auto.
  + rewrite dub_neg_ptree_ord; auto.
  + rewrite H3. simpl. auto.

- simpl. inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  destruct S; try inversion Hs. rewrite H9.
  destruct (and_bool_prop _ _ H9) as [H10 H11].
  simpl. repeat split; rewrite dub_neg_ptree_formula_true.
  + rewrite dub_neg_ptree_formula; auto.
    rewrite H1. unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
    * rewrite non_target_sub. auto.
    * rewrite H10, non_target_fit. auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + apply IHP1; auto. rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite dub_neg_ptree_formula; auto.
    rewrite H3. unfold dub_neg_sub_formula. rewrite formula_sub_ind_lor.
    * rewrite non_target_sub. auto.
    * rewrite H11, non_target_fit. auto.
  + rewrite H3. simpl. auto.
  + apply IHP2; auto. rewrite H3. simpl. auto.
  + rewrite H3. simpl. auto.
  + rewrite dub_neg_ptree_deg; auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite dub_neg_ptree_deg; auto.
  + rewrite H3. simpl. auto.
  + rewrite dub_neg_ptree_ord; auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite dub_neg_ptree_ord; auto.
  + rewrite H3. simpl. auto.
Qed.





(* We finally show that if the formulas ~~A and/or ~~A \/ D are provable,
so are the formulas A and/or A \/ D *)
(* *)
Lemma double_negation_invertible_a :
  forall (A : formula) (d : nat) (alpha : ord),
  provable (neg (neg A)) d alpha -> provable A d alpha.
Proof.
unfold provable. intros A d alpha H. destruct H as [t [[[Ht1 Ht2] Ht3] Ht4]].
exists (dub_neg_sub_ptree t A (1)). unfold P_proves. repeat split.
- rewrite dub_neg_ptree_formula; auto.
  rewrite Ht1. unfold dub_neg_sub_formula. simpl. rewrite eq_f_refl. auto.
- apply dub_neg_valid; auto. rewrite Ht1. auto.
- rewrite dub_neg_ptree_deg; auto.
- rewrite dub_neg_ptree_ord; auto.
Qed.

Lemma double_negation_invertible_ad :
  forall (A D : formula) (d : nat) (alpha : ord),
  provable (lor (neg (neg A)) D) d alpha -> provable (lor A D) d alpha.
Proof.
unfold provable. intros A D d alpha H. destruct H as [t [[[Ht1 Ht2] Ht3] Ht4]].
exists (dub_neg_sub_ptree t A (lor_ind (1) (non_target D))).
unfold P_proves. repeat split.
- rewrite dub_neg_ptree_formula; auto.
  rewrite Ht1. unfold dub_neg_sub_formula. simpl. rewrite eq_f_refl.
  rewrite non_target_fit. rewrite non_target_sub'. auto.
- apply dub_neg_valid; auto. rewrite Ht1. simpl. rewrite non_target_fit. auto.
- rewrite dub_neg_ptree_deg; auto.
- rewrite dub_neg_ptree_ord; auto.
Qed.








(*
###############################################################################
Section 9.2: Here we show invertibility of DeMorgan (the first half),
i.e. from a proof of ~(E \/ F) \/ D we can get a proof of ~E \/ D.
###############################################################################
*)

(* Defining DeMorgan substitution in an ptree. First, we replace ~(E \/ F)
with ~E at certain places in a formula (given a substitution indicator).
Applying this operation to an entire ptree, we change the substitution
indicator as the structure of the formula(s) change as we move up the ptree. *)
(* *)
Definition demorgan1_sub_formula (A E F : formula) (S : subst_ind) : formula :=
  formula_sub_ind A (neg (lor E F)) (neg E) S.

Lemma demorgan1_sub_formula_closed : forall (A : formula),
  closed A = true ->
  forall (E F : formula) (S : subst_ind),
    closed (demorgan1_sub_formula A E F S) = true.
Proof.
intros. unfold demorgan1_sub_formula. apply formula_sub_ind_closed; auto.
simpl. intros. destruct (and_bool_prop _ _ H0). auto.
Qed.

Fixpoint demorgan1_sub_ptree_fit
  (P : ptree) (E F : formula) (S : subst_ind) : ptree :=
match P, S with
| deg_up d P', _ => deg_up d (demorgan1_sub_ptree_fit P' E F S)

| ord_up alpha P', _ => ord_up alpha (demorgan1_sub_ptree_fit P' E F S)

| node A, _ => P

| exchange_ab A B d alpha P', lor_ind S_B S_A =>
    exchange_ab
      (demorgan1_sub_formula A E F S_A)
      (demorgan1_sub_formula B E F S_B)
      d alpha
      (demorgan1_sub_ptree_fit P' E F (lor_ind S_A S_B))

| exchange_cab C A B d alpha P', lor_ind (lor_ind S_C S_B) S_A =>
    exchange_cab
      (demorgan1_sub_formula C E F S_C)
      (demorgan1_sub_formula A E F S_A)
      (demorgan1_sub_formula B E F S_B)
      d alpha
      (demorgan1_sub_ptree_fit P' E F (lor_ind (lor_ind S_C S_A) S_B))

| exchange_abd A B D d alpha P', lor_ind (lor_ind S_B S_A) S_D =>
    exchange_abd
      (demorgan1_sub_formula A E F S_A)
      (demorgan1_sub_formula B E F S_B)
      (demorgan1_sub_formula D E F S_D)
      d alpha
      (demorgan1_sub_ptree_fit P' E F (lor_ind (lor_ind S_A S_B) S_D))

| exchange_cabd C A B D d alpha P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D =>
    exchange_cabd
      (demorgan1_sub_formula C E F S_C)
      (demorgan1_sub_formula A E F S_A)
      (demorgan1_sub_formula B E F S_B)
      (demorgan1_sub_formula D E F S_D)
      d alpha
      (demorgan1_sub_ptree_fit P' E F (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D))

| contraction_a A d alpha P', _ =>
    contraction_a
      (demorgan1_sub_formula A E F S)
      d alpha
      (demorgan1_sub_ptree_fit P' E F (lor_ind S S))

| contraction_ad A D d alpha P', lor_ind S_A S_D =>
    contraction_ad
      (demorgan1_sub_formula A E F S_A)
      (demorgan1_sub_formula D E F S_D)
      d alpha
      (demorgan1_sub_ptree_fit P' E F (lor_ind (lor_ind S_A S_A) S_D))

| weakening_ad A D d alpha P', lor_ind S_A S_D =>
    weakening_ad
      (demorgan1_sub_formula A E F S_A)
      (demorgan1_sub_formula D E F S_D)
      d alpha
      (demorgan1_sub_ptree_fit P' E F S_D)

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, _ =>
    (match eq_f A E, eq_f B F, S with
    | true, true, (1) =>
      (match eq_nat d1 (ptree_deg P) with
      | true => ord_up (ptree_ord P) P1
      | false => deg_up (ptree_deg P) (ord_up (ptree_ord P) P1)
      end)
    | _, _, _ => P
    end)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_AB S_D =>
    (match eq_f A E, eq_f B F, S_AB with
    | true, true, (1) =>
      (match eq_nat d1 (ptree_deg P) with
      | true =>
          ord_up
            (ptree_ord P)
            (demorgan1_sub_ptree_fit P1 E F (lor_ind (non_target (neg A)) S_D))
      | false =>
          deg_up
            (ptree_deg P)
              (ord_up
                (ptree_ord P)
                (demorgan1_sub_ptree_fit
                  P1 E F
                  (lor_ind (non_target (neg A)) S_D)))
      end)
    | _, _, _ =>
        demorgan_abd
          A B
          (demorgan1_sub_formula D E F S_D)
          d1 d2 alpha1 alpha2
          (demorgan1_sub_ptree_fit P1 E F (lor_ind (non_target (neg A)) S_D))
          (demorgan1_sub_ptree_fit P2 E F (lor_ind (non_target (neg B)) S_D))
    end)

| negation_a A d alpha P', _ => P

| negation_ad A D d alpha P', lor_ind S_A S_D =>
    negation_ad
      A
      (demorgan1_sub_formula D E F S_D)
      d alpha
      (demorgan1_sub_ptree_fit P' E F (lor_ind (non_target A) S_D))

| quantification_a A n t d alpha P', _ => P

| quantification_ad A D n t d alpha P', lor_ind S_A S_D =>
    quantification_ad
      A
      (demorgan1_sub_formula D E F S_D)
      n t d alpha
      (demorgan1_sub_ptree_fit P' E F (lor_ind (0) S_D))

| w_rule_a A n d alpha g, _ => P

| w_rule_ad A D n d alpha g, lor_ind S_A S_D =>
    w_rule_ad
      A
      (demorgan1_sub_formula D E F S_D)
      n d alpha
      (fun (n : nat) =>
          demorgan1_sub_ptree_fit (g n) E F (lor_ind (non_target A) S_D))

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ca
      (demorgan1_sub_formula C E F S)
      A d1 d2 alpha1 alpha2
      (demorgan1_sub_ptree_fit P1 E F (lor_ind S (non_target A)))
      P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ad
      A
      (demorgan1_sub_formula D E F S)
      d1 d2 alpha1 alpha2
      P1
      (demorgan1_sub_ptree_fit P2 E F (lor_ind (0) S))

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_D =>
    cut_cad
      (demorgan1_sub_formula C E F S_C)
      A
      (demorgan1_sub_formula D E F S_D)
      d1 d2 alpha1 alpha2
      (demorgan1_sub_ptree_fit P1 E F (lor_ind S_C (non_target A)))
      (demorgan1_sub_ptree_fit P2 E F (lor_ind (0) S_D))

| _, _ => P
end.

Fixpoint demorgan1_sub_ptree
  (P : ptree) (E F : formula) (S : subst_ind) : ptree :=
match subst_ind_fit (ptree_formula P) S with
| false => P
| true => demorgan1_sub_ptree_fit P E F S
end.


(* First, we must prove that demorgan1_sub_ptree simply changes the base formula
of an ptree the way we expect with demorgan1_sub_formula *)
(* *)
Lemma demorgan1_ptree_formula_aux' :
  forall (P : ptree) (E F : formula) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
    demorgan1_sub_ptree P E F S = P.
Proof. intros. unfold demorgan1_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma demorgan1_ptree_formula_aux :
  forall (P : ptree) (E F : formula) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
      ptree_formula (demorgan1_sub_ptree P E F S) =
      demorgan1_sub_formula (ptree_formula P) E F S.
Proof.
intros. rewrite demorgan1_ptree_formula_aux'.
- unfold demorgan1_sub_formula. rewrite sub_fit_false. auto. apply H.
- apply H.
Qed.

Lemma demorgan1_ptree_formula_true :
  forall (P : ptree) (E F : formula) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    demorgan1_sub_ptree_fit P E F S = demorgan1_sub_ptree P E F S.
Proof. intros. unfold demorgan1_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma demorgan1_ptree_formula' : forall (P : ptree) (E F : formula),
  valid P ->
  forall (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    ptree_formula (demorgan1_sub_ptree P E F S) =
    demorgan1_sub_formula (ptree_formula P) E F S.
Proof.
intros P E F.
induction P; try intros H S Hs.

- simpl in Hs. simpl. rewrite Hs. simpl.
  rewrite (demorgan1_ptree_formula_true _ _ _ _ Hs).
  destruct H as [H1 H2]. apply (IHP H2). auto.

- simpl in Hs. simpl. rewrite Hs. simpl.
  rewrite (demorgan1_ptree_formula_true _ _ _ _ Hs).
  destruct H as [[H1 H2] H3]. apply (IHP H2). auto.

- simpl. inversion H.
  destruct (axiom_atomic _ H1); destruct H0; rewrite H0;
  unfold demorgan1_sub_formula; simpl; destruct S; auto.

- simpl.
  destruct S; inversion Hs; rewrite H1; simpl; unfold demorgan1_sub_formula.
  rewrite formula_sub_ind_lor; auto.

- simpl.
  destruct S; try destruct S1; inversion Hs; rewrite H1;
  simpl; unfold demorgan1_sub_formula.
  rewrite formula_sub_ind_lor, formula_sub_ind_lor; auto.
  apply (and_bool_prop _ _ H1).

- simpl.
  destruct S; try destruct S1; inversion Hs; rewrite H1;
  simpl; unfold demorgan1_sub_formula.
  rewrite formula_sub_ind_lor, formula_sub_ind_lor; auto.
  apply (and_bool_prop _ _ H1).

- simpl. destruct S; simpl.
  + unfold demorgan1_sub_formula. auto.
  + unfold demorgan1_sub_formula. auto.
  + destruct S1; try destruct S1_1; inversion Hs.
    rewrite H1. simpl. unfold demorgan1_sub_formula.
    destruct (and_bool_prop _ _ H1). destruct (and_bool_prop _ _ H0).
    repeat rewrite formula_sub_ind_lor; auto.

- simpl. inversion Hs. rewrite H1. auto.

- simpl. destruct S; inversion Hs.
  rewrite H1. simpl. unfold demorgan1_sub_formula.
  rewrite formula_sub_ind_lor. auto. apply H1.

- simpl. destruct S; auto. inversion Hs. rewrite H1. simpl.
  unfold demorgan1_sub_formula. rewrite formula_sub_ind_lor. auto. apply H1.

- simpl. destruct S; auto; destruct (eq_f f E) eqn:HE.
  + destruct (eq_f f0 F) eqn:HF; simpl;
    unfold demorgan1_sub_formula; rewrite formula_sub_ind_0; auto.
  + simpl. unfold demorgan1_sub_formula. rewrite formula_sub_ind_0. auto.
  + destruct (eq_f f0 F) eqn:HF.
    * inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
      clear IHP1. clear IHP2.
      case (eq_nat n (Init.Nat.max n n0)) eqn:Hn;
      simpl; rewrite H1; unfold demorgan1_sub_formula; simpl; rewrite HE,HF;
      simpl; rewrite (f_eq_decid _ _ HE); auto.
    * simpl. unfold demorgan1_sub_formula. simpl. rewrite HE,HF. auto.
  + simpl. unfold demorgan1_sub_formula. simpl. rewrite HE. auto.

- simpl. destruct S; auto.
  destruct S1; auto.
  + destruct (eq_f f E) eqn:HE; destruct (eq_f f0 F) eqn:HF;
    destruct (subst_ind_fit f1 S2) eqn:HS2; simpl; unfold demorgan1_sub_formula;
    simpl; rewrite HE,HF,HS2; auto; rewrite sub_fit_true; auto.
  + destruct (eq_f f E) eqn:HE.
    * destruct (eq_f f0 F) eqn:HF.
      { destruct (subst_ind_fit f1 S2) eqn:HS2.
        { clear IHP2. simpl.
          inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
          rewrite demorgan1_ptree_formula_true; auto.
          { case (eq_nat n (Init.Nat.max n n0)) eqn:Hn;
            simpl; rewrite IHP1; auto; rewrite H1; auto;
            unfold demorgan1_sub_formula; simpl; rewrite HE,HF,HS2;
            destruct (eq_f f (lor E F)); rewrite (f_eq_decid _ _ HE); auto. }
          { rewrite H1. auto. } }
        { simpl. unfold demorgan1_sub_formula. simpl. rewrite HE,HF,HS2. auto. } }
      { destruct (subst_ind_fit f1 S2) eqn:HS2; simpl;
        unfold demorgan1_sub_formula; simpl; rewrite HE,HF,HS2; auto;
        rewrite sub_fit_true; auto. }
    * destruct (eq_f f0 F) eqn:HF; destruct (subst_ind_fit f1 S2) eqn:HS2; simpl;
        unfold demorgan1_sub_formula; simpl; rewrite HE,HF,HS2; auto;
        rewrite sub_fit_true; auto.

- simpl. destruct S; auto.

- simpl. destruct S; auto. destruct S1; auto;
  destruct (subst_ind_fit f0 S2) eqn:HS2; simpl; unfold demorgan1_sub_formula;
  simpl; rewrite HS2; auto; rewrite sub_fit_true; auto.

- simpl. destruct S; simpl; unfold demorgan1_sub_formula; auto.

- simpl. destruct S.
  + simpl. unfold demorgan1_sub_formula. simpl. auto.
  + simpl. unfold demorgan1_sub_formula. simpl. auto.
  + destruct S1; inversion Hs; rewrite H1; simpl; unfold demorgan1_sub_formula.
    * rewrite formula_sub_ind_lor; auto.
    * simpl. rewrite H1. rewrite sub_fit_true; auto.

- intros. simpl. destruct S; simpl; unfold demorgan1_sub_formula; auto.

- intros. simpl. destruct S; try destruct S1; inversion H0;
  rewrite H2; unfold demorgan1_sub_formula; rewrite formula_sub_ind_lor; auto.

- simpl. inversion Hs. rewrite H1. auto.

- simpl. inversion Hs. rewrite H1. auto.

- simpl. destruct S; inversion Hs.
  rewrite H1. simpl. unfold demorgan1_sub_formula.
  rewrite formula_sub_ind_lor; auto.
Qed.


Lemma demorgan1_ptree_formula : forall (P : ptree) (E F : formula),
  valid P ->
  forall (S : subst_ind),
    ptree_formula (demorgan1_sub_ptree P E F S) =
    demorgan1_sub_formula (ptree_formula P) E F S.
Proof.
intros. destruct (subst_ind_fit (ptree_formula P) S) eqn:Hs.
- apply demorgan1_ptree_formula'. apply X. apply Hs.
- apply demorgan1_ptree_formula_aux. apply Hs.
Qed.





(* Second, we must prove that demorgan1_sub_ptree does not change the degree
of an ptree. *)
(* *)
Lemma demorgan1_ptree_deg : forall (P : ptree) (E F : formula),
  valid P ->
  forall (S : subst_ind), ptree_deg (demorgan1_sub_ptree P E F S) = ptree_deg P.
Proof.
intros P E F H. induction P; intros S.
- simpl. case (subst_ind_fit (ptree_formula P) S); auto.
- simpl. case (subst_ind_fit (ptree_formula P) S) eqn:Hfit; auto. simpl.
  rewrite (demorgan1_ptree_formula_true _ _ _ _ Hfit).
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
  + case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
  + inversion H as [[[[[H1 H2] H3] H4] H5] H6].
    case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
    case (eq_nat n (Init.Nat.max n n0)) eqn:Hn;
    simpl; auto; rewrite <- (nat_eq_decid _ _ Hn); auto.
- simpl. destruct S; auto.
  destruct S1; auto; destruct (subst_ind_fit f1 S2) eqn:HS2; auto; simpl.
  + case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
  + inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
    case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
    case (eq_nat n (Init.Nat.max n n0)) eqn:Hn;
    simpl; auto; rewrite <- (nat_eq_decid _ _ Hn); auto;
    rewrite demorgan1_ptree_formula_true;
    try rewrite IHP1; auto; rewrite H1; simpl; auto.
- simpl. destruct S; auto.
- simpl. destruct S; auto.
  destruct S1; auto; destruct (subst_ind_fit f0 S2); auto.
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



Lemma demorgan1_ptree_ord : forall (P : ptree) (E F : formula),
  valid P ->
  forall (S : subst_ind), ptree_ord (demorgan1_sub_ptree P E F S) = ptree_ord P.
Proof.
intros P E F H. induction P; intros S.
- simpl. case (subst_ind_fit (ptree_formula P) S) eqn:Hfit; auto. simpl.
  rewrite (demorgan1_ptree_formula_true _ _ _ _ Hfit).
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
  + case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
  + inversion H as [[[[[H1 H2] H3] H4] H5] H6].
    case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
    case (eq_nat n (Init.Nat.max n n0)) eqn:Hn;
    case (ord_eqb o (ord_succ (ord_max o o0))) eqn:Ho; simpl; auto;
    rewrite <- (ord_eqb_eq _ _ Ho); auto.
- simpl. destruct S; auto.
  destruct S1; auto; destruct (subst_ind_fit f1 S2) eqn:HS2; auto; simpl.
  + case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
  + inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
    case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
    case (eq_nat n (Init.Nat.max n n0)) eqn:Hn;
    simpl; auto.
- simpl. destruct S; auto.
- simpl. destruct S; auto.
  destruct S1; auto; destruct (subst_ind_fit f0 S2); auto.
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
double negation substitution on it results in a valid ptree *)
(* *)
Lemma demorgan1_valid : forall (P : ptree) (E F : formula),
  valid P ->
  forall (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    valid (demorgan1_sub_ptree P E F S).
Proof.
intros P E F. induction P; try intros H S Hs.

- simpl. inversion H as [H1 H2]. inversion Hs. rewrite H3.
  rewrite demorgan1_ptree_formula_true; auto. split.
  + rewrite demorgan1_ptree_deg; auto.
  + apply (IHP H2 S H3).

- simpl. inversion H as [[H1 H2] H3]. inversion Hs. rewrite H4.
  rewrite demorgan1_ptree_formula_true; auto. split.
  + rewrite demorgan1_ptree_ord; auto.
  + auto.

- simpl. destruct (subst_ind_fit f S); apply H.

- simpl. destruct S; inversion Hs. rewrite H1. simpl.
  inversion H as [[[H2 H3] H4] H5].
  repeat split; rewrite demorgan1_ptree_formula_true.
  + rewrite demorgan1_ptree_formula; auto.
    rewrite H2. unfold demorgan1_sub_formula.
    rewrite formula_sub_ind_lor; auto. apply (and_bool_symm _ _ H1).
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + apply IHP. apply H. rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + rewrite demorgan1_ptree_deg; auto.
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + rewrite demorgan1_ptree_ord; auto.
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).

- simpl. destruct S; try destruct S1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H4 H5] H6] H7].
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  repeat split; rewrite demorgan1_ptree_formula_true.
  + rewrite demorgan1_ptree_formula; auto.
    rewrite H4. unfold demorgan1_sub_formula.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H1, H2. auto.
    * simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + apply IHP; auto. rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite demorgan1_ptree_deg; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite demorgan1_ptree_ord; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.

- simpl. destruct S; try destruct S1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H4 H5] H6] H7].
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  repeat split; rewrite demorgan1_ptree_formula_true.
  + rewrite demorgan1_ptree_formula; auto.
    rewrite H4. unfold demorgan1_sub_formula.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H1, H3. auto.
    * simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + apply IHP; auto. rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite demorgan1_ptree_deg; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite demorgan1_ptree_ord; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.

- simpl. destruct S; try destruct S1; try destruct S1_1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H5 H6] H7] H8].
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  destruct (and_bool_prop _ _ H1). clear H1.
  repeat split; rewrite demorgan1_ptree_formula_true.
  + rewrite demorgan1_ptree_formula; auto.
    rewrite H5. unfold demorgan1_sub_formula.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H0,H3. auto.
    * simpl. rewrite H0, H3, H4. auto.
    * simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + apply IHP; auto. rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite demorgan1_ptree_deg; auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite demorgan1_ptree_ord; auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.

- simpl. inversion Hs. rewrite H1. inversion H as [[[H2 H3] H4] H5].
  repeat split; rewrite demorgan1_ptree_formula_true.
  + rewrite demorgan1_ptree_formula; auto.
    unfold demorgan1_sub_formula. rewrite H2.
    rewrite formula_sub_ind_lor; auto. rewrite H1. auto.
  + rewrite H2. simpl. rewrite H1. auto.
  + apply IHP. apply H. rewrite H2. simpl. rewrite H1. auto.
  + rewrite H2. simpl. rewrite H1. auto.
  + rewrite demorgan1_ptree_deg; auto.
  + rewrite H2. simpl. rewrite H1. auto.
  + rewrite demorgan1_ptree_ord; auto.
  + rewrite H2. simpl. rewrite H1. auto.

- simpl. destruct S; inversion Hs. rewrite H1.
  inversion H as [[[H2 H3] H4] H5]. destruct (and_bool_prop _ _ H1).
  repeat split; rewrite demorgan1_ptree_formula_true.
  + rewrite demorgan1_ptree_formula; auto.
    unfold demorgan1_sub_formula. rewrite H2.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H0. auto.
    * simpl. rewrite H0, H6. auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + apply IHP. apply H. rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite demorgan1_ptree_deg; auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite demorgan1_ptree_ord; auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.

- simpl. destruct S; inversion Hs. rewrite H1. simpl.
  inversion H as [[[[H2 H3] H4] H5] H6]. destruct (and_bool_prop _ _ H1).
  repeat split.
  + rewrite demorgan1_ptree_formula_true.
    * rewrite demorgan1_ptree_formula; auto. rewrite H2. auto.
    * rewrite H2. auto.
  + apply demorgan1_sub_formula_closed. auto.
  + rewrite demorgan1_ptree_formula_true.
    * apply IHP; auto. rewrite H2. auto.
    * rewrite H2. auto.
  + rewrite demorgan1_ptree_formula_true.
    * rewrite demorgan1_ptree_deg; auto.
    * rewrite H2. auto.
  + rewrite demorgan1_ptree_formula_true.
    * rewrite demorgan1_ptree_ord; auto.
    * rewrite H2. auto.

- simpl. inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  destruct S; auto; destruct (eq_f f E); destruct (eq_f f0 F);
  simpl; repeat split; auto.
  case (eq_nat n (Init.Nat.max n n0)) eqn:Hn;
  simpl; repeat split; auto.
  + rewrite <- H7. apply ord_max_succ_l.
  + apply ord_succ_nf. apply ord_max_nf.
    * rewrite H7. apply ptree_ord_nf. auto.
    * rewrite H8. apply ptree_ord_nf. auto.
  + rewrite <- H5. apply max_lem1. auto.
  + rewrite <- H7. apply ord_max_succ_l.
  + apply ord_succ_nf. apply ord_max_nf.
    * rewrite H7. apply ptree_ord_nf. auto.
    * rewrite H8. apply ptree_ord_nf. auto.
  
- simpl. inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  destruct S; auto.
  destruct S1; auto; destruct (subst_ind_fit f1 S2) eqn:HS2; simpl.
  + destruct (eq_f f E) eqn:HE; destruct (eq_f f0 F) eqn:HF;
    simpl; repeat split; auto; rewrite demorgan1_ptree_formula_true;
    try rewrite demorgan1_ptree_deg; try rewrite demorgan1_ptree_ord;
    try rewrite demorgan1_ptree_formula;
    try apply IHP1; try apply IHP2; try rewrite H1; try rewrite H3;
    auto; unfold demorgan1_sub_formula; simpl; try rewrite HS2;
    try destruct (eq_f f0 (lor E F)); try destruct (eq_f f (lor E F));
    try rewrite sub_fit_true; auto;
    case (eq_nat n (Init.Nat.max n n0)) eqn:Hn;
    simpl; repeat split; auto;
    try apply IHP1; auto; try rewrite H1; auto;
    try rewrite demorgan1_ptree_ord; auto;
    try rewrite <- H7; try apply ord_max_lt1; auto;
    try rewrite demorgan1_ptree_deg; auto; try rewrite <- H5; try apply max_lem1; auto;
    try apply ord_max_nf; try rewrite H7; try rewrite H8; try apply ptree_ord_nf; auto.
  + repeat split; auto.
  + destruct (eq_f f E) eqn:HE; destruct (eq_f f0 F) eqn:HF;
    simpl; repeat split; auto; rewrite demorgan1_ptree_formula_true;
    try rewrite demorgan1_ptree_deg; try rewrite demorgan1_ptree_ord;
    try rewrite demorgan1_ptree_formula;
    try apply IHP1; try apply IHP2; try rewrite H1; try rewrite H3;
    auto; unfold demorgan1_sub_formula; simpl; try rewrite HS2;
    try destruct (eq_f f0 (lor E F)); try destruct (eq_f f (lor E F));
    try rewrite sub_fit_true; auto;
    case (eq_nat n (Init.Nat.max n n0)) eqn:Hn;
    simpl; repeat split; auto;
    try apply IHP1; auto; try rewrite H1; auto;
    try rewrite demorgan1_ptree_ord; auto;
    try rewrite <- H7; try apply ord_max_lt1; try apply ord_max_succ_l; auto;
    try rewrite demorgan1_ptree_deg; auto; try rewrite <- H5; try apply max_lem1; auto;
    try apply ord_succ_nf; try apply ord_max_nf; try rewrite H7; try rewrite H8; try apply ptree_ord_nf; auto.
  + repeat split; auto.

- simpl. destruct S; auto.

- simpl. inversion H as [[[H1 H2] H3] H4]. destruct S; auto.
  destruct S1; auto; destruct (subst_ind_fit f0 S2) eqn:HS2; simpl;
  repeat split; auto; rewrite demorgan1_ptree_formula_true;
  try apply IHP; auto; try rewrite H1; simpl; try rewrite non_target_fit,HS2;
  try rewrite demorgan1_ptree_deg; try rewrite demorgan1_ptree_ord; auto.
  + rewrite demorgan1_ptree_formula; auto. rewrite H1.
    unfold demorgan1_sub_formula. simpl. rewrite non_target_fit,HS2.
    simpl. rewrite <- sub_fit_true; auto.
    * rewrite non_target_sub. rewrite <- sub_fit_true; auto.
    * apply non_target_fit.
  + rewrite demorgan1_ptree_formula; auto. rewrite H1.
    unfold demorgan1_sub_formula. simpl. rewrite non_target_fit,HS2.
    simpl. rewrite <- sub_fit_true; auto.
    * rewrite non_target_sub. rewrite <- sub_fit_true; auto.
    * apply non_target_fit.

- simpl. destruct S; apply H.

- simpl. destruct S; try apply H. inversion H as [[[[H0 H1] H2] H3] H4].
  destruct S1; inversion Hs; rewrite H6; simpl.
  + repeat split; auto.
    * rewrite demorgan1_ptree_formula_true, demorgan1_ptree_formula; auto.
      { rewrite H0. unfold demorgan1_sub_formula.
        { rewrite formula_sub_ind_lor. simpl.
          { destruct (eq_f (substitution f n t)); auto. }
          { simpl. apply H6. } } }
      { rewrite H0. simpl. apply H6. }
    * rewrite demorgan1_ptree_formula_true.
      { apply IHP; auto. rewrite H0. simpl. apply H6. }
      { rewrite H0. simpl. apply H6. }
    * rewrite demorgan1_ptree_formula_true.
      { rewrite demorgan1_ptree_deg; auto. }
      { rewrite H0. simpl. auto. }
    * rewrite demorgan1_ptree_formula_true.
      { rewrite demorgan1_ptree_ord; auto. }
      { rewrite H0. simpl. auto. }
  + repeat split; auto.
    * rewrite demorgan1_ptree_formula_true, demorgan1_ptree_formula; auto.
      { rewrite H0. unfold demorgan1_sub_formula.
        { rewrite formula_sub_ind_lor. simpl.
          { destruct (eq_f (substitution f n t)); auto. }
          { simpl. apply H6. } } }
      { rewrite H0. simpl. apply H6. }
    * rewrite demorgan1_ptree_formula_true.
      { apply IHP; auto. rewrite H0. simpl. apply H6. }
      { rewrite H0. simpl. apply H6. }
    * rewrite demorgan1_ptree_formula_true.
      { rewrite demorgan1_ptree_deg; auto. }
      { rewrite H0. simpl. auto. }
    * rewrite demorgan1_ptree_formula_true.
      { rewrite demorgan1_ptree_ord; auto. }
      { rewrite H0. simpl. auto. }

- intros. simpl. destruct S; apply H.

- rename H into H0. rename X into H. rename Hs into H1.
  simpl. destruct S; try apply H0. destruct S1; inversion H1.
  + rewrite H3. simpl. intros. destruct (valid_w_rule_ad _ _ _ _ _ _ H0 m) as [[[H4 H5] H6] H7].
    repeat split.
    * rewrite demorgan1_ptree_formula_true, demorgan1_ptree_formula; auto.
      { rewrite H4. unfold demorgan1_sub_formula. rewrite formula_sub_ind_lor.
        { rewrite (non_target_term_sub f n (represent m)).
          rewrite non_target_sub. auto. }
        { rewrite (non_target_term_sub f n (represent m)).
          rewrite non_target_fit. apply H3. } }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
    * rewrite demorgan1_ptree_formula_true.
      { apply H. apply H5. rewrite H4. simpl.
        rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
    * rewrite demorgan1_ptree_formula_true.
      { rewrite demorgan1_ptree_deg; auto. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. rewrite H3. auto. }
    * rewrite demorgan1_ptree_formula_true.
      { rewrite demorgan1_ptree_ord; auto. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. rewrite H3. auto. }
  + rewrite H3. simpl. intros. destruct (valid_w_rule_ad _ _ _ _ _ _ H0 m) as [[[H4 H5] H6] H7].
    repeat split.
    * rewrite demorgan1_ptree_formula_true, demorgan1_ptree_formula; auto.
      { rewrite H4. unfold demorgan1_sub_formula. rewrite formula_sub_ind_lor.
        { rewrite (non_target_term_sub f n (represent m)).
          rewrite non_target_sub. auto. }
        { rewrite (non_target_term_sub f n (represent m)).
          rewrite non_target_fit. apply H3. } }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
    * rewrite demorgan1_ptree_formula_true.
      { apply H. apply H5. rewrite H4. simpl.
        rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
    * rewrite demorgan1_ptree_formula_true.
      { rewrite demorgan1_ptree_deg; auto. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. rewrite H3. auto. }
    * rewrite demorgan1_ptree_formula_true.
      { rewrite demorgan1_ptree_ord; auto. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. rewrite H3. auto. }
  - clear IHP2. simpl. destruct (subst_ind_fit f S) eqn:Heq; try apply H. simpl.
    inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
    repeat split; auto; rewrite demorgan1_ptree_formula_true.
    + rewrite demorgan1_ptree_formula; auto.
      rewrite H1. unfold demorgan1_sub_formula. rewrite formula_sub_ind_lor.
      * rewrite non_target_sub. auto.
      * rewrite Heq, non_target_fit. auto.
    + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
    + apply IHP1; auto. rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
    + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
    + rewrite demorgan1_ptree_deg; auto.
    + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
    + rewrite demorgan1_ptree_ord; auto.
    + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.

- clear IHP1. simpl. destruct (subst_ind_fit f0 S) eqn:Heq; try apply H. simpl.
  inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  repeat split; auto; rewrite demorgan1_ptree_formula_true.
  + rewrite demorgan1_ptree_formula; auto.
    rewrite H3. unfold demorgan1_sub_formula. rewrite formula_sub_ind_lor.
    * rewrite non_target_sub. auto.
    * rewrite Heq, non_target_fit. auto.
  + rewrite H3. simpl. auto.
  + apply IHP2; auto. rewrite H3. simpl. auto.
  + rewrite H3. simpl. auto.
  + rewrite demorgan1_ptree_deg; auto.
  + rewrite H3. simpl. auto.
  + rewrite demorgan1_ptree_ord; auto.
  + rewrite H3. simpl. auto.

- simpl. inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  destruct S; try inversion Hs. rewrite H9.
  destruct (and_bool_prop _ _ H9) as [H10 H11].
  simpl. repeat split; rewrite demorgan1_ptree_formula_true.
  + rewrite demorgan1_ptree_formula; auto.
    rewrite H1. unfold demorgan1_sub_formula. rewrite formula_sub_ind_lor.
    * rewrite non_target_sub. auto.
    * rewrite H10, non_target_fit. auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + apply IHP1; auto. rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite demorgan1_ptree_formula; auto.
    rewrite H3. unfold demorgan1_sub_formula. rewrite formula_sub_ind_lor.
    * rewrite non_target_sub. auto.
    * rewrite H11, non_target_fit. auto.
  + rewrite H3. simpl. auto.
  + apply IHP2; auto. rewrite H3. simpl. auto.
  + rewrite H3. simpl. auto.
  + rewrite demorgan1_ptree_deg; auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite demorgan1_ptree_deg; auto.
  + rewrite H3. simpl. auto.
  + rewrite demorgan1_ptree_ord; auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite demorgan1_ptree_ord; auto.
  + rewrite H3. simpl. auto.
Qed.



(* We finally show that if the formulas ~~A and/or ~~A \/ D are provable,
so are the formulas A and/or A \/ D *)
(* *)
Lemma demorgan1_invertible_a :
  forall (A B : formula) (d : nat) (alpha : ord),
  provable (neg (lor A B)) d alpha -> provable (neg A) d alpha.
Proof.
unfold provable. intros A B d alpha H. destruct H as [t [[[Ht1 Ht2] Ht3] Ht4]].
exists (demorgan1_sub_ptree t A B (1)). unfold P_proves. repeat split.
- rewrite demorgan1_ptree_formula; auto. rewrite Ht1.
  unfold demorgan1_sub_formula. simpl. repeat rewrite eq_f_refl. auto.
- apply demorgan1_valid; auto. rewrite Ht1. auto.
- rewrite demorgan1_ptree_deg; auto.
- rewrite demorgan1_ptree_ord; auto.
Qed.

Lemma demorgan1_invertible_ad :
  forall (A B D : formula) (d : nat) (alpha : ord),
  provable (lor (neg (lor A B)) D) d alpha -> provable (lor (neg A) D) d alpha.
Proof.
unfold provable. intros A B D d alpha H. destruct H as [t [[[Ht1 Ht2] Ht3] Ht4]].
exists (demorgan1_sub_ptree t A B (lor_ind (1) (non_target D))).
unfold P_proves. repeat split.
- rewrite demorgan1_ptree_formula; auto. rewrite Ht1.
  unfold demorgan1_sub_formula. simpl. rewrite non_target_fit.
  repeat rewrite eq_f_refl. simpl. rewrite <- sub_fit_true.
  + rewrite non_target_sub. auto.
  + apply non_target_fit.
- apply demorgan1_valid; auto. rewrite Ht1. simpl. apply non_target_fit.
- rewrite demorgan1_ptree_deg; auto.
- rewrite demorgan1_ptree_ord; auto.
Qed.















(*
###############################################################################
Section 9.3: Here we show invertibility of DeMorgan (the second half),
i.e. from a proof of ~(E \/ F) \/ D we can get a proof of ~F \/ D.
###############################################################################
*)
(* Defining DeMorgan substitution in an ptree. First, we replace ~(E \/ F)
with ~F at certain places in a formula (given a substitution indicator).
Applying this operation to an entire ptree, we change the substitution
indicator as the structure of the formula(s) change as we move up the ptree. *)
(* *)
Definition demorgan2_sub_formula (A E F : formula) (S : subst_ind) : formula :=
  formula_sub_ind A (neg (lor E F)) (neg F) S.

Lemma demorgan2_sub_formula_closed : forall (A : formula),
  closed A = true ->
  forall (E F : formula) (S : subst_ind),
    closed (demorgan2_sub_formula A E F S) = true.
Proof.
intros. unfold demorgan2_sub_formula. apply formula_sub_ind_closed; auto.
simpl. intros. destruct (and_bool_prop _ _ H0). auto.
Qed.

Fixpoint demorgan2_sub_ptree_fit
  (P : ptree) (E F : formula) (S : subst_ind) : ptree :=
match P, S with
| deg_up d P', _ => deg_up d (demorgan2_sub_ptree_fit P' E F S)

| ord_up alpha P', _ => ord_up alpha (demorgan2_sub_ptree_fit P' E F S)

| node A, _ => P

| exchange_ab A B d alpha P', lor_ind S_B S_A =>
    exchange_ab
      (demorgan2_sub_formula A E F S_A)
      (demorgan2_sub_formula B E F S_B)
      d alpha
      (demorgan2_sub_ptree_fit P' E F (lor_ind S_A S_B))

| exchange_cab C A B d alpha P', lor_ind (lor_ind S_C S_B) S_A =>
    exchange_cab
      (demorgan2_sub_formula C E F S_C)
      (demorgan2_sub_formula A E F S_A)
      (demorgan2_sub_formula B E F S_B)
      d alpha
      (demorgan2_sub_ptree_fit P' E F (lor_ind (lor_ind S_C S_A) S_B))

| exchange_abd A B D d alpha P', lor_ind (lor_ind S_B S_A) S_D =>
    exchange_abd
      (demorgan2_sub_formula A E F S_A)
      (demorgan2_sub_formula B E F S_B)
      (demorgan2_sub_formula D E F S_D)
      d alpha
      (demorgan2_sub_ptree_fit P' E F (lor_ind (lor_ind S_A S_B) S_D))

| exchange_cabd C A B D d alpha P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D =>
    exchange_cabd
      (demorgan2_sub_formula C E F S_C)
      (demorgan2_sub_formula A E F S_A)
      (demorgan2_sub_formula B E F S_B)
      (demorgan2_sub_formula D E F S_D)
      d alpha
      (demorgan2_sub_ptree_fit P' E F (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D))

| contraction_a A d alpha P', _ =>
    contraction_a
      (demorgan2_sub_formula A E F S)
      d alpha
      (demorgan2_sub_ptree_fit P' E F (lor_ind S S))

| contraction_ad A D d alpha P', lor_ind S_A S_D =>
    contraction_ad
      (demorgan2_sub_formula A E F S_A)
      (demorgan2_sub_formula D E F S_D)
      d alpha
      (demorgan2_sub_ptree_fit P' E F (lor_ind (lor_ind S_A S_A) S_D))

| weakening_ad A D d alpha P', lor_ind S_A S_D =>
    weakening_ad
      (demorgan2_sub_formula A E F S_A)
      (demorgan2_sub_formula D E F S_D)
      d alpha
      (demorgan2_sub_ptree_fit P' E F S_D)

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, _ =>
    (match eq_f A E, eq_f B F, S with
    | true, true, (1) =>
      (match eq_nat d2 (ptree_deg P) with
      | true => ord_up (ptree_ord P) P2
      | false => deg_up (ptree_deg P) (ord_up (ptree_ord P) P2)
      end)
    | _, _, _ => P
    end)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_AB S_D =>
    (match eq_f A E, eq_f B F, S_AB with
    | true, true, (1) =>
      (match eq_nat d2 (ptree_deg P) with
      | true =>
          ord_up
            (ptree_ord P)
            (demorgan2_sub_ptree_fit P2 E F (lor_ind (non_target (neg A)) S_D))
      | false =>
          deg_up
            (ptree_deg P)
              (ord_up
                (ptree_ord P)
                (demorgan2_sub_ptree_fit
                  P2 E F
                  (lor_ind (non_target (neg A)) S_D)))
      end)
    | _, _, _ =>
        demorgan_abd
          A B
          (demorgan2_sub_formula D E F S_D)
          d1 d2 alpha1 alpha2
          (demorgan2_sub_ptree_fit P1 E F (lor_ind (non_target (neg A)) S_D))
          (demorgan2_sub_ptree_fit P2 E F (lor_ind (non_target (neg B)) S_D))
    end)

| negation_a A d alpha P', _ => P

| negation_ad A D d alpha P', lor_ind S_A S_D =>
    negation_ad
      A
      (demorgan2_sub_formula D E F S_D)
      d alpha
      (demorgan2_sub_ptree_fit P' E F (lor_ind (non_target A) S_D))

| quantification_a A n t d alpha P', _ => P

| quantification_ad A D n t d alpha P', lor_ind S_A S_D =>
    quantification_ad
      A
      (demorgan2_sub_formula D E F S_D)
      n t d alpha
      (demorgan2_sub_ptree_fit P' E F (lor_ind (0) S_D))

| w_rule_a A n d alpha g, _ => P

| w_rule_ad A D n d alpha g, lor_ind S_A S_D =>
    w_rule_ad
      A
      (demorgan2_sub_formula D E F S_D)
      n d alpha
      (fun (n : nat) =>
          demorgan2_sub_ptree_fit (g n) E F (lor_ind (non_target A) S_D))

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ca
      (demorgan2_sub_formula C E F S)
      A d1 d2 alpha1 alpha2
      (demorgan2_sub_ptree_fit P1 E F (lor_ind S (non_target A)))
      P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ad
      A
      (demorgan2_sub_formula D E F S)
      d1 d2 alpha1 alpha2
      P1
      (demorgan2_sub_ptree_fit P2 E F (lor_ind (0) S))

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_D =>
    cut_cad
      (demorgan2_sub_formula C E F S_C)
      A
      (demorgan2_sub_formula D E F S_D)
      d1 d2 alpha1 alpha2
      (demorgan2_sub_ptree_fit P1 E F (lor_ind S_C (non_target A)))
      (demorgan2_sub_ptree_fit P2 E F (lor_ind (0) S_D))

| _, _ => P
end.

Fixpoint demorgan2_sub_ptree
  (P : ptree) (E F : formula) (S : subst_ind) : ptree :=
match subst_ind_fit (ptree_formula P) S with
| false => P
| true => demorgan2_sub_ptree_fit P E F S
end.

(* First, we must prove that demorgan2_sub_ptree simply changes the base formula
of an ptree the way we expect with demorgan2_sub_formula *)
(* *)
Lemma demorgan2_ptree_formula_aux' :
  forall (P : ptree) (E F : formula) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
    demorgan2_sub_ptree P E F S = P.
Proof. intros. unfold demorgan2_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma demorgan2_ptree_formula_aux :
  forall (P : ptree) (E F : formula) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
      ptree_formula (demorgan2_sub_ptree P E F S) =
      demorgan2_sub_formula (ptree_formula P) E F S.
Proof.
intros. rewrite demorgan2_ptree_formula_aux'.
- unfold demorgan2_sub_formula. rewrite sub_fit_false. auto. apply H.
- apply H.
Qed.

Lemma demorgan2_ptree_formula_true :
  forall (P : ptree) (E F : formula) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    demorgan2_sub_ptree_fit P E F S = demorgan2_sub_ptree P E F S.
Proof. intros. unfold demorgan2_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma demorgan2_ptree_formula' : forall (P : ptree) (E F : formula),
  valid P ->
  forall (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    ptree_formula (demorgan2_sub_ptree P E F S) =
    demorgan2_sub_formula (ptree_formula P) E F S.
Proof.
intros P E F.
induction P; try intros H S Hs.

- simpl in Hs. simpl. rewrite Hs. simpl.
  rewrite (demorgan2_ptree_formula_true _ _ _ _ Hs).
  destruct H as [H1 H2]. apply (IHP H2). auto.

- simpl in Hs. simpl. rewrite Hs. simpl.
  rewrite (demorgan2_ptree_formula_true _ _ _ _ Hs).
  destruct H as [[H1 H2] H3]. apply (IHP H2). auto.

- simpl. inversion H.
  destruct (axiom_atomic _ H1); destruct H0; rewrite H0;
  unfold demorgan2_sub_formula; simpl; destruct S; auto.

- simpl.
  destruct S; inversion Hs; rewrite H1; simpl; unfold demorgan2_sub_formula.
  rewrite formula_sub_ind_lor; auto.

- simpl.
  destruct S; try destruct S1; inversion Hs; rewrite H1;
  simpl; unfold demorgan2_sub_formula.
  rewrite formula_sub_ind_lor, formula_sub_ind_lor; auto.
  apply (and_bool_prop _ _ H1).

- simpl.
  destruct S; try destruct S1; inversion Hs; rewrite H1;
  simpl; unfold demorgan2_sub_formula.
  rewrite formula_sub_ind_lor, formula_sub_ind_lor; auto.
  apply (and_bool_prop _ _ H1).

- simpl. destruct S; simpl.
  + unfold demorgan2_sub_formula. auto.
  + unfold demorgan2_sub_formula. auto.
  + destruct S1; try destruct S1_1; inversion Hs.
    rewrite H1. simpl. unfold demorgan2_sub_formula.
    destruct (and_bool_prop _ _ H1). destruct (and_bool_prop _ _ H0).
    repeat rewrite formula_sub_ind_lor; auto.

- simpl. inversion Hs. rewrite H1. auto.

- simpl. destruct S; inversion Hs.
  rewrite H1. simpl. unfold demorgan2_sub_formula.
  rewrite formula_sub_ind_lor. auto. apply H1.

- simpl. destruct S; auto. inversion Hs. rewrite H1. simpl.
  unfold demorgan2_sub_formula. rewrite formula_sub_ind_lor. auto. apply H1.

- simpl. destruct S; auto; destruct (eq_f f E) eqn:HE.
  + destruct (eq_f f0 F) eqn:HF; simpl;
    unfold demorgan2_sub_formula; rewrite formula_sub_ind_0; auto.
  + simpl. unfold demorgan2_sub_formula. rewrite formula_sub_ind_0. auto.
  + destruct (eq_f f0 F) eqn:HF.
    * inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
      clear IHP1. clear IHP2.
      case (eq_nat n0 (Init.Nat.max n n0)) eqn:Hn;
      simpl; rewrite H3; unfold demorgan2_sub_formula; simpl; rewrite HE,HF;
      simpl; rewrite (f_eq_decid _ _ HF); auto.
    * simpl. unfold demorgan2_sub_formula. simpl. rewrite HE,HF. auto.
  + simpl. unfold demorgan2_sub_formula. simpl. rewrite HE. auto.

- simpl. destruct S; auto.
  destruct S1; auto.
  + destruct (eq_f f E) eqn:HE; destruct (eq_f f0 F) eqn:HF;
    destruct (subst_ind_fit f1 S2) eqn:HS2; simpl; unfold demorgan2_sub_formula;
    simpl; rewrite HE,HF,HS2; auto; rewrite sub_fit_true; auto.
  + destruct (eq_f f E) eqn:HE.
    * destruct (eq_f f0 F) eqn:HF.
      { destruct (subst_ind_fit f1 S2) eqn:HS2.
        { clear IHP1. simpl.
          inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
          rewrite demorgan2_ptree_formula_true; auto.
          { case (eq_nat n0 (Init.Nat.max n n0)) eqn:Hn0;
            simpl; rewrite IHP2; auto; rewrite H3; auto;
            unfold demorgan2_sub_formula; simpl; rewrite HE,HF,HS2;
            destruct (eq_f f0 (lor E F)); rewrite (f_eq_decid _ _ HF); auto. }
          { rewrite H3. auto. } }
        { simpl. unfold demorgan2_sub_formula. simpl. rewrite HE,HF,HS2. auto. } }
      { destruct (subst_ind_fit f1 S2) eqn:HS2; simpl;
        unfold demorgan2_sub_formula; simpl; rewrite HE,HF,HS2; auto;
        rewrite sub_fit_true; auto. }
    * destruct (eq_f f0 F) eqn:HF; destruct (subst_ind_fit f1 S2) eqn:HS2; simpl;
        unfold demorgan2_sub_formula; simpl; rewrite HE,HF,HS2; auto;
        rewrite sub_fit_true; auto.

- simpl. destruct S; auto.

- simpl. destruct S; auto. destruct S1; auto;
  destruct (subst_ind_fit f0 S2) eqn:HS2; simpl; unfold demorgan2_sub_formula;
  simpl; rewrite HS2; auto; rewrite sub_fit_true; auto.

- simpl. destruct S; simpl; unfold demorgan2_sub_formula; auto.

- simpl. destruct S.
  + simpl. unfold demorgan2_sub_formula. simpl. auto.
  + simpl. unfold demorgan2_sub_formula. simpl. auto.
  + destruct S1; inversion Hs; rewrite H1; simpl; unfold demorgan2_sub_formula.
    * rewrite formula_sub_ind_lor; auto.
    * simpl. rewrite H1. rewrite sub_fit_true; auto.

- intros. simpl. destruct S; simpl; unfold demorgan2_sub_formula; auto.

- intros. simpl. destruct S; try destruct S1; inversion H0;
  rewrite H2; unfold demorgan2_sub_formula; rewrite formula_sub_ind_lor; auto.

- simpl. inversion Hs. rewrite H1. auto.

- simpl. inversion Hs. rewrite H1. auto.

- simpl. destruct S; inversion Hs.
  rewrite H1. simpl. unfold demorgan2_sub_formula.
  rewrite formula_sub_ind_lor; auto.
Qed.


Lemma demorgan2_ptree_formula : forall (P : ptree) (E F : formula),
  valid P ->
  forall (S : subst_ind),
    ptree_formula (demorgan2_sub_ptree P E F S) =
    demorgan2_sub_formula (ptree_formula P) E F S.
Proof.
intros. destruct (subst_ind_fit (ptree_formula P) S) eqn:Hs.
- apply demorgan2_ptree_formula'. apply X. apply Hs.
- apply demorgan2_ptree_formula_aux. apply Hs.
Qed.





(* Second, we must prove that demorgan2_sub_ptree does not change the degree
of an ptree. *)
(* *)
Lemma demorgan2_ptree_deg : forall (P : ptree) (E F : formula),
  valid P ->
  forall (S : subst_ind), ptree_deg (demorgan2_sub_ptree P E F S) = ptree_deg P.
Proof.
intros P E F H. induction P; intros S.
- simpl. case (subst_ind_fit (ptree_formula P) S); auto.
- simpl. case (subst_ind_fit (ptree_formula P) S) eqn:Hfit; auto. simpl.
  rewrite (demorgan2_ptree_formula_true _ _ _ _ Hfit).
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
  + case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
  + inversion H as [[[[[H1 H2] H3] H4] H5] H6].
    case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
    case (eq_nat n0 (Init.Nat.max n n0)) eqn:Hn0;
    simpl; auto; rewrite <- (nat_eq_decid _ _ Hn0); auto.
- simpl. destruct S; auto.
  destruct S1; auto; destruct (subst_ind_fit f1 S2) eqn:HS2; auto; simpl.
  + case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
  + inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
    case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
    case (eq_nat n0 (Init.Nat.max n n0)) eqn:Hn0;
    simpl; auto; rewrite <- (nat_eq_decid _ _ Hn0); auto;
    rewrite demorgan2_ptree_formula_true;
    try rewrite IHP2; auto; rewrite H3; simpl; auto.
- simpl. destruct S; auto.
- simpl. destruct S; auto.
  destruct S1; auto; destruct (subst_ind_fit f0 S2); auto.
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



Lemma demorgan2_ptree_ord : forall (P : ptree) (E F : formula),
  valid P ->
  forall (S : subst_ind), ptree_ord (demorgan2_sub_ptree P E F S) = ptree_ord P.
Proof.
intros P E F H. induction P; intros S.
- simpl. case (subst_ind_fit (ptree_formula P) S) eqn:Hfit; auto. simpl.
  rewrite (demorgan2_ptree_formula_true _ _ _ _ Hfit).
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
  + case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
  + inversion H as [[[[[H1 H2] H3] H4] H5] H6].
    case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
    case (eq_nat n0 (Init.Nat.max n n0)) eqn:Hn0;
    simpl; auto; rewrite <- (ord_eqb_eq _ _ Ho0); auto.
- simpl. destruct S; auto.
  destruct S1; auto; destruct (subst_ind_fit f1 S2) eqn:HS2; auto; simpl.
  + case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
  + inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
    case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
    case (eq_nat n0 (Init.Nat.max n n0)) eqn:Hn0;
    simpl; auto; rewrite <- (ord_eqb_eq _ _ Ho0); auto;
    rewrite demorgan2_ptree_formula_true;
    try rewrite IHP2; auto; rewrite H3; simpl; auto.
- simpl. destruct S; auto.
- simpl. destruct S; auto.
  destruct S1; auto; destruct (subst_ind_fit f0 S2); auto.
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
double negation substitution on it results in a valid ptree *)
(* *)
Lemma demorgan2_valid : forall (P : ptree) (E F : formula),
  valid P ->
  forall (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    valid (demorgan2_sub_ptree P E F S).
Proof.
intros P E F. induction P; try intros H S Hs.

- simpl. inversion H as [H1 H2]. inversion Hs. rewrite H3.
  rewrite demorgan2_ptree_formula_true; auto. split.
  + rewrite demorgan2_ptree_deg; auto.
  + apply (IHP H2 S H3).

- simpl. inversion H as [[H1 H2] H3]. inversion Hs. rewrite H4.
  rewrite demorgan2_ptree_formula_true; auto. split.
  + rewrite demorgan2_ptree_ord; auto.
  + auto.

- simpl. destruct (subst_ind_fit f S); apply H.

- simpl. destruct S; inversion Hs. rewrite H1. simpl.
  inversion H as [[[H2 H3] H4] H5].
  repeat split; rewrite demorgan2_ptree_formula_true.
  + rewrite demorgan2_ptree_formula; auto.
    rewrite H2. unfold demorgan2_sub_formula.
    rewrite formula_sub_ind_lor; auto. apply (and_bool_symm _ _ H1).
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + apply IHP. apply H. rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + rewrite demorgan2_ptree_deg; auto.
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  + rewrite demorgan2_ptree_ord; auto.
  + rewrite H2. simpl. apply (and_bool_symm _ _ H1).

- simpl. destruct S; try destruct S1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H4 H5] H6] H7].
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  repeat split; rewrite demorgan2_ptree_formula_true.
  + rewrite demorgan2_ptree_formula; auto.
    rewrite H4. unfold demorgan2_sub_formula.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H1, H2. auto.
    * simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + apply IHP; auto. rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite demorgan2_ptree_deg; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite demorgan2_ptree_ord; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.

- simpl. destruct S; try destruct S1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H4 H5] H6] H7].
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  repeat split; rewrite demorgan2_ptree_formula_true.
  + rewrite demorgan2_ptree_formula; auto.
    rewrite H4. unfold demorgan2_sub_formula.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H1, H3. auto.
    * simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + apply IHP; auto. rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite demorgan2_ptree_deg; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  + rewrite demorgan2_ptree_ord; auto.
  + rewrite H4. simpl. rewrite H1, H2, H3. auto.

- simpl. destruct S; try destruct S1; try destruct S1_1; inversion Hs.
  rewrite H1. simpl. inversion H as [[[H5 H6] H7] H8].
  destruct (and_bool_prop _ _ H1). clear H1.
  destruct (and_bool_prop _ _ H0). clear H0.
  destruct (and_bool_prop _ _ H1). clear H1.
  repeat split; rewrite demorgan2_ptree_formula_true.
  + rewrite demorgan2_ptree_formula; auto.
    rewrite H5. unfold demorgan2_sub_formula.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H0,H3. auto.
    * simpl. rewrite H0, H3, H4. auto.
    * simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + apply IHP; auto. rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite demorgan2_ptree_deg; auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  + rewrite demorgan2_ptree_ord; auto.
  + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.

- simpl. inversion Hs. rewrite H1. inversion H as [[[H2 H3] H4] H5].
  repeat split; rewrite demorgan2_ptree_formula_true.
  + rewrite demorgan2_ptree_formula; auto.
    unfold demorgan2_sub_formula. rewrite H2.
    rewrite formula_sub_ind_lor; auto. rewrite H1. auto.
  + rewrite H2. simpl. rewrite H1. auto.
  + apply IHP. apply H. rewrite H2. simpl. rewrite H1. auto.
  + rewrite H2. simpl. rewrite H1. auto.
  + rewrite demorgan2_ptree_deg; auto.
  + rewrite H2. simpl. rewrite H1. auto.
  + rewrite demorgan2_ptree_ord; auto.
  + rewrite H2. simpl. rewrite H1. auto.

- simpl. destruct S; inversion Hs. rewrite H1.
  inversion H as [[[H2 H3] H4] H5]. destruct (and_bool_prop _ _ H1).
  repeat split; rewrite demorgan2_ptree_formula_true.
  + rewrite demorgan2_ptree_formula; auto.
    unfold demorgan2_sub_formula. rewrite H2.
    repeat rewrite formula_sub_ind_lor; auto.
    * rewrite H0. auto.
    * simpl. rewrite H0, H6. auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + apply IHP. apply H. rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite demorgan2_ptree_deg; auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.
  + rewrite demorgan2_ptree_ord; auto.
  + rewrite H2. simpl. rewrite H0, H6. auto.

- simpl. destruct S; inversion Hs. rewrite H1. simpl.
  inversion H as [[[[H2 H3] H4] H5] H6]. destruct (and_bool_prop _ _ H1).
  repeat split.
  + rewrite demorgan2_ptree_formula_true.
    * rewrite demorgan2_ptree_formula; auto. rewrite H2. auto.
    * rewrite H2. auto.
  + apply demorgan2_sub_formula_closed. auto.
  + rewrite demorgan2_ptree_formula_true.
    * apply IHP; auto. rewrite H2. auto.
    * rewrite H2. auto.
  + rewrite demorgan2_ptree_formula_true.
    * rewrite demorgan2_ptree_deg; auto.
    * rewrite H2. auto.
  + rewrite demorgan2_ptree_formula_true.
    * rewrite demorgan2_ptree_ord; auto.
    * rewrite H2. auto.

- simpl. inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  destruct S; auto; destruct (eq_f f E); destruct (eq_f f0 F);
  simpl; repeat split; auto.
  case (eq_nat n0 (Init.Nat.max n n0)) eqn:Hn0;
  simpl; repeat split; auto.
  + rewrite <- H8. apply ord_max_succ_r.
  + apply ord_succ_nf. apply ord_max_nf.
    * rewrite H7. apply ptree_ord_nf. auto.
    * rewrite H8. apply ptree_ord_nf. auto.
  + rewrite <- H6. apply max_lem2. auto.
  + rewrite <- H8. apply ord_max_succ_r.
  + apply ord_succ_nf. apply ord_max_nf.
    * rewrite H7. apply ptree_ord_nf. auto.
    * rewrite H8. apply ptree_ord_nf. auto.
- simpl. inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  destruct S; auto.
  destruct S1; auto; destruct (subst_ind_fit f1 S2) eqn:HS2;
  destruct (eq_f f E) eqn:HE; destruct (eq_f f0 F) eqn:HF;
  simpl; repeat split; auto; rewrite demorgan2_ptree_formula_true;
  try rewrite demorgan2_ptree_deg; try rewrite demorgan2_ptree_ord;
  try rewrite demorgan2_ptree_formula;
  try apply IHP1; try apply IHP2; try rewrite H1; try rewrite H3;
  auto; unfold demorgan2_sub_formula; simpl; try rewrite HS2;
  try destruct (eq_f f0 (lor E F)); try destruct (eq_f f (lor E F));
  try rewrite sub_fit_true; auto;
  case (eq_nat n0 (Init.Nat.max n n0)) eqn:Hn0;
  simpl; repeat split; auto;
  try apply IHP2; auto; try rewrite H3; auto;
  try rewrite demorgan2_ptree_ord; auto;
  try rewrite <- H8; try apply ord_max_succ_r; auto;
  try rewrite demorgan2_ptree_deg; auto; try rewrite <- H6; try apply max_lem2; auto;
  try apply ord_succ_nf; try apply ord_max_nf; try rewrite H7; try rewrite H8; try apply ptree_ord_nf; auto.

- simpl. destruct S; auto.

- simpl. inversion H as [[[H1 H2] H3] H4]. destruct S; auto.
  destruct S1; auto; destruct (subst_ind_fit f0 S2) eqn:HS2; simpl;
  repeat split; auto; rewrite demorgan2_ptree_formula_true;
  try apply IHP; auto; try rewrite H1; simpl; try rewrite non_target_fit,HS2;
  try rewrite demorgan2_ptree_deg; try rewrite demorgan2_ptree_ord; auto.
  + rewrite demorgan2_ptree_formula; auto. rewrite H1.
    unfold demorgan2_sub_formula. simpl. rewrite non_target_fit,HS2.
    simpl. rewrite <- sub_fit_true; auto.
    * rewrite non_target_sub. rewrite <- sub_fit_true; auto.
    * apply non_target_fit.
  + rewrite demorgan2_ptree_formula; auto. rewrite H1.
    unfold demorgan2_sub_formula. simpl. rewrite non_target_fit,HS2.
    simpl. rewrite <- sub_fit_true; auto.
    * rewrite non_target_sub. rewrite <- sub_fit_true; auto.
    * apply non_target_fit.

- simpl. destruct S; apply H.

- simpl. destruct S; try apply H. inversion H as [[[[H0 H1] H2] H3] H4].
  destruct S1; inversion Hs; rewrite H6; simpl.
  + repeat split; auto.
    * rewrite demorgan2_ptree_formula_true, demorgan2_ptree_formula; auto.
      { rewrite H0. unfold demorgan2_sub_formula.
        { rewrite formula_sub_ind_lor. simpl.
          { destruct (eq_f (substitution f n t)); auto. }
          { simpl. apply H6. } } }
      { rewrite H0. simpl. apply H6. }
    * rewrite demorgan2_ptree_formula_true.
      { apply IHP; auto. rewrite H0. simpl. apply H6. }
      { rewrite H0. simpl. apply H6. }
    * rewrite demorgan2_ptree_formula_true.
      { rewrite demorgan2_ptree_deg; auto. }
      { rewrite H0. simpl. auto. }
    * rewrite demorgan2_ptree_formula_true.
      { rewrite demorgan2_ptree_ord; auto. }
      { rewrite H0. simpl. auto. }
  + repeat split; auto.
    * rewrite demorgan2_ptree_formula_true, demorgan2_ptree_formula; auto.
      { rewrite H0. unfold demorgan2_sub_formula.
        { rewrite formula_sub_ind_lor. simpl.
          { destruct (eq_f (substitution f n t)); auto. }
          { simpl. apply H6. } } }
      { rewrite H0. simpl. apply H6. }
    * rewrite demorgan2_ptree_formula_true.
      { apply IHP; auto. rewrite H0. simpl. apply H6. }
      { rewrite H0. simpl. apply H6. }
    * rewrite demorgan2_ptree_formula_true.
      { rewrite demorgan2_ptree_deg; auto. }
      { rewrite H0. simpl. auto. }
    * rewrite demorgan2_ptree_formula_true.
      { rewrite demorgan2_ptree_ord; auto. }
      { rewrite H0. simpl. auto. }

- intros. simpl. destruct S; apply H.

- rename H into H0. rename X into H. rename Hs into H1.
  simpl. destruct S; try apply H0. destruct S1; inversion H1.
  + rewrite H3. simpl. intros. destruct (valid_w_rule_ad _ _ _ _ _ _ H0 m)  as [[[H4 H5] H6] H7].
    repeat split.
    * rewrite demorgan2_ptree_formula_true, demorgan2_ptree_formula; auto.
      { rewrite H4. unfold demorgan2_sub_formula. rewrite formula_sub_ind_lor.
        { rewrite (non_target_term_sub f n (represent m)).
          rewrite non_target_sub. auto. }
        { rewrite (non_target_term_sub f n (represent m)).
          rewrite non_target_fit. apply H3. } }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
    * rewrite demorgan2_ptree_formula_true.
      { apply H. apply H5. rewrite H4. simpl.
        rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
    * rewrite demorgan2_ptree_formula_true.
      { rewrite demorgan2_ptree_deg; auto. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. rewrite H3. auto. }
    * rewrite demorgan2_ptree_formula_true.
      { rewrite demorgan2_ptree_ord; auto. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. rewrite H3. auto. }
  + rewrite H3. simpl. intros. destruct (valid_w_rule_ad _ _ _ _ _ _ H0 m) as [[[H4 H5] H6] H7].
    repeat split.
    * rewrite demorgan2_ptree_formula_true, demorgan2_ptree_formula; auto.
      { rewrite H4. unfold demorgan2_sub_formula. rewrite formula_sub_ind_lor.
        { rewrite (non_target_term_sub f n (represent m)).
          rewrite non_target_sub. auto. }
        { rewrite (non_target_term_sub f n (represent m)).
          rewrite non_target_fit. apply H3. } }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
    * rewrite demorgan2_ptree_formula_true.
      { apply H. apply H5. rewrite H4. simpl.
        rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. apply H3. }
    * rewrite demorgan2_ptree_formula_true.
      { rewrite demorgan2_ptree_deg; auto. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. rewrite H3. auto. }
    * rewrite demorgan2_ptree_formula_true.
      { rewrite demorgan2_ptree_ord; auto. }
      { rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. rewrite H3. auto. }
- clear IHP2. simpl. destruct (subst_ind_fit f S) eqn:Heq; try apply H. simpl.
  inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  repeat split; auto; rewrite demorgan2_ptree_formula_true.
  + rewrite demorgan2_ptree_formula; auto.
    rewrite H1. unfold demorgan2_sub_formula. rewrite formula_sub_ind_lor.
    * rewrite non_target_sub. auto.
    * rewrite Heq, non_target_fit. auto.
  + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + apply IHP1; auto. rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + rewrite demorgan2_ptree_deg; auto.
  + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  + rewrite demorgan2_ptree_ord; auto.
  + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.

- clear IHP1. simpl. destruct (subst_ind_fit f0 S) eqn:Heq; try apply H. simpl.
  inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  repeat split; auto; rewrite demorgan2_ptree_formula_true.
  + rewrite demorgan2_ptree_formula; auto.
    rewrite H3. unfold demorgan2_sub_formula. rewrite formula_sub_ind_lor.
    * rewrite non_target_sub. auto.
    * rewrite Heq, non_target_fit. auto.
  + rewrite H3. simpl. auto.
  + apply IHP2; auto. rewrite H3. simpl. auto.
  + rewrite H3. simpl. auto.
  + rewrite demorgan2_ptree_deg; auto.
  + rewrite H3. simpl. auto.
  + rewrite demorgan2_ptree_ord; auto.
  + rewrite H3. simpl. auto.

- simpl. inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  destruct S; try inversion Hs. rewrite H9.
  destruct (and_bool_prop _ _ H9) as [H10 H11].
  simpl. repeat split; rewrite demorgan2_ptree_formula_true.
  + rewrite demorgan2_ptree_formula; auto.
    rewrite H1. unfold demorgan2_sub_formula. rewrite formula_sub_ind_lor.
    * rewrite non_target_sub. auto.
    * rewrite H10, non_target_fit. auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + apply IHP1; auto. rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite demorgan2_ptree_formula; auto.
    rewrite H3. unfold demorgan2_sub_formula. rewrite formula_sub_ind_lor.
    * rewrite non_target_sub. auto.
    * rewrite H11, non_target_fit. auto.
  + rewrite H3. simpl. auto.
  + apply IHP2; auto. rewrite H3. simpl. auto.
  + rewrite H3. simpl. auto.
  + rewrite demorgan2_ptree_deg; auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite demorgan2_ptree_deg; auto.
  + rewrite H3. simpl. auto.
  + rewrite demorgan2_ptree_ord; auto.
  + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
  + rewrite demorgan2_ptree_ord; auto.
  + rewrite H3. simpl. auto.
Qed.





(* We finally show that if the formulas ~~A and/or ~~A \/ D are provable,
so are the formulas A and/or A \/ D *)
(* *)
Lemma demorgan2_invertible_a :
  forall (A B : formula) (d : nat) (alpha : ord),
  provable (neg (lor A B)) d alpha -> provable (neg B) d alpha.
Proof.
unfold provable. intros A B d alpha H. destruct H as [t [[[Ht1 Ht2] Ht3] Ht4]].
exists (demorgan2_sub_ptree t A B (1)). unfold P_proves. repeat split.
- rewrite demorgan2_ptree_formula; auto. rewrite Ht1.
  unfold demorgan2_sub_formula. simpl. repeat rewrite eq_f_refl. auto.
- apply demorgan2_valid; auto. rewrite Ht1. auto.
- rewrite demorgan2_ptree_deg; auto.
- rewrite demorgan2_ptree_ord; auto.
Qed.

Lemma demorgan2_invertible_ad :
  forall (A B D : formula) (d : nat) (alpha : ord),
  provable (lor (neg (lor A B)) D) d alpha -> provable (lor (neg B) D) d alpha.
Proof.
unfold provable. intros A B D d alpha H. destruct H as [t [[[Ht1 Ht2] Ht3] Ht4]].
exists (demorgan2_sub_ptree t A B (lor_ind (1) (non_target D))).
unfold P_proves. repeat split.
- rewrite demorgan2_ptree_formula; auto. rewrite Ht1.
  unfold demorgan2_sub_formula. simpl. rewrite non_target_fit.
  repeat rewrite eq_f_refl. simpl. rewrite <- sub_fit_true.
  + rewrite non_target_sub. auto.
  + apply non_target_fit.
- apply demorgan2_valid; auto. rewrite Ht1. simpl. apply non_target_fit.
- rewrite demorgan2_ptree_deg; auto.
- rewrite demorgan2_ptree_ord; auto.
Qed.










(*
###############################################################################
Section 9.4: Here we show invertibility of the w_rule.
###############################################################################
*)

(* Defining w_rule substitution in an ptree. First, we replace
(univ n E) with E(m) at certain places in a formula (given a substitution indicator).
Applying this operation to an entire ptree, we change the substitution
indicator as the structure of the formula(s) change as we move up the ptree. *)
(* *)
Definition w_rule_sub_formula
  (A E : formula) (n m : nat) (S : subst_ind) : formula :=
  formula_sub_ind A (univ n E) (substitution E n (represent m)) S.

Lemma w_rule_sub_formula_closed : forall (A : formula),
  closed A = true ->
  forall (E : formula) (n m : nat) (S : subst_ind),
    closed (w_rule_sub_formula A E n m S) = true.
Proof.
intros. unfold w_rule_sub_formula. apply formula_sub_ind_closed; auto.
intros. apply (closed_univ_sub E n H0 (represent m)). apply repr_closed.
Qed.


Fixpoint w_rule_sub_ptree_fit
  (P : ptree) (E : formula) (n m : nat) (S : subst_ind) : ptree :=
match P, S with
| deg_up d P', _ => deg_up d (w_rule_sub_ptree_fit P' E n m S)

| ord_up alpha P', _ => ord_up alpha (w_rule_sub_ptree_fit P' E n m S)

| node A, _ => P

| exchange_ab A B d alpha P', lor_ind S_B S_A =>
    exchange_ab
      (w_rule_sub_formula A E n m S_A)
      (w_rule_sub_formula B E n m S_B)
      d alpha
      (w_rule_sub_ptree_fit P' E n m (lor_ind S_A S_B))

| exchange_cab C A B d alpha P', lor_ind (lor_ind S_C S_B) S_A =>
    exchange_cab
      (w_rule_sub_formula C E n m S_C)
      (w_rule_sub_formula A E n m S_A)
      (w_rule_sub_formula B E n m S_B)
      d alpha
      (w_rule_sub_ptree_fit P' E n m (lor_ind (lor_ind S_C S_A) S_B))

| exchange_abd A B D d alpha P', lor_ind (lor_ind S_B S_A) S_D =>
    exchange_abd
      (w_rule_sub_formula A E n m S_A)
      (w_rule_sub_formula B E n m S_B)
      (w_rule_sub_formula D E n m S_D)
      d alpha
      (w_rule_sub_ptree_fit P' E n m (lor_ind (lor_ind S_A S_B) S_D))

| exchange_cabd C A B D d alpha P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D =>
    exchange_cabd
      (w_rule_sub_formula C E n m S_C)
      (w_rule_sub_formula A E n m S_A)
      (w_rule_sub_formula B E n m S_B)
      (w_rule_sub_formula D E n m S_D)
      d alpha
      (w_rule_sub_ptree_fit
        P' E n m
        (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D))

| contraction_a A d alpha P', _ =>
    contraction_a
      (w_rule_sub_formula A E n m S)
      d alpha
      (w_rule_sub_ptree_fit P' E n m (lor_ind S S))

| contraction_ad A D d alpha P', lor_ind S_A S_D =>
    contraction_ad
      (w_rule_sub_formula A E n m S_A)
      (w_rule_sub_formula D E n m S_D)
      d alpha
      (w_rule_sub_ptree_fit P' E n m (lor_ind (lor_ind S_A S_A) S_D))

| weakening_ad A D d alpha P', lor_ind S_A S_D =>
    weakening_ad
      (w_rule_sub_formula A E n m S_A)
      (w_rule_sub_formula D E n m S_D)
      d alpha
      (w_rule_sub_ptree_fit P' E n m S_D)

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, _ => P

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_AB S_D =>
    demorgan_abd
      A B
      (w_rule_sub_formula D E n m S_D)
      d1 d2 alpha1 alpha2
      (w_rule_sub_ptree_fit P1 E n m (lor_ind (0) S_D))
      (w_rule_sub_ptree_fit P2 E n m (lor_ind (0) S_D))

| negation_a A d alpha P', _ => P

| negation_ad A D d alpha P', lor_ind S_A S_D =>
    negation_ad
      A
      (w_rule_sub_formula D E n m S_D)
      d alpha
      (w_rule_sub_ptree_fit P' E n m (lor_ind (non_target A) S_D))

| quantification_a A k t d alpha P', _ => P

| quantification_ad A D k t d alpha P', lor_ind S_A S_D =>
    quantification_ad
      A
      (w_rule_sub_formula D E n m S_D)
      k t d alpha
      (w_rule_sub_ptree_fit P' E n m (lor_ind (0) S_D))

| w_rule_a A k d alpha g, _ =>
    (match eq_f A E, eq_nat d (ptree_deg (g m)), eq_nat k n, S with
    | true, true, true, (1) => ord_up (cons alpha 0 Zero) (g m)
    | true, false, true, (1) => deg_up d (ord_up (cons alpha 0 Zero) (g m))
    | _, _, _, _ => P
    end)

| w_rule_ad A D k d alpha g, lor_ind S_A S_D =>
    (match eq_f A E, eq_nat d (ptree_deg (g m)), eq_nat k n, S_A with
    | true, true, true, (1) =>
        ord_up (cons alpha 0 Zero) (w_rule_sub_ptree_fit (g m) E n m (lor_ind (non_target A) S_D))
    | true, false, true, (1) =>
        deg_up d (ord_up (cons alpha 0 Zero) (w_rule_sub_ptree_fit (g m) E n m (lor_ind (non_target A) S_D)))
    
    | _, _, _, _ => 
        w_rule_ad
          A
          (w_rule_sub_formula D E n m S_D)
          k d alpha
          (fun (p : nat) =>
            w_rule_sub_ptree_fit (g p) E n m (lor_ind (non_target A) S_D))
    end)

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ca
      (w_rule_sub_formula C E n m S)
      A d1 d2 alpha1 alpha2
      (w_rule_sub_ptree_fit P1 E n m (lor_ind S (non_target A)))
      P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ad
      A
      (w_rule_sub_formula D E n m S)
      d1 d2 alpha1 alpha2
      P1
      (w_rule_sub_ptree_fit P2 E n m (lor_ind (0) S))

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_D =>
    cut_cad
      (w_rule_sub_formula C E n m S_C)
      A
      (w_rule_sub_formula D E n m S_D)
      d1 d2 alpha1 alpha2
      (w_rule_sub_ptree_fit P1 E n m (lor_ind S_C (non_target A)))
      (w_rule_sub_ptree_fit P2 E n m (lor_ind (0) S_D))

| _, _ => P
end.

Fixpoint w_rule_sub_ptree
  (P : ptree) (E : formula) (n m : nat) (S : subst_ind) : ptree :=
match subst_ind_fit (ptree_formula P) S with
| false => P
| true => w_rule_sub_ptree_fit P E n m S
end.


Lemma w_rule_simp : forall (P : ptree) (E : formula) (n m : nat) (S : subst_ind), subst_ind_fit (ptree_formula P) S = true -> w_rule_sub_ptree P E n m S = w_rule_sub_ptree_fit P E n m S .
Proof.
intros.
destruct P; simpl; simpl in H; rewrite H; auto.
Qed.
(* First, we must prove that w_rule_sub_ptree simply changes the base formula
of an ptree the way we expect with w_rule_sub_formula *)
(* *)
Lemma w_rule_ptree_formula_aux' :
  forall (P : ptree) (E : formula) (n m : nat) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
    w_rule_sub_ptree P E n m S = P.
Proof. intros. unfold w_rule_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma w_rule_ptree_formula_aux :
  forall (P : ptree) (E : formula) (n m : nat) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
      ptree_formula (w_rule_sub_ptree P E n m S) =
      w_rule_sub_formula (ptree_formula P) E n m S.
Proof.
intros. rewrite w_rule_ptree_formula_aux'.
- unfold w_rule_sub_formula. rewrite sub_fit_false. auto. apply H.
- apply H.
Qed.

Lemma w_rule_ptree_formula_true :
  forall (P : ptree) (E : formula) (n m : nat) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    w_rule_sub_ptree_fit P E n m S = w_rule_sub_ptree P E n m S.
Proof. intros. unfold w_rule_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma w_rule_ptree_formula' : forall (P : ptree) (E : formula) (n m : nat),
  valid P ->
  forall (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    ptree_formula (w_rule_sub_ptree P E n m S) =
    w_rule_sub_formula (ptree_formula P) E n m S.
Proof.
intros P E n m.
induction P; try intros H S Hs.

- simpl in Hs. simpl. rewrite Hs. simpl.
  rewrite (w_rule_ptree_formula_true _ _ _ _ _ Hs).
  destruct H as [H1 H2]. apply (IHP H2). auto.

- simpl in Hs. simpl. rewrite Hs. simpl.
  rewrite (w_rule_ptree_formula_true _ _ _ _ _ Hs).
  destruct H as [[H1 H2] H3]. apply (IHP H2). auto.

- simpl. inversion H.
  destruct (axiom_atomic _ H1); destruct H0; rewrite H0;
  unfold w_rule_sub_formula; simpl; destruct S; auto.

- simpl.
  destruct S; inversion Hs; rewrite H1; simpl; unfold w_rule_sub_formula.
  rewrite formula_sub_ind_lor; auto.

- simpl.
  destruct S; try destruct S1; inversion Hs; rewrite H1;
  simpl; unfold w_rule_sub_formula.
  rewrite formula_sub_ind_lor, formula_sub_ind_lor; auto.
  apply (and_bool_prop _ _ H1).

- simpl.
  destruct S; try destruct S1; inversion Hs; rewrite H1;
  simpl; unfold w_rule_sub_formula.
  rewrite formula_sub_ind_lor, formula_sub_ind_lor; auto.
  apply (and_bool_prop _ _ H1).

- simpl. destruct S; simpl.
  + unfold w_rule_sub_formula. auto.
  + unfold w_rule_sub_formula. auto.
  + destruct S1; try destruct S1_1; inversion Hs.
    rewrite H1. simpl. unfold w_rule_sub_formula.
    destruct (and_bool_prop _ _ H1). destruct (and_bool_prop _ _ H0).
    repeat rewrite formula_sub_ind_lor; auto.

- simpl. inversion Hs. rewrite H1. auto.

- simpl. destruct S; inversion Hs.
  rewrite H1. simpl. unfold w_rule_sub_formula.
  rewrite formula_sub_ind_lor. auto. apply H1.

- simpl. destruct S; auto. inversion Hs. rewrite H1. simpl.
  unfold w_rule_sub_formula. rewrite formula_sub_ind_lor. auto. apply H1.

- simpl. destruct S; auto.

- simpl. destruct S.
  + inversion Hs.
  + inversion Hs.
  + destruct S1; inversion Hs; rewrite H1; simpl; unfold w_rule_sub_formula;
    rewrite formula_sub_ind_lor; auto; apply H1.

- simpl. destruct (eq_f f E) eqn:Heq; destruct S.
  + simpl. unfold w_rule_sub_formula. rewrite formula_sub_ind_0. auto.
  + unfold w_rule_sub_formula. simpl. inversion H as [[[H1 H2] H3] H4]. auto.
  + inversion Hs.
  + simpl. unfold w_rule_sub_formula. rewrite formula_sub_ind_0. auto.
  + unfold w_rule_sub_formula. simpl. auto.
  + inversion Hs.

- simpl. destruct (eq_f f E) eqn:Heq; destruct S.
  + inversion Hs.
  + inversion Hs.
  + destruct S1.
    * apply (subst_ind_fit_lor) in Hs. destruct (and_bool_prop _ _ Hs).
      rewrite H1. simpl. unfold w_rule_sub_formula.
      rewrite formula_sub_ind_lor, formula_sub_ind_0. auto. apply Hs.
    * inversion Hs. rewrite H1. simpl. inversion H as [[[H2 H3] H4] H5].
      unfold w_rule_sub_formula. simpl. rewrite H1. rewrite sub_fit_true; auto.
    * simpl. inversion Hs.
  + inversion Hs.
  + inversion Hs.
  + destruct S1.
    * apply (subst_ind_fit_lor) in Hs. destruct (and_bool_prop _ _ Hs).
      rewrite H1. simpl. unfold w_rule_sub_formula.
      rewrite formula_sub_ind_lor, formula_sub_ind_0. auto. apply Hs.
    * inversion Hs. rewrite H1. simpl. unfold w_rule_sub_formula.
      rewrite formula_sub_ind_lor; auto.
    * simpl. inversion Hs.

- simpl. destruct S; simpl; unfold w_rule_sub_formula; auto.

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
  provable (univ n A) d alpha ->
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























































































(*
###############################################################################
Section 10: Erasure Lemma
###############################################################################
*)

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

| exchange_cab C A B d alpha P', lor_ind (lor_ind S_C S_B) S_A =>
    exchange_cab
      (formula_sub_ind_fit C E F S_C)
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

| exchange_cabd C A B D d alpha P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D =>
    exchange_cabd
      (formula_sub_ind_fit C E F S_C)
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
      (fun (n : nat) =>
          formula_sub_ptree_fit (g n) E F (lor_ind (non_target A) S_D))

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ca
      (formula_sub_ind_fit C E F S)
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

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_D =>
    cut_cad
      (formula_sub_ind_fit C E F S_C)
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

- simpl. destruct S; auto. inversion H as [[[[H0 H1] H2] H3] H4].
  destruct S1; inversion Hs; rewrite H6; simpl.
  + repeat split; auto; rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_formula_atom_fit;
      auto; rewrite H0; simpl; auto.
    * rewrite H0. simpl. apply H6.
    * apply IHP; auto. rewrite H0. simpl. apply H6.
    * rewrite H0. simpl. apply H6.
    * rewrite formula_sub_ptree_deg_atom; auto.
    * rewrite H0. simpl. auto.
    * rewrite formula_sub_ptree_ord_atom; auto.
    * rewrite H0. simpl. auto.
  + repeat split; auto; rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_formula_atom_fit;
      auto; rewrite H0; simpl; auto.
    * rewrite H0. simpl. apply H6.
    * apply IHP; auto. rewrite H0. simpl. apply H6.
    * rewrite H0. simpl. apply H6.
    * rewrite formula_sub_ptree_deg_atom; auto.
    * rewrite H0. simpl. auto.
    * rewrite formula_sub_ptree_ord_atom; auto.
    * rewrite H0. simpl. auto.

- intros. simpl. destruct S; auto.

- rename H into H0. rename X into H. rename Hs into H1.
  simpl. destruct S; auto. destruct S1; inversion H1.
  + rewrite H3. simpl. intros. destruct (valid_w_rule_ad _ _ _ _ _ _ H0 m) as [[[H4 H5] H6] H7].
    repeat split; rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_formula_atom_fit; auto; rewrite H4; simpl;
      rewrite (non_target_term_sub f n (represent m)).
      { rewrite non_target_sub'. auto. }
      { rewrite non_target_fit. auto. }
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
      rewrite non_target_fit. apply H3.
    * apply H; auto. rewrite H4. simpl.
      rewrite (non_target_term_sub f n (represent m)).
      rewrite non_target_fit. apply H3.
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
      rewrite non_target_fit. apply H3.
    * rewrite formula_sub_ptree_deg_atom; auto.
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. rewrite H3. auto.
    * rewrite formula_sub_ptree_ord_atom; auto.
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
      rewrite non_target_fit. rewrite H3. auto.
  + rewrite H3. simpl. intros. destruct (valid_w_rule_ad _ _ _ _ _ _ H0 m) as [[[H4 H5] H6] H7].
    repeat split; rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_formula_atom_fit; auto; rewrite H4; simpl;
      rewrite (non_target_term_sub f n (represent m)).
      { rewrite non_target_sub'. auto. }
      { rewrite non_target_fit. auto. }
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
      rewrite non_target_fit. apply H3.
    * apply H; auto. rewrite H4. simpl.
      rewrite (non_target_term_sub f n (represent m)).
      rewrite non_target_fit. apply H3.
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
      rewrite non_target_fit. apply H3.
    * rewrite formula_sub_ptree_deg_atom; auto.
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. rewrite H3. auto.
    * rewrite formula_sub_ptree_ord_atom; auto.
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
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

- simpl. destruct S; auto. inversion H as [[[[H0 H1] H2] H3] H4].
  destruct S1; inversion Hs; rewrite H6; simpl.
  + repeat split; auto; rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_formula_neg_fit; auto; rewrite H0; simpl; auto.
      case (eq_f (substitution f n t) (atom a)); auto.
    * rewrite H0. simpl. apply H6.
    * apply IHP; auto. rewrite H0. simpl. apply H6.
    * rewrite H0. simpl. apply H6.
    * rewrite formula_sub_ptree_deg_neg; auto.
    * rewrite H0. simpl. auto.
    * rewrite formula_sub_ptree_ord_neg; auto.
    * rewrite H0. simpl. auto.
  + repeat split; auto; rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_formula_neg_fit; auto; rewrite H0; simpl; auto.
      case (eq_f (substitution f n t) (atom a)); auto.
    * rewrite H0. simpl. apply H6.
    * apply IHP; auto. rewrite H0. simpl. apply H6.
    * rewrite H0. simpl. apply H6.
    * rewrite formula_sub_ptree_deg_neg; auto.
    * rewrite H0. simpl. auto.
    * rewrite formula_sub_ptree_ord_neg; auto.
    * rewrite H0. simpl. auto.

- intros. simpl. destruct S; auto.

- rename H into H0. rename X into H. rename Hs into H1.
  simpl. destruct S; auto. destruct S1; inversion H1.
  + rewrite H3. simpl. intros. destruct (valid_w_rule_ad _ _ _ _ _ _ H0 m) as [[[H4 H5] H6] H7].
    repeat split; rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_formula_neg_fit; auto; rewrite H4; simpl;
      rewrite (non_target_term_sub f n (represent m)).
      { rewrite non_target_sub'. auto. }
      { rewrite non_target_fit. auto. }
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
      rewrite non_target_fit. apply H3.
    * apply H; auto. rewrite H4. simpl.
      rewrite (non_target_term_sub f n (represent m)).
      rewrite non_target_fit. apply H3.
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
      rewrite non_target_fit. apply H3.
    * rewrite formula_sub_ptree_deg_neg; auto.
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. rewrite H3. auto.
    * rewrite formula_sub_ptree_ord_neg; auto.
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
      rewrite non_target_fit. rewrite H3. auto.
  + rewrite H3. simpl. intros. destruct (valid_w_rule_ad _ _ _ _ _ _ H0 m) as [[[H4 H5] H6] H7].
    repeat split; rewrite formula_sub_ptree_formula_true.
    * rewrite formula_sub_ptree_formula_neg_fit; auto; rewrite H4; simpl;
      rewrite (non_target_term_sub f n (represent m)).
      { rewrite non_target_sub'. auto. }
      { rewrite non_target_fit. auto. }
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
      rewrite non_target_fit. apply H3.
    * apply H; auto. rewrite H4. simpl.
      rewrite (non_target_term_sub f n (represent m)).
      rewrite non_target_fit. apply H3.
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
      rewrite non_target_fit. apply H3.
    * rewrite formula_sub_ptree_deg_neg; auto.
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
        rewrite non_target_fit. rewrite H3. auto.
    * rewrite formula_sub_ptree_ord_neg; auto.
    * rewrite H4. simpl. rewrite (non_target_term_sub f n (represent m)).
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


















































(*
###############################################################################
Section 11: ...
###############################################################################
*)

(* Defining formula substitution for multiple formulas *)
(* *)
Fixpoint eq_length_list {X Y : Type} (lX : list X) (lY : list Y) : bool :=
match lX, lY with
| [], [] => true
| x :: lX', y :: lY' => eq_length_list lX' lY'
| _, _ => false
end.

Fixpoint formula_sub_ind_list_len
  (A : formula) (l1 l2 : list formula) (ls : list subst_ind) : formula :=
match l1, l2, ls with
| E :: l1', F :: l2', s :: ls' =>
    formula_sub_ind_list_len (formula_sub_ind A E F s) l1' l2' ls'
| _, _, _ => A
end.

Definition formula_sub_ind_list
  (A : formula) (l1 l2 : list formula) (ls : list subst_ind) : formula :=
match eq_length_list l1 l2, eq_length_list l1 ls with
| true, true => formula_sub_ind_list_len A l1 l2 ls
| _, _ => A
end.







(* Defining term substitution on multiple formulas *)
(* *)
Fixpoint sub_list (l : list formula) (n : nat) (t : term) : list formula :=
match l with
| [] => []
| E :: l' => (substitution E n t) :: sub_list l' n t
end.

Definition term_sub_ind_list_len
  (A : formula) (l : list formula) (ls : list subst_ind)
  (n : nat) (s t : term) : formula :=
formula_sub_ind_list_len A (sub_list l n s) (sub_list l n t) ls.

Definition term_sub_ind_list
  (A : formula) (l : list formula) (ls : list subst_ind)
  (n : nat) (s t : term) : formula :=
match eq_length_list l ls with
| true => term_sub_ind_list_len A l ls n s t
| _ => A
end.

Lemma formula_sub_ind_list_single :
  forall (A : formula) (E F : formula) (S : subst_ind),
  formula_sub_ind_list A [E] [F] [S] = formula_sub_ind A E F S.
Proof. intros. unfold formula_sub_ind_list. simpl. auto. Qed.

(*
(* Defining term substitution on proof trees *)
(* *)
Program Fixpoint term_sub_ptree_fit_list
  (P : ptree) (l : list formula) (ls : list subst_ind) (n : nat) (s t : term)
  : ptree :=
match P, S with
| deg_up d P', _ => deg_up d (term_sub_ptree_fit_list P' l ls n s t)

| ord_up alpha P', _ => ord_up alpha (term_sub_ptree_fit_list P' l ls n s t)

| node A, _ => node (term_sub_ind_fit A l ls n s t)

| exchange_ab A B d alpha P', lor_ind S_B S_A =>
    exchange_ab
      (term_sub_ind_fit A E n s t S_A)
      (term_sub_ind_fit B E n s t S_B)
      d alpha
      (term_sub_ptree_fit P' l ls n s t (lor_ind S_A S_B))

| exchange_cab C A B d alpha P', lor_ind (lor_ind S_C S_B) S_A =>
    exchange_cab
      (term_sub_ind_fit C E n s t S_C)
      (term_sub_ind_fit A E n s t S_A)
      (term_sub_ind_fit B E n s t S_B)
      d alpha
      (term_sub_ptree_fit P' E n s t (lor_ind (lor_ind S_C S_A) S_B))

| exchange_abd A B D d alpha P', lor_ind (lor_ind S_B S_A) S_D =>
    exchange_abd
      (term_sub_ind_fit A E n s t S_A)
      (term_sub_ind_fit B E n s t S_B)
      (term_sub_ind_fit D E n s t S_D)
      d alpha
      (term_sub_ptree_fit P' E n s t (lor_ind (lor_ind S_A S_B) S_D))

| exchange_cabd C A B D d alpha P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D =>
    exchange_cabd
      (term_sub_ind_fit C E n s t S_C)
      (term_sub_ind_fit A E n s t S_A)
      (term_sub_ind_fit B E n s t S_B)
      (term_sub_ind_fit D E n s t S_D)
      d alpha
      (term_sub_ptree_fit P' E n s t (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D))

| contraction_a A d alpha P', _ =>
    contraction_a
      (term_sub_ind_fit A E n s t S)
      d alpha
      (term_sub_ptree_fit P' E n s t (lor_ind S S))

| contraction_ad A D d alpha P', lor_ind S_A S_D =>
    contraction_ad
      (term_sub_ind_fit A E n s t S_A)
      (term_sub_ind_fit D E n s t S_D)
      d alpha
      (term_sub_ptree_fit P' E n s t (lor_ind (lor_ind S_A S_A) S_D))

| weakening_ad A D d alpha P', lor_ind S_A S_D =>
    weakening_ad
      (term_sub_ind_fit A E n s t S_A)
      (term_sub_ind_fit D E n s t S_D)
      d alpha
      (term_sub_ptree_fit P' E n s t S_D)

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, (1) =>
    (match eq_f (neg (lor A B)) (substitution E n s) with
    | true =>
        demorgan_ab
          (substitution A n t)
          (substitution B n t)
          d1 d2 alpha1 alpha2
          (term_sub_ptree_fit P1 A n s t (target A))
          (term_sub_ptree_fit P2 B n s t (target B))
    | false => P
    end)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, lor_ind (1) S_D =>
    (match eq_f (neg (lor A B)) (substitution E n s) with
    | true =>
        demorgan_abd
          (substitution A n t)
          (substitution B n t)
          (term_sub_ind_fit D E n s t S_D)
          d1 d2 alpha1 alpha2
          (term_sub_ptree_fit
            (term_sub_ptree_fit P1 E n s t (lor_ind (0) S_D))
            A n s t (lor_ind (1) (non_target D)))
          (term_sub_ptree_fit
            (term_sub_ptree_fit P2 E n s t (lor_ind (0) S_D))
            B n s t (lor_ind (1) (non_target D)))
    | false =>
        demorgan_abd
          A B
          (term_sub_ind_fit D E n s t S_D)
          d1 d2 alpha1 alpha2
          (term_sub_ptree_fit P1 E n s t (lor_ind (0) S_D))
          (term_sub_ptree_fit P2 E n s t (lor_ind (0) S_D))
    end)

| _, _ => P
end.

(*


| negation_a A d alpha P', (1) =>
    (match eq_f (neg (neg A)) (substitution E n s) with
    | true =>
        negation_a
          (substitution A n t)
          d alpha
          (term_sub_ptree_fit P' A n s t (1))
    | false => P
    end)

| negation_ad A D d alpha P', lor_ind (1) S_D =>
    (match eq_f (neg (neg A)) (substitution E n s) with
    | true =>
        negation_ad
          (substitution A n t)
          (term_sub_ind_fit D E n s t S_D)
          d alpha
          (term_sub_ptree_fit
            (term_sub_ptree_fit P' E n s t (lor_ind (0) S_D))
            A n s t (lor_ind (1) (non_target D)))
    | false =>
        negation_ad
          A
          (term_sub_ind_fit D E n s t S_D)
          d alpha
          (term_sub_ptree_fit P E n s t (lor_ind (0) S_D))
    end)



| quantification_a A k t d alpha P', (1) =>
    quantification_a
      (substitution A n t)
      d alpha
      (term_sub_ptree_fit P' E n s t S)

| quantification_ad A D k t d alpha P', lor_ind (1) S_D =>
    quantification_ad
      (substitution A n t)
      (term_sub_ind_fit D E n s t S_D)
      d alpha
      (term_sub_ptree_fit P' E n s t S)

| w_rule_a A k d alpha g, _ =>
    w_rule_a
      (substitution A n t)
      n d alpha
      (fun (p : nat) =>
        term_sub_ptree_fit (g p) E n s t S)

| w_rule_ad A D k d alpha g, lor_ind S_A S_D =>
    w_rule_a
      (substitution A n t)
      (term_sub_ind_fit D E F S_D)
      n d alpha
      (fun (p : nat) =>
        term_sub_ptree_fit (g p) E n s t S)

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ca
      (term_sub_ind_fit C E F S)
      A d1 d2 alpha1 alpha2
      (term_sub_ptree_fit P1 E F (lor_ind S (non_target A)))
      P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ad
      A
      (term_sub_ind_fit D E F S)
      d1 d2 alpha1 alpha2
      P1
      (term_sub_ptree_fit P2 E F (lor_ind (0) S))

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_D =>
    cut_cad
      (term_sub_ind_fit C E F S_C)
      A
      (term_sub_ind_fit D E F S_D)
      d1 d2 alpha1 alpha2
      (term_sub_ptree_fit P1 E F (lor_ind S_C (non_target A)))
      (term_sub_ptree_fit P2 E F (lor_ind (0) S_D))

| _, _ => P
end.

*)




(* Defining term substitution on proof trees *)
(* *)
Program Fixpoint term_sub_ptree_fit
  (P : ptree) (E : formula) (n : nat) (s t : term) (S : subst_ind) : ptree :=
match P, S with
| deg_up d P', _ => deg_up d (term_sub_ptree_fit P' E n s t S)

| ord_up alpha P', _ => ord_up alpha (term_sub_ptree_fit P' E n s t S)

| node A, _ => node (term_sub_ind_fit A E n s t S)

| exchange_ab A B d alpha P', lor_ind S_B S_A =>
    exchange_ab
      (term_sub_ind_fit A E n s t S_A)
      (term_sub_ind_fit B E n s t S_B)
      d alpha
      (term_sub_ptree_fit P' E n s t (lor_ind S_A S_B))

| exchange_cab C A B d alpha P', lor_ind (lor_ind S_C S_B) S_A =>
    exchange_cab
      (term_sub_ind_fit C E n s t S_C)
      (term_sub_ind_fit A E n s t S_A)
      (term_sub_ind_fit B E n s t S_B)
      d alpha
      (term_sub_ptree_fit P' E n s t (lor_ind (lor_ind S_C S_A) S_B))

| exchange_abd A B D d alpha P', lor_ind (lor_ind S_B S_A) S_D =>
    exchange_abd
      (term_sub_ind_fit A E n s t S_A)
      (term_sub_ind_fit B E n s t S_B)
      (term_sub_ind_fit D E n s t S_D)
      d alpha
      (term_sub_ptree_fit P' E n s t (lor_ind (lor_ind S_A S_B) S_D))

| exchange_cabd C A B D d alpha P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D =>
    exchange_cabd
      (term_sub_ind_fit C E n s t S_C)
      (term_sub_ind_fit A E n s t S_A)
      (term_sub_ind_fit B E n s t S_B)
      (term_sub_ind_fit D E n s t S_D)
      d alpha
      (term_sub_ptree_fit P' E n s t (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D))

| contraction_a A d alpha P', _ =>
    contraction_a
      (term_sub_ind_fit A E n s t S)
      d alpha
      (term_sub_ptree_fit P' E n s t (lor_ind S S))

| contraction_ad A D d alpha P', lor_ind S_A S_D =>
    contraction_ad
      (term_sub_ind_fit A E n s t S_A)
      (term_sub_ind_fit D E n s t S_D)
      d alpha
      (term_sub_ptree_fit P' E n s t (lor_ind (lor_ind S_A S_A) S_D))

| weakening_ad A D d alpha P', lor_ind S_A S_D =>
    weakening_ad
      (term_sub_ind_fit A E n s t S_A)
      (term_sub_ind_fit D E n s t S_D)
      d alpha
      (term_sub_ptree_fit P' E n s t S_D)

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, (1) =>
    (match eq_f (neg (lor A B)) (substitution E n s) with
    | true =>
        demorgan_ab
          (substitution A n t)
          (substitution B n t)
          d1 d2 alpha1 alpha2
          (term_sub_ptree_fit P1 A n s t (target A))
          (term_sub_ptree_fit P2 B n s t (target B))
    | false => P
    end)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, lor_ind (1) S_D =>
    (match eq_f (neg (lor A B)) (substitution E n s) with
    | true =>
        demorgan_abd
          (substitution A n t)
          (substitution B n t)
          (term_sub_ind_fit D E n s t S_D)
          d1 d2 alpha1 alpha2
          (term_sub_ptree_fit
            (term_sub_ptree_fit P1 E n s t (lor_ind (0) S_D))
            A n s t (lor_ind (1) (non_target D)))
          (term_sub_ptree_fit
            (term_sub_ptree_fit P2 E n s t (lor_ind (0) S_D))
            B n s t (lor_ind (1) (non_target D)))
    | false =>
        demorgan_abd
          A B
          (term_sub_ind_fit D E n s t S_D)
          d1 d2 alpha1 alpha2
          (term_sub_ptree_fit P1 E n s t (lor_ind (0) S_D))
          (term_sub_ptree_fit P2 E n s t (lor_ind (0) S_D))
    end)

| _, _ => P
end.

(*


| negation_a A d alpha P', (1) =>
    (match eq_f (neg (neg A)) (substitution E n s) with
    | true =>
        negation_a
          (substitution A n t)
          d alpha
          (term_sub_ptree_fit P' A n s t (1))
    | false => P
    end)

| negation_ad A D d alpha P', lor_ind (1) S_D =>
    (match eq_f (neg (neg A)) (substitution E n s) with
    | true =>
        negation_ad
          (substitution A n t)
          (term_sub_ind_fit D E n s t S_D)
          d alpha
          (term_sub_ptree_fit
            (term_sub_ptree_fit P' E n s t (lor_ind (0) S_D))
            A n s t (lor_ind (1) (non_target D)))
    | false =>
        negation_ad
          A
          (term_sub_ind_fit D E n s t S_D)
          d alpha
          (term_sub_ptree_fit P E n s t (lor_ind (0) S_D))
    end)



| quantification_a A k t d alpha P', (1) =>
    quantification_a
      (substitution A n t)
      d alpha
      (term_sub_ptree_fit P' E n s t S)

| quantification_ad A D k t d alpha P', lor_ind (1) S_D =>
    quantification_ad
      (substitution A n t)
      (term_sub_ind_fit D E n s t S_D)
      d alpha
      (term_sub_ptree_fit P' E n s t S)

| w_rule_a A k d alpha g, _ =>
    w_rule_a
      (substitution A n t)
      n d alpha
      (fun (p : nat) =>
        term_sub_ptree_fit (g p) E n s t S)

| w_rule_ad A D k d alpha g, lor_ind S_A S_D =>
    w_rule_a
      (substitution A n t)
      (term_sub_ind_fit D E F S_D)
      n d alpha
      (fun (p : nat) =>
        term_sub_ptree_fit (g p) E n s t S)

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ca
      (term_sub_ind_fit C E F S)
      A d1 d2 alpha1 alpha2
      (term_sub_ptree_fit P1 E F (lor_ind S (non_target A)))
      P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ad
      A
      (term_sub_ind_fit D E F S)
      d1 d2 alpha1 alpha2
      P1
      (term_sub_ptree_fit P2 E F (lor_ind (0) S))

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_D =>
    cut_cad
      (term_sub_ind_fit C E F S_C)
      A
      (term_sub_ind_fit D E F S_D)
      d1 d2 alpha1 alpha2
      (term_sub_ptree_fit P1 E F (lor_ind S_C (non_target A)))
      (term_sub_ptree_fit P2 E F (lor_ind (0) S_D))

| _, _ => P
end.

*)

Fixpoint term_sub_ptree
  (P : ptree) (E : formula) (n : nat) (s t : term) (S : subst_ind) : ptree :=
match subst_ind_fit (ptree_formula P) S with
| false => P
| true => term_sub_ptree_fit P E n s t S
end.


(* Some preliminary lemmas *)
(* *)
Lemma term_sub_fit_false :
  forall (A E : formula) (n : nat) (s t : term) (S : subst_ind),
  subst_ind_fit A S = false ->
  term_sub_ind A E n s t S = A.
Proof. intros. unfold term_sub_ind. destruct A; rewrite H; auto. Qed.

Lemma term_sub_ptree_term_aux' :
  forall (P : ptree) (E : formula) (n : nat) (s t : term) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
    term_sub_ptree P E n s t S = P.
Proof. intros. unfold term_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma term_sub_ptree_term_aux :
  forall (P : ptree) (E : formula) (n : nat) (s t : term) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
      ptree_formula (term_sub_ptree P E n s t S) =
      term_sub_ind (ptree_formula P) E n s t S.
Proof.
intros. rewrite term_sub_ptree_term_aux'; auto.
unfold term_sub_ind. rewrite term_sub_fit_false. auto. apply H.
Qed.

Lemma term_sub_fit_true :
  forall (A E : formula) (n : nat) (s t : term) (S : subst_ind),
    subst_ind_fit A S = true ->
    term_sub_ind_fit A E n s t S = term_sub_ind A E n s t S.
Proof. intros. unfold term_sub_ind. destruct A; rewrite H; auto. Qed.

Lemma term_sub_ptree_formula_true :
  forall (P : ptree) (E : formula) (n : nat) (s t : term) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    term_sub_ptree_fit P E n s t S = term_sub_ptree P E n s t S.
Proof. intros. unfold term_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma term_sub_ptree_fit_false :
  forall (P : ptree) (E : formula) (n : nat) (s t : term) (S : subst_ind),
  subst_ind_fit (ptree_formula P) S = false -> 
  term_sub_ptree P E n s t S = P.
Proof. intros. unfold term_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma term_sub_formula_sub :
  forall (A E : formula) (n : nat) (s t : term) (S : subst_ind),
  term_sub_ind_fit A E n s t S =
  formula_sub_ind_fit A (substitution E n s) (substitution E n t) S.
Proof. intros. unfold term_sub_ind_fit. destruct A; auto. Qed.

Lemma subst_closed_a : forall (a : atomic_formula) (n : nat) (s t : term),
  closed_t t = true ->
  closed_a (substitution_a a n s) = true ->
  closed_a (substitution_a a n t) = true.
Proof.
intros. destruct a. simpl. destruct (and_bool_prop _ _ H0).
rewrite (subst_closed_t n t0 s t H H1), (subst_closed_t n t1 s t H H2). auto.
Qed.

Lemma subst_closed : forall (A : formula) (n : nat) (s t : term),
  closed_t t = true ->
  closed (substitution A n s) = true ->
  closed (substitution A n t) = true.
Proof.
intros. induction A.
- simpl. apply (subst_closed_a _ _ s); auto.
- simpl. apply IHA. apply H0.
- simpl. simpl in H0. destruct (and_bool_prop _ _ H0).
  rewrite (IHA1 H1), (IHA2 H2). auto.
- simpl. simpl in H0. destruct (eq_nat n0 n); auto.
  destruct (closed_univ _ _ H0).
  + apply IHA in H1. simpl. rewrite H1. auto.
  + simpl. destruct (closed (substitution A n t)) eqn:HA; auto.
    destruct (free_list (substitution A n t)).
    * apply IHA. admit.
    * admit.
Admitted.

Lemma term_sub_ind_fit_closed : forall (A E : formula) (n : nat) (s t : term),
  closed A = true -> closed_t t = true ->
  forall (S : subst_ind),
    subst_ind_fit A S = true ->
    closed (term_sub_ind_fit A E n s t S) = true.
Proof.
intros. rewrite term_sub_formula_sub. apply formula_sub_ind_fit_closed; auto.
intros. apply (subst_closed _ _ s); auto.
Qed.

Lemma subst_twice_t : forall (n : nat) (T s t : term),
  substitution_t T n t = substitution_t (substitution_t T n s) n t.
Proof.
intros. induction T; auto.
- simpl. rewrite IHT. auto.
- simpl. rewrite IHT1,IHT2. auto.
- simpl. rewrite IHT1,IHT2. auto.
Admitted.


Lemma subst_twice_a : forall (a : atomic_formula) (n : nat) (s t : term),
  substitution_a a n t = substitution_a (substitution_a a n s) n t.
Proof.
intros. Admitted.

Lemma subst_twice : forall (A : formula) (n : nat) (s t : term),
  substitution A n t = substitution (substitution A n s) n t.
Proof.
intros. Admitted.

















(* First, we must prove that term_sub_ptree simply changes the base formula
of an ptree the way we expect with formula_sub_ind *)
(* *)
Lemma term_sub_ptree_formula' :
  forall (P : ptree) (E : formula) (n : nat) (s t : term),
  valid P ->
  correct_a (equ s t) = true ->
  forall (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    ptree_formula
      (term_sub_ptree P E n s t S) =
    term_sub_ind
      (ptree_formula P) E n s t S.
Proof.
intros P E n s t.
induction P; try intros H Hst S Hs.

- simpl in Hs. simpl. rewrite Hs. simpl.
  rewrite term_sub_ptree_formula_true; auto.
  destruct H as [H1 H2]. apply (IHP H2); auto.

- simpl in Hs. simpl. rewrite Hs. simpl.
  rewrite term_sub_ptree_formula_true; auto.
  destruct H as [H1 H2]. apply (IHP H2); auto.

- simpl in Hs. simpl. rewrite Hs. simpl. rewrite term_sub_fit_true; auto.

- simpl. destruct S; auto. inversion Hs. rewrite H1. simpl.
  repeat rewrite term_sub_formula_sub. auto.

- simpl. destruct S; auto. destruct S1; auto.
  inversion Hs. rewrite H1. simpl. auto.
  repeat rewrite term_sub_formula_sub. auto.

- simpl. destruct S; auto. destruct S1; auto.
  inversion Hs. rewrite H1. simpl. auto.
  repeat rewrite term_sub_formula_sub. auto.

- simpl. destruct S; auto. destruct S1; auto. destruct S1_1; auto.
  inversion Hs. rewrite H1. simpl. auto.
  repeat rewrite term_sub_formula_sub. auto.

- simpl. destruct (subst_ind_fit f S) eqn:HS.
  + simpl. rewrite term_sub_fit_true; auto.
  + simpl. rewrite term_sub_fit_false; auto.

- simpl. destruct S; auto. inversion Hs. rewrite H1. simpl.
  repeat rewrite term_sub_formula_sub. auto.

- simpl. destruct S; auto. inversion Hs. rewrite H1. simpl.
  repeat rewrite term_sub_formula_sub. auto.

- simpl. destruct S; auto.
  + simpl. destruct (substitution E n s); auto. destruct f1; auto.
    destruct (eq_f f f1_1 && eq_f f0 f1_2); auto.
  + simpl. destruct (substitution E n s) eqn:HE; auto. destruct f1; auto.
    destruct (eq_f f f1_1 && eq_f f0 f1_2) eqn:Hf1; auto. simpl.
    rewrite (subst_twice E _ s). rewrite HE.
    destruct (and_bool_prop _ _ Hf1).
    rewrite (f_eq_decid _ _ H0). rewrite (f_eq_decid _ _ H1). auto.





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
















































*)

(*
#####################
My Section: Degree Elimination, need to show that deg_up can be eliminated,
i.e has no logical conseqeunces, is just a convenient tool.
#####################
*)


(*
Theorem deg_elimination_valid: forall (P : ptree),
valid P -> valid (deg_elimination P).
Proof.
intros. induction P.
- destruct X as [X1 X2]. simpl. auto.
- destruct X as [X1 X2]. simpl. pose proof (IHP X2). split; auto. rewrite deg_elimination_ord; auto.
- auto.
- destruct X as [[[X1 X2] X3] X4]. simpl. pose proof (IHP X2).
  repeat split; auto. rewrite deg_elimination_formula; auto. rewrite real_deg_is_deg_elim_deg; auto. rewrite deg_elimination_ord; auto.
- destruct X as [[[X1 X2] X3] X4]. simpl. pose proof (IHP X2).
  repeat split; auto. rewrite deg_elimination_formula; auto. rewrite real_deg_is_deg_elim_deg; auto. rewrite deg_elimination_ord; auto.
- destruct X as [[[X1 X2] X3] X4]. simpl. pose proof (IHP X2). auto.
  repeat split; auto. rewrite deg_elimination_formula; auto. rewrite real_deg_is_deg_elim_deg; auto. rewrite deg_elimination_ord; auto.
- destruct X as [[[X1 X2] X3] X4]. simpl. pose proof (IHP X2). auto.
  repeat split; auto. rewrite deg_elimination_formula; auto. rewrite real_deg_is_deg_elim_deg; auto. rewrite deg_elimination_ord; auto.
- destruct X as [[[X1 X2] X3] X4]. simpl. pose proof (IHP X2). auto.
  repeat split; auto. rewrite deg_elimination_formula; auto. rewrite real_deg_is_deg_elim_deg; auto. rewrite deg_elimination_ord; auto.
- destruct X as [[[X1 X2] X3] X4]. simpl. pose proof (IHP X2). auto.
  repeat split; auto. rewrite deg_elimination_formula; auto. rewrite real_deg_is_deg_elim_deg; auto. rewrite deg_elimination_ord; auto.
- destruct X as [[[X1 X2] X3] X4]. simpl. pose proof (IHP X2). auto. destruct X1 as [X0 X1].
  repeat split; auto. rewrite deg_elimination_formula; auto. rewrite real_deg_is_deg_elim_deg; auto. rewrite deg_elimination_ord; auto.
- destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. simpl. pose proof (IHP1 X2). pose proof (IHP2 X4). auto.
  repeat split; auto. rewrite deg_elimination_formula; auto. rewrite deg_elimination_formula; auto. rewrite real_deg_is_deg_elim_deg; auto. rewrite real_deg_is_deg_elim_deg; auto. rewrite deg_elimination_ord; auto. rewrite deg_elimination_ord; auto.
- destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. simpl. pose proof (IHP1 X2). pose proof (IHP2 X4). auto.
  repeat split; auto. rewrite deg_elimination_formula; auto. rewrite deg_elimination_formula; auto. rewrite real_deg_is_deg_elim_deg; auto. rewrite real_deg_is_deg_elim_deg; auto. rewrite deg_elimination_ord; auto. rewrite deg_elimination_ord; auto.
- destruct X as [[[X1 X2] X3] X4]. simpl. pose proof (IHP X2). auto.
  repeat split; auto. rewrite deg_elimination_formula; auto. rewrite real_deg_is_deg_elim_deg; auto. rewrite deg_elimination_ord; auto.
- destruct X as [[[X1 X2] X3] X4]. simpl. pose proof (IHP X2). auto.
  repeat split; auto. rewrite deg_elimination_formula; auto. rewrite real_deg_is_deg_elim_deg; auto. rewrite deg_elimination_ord; auto.
- destruct X as [[[X1 X2] X3] X4]. simpl. pose proof (IHP X2). auto. destruct X1 as [X0 X1].
  repeat split; auto. rewrite deg_elimination_formula; auto. rewrite real_deg_is_deg_elim_deg; auto. rewrite deg_elimination_ord; auto.
- destruct X as [[[X1 X2] X3] X4]. simpl. pose proof (IHP X2). destruct X1 as [X0 X1].
  repeat split; auto. rewrite deg_elimination_formula; auto. rewrite real_deg_is_deg_elim_deg; auto. rewrite deg_elimination_ord; auto.
- destruct X as [T1 T2]. split. simpl. intros. destruct (T1 m) as [[[X1 X2] X3] X4]. pose proof (X0 m X2). repeat split.
  + rewrite deg_elimination_formula; auto.
  + apply X.
  + rewrite <- (real_deg_is_deg_elim_deg (p m) X2). pose proof (real_deg_le (p m) X2). lia.
  + rewrite deg_elimination_ord; auto. 
  + destruct (T1 x) as [[[X1 X2] X3] X4].
- admit.
- destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. simpl. pose proof (IHP1 X2). pose proof (IHP2 X4).
  repeat split; auto. rewrite deg_elimination_formula; auto. rewrite deg_elimination_formula; auto. rewrite real_deg_is_deg_elim_deg; auto. rewrite real_deg_is_deg_elim_deg; auto. rewrite deg_elimination_ord; auto. rewrite deg_elimination_ord; auto.
- destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. simpl. pose proof (IHP1 X2). pose proof (IHP2 X4).
  repeat split; auto. rewrite deg_elimination_formula; auto. rewrite deg_elimination_formula; auto. rewrite real_deg_is_deg_elim_deg; auto. rewrite real_deg_is_deg_elim_deg; auto. rewrite deg_elimination_ord; auto. rewrite deg_elimination_ord; auto.
- destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. simpl. pose proof (IHP1 X2). pose proof (IHP2 X4).
  repeat split; auto. rewrite deg_elimination_formula; auto. rewrite deg_elimination_formula; auto. rewrite real_deg_is_deg_elim_deg; auto. rewrite real_deg_is_deg_elim_deg; auto. rewrite deg_elimination_ord; auto. rewrite deg_elimination_ord; auto.
Admitted.

Fixpoint deg_free (P : ptree) : Type :=
match P with
| deg_up d P' => False

| ord_up alpha P' => deg_free P'

| node A => True

| exchange_ab A B d alpha P' => deg_free P'

| exchange_cab C A B d alpha P' => deg_free P'

| exchange_abd A B D d alpha P' => deg_free P'

| exchange_cabd C A B D d alpha P' => deg_free P'

| contraction_a A d alpha P' => deg_free P'

| contraction_ad A D d alpha P' => deg_free P'

| weakening_ad A D d alpha P' => deg_free P'

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2 => (deg_free P1) * (deg_free P2)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2 => (deg_free P1) * (deg_free P2)

| negation_a A d alpha P' => deg_free P'

| negation_ad A D d alpha P' => deg_free P'

| quantification_a A n t d alpha P' => deg_free P'

| quantification_ad A D n t d alpha P' => deg_free P'

| w_rule_a A n d alpha g => forall (m : nat), deg_free (g m)

| w_rule_ad A D n d alpha g => forall (m : nat), deg_free (g m)

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2 => (deg_free P1) * (deg_free P2)

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 => (deg_free P1) * (deg_free P2)

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2 => (deg_free P1) * (deg_free P2)
end.

Lemma deg_elim_deg_free: forall (P : ptree), deg_free (deg_elimination P).
Proof.
intros. induction P; simpl; auto.
Qed.

Definition P_proves' (P : ptree) (A : formula) : Type :=
  (ptree_formula P = A) * (valid P) *
  {d : nat & ptree_deg P = d & {alpha : ord & ptree_ord P = alpha}}.

Lemma deg_elim : forall (A : formula) (d : nat) (alpha : ord),
  provable A d alpha -> {P : ptree & P_proves' P A & deg_free P}.
Proof.
intros. destruct X as [P [[[X1 X2] X3] X4] ]. exists (deg_elimination P).
- repeat split; auto. rewrite deg_elimination_formula; auto. apply deg_elimination_valid. auto.
  exists (ptree_deg (deg_elimination P)). auto.
  exists (ptree_ord (deg_elimination P)). auto.
- apply deg_elim_deg_free. 
Qed.
*)

  (*
###############################################################################
Section 12: Here we define the cut_elimination algorithm.
This is a complicated operation on ptrees, and we will define the many cases
separately before piecing them together.
###############################################################################
*)


(* Defining cut_elimination_0, the case where the ordinal alpha = 0 *)
(* *)
Fixpoint cut_elimination_0 (P : ptree) : ptree :=
match P with
| ord_up alpha P' => P'
| deg_up d P' => P'
| _ => P
end.


(* Defining cut_elimination_atom, the case where the cut formula is atom a *)
(* *)
Fixpoint cut_elimination_atom (P : ptree) : ptree :=
match P with
| cut_ca C (atom a) d1 d2 alpha1 alpha2 P1 P2 =>
  (match PA_omega_axiom (atom a) with
  | true =>
      formula_sub_ptree P2 (neg (atom a)) C (1)
  | false =>
      contraction_a
        C d1 alpha1
        (formula_sub_ptree P1 (atom a) C (lor_ind (non_target C) (1)))
  end)

| cut_ad (atom a) D d1 d2 alpha1 alpha2 P1 P2 =>
  (match PA_omega_axiom (atom a) with
  | true =>
      contraction_a
        D d2 alpha2
        (formula_sub_ptree P2 (neg (atom a)) D (lor_ind (1) (non_target D)))
  | false =>
      formula_sub_ptree P1 (atom a) D (1)
  end)

| cut_cad C (atom a) D d1 d2 alpha1 alpha2 P1 P2 =>
  (match PA_omega_axiom (atom a) with
  | true =>
      weakening_ad C D d2 alpha2
        (contraction_a
          D d2 alpha2
          (formula_sub_ptree P2 (neg (atom a)) D (lor_ind (1) (non_target D))))
  | false =>
      exchange_ab
        D C d1 (ord_succ alpha1)
        (weakening_ad
          D C d1 alpha1
          (contraction_a
            C d1 alpha1
            (formula_sub_ptree P1 (atom a) C (lor_ind (non_target C) (1)))))
  end)
| deg_up d P' => cut_elimination_atom P'
| ord_up alpha P' => cut_elimination_atom P'
| _ => P
end.


(* Defining cut_elimination_neg, the case where the cut formula is ~E *)
(* *)
Fixpoint cut_elimination_neg (P : ptree) : ptree :=
match P with
| cut_ca C (neg E) d1 d2 alpha1 alpha2 P1 P2 =>
    cut_ad
      E C d2 d1 alpha2 alpha1
      (dub_neg_sub_ptree P2 E (1))
      (exchange_ab C (neg E) d1 alpha1 P1)

| cut_ad (neg E) D d1 d2 alpha1 alpha2 P1 P2 =>
    cut_ca
      D E d2 d1 alpha2 alpha1
      (exchange_ab
        E D d2 alpha2
        (dub_neg_sub_ptree P2 E (lor_ind (1) (non_target D))))
      P1

| cut_cad C (neg E) D d1 d2 alpha1 alpha2 P1 P2 =>
  (match (eq_nat (max (max d2 d1) (S (num_conn E))) (S (num_conn E))) with
    | true =>  exchange_ab
                D C (ptree_deg P) (ptree_ord P)
                (deg_up (max (max d1 d2) (S (S (num_conn E))))
                  (cut_cad
                    D E C d2 d1 alpha2 alpha1
                    (exchange_ab
                    E D d2 alpha2
                      (dub_neg_sub_ptree P2 E (lor_ind (1) (non_target D))))
                        (exchange_ab C (neg E) d1 alpha1 P1)))
    | false => exchange_ab
                D C (ptree_deg P) (ptree_ord P)
                (cut_cad
                  D E C d2 d1 alpha2 alpha1
                  (exchange_ab
                    E D d2 alpha2
                    (dub_neg_sub_ptree P2 E (lor_ind (1) (non_target D))))
                      (exchange_ab C (neg E) d1 alpha1 P1))
  end)
| deg_up d P' => cut_elimination_neg P'
| ord_up alpha P' => cut_elimination_neg P'
| _ => P
end.


(* Defining cut_elimination_lor, the case where the cut formula is E \/ F *)
(* *)
Definition associativity_1' (P : ptree) : ptree :=
match ptree_formula P, ptree_deg P, ptree_ord P with
| lor (lor C A) B, d, alpha =>
    exchange_ab
      (lor A B) C d alpha
      (exchange_cab
        A C B d alpha
        (exchange_abd C A B d alpha P))

| _, _, _ => P
end.

Definition associativity_2' (P : ptree) : ptree :=
match ptree_formula P, ptree_deg P, ptree_ord P with
| lor C (lor A B), d, alpha =>
    exchange_abd
      A C B d alpha
      (exchange_cab
        A B C d alpha
        (exchange_ab C (lor A B) d alpha P))

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

Definition contraction_help (P : ptree) : ptree :=
match ptree_formula P, ptree_deg P, ptree_ord P with
| lor (lor C D) E, d, alpha =>
    (match eq_f D E with
    | true =>
        exchange_ab
          D C d alpha
          (contraction_ad
            D C d alpha
            (exchange_cab
              D C D d alpha
              (exchange_abd C D D d alpha P)))

    | false => P
    end)

| _, _, _ => P
end.

Fixpoint cut_elimination_lor (P : ptree) : ptree :=
match P with
| cut_ca C (lor E F) d1 d2 alpha1 alpha2 P1 P2 =>
    cut_ca
      C E
      (max (max d1 d2) (num_conn F))
      d2
      (ord_succ (ord_max alpha1 alpha2))
      alpha2
      (cut_ca (lor C E) F d1 d2 alpha1 alpha2
        (associativity_2' P1)
        (demorgan2_sub_ptree P2 E F (1)))
      (demorgan1_sub_ptree P2 E F (1))

| cut_ad (lor E F) D d1 d2 alpha1 alpha2 P1 P2 =>
    contraction_a
      D
      (max (max d1 d2) (max (num_conn E) (num_conn F)))
      (ord_succ (ord_succ (ord_max alpha1 alpha2)))
      (cut_cad
        D E D
        (max (max d1 d2) (num_conn F))
        d2
        (ord_succ (ord_max alpha1 alpha2))
        alpha2
        (exchange_ab
          E D
          (max (max d1 d2) (num_conn F))
          (ord_succ (ord_max alpha1 alpha2))
          (cut_cad
            E F D d1 d2 alpha1 alpha2 P1
            (demorgan2_sub_ptree P2 E F (lor_ind (1) (non_target D)))))
        (demorgan1_sub_ptree P2 E F (lor_ind (1) (non_target D))))

| cut_cad C (lor E F) D d1 d2 alpha1 alpha2 P1 P2 =>
    contraction_help
      (cut_cad
        (lor C D) E D
        (max (max d1 d2) (S (num_conn F)))
        d2
        (ord_succ (ord_max alpha1 alpha2))
        alpha2
        (exchange_cab
          C E D
          (max (max d1 d2) (S (num_conn F)))
          (ord_succ (ord_max alpha1 alpha2))
          (cut_cad (lor C E) F D d1 d2 alpha1 alpha2
            (associativity_2' P1)
            (demorgan2_sub_ptree P2 E F (lor_ind (1) (non_target D)))))
        (demorgan1_sub_ptree P2 E F (lor_ind (1) (non_target D))))

| deg_up d P' => cut_elimination_lor P'
| ord_up alpha P' => cut_elimination_lor P'
| _ => P
end.




(* Defining cut_elimination_univ, the case where the cut formula is univ n E *)
(* *)
(*
Fixpoint cut_elimination_univ (P : ptree) : ptree :=
match P with
| cut_ca C (univ n F) d1 d2 alpha1 alpha2 P1 P2 =>
    cut_ca
      C E
      (max (max d1 d2) (num_conn F))
      d2
      (ord_succ (ord_max alpha1 alpha2))
      alpha2
      (cut_ca (lor C E) F d1 d2 alpha1 alpha2
        (associativity_2' P1)
        (demorgan2_sub_ptree P2 E F (1)))
      (demorgan1_sub_ptree P2 E F (1))

| cut_ad (lor E F) D d1 d2 alpha1 alpha2 P1 P2 =>
    contraction_a
      D
      (max (max d1 d2) (max (num_conn E) (num_conn F)))
      (ord_succ (ord_succ (ord_max alpha1 alpha2)))
      (cut_cad
        D E D
        (max (max d1 d2) (num_conn F))
        d2
        (ord_succ (ord_max alpha1 alpha2))
        alpha2
        (exchange_ab
          E D
          (max (max d1 d2) (num_conn F))
          (ord_succ (ord_max alpha1 alpha2))
          (cut_cad
            E F D d1 d2 alpha1 alpha2 P1
            (demorgan2_sub_ptree P2 E F (lor_ind (1) (non_target D)))))
        (demorgan1_sub_ptree P2 E F (lor_ind (1) (non_target D))))

| cut_cad C (lor E F) D d1 d2 alpha1 alpha2 P1 P2 =>
    contraction_help
      (cut_cad
        (lor C D) E D
        (max (max d1 d2) (max (num_conn E) (num_conn F)))
        d2
        (ord_succ (ord_succ (ord_max alpha1 alpha2)))
        alpha2
        (exchange_cab
          C E D
          (max (max d1 d2) (num_conn F))
          (ord_succ (ord_max alpha1 alpha2))
          (cut_cad (lor C E) F D d1 d2 alpha1 alpha2
            (associativity_2' P1)
            (demorgan2_sub_ptree P2 E F (lor_ind (1) (non_target D)))))
        (demorgan1_sub_ptree P2 E F (lor_ind (1) (non_target D))))

| _ => P
end.
*)




(* Define cut_elimination, an operation on ptrees *)
(* *)
Fixpoint cut_elimination (P : ptree) : ptree :=
match ptree_ord P with
| Zero => cut_elimination_0 P
| cons a n b =>
  (match P with
  | cut_cad C A D d1 d2 alpha1 alpha2 P1 P2 =>
    (match A with
    | atom a => cut_elimination_atom P
    | neg E => cut_elimination_neg P
    | lor E F => cut_elimination_lor P
    | univ n E => P
    end)
  | deg_up d P' => cut_elimination P'
  | ord_up alpha P' => cut_elimination P'
  | _ => P
  end)
end.

Fixpoint cut_last (P : ptree) : bool := 
match P with
| cut_ca C A d1 d2 alpha1 alpha2 P1 P2 => true

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 => true

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2 => true

| _ => false
end.


(*
###############################################################################
Section 12:
Here we prove that if P is a valid ptree with ordinal alpha and degree d+1,
then cut_elimination(P) is a valid ptree with ordinal 2^alpha and degree d
###############################################################################
*)
(* *)


(*Lemmas I needed*)
Lemma formula_sub_ind_1 : forall (A B : formula),
(subst_ind_fit A (1) = true) -> formula_sub_ind A A B (1) = B.
Proof.
intros.
destruct A.
- simpl. rewrite eq_atom_refl. auto.
- simpl. rewrite eq_f_refl. auto.
- inversion H.
- simpl. rewrite eq_f_refl. rewrite eq_nat_refl. auto.
Qed.

Theorem good_replace1: forall f g r , (subst_ind_fit r (1) = true) -> formula_sub_ind (lor f r) r g (lor_ind (non_target f) (1)) = lor f g.
Proof.
intros.
rewrite formula_sub_ind_lor.
- rewrite (formula_sub_ind_1 _ g H). rewrite non_target_sub. auto.
- rewrite non_target_fit. auto.
Qed.

Theorem good_replace2: forall f g r, (subst_ind_fit r (1) = true) -> formula_sub_ind (lor r f) r g (lor_ind (1) (non_target f)) = lor g f.
Proof.
intros.
rewrite formula_sub_ind_lor.
- rewrite (formula_sub_ind_1 _ g H). rewrite non_target_sub. auto.
- rewrite non_target_fit. rewrite H. auto.
Qed.

(*Morgans Work which I am editing*)
Theorem cut_elimination_formula : forall (P : ptree),
  valid P -> ptree_formula (cut_elimination P) = ptree_formula P.
Proof.
intros. induction P.
- simpl. destruct (ptree_ord P); simpl; auto. apply IHP. destruct X as [X1 X2]. apply X2.
- simpl. destruct o; simpl; auto. apply IHP. destruct X as [[X1 X2] X3]. apply X2.
- simpl. auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct (ord_succ o); simpl; auto.
- simpl. destruct (ord_succ (ord_max o o0)); simpl; auto.
- simpl. destruct (ord_succ (ord_max o o0)); simpl; auto.
- simpl. destruct (ord_succ o); simpl; auto.
- simpl. destruct (ord_succ o); simpl; auto.
- simpl. destruct (ord_succ o); simpl; auto.
- simpl. destruct (ord_succ o); simpl; auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct (ord_succ (ord_max o o0)); simpl; auto.
- simpl. destruct (ord_succ (ord_max o o0)); simpl; auto.
- simpl. destruct (ord_succ (ord_max o o0)). simpl. auto.
  destruct f0.
  + destruct (correct_a a).
   * auto.
   * auto.
  + case (eq_nat (max (max n0 n) (S (num_conn (f0)))) (S (num_conn f0))); auto. 
  + unfold ptree_formula. unfold contraction_help. simpl. rewrite eq_f_refl. auto.
  + auto.
Qed.

(*
Theorem cut_elimination_ord_aux : forall (P : ptree),
  valid P -> ord_lt (ptree_ord P) (ptree_ord (cut_elimination P)) \/ (cut_elimination P) = P.
Proof.
Admitted.
*)
Theorem cut_elimination_ord : forall (P : ptree),
  valid P -> ord_lt (ptree_ord (cut_elimination P)) (ord_2_exp (ptree_ord P)).
Proof.
Admitted.
(*
intros. induction P.
  - simpl. destruct (ptree_ord P) eqn:O.
   + simpl. rewrite O. apply ord_ltb_lt. auto.
   + destruct X as [X1 X2]. pose proof (IHP X2) as Y1. destruct (cut_elimination_ord_aux P X2) as [Y2 | Y2].
     * apply ord_lt_ltb in Y2. apply ord_lt_ltb in Y1. pose proof (ord_ltb_trans _ _ _ Y2 Y1). apply ord_ltb_lt. auto.
     * rewrite Y2 in Y1. auto.
  - admit.
  - simpl. apply ord_ltb_lt. auto.
  - destruct X as  [[[X1 X2] X3] X4]. pose proof (IHP X2) as Y1. destruct (cut_elimination_ord_aux P X2) as [Y2 | Y2].
    + destruct o.
     * simpl.  apply ord_ltb_lt. auto.
     * apply ord_lt_ltb in Y2. apply ord_lt_ltb in Y1. pose proof (ord_ltb_trans _ _ _ Y2 Y1) as Y3. apply ord_ltb_lt. simpl. auto. apply Y3.  admit. (*apply ord_2_exp_fp.*)
    * rewrite Y2 in Y1. auto.
  - simpl. destruct o. simpl. apply ord_ltb_lt. auto.
    destruct X as [[[X1 X2] X3] X4]. pose proof (IHP X2). assert (ord_lt (ptree_ord P) (ptree_ord (cut_elimination P))).
    admit. apply ord_lt_ltb in H. apply ord_lt_ltb in H0. pose proof (ord_ltb_trans _ _ _ H0 H). apply ord_ltb_lt. unfold ptree_ord. admit. (*apply ord_2_exp_fp.*)
    - simpl. destruct o. simpl. apply ord_ltb_lt. auto.
    destruct X as [[[X1 X2] X3] X4]. pose proof (IHP X2). assert (ord_lt (ptree_ord P) (ptree_ord (cut_elimination P))).
    admit. apply ord_lt_ltb in H. apply ord_lt_ltb in H0. pose proof (ord_ltb_trans _ _ _ H0 H). apply ord_ltb_lt. unfold ptree_ord. admit. (*apply ord_2_exp_fp.*)
    - simpl. destruct o. simpl. apply ord_ltb_lt. auto.
    destruct X as [[[X1 X2] X3] X4]. pose proof (IHP X2). assert (ord_lt (ptree_ord P) (ptree_ord (cut_elimination P))).
    admit. apply ord_lt_ltb in H. apply ord_lt_ltb in H0. pose proof (ord_ltb_trans _ _ _ H0 H). apply ord_ltb_lt. unfold ptree_ord. admit. (*apply ord_2_exp_fp.*)
    - simpl. destruct o. simpl. apply ord_ltb_lt. auto.
    destruct X as [[[X1 X2] X3] X4]. pose proof (IHP X2). assert (ord_lt (ptree_ord P) (ptree_ord (cut_elimination P))).
    admit. apply ord_lt_ltb in H. apply ord_lt_ltb in H0. pose proof (ord_ltb_trans _ _ _ H0 H). apply ord_ltb_lt. unfold ptree_ord. admit. (*apply ord_2_exp_fp.*)
    - simpl. destruct o. simpl. apply ord_ltb_lt. auto.
    destruct X as [[[X1 X2] X3] X4]. pose proof (IHP X2). assert (ord_lt (ptree_ord P) (ptree_ord (cut_elimination P))).
    admit. apply ord_lt_ltb in H. apply ord_lt_ltb in H0. pose proof (ord_ltb_trans _ _ _ H0 H). apply ord_ltb_lt. unfold ptree_ord. admit. (*apply ord_2_exp_fp.*)
    - simpl. destruct o. simpl. apply ord_ltb_lt. auto.
    destruct X as [[[X1 X2] X3] X4]. pose proof (IHP X2). assert (ord_lt (ptree_ord P) (ptree_ord (cut_elimination P))).
    admit. apply ord_lt_ltb in H. apply ord_lt_ltb in H0. pose proof (ord_ltb_trans _ _ _ H0 H). apply ord_ltb_lt. unfold ptree_ord. admit. (*apply ord_2_exp_fp.*)
    - simpl. destruct o. simpl. apply ord_ltb_lt. auto.
    destruct X as [[[X1 X2] X3] X4]. pose proof (IHP X2). assert (ord_lt (ptree_ord P) (ptree_ord (cut_elimination P))).
    admit. apply ord_lt_ltb in H. apply ord_lt_ltb in H0. pose proof (ord_ltb_trans _ _ _ H0 H). apply ord_ltb_lt. unfold ptree_ord. admit. (*apply ord_2_exp_fp.*)
    - simpl. destruct o. simpl. apply ord_ltb_lt. auto.
    destruct X as [[[X1 X2] X3] X4]. pose proof (IHP X2). assert (ord_lt (ptree_ord P) (ptree_ord (cut_elimination P))).
    admit. apply ord_lt_ltb in H. apply ord_lt_ltb in H0. pose proof (ord_ltb_trans _ _ _ H0 H). apply ord_ltb_lt. unfold ptree_ord. admit. (*apply ord_2_exp_fp.*)
    - simpl. destruct o. simpl. apply ord_ltb_lt. auto.
    destruct X as [[[X1 X2] X3] X4]. pose proof (IHP X2). assert (ord_lt (ptree_ord P) (ptree_ord (cut_elimination P))).
    admit. apply ord_lt_ltb in H. apply ord_lt_ltb in H0. pose proof (ord_ltb_trans _ _ _ H0 H). apply ord_ltb_lt. unfold ptree_ord. admit. (*apply ord_2_exp_fp.*)
  - simpl. destruct o; simpl; auto.
  - simpl. destruct o; simpl; auto.
  - simpl. destruct o; simpl; auto.
  - simpl. destruct o; simpl; auto.
  - simpl. destruct o; simpl; auto.
  - simpl. destruct (ord_max o o0); simpl; auto.
  - simpl. destruct (ord_max o o0); simpl; auto.
  - simpl. destruct o; simpl; auto.
  - simpl. destruct o; simpl; auto.
  - simpl. destruct o; simpl; auto.
  - simpl. destruct o; simpl; auto.
  - simpl. destruct o; simpl; auto.
  - simpl. destruct o; simpl; auto.
  - simpl. destruct (ord_succ (ord_max o o0)); simpl; auto.
  - simpl. destruct (ord_succ (ord_max o o0)); simpl; auto.
  - simpl. destruct (ord_succ (ord_max o o0)). simpl. auto.
    destruct f0.
    + destruct (correct_a a).
     * auto.
     * auto.
    + auto.
    + unfold ptree_formula. unfold contraction_help. simpl. rewrite eq_f_refl. auto.
    + auto.
Admitted.
*)

Theorem cut_elimination_deg : forall (P : ptree),
  valid P -> (lt_nat (ptree_deg (cut_elimination P)) (ptree_deg P) = true) + ((cut_elimination P) = P).
Proof.
intros. induction P.
  - left. destruct X as [X1 X2]. pose proof (IHP X2). destruct (ptree_ord P) eqn:F; simpl; rewrite F; try apply (lt_nat_decid_conv (ptree_deg P) _ X1). destruct H. apply (lt_nat_trans _ _ _ e (lt_nat_decid_conv (ptree_deg P) _ X1)). rewrite e. apply (lt_nat_decid_conv (ptree_deg P) _ X1).
  - admit. (*destruct X as [X1 X2]. destruct o; simpl. apply zero_minimal in X1. contradiction. right. auto.*)
  - admit.
  - 
Admitted.

Theorem cut_elimination_valid : forall (P : ptree),
  valid P -> valid (cut_elimination P).
Proof.
  intros. induction P.
- simpl. destruct X. destruct (ptree_ord P); simpl; auto.
- simpl. destruct o; simpl; simpl in X; destruct X as [[X1 X2] X3]; auto.
- simpl. auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct (ord_succ o); simpl; auto.
- simpl. destruct (ord_succ (ord_max o o0)); simpl; auto.
- simpl. destruct (ord_succ (ord_max o o0)); simpl; auto.
- simpl. destruct (ord_succ o); simpl; auto.
- simpl. destruct (ord_succ o); simpl; auto.
- simpl. destruct (ord_succ o); simpl; auto.
- simpl. destruct (ord_succ o); simpl; auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct o; simpl; auto.
- simpl. destruct (ord_succ (ord_max o o0)); simpl; auto.
- simpl. destruct (ord_succ (ord_max o o0)); simpl; auto.
- simpl. destruct (ord_succ (ord_max o o0)) eqn:F. simpl. auto.
  destruct f0.
  + case (correct_a a) eqn:H.
   * simpl. simpl in X. destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8].
     pose proof (provable_closed' P4 (lor f (atom a)) X2 X1) as Y1.
     simpl in Y1. apply and_bool_prop in Y1. destruct Y1 as [Y1 Y2].
     pose proof (provable_closed' P5 (lor (neg (atom a)) f1) X4 X3) as Z1.
     simpl in Z1. apply and_bool_prop in Z1. destruct Z1 as [Z1 Z2].
     repeat split; auto.
     { pose proof (formula_sub_ptree_formula_neg P5 a f1 X4 (lor_ind (1) (non_target f1))). rewrite H0.
       rewrite X3. apply good_replace2. auto. }
     { apply formula_sub_valid_neg; simpl; auto. apply correct_correctness in H. unfold incorrect_a. rewrite H. auto. rewrite X3. simpl. apply non_target_fit. }
     { rewrite X6. apply eq_sym. apply formula_sub_ptree_deg_neg. auto. }
     { rewrite X8. apply eq_sym. apply formula_sub_ptree_ord_neg. auto. }
   * simpl. simpl in X. destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8].
     pose proof (provable_closed' P4 (lor f (atom a)) X2 X1) as Y1.
     simpl in Y1. apply and_bool_prop in Y1. destruct Y1 as [Y1 Y2].
     pose proof (provable_closed' P5 (lor (neg (atom a)) f1) X4 X3) as Z1.
     simpl in Z1. apply and_bool_prop in Z1. destruct Z1 as [Z1 Z2].
     repeat split; auto.
     { pose proof (formula_sub_ptree_formula_atom P4 a f X2 (lor_ind (non_target f) (1) )). rewrite H0.
       rewrite X1. apply good_replace1. auto. }
     { apply formula_sub_valid_atom; simpl; auto. rewrite X1. simpl. apply and_bool_symm. apply non_target_fit. }
     { rewrite X5. apply eq_sym. apply formula_sub_ptree_deg_atom. auto. }
     { rewrite X7. apply eq_sym. apply formula_sub_ptree_ord_atom. auto. }
  + case (eq_nat (max (max n0 n) (S (num_conn f0))) (S (num_conn f0))) eqn:Hd.
    * simpl. simpl in X. destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8].
      repeat split; auto.
      { apply nat_eq_decid in Hd. rewrite Hd. lia. }
      { pose proof (dub_neg_ptree_formula P5 f0 X4 (lor_ind (1) (non_target f1))). rewrite H.
       rewrite X3. unfold dub_neg_sub_formula. apply good_replace2. auto. }
      { apply dub_neg_valid. auto. rewrite X3. simpl. apply non_target_fit. }
      { rewrite X6. apply eq_sym. apply dub_neg_ptree_deg. auto. }
      { rewrite X8. apply eq_sym. apply dub_neg_ptree_ord. auto. }
      { rewrite <- F. rewrite ord_max_symm. reflexivity. }
    * simpl. simpl in X. destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8].
      repeat split; auto.
      { pose proof (dub_neg_ptree_formula P5 f0 X4 (lor_ind (1) (non_target f1))). rewrite H.
        rewrite X3. unfold dub_neg_sub_formula. apply good_replace2. auto. }
      { apply dub_neg_valid. auto. rewrite X3. simpl. apply non_target_fit. }
      { rewrite X6. apply eq_sym. apply dub_neg_ptree_deg. auto. }
      { rewrite X8. apply eq_sym. apply dub_neg_ptree_ord. auto. }
      { pose (max_lem2 _ _ (eq_nat_symm' _ _ Hd)). lia. }
      { rewrite <- F. rewrite ord_max_symm. reflexivity. }
  + destruct X as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. unfold contraction_help. simpl. rewrite eq_f_refl. simpl. repeat split; simpl; auto.
    * unfold associativity_2'. rewrite X1. simpl. auto.
    * unfold associativity_2'. rewrite X1. simpl. repeat split; auto.
    * rewrite demorgan2_ptree_formula; auto. rewrite X3. unfold demorgan2_sub_formula. simpl. rewrite non_target_fit. repeat rewrite eq_f_refl. simpl. rewrite non_target_sub'. auto. 
    * apply demorgan2_valid. auto. rewrite X3. simpl. rewrite non_target_fit. auto.
    * unfold associativity_2'. rewrite X1. simpl. auto.
    * rewrite demorgan2_ptree_deg; auto.
    * unfold associativity_2'. rewrite X1. simpl. auto.
    * rewrite demorgan2_ptree_ord; auto.
    * rewrite demorgan1_ptree_formula; auto. rewrite X3. unfold demorgan1_sub_formula. simpl. rewrite non_target_fit. repeat rewrite eq_f_refl. simpl. rewrite non_target_sub'. auto. 
    * apply demorgan1_valid. auto. rewrite X3. simpl. rewrite non_target_fit. auto.
    * rewrite demorgan1_ptree_deg; auto.
    * rewrite demorgan1_ptree_ord; auto.

  + auto.
Qed.

Definition true_lt : ord -> ord -> Prop := (fun (x y : ord) => ord_lt x y /\ nf x /\ nf y).

(*
Theorem ord_acc_last: forall (beta beta' alpha : ord) (n : nat), Acc true_lt (cons alpha n beta) -> Acc true_lt (cons alpha n beta').
Proof.
intros beta. induction beta.
- intros beta'. induction beta'.
  + intros. auto.
  + intros. constructor; intros l [Hl1 [Hl2 Hl3]]. apply H. repeat split; auto. apply ord_ltb_lt. apply (ord_ltb_trans _ _ _ (ord_lt_ltb _ _ Hl1) (ord_lt_ltb _ _ (tail_lt _ _ _  _(zero_lt _ _ _)))).
    destruct H.  admit.
-  


Theorem ord_acc: forall (n n' : nat) (alpha beta : ord), Acc true_lt (cons alpha n' beta) -> Acc true_lt (cons alpha n beta).
Proof.
intros n. induction n.
- intros n'. induction n'.
  + intros. auto.
  + intros. constructor; intros l [Hl1 [Hl2 Hl3]]. apply H. repeat split; auto. apply ord_ltb_lt. apply (ord_ltb_trans _ (cons alpha 0 beta) _ (ord_lt_ltb _ _ Hl1)). apply ord_lt_ltb. apply coeff_lt. lia. apply (nf_scalar _ _ _ _ Hl3).
- intros. constructor; intros l [Hl1 [Hl2 Hl3]]. inversion Hl1.
    * constructor; intros l' [Hl'1 [Hl'2 Hl'3]]. inversion Hl'1.
    * destruct H0,H1,H3,H4. apply (IHn _ _ _ H). repeat split; auto. apply head_lt. auto. apply (nf_scalar _ _ _ _ Hl3).
    * unfold lt in H2. inversion H2.
      { destruct H0,H1,H4,H6. apply (IHn _ _ _ H). }
     destruct H0,H1,H3,H4. apply (IHn _ _ _ H). repeat split; auto. apply coeff_lt. admit. apply (nf_scalar _ _ _ _ Hl3).
    * destruct H0,H1,H3,H4. apply (IHn _ _ _ H). repeat split; auto. apply coeff_lt. auto. apply (nf_scalar _ _ _ _ Hl3).

induction alpha.
- unfold true_lt. induction n.
  + constructor; intros l [Hl1 [Hl2 Hl3]]. inversion Hl3.
    * destruct H2,H3. inversion Hl1.
      { destruct H2. constructor; intros l [Hl'1 [Hl'2 Hl'3]]. inversion Hl'1. }
      { inversion H4. }
      { inversion H4.
        { destruct H3. rewrite H2 in Hl2. inversion Hl2. destruct H5,H7,H9,H10.
           admit. }
        { admit. } }
      { inversion H4. }
    * destruct H1,H2. inversion Hl3. inversion H7.
  + destruct H. apply IHn. apply H. admit.
- unfold true_lt. constructor; intros l Hl.

assert (l = (cons Zero n0 Zero) \/ ord_lt l (cons Zero n0 Zero)).
{ inversion Hl1. right. apply zero_lt. inversion H4. inversion H4. left. destruct H3. rewrite H2 in Hl2. inversion Hl2. reflexivity. inversion H10.
  destruct H3. rewrite H2 in Hl2. inversion Hl2. right. apply coeff_lt. lia. inversion H11. inversion H4. } destruct H2.
{ rewrite H2. constructor; intros l' [Hl'1 [Hl'2 Hl'3]]. apply IHn0.
 apply H. unfold true_lt.

admit. }
{ apply IHn0. auto. apply single_nf. auto. }
+ inversion H3.


Qed.

Theorem ord_acc: forall (alpha beta : ord) (n n' : nat), Acc true_lt (cons alpha n beta) -> Acc true_lt (cons alpha n' beta).
Proof.
intros. induction alpha.
- unfold true_lt. induction n.
  + constructor; intros l [Hl1 [Hl2 Hl3]]. inversion Hl3.
    * destruct H2,H3. inversion Hl1.
      { destruct H2. constructor; intros l [Hl'1 [Hl'2 Hl'3]]. inversion Hl'1. }
      { inversion H4. }
      { inversion H4.
        { destruct H3. rewrite H2 in Hl2. inversion Hl2. destruct H5,H7,H9,H10.
           admit. }
        { admit. } }
      { inversion H4. }
    * destruct H1,H2. inversion Hl3. inversion H7.
  + destruct H. apply IHn. apply H. admit.
- unfold true_lt. constructor; intros l Hl.

assert (l = (cons Zero n0 Zero) \/ ord_lt l (cons Zero n0 Zero)).
{ inversion Hl1. right. apply zero_lt. inversion H4. inversion H4. left. destruct H3. rewrite H2 in Hl2. inversion Hl2. reflexivity. inversion H10.
  destruct H3. rewrite H2 in Hl2. inversion Hl2. right. apply coeff_lt. lia. inversion H11. inversion H4. } destruct H2.
{ rewrite H2. constructor; intros l' [Hl'1 [Hl'2 Hl'3]]. apply IHn0.
 apply H. unfold true_lt.

admit. }
{ apply IHn0. auto. apply single_nf. auto. }
+ inversion H3.


Qed.


Theorem ord_lt_wf: well_founded ord_lt.
Proof.
intros alpha. induction alpha.
- constructor; intros l Hl. inversion Hl.
- constructor; intros l Hl. inversion Hl.
  + constructor; intros l' Hl'. inversion Hl'.
  + destruct H,H2,H3,H0. admit.
  + destruct H,H2,H3,H0. induction n'; inversion H1.
    * destruct H0. admit.
    * destruct H. apply IHn'. apply coeff_lt. lia. lia.
  + destruct H,H2,H3,H0. admit.  
Admitted.


Theorem ord_lt_nf_wf: well_founded (fun (x y : ord) => ord_lt x y /\ nf x /\ nf y).
Proof.
intros alpha. induction alpha.
- constructor; intros l [Hl1 [Hl2 Hl3]]. inversion Hl1.
- constructor; intros l [Hl1 [Hl2 Hl3]]. inversion Hl1.
  + constructor; intros l' [Hl'1 [Hl'2 Hl'3]]. inversion Hl'1.
  + destruct H,H2,H3,H0. 
    * 
   admit.
  + destruct H,H2,H3,H0. induction n'; inversion H1.
    * destruct H0. admit.
    * destruct H. apply IHn'. apply coeff_lt. lia. apply (nf_scalar _ _ _ _ Hl3). lia.
  + destruct H,H2,H3,H0. admit.
  
Qed.
*)

Theorem ord_lt_succ_cases : forall beta alpha, ord_lt alpha (ord_succ beta) -> nf alpha -> nf beta -> alpha = beta \/ ord_lt alpha beta.
Proof.
intros beta. induction beta.
- intros. inversion H; inversion H4. auto.
- intros alpha Hl1 Hl2 Hl3. inversion Hl1.
  * right. apply zero_lt.
  * destruct beta1.
    { inversion H. rewrite H3 in H1. inversion H1. }
    { inversion H. destruct H0,H,H3,H4,H5. right. apply head_lt. auto. }
  * destruct beta1.
    { inversion Hl3.
      { inversion H. destruct H0,H4,H5. rewrite H8 in H1. unfold lt in H1. inversion H1.
        { destruct H4. left. rewrite H7 in Hl2. inversion Hl2. auto. inversion H6. }
        { right. apply coeff_lt. lia. } }
      { inversion H5. } }
    { inversion H. destruct H0,H,H3,H4,H5. right. apply coeff_lt. auto. }
  * destruct beta1.
    { inversion Hl3.
      { inversion H. destruct H0,H4,H5. rewrite H9 in H1. inversion H1. }
      { inversion H5. } }
    { inversion H. destruct H0,H,H4,H5. destruct (IHbeta2 _ H1 (nf_hered_third _ _ _ Hl2) (nf_hered_third _ _ _ Hl3)).
      { destruct H. auto. }
      { right. apply tail_lt. auto. } }
Qed.


Theorem acc_help': forall alpha, Acc true_lt alpha -> Acc true_lt (ord_succ alpha).
Proof.
intros alpha. induction alpha.
- intros. constructor; intros l [Hl1 [Hl2 Hl3]]. inversion Hl1; inversion H2. auto.
- intros. constructor; intros l [Hl1 [Hl2 Hl3]]. destruct (ord_lt_succ_cases _ _ Hl1 Hl2 (ord_nf_succ _ Hl3)).
  + destruct H0. auto.
  + apply H. repeat split; auto. apply ord_nf_succ. auto.
Qed.

Theorem acc_dumb: forall alpha, nf alpha -> Acc true_lt alpha -> forall beta, nf beta -> ord_lt beta alpha -> Acc true_lt beta.
Proof.
intros. apply H0. repeat split; auto.
Qed.

Theorem acc_ord_nat: forall n, Acc true_lt (cons Zero n Zero).
Proof.
intros. induction n.
- constructor; intros l [Hl1 [Hl2 Hl3]]. inversion Hl1. constructor; intros l' [Hl'1 [Hl'2 Hl'3]]. inversion Hl'1. inversion H1. inversion H1. inversion H1.
- pose (acc_help' _ IHn). unfold ord_succ in a. auto.
Qed.

Theorem acc_add : forall alpha beta, Acc true_lt (cons alpha 0 Zero) -> ord_lt beta alpha -> nf alpha -> nf beta -> Acc true_lt (cons alpha 0 beta).
Proof.
intros alpha. induction alpha.
- intros. inversion H0.
- intros beta. induction beta.
  + intros. auto.
  + intros. 


Admitted.


Theorem acc_exp : forall alpha, Acc true_lt (cons alpha 0 Zero) -> nf alpha -> Acc true_lt (cons (ord_succ alpha) 0 Zero).
Proof.
intros alpha. induction alpha.
- intros. simpl. constructor; intros l [Hl1 [Hl2 Hl3]]. inversion Hl1.
  + constructor; intros l' [Hl'1 [Hl'2 Hl'3]]. inversion Hl'1. 
  + inversion H3.
    * destruct H2,H6. inversion Hl2. destruct H7,H11. apply acc_ord_nat. inversion H11.
    * inversion H8.
    * inversion H8.
    * inversion H8.
  + inversion H3.
  + inversion H3.
- intros. destruct alpha1.
  + inversion H0.
    * destruct H3,H4. unfold ord_succ. constructor; intros l [Hl1 [Hl2 Hl3]]. inversion Hl1.
      { constructor; intros l' [Hl'1 [Hl'2 Hl'3]]. inversion Hl'1. }
      { inversion H5.
        { destruct H4,H8. inversion Hl2. apply acc_ord_nat. inversion H13. }
        { inversion H10. }
        { destruct H4,H9. rewrite H8 in *. 
         admit. }
        { inversion H10. } }
      { inversion H5. }
      { inversion H5. }
    * inversion H4.
  + admit.

Qed.


Theorem acc_help: forall (beta alpha : ord) , Acc true_lt alpha -> ord_lt beta alpha -> nf alpha -> nf beta -> Acc true_lt (ord_add alpha beta).
Proof.
intros beta. induction beta.
- intros. induction alpha. inversion H0. unfold ord_add. auto.
- intros alpha. induction alpha. intros. inversion H0. intros. pose (fun x => IHbeta1 _ H x H1 (nf_hered_first _ _ _ H2)).

Theorem acc_help: forall (alpha : ord) (n : nat), Acc true_lt (cons alpha n Zero) -> Acc true_lt (cons alpha (S n) Zero).
Proof.
intros. induction n.
- induction alpha.
  + constructor; intros l [Hl1 [Hl2 Hl3]]. inversion Hl1; inversion H2. constructor; intros l' [Hl'1 [Hl'2 Hl'3]]. inversion Hl'1.
    destruct H1. rewrite H0 in Hl2. inversion Hl2. auto. inversion H8. inversion H6.
  + constructor; intros l [Hl1 [Hl2 Hl3]]. inversion Hl1.
    * constructor; intros l' [Hl'1 [Hl'2 Hl'3]]. inversion Hl'1.
    * destruct H0,H1,H3. apply H. repeat split; auto. apply head_lt. auto. apply (nf_scalar _ _ _ _ Hl3).
    * inversion H2. destruct H1.  admit. inversion H6.
    * inversion H2.
- admit.
Qed.

Theorem acc_help: forall alpha, nf alpha -> Acc true_lt (cons alpha 0 Zero).
Proof.
intros alpha. induction alpha.
- intros. constructor; intros l [Hl1 [Hl2 Hl3]]. inversion Hl1; inversion H2. constructor; intros l' [Hl'1 [Hl'2 Hl'3]]. inversion Hl'1.
- intros. constructor; intros l [Hl1 [Hl2 Hl3]]. inversion Hl1.
  + constructor; intros l' [Hl'1 [Hl'2 Hl'3]]. inversion Hl'1.
  + destruct H1. admit.
  + inversion H2.
  + inversion H2.
Admitted.

Theorem strong_ind_ord: forall (P : ord -> Prop), (forall alpha, (forall beta, true_lt beta alpha -> P beta) -> P alpha) -> forall gamma, P gamma.
Proof.
apply well_founded_ind.
unfold well_founded.
intros. induction a.
- constructor; intros l [Hl1 [Hl2 Hl3]]. inversion Hl1.
- constructor; intros l [Hl1 [Hl2 Hl3]]. inversion Hl1.
  + admit.
  + destruct H0,H,H2,H3. apply (acc_help _ IHa1). repeat split; auto. apply head_lt. auto. apply single_nf. apply (nf_hered_first _ _ _ Hl3).
  + destruct H0,H,H2,H3. apply (acc_help _ IHa1). repeat split; auto. apply head_lt. auto. apply single_nf. apply (nf_hered_first _ _ _ Hl3).

Qed.


(*


Lemma ord_max_0 : forall alpha beta, ord_max alpha beta = Zero -> alpha = Zero /\ beta = Zero.
Admitted.


Lemma ord_max_split : forall alpha beta gamma, ord_lt (ord_max alpha beta) gamma -> ord_lt alpha gamma /\ ord_lt beta gamma.
Admitted.

*)

Lemma one_nf : nf (cons Zero 0 Zero).
Proof.
assert (cons Zero 0 Zero = nat_ord 1). auto.
rewrite H.
apply nf_nat.
Qed.

Lemma ord_succ_non_Zero : forall alpha, ord_eqb (ord_succ alpha) Zero = false.
Proof.
intros. induction alpha. auto. simpl. destruct alpha1. auto. auto.
Qed.

Lemma ord_lt_one : forall alpha, ord_lt alpha (nat_ord 1) -> alpha = Zero.
Proof.
intros. induction alpha. auto.
inversion H; inversion H1.
Qed.

(*

(*Lemma w_nf :

Lemma w_fp : *)

(*
The inductive proof here is quite similar with LEM, and Q1,Q2,Q3
are meant to break this up. *)
(* *)
Definition C1 (P : ptree) : Type := forall (alpha : ord) (d : nat) (A : formula),
  P_proves P A (S d) alpha ->
  provable A d (ord_2_exp alpha).

Definition C2 (P : ptree) (alpha : ord) : Type := ptree_ord P = alpha -> C1 P.

Definition C3 (alpha : ord) : Type := forall (P : ptree), C2 P alpha.

Lemma C3_strongind_aux :
  C3 Zero ->
  (forall alpha,
    ((forall beta, ord_lt beta alpha -> C3 beta) -> C3 alpha)) ->
  (forall beta gamma, ord_lt gamma beta -> C3 gamma).
Proof.
intros. induction gamma as [| n' IHn' ].
- auto. 
- apply X0. intros. pose (X0 gamma1).
  destruct H0 as [H1 | H1].
  + rewrite H1. apply X0. apply IHn'.
  + apply IHn'. apply H1.
Qed.
Admitted.

Lemma C3_strongind :
  C3 Zero ->
  (forall n,
    ((forall m, ord_lt m n -> C3 m) -> C3 n)) ->
  (forall n, C3 n).
Proof. intros. apply (C3_strongind_aux X X0 (ord_succ n) _). apply ord_succ_monot. Qed.

Lemma C3_0 : C3 Zero.
Proof.
unfold C3, C2, C1. intros.
unfold provable. unfold P_proves.
destruct X as [[[H1 H2] H3] H4].

induction P; rewrite H in *.
+ exists (ord_up (ord_2_exp Zero) P). simpl in H1,H4,H. destruct H2 as [H2a H2b]. repeat split; auto. apply ord_ltb_lt. rewrite H. auto. apply one_nf. simpl. simpl in H3. lia. rewrite <- H4. auto.
+ destruct H2. destruct p. simpl in H. rewrite H in o0. apply ord_lt_ltb in o0. destruct H4. destruct (ptree_ord P) in o0; inversion o0.
+ exists (ord_up (ord_2_exp Zero) (node f)). destruct H4. repeat split; simpl; auto. apply ord_ltb_lt. auto. apply one_nf. lia.
+ destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. rewrite X3 in *. rewrite X4 in *. destruct (IHP (lor f f0) d (X1,X2,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
  exists (exchange_ab f f0 (ptree_deg T) (ptree_ord T) T). repeat split; auto.
+ destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. rewrite X3 in *. rewrite X4 in *. destruct (IHP _ _ (X1,X2,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
  exists (exchange_cab f f0 f1 (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
+ destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. rewrite X3 in *. rewrite X4 in *. destruct (IHP _ _ (X1,X2,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
  exists (exchange_abd f f0 f1 (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
+ destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. rewrite X3 in *. rewrite X4 in *. destruct (IHP _ _ (X1,X2,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
  exists (exchange_cabd f f0 f1 f2 (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
+ destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. rewrite X3 in *. rewrite X4 in *. destruct (IHP _ _ (X1,X2,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
  exists (contraction_a f (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
+ destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. rewrite X3 in *. rewrite X4 in *. destruct (IHP _ _ (X1,X2,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
  exists (contraction_ad f f0 (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
+ destruct H2 as [[[[X1 X2] X3] X4] X5]. simpl in H3,H4. rewrite X4 in *. rewrite X5 in *. destruct (IHP _ _ (X1,X3,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
  exists (weakening_ad f f0 (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
+ destruct H2 as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. simpl in H3,H4. rewrite X5 in *. rewrite X6 in *. rewrite X7 in *. rewrite X8 in *. apply max_m_n in H3. destruct H3 as [Z1 Z2].
  apply ord_max_0 in H4. destruct H4 as [Z3 Z4]. destruct (IHP1 _ _ (X1,X2,Z1,Z3)) as [T [[[Y1 Y2] Y3] Y4]].
  destruct (IHP2 _ _ (X3,X4,Z2,Z4)) as [T' [[[Y1' Y2'] Y3'] Y4']].
  exists (demorgan_ab f f0 (ptree_deg T) (ptree_deg T') (ptree_ord T) (ptree_ord T') T T'). repeat split; simpl; auto. lia. rewrite Y4,Y4'. auto.
+ destruct H2 as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. simpl in H3,H4. rewrite X5 in *. rewrite X6 in *. rewrite X7 in *. rewrite X8 in *. apply max_m_n in H3. destruct H3 as [Z1 Z2].
  apply ord_max_0 in H4. destruct H4 as [Z3 Z4]. destruct (IHP1 _ _ (X1,X2,Z1,Z3)) as [T [[[Y1 Y2] Y3] Y4]].
  destruct (IHP2 _ _ (X3,X4,Z2,Z4)) as [T' [[[Y1' Y2'] Y3'] Y4']].
  exists (demorgan_abd f f0 f1 (ptree_deg T) (ptree_deg T') (ptree_ord T) (ptree_ord T') T T'). repeat split; simpl; auto. lia. rewrite Y4,Y4'. auto.
+ destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. rewrite X4 in *. rewrite X3 in *. destruct (IHP _ _ (X1,X2,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
  exists (negation_a f (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
+ destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. rewrite X4 in *. rewrite X3 in *. destruct (IHP _ _ (X1,X2,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
  exists (negation_ad f f0 (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
+ destruct H2 as [[[[X1 X2] X3] X4] X5]. simpl in H3,H4. rewrite X4 in *. rewrite X5 in *. destruct (IHP _ _ (X1,X3,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
  exists (quantification_a f n t (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
+ destruct H2 as [[[[X1 X2] X3] X4] X5]. simpl in H3,H4. rewrite X4 in *. rewrite X5 in *. destruct (IHP _ _ (X1,X3,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
  exists (quantification_ad f f0 n t (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
+ unfold valid in H2. fold valid in H2. simpl in H1,H3,H4. rewrite <- H1, H4 in *. 
  assert (forall m : nat,
   (ptree_formula (p m) = substitution f n (represent m)) * valid (p m) *
   (S d >= ptree_deg (p m)) * (ptree_ord (p m) = Zero)).
   { intros m. destruct (H2 m) as [[[X1 X2] X3] X4]. repeat split; simpl; auto. lia. }
  pose proof (fun m => X m (substitution f n (represent m)) d (X0 m)).
  exists (w_rule_a f n d (ord_2_exp Zero) (fun m => projT1 (X1 m))). repeat split;
  try destruct (X1 m) as [T [[[Y1 Y2] Y3] Y4]]; simpl; auto.
+ unfold valid in H2. fold valid in H2. simpl in H1,H3,H4. rewrite <- H1, H4 in *. 
  assert (forall m : nat,
   (ptree_formula (p m) = lor (substitution f n (represent m)) f0) * valid (p m) *
   (S d >= ptree_deg (p m)) * (ptree_ord (p m) = Zero)).
   { intros m. destruct (H2 m) as [[[X1 X2] X3] X4]. repeat split; simpl; auto. lia. }
  pose proof (fun m => X m (lor (substitution f n (represent m)) f0) d (X0 m)).
  exists (w_rule_ad f f0 n d (ord_2_exp Zero) (fun m => projT1 (X1 m))). repeat split;
  try destruct (X1 m) as [T [[[Y1 Y2] Y3] Y4]]; simpl; auto.
+ inversion H4. destruct (ord_max o o0) in H0. inversion H0. simpl in H0. destruct o1_1 in H0. inversion H0. inversion H0.
+ inversion H4. destruct (ord_max o o0) in H0. inversion H0. simpl in H0. destruct o1_1 in H0. inversion H0. inversion H0.
+ inversion H4. destruct (ord_max o o0) in H0. inversion H0. simpl in H0. destruct o1_1 in H0. inversion H0. inversion H0.
Qed.


Lemma Q3_inductive : forall n, (forall m, m <= n -> Q3 m) -> Q3 (S n).
Proof.
unfold Q3,Q2, Q1. intros.
destruct A as [| B | B C | m B].
- inversion H0.
- inversion H0. simpl. apply negation2. apply exchange1.
  apply (H n (le_refl n) B H4 n0 t s); auto. apply equ_symm,H1.
- destruct (free_list_lor B C n0 H2) as [HB HC].
  destruct (num_conn_lor _ _ _ H0) as [HB' HC'].
  destruct (correct_closed_t _ _ H1) as [Hs Ht].
  simpl. apply (demorgan2 _ _ _ 0 0 Zero Zero).
  + apply associativity1. apply exchange1. apply weakening.
    * destruct HC as [HC | HC].
      { apply (one_var_free_lemma _ _ _ Ht HC). }
      { rewrite closed_subst_eq; apply HC. }
    * destruct HB as [HB | HB].
      { apply (H (num_conn B) HB' B (eq_refl (num_conn B)) n0 s t H1 HB). }
      { rewrite closed_subst_eq, closed_subst_eq; auto. apply (LEM B HB). }
  + apply associativity1. apply exchange2. apply exchange1. apply weakening.
    * destruct HB as [HB | HB].
      { apply (one_var_free_lemma _ _ _ Ht HB). }
      { rewrite closed_subst_eq; apply HB. }
    * destruct HC as [HC | HC].
      { apply (H (num_conn C) HC' C (eq_refl (num_conn C)) n0 s t H1 HC). }
      { rewrite closed_subst_eq, closed_subst_eq; auto. apply (LEM C HC). }
- apply exchange1. inversion H0.
  simpl. pose proof (univ_free_var _ _ _ H2) as Heq. rewrite Heq.
  apply w_rule2. intros k. apply exchange1.
  apply (quantification2 _ _ _ (represent k)).
  + apply repr_closed.
  + destruct (correct_closed_t _ _ H1) as [Hs Ht].
    rewrite (substitution_order B m n0 s _ Hs (repr_closed k) Heq).
    rewrite (substitution_order B m n0 t _ Ht (repr_closed k) Heq).
    apply (H n (le_refl n) (substitution B m (represent k))); auto.
    * rewrite num_conn_sub. auto.
    * apply free_list_univ_sub; auto. apply repr_closed.
Qed.

Lemma Q3_lemma : forall n, Q3 n.
Proof. apply Q3_strongind. apply Q3_0. apply Q3_inductive. Qed.

Lemma Q2_lemma : forall (n : nat) (A : formula), Q2 A n.
Proof. apply Q3_lemma. Qed.

Lemma Q1_lemma : forall (A : formula), Q1 A.
Proof.
intros.
pose proof (Q2_lemma) as H.
unfold Q2 in H.
apply (H (num_conn A) A). auto.
Qed.

Lemma LEM_term : forall (A : formula) (n : nat) (s t : term),
  correct_a (equ s t) = true ->
  free_list A = [n] ->
  PA_omega_theorem (lor (neg (substitution A n s)) (substitution A n t))
                   0 Zero.
Proof. apply Q1_lemma. Qed.

*)
Lemma cut_elim_ord_Zero : forall (A : formula) (d : nat),
provable A (S d) Zero -> provable A d (ord_2_exp Zero).
Proof.
unfold provable. unfold P_proves. intros A. induction A.
- intros d [P [[[H1 H2] H3] H4]]. induction P.
  + exists (ord_up (ord_2_exp Zero) P). destruct H2. simpl in H1,H4. repeat split; auto. apply ord_ltb_lt. rewrite H4. auto. apply one_nf. simpl. simpl in H3. lia.
  + destruct H2. destruct p. simpl in H4. rewrite H4 in o0. apply ord_lt_ltb in o0. destruct (ptree_ord P) in o0; inversion o0.
  + exists (ord_up (ord_2_exp Zero) (node f)). repeat split; simpl; auto. apply ord_ltb_lt. auto. apply one_nf. lia.
  + inversion H1.
  + inversion H1.
  + inversion H1.
  + inversion H1.
  + destruct H2 as [[[X1 X2] X3] X4]. exists (ord_up (cons Zero 0 Zero) (node (atom a))). repeat split; simpl; auto. apply zero_lt.
    unfold valid in X2. fold valid in X2. admit. apply single_nf. apply zero_nf. lia.
  + inversion H1.
  + inversion H1.
  + inversion H1.
  + inversion H1.
  + inversion H1.
  + inversion H1.
  + inversion H1.
  + inversion H1.
  + inversion H1.
  + inversion H1.
  + destruct H2 as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. exists (ord_up (cons Zero 0 Zero) (node (atom a))). repeat split; simpl; auto. apply zero_lt.
  
  destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. rewrite X3 in *. rewrite X4 in *. destruct (IHP _ _ (X1,X2,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
    exists (exchange_cab f f0 f1 (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
  + destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. rewrite X3 in *. rewrite X4 in *. destruct (IHP _ _ (X1,X2,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
    exists (exchange_abd f f0 f1 (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
  + destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. rewrite X3 in *. rewrite X4 in *. destruct (IHP _ _ (X1,X2,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
    exists (exchange_cabd f f0 f1 f2 (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
  + destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. rewrite X3 in *. rewrite X4 in *. destruct (IHP _ _ (X1,X2,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
    exists (contraction_a f (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
  + destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. rewrite X3 in *. rewrite X4 in *. destruct (IHP _ _ (X1,X2,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
    exists (contraction_ad f f0 (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
  + destruct H2 as [[[[X1 X2] X3] X4] X5]. simpl in H3,H4. pose (ord_succ_non_Zero o). rewrite H4 in e. inversion e.
  + destruct H2 as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. simpl in H3,H4. pose (ord_succ_non_Zero (ord_max o o0)). rewrite H4 in e. inversion e.
  + destruct H2 as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. simpl in H3,H4. pose (ord_succ_non_Zero (ord_max o o0)). rewrite H4 in e. inversion e.
  + destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. pose (ord_succ_non_Zero o). rewrite H4 in e. inversion e.
  + destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. pose (ord_succ_non_Zero o). rewrite H4 in e. inversion e.
  + destruct H2 as [[[[X1 X2] X3] X4] X5]. simpl in H3,H4. pose (ord_succ_non_Zero o). rewrite H4 in e. inversion e.
  + destruct H2 as [[[[X1 X2] X3] X4] X5]. simpl in H3,H4. pose (ord_succ_non_Zero o). rewrite H4 in e. inversion e.
  + simpl in H4. inversion H4.
  + simpl in H4. inversion H4.
  + simpl in H3,H4. pose (ord_succ_non_Zero (ord_max o o0)). rewrite H4 in e. inversion e.
  + simpl in H3,H4. pose (ord_succ_non_Zero (ord_max o o0)). rewrite H4 in e. inversion e.
  + simpl in H3,H4. pose (ord_succ_non_Zero (ord_max o o0)). rewrite H4 in e. inversion e.

  + exists (ord_up (ord_2_exp Zero) P). destruct H2. simpl in H1,H4. repeat split; auto. apply ord_ltb_lt. rewrite H4. auto. apply one_nf. simpl. simpl in H3. lia.
  + destruct H2. destruct p. simpl in H4. rewrite H4 in o0. apply ord_lt_ltb in o0. destruct (ptree_ord P) in o0; inversion o0.
  + exists (ord_up (ord_2_exp Zero) (node f)). repeat split; simpl; auto. apply ord_ltb_lt. auto. apply one_nf. lia.
  + destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. rewrite X3 in *. rewrite X4 in *.  destruct (IHP (lor f f0) d (X1,X2,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
    exists (exchange_ab f f0 (ptree_deg T) (ptree_ord T) T). repeat split; auto.
  + destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. rewrite X3 in *. rewrite X4 in *. destruct (IHP _ _ (X1,X2,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
    exists (exchange_cab f f0 f1 (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
  + destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. rewrite X3 in *. rewrite X4 in *. destruct (IHP _ _ (X1,X2,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
    exists (exchange_abd f f0 f1 (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
  + destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. rewrite X3 in *. rewrite X4 in *. destruct (IHP _ _ (X1,X2,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
    exists (exchange_cabd f f0 f1 f2 (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
  + destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. rewrite X3 in *. rewrite X4 in *. destruct (IHP _ _ (X1,X2,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
    exists (contraction_a f (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
  + destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. rewrite X3 in *. rewrite X4 in *. destruct (IHP _ _ (X1,X2,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
    exists (contraction_ad f f0 (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
  + destruct H2 as [[[[X1 X2] X3] X4] X5]. simpl in H3,H4. pose (ord_succ_non_Zero o). rewrite H4 in e. inversion e.
  + destruct H2 as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. simpl in H3,H4. pose (ord_succ_non_Zero (ord_max o o0)). rewrite H4 in e. inversion e.
  + destruct H2 as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. simpl in H3,H4. pose (ord_succ_non_Zero (ord_max o o0)). rewrite H4 in e. inversion e.
  + destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. pose (ord_succ_non_Zero o). rewrite H4 in e. inversion e.
  + destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. pose (ord_succ_non_Zero o). rewrite H4 in e. inversion e.
  + destruct H2 as [[[[X1 X2] X3] X4] X5]. simpl in H3,H4. pose (ord_succ_non_Zero o). rewrite H4 in e. inversion e.
  + destruct H2 as [[[[X1 X2] X3] X4] X5]. simpl in H3,H4. pose (ord_succ_non_Zero o). rewrite H4 in e. inversion e.
  + simpl in H4. inversion H4.
  + simpl in H4. inversion H4.
  + simpl in H3,H4. pose (ord_succ_non_Zero (ord_max o o0)). rewrite H4 in e. inversion e.
  + simpl in H3,H4. pose (ord_succ_non_Zero (ord_max o o0)). rewrite H4 in e. inversion e.
  + simpl in H3,H4. pose (ord_succ_non_Zero (ord_max o o0)). rewrite H4 in e. inversion e.
Qed.

Lemma cut_elim_ord_one : forall (P : ptree) (A : formula) (d : nat),
P_proves P A (S d) (cons Zero 0 Zero) -> provable A d (ord_2_exp (cons Zero 0 Zero)).
Proof.

Admitted.
(* Having done the hard work of showing the Cut-elimination algorithm
terminates, we now complete the reasoning for:
'if A is provable, it has a Cut-free proof' *)
(* *)
Lemma cut_elim_aux1 : forall (alpha : ord) (P : ptree) (A : formula) (d : nat),
  P_proves P A (S d) alpha -> provable A d (ord_2_exp alpha).
Proof.
intros alpha. induction alpha.
- apply cut_elim_ord_Zero.
- case (ord_eqb (cons alpha1 n alpha2) (cons Zero 0 Zero)) eqn:O.
    + apply ord_eqb_eq in O. inversion O. apply cut_elim_ord_one.
    + intros P. induction P.
      * intros. destruct X as [[[H1 H2] H3] H4]. simpl in H1. destruct H2 as [X1 X2]. apply IHP; auto. simpl in H3. unfold P_proves. repeat split; auto. lia.
      * intros. destruct X as [[[H1 H2] H3] H4]. simpl in H1. destruct H2 as [[X1 X2] X3]. apply IHP; auto. simpl in H3. unfold P_proves. repeat split; auto. admit.
      * exists (ord_up (ord_2_exp (cons alpha1 n alpha2)) (node f)). destruct X as [[[H1 H2] H3] H4]. repeat split; auto. apply exp_geq_1. rewrite <- H4. apply ptree_ord_nf. auto. apply nf_2_exp. rewrite <- H4. apply ptree_ord_nf. auto. simpl. lia.
      * intros. apply IHP. destruct X as [[[H1 H2] H3] H4]. repeat split; auto.

      (*
      * exists (ord_up (ord_2_exp (nat_ord 1)) P). destruct H2. simpl in H1,H4. repeat split; auto. apply ord_ltb_lt. rewrite H4. 
        assert (nf (nat_ord 1)). rewrite <- O. rewrite <- H4. apply ptree_ord_nf. apply v.
        destruct (ord_2_exp_fp _ H). apply ord_lt_ltb. rewrite O in *. auto. inversion H0.
        apply nf_2_exp. apply nf_nat. simpl. simpl in H3. lia. rewrite O. auto.
      * destruct o; simpl in H4. inversion H4. destruct H2 as [[X1 X2] X3]. destruct H4. rewrite O in X1. apply ord_lt_one in X1.
        { }
      inversion X1. simpl in H1. simpl in H3. (*simpl in H4.*) pose proof (IHP A d (H1,X2,H3, H4)).
      destruct H2. destruct p. simpl in H4. rewrite H4 in o0. apply ord_lt_ltb in o0. destruct (ptree_ord P) in o0; inversion o0.
      * exists (ord_up (ord_2_exp (cons alpha1 n alpha2)) (node f)). repeat split; simpl; auto. pose ord_mult_exp_monot.
      apply ord_ltb_lt. auto. destruct alpha1.
        simpl. unfold nat_ord. admit. simpl. lia.
      * destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. rewrite X3 in *. rewrite X4 in *. destruct (IHP (lor f f0) d (X1,X2,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
        exists (exchange_ab f f0 (ptree_deg T) (ptree_ord T) T). repeat split; auto.
      * destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. rewrite X3 in *. rewrite X4 in *. destruct (IHP _ _ (X1,X2,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
        exists (exchange_cab f f0 f1 (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
      * destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. rewrite X3 in *. rewrite X4 in *. destruct (IHP _ _ (X1,X2,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
        exists (exchange_abd f f0 f1 (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
      * destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. rewrite X3 in *. rewrite X4 in *. destruct (IHP _ _ (X1,X2,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
        exists (exchange_cabd f f0 f1 f2 (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
      * destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. rewrite X3 in *. rewrite X4 in *. destruct (IHP _ _ (X1,X2,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
        exists (contraction_a f (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
      * destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. rewrite X3 in *. rewrite X4 in *. destruct (IHP _ _ (X1,X2,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
        exists (contraction_ad f f0 (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
      * destruct H2 as [[[[X1 X2] X3] X4] X5]. simpl in H3,H4. rewrite X4 in *. rewrite X5 in *. destruct (IHP _ _ (X1,X3,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
        exists (weakening_ad f f0 (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
      * destruct H2 as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. simpl in H3,H4. rewrite X5 in *. rewrite X6 in *. rewrite X7 in *. rewrite X8 in *. apply max_m_n in H3. destruct H3 as [Z1 Z2].
        apply ord_max_0 in H4. destruct H4 as [Z3 Z4]. destruct (IHP1 _ _ (X1,X2,Z1,Z3)) as [T [[[Y1 Y2] Y3] Y4]].
        destruct (IHP2 _ _ (X3,X4,Z2,Z4)) as [T' [[[Y1' Y2'] Y3'] Y4']].
        exists (demorgan_ab f f0 (ptree_deg T) (ptree_deg T') (ptree_ord T) (ptree_ord T') T T'). repeat split; simpl; auto. lia. rewrite Y4,Y4'. auto.
      * destruct H2 as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8]. simpl in H3,H4. rewrite X5 in *. rewrite X6 in *. rewrite X7 in *. rewrite X8 in *. apply max_m_n in H3. destruct H3 as [Z1 Z2].
        apply ord_max_0 in H4. destruct H4 as [Z3 Z4]. destruct (IHP1 _ _ (X1,X2,Z1,Z3)) as [T [[[Y1 Y2] Y3] Y4]].
        destruct (IHP2 _ _ (X3,X4,Z2,Z4)) as [T' [[[Y1' Y2'] Y3'] Y4']].
        exists (demorgan_abd f f0 f1 (ptree_deg T) (ptree_deg T') (ptree_ord T) (ptree_ord T') T T'). repeat split; simpl; auto. lia. rewrite Y4,Y4'. auto.
      * destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. rewrite X4 in *. rewrite X3 in *. destruct (IHP _ _ (X1,X2,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
        exists (negation_a f (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
      * destruct H2 as [[[X1 X2] X3] X4]. simpl in H3,H4. rewrite X4 in *. rewrite X3 in *. destruct (IHP _ _ (X1,X2,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
        exists (negation_ad f f0 (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
      * destruct H2 as [[[[X1 X2] X3] X4] X5]. simpl in H3,H4. rewrite X4 in *. rewrite X5 in *. destruct (IHP _ _ (X1,X3,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
        exists (quantification_a f n t (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
      * destruct H2 as [[[[X1 X2] X3] X4] X5]. simpl in H3,H4. rewrite X4 in *. rewrite X5 in *. destruct (IHP _ _ (X1,X3,H3,H4)) as [T [[[Y1 Y2] Y3] Y4]].
        exists (quantification_ad f f0 n t (ptree_deg T) (ptree_ord T) T). repeat split; simpl; auto.
      * unfold valid in H2. fold valid in H2. simpl in H1,H3,H4. rewrite <- H1, H4 in *. 
        assert (forall m : nat,
         (ptree_formula (p m) = substitution f n (represent m)) * valid (p m) *
         (S d >= ptree_deg (p m)) * (ptree_ord (p m) = Zero)).
         { intros m. destruct (H2 m) as [[[X1 X2] X3] X4]. repeat split; simpl; auto. lia. }
        pose proof (fun m => X m (substitution f n (represent m)) d (X0 m)).
        exists (w_rule_a f n d (ord_2_exp Zero) (fun m => projT1 (X1 m))). repeat split;
        try destruct (X1 m) as [T [[[Y1 Y2] Y3] Y4]]; simpl; auto.
      * unfold valid in H2. fold valid in H2. simpl in H1,H3,H4. rewrite <- H1, H4 in *. 
        assert (forall m : nat,
         (ptree_formula (p m) = lor (substitution f n (represent m)) f0) * valid (p m) *
         (S d >= ptree_deg (p m)) * (ptree_ord (p m) = Zero)).
         { intros m. destruct (H2 m) as [[[X1 X2] X3] X4]. repeat split; simpl; auto. lia. }
        pose proof (fun m => X m (lor (substitution f n (represent m)) f0) d (X0 m)).
        exists (w_rule_ad f f0 n d (ord_2_exp Zero) (fun m => projT1 (X1 m))). repeat split;
        try destruct (X1 m) as [T [[[Y1 Y2] Y3] Y4]]; simpl; auto.
      * inversion H4. destruct (ord_max o o0) in H0. inversion H0. simpl in H0. destruct o1_1 in H0. inversion H0. inversion H0.
      * inversion H4. destruct (ord_max o o0) in H0. inversion H0. simpl in H0. destruct o1_1 in H0. inversion H0. inversion H0.
      * inversion H4. destruct (ord_max o o0) in H0. inversion H0. simpl in H0. destruct o1_1 in H0. inversion H0. inversion H0.
    *)
Admitted.


Lemma cut_elim_aux2 : forall (A : formula) (d : nat),
  {alpha : ord & provable A d alpha} -> {beta : ord & provable A 0 beta}.
Proof.
intros. induction d.
- destruct X as [alpha H]. exists alpha. auto.
- apply IHd. destruct X as [alpha H].
  exists (ord_2_exp alpha). apply cut_elim_aux1. auto.
Qed.


Lemma cut_elim_aux3 : forall (A : formula) (d : nat) (alpha : ord),
  provable A d alpha -> {beta : ord & provable A 0 beta}.
Proof. intros. apply (cut_elim_aux2 A d). exists alpha. auto. Qed.





Fixpoint cut_free (P : ptree) : Type :=
match P with
| deg_up d P' => cut_free P'

| ord_up alpha P' => cut_free P'

| node A => True


| exchange_ab A B d alpha P' => cut_free P'

| exchange_cab C A B d alpha P' => cut_free P'

| exchange_abd A B D d alpha P' => cut_free P'

| exchange_cabd C A B D d alpha P' => cut_free P'

| contraction_a A d alpha P' => cut_free P'

| contraction_ad A D d alpha P' => cut_free P'


| weakening_ad A D d alpha P' => cut_free P'

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2 => (cut_free P1) * (cut_free P2)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2 => (cut_free P1) * (cut_free P2)

| negation_a A d alpha P' => cut_free P'

| negation_ad A D d alpha P' => cut_free P'


| quantification_a A n t d alpha P' => cut_free P'

| quantification_ad A D n t d alpha P' => cut_free P'

| w_rule_a A n d alpha g => forall (m : nat), cut_free (g m)

| w_rule_ad A D n d alpha g => forall (m : nat), cut_free (g m)


| cut_ca C A d1 d2 alpha1 alpha2 P1 P2 => False

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 => False

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2 => False

end.


Lemma cut_elim_aux4 : forall (P : ptree),
  valid P -> ptree_deg P = 0 -> cut_free P.
Proof.
intros. induction P; simpl; auto.
- destruct X as [H1 H2]. simpl in H. rewrite H in H1. lia.
- destruct X as [H1 H2]. simpl in H. apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  simpl in H. rewrite H5 in H. rewrite H6 in H.
  destruct (max_0 _ _ H). split.
  + apply IHP1; auto.
  + apply IHP2; auto.
- destruct X as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  simpl in H. rewrite H5 in H. rewrite H6 in H.
  destruct (max_0 _ _ H). split.
  + apply IHP1; auto.
  + apply IHP2; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- rename f into A. rename p into g. rename n0 into d. rename o into alpha.
  intros. simpl in H. simpl in X. destruct (X m) as [[[H1 H2] H3] H4].
  rewrite H in H3. apply X0; auto.
- rename f into A. rename f0 into D. rename p into g.
  rename n0 into d. rename o into alpha.
  intros. simpl in H. simpl in X. destruct (X m) as [[[H1 H2] H3] H4].
  rewrite H in H3. apply X0; auto.
- simpl in H. apply max_succ_0 in H. auto.
- simpl in H. apply max_succ_0 in H. auto.
- simpl in H. apply max_succ_0 in H. auto.
Qed.




Definition P_proves' (P : ptree) (A : formula) : Type :=
  (ptree_formula P = A) * (valid P) *
  {d : nat & ptree_deg P = d & {alpha : ord & ptree_ord P = alpha}}.







Lemma cut_elim_aux5 : forall (A : formula) (d : nat) (alpha : ord),
  provable A d alpha -> {P : ptree & P_proves' P A & cut_free P}.
Proof.
intros. apply cut_elim_aux3 in X. destruct X as [gamma [P [[[H1 H2] H3] H4]]].
exists P.
- unfold P_proves'. repeat split; auto.
  exists 0; auto. exists gamma; auto.
- apply cut_elim_aux4; auto.
Qed.
































(*
###############################################################################
Section 13: The consistency of PA
###############################################################################
*)
Fixpoint disjunction_of (A E : formula) : bool :=
match A with
| lor B C =>
  (match eq_f B E, eq_f C E with
  | true, true => true
  | true, false => disjunction_of C E
  | false, true => disjunction_of B E
  | false, false => disjunction_of B E && disjunction_of C E
  end)
| _ => eq_f A E
end.

Definition danger : formula := atom (equ zero (succ zero)).

Definition dangerous_disjunct (A : formula) : bool := disjunction_of A danger.
