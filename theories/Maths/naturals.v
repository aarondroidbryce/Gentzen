Require Import Lia.
Require Import Nat.
Notation "b1 && b2" := (andb b1 b2).
Notation "b1 || b2" := (orb b1 b2).

Notation eq_nat := Nat.eqb.

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
  lt_nat n m = true -> lt_nat m n = false.
Proof.
intros. unfold not. intros.
pose proof (lt_nat_trans n).
unfold nat_trans in H0.
specialize H0 with m n.
case (lt_nat m n) eqn:X.
assert (lt_nat n n = true). { apply H0. apply H. auto. }
rewrite (lt_nat_irrefl n) in H1.
inversion H1. auto.
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

Lemma max_split1 : forall (n m : nat), lt_nat n m = true -> max n m = m.
Proof.
intros n. induction n.
- auto.
- intros. destruct m. inversion H. simpl. apply eq_succ. apply IHn. auto.
Qed.

Lemma max_split2 : forall (m n : nat), lt_nat m n = true -> max n m = n.
Proof.
intros m. induction m.
- intros. destruct n; auto.
- intros. destruct n. inversion H. simpl. apply eq_succ. apply IHm. auto. 
Qed.

Lemma max_0 : forall (m n : nat), max m n = 0 -> m = 0 /\ n = 0.
Proof. intros. lia. Qed.

Lemma max_simp0 : forall (n : nat), (max n 0) = n.
Proof.
intros n. induction n; auto.
Qed.

Lemma max_succ_0 : forall (m n : nat), max m (S n) = 0 -> False.
Proof. intros. lia. Qed.

Lemma exp_succ : forall n, 2^n <> 0. intros. induction n; simpl; lia. Qed.

Lemma nat_2_exp_succ_not_one : forall n, 2^(S n) <> 1. intros. induction n. discriminate. simpl. lia. Qed.

Lemma nat_lt_succ : forall n, (n < S n)%nat.
Proof.
auto.
Qed.

Lemma nat_lt_succ_lt : forall n m, (n < m)%nat -> (S n < S m)%nat.
Proof.
lia.
Qed.

Lemma nat_2_exp_monot : forall n m, (n < m)%nat -> (2^n < 2^m)%nat.
Proof.
intros n. induction n.
- intros. induction m. inversion H. simpl. simpl in IHm. destruct m. simpl. lia. lia.
- intros. destruct m. inversion H. inversion H.
  + pose (IHn (S n) (nat_lt_succ _)). simpl in l. simpl. lia.
  + assert (n < m)%nat. lia. pose (IHn m H2). simpl. lia. 
Qed.

Lemma two_mul : forall n, n * 2 = n + n. lia. Qed.

Lemma succ_distrib : forall n m, n * m + m = (S n) * m.
Proof.
intros. induction n. simpl. auto. simpl. lia.
Qed.

Lemma nat_ne_symm : forall n m, eq_nat n m = false -> eq_nat m n = false. intros n. induction n. intros. destruct m. inversion H. auto. intros. destruct m. auto. simpl. auto. Qed.

Lemma nat_max_left_not : forall n m, eq_nat n (max n m) = false -> eq_nat m (max n m) = true.
Proof.
intros n. induction n. intros. simpl. apply eq_nat_refl. intros. destruct m. rewrite eq_nat_refl in H. inversion H. simpl in H. simpl. auto. 
Qed.

Lemma nat_max_right_not : forall n m, eq_nat m (max n m) = false -> eq_nat n (max n m) = true.
Proof.
intros n. induction n. intros. rewrite eq_nat_refl in H. inversion H. intros. destruct m. simpl. apply eq_nat_refl. simpl in H. simpl. auto. 
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

Lemma nat_2_exp_help : forall n m, 2 ^ S (S n) = S m -> S (S n) < m.
Proof.
intros n. induction n.
- intros. inversion H. auto.
- intros. destruct m. pose (nat_2_exp_succ_not_one (S (S n))). lia.
  assert ((S (S m)) = 2^(S (S n)) + 2^(S (S n))). simpl. simpl in H. lia.
  case (2^(S ( S n))) eqn:X. inversion H0.
  assert (n0 + n0 = m). lia.
  pose (IHn n0 (nat_eq_decid _ _(eq_nat_refl _))). lia.
Qed.