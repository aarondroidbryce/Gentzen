Require Import Lia.
Require Import Nat.

Open Scope bool_scope.

Notation nat_eqb := Nat.eqb.
Notation nat_ltb := Nat.ltb.

Lemma nat_eqb_refl :
    forall (n : nat),
        nat_eqb n n = true.
Proof.
induction n as [| n IH].
- reflexivity.
- apply IH.
Qed.

Lemma nat_le_refl :
    forall (n : nat),
        n <= n.
Proof. reflexivity. Qed.

Lemma leb_type :
    forall (n m : nat),
        leb n m = true ->
            n = m \/ n < m.
Proof.
induction n;
intros m GT;
induction m.
- left.
  reflexivity.
- right.
  apply le_n_S.
  apply le_0_n.
- inversion GT.
- unfold lt in *.
  unfold leb in GT; fold leb in GT.
  destruct (IHn _ GT) as [EQ | LT].
  destruct EQ.
  + left.
    reflexivity.
  + right.
    apply le_n_S.
    apply LT.
Qed. 

Lemma nat_ltb_irrefl : forall (n : nat), ltb n n = false.
Proof.
induction n.
- unfold ltb.
  reflexivity.
- rewrite <- IHn.
  unfold ltb.
  reflexivity.
Qed.

Lemma succ_not_eq : forall (n : nat), nat_eqb n (S n) = false.
Proof.
induction n.
- reflexivity.
- rewrite <- IHn.
  reflexivity.
Qed.

Lemma nat_ltb_lt :
    forall (n m : nat),
        ltb n m = true ->
            n < m.
Proof.
induction n;
intros m LTB;
destruct m;
inversion LTB;
apply le_n_S.
- apply le_0_n.
- apply (IHn _ LTB).
Qed.

Lemma nat_lt_ltb :
    forall (n m : nat),
        n < m ->
          ltb n m = true.
Proof.
induction n;
intros m LTB;
destruct m.
- inversion LTB.
- unfold ltb.
  unfold leb.
  reflexivity.
- inversion LTB.
- apply (IHn _ (le_S_n _ _ LTB)).
Qed.

Lemma nat_eqb_eq :
    forall (n m : nat),
        nat_eqb n m = true ->
            n = m.
Proof.
induction n;
intros m EQ;
destruct m;
inversion EQ as [EQ'].
- reflexivity.
- apply (eq_S _ _ (IHn _ EQ')).
Qed.

Lemma nat_ltb_trans :
    forall (n m p : nat),
        ltb n m = true ->
            ltb m p = true ->
                ltb n p = true.
Proof.
induction n;
intros m p LTNM LTMP;
destruct p.
- inversion LTMP.
- reflexivity.
- inversion LTMP.
- destruct m.
  inversion LTNM.
  apply (IHn m _ LTNM LTMP).
Qed.

Lemma nat_ltb_asymm :
    forall (n m : nat),
        ltb n m = true ->
            ltb m n = false.
Proof.
intros n m LT.
case (ltb m n) eqn:IE.
pose proof (nat_ltb_trans _ _ _ LT IE) as Fal.
rewrite nat_ltb_irrefl in Fal.
inversion Fal.
reflexivity.
Qed.

Lemma mult_right_incr'_aux :
    forall (n m p : nat),
        n < m ->
            n + p * (S n) < m + p * (S m).
Proof. induction p; lia. Qed.

Lemma mult_left_incr_aux_aux :
    forall (n m p : nat),
        n < m ->
            p + n * (S p) < p + m * (S p).
Proof. induction p; lia. Qed.

Lemma minus_n_0 : forall (n : nat), n - 0 = n.
Proof. induction n; reflexivity. Qed.

Lemma nat_exp_monot_lem : forall (n : nat), S n < (2 ^ n) + (2 ^ n).
Proof.
induction n.
- apply le_n_S.
  apply le_n.
- unfold pow; fold pow.
  lia.
Qed.

Lemma plus_comm :
    forall (n m : nat),
      n + m = m + n.
Proof.
induction m.
- rewrite plus_O_n.
  rewrite <- plus_n_O.
  reflexivity.
- rewrite <- plus_n_Sm.
  rewrite IHm.
  reflexivity.
Qed.

Lemma plus_assoc :
    forall (n m p : nat),
        n + (m + p) = (n + m) + p.
Proof.
intros n m p.
induction n.
- repeat rewrite plus_O_n.
  reflexivity.
- unfold plus. fold plus.
  rewrite IHn.
  reflexivity.
Qed.

Lemma mult1_r : forall (n : nat), n * 1 = n.
Proof.
induction n.
- reflexivity.
- unfold mul. fold mul.
  rewrite IHn.
  reflexivity.
Qed.

Lemma nat_semiconnex : forall (m n : nat), m < n \/ n < m \/ m = n.
Proof. intros. lia. Qed.

Lemma nat_lt_trans : forall (n n' n'' : nat), n < n' -> n' < n'' -> n < n''.
Proof. intros. lia. Qed.

Lemma nat_semiconnex_bool :
    forall (m n : nat), 
      ltb m n = true \/ ltb n m = true \/ eqb m n = true.
Proof.
intros.
destruct (nat_semiconnex m n) as [LT | [GT | EQ]].
- left.
  apply nat_lt_ltb.
  apply LT.
- right.
  left.
  apply nat_lt_ltb.
  apply GT.
- right.
  right.
  rewrite EQ.
  apply nat_eqb_refl.
Qed.

Definition less (m n : nat) := { z : nat & S (z + m) = n}.

Lemma less_lt :
    forall (m n : nat),
        less m n ->
            m < n.
Proof. intros m n L. destruct L as [p EQ]. lia. Qed.

Theorem nat_semiconnex_type_aux :
    forall (m n : nat),
        (less n m) + (n = m) + (less m n).
Proof.
intros m n.
induction n.
- destruct m.
  + left.
    right.
    reflexivity.
  + left.
    left.
    exists m.
    rewrite plus_n_O.
    reflexivity.
- destruct m.
  + right.
    exists n.
    rewrite plus_n_O.
    reflexivity.
  + destruct IHn as [[IHn | IHn] | IHn].
    * destruct IHn as [p EQ].
      destruct p.
      --  left.
          right.
          apply EQ.
      --  left.
          left.
          exists p.
          rewrite plus_comm.
          rewrite plus_n_Sm.
          rewrite plus_comm.
          rewrite plus_n_Sm in EQ.
          apply EQ.
    * right.
      exists 0.
      apply eq_S.
      symmetry.
      apply IHn.
    * right.
      destruct IHn as [p EQ].
      exists (S p).
      apply eq_S.
      apply EQ.
Qed.

Lemma nat_semiconnex_type :
    forall (m n : nat),
        (m > n) + (m = n) + (n > m).
Proof.
intros m n.
destruct (nat_semiconnex_type_aux m n) as [[GT | EQ] | LT].
- left.
  left.
  apply (less_lt _ _ GT).
- left.
  right.
  symmetry.
  apply EQ.
- right.
  apply (less_lt _ _ LT).
Qed.

Lemma nat_ge_case_type :
    forall (m n : nat),
        m >= n ->
            (m > n) + (m = n).
Proof.
intros m n GE.
destruct (nat_semiconnex_type m n) as [[GT | EQ] | LT].
- left.
  apply GT.
- right.
  apply EQ.
- lia.
Qed.

Lemma max_lem1 :
    forall (m n : nat),
        eqb n (max n m) = false ->
            max n m > n.
Proof.
intros n m NE.
destruct (nat_semiconnex n m) as [LT | [GT | EQ]].
- rewrite max_l in NE.
  rewrite nat_eqb_refl in NE.
  inversion NE.
  apply le_S_n.
  apply le_S.
  apply LT.
- rewrite max_r.
  apply GT.
  apply le_S_n.
  apply le_S.
  apply GT.
- rewrite max_l in NE.
  rewrite nat_eqb_refl in NE.
  inversion NE.
  destruct EQ.
  reflexivity.
Qed.

Lemma max_lem2 :
    forall (m n : nat),
        eqb m (max n m) = false ->
            max n m > m.
Proof.
intros n m NE. destruct (nat_semiconnex n m) as [LT | [GT | EQ]].
- rewrite max_l.
  apply LT.
  apply le_S_n.
  apply le_S.
  apply LT.
- rewrite max_r in NE.
  rewrite nat_eqb_refl in NE.
  inversion NE.
  apply le_S_n.
  apply le_S.
  apply GT.
- rewrite max_r in NE.
  rewrite nat_eqb_refl in NE.
  inversion NE.
  destruct EQ.
  reflexivity.
Qed.

Lemma max_split1 :
    forall (n m : nat),
        ltb n m = true ->
            max n m = m.
Proof.
intros n m LTB.
apply (max_r _ _ (le_S_n _ _ (le_S _ _ (nat_ltb_lt _ _ LTB)))).
Qed.

Lemma max_split2 :
    forall (n m : nat),
        ltb m n = true ->
            max n m = n.
Proof.
intros n m LTB.
apply (max_l _ _ (le_S_n _ _ (le_S _ _ (nat_ltb_lt _ _ LTB)))).
Qed.

Lemma nat_2_exp_not_zero :
    forall n,
        2^n <> 0.
Proof.
induction n;
unfold pow;
fold pow;
lia.
Qed.

Lemma nat_2_exp_succ_not_one :
    forall n,
      2^(S n) <> 1.
Proof.
induction n.
discriminate. 
unfold pow.
lia.
Qed.

Lemma two_mul : forall n, n * 2 = n + n. lia. Qed.

Lemma nat_max_neb_r_eqb_l :
    forall (n m : nat),
        nat_eqb m (max n m) = false ->
            nat_eqb n (max n m) = true.
Proof.
induction n;
intros m EQ.
- unfold max in EQ.
  rewrite nat_eqb_refl in EQ.
  inversion EQ.
- destruct m.
  + unfold max.
    apply nat_eqb_refl.
  + unfold max, nat_eqb in *; fold max nat_eqb in *.
    apply (IHn _ EQ). 
Qed.

Lemma nat_eqb_symm :
    forall (n m : nat),
        nat_eqb m n = nat_eqb n m.
Proof.
induction n;
destruct m;
try reflexivity.
unfold nat_eqb; fold nat_eqb.
apply IHn.
Qed.

Lemma nat_lt_max_shuffle_l :
    forall (s l r e b : nat),
        (max s (max (max l r) e)) < b ->
            max s l < b.
Proof. lia. Qed.

Lemma nat_lt_max_shuffle_r :
    forall (s l r e b : nat),
        (max s (max (max l r) e)) < b ->
            max s r < b.
Proof. lia. Qed.

Lemma nat_lt_max_max_l :
    forall (s l r b : nat),
        (max s (max l r)) < b ->
            max s l < b.
Proof. lia. Qed.

Lemma nat_lt_max_max_r :
    forall (s l r b : nat),
        (max s (max l r)) < b ->
            max s r < b.
Proof. lia. Qed.

Lemma nat_2_exp_non_zero :
    forall n,
        0 < 2^n.
Proof.
induction n; unfold pow, lt.
reflexivity.
fold pow. lia.
Qed.

Lemma nat_lt_mul_S_lt :
    forall (m n p : nat),
        m < n ->
            (m + p * S m < n + p * S n).
Proof.
induction p;
intros LT;
lia.
Qed.