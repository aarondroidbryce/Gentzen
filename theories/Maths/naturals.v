Require Import Lia.
Require Import Nat.

Open Scope bool_scope.

Notation nat_eqb := Nat.eqb.

Lemma nat_eqb_refl :
    forall (n : nat),
        nat_eqb n n = true.
Proof.
induction n as [| n IH].
- reflexivity.
- apply IH.
Qed.

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
intros n.
induction n.
- auto.
- rewrite <- IHn. auto.
Qed.

Lemma succ_not_eq : forall (n : nat), nat_eqb n (S n) = false.
Proof.
intros. induction n.
- auto.
- rewrite <- IHn. auto.
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

(*
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
*)
(*
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
*)

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

(*
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
*)

Lemma mult1_r : forall (n : nat), n * 1 = n.
Proof.
induction n.
- reflexivity.
- unfold mul. fold mul.
  rewrite IHn.
  reflexivity.
Qed.

(*
Lemma mult_n_Sm : forall (n m : nat), n * S (m) = n * m + n.
Proof.
intros.
induction n.
- rewrite plus_n_0. unfold mul. reflexivity.
- unfold mul. fold mul. rewrite IHn. rewrite plus_comm.
  rewrite <- plus_n_Sm. rewrite <- plus_assoc.
  rewrite plus_n_Sm. rewrite plus_comm. rewrite (plus_comm n).
  rewrite plus_n_Sm. rewrite plus_comm. rewrite plus_assoc.
  rewrite (plus_comm m). reflexivity.
Qed.
*)

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

Lemma ge_type : forall (m n : nat), m >= n -> (m > n) \/ (m = n).
Proof.
intros n m GT.
inversion GT as [EQ | p LT EQ];
destruct EQ.
- right.
  reflexivity.
- unfold ge in GT.
  left.
  apply le_n_S.
  apply LT.
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

(*Lemma exp_succ : forall n, 2^n <> 0. intros. induction n; simpl; lia. Qed.*)

Lemma nat_2_exp_succ_not_one :
    forall n,
      2^(S n) <> 1.
Proof.
induction n.
discriminate. 
unfold pow.
lia.
Qed.

(* Lemma two_mul : forall n, n * 2 = n + n. lia. Qed. *)

(* Lemma nat_max_right_not : forall n m, eq_nat m (max n m) = false -> eq_nat n (max n m) = true.
Proof.
intros n. induction n. intros. rewrite eq_nat_refl in H. inversion H. intros. destruct m. simpl. apply eq_nat_refl. simpl in H. simpl. auto. 
Qed.
*)

(*
Lemma nat_eqb_symm : forall (n m : nat),
  nat_eqb m n = nat_eqb n m.
Proof.
induction n;
destruct m;
try reflexivity.
unfold nat_eqb. fold nat_eqb.
apply IHn.
Qed.
*)

(*Lemma nat_max_symm : forall n m, max n m = max m n.
Proof.
intros.
intros. destruct (nat_semiconnex_bool n m) as [H | [H | H]].
- rewrite (max_split1 _ _ H). rewrite (max_split2 _ _ H). auto.
- rewrite (max_split1 _ _ H). rewrite (max_split2 _ _ H). auto.
- apply nat_eqb_eq in H. destruct H. auto.
Qed.
*)
(*
Lemma nat_max_comm :
    forall n m p,
        max (max n m) p = max n (max m p).
Proof.
intros. destruct (nat_semiconnex_bool n m) as [H | [H | H]].
- rewrite (max_split1 _ _ H). rewrite (max_split1 n); auto. destruct (nat_semiconnex_bool m p) as [H1 | [H1 | H1]].
  + rewrite (max_split1 _ _ H1). apply (nat_ltb_trans _ _ _ H H1).
  + rewrite (max_split2 _ _ H1). auto.
  + apply nat_eqb_eq in H1. destruct H1. rewrite max_n_n. auto.
- rewrite (max_split2 _ _ H). destruct (nat_semiconnex_bool m p) as [H1 | [H1 | H1]].
  + rewrite (max_split1 _ _ H1). auto.
  + rewrite (max_split2 _ _ H1). rewrite (max_split2 _ _ H). refine (max_split2 _ _ _). apply (lt_nat_trans _ _ _ H1 H).
  + apply nat_eqb_eq in H1. destruct H1. rewrite max_n_n. auto.
- apply nat_eqb_eq in H. destruct H. rewrite max_n_n. destruct (nat_semiconnex_bool n p) as [H1 | [H1 | H1]].
  + rewrite (max_split1 _ _ H1). rewrite (max_split1 _ _ H1). auto.
  + rewrite (max_split2 _ _ H1). rewrite max_n_n. auto.
  + apply nat_eqb_eq in H1. destruct H1. rewrite max_n_n. rewrite max_n_n. auto.
Qed.
*)
(*
Lemma nat_max_order : forall n m p, max (max n m) p = max (max n p) m.
Proof.
intros. rewrite (nat_max_symm _ p). rewrite <- (nat_max_comm p). rewrite (nat_max_symm p). auto.
Qed.
*)

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