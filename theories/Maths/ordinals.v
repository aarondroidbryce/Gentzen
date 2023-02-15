Add LoadPath "theories/Casteran" as Ordering.
Add LoadPath "theories/Maths" as Maths_Facts.
Add LoadPath "theories/Logic" as Systems.

Require Import Lia.
Require Import Nat.
Require Import Wellfounded.
From Ordering Require Import rpo.
From Maths_Facts Require Import naturals.
From Systems Require Import definitions.

Inductive ord : Set :=
| Zero : ord
| cons : ord -> nat -> ord -> ord.

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

Definition leq (alpha beta : ord) := alpha = beta \/ alpha < beta.
Notation "alpha <= beta" := (leq alpha beta) : cantor_scope.

Lemma ord_semiconnex :
    forall (alpha beta : ord),
        alpha < beta \/ beta < alpha \/ alpha = beta.
Proof.
induction alpha.
- induction beta.
  + right.
    right.
    reflexivity.
  + left.
    apply zero_lt.
- destruct beta.
  + right.
    left.
    apply zero_lt.
  + destruct (IHalpha1 beta1) as [LT | [GT | EQ]].
    * left.
      apply head_lt.
      apply LT.
    * right.
      left.
      apply head_lt.
      apply GT.
    * destruct EQ.
      destruct (nat_semiconnex n n0) as [LT | [GT | EQ]].
      --  left.
          apply coeff_lt.
          apply LT.
      --  right.
          left.
          apply coeff_lt.
          apply GT.
      --  destruct EQ.
          destruct (IHalpha2 beta2) as [LT | [GT | EQ]].
          ++  left.
              apply tail_lt.
              apply LT.
          ++  right.
              left.
              apply tail_lt.
              apply GT.
          ++  destruct EQ.
              right.
              right.
              reflexivity.
Qed.

Lemma cons_lt_aux :
    forall (a a' b b' : ord) (n n' : nat),
        cons a n b < cons a' n' b' ->
            (a < a' \/ (a = a' /\ lt n n') \/ (a = a' /\ n = n' /\ b < b')).
Proof.
intros a a' b b' n n' LT.
inversion LT.
- left.
  apply H0.
- right.
  left.
  split.
  + reflexivity.
  + apply H0.
- right.
  right.
  repeat split.
  apply H0.
Qed.

Lemma ord_lt_trans :
    forall (alpha beta gamma : ord),
        alpha < beta ->
            beta < gamma ->
                alpha < gamma.
Proof.
induction alpha as [| a1 IHa1 an a2 IHa2];
intros beta gamma LTAB LTBG;
destruct gamma as [| g1 gn g2].
1,3 : inversion LTBG.
1 : apply zero_lt.
1 : destruct beta as [| b1 bn b2].
- inversion LTAB.
- destruct (cons_lt_aux _ _ _ _ _ _ LTAB) as [LT | [[EQO LT] | [EQO [EQN LT]]]];
  destruct (cons_lt_aux _ _ _ _ _ _ LTBG) as [LT' | [[EQO' LT'] | [EQO' [EQN' LT']]]];
  try destruct EQO; try destruct EQO'; try destruct EQN; try destruct EQN'.
  + apply head_lt.
    apply (IHa1 _ _ LT LT').
  + apply head_lt.
    apply LT.
  + apply head_lt.
    apply LT.
  + apply head_lt.
    apply LT'.
  + apply coeff_lt.
    apply (nat_lt_trans _ _ _ LT LT').
  + apply coeff_lt.
    apply LT.
  + apply head_lt.
    apply LT'.
  + apply coeff_lt.
    apply LT'.
  + apply tail_lt.
    apply (IHa2 _ _ LT LT').
Qed.

Lemma ord_lt_irrefl :
    forall (alpha : ord),
        ~ (alpha < alpha).
Proof.
intros alpha Fal.
induction alpha as [ | a1 IHa1 n a2 IHa2].
- inversion Fal.
- destruct (cons_lt_aux _ _ _ _ _ _ Fal) as [LT | [[EQO LT] | [EQO [EQN LT]]]].
  + apply (IHa1 LT).
  + lia.
  + apply (IHa2 LT).
Qed.

Lemma ord_lt_asymm :
    forall (alpha beta : ord),
        alpha < beta ->
            ~(beta < alpha).
Proof.
intros alpha beta LT GT.
apply (ord_lt_irrefl _ (ord_lt_trans alpha beta alpha LT GT)).
Qed.


(* Here we define Cantor Normal Form, or more accurately, we copy
Pierre Casteran's definition *)
(* *)
Inductive nf : ord -> Prop :=
| zero_nf : nf Zero
| single_nf : forall a n,
                  nf a ->
                      nf (cons a n Zero)
| cons_nf : forall a n a' n' b,
                a' < a ->
                    nf a ->
                        nf (cons a' n' b) ->
                            nf (cons a n (cons a' n' b)).

Definition nat_ord (n : nat) : ord :=
  match n with
  | O => Zero
  | S n' => cons Zero n' Zero
  end.

Lemma nf_nat :
    forall (n : nat),
        nf (nat_ord n).
Proof.
induction n.
- apply zero_nf.
- apply single_nf.
  apply zero_nf.
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
        (match nat_eqb n n' with
        | false => false
        | true => ord_eqb b b'
        end)
    end)
end.

Fixpoint ord_ltb (alpha beta : ord) : bool :=
match alpha, beta with
| _, Zero => false
| Zero, _ => true
| cons a n b, cons a' n' b' =>
    (match ord_ltb a a', ord_eqb a a' with
    | true, _ => true
    | _, false => false
    | _, true =>
        (match ltb n n', ltb n' n with
        | true, _ => true
        | _, true => false
        | _, _ => ord_ltb b b'
        end)
    end)
end.

Lemma ord_lt_one :
    forall alpha,
        ord_lt alpha (nat_ord 1) ->
            Zero = alpha.
Proof.
intros alpha LT.
induction alpha.
- reflexivity.
- inversion LT;
  inversion H0.
Qed.

Lemma nf_hered_third :
    forall (a b : ord) (n : nat),
        nf (cons a n b) ->
            nf b.
Proof.
intros a b n N.
inversion N.
- apply zero_nf.
- apply H4.
Qed.

Lemma nf_hered_first :
    forall (a b : ord) (n : nat),
        nf (cons a n b) ->
            nf a.
Proof.
intros a b n N.
inversion N.
- apply H0.
- apply H3.
Qed.

Lemma nf_head_zero :
    forall (alpha : ord) (n : nat),
        nf (cons Zero n alpha) ->
            Zero = alpha.
Proof.
intros alpha n NA.
inversion NA.
reflexivity.
inversion H2.
Qed.

Lemma ord_eqb_refl :
    forall (alpha : ord),
        ord_eqb alpha alpha = true.
Proof.
induction alpha.
- reflexivity.
- unfold ord_eqb; fold ord_eqb.
  rewrite IHalpha1.
  rewrite nat_eqb_refl.
  rewrite IHalpha2.
  reflexivity.
Qed.

Lemma ord_ltb_irrefl :
    forall (alpha : ord),
        ord_ltb alpha alpha = false.
Proof.
induction alpha.
- reflexivity.
- unfold ord_ltb; fold ord_ltb.
  rewrite IHalpha1.
  rewrite ord_eqb_refl.
  rewrite nat_ltb_irrefl.
  apply IHalpha2.
Qed.

Lemma ord_lt_ltb :
    forall (alpha beta : ord),
        alpha < beta ->
            ord_ltb alpha beta = true.
Proof.
induction alpha;
intros beta LT;
destruct beta.
- inversion LT.
- reflexivity.
- inversion LT.
- apply cons_lt_aux in LT.
  destruct LT as [LT | [[EQO LT] | [EQO [EQN LT]]]];
  unfold ord_ltb; fold ord_ltb.
  + rewrite IHalpha1.
    reflexivity.
    apply LT.
  + destruct EQO.
    rewrite ord_ltb_irrefl.
    rewrite ord_eqb_refl.
    rewrite (nat_lt_ltb _ _ LT).
    reflexivity.
  + destruct EQO,EQN.
    rewrite ord_ltb_irrefl.
    rewrite ord_eqb_refl.
    rewrite nat_ltb_irrefl.
    apply IHalpha2.
    apply LT.
Qed.

Lemma ord_eqb_eq :
    forall (alpha beta : ord),
        ord_eqb alpha beta = true -> alpha = beta.
Proof.
induction alpha;
intros beta EQ;
destruct beta.
- reflexivity.
- inversion EQ.
- inversion EQ.
- unfold ord_eqb in EQ; fold ord_eqb in EQ.
  case (ord_eqb alpha1 beta1) eqn:EQ1;
  case (nat_eqb n n0) eqn:EQn;
  case (ord_eqb alpha2 beta2) eqn:EQ2;
  try inversion EQ.
  rewrite (IHalpha1 _ EQ1).
  rewrite (IHalpha2 _ EQ2).
  apply nat_eqb_eq in EQn.
  destruct EQn.
  reflexivity.
Qed.

Lemma ord_semiconnex_bool :
    forall (alpha beta : ord),
      ord_ltb alpha beta = true \/ ord_ltb beta alpha = true \/ ord_eqb alpha beta = true.
Proof.
intros alpha beta.
destruct (ord_semiconnex alpha beta) as [LT | [GT | EQ]].
- left.
  apply ord_lt_ltb.
  apply LT.
- right.
  left.
  apply ord_lt_ltb.
  apply GT.
- right.
  right.
  destruct EQ.
  apply ord_eqb_refl.
Qed.

Lemma cons_ltb_aux :
    forall (a a' b b' : ord) (n n' : nat),
        ord_ltb (cons a n b) (cons a' n' b') = true ->
              (ord_ltb a a' = true \/
                  (ord_eqb a a' = true /\ ltb n n' = true) \/
                      (ord_eqb a a' = true /\ n = n' /\ ord_ltb b b' = true)).
Proof.
intros a a' b b' n n' LT.
case (ord_ltb a a') eqn:LT1. 
- left.
  reflexivity.
- unfold ord_ltb in LT; fold ord_ltb in LT.
  right.
  rewrite LT1 in LT.
  case (ord_eqb a a') eqn:EQ1.
  + apply ord_eqb_eq in EQ1.
    destruct EQ1.
    destruct (nat_semiconnex_bool n n') as [LTn | [LTn | EQn]].
    * left.
      repeat split.
      apply LTn.
    * rewrite LTn in LT.
      rewrite (nat_ltb_asymm _ _ LTn) in LT.
      inversion LT.
    * right.
      apply nat_eqb_eq in EQn.
      destruct EQn.
      rewrite nat_ltb_irrefl in LT.
      repeat split.
      apply LT.
  + inversion LT.
Qed.

Lemma ord_ltb_trans :
    forall (alpha beta gamma : ord),
        ord_ltb alpha beta = true ->
            ord_ltb beta gamma = true ->
                ord_ltb alpha gamma = true.
Proof.
induction alpha;
intros beta gamma LTAB LTBG;
destruct gamma;
destruct beta.
1,2,5,6 : inversion LTBG.
1,3 : inversion LTAB.

- reflexivity.
- destruct (cons_ltb_aux _ _ _ _ _ _ LTAB) as [LT | [[EQO LT] | [EQO [EQN LT]]]];
  destruct (cons_ltb_aux _ _ _ _ _ _ LTBG) as [LT' | [[EQO' LT'] | [EQO' [EQN' LT']]]];
  try apply ord_eqb_eq in EQO; try apply ord_eqb_eq in EQO';
  try apply nat_eqb_eq in EQN; try apply nat_eqb_eq in EQN';
  try destruct EQO; try destruct EQO'; try destruct EQN; try destruct EQN';
  unfold ord_ltb; fold ord_ltb;
  try rewrite ord_ltb_irrefl;
  try rewrite ord_eqb_refl;
  try rewrite LT;
  try rewrite LT';
  try reflexivity.  
  + rewrite (IHalpha1 _ _ LT LT').
    reflexivity.
  + rewrite (nat_ltb_trans _ _ _ LT LT').
    reflexivity.
  + rewrite nat_ltb_irrefl.
    apply (IHalpha2 _ _ LT LT').
Qed.

Lemma ord_ltb_asymm :
    forall (alpha beta : ord),
        ord_ltb alpha beta = true ->
            ord_ltb beta alpha = false.
Proof.
intros alpha beta LT.
case (ord_ltb beta alpha) eqn:IE.
- pose proof (ord_ltb_trans alpha beta alpha LT IE) as Fal.
  rewrite (ord_ltb_irrefl alpha) in Fal.
  inversion Fal.
- reflexivity.
Qed.

Lemma ord_ltb_lt :
    forall (alpha beta : ord),
        ord_ltb alpha beta = true ->
            alpha < beta.
Proof.
intros alpha beta LTB.
destruct (ord_semiconnex alpha beta) as [LT | [GT | EQ]].
- apply LT.
- apply ord_lt_ltb in GT.
  apply ord_ltb_asymm in GT.
  rewrite GT in LTB.
  inversion LTB.
- destruct EQ.
  rewrite ord_ltb_irrefl in LTB.
  inversion LTB.
Qed.

Lemma ord_eqb_symm :
    forall (alpha beta : ord),
        ord_eqb alpha beta = ord_eqb beta alpha.
Proof.
intros alpha beta.
case (ord_eqb beta alpha) eqn:EQ.
- apply ord_eqb_eq in EQ.
  destruct EQ.
  apply ord_eqb_refl.
- case (ord_eqb alpha beta) eqn:NEQ.
  + apply ord_eqb_eq in NEQ.
    destruct NEQ.
    rewrite ord_eqb_refl in EQ.
    inversion EQ.
  + reflexivity.
Qed.

Lemma ord_ltb_neb :
    forall (alpha beta: ord),
        ord_ltb alpha beta = true ->
            ord_eqb beta alpha = false.
Proof.
intros alpha beta LT.
case (ord_eqb beta alpha) eqn:EQ.
- apply ord_eqb_eq in EQ.
  destruct EQ.
  rewrite ord_ltb_irrefl in LT.
  inversion LT.
- reflexivity.
Qed.

Lemma ord_lt_self :
    forall (alpha beta : ord) (n : nat),
        alpha < cons alpha n beta.
Proof.
induction alpha.
- intros. apply zero_lt.
- intros. apply head_lt. apply IHalpha1.
Qed.

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
| cons (cons Zero 0 _) n b =>
    ord_mult (cons (cons Zero n Zero) 0 Zero) (ord_2_exp b)
| cons (cons Zero (S n) _) m b =>
    ord_mult (cons (cons (cons Zero n Zero) m Zero) 0 Zero) (ord_2_exp b)
| cons (cons a n b) n' b' =>
    ord_mult (cons (cons (cons a n b) n' Zero) 0 Zero) (ord_2_exp b')
end.

Lemma ord_add_zero :
    forall (alpha : ord),
        ord_add alpha Zero = alpha.
Proof. destruct alpha; reflexivity. Qed.

Lemma ord_zero_add : 
    forall (alpha : ord),
        ord_add Zero alpha = alpha.
Proof. destruct alpha; reflexivity. Qed.

Lemma ord_add_nat :
    forall (n m : nat),
        nat_ord (n + m) = ord_add (nat_ord n) (nat_ord m).
Proof.
intros n m.
induction m as [| m' IH].
- rewrite ord_add_zero.
  rewrite <- plus_n_O.
  reflexivity.
- induction n as [| n' IHn].
  + reflexivity.
  + rewrite <- plus_n_Sm.
    unfold nat_ord, ord_add, add.
    fold add.
    rewrite ord_ltb_irrefl.
    rewrite ord_eqb_refl.
    rewrite <- plus_assoc.
    rewrite <- plus_n_Sm.
    rewrite <- plus_n_O.
    rewrite plus_n_Sm.
    reflexivity.
Qed.

Fixpoint ord_succ (alpha : ord) : ord :=
match alpha with
| Zero => nat_ord 1
| cons Zero n b => cons Zero (S n) b
| cons a n b => cons a n (ord_succ b)
end.

Lemma ord_succ_neb_zero :
    forall alpha,
        ord_eqb (ord_succ alpha) Zero = false.
Proof.
induction alpha.
- reflexivity.
- destruct alpha1;
  reflexivity.
Qed.

Lemma ord_succ_one :
    forall alpha,
        cons Zero 0 Zero = ord_succ alpha ->
            Zero = alpha.
Proof.
intros alpha EQ.
destruct alpha.
- reflexivity.
- unfold ord_succ in EQ.
  fold ord_succ in EQ.
  destruct alpha1;
  inversion EQ.
Qed.

Lemma ord_succ_monot :
    forall (alpha : ord),
        ord_lt alpha (ord_succ alpha).
Proof.
induction alpha.
- apply zero_lt.
- destruct alpha1.
  + apply coeff_lt.
    unfold lt.
    reflexivity.
  + apply tail_lt.
    apply IHalpha2.
Qed.

Lemma ord_succ_nat :
    forall (n : nat),
        ord_succ (nat_ord n) = nat_ord (S n).
Proof. destruct n; reflexivity. Qed.

Fixpoint is_succ (alpha : ord) : bool :=
match alpha with
| Zero => false
| cons a n b => match b with
    | Zero => match a with
        | Zero => true
        | _ => false
        end
    | _ => is_succ b
    end
end.

Lemma ord_succ_is_succ :
    forall alpha,
        nf alpha ->
            is_succ (ord_succ alpha) = true.
Proof.
intros alpha NA.
induction alpha.
- reflexivity.
- destruct alpha1.
  + destruct (nf_head_zero _ _ NA).
    reflexivity.
  + unfold ord_succ, is_succ; fold ord_succ is_succ.
    destruct (ord_succ alpha2);
    apply (IHalpha2 (nf_hered_third _ _ _ NA)).
Qed.

Fixpoint ord_pred (alpha : ord) : ord :=
match alpha with
| Zero => Zero
| cons a n b => match b with
    | Zero => match a with
        | Zero => match n with
            | 0 => Zero
            | S p => cons Zero p Zero
            end
        | _ => cons a n b
        end
    | _ => cons a n (ord_pred b)
    end
end.

Lemma ord_succ_pred_if_succ :
    forall alpha,
        nf alpha ->
            is_succ alpha = true ->
                ord_succ (ord_pred alpha) = alpha.
Proof.
intros alpha NA SA.
induction alpha;
unfold ord_pred, ord_succ; fold ord_pred ord_succ.
- inversion SA.
- destruct alpha1.
  + destruct (nf_head_zero _ _ NA).
    destruct n;
    reflexivity.
  + destruct alpha2.
    * inversion SA.
    * rewrite <- (IHalpha2 (nf_hered_third _ _ _ NA) SA) at 2.
      reflexivity.
Qed.

Lemma ord_mult_omega_not_succ :
    forall alpha,
        nf alpha ->
            is_succ (ord_mult (cons (cons Zero 0 Zero) 0 Zero) alpha) = false.
Proof.
intros alpha NA.
induction alpha.
- reflexivity.
- unfold ord_mult. fold ord_mult.
  destruct alpha1.
  + reflexivity.
  + unfold is_succ; fold is_succ.
    rewrite (IHalpha2 (nf_hered_third _ _ _ NA)).
    destruct (ord_mult (cons (cons Zero 0 Zero) 0 Zero) alpha2);
    destruct alpha1_1;
    reflexivity.
Qed.

Lemma ord_lt_succ :
    forall alpha beta,
        ord_lt alpha beta ->
            ord_lt (ord_succ alpha) (ord_succ beta).
Proof.
induction alpha as [| a1 IHa1 an a2 IHa2];
intros beta LT;
destruct beta as [| b1 bn b2].
1,3 : inversion LT.
- destruct b1.
  + apply coeff_lt.
    lia.
  + apply (head_lt _ _ _ _ _ _ (zero_lt _ _ _)).
- destruct (cons_lt_aux _ _ _ _ _ _ LT) as [LT' | [[EQO LT'] | [EQO [EQN LT']]]].
  + destruct b1.
    * inversion LT'.
    * destruct a1.
      --  apply (head_lt _ _ _ _ _ _ (zero_lt _ _ _)).
      --  apply (head_lt _ _ _ _ _ _ LT').
  + destruct EQO.
    destruct a1.
    * apply (coeff_lt _ _ _ _ _ (le_n_S _ _ LT')).
    * apply (coeff_lt _ _ _ _ _ LT').
  + destruct EQO,EQN.
    destruct a1.
    * apply (tail_lt _ _ _ _ LT').
    * apply (tail_lt _ _ _ _ (IHa2 _ LT')).
Qed.

Lemma ord_succ_lt :
    forall alpha beta,
        ord_lt (ord_succ alpha) (ord_succ beta) ->
            ord_lt alpha beta.
Proof.
induction alpha as [| a1 IHa1 an a2 IHa2];
intros beta LT;
destruct beta as [| b1 bn b2].
- destruct (ord_lt_irrefl _ LT).
- apply zero_lt.
- destruct a1;
  unfold ord_succ, nat_ord in LT;
  destruct (cons_lt_aux _ _ _ _ _ _ LT) as [LT' | [[EQO LT'] | [EQO [EQN LT']]]];
  inversion LT'.
- destruct b1;
  destruct a1.
  3 : apply head_lt;
      apply zero_lt.
  all : destruct (cons_lt_aux _ _ _ _ _ _ LT) as [LT' | [[EQO LT'] | [EQO [EQN LT']]]].
  + inversion LT'.
  + apply coeff_lt.
    apply le_S_n.
    apply LT'.
  + apply eq_add_S in EQN.
    destruct EQN.
    apply tail_lt.
    apply LT'.
  + inversion LT'.
  + inversion EQO.
  + inversion EQO.
  + apply head_lt.
    apply LT'.
  + destruct EQO.
    apply coeff_lt.
    apply LT'.
  + destruct EQO,EQN.
    apply tail_lt.
    apply IHa2.
    apply LT'.
Qed.

Lemma ord_geb_trans :
    forall alpha beta gamma,
        ord_ltb alpha beta = false ->
            ord_ltb beta gamma = false ->
                ord_ltb alpha gamma = false.
Proof.
intros alpha beta gamma GEAB GEBG.
destruct (ord_semiconnex_bool alpha beta) as [LT | [GT | EQ]].
- rewrite LT in GEAB.
  inversion GEAB.
- destruct (ord_semiconnex_bool beta gamma) as [LT' | [GT' | EQ']].
  + rewrite LT' in GEBG.
    inversion GEBG.
  + apply (ord_ltb_asymm _ _ (ord_ltb_trans _ _ _ GT' GT)).
  + apply ord_eqb_eq in EQ'.
    destruct EQ'.
    apply GEAB.
- apply ord_eqb_eq in EQ.
  destruct EQ.
  apply GEBG.
Qed.

Lemma ord_geb_succ :
    forall alpha beta,
        ord_ltb alpha beta = false ->
            ord_ltb (ord_succ alpha) (ord_succ beta) = false.
Proof.
intros alpha beta GE.
destruct (ord_semiconnex_bool alpha beta) as [LT | [GT | EQ]].
- rewrite LT in GE.
  inversion GE.
- apply ord_ltb_asymm.
  apply (ord_lt_ltb _ _ (ord_lt_succ _ _ (ord_ltb_lt _ _ GT))).
- apply ord_eqb_eq in EQ.
  destruct EQ.
  apply ord_ltb_irrefl.
Qed.

Definition ord_max (alpha beta : ord) : ord :=
match ord_ltb alpha beta with
| true => beta
| false => alpha
end.

Lemma ord_max_ltb_is_r :
    forall (alpha beta : ord),
        ord_ltb alpha beta = true ->
            ord_max alpha beta = beta.
Proof.
intros alpha beta LT.
unfold ord_max.
rewrite LT.
reflexivity.
Qed.

Lemma ord_max_ltb_not_l :
    forall (alpha beta : ord),
        ord_ltb alpha beta = false ->
            ord_max alpha beta = alpha.
Proof.
intros alpha beta LT.
unfold ord_max.
rewrite LT.
reflexivity.
Qed.

Lemma ord_max_symm :
    forall (alpha beta : ord),
        ord_max alpha beta = ord_max beta alpha.
Proof.
intros alpha beta.
unfold ord_max.
destruct (ord_semiconnex_bool alpha beta) as [LT | [GT | EQ]].
- rewrite LT.
  rewrite (ord_ltb_asymm _ _ LT).
  reflexivity.
- rewrite GT.
  rewrite (ord_ltb_asymm _ _ GT).
  reflexivity.
- apply ord_eqb_eq in EQ.
  destruct EQ.
  reflexivity.
Qed.

Lemma ord_max_succ_succ :
    forall alpha beta,
        ord_max (ord_succ alpha) (ord_succ beta) = ord_succ (ord_max alpha beta).
Proof.
intros alpha beta.
destruct (ord_semiconnex_bool alpha beta) as [LT | [GT | EQ]];
unfold ord_max.
- rewrite LT.
  rewrite (ord_lt_ltb _ _  (ord_lt_succ _ _ (ord_ltb_lt _ _ LT))).
  reflexivity.
- rewrite (ord_ltb_asymm _ _ GT).
  rewrite (ord_ltb_asymm _ _ (ord_lt_ltb _ _  (ord_lt_succ _ _ (ord_ltb_lt _ _ GT)))).
  reflexivity.
- apply ord_eqb_eq in EQ.
  destruct EQ.
  repeat rewrite ord_ltb_irrefl.
  reflexivity.
Qed.

Lemma ord_max_self :
    forall (alpha : ord),
        alpha = ord_max alpha alpha.
Proof.
intros alpha.
unfold ord_max.
rewrite ord_ltb_irrefl.
reflexivity.
Qed.

Lemma ord_max_nat :
    forall n m,
        ord_max (nat_ord n) (nat_ord m) = nat_ord (max n m).
Proof.
induction n;
destruct m;
try reflexivity.
- unfold max. fold max.
  repeat rewrite <- ord_succ_nat.
  rewrite ord_max_succ_succ.
  rewrite IHn.
  reflexivity. 
Qed.

Lemma ord_lt_max_succ_l :
    forall (alpha beta : ord),
        ord_lt alpha (ord_succ (ord_max alpha beta)).
Proof.
intros alpha beta.
unfold ord_max.
case (ord_ltb alpha beta) eqn:LT.
- apply (ord_lt_trans _ _ _ (ord_ltb_lt _ _ LT) (ord_succ_monot _)).
- apply ord_succ_monot.
Qed.

Lemma ord_lt_max_succ_r :
    forall (alpha beta : ord),
        ord_lt beta (ord_succ (ord_max alpha beta)).
Proof.
intros alpha beta.
rewrite ord_max_symm.
apply ord_lt_max_succ_l.
Qed.

Lemma ord_max_geb_l :
    forall (alpha beta : ord),
        ord_ltb (ord_max alpha beta) alpha = false.
Proof.
intros alpha beta.
unfold ord_max in *.
destruct (ord_ltb alpha beta) eqn:LT.
- apply (ord_ltb_asymm _ _ LT).
- apply ord_ltb_irrefl.
Qed.

Lemma ord_max_geb_r :
    forall (alpha beta : ord),
        ord_ltb (ord_max alpha beta) beta = false.
Proof.
intros alpha beta.
rewrite ord_max_symm.
apply ord_max_geb_l.
Qed.

Lemma ord_max_zero :
    forall (alpha beta : ord),
        Zero = ord_max alpha beta ->
            Zero = alpha /\ Zero = beta.
Proof.
intros alpha beta EQ.
unfold ord_max in EQ.
case (ord_ltb alpha beta) eqn:LT.
- destruct EQ.
  destruct alpha.
  + split;
    reflexivity.
  + inversion LT.
- destruct EQ.
  destruct beta.
  + split;
    reflexivity.
  + inversion LT.
Qed.

Lemma nf_scalar :
    forall (a b : ord) (n n' : nat),
        nf (cons a n b) ->
            nf (cons a n' b).
Proof.
intros a b n n' N.
inversion N.
- apply single_nf.
  apply H0.
- apply cons_nf.
  + apply H2.
  + apply H3.
  + apply H4.
Qed.


Lemma nf_cons_head_lt :
    forall (a a' b' : ord) (n n' : nat),
        nf (cons a n (cons a' n' b')) ->
            a' < a.
Proof.
intros a a' b' n n' N.
inversion N.
apply H2.
Qed.

Lemma nf_succ_nf :
    forall alpha,
        nf (ord_succ alpha) ->
            nf alpha.
Proof.
intros alpha NA.
induction alpha as [| a1 IHa1 an a2 IHa2].
- apply zero_nf.
- destruct a1.
  + apply (nf_scalar _ _ _ _ NA).
  + unfold ord_succ in NA; fold ord_succ in NA.
    destruct a2.
    * apply (single_nf _ _ (nf_hered_first _ _ _ NA)).
    * refine (cons_nf _ _ _ _ _ _ (nf_hered_first _ _ _ NA) (IHa2 (nf_hered_third _ _ _ NA))).
      destruct a2_1.
      --  apply zero_lt.
      --  apply (nf_cons_head_lt _ _ _ _ _ NA).
Qed.

Lemma nf_nf_succ :
    forall alpha,
        nf alpha ->
            nf (ord_succ alpha).
Proof.
intros alpha NA.
induction alpha as [| a1 IHa1 an a2 IHa2].
- apply (single_nf _ _ zero_nf).
- destruct a1.
  + destruct (nf_head_zero _ _ NA).
    unfold ord_succ.
    fold (nat_ord (S (S an))).
    apply nf_nat.
  + destruct a2.
    * apply (cons_nf _ _ _ _ _ (zero_lt _ _ _) (nf_hered_first _ _ _ NA) (single_nf _ _ zero_nf)).
    * unfold ord_succ; fold ord_succ.
      destruct a2_1.
      --  destruct (nf_head_zero _ _ (nf_hered_third _ _ _ NA)).
          apply (cons_nf _ _ _ _ _ (zero_lt _ _ _) (nf_hered_first _ _ _ NA) (nf_scalar _ _ _ _ (nf_hered_third _ _ _ NA))).
      --  apply (cons_nf _ _ _ _ _ (nf_cons_head_lt _ _ _ _ _ NA) (nf_hered_first _ _ _ NA) (IHa2 (nf_hered_third _ _ _ NA))).
Qed.

Lemma nf_ord_max :
    forall alpha beta,
        nf alpha ->
            nf beta ->
                nf (ord_max alpha beta).
Proof.
intros alpha beta NA NB.
case (ord_ltb alpha beta) eqn:LT;
unfold ord_max;
rewrite LT.
- apply NB.
- apply NA.
Qed.

Lemma nf_cons_decr :
    forall (alpha beta : ord) (n : nat),
        nf (cons alpha n beta) ->
            beta < cons alpha n Zero.
Proof.
intros alpha beta n N.
inversion N.
- apply zero_lt.
- apply head_lt.
  apply H2.
Qed.

Lemma nf_add_eq_exp :
    forall (a a' a'' b b' b'' : ord) (n n' n'' : nat),
        cons a n b = ord_add (cons a' n' b') (cons a'' n'' b'') ->
            (a = a' \/ a = a'').
Proof.
intros a a' a'' b b' b'' n n' n''.
unfold ord_add; fold ord_add.
case (ord_ltb a' a'').
- intros EQ.
  inversion EQ.
  right.
  reflexivity.
- case (ord_eqb a' a'').
  + intros EQ.
    inversion EQ.
    right.
    reflexivity.
  + intros EQ.
    inversion EQ.
    left. 
    reflexivity.
Qed.

Lemma nf_add : 
    forall (alpha beta : ord),
        nf alpha ->
            nf beta ->
                nf (ord_add alpha beta).
Proof.
induction alpha.
- intros beta NA NB.
  rewrite ord_zero_add.
  apply NB.
- intros beta NA NB.
  unfold ord_add; fold ord_add.
  destruct beta.
  + apply NA.
  + destruct (ord_semiconnex_bool alpha1 beta1) as [LT | [GT | EQ]].
    * rewrite LT.
      apply NB.
    * rewrite (ord_ltb_asymm _ _ GT).
      rewrite (ord_ltb_neb _ _ GT).
      unfold ord_add; fold ord_add.
      destruct alpha2.
      --  rewrite ord_zero_add.
          apply (cons_nf _ _ _ _ _ (ord_ltb_lt _ _ GT) (nf_hered_first _ _ _ NA) NB).
      --  remember (ord_add (cons alpha2_1 n1 alpha2_2) (cons beta1 n0 beta2)) as A.
          destruct A.
          ++  apply (single_nf _ _ (nf_hered_first _ _ _ NA)).
          ++  refine (cons_nf _ _ _ _ _ _ (nf_hered_first _ _ _ NA) _).
              **  destruct (nf_add_eq_exp _ _ _ _ _ _ _ _ _ HeqA) as [EQ | EQ];
                  destruct EQ.
                  { apply (nf_cons_head_lt _ _ _ _ _ NA). }
                  { apply (ord_ltb_lt _ _ GT). }
              **  rewrite HeqA.
                  apply (IHalpha2 _ (nf_hered_third _ _ _ NA) NB).
    * apply ord_eqb_eq in EQ.
      destruct EQ.
      rewrite ord_ltb_irrefl.
      rewrite ord_eqb_refl.
      apply (nf_scalar _ _ _ _ NB).
Qed.

Lemma add_right_incr :
    forall (alpha beta gamma : ord),
        beta < gamma ->
            ord_add alpha beta < ord_add alpha gamma.
Proof.
induction alpha as [| a1 IHa1 an a2 IHa2].
- intros beta gamma LTBG.
  repeat rewrite ord_zero_add.
  apply LTBG.
- destruct gamma as [| g1 gn g2];
  intros LTBG.
  + inversion LTBG.
  + destruct beta as [| b1 bn b2].

1 : rewrite ord_add_zero.

all : unfold ord_add; fold ord_add;
      destruct (ord_semiconnex_bool a1 g1) as [LT | [GT | EQ]];
      try rewrite LT;
      try rewrite (ord_ltb_asymm _ _ GT);
      try rewrite (ord_ltb_neb _ _ GT);
      try apply ord_eqb_eq in EQ;
      try destruct EQ;
      try rewrite ord_ltb_irrefl;
      try rewrite ord_eqb_refl.

1 : apply (head_lt _ _ _ _ _ _ (ord_ltb_lt _ _ LT)).

1 : apply tail_lt.
    rewrite <- ord_add_zero at 1.
    apply (IHa2 _ _ LTBG).

1 : apply coeff_lt.
    lia.

1 : { destruct (ord_semiconnex_bool a1 b1) as [LT' | [GT' | EQ']];
      try rewrite LT';
      try rewrite (ord_ltb_asymm _ _ GT');
      try rewrite (ord_ltb_neb _ _ GT');
      try apply ord_eqb_eq in EQ';
      try destruct EQ';
      try rewrite ord_ltb_irrefl;
      try rewrite ord_eqb_refl.
      - apply LTBG.
      - apply (head_lt _ _ _ _ _ _ (ord_ltb_lt _ _ LT)).
      - apply (head_lt _ _ _ _ _ _ (ord_ltb_lt _ _ LT)). }


all : destruct (cons_lt_aux _ _ _ _ _ _ LTBG) as [LT' | [[EQO LT'] | [EQO [EQN LT']]]];
      try destruct EQO;
      try destruct EQO';
      try destruct EQN;
      try destruct EQN';
      try rewrite (ord_ltb_asymm _ _ (ord_ltb_trans _ _ _ (ord_lt_ltb _ _ LT') GT));
      try rewrite (ord_ltb_asymm _ _ (ord_lt_ltb _ _ LT'));
      try rewrite (ord_ltb_asymm _ _ GT);
      try rewrite (ord_ltb_neb _ _ (ord_ltb_trans _ _ _ (ord_lt_ltb _ _ LT') GT));
      try rewrite (ord_ltb_neb _ _ GT);
      try rewrite (ord_ltb_neb _ _ (ord_lt_ltb _ _ LT'));
      try rewrite ord_ltb_irrefl;
      try rewrite ord_eqb_refl.

1-3 : apply (tail_lt _ _ _ _ (IHa2 _ _ LTBG)).

1,2 : apply coeff_lt; lia.

apply (tail_lt _ _ _ _ LT').
Qed.


Lemma add_right_incr_non_zero :
    forall (alpha beta : ord),
        Zero < beta ->
            alpha < ord_add alpha beta.
Proof.
intros alpha beta LT.
rewrite <- (ord_add_zero alpha) at 1.
apply (add_right_incr alpha Zero beta LT).
Qed.

Lemma add_right_non_decr :
    forall alpha beta,
        ord_ltb (ord_add alpha beta) alpha = false.
Proof.
intros alpha beta.
destruct beta.
- rewrite ord_add_zero.
  apply ord_ltb_irrefl.
- apply ord_ltb_asymm.
  apply ord_lt_ltb.
  apply add_right_incr_non_zero.
  apply zero_lt.
Qed.

Lemma add_left_non_decr :
    forall alpha beta,
        ord_ltb (ord_add beta alpha) alpha = false.
Proof.
intros alpha beta.
destruct beta as [| b1 nb b2].
- rewrite ord_zero_add.
  apply ord_ltb_irrefl.
- destruct alpha as [| a1 na a2].
  + reflexivity.
  + unfold ord_add; fold ord_add.
    destruct (ord_semiconnex_bool b1 a1) as [LT | [GT | EQ]].
    * rewrite LT.
      apply ord_ltb_irrefl.
    * rewrite (ord_ltb_asymm _ _ GT).
      rewrite (ord_ltb_neb _ _ GT).
      apply (ord_ltb_asymm _ _ (ord_lt_ltb _ _ (head_lt _ _ _ _ _ _ (ord_ltb_lt _ _ GT)))).
    * apply ord_eqb_eq in EQ.
      destruct EQ.
      rewrite ord_ltb_irrefl.
      rewrite ord_eqb_refl.
      refine (ord_ltb_asymm _ _ (ord_lt_ltb _ _ (coeff_lt _ _ _ _ _ _))).
      lia.
Qed.

Lemma ord_max_add_comm :
    forall alpha beta gamma,
        ord_add alpha (ord_max beta gamma) = ord_max (ord_add alpha beta) (ord_add alpha gamma).
Proof.
intros alpha beta gamma.
destruct (ord_semiconnex_bool beta gamma) as [LT | [GT | EQ]].
- unfold ord_max.
  rewrite LT.
  rewrite (ord_lt_ltb _ _ (add_right_incr _ _ _ (ord_ltb_lt _ _ LT))).
  reflexivity.
- unfold ord_max.
  rewrite (ord_ltb_asymm _ _ GT).
  rewrite (ord_ltb_asymm _ _ (ord_lt_ltb _ _ (add_right_incr _ _ _ (ord_ltb_lt _ _ GT)))).
  reflexivity.
- apply ord_eqb_eq in EQ.
  destruct EQ.
  unfold ord_max.
  repeat rewrite ord_ltb_irrefl.
  reflexivity.
Qed.

Lemma ord_max_geb_split :
    forall alpha beta gamma delta,
        ord_ltb alpha gamma = false ->
            ord_ltb beta delta = false ->
                ord_ltb (ord_max alpha beta) (ord_max gamma delta) = false.
Proof.
intros alpha beta gamma delta GEAG GEBD;
unfold ord_max.
destruct (ord_semiconnex_bool alpha beta) as [LT | [GT | EQ]];
case (ord_ltb gamma delta) eqn:LTGD.
1,2 : rewrite LT.
3,4 : rewrite (ord_ltb_asymm _ _ GT).
5,6 : apply ord_eqb_eq in EQ;
      destruct EQ;
      rewrite ord_ltb_irrefl.
- apply GEBD.
- apply (ord_geb_trans _ _ _ (ord_ltb_asymm _ _ LT) GEAG).
- apply (ord_geb_trans _ _ _ (ord_ltb_asymm _ _ GT) GEBD).
- apply GEAG.
- apply GEBD.
- apply GEAG.
Qed.

Lemma ord_max_le_add :
    forall alpha beta,
        nf alpha ->
            nf beta ->
                ord_ltb (ord_add alpha beta) (ord_max alpha beta) = false.
Proof.
intros alpha beta NA NB.
unfold ord_max.
destruct (ord_semiconnex_bool alpha beta) as [LT | [GT | EQ]].
- rewrite LT.
  apply add_left_non_decr.
- rewrite (ord_ltb_asymm _ _ GT).
  destruct beta.
  + rewrite ord_add_zero.
    apply ord_ltb_irrefl.
  + apply (ord_ltb_asymm _ _ (ord_lt_ltb _ _ (add_right_incr_non_zero _ _ (zero_lt _ _ _)))).
- apply ord_eqb_eq in EQ.
  destruct EQ.
  rewrite ord_ltb_irrefl.
  destruct alpha.
  + reflexivity.
  + unfold ord_add; fold ord_add.
    rewrite ord_ltb_irrefl.
    rewrite ord_eqb_refl.
    apply ord_ltb_asymm.
    apply ord_lt_ltb.
    apply coeff_lt.
    lia.
Qed.

Lemma ord_add_one_succ :
    forall alpha,
        nf alpha ->
            ord_add alpha (cons Zero 0 Zero) = ord_succ alpha.
Proof.
intros alpha NA.
induction alpha.
- reflexivity.
- destruct alpha1;
  unfold ord_add; fold ord_add.
  + rewrite ord_ltb_irrefl.
    rewrite ord_eqb_refl.
    rewrite <- plus_n_Sm.
    repeat rewrite <- plus_n_O.
    destruct (nf_head_zero _ _ NA).
    reflexivity.
  + unfold ord_ltb, ord_eqb.
    rewrite (IHalpha2 (nf_hered_third _ _ _ NA)).
    reflexivity.
Qed.

Lemma ord_add_assoc :
    forall alpha beta gamma,
        ord_add (ord_add alpha beta) gamma = ord_add alpha (ord_add beta gamma).
Proof.
induction alpha as [| a1 IHa1 na a2 IHa2];
intros beta gamma.
- repeat rewrite ord_zero_add.
  reflexivity.
- destruct beta as [| b1 nb b2].
  + rewrite ord_zero_add.
    rewrite ord_add_zero.
    reflexivity.
  + destruct gamma as [| g1 ng].
    * repeat rewrite ord_add_zero.
      reflexivity.
    * unfold ord_add; fold ord_add.
      destruct (ord_semiconnex_bool a1 b1) as [LT | [GT | EQ]];
      destruct (ord_semiconnex_bool b1 g1) as [LT' | [GT' | EQ']];
      try apply ord_eqb_eq in EQ;
      try apply ord_eqb_eq in EQ';
      try destruct EQ;
      try destruct EQ';
      try rewrite ord_ltb_irrefl;
      try rewrite ord_eqb_refl;
      try rewrite LT;
      try rewrite LT';
      try rewrite (ord_ltb_asymm _ _ GT);
      try rewrite (ord_ltb_asymm _ _ GT');
      try rewrite (ord_ltb_neb _ _ GT);
      try rewrite (ord_ltb_neb _ _ GT');
      try rewrite ord_ltb_irrefl;
      try rewrite ord_eqb_refl;
      unfold ord_add; fold ord_add;
      try rewrite ord_ltb_irrefl;
      try rewrite ord_eqb_refl;
      try rewrite LT;
      try rewrite LT';
      try rewrite (ord_ltb_asymm _ _ GT);
      try rewrite (ord_ltb_asymm _ _ GT');
      try rewrite (ord_ltb_neb _ _ GT);
      try rewrite (ord_ltb_neb _ _ GT');
      try reflexivity.
      --  rewrite (ord_ltb_trans _ _ _ LT LT').
          reflexivity.
      --  destruct (ord_semiconnex_bool a1 g1) as [LT | [GT' | EQ]].
          ++  rewrite LT.
              reflexivity.
          ++  rewrite (ord_ltb_neb _ _ GT').
              rewrite (ord_ltb_asymm _ _ GT').
              rewrite IHa2.
              unfold ord_add at 2.
              rewrite LT'.
              reflexivity.
          ++  apply ord_eqb_eq in EQ.
              destruct EQ.
              rewrite ord_ltb_irrefl.
              rewrite ord_eqb_refl.
              reflexivity.
      --  rewrite (ord_ltb_asymm _ _ (ord_ltb_trans _ _ _ GT' GT)).
          rewrite (ord_ltb_neb _ _ (ord_ltb_trans _ _ _ GT' GT)).
          rewrite IHa2.
          unfold ord_add at 2.
          rewrite (ord_ltb_asymm _ _ GT').
          rewrite (ord_ltb_neb _ _ GT').
          reflexivity.
      --  rewrite IHa2.
          unfold ord_add at 2.
          rewrite ord_ltb_irrefl.
          rewrite ord_eqb_refl.
          reflexivity.
      --  rewrite <- (plus_assoc nb ng 1).
          rewrite (plus_comm ng 1).
          repeat rewrite plus_assoc.
          reflexivity.
Qed.

Lemma ord_succ_add_succ :
    forall alpha beta,
        nf alpha ->
            nf beta ->
                ord_add alpha (ord_succ beta) = ord_succ (ord_add alpha beta).
Proof.
intros alpha beta NA NB.
rewrite <- (ord_add_one_succ _ NB).
rewrite <- ord_add_assoc.
rewrite (ord_add_one_succ _ (nf_add _ _ NA NB)).
reflexivity.
Qed.

Lemma ord_add_succ_nat_succ_add :
    forall (alpha : ord) (n : nat),
        nf alpha ->
            ord_add alpha (nat_ord (S n)) = ord_add (ord_succ alpha) (nat_ord n).
Proof.
intros alpha n NA.
induction alpha as [| a1 IHa1 an a2 IHa2].
- destruct n.
  + reflexivity.
  + rewrite ord_zero_add.
    unfold ord_succ, nat_ord, ord_add.
    rewrite ord_ltb_irrefl.
    rewrite ord_eqb_refl.
    rewrite <- plus_n_Sm.
    rewrite <- plus_n_O.
    reflexivity.
- destruct n.
  + rewrite ord_add_zero.
    unfold nat_ord.
    rewrite (ord_add_one_succ _ NA).
    reflexivity.
  + destruct a1.
    * destruct (nf_head_zero _ _ NA).
      unfold ord_succ, nat_ord, ord_add.
      rewrite ord_ltb_irrefl.
      rewrite ord_eqb_refl.
      repeat rewrite <- plus_n_Sm.
      reflexivity.
    * unfold ord_succ; fold ord_succ.
      unfold ord_add, nat_ord; fold ord_add.
      unfold ord_ltb, ord_eqb.
      unfold nat_ord in IHa2.
      rewrite (IHa2 (nf_hered_third _ _ _ NA)).
      reflexivity.
Qed.

Lemma nf_mult_eval :
    forall (a a' b b' : ord) (n n' : nat),
        Zero < a' ->
            ord_mult (cons a n b) (cons a' n' b') = cons (ord_add a a') n' (ord_mult (cons a n b) b').
Proof.
intros a a' b b' n n' LT.
destruct a'.
inversion LT.
reflexivity.
Qed.

Lemma mult_right_incr :
    forall (alpha beta gamma : ord),
        beta < gamma ->
            Zero < alpha ->
                nf gamma ->
                    ord_mult alpha beta < ord_mult alpha gamma.
Proof.
induction alpha as [| a1 IHa1 an a2 IHa2].
1 : intros beta gamma LTBG LT NG.
    inversion LT.

induction beta as [| b1 IHb1 bn b2 IHb2];
intros gamma LTBG LT NG;
destruct gamma.

1,3 : inversion LTBG.

1 : destruct gamma1;
    apply zero_lt.

destruct (cons_lt_aux _ _ _ _ _ _ LTBG) as [LT' | [[EQO LT'] | [EQO [EQN LT']]]];
try destruct EQO; try destruct EQN.

- destruct gamma1.
  inversion LT'.
  rewrite (nf_mult_eval _ _ _ _ _ _ (zero_lt _ _ _)).
  destruct b1.
  + apply head_lt.
    apply add_right_incr_non_zero.
    apply zero_lt.
  + rewrite (nf_mult_eval _ _ _ _ _ _ (zero_lt _ _ _)).
    apply head_lt.
    apply add_right_incr.
    apply LT'.

- destruct b1.
  + apply coeff_lt.
    unfold mul; fold mul.
    unfold add, sub; fold add sub.
    repeat rewrite minus_n_0.
    apply (nat_lt_mul_S_lt _ _ _ LT').
  + repeat rewrite (nf_mult_eval _ _ _ _ _ _ (zero_lt _ _ _)).
    apply (coeff_lt _ _ _ _ _ LT').

- destruct b1.
  + destruct (nf_head_zero _ _ NG).
    inversion LT'.
  + apply tail_lt.
    apply (IHb2 _ LT' (zero_lt _ _ _) (nf_hered_third _ _ _ NG)).
Qed.


Lemma nf_mult : 
    forall (alpha beta : ord),
        nf alpha ->
            nf beta ->
                nf (ord_mult alpha beta).
Proof.
induction alpha as [| a1 IHa1 na a2 IHa2].
- intros beta NA NB.
  destruct beta;
  apply zero_nf.
- intros beta NA NB.
  induction beta as [| b1 IHb1 nb b2 IHb2].
  + apply zero_nf.
  + destruct b1.
    * destruct (nf_head_zero _ _ NB).
      unfold ord_mult.
      apply (nf_scalar _ _ _ _ NA).
    * rewrite (nf_mult_eval _ _ _ _ _ _ (zero_lt _ _ _)).
      remember (ord_mult (cons a1 na a2) b2) as gamma.
      destruct gamma.
      --  apply (single_nf _ _ (nf_add _ _ (nf_hered_first _ _ _ NA) (nf_hered_first _ _ _ NB))).
      --  apply cons_nf.
          ++  destruct b2.
              **  inversion Heqgamma.
              **  destruct b2_1.
                  { unfold ord_mult in Heqgamma.
                    inversion Heqgamma.
                    destruct H0,H1,H2.
                    apply (add_right_incr_non_zero _ _ (zero_lt _ _ _)). }
                  { unfold ord_mult in Heqgamma; fold ord_mult in Heqgamma.
                    inversion Heqgamma.
                    rewrite H0,H1,H2 in *.
                    apply add_right_incr.
                    apply (nf_cons_head_lt _ _ _ _ _ NB). }
          ++  apply (nf_add _ _ (nf_hered_first _ _ _ NA) (nf_hered_first _ _ _ NB)).
          ++  apply (IHb2 (nf_hered_third _ _ _ NB)).
Qed.

Lemma nf_2_exp :
    forall (alpha : ord),
        nf alpha ->
            nf (ord_2_exp alpha).
Proof.
intros alpha NA.
induction alpha as [| a1 IHa1 na a2 IHa2].
- apply single_nf.
  apply zero_nf.
- destruct a1 as [| a1_1 na1 a1_2].
  + apply nf_nat.
  + destruct a1_1 as [| a1_1_1 na1_1 a1_1_2].        
    * destruct (nf_head_zero _ _ (nf_hered_first _ _ _ NA)).
      destruct na1.
      --  apply (nf_mult _ _ (single_nf _ _ (single_nf _ _ zero_nf)) (IHa2 (nf_hered_third _ _ _ NA))).
      --  apply (nf_mult _ _ (single_nf _ _ (single_nf _ _ (single_nf _ _ zero_nf))) (IHa2 (nf_hered_third _ _ _ NA))).
    * apply (nf_mult _ _ (single_nf _ _ (single_nf _ _ (nf_hered_first _ _ _ NA))) (IHa2 (nf_hered_third _ _ _ NA))).
Qed.

Lemma ord_mult_1_r :
    forall (alpha : ord),
        alpha = ord_mult alpha (nat_ord 1).
Proof.
induction alpha as [| a1 IHa1 na a2 IHa2].
- reflexivity.
- unfold nat_ord, ord_mult, mul, add, sub.
  rewrite minus_n_0.
  rewrite mult1_r.
  reflexivity.
Qed.

Lemma ord_mult_1_l :
    forall (alpha : ord),
        nf alpha ->
            alpha = ord_mult (nat_ord 1) alpha.
Proof.
intros alpha NA.
induction alpha as [| a1 IHa1 na a2 IHa2].
- reflexivity.
- destruct a1.
  + unfold nat_ord, ord_mult, mul, add, sub.
    rewrite minus_n_0.
    rewrite <- plus_n_O.
    destruct (nf_head_zero _ _ NA).
    reflexivity.
  + unfold nat_ord, ord_mult in *.
    fold ord_mult in *.
    rewrite ord_zero_add.
    rewrite (IHa2 (nf_hered_third _ _ _ NA)) at 1.
    reflexivity.
Qed.

Lemma ord_mult_monot :
    forall (alpha beta : ord),
        nat_ord 1 < beta ->
            nf beta ->
                Zero < alpha ->
                    alpha < ord_mult alpha beta.
Proof.
intros alpha beta LT1B NB LTZA.
destruct alpha as [| a1 na a2].
- inversion LTZA.
- rewrite ord_mult_1_r at 1.
  apply (mult_right_incr _ _ _ LT1B LTZA NB).
Qed.

Lemma ord_mult_0_l :
    forall (alpha : ord),
        ord_mult Zero alpha = Zero.
Proof.
induction alpha;
reflexivity.
Qed.

Lemma ord_mult_0_r :
    forall (alpha : ord),
        ord_mult alpha Zero = Zero.
Proof.
induction alpha;
reflexivity.
Qed.

Lemma ord_mult_nonzero :
    forall (alpha beta : ord),
        Zero < alpha ->
            Zero < beta ->
                nf beta ->
                    Zero < ord_mult alpha beta.
Proof.
intros alpha beta LTZA LTZB NB.
rewrite <- (ord_mult_0_r alpha) at 1.
apply (mult_right_incr _ _ _ LTZB LTZA NB).
Qed.

Lemma nat_ord_lt :
    forall (n m : nat),
        (n < m)%nat ->
            nat_ord n < nat_ord m.
Proof.
intros n m LT.
destruct m.
- inversion LT.
- induction n.
  + apply zero_lt.
  + apply (coeff_lt _ _ _ _ _ (le_S_n _ _ LT)).
Qed.

Lemma nat_ord_eq :
    forall (n m : nat),
        n = m ->
            nat_ord n = nat_ord m.
Proof. intros n m EQ. destruct EQ. reflexivity. Qed.

Lemma ord_2_exp_geq_1 :
    forall (alpha : ord),
        nf alpha ->
            Zero < ord_2_exp alpha.
Proof.
intros alpha NA.
induction alpha as [| a1 IHa1 na a2 IHa2].
- apply zero_lt.
- destruct a1 as [| a1_1 na1 a1_2].
  + destruct (nf_head_zero _ _ NA).
    unfold ord_2_exp.
    fold (nat_ord 0).
    apply nat_ord_lt.
    apply nat_2_exp_non_zero.
  + destruct a1_1 as [| a1_1_1 na1_1 a1_1_2].
    * destruct (nf_head_zero _ _ (nf_hered_first _ _ _ NA)).
      destruct na1;
      apply (ord_mult_nonzero _ _ (zero_lt _ _ _) (IHa2 (nf_hered_third _ _ _ NA)) (nf_2_exp _ (nf_hered_third _ _ _ NA))).
    * apply (ord_mult_nonzero _ _ (zero_lt _ _ _) (IHa2 (nf_hered_third _ _ _ NA)) (nf_2_exp _ (nf_hered_third _ _ _ NA))).
Qed.

Lemma ord_gt_one_succ_lt_dub :
    forall (alpha : ord),
        nf alpha ->
            ord_lt (cons Zero 0 Zero) alpha ->
                ord_lt (ord_succ alpha) (ord_mult alpha (nat_ord 2)).
Proof.
intros alpha NA LT.
induction alpha.
- inversion LT.
- destruct (cons_lt_aux _ _ _ _ _ _ LT) as [LT' | [[EQO LT'] | [EQO [EQN LT']]]].
  + destruct alpha1.
    * inversion LT'.
    * apply coeff_lt.
      lia.
  + destruct EQO.
    destruct (nf_head_zero _ _ NA).
    apply coeff_lt.
    lia.
  + destruct EQO.
    destruct (nf_head_zero _ _ NA).
    inversion LT'.
Qed.  

Lemma ord_gt_zero_exp_gt_one :
    forall (alpha : ord),
        nf alpha ->
            ord_lt Zero alpha ->
                ord_lt (cons Zero 0 Zero) (ord_2_exp alpha).
Proof.
intros alpha NA LT.
induction alpha as [| a1 IHa1 na a2 IHa2].
- inversion LT.
- destruct a1.
  + destruct (nf_head_zero _ _ NA).
    destruct na.
    * apply coeff_lt.
      unfold lt.
      reflexivity.
    * fold (nat_ord 1).
      apply nat_ord_lt.
      pose proof (nat_exp_monot_lem na) as IE.
      unfold pow; fold pow.
      lia.
  + destruct a1_1.
    * destruct (nf_head_zero _ _ (nf_hered_first _ _ _ NA)).
      destruct a2.
      --  destruct n;
          apply head_lt;
          apply zero_lt.
      --  destruct n;
          apply (ord_lt_trans _ _ _ (head_lt _ _ _ _ _ _ (zero_lt _ _ _)) (mult_right_incr _ _ _ (IHa2 (nf_hered_third _ _ _ NA) (zero_lt _ _ _)) (zero_lt _ _ _) (nf_2_exp _ (nf_hered_third _ _ _ NA)))).
    * destruct a2.
      --  destruct n;
          apply head_lt;
          apply zero_lt.
      --  destruct n;
          apply (ord_lt_trans _ _ _ (head_lt _ _ _ _ _ _ (zero_lt _ _ _)) (mult_right_incr _ _ _ (IHa2 (nf_hered_third _ _ _ NA) (zero_lt _ _ _)) (zero_lt _ _ _) (nf_2_exp _ (nf_hered_third _ _ _ NA)))).
Qed.

Lemma ord_geq_1_cases :
    forall (alpha : ord),
        Zero < alpha ->
            (alpha = nat_ord 1 \/ nat_ord 1 < alpha).
Proof.
intros alpha LTZA.
destruct (ord_semiconnex (nat_ord 1) alpha) as [LT | [GT | EQ]].
- right.
  apply LT.
- destruct alpha.
  + inversion LTZA.
  + destruct (cons_lt_aux _ _ _ _ _ _ GT) as [LT | [[EQO LT] | [EQO [EQn LT]]]];
    inversion LT.
- left.
  symmetry.
  apply EQ.
Qed.

Lemma ord_mult_geq_1_case_incr :
    forall (alpha beta : ord),
        nf beta ->
            Zero < beta ->
                alpha <= ord_mult alpha beta.
Proof.
intros alpha beta NB LTZB.
unfold leq.
destruct (ord_geq_1_cases _ LTZB) as [EQ | LT].
- left. 
  rewrite EQ.
  apply ord_mult_1_r.
- destruct alpha as [| a1 na a2].
  + left.
    symmetry.
    apply ord_mult_0_l.
  + right.
    apply (ord_mult_monot _ _ LT NB (zero_lt _ _ _)).
Qed.

Lemma ord_le_mult_exp :
    forall (alpha beta : ord),
        nf beta ->
            alpha <= ord_mult alpha (ord_2_exp beta).
Proof.
intros alpha beta NB.
apply (ord_mult_geq_1_case_incr _ _ (nf_2_exp _ NB) (ord_2_exp_geq_1 _ NB)).
Qed.

Lemma ord_mult_exp_monot :
    forall (alpha beta gamma : ord),
        nf gamma ->
            alpha < beta ->
                alpha < ord_mult beta (ord_2_exp gamma).
Proof.
intros alpha beta gamma NG LTAB.
destruct (ord_le_mult_exp beta gamma NG) as [EQ | LT].
- destruct EQ.
  apply LTAB.
- apply (ord_lt_trans _ _ _ LTAB LT).
Qed.

Lemma ord_2_exp_fp :
    forall (alpha : ord),
        nf alpha ->
            alpha < ord_2_exp alpha \/ alpha = cons (nat_ord 1) 0 Zero.
Proof.
intros alpha NA.
induction alpha as [| a1 IHa1 na a2 IHa2].
- left.
  apply zero_lt.
- destruct a1 as [| a1_1 na1 a1_2].
  + left.
    destruct (nf_head_zero _ _ NA).
    unfold ord_2_exp.
    fold (nat_ord (S na)).
    apply nat_ord_lt.
    unfold pow; fold pow.
    unfold mul.
    rewrite <- plus_n_O.
    apply nat_exp_monot_lem.
  + destruct a1_1 as [| a1_1_1 na1_1 a1_1_2].
    * destruct (nf_head_zero _ _ (nf_hered_first _ _ _ NA)).
      destruct na1.
      --  unfold ord_2_exp; fold ord_2_exp.
          destruct a2.
          ++  destruct na.
              **  right.
                  reflexivity.
              **  left.
                  apply (ord_mult_exp_monot _ _ _ zero_nf).
                  apply head_lt.
                  apply coeff_lt.
                  lia.
          ++  left.
              destruct (ord_lt_one _ (nf_cons_head_lt _ _ _ _ _ NA)).
              destruct (nf_head_zero _ _ (nf_hered_third _ _ _ NA)).
              unfold ord_2_exp, nat_ord, pow;
              fold pow.
              case (2^n) eqn:EQ.
              **  destruct (nat_2_exp_not_zero _ EQ).
              **  unfold mul.
                  rewrite <- plus_n_O.
                  rewrite <- plus_n_Sm.
                  unfold ord_mult, mul, sub.
                  rewrite <- plus_n_O.
                  rewrite minus_n_0.
                  destruct na.
                  { apply coeff_lt.
                    lia. }
                  { apply head_lt.
                    apply coeff_lt.
                    lia. }
      --  left.
          apply (ord_mult_exp_monot _ _ _ (nf_hered_third _ _ _ NA)).
          repeat apply head_lt.
          apply zero_lt.
    * left.
      apply (ord_mult_exp_monot _ _ _ (nf_hered_third _ _ _ NA)).
      repeat apply head_lt.
      apply ord_lt_self.
Qed.

Lemma ord_ltb_exp_false :
    forall (alpha : ord),
        nf alpha ->
            ord_ltb (ord_2_exp alpha) alpha = false.
Proof.
intros alpha Na.
destruct (ord_2_exp_fp alpha Na) as [LT | EQ].
- apply (ord_ltb_asymm _ _ (ord_lt_ltb _ _ LT)).
- rewrite EQ.
  apply ord_ltb_irrefl.  
Qed.

Lemma ord_succ_not_exp_fp :
    forall (alpha : ord),
        nf (ord_succ alpha) ->
            ord_lt (ord_succ alpha) (ord_2_exp (ord_succ alpha)).
Proof.
intros alpha NA.
destruct (ord_2_exp_fp (ord_succ alpha) NA) as [LT | EQ].
- apply LT.
- pose proof (ord_succ_is_succ _ (nf_succ_nf _ NA)) as FAL.
  rewrite EQ in FAL.
  inversion FAL.
Qed.

Lemma ord_mult_assoc :
    forall alpha beta gamma,
        ord_mult (ord_mult alpha beta) gamma = ord_mult alpha (ord_mult beta gamma).
Proof.
intros alpha beta gamma.
induction gamma as [| g1 IHg1 ng g2 IHg2].
- destruct beta;
  destruct alpha;
  try destruct beta1;
  reflexivity.
- destruct beta as [| b1 nb b2].
  + destruct alpha;
    reflexivity.
  + destruct alpha as [| a1 na a2].
    * destruct g1;
      reflexivity.
    * destruct g1 as [| g1_1 ng1 g1_2].
      --  unfold ord_mult; fold ord_mult.
          destruct b1.
          ++  assert ((S (S na * S nb - 1) * S ng - 1) = (S na * S (S nb * S ng - 1) - 1)) as EQ.
              { unfold mul; fold mul.
                repeat rewrite <- mult_n_Sm.
                repeat rewrite (plus_comm (S ng)).
                rewrite (plus_comm (S nb)).
                rewrite (plus_comm (S _)).
                repeat rewrite <- plus_assoc.
                repeat rewrite <- plus_n_Sm.
                unfold sub; fold sub.
                repeat rewrite minus_n_0.
                lia. }
              rewrite EQ.
              reflexivity.
          ++  reflexivity.
      --  unfold ord_mult; fold ord_mult.
          destruct b1 as [| b1_1 nb1 b1_2].
          ++  rewrite ord_zero_add.
              rewrite <- IHg2.
              reflexivity.
          ++  case (ord_add (cons b1_1 nb1 b1_2) (cons g1_1 ng1 g1_2)) eqn:EQ.
              **  unfold ord_add in EQ; fold ord_add in EQ.
                  destruct (ord_semiconnex_bool b1_1 g1_1) as [LT | [GT | EQ']].
                  { rewrite LT in EQ.
                    inversion EQ. }
                  { rewrite (ord_ltb_asymm _ _ GT) in EQ.
                    rewrite (ord_ltb_neb _ _ GT) in EQ.
                    inversion EQ. }
                  { apply ord_eqb_eq in EQ'.
                    destruct EQ'.
                    rewrite ord_ltb_irrefl in EQ.
                    rewrite ord_eqb_refl in EQ.
                    inversion EQ. }
              **  destruct EQ.
                  rewrite ord_add_assoc.
                  rewrite <- IHg2.
                  reflexivity.
Qed.

Lemma ord_not_succ_is_mul :
    forall alpha,
        nf alpha ->
            is_succ alpha = false ->
                { beta : ord & alpha = ord_mult (cons (cons Zero 0 Zero) 0 Zero) beta /\ nf beta}.
Proof.
intros alpha NA UA.
induction alpha as [|a1 IHa1 na a2 IHa2].
- exists Zero. 
  split.
  + reflexivity.
  + apply zero_nf.
- unfold is_succ in UA. fold is_succ in UA.
  destruct a1 as [|a1_1 na1 a1_2].
  + destruct (nf_head_zero _ _ NA).
    inversion UA.
  + destruct a2 as [|a2_1 na2 a2_2].
    * destruct a1_1 as [|a1_1_1 na1_1 a1_1_2].
      --  exists (cons (ord_pred (cons Zero na1 a1_2)) na Zero).
          destruct (nf_head_zero _ _ (nf_hered_first _ _ _ NA)).
          destruct na1.
          ++  unfold ord_mult, ord_pred, mul.
              rewrite <- plus_n_O.
              unfold sub.
              rewrite minus_n_0.
              split.
              **  reflexivity.
              **  apply single_nf.
                  apply zero_nf.
          ++  unfold ord_pred.
              rewrite (nf_mult_eval _ _ _ _ _ _ (zero_lt _ _ _)).
              rewrite ord_mult_0_r.
              unfold ord_add.
              rewrite ord_ltb_irrefl.
              rewrite ord_eqb_refl.
              rewrite <- plus_n_Sm.
              rewrite <- plus_n_O.
              split.
              **  reflexivity.
              **  repeat apply single_nf.
                  apply zero_nf.
      --  exists (cons (cons (cons a1_1_1 na1_1 a1_1_2) na1 a1_2) na Zero).
          rewrite (nf_mult_eval _ _ _ _ _ _ (zero_lt _ _ _)).
          split.
          ++  reflexivity.
          ++  apply NA.
    * destruct (IHa2 (nf_hered_third _ _ _ NA) UA) as [beta [EQ NB]].
      rewrite EQ.
      destruct a1_1 as [| a1_1_1 na1_1 a1_1_2].
      --  destruct (nf_head_zero _ _ (nf_hered_first _ _ _ NA)).
          destruct na1.
        ++  exists Zero.
            pose proof (nf_cons_head_lt _ _ _ _ _ NA) as IE.
            destruct a2_1.
            **  destruct (nf_head_zero _ _ (nf_hered_third _ _ _ NA)).
                inversion UA.
            **  destruct (cons_lt_aux _ _ _ _ _ _ IE) as [LT | [[EQO LT] | [EQO [EQn LT]]]];
                inversion LT.
        ++  exists (cons (ord_pred (cons Zero (S na1) Zero)) na beta).
            unfold ord_pred.
            rewrite (nf_mult_eval _ _ _ _ _ _ (zero_lt _ _ _)).
            unfold ord_add.
            rewrite ord_ltb_irrefl.
            rewrite ord_eqb_refl.
            rewrite <- plus_n_Sm.
            rewrite <- plus_n_O.
            split.
            **  reflexivity.
            **  destruct beta.
                { inversion EQ. }
                { refine (cons_nf _ _ _ _ _ _ (single_nf _ _ zero_nf) NB).
                  destruct beta1.
                  { apply zero_lt. }
                  { rewrite (nf_mult_eval _ _ _ _ _ _ (zero_lt _ _ _)) in EQ.
                    pose proof (nf_cons_head_lt _ _ _ _ _ NA) as LT.
                    destruct beta1_1.
                    { destruct (nf_head_zero _ _ (nf_hered_first _ _ _ NB)).
                      unfold ord_add in EQ.
                      rewrite ord_ltb_irrefl, ord_eqb_refl, <- plus_n_Sm, <- plus_n_O in EQ.
                      inversion EQ as [[EQ1 EQ2 EQ3]].
                      rewrite EQ1 in *.
                      apply coeff_lt.
                      apply le_S_n.
                      destruct (cons_lt_aux _ _ _ _ _ _ LT) as [LT' | [[EQO LT'] | [EQO [EQn LT']]]].
                      { inversion LT'. }
                      { apply LT'. }
                      { inversion LT'. } }
                    { unfold ord_add, ord_ltb in EQ.
                      inversion EQ as [[EQ1 EQ2 EQ3]].
                      rewrite EQ1 in *.
                      inversion LT.
                      inversion H0. } } }
      --  exists (cons (cons (cons a1_1_1 na1_1 a1_1_2) na1 a1_2) na beta).
          rewrite (nf_mult_eval _ _ _ _ _ _ (zero_lt _ _ _)).
          split.
          { reflexivity. }
          { destruct beta.
            { inversion EQ. }
            { refine (cons_nf _ _ _ _ _ _ (nf_hered_first _ _ _ NA) NB).
              destruct beta1.
              { apply zero_lt. }
              { rewrite (nf_mult_eval _ _ _ _ _ _ (zero_lt _ _ _)) in EQ.
                pose proof (nf_cons_head_lt _ _ _ _ _ NA) as LT.
                destruct beta1_1.
                { destruct (nf_head_zero _ _ (nf_hered_first _ _ _ NB)).
                  unfold ord_add in EQ.
                  rewrite ord_ltb_irrefl, ord_eqb_refl, <- plus_n_Sm, <- plus_n_O in EQ.
                  inversion EQ as [[EQ1 EQ2 EQ3]].
                  rewrite EQ1 in *.
                  apply head_lt.
                  apply zero_lt. }
                { unfold ord_add, ord_ltb in EQ.
                  inversion EQ as [[EQ1 EQ2 EQ3]].
                  rewrite EQ1 in *.
                  apply LT. } } } }
Qed.

Theorem ord_lt_succ_cases :
    forall beta alpha,
        ord_lt alpha (ord_succ beta) ->
            nf alpha ->
                nf beta ->
                    alpha = beta \/ ord_lt alpha beta.
Proof.
induction beta as [|b1 IHb1 nb b2 IHb2];
intros alpha LT NA NB.
- left.
  destruct alpha.
  + reflexivity.
  + destruct (cons_lt_aux _ _ _ _ _ _ LT) as [LT' | [[EQO LT'] | [EQO [EQN LT']]]];
    inversion LT'.
- destruct alpha as [| a1 na a2].
  + right.
    apply zero_lt.
  + destruct b1.
    * destruct (nf_head_zero _ _ NB).
      destruct (cons_lt_aux _ _ _ _ _ _ LT) as [LT' | [[EQO LT'] | [EQO [EQN LT']]]];
      try rewrite EQO in *;
      try rewrite EQN in *.
      --  inversion LT'.
      --  destruct (nat_ge_case_type _ _ LT') as [GT | EQ].
          ++  right.
              apply coeff_lt.
              apply (le_S_n _ _ GT).
          ++  left.
              destruct (nf_head_zero _ _ NA).
              apply eq_add_S in EQ.
              destruct EQ.
              reflexivity.
      --  inversion LT'.
    * destruct (cons_lt_aux _ _ _ _ _ _ LT) as [LT' | [[EQO LT'] | [EQO [EQN LT']]]];
      try rewrite EQO in *;
      try rewrite EQN in *.
      --  right.
          apply head_lt.
          apply LT'.
      --  right.
          apply coeff_lt.
          apply LT'.
      --  destruct (IHb2 _ LT' (nf_hered_third _ _ _ NA) (nf_hered_third _ _ _ NB)) as [EQ | LT''].
          ++  destruct EQ.
              left.
              reflexivity.
          ++  right.
              apply tail_lt.
              apply LT''.
Qed.

Lemma ord_ltb_succ_leb :
    forall (alpha beta : ord),
        nf alpha ->
            nf beta ->
                ord_ltb alpha beta = true ->
                    ord_ltb beta (ord_succ alpha) = false.
Proof.
intros alpha beta NA NB LT.
apply ord_ltb_lt in LT.
apply ord_lt_succ in LT.
destruct (ord_lt_succ_cases _ _ LT (nf_nf_succ _ NA) NB) as [EQ | LT'].
- destruct EQ.
  apply ord_ltb_irrefl.
- apply ord_ltb_asymm.
  apply ord_lt_ltb.
  apply LT'.
Qed.

Lemma nf_pred :
    forall alpha,
        nf alpha ->
            nf (ord_pred alpha).
intros alpha NA.
induction alpha as [| a1 IHa1 na a2 IHa2].
- apply zero_nf.
- unfold ord_pred; fold ord_pred.
  destruct a1.
  + destruct (nf_head_zero _ _ NA).
    destruct na.
    * apply zero_nf.
    * apply single_nf.
      apply zero_nf.
  + destruct a2.
    * apply NA.
    * case (ord_pred (cons a2_1 n0 a2_2)) eqn:EQ.
      --  apply single_nf.
          apply (nf_hered_first _ _ _ NA).
      --  apply cons_nf.
          ++  pose proof (nf_cons_head_lt _ _ _ _ _ NA) as LT.
              unfold ord_pred in EQ; fold ord_pred in EQ.
              destruct a2_2;
              destruct a2_1;
              destruct n0;
              inversion EQ as [[EQ1 EQ2 EQ3]];
              destruct EQ1;
              apply LT.
          ++  apply (nf_hered_first _ _ _ NA).
          ++  apply (IHa2 (nf_hered_third _ _ _ NA)).
Qed.

Lemma ord_pred_lt :
    forall alpha,
        nf alpha ->
            is_succ alpha = true ->
                ord_lt (ord_pred alpha) alpha.
Proof.
intros alpha NA UA.
rewrite <- (ord_succ_pred_if_succ _ NA UA) at 2.
apply ord_succ_monot.
Qed.

Lemma mult_right_incr_conv :
    forall (alpha beta gamma : ord),
        Zero < alpha ->
            nf beta ->
                ord_mult alpha beta < ord_mult alpha gamma -> beta < gamma.
Proof.
intros alpha beta gamma LTZA NB LTm.
destruct (ord_semiconnex beta gamma) as [LT | [GT | EQ]].
- apply LT.
- pose proof (mult_right_incr _ _ _ GT LTZA NB) as FAL.
  apply (ord_lt_asymm _ _ LTm) in FAL.
  inversion FAL.
- destruct EQ.
  apply ord_lt_irrefl in LTm.
  inversion LTm.
Qed.

Lemma ord_mult_2_is_add :
    forall (alpha : ord),
        nf alpha ->
            (ord_mult alpha (nat_ord 2)) = ord_add alpha alpha.
Proof.
intros alpha NA.
induction alpha as [| a1 IHa1 na a2 IHa2].
- reflexivity.
- unfold nat_ord, ord_mult, ord_add, mul;
  fold ord_add mul.
  rewrite ord_ltb_irrefl.
  rewrite ord_eqb_refl.
  unfold add, sub.
  fold add sub.
  rewrite two_mul.
  rewrite <- plus_n_Sm.
  rewrite <- plus_n_O.
  reflexivity.
Qed.

Lemma twice_max_ge_add :
    forall (alpha beta : ord),
        nf alpha ->
            nf beta ->
                ord_ltb (ord_mult (ord_max alpha beta) (nat_ord 2)) (ord_add alpha beta) = false.
Proof.
intros alpha beta NA NB.
rewrite (ord_mult_2_is_add _ (nf_ord_max _ _ NA NB)).
unfold ord_max.
destruct (ord_semiconnex_bool alpha beta) as [LT | [GT | EQ]].
- rewrite LT.
  destruct alpha as [| a1 na a2].
  + rewrite ord_zero_add.
    apply ord_ltb_asymm.
    apply ord_lt_ltb.
    apply add_right_incr_non_zero.
    apply ord_ltb_lt.
    apply LT.
  + destruct beta as [| b1 nb b2].
    * inversion LT.
    * unfold ord_add; fold ord_add.
      rewrite ord_ltb_irrefl.
      rewrite ord_eqb_refl.
      destruct (cons_ltb_aux _ _ _ _ _ _ LT) as [LT' | [[EQO LT'] | [EQO [EQN LT']]]].
      --  rewrite LT'.
          apply ord_ltb_asymm.
          apply ord_lt_ltb.
          apply coeff_lt.
          lia.
      --  apply ord_eqb_eq in EQO.
          destruct EQO.
          apply nat_ltb_lt in LT'.
          rewrite ord_ltb_irrefl.
          rewrite ord_eqb_refl.
          apply ord_ltb_asymm.
          apply ord_lt_ltb.
          apply coeff_lt.
          lia.
      --  apply ord_eqb_eq in EQO.
          destruct EQO, EQN.
          rewrite ord_ltb_irrefl.
          rewrite ord_eqb_refl.
          apply ord_ltb_irrefl.
- rewrite (ord_ltb_asymm _ _ GT).
  apply ord_ltb_asymm.
  apply ord_lt_ltb.
  apply add_right_incr.
  apply ord_ltb_lt.
  apply GT.
- apply ord_eqb_eq in EQ.
  destruct EQ.
  rewrite ord_ltb_irrefl.
  apply ord_ltb_irrefl.
Qed.

Lemma add_left_weak_monot :
    forall (alpha beta gamma : ord),
        ord_ltb alpha beta = false ->
            ord_ltb (ord_add alpha gamma) (ord_add beta gamma) = false.
Proof.
induction alpha as [| a1 IHa1 na a2 IHa2];
intros beta gamma GE.
- destruct beta.
  + apply ord_ltb_irrefl.
  + inversion GE.
- destruct gamma as [| g1 ng g2].
  + repeat rewrite ord_add_zero.
    apply GE.
  + destruct beta as [| b1 nb b2];
    unfold ord_add; fold ord_add.
    * destruct (ord_semiconnex_bool a1 g1) as [LT | [GT | EQ]].
      --  rewrite LT.
          apply ord_ltb_irrefl.
      --  rewrite (ord_ltb_asymm _ _ GT).
          rewrite (ord_ltb_neb _ _ GT).
          apply ord_ltb_asymm.
          apply ord_lt_ltb.
          apply head_lt.
          apply ord_ltb_lt.
          apply GT.
      --  apply ord_eqb_eq in EQ.
          destruct EQ.
          rewrite ord_ltb_irrefl.
          rewrite ord_eqb_refl.
          apply ord_ltb_asymm.
          apply ord_lt_ltb.
          apply coeff_lt.
          lia.
    * destruct (ord_semiconnex_bool a1 b1) as [LT | [GT | EQ]].
      --  unfold ord_ltb in GE; fold ord_ltb in GE.
          rewrite LT in GE.
          inversion GE.
      --  unfold ord_add; fold ord_add.
          destruct (ord_semiconnex_bool a1 g1) as [LT' | [GT' | EQ]].
          ++  rewrite LT'.
              rewrite (ord_ltb_trans _ _ _ GT LT').
              apply ord_ltb_irrefl.
          ++  rewrite (ord_ltb_asymm _ _ GT').
              rewrite (ord_ltb_neb _ _ GT').
              destruct (ord_semiconnex_bool b1 g1) as [LT'' | [GT'' | EQ]].
              **  rewrite LT''.
                  unfold ord_ltb; fold ord_ltb.
                  rewrite (ord_ltb_asymm _ _ GT').
                  rewrite (ord_ltb_neb _ _ GT').
                  reflexivity.
              **  rewrite (ord_ltb_asymm _ _ GT'').
                  rewrite (ord_ltb_neb _ _ GT'').
                  unfold ord_ltb; fold ord_ltb.
                  rewrite (ord_ltb_asymm _ _ GT).
                  rewrite (ord_ltb_neb _ _ GT).
                  reflexivity.
              **  apply ord_eqb_eq in EQ.
                  destruct EQ.
                  rewrite ord_ltb_irrefl.
                  rewrite ord_eqb_refl.
                  unfold ord_ltb; fold ord_ltb.
                  rewrite (ord_ltb_asymm _ _ GT).
                  rewrite (ord_ltb_neb _ _ GT).
                  reflexivity.
          ++  apply ord_eqb_eq in EQ.
              destruct EQ.
              rewrite ord_ltb_irrefl.
              rewrite ord_eqb_refl.
              rewrite GT.
              apply ord_ltb_asymm.
              apply ord_lt_ltb.
              apply coeff_lt.
              lia.
      --  apply ord_eqb_eq in EQ.
          destruct EQ.
          unfold ord_ltb in GE; fold ord_ltb in GE.
          rewrite ord_ltb_irrefl in GE.
          rewrite ord_eqb_refl in GE.
          destruct (nat_semiconnex_bool na nb) as [LT | [GT | EQ]].
          ++  rewrite LT in GE.
              inversion GE.
          ++  destruct (ord_semiconnex_bool a1 g1) as [LT' | [GT' | EQ]].
              **  rewrite LT'.
                  apply ord_ltb_irrefl.
              **  rewrite (ord_ltb_asymm _ _ GT').
                  rewrite (ord_ltb_neb _ _ GT').
                  unfold ord_ltb; fold ord_ltb.
                  rewrite ord_ltb_irrefl.
                  rewrite ord_eqb_refl.
                  rewrite GT.
                  rewrite (nat_ltb_asymm _ _ GT).
                  reflexivity.
              **  apply ord_eqb_eq in EQ.
                  destruct EQ.
                  rewrite ord_ltb_irrefl.
                  rewrite ord_eqb_refl.
                  apply ord_ltb_asymm.
                  apply ord_lt_ltb.
                  apply coeff_lt.
                  apply nat_ltb_lt in GT.
                  lia.
          ++  apply nat_eqb_eq in EQ.
              destruct EQ.
              rewrite nat_ltb_irrefl in GE.
              destruct (ord_semiconnex_bool a1 g1) as [LT' | [GT' | EQ]].
              **  rewrite LT'.
                  apply ord_ltb_irrefl.
              **  rewrite (ord_ltb_asymm _ _ GT').
                  rewrite (ord_ltb_neb _ _ GT').
                  unfold ord_ltb; fold ord_ltb.
                  rewrite ord_ltb_irrefl.
                  rewrite ord_eqb_refl.
                  rewrite nat_ltb_irrefl.
                  apply IHa2.
                  apply GE.
              **  apply ord_eqb_eq in EQ.
                  destruct EQ.
                  rewrite ord_ltb_irrefl.
                  rewrite ord_eqb_refl.
                  unfold ord_ltb; fold ord_ltb.
                  rewrite ord_ltb_irrefl.
                  rewrite ord_eqb_refl.
                  rewrite nat_ltb_irrefl.
                  apply ord_ltb_irrefl.
Qed.

(********)
(*Inline elements from Casteran's Work*)
(********)
Declare Module R : rpo.RPO.
Import R.

Inductive nf2 : ord -> ord -> Prop :=
| nf2_z : forall a, nf2 Zero a
| nf2_c : forall a a' n' b', ord_lt a' a ->
                             nf2 (cons a' n' b') a.

Lemma nf_of_finite :
    forall n b,
        nf (cons Zero n b) ->
            b = Zero.
Proof.
intros n b H; inversion_clear H.
- trivial.
- inversion H0.
Qed.     

Definition nf_rect :
    forall P : ord -> Type,
        P Zero ->
            (forall n: nat, 
                P (cons Zero n Zero))
            ->  (forall a n b n' b',
                    nf (cons a n b) ->
                        P (cons a n b) ->
                            nf2 b' (cons a n b) ->
                                nf b' ->
                                    P b' ->
                                        P (cons (cons a n b) n' b'))
                ->  forall a,
                        nf a ->
                            P a.
Proof.
intros P H0 Hfinite Hcons.
induction a.
- trivial.
- generalize IHa1; case a1.
  + intros IHc0 H.
    rewrite (nf_of_finite _ _ H).
    apply Hfinite.
  + intros c n0 c0 IHc0 H2; apply Hcons.
    * inversion H2; auto.
    * apply IHc0.
      inversion H2; auto.
    * inversion H2.
      apply nf2_z.
      apply nf2_c.
      auto.
    * inversion H2; auto.
      apply zero_nf.
    * apply IHa2.
      inversion H2; auto.
      apply zero_nf.
Defined.

Section restricted_recursion.

Variables (A:Type)(P:A->Prop)(R:A->A->Prop).

Definition restrict (a b:A):Prop := P a /\ R a b /\ P b.

Definition well_founded_P := forall (a:A), P a -> Acc restrict a.

Definition P_well_founded_induction_type : well_founded_P  ->
  forall X : A -> Type,
    (forall x : A, P x -> (forall y : A,P y-> R y x -> X y) -> X x) ->
        forall a : A, P a -> X a.
intros W X H a. pattern a; eapply well_founded_induction_type with (R:=restrict).
- unfold well_founded. split. unfold well_founded_P in W. intros; apply W. case H0. auto.
- intros; apply H. auto. intros; apply X0.
  + unfold restrict; auto.
  + auto.
Defined.

End restricted_recursion.
 
Theorem AccElim3 : forall A B C:Type,
  forall (RA:A->A->Prop)
        (RB:B->B->Prop)
        (RC:C->C->Prop),
  forall (P : A -> B -> C ->  Prop),
    (forall x y z,
        (forall (t : A), RA t x -> 
            forall y' z', Acc RB y' -> Acc RC z' ->
                  P t y' z') -> (forall (t : B), RB t y -> 
          forall z', Acc RC z' -> P x t z') ->
    (forall (t : C), RC t z -> P x y t) -> 
    P x y z) -> forall x y z, Acc RA x -> Acc RB y -> Acc RC z -> P x y z.
Proof.
intros A B C RA RB RC P H x y z Ax; generalize y z; clear y z. elim Ax; clear Ax x; intros x _ Hrecx y z Ay; generalize z; clear z. elim Ay; clear Ay y; intros y _ Hrecy z Az; elim Az; clear Az z; auto. 
Qed.

Theorem accElim3:
 forall (A B C:Set)(RA : A -> A ->Prop) (RB : B-> B-> Prop)
                   (RC : C -> C -> Prop)(P : A -> B -> C ->  Prop),
 (forall x y z ,
  (forall (t : A), RA t x ->  P t y z) ->
  (forall (t : B), RB t y ->  P x t z) ->
  (forall (t : C), RC t z ->  P x y t) ->  P x y z) ->
 forall x y z, Acc RA x -> Acc RB y -> Acc RC z ->  P x y z.
Proof.
intros A B C RA RB RC P H x y z Ax Ay Az. generalize Ax Ay Az. pattern x, y, z;
 eapply AccElim3 with (RA:=RA)(RB:=RB)(RC:=RC) ;eauto. intros; apply H.
- intros;apply H0; auto. eapply Acc_inv;eauto.
- intros;apply H1; auto. eapply Acc_inv;eauto.
- intros;apply H2; auto. eapply Acc_inv;eauto.
Qed.

Module  Eps0_sig <: term.Signature.
Inductive symb0 : Set := nat_0 | nat_S | ord_zero | ord_cons.
Definition symb := symb0.

Lemma eq_symbol_dec : forall f1 f2 : symb, {f1 = f2} + {f1 <> f2}.
Proof.
intros; decide equality.
Qed.

(** The arity of a symbol contains also the information about built-in theories as in CiME *)
Inductive arity_type : Set :=
| AC : arity_type
| C : arity_type
| Free : nat -> arity_type.

Definition arity : symb -> arity_type := fun f => match f with
| nat_0 => Free 0
| ord_zero => Free 0
| nat_S => Free 1
| ord_cons => Free 3
end.

End Eps0_sig.

(** * Module Type Variables. 
 There are almost no assumptions, except a decidable equality. *) 
Module Vars <: term.Variables.
Inductive empty_set : Set := .
Definition var := empty_set.

Lemma eq_variable_dec : forall v1 v2 : var, {v1 = v2} + {v1 <> v2}.
Proof.
intros; decide equality.
Qed.

End Vars.

Module  Eps0_prec <: Precedence.
Definition A : Set := Eps0_sig.symb.
Import Eps0_sig.
Require Import Relations.

Definition prec : relation A := fun f g => match f, g with
| nat_0, nat_S => True
| nat_0, ord_zero => True
| nat_0, ord_cons => True
| ord_zero, nat_S => True
| ord_zero, ord_cons => True
| nat_S, ord_cons => True
| _, _ => False
end.

Inductive status_type : Set :=
| Lex : status_type
| Mul : status_type.

Definition status : A -> status_type := fun f => Lex.

Lemma prec_dec : forall a1 a2 : A, {prec a1 a2} + {~ prec a1 a2}.
Proof.
intros a1 a2; destruct a1; destruct a2; ((right; intro; contradiction)||(left;simpl;trivial)).
Qed.

Lemma prec_antisym : forall s, prec s s -> False.
Proof.
intros s; destruct s; simpl; trivial.
Qed.

Lemma prec_transitive : transitive A prec.
Proof.
intros s1 s2 s3; destruct s1; destruct s2; destruct s3; simpl; intros; trivial; contradiction.
Qed.

End Eps0_prec.

Module Eps0_alg <: term.Term := term.Make (Eps0_sig) (Vars).
Module Eps0_rpo <: RPO := rpo.Make (Eps0_alg) (Eps0_prec).
Import Eps0_alg.
Import Eps0_rpo.
Import Eps0_sig.

Remark R1 : Acc P.prec nat_0. 
 split.
 destruct y; try contradiction.
Qed.
#[local] Hint Resolve R1 : ords.

Remark R2 : Acc P.prec ord_zero. 
 split.
 destruct y; try contradiction; auto with ords.
Qed.
#[local] Hint Resolve R2 : ords.

Remark R3 : Acc P.prec nat_S.
 split.
 destruct y; try contradiction; auto with ords.
Qed.
#[local] Hint Resolve R3 : ords.

Remark R4 : Acc P.prec ord_cons.
 split.
 destruct y; try contradiction; auto with ords.
Qed.
#[local] Hint Resolve R4 : ords.

Theorem well_founded_rpo : well_founded rpo.
Proof.
apply wf_rpo. red. destruct a; auto with ords.
Qed.

Fixpoint nat_2_term (n:nat) : term :=
match n with
| 0 => (Term nat_0 Datatypes.nil)
| S p => Term nat_S ((nat_2_term p)::Datatypes.nil)
end.

Fixpoint ord_2_term (alpha : ord) : term := 
match alpha with
| Zero => Term ord_zero Datatypes.nil
|cons a n b => Term ord_cons (ord_2_term a :: nat_2_term n ::ord_2_term b::Datatypes.nil)
end.

Fixpoint ord_size (o : ord):nat :=
match o with
|Zero => 0
| cons a n b => S (ord_size a + n + ord_size b)%nat
end.

Lemma nat_lt_cons : forall (n:nat) a p  b , rpo (nat_2_term n) (Term ord_cons (a::p::b::Datatypes.nil)).
Proof.
induction n;simpl.
- constructor 2.
  + simpl; trivial.
  + destruct 1.
- constructor 2.
  + simpl; trivial.
  + inversion_clear 1.
    * subst s';apply IHn.
    * case H0.
Qed.

Lemma nat_2_term_mono : forall n n', (n < n')%nat -> rpo (nat_2_term n) (nat_2_term n').
Proof.
induction 1; simpl; eapply Subterm. eleft. esplit. constructor. eleft. esplit. constructor. auto.
Qed.

Theorem lt_inc_rpo_0 : forall n,
    forall o' o, (ord_size o + ord_size o' <= n)%nat->
        ord_lt o o' -> nf o -> nf o' -> 
            rpo (ord_2_term o) (ord_2_term o').
Proof.
induction n. destruct o'. inversion 2. destruct o. simpl. inversion 1. simpl;inversion 1. inversion 2.
- simpl. intros; apply Top_gt. simpl;trivial. inversion 1.
- simpl; intros; apply Top_eq_lex. simpl;trivial.
  + left.
    * apply IHn; auto.
      { subst o;subst o'. unfold ord_size in H. fold ord_size in H. lia. }
      { inversion H4; auto. }
      { inversion H5; auto. }
    * simpl. lia.
 + inversion_clear 1.
    * subst s'. change (rpo (ord_2_term a) (ord_2_term (cons a' n' b'))). apply IHn;auto.
      { subst o;subst o'. unfold ord_size in *. fold ord_size in *. lia. }
      { refine (ord_lt_trans _ _ _ (ord_lt_self _ Zero 0) (head_lt _ _ _ _ _ _ H1)). }
      { inversion H4; auto. }
    * simpl in H7. decompose [or] H7.
      { subst s'. apply nat_lt_cons. }
      { subst s'. change (rpo (ord_2_term b) (ord_2_term (cons a' n' b'))). apply IHn;auto.
        { subst o;subst o'. unfold ord_size in *. fold ord_size in *. lia. }
        { inversion H4. apply zero_lt. apply head_lt. apply (ord_lt_trans _ _ _ H10 H1). }
        { inversion H4; auto. apply zero_nf. } }
      { case H8. }
- intros. simpl;apply Top_eq_lex. auto. constructor 2. constructor 1. apply nat_2_term_mono. auto. auto. inversion_clear 1.
  + subst s'.  change (rpo (ord_2_term a) (ord_2_term (cons a n' b'))). apply IHn;auto.
    * subst o;subst o'. unfold ord_size in *. fold ord_size in *. lia.
    * apply ord_lt_self.
    * inversion H4;auto.
  + simpl in H7. decompose [or] H7. subst s'. apply nat_lt_cons.
    * subst s'. change (rpo (ord_2_term b) (ord_2_term (cons a n' b'))). apply IHn;auto.
      { subst o;subst o'. unfold ord_size in *. fold ord_size in *. lia. }
      { inversion H4.
        { apply zero_lt. }
        { apply head_lt. auto. } }
      { inversion H4;auto. apply zero_nf. }
    * case H8.
- simpl. intros;apply Top_eq_lex. auto.
  + right. right. left.
    * apply IHn; auto.
      { subst o;subst o';auto. unfold ord_size in H. fold ord_size in H. lia. }
      { inversion H4;auto. apply zero_nf. }
      { inversion H5;auto. apply zero_nf. }
    * auto.
  + inversion_clear 1. subst s'. eapply Subterm. 2:eleft. left;auto. simpl in H7. decompose [or] H7.
    * subst s'. apply nat_lt_cons.
    * subst s'. change (rpo (ord_2_term b) (ord_2_term (cons a n0 b'))). apply IHn; auto.
      { subst o;subst o'. unfold ord_size in *. fold ord_size in *. lia. }
      { apply (ord_lt_trans _ _ _ H1). inversion H5.
        apply zero_lt. apply head_lt. apply H10. }
      { inversion H4; auto. apply zero_nf. }
    * case H8.
Qed.

Let R := restrict ord nf ord_lt.

Lemma R_inc_rpo : forall o o', R o o' -> rpo (ord_2_term o) (ord_2_term o').
Proof.
intros o o' (H,(H1,H2)). eapply lt_inc_rpo_0;auto.
Qed. 

Lemma nf_Wf : well_founded_P _ nf ord_lt.
Proof.
unfold well_founded_P. intros. unfold restrict. generalize (Acc_inverse_image _ _ rpo ord_2_term a (well_founded_rpo (ord_2_term a))). intro.
eapply  Acc_incl  with  (fun x y : ord => rpo (ord_2_term x) (ord_2_term y)). 
- red. apply R_inc_rpo.
- auto.
Qed.

Definition transfinite_induction :
 forall (P: ord -> Type),
   (forall x: ord, nf x ->
                   (forall y: ord, nf y ->  ord_lt y x -> P y) -> P x) ->
    forall a, nf a -> P a.
Proof.
intros; eapply P_well_founded_induction_type; eauto. eexact nf_Wf;auto.
Defined.

(******************)
(*End Casteran inline*)
(******************)


Lemma ord_2_exp_succ_mult :
    forall (alpha : ord),
        nf alpha ->
            ord_2_exp (ord_succ alpha) = ord_mult (ord_2_exp alpha) (nat_ord 2).
Proof.
apply (transfinite_induction (fun alpha => ord_2_exp (ord_succ alpha) = ord_mult (ord_2_exp alpha) (nat_ord 2))).
intros alpha NA IND.
destruct alpha as [| a1 na a2].
- reflexivity.
- destruct a1.
  + destruct (nf_head_zero _ _ NA).
    unfold ord_succ, ord_2_exp.
    unfold pow; fold pow.
    destruct (2 ^ na).
    * reflexivity.
    * destruct (2 * S n).
      --  reflexivity.
      --  unfold nat_ord at 2 3.
          unfold ord_mult.
          unfold mul; fold mul.
          rewrite (plus_comm 2).
          rewrite <- plus_n_Sm.
          unfold sub; fold sub.
          rewrite minus_n_0.
          rewrite <- plus_n_Sm.
          repeat rewrite <- plus_n_O.
          rewrite <- plus_n_Sm.
          rewrite two_mul.
          reflexivity.
  + unfold ord_succ; fold ord_succ.
    unfold ord_2_exp; fold ord_2_exp.
    destruct a1_1.
    * destruct n.
      --  destruct a2.
          ++  reflexivity.
          ++  rewrite (IND _ (nf_hered_third _ _ _ NA) (head_lt _ _ _ _ _ _ (nf_cons_head_lt _ _ _ _ _ NA))).
              rewrite ord_mult_assoc.
              reflexivity.
      --  rewrite (IND _ (nf_hered_third _ _ _ NA)).
          rewrite ord_mult_assoc.
          reflexivity.
          inversion NA.
          ++  apply zero_lt.
          ++  apply head_lt.
              apply H2.
    * rewrite (IND _ (nf_hered_third _ _ _ NA)).
      rewrite ord_mult_assoc.
      reflexivity.
      inversion NA.
      --  apply zero_lt.
      --  apply head_lt.
          apply H2.
Qed.

Lemma ord_succ_lt_exp_succ :
    forall (alpha : ord),
        nf alpha ->
            ord_lt Zero alpha ->
                ord_lt (ord_succ (ord_2_exp alpha)) (ord_2_exp (ord_succ alpha)).
Proof.
intros alpha NA LT.
rewrite (ord_2_exp_succ_mult _ NA).
apply (ord_gt_one_succ_lt_dub _ (nf_2_exp _ NA) (ord_gt_zero_exp_gt_one _ NA LT)).
Qed.

Lemma ord_2_exp_eval :
    forall alpha,
        nf alpha ->
            ord_2_exp (ord_mult (cons (cons Zero 0 Zero) 0 Zero) alpha) = cons alpha 0 Zero.
Proof.
apply transfinite_induction.
intros alpha NA IND.
destruct alpha as [| a1 na a2].
- reflexivity.
- destruct a1 as [| a1_1 na1 a1_2].
  + destruct (nf_head_zero _ _ NA).
    unfold ord_mult, mul, sub.
    rewrite <- plus_n_O.
    rewrite minus_n_0.
    reflexivity.
  + rewrite (nf_mult_eval _ _ _ _ _ _ (zero_lt _ _ _)).
    destruct a1_1.
    * destruct (nf_head_zero _ _ (nf_hered_first _ _ _ NA)).
      unfold ord_add, ord_ltb, ord_eqb.
      rewrite <- plus_n_Sm, <- plus_n_O.
      destruct a2.
      --  reflexivity.
      --  unfold ord_2_exp; fold ord_2_exp.
          rewrite (IND _ (nf_hered_third _ _ _ NA)).
          ++  rewrite (nf_mult_eval _ _ _ _ _ _ (zero_lt _ _ _)).
              unfold ord_add, add.
              fold add.
              pose proof (nf_cons_head_lt _ _ _ _ _ NA) as LT.
              rewrite (ord_ltb_asymm _ _ (ord_lt_ltb _ _ LT)).
              rewrite (ord_ltb_neb _ _ (ord_lt_ltb _ _ LT)).
              reflexivity.
          ++  apply (ord_lt_trans _ _ _ (nf_cons_decr _ _ _ NA) (tail_lt _ _ _ _ (zero_lt _ _ _))).
    * unfold ord_add, ord_ltb, ord_eqb.
      destruct a2.
      --  reflexivity.
      --  unfold ord_2_exp; fold ord_2_exp.
          rewrite (IND _ (nf_hered_third _ _ _ NA)).
          ++  rewrite (nf_mult_eval _ _ _ _ _ _ (zero_lt _ _ _)).
              unfold ord_add, add.
              fold add.
              pose proof (nf_cons_head_lt _ _ _ _ _ NA) as LT.
              rewrite (ord_ltb_asymm _ _ (ord_lt_ltb _ _ LT)).
              rewrite (ord_ltb_neb _ _ (ord_lt_ltb _ _ LT)).
              reflexivity.
          ++  apply (ord_lt_trans _ _ _ (nf_cons_decr _ _ _ NA) (tail_lt _ _ _ _ (zero_lt _ _ _))).
Qed.

Definition exp_monot (alpha : ord ) : Prop :=
      forall beta,
          nf beta ->
              ord_lt beta alpha ->
                  ord_lt (ord_2_exp beta) (ord_2_exp alpha).

Definition exp_monot_2 (alpha beta : ord ) : Prop :=
      ord_lt beta alpha ->
          ord_lt (ord_2_exp beta) (ord_2_exp alpha).

Lemma ord_2_exp_monot :
    forall alpha,
        nf alpha ->
            forall beta,
                nf beta ->
                    beta < alpha ->
                        ord_2_exp beta < ord_2_exp alpha.
Proof.
apply (transfinite_induction exp_monot).
unfold exp_monot.
intros alpha NA IND beta NB LT.
destruct alpha as [| a1 na a2].
- inversion LT.
- case (is_succ (cons a1 na a2)) eqn:UA.
  + rewrite <- (ord_succ_pred_if_succ _ NA UA) in LT.
    destruct (ord_lt_succ_cases _ _ LT NB (nf_pred _ NA)) as [EQ | LT'];
    rewrite <- (ord_succ_pred_if_succ _ NA UA).
    * destruct EQ.
      rewrite (ord_2_exp_succ_mult _ NB).
      refine (ord_mult_monot _ _ (coeff_lt _ _ _ _ _ _) (single_nf _ _ zero_nf) (ord_2_exp_geq_1 _ NB)).
      lia.
    * apply (ord_lt_trans _ (ord_2_exp (ord_pred (cons a1 na a2)))).
      --  apply (IND _ (nf_pred _ NA) (ord_pred_lt _  NA UA) _ NB LT').
      --  rewrite (ord_2_exp_succ_mult _ (nf_pred _ NA)).
          refine (ord_mult_monot _ _ (coeff_lt _ _ _ _ _ _) (single_nf _ _ zero_nf) (ord_2_exp_geq_1 _ (nf_pred _ NA))).
          lia.
  + refine (transfinite_induction (exp_monot_2 (cons a1 na a2)) _ _ NB LT). 
    unfold exp_monot_2.
    intros gamma NG IND2 LT'. 
    destruct gamma as [|g1 ng g2].
    * destruct a1.
      --  destruct (nf_head_zero _ _ NA).
          unfold ord_2_exp, pow.
          fold pow.
          case (2^na) eqn:EQ.
          ++  apply nat_2_exp_not_zero in EQ.
              inversion EQ.
          ++  apply coeff_lt.
              fold add.
              lia.
      --  destruct a1_1;
          destruct n;
          apply (ord_mult_exp_monot _ _ _ (nf_hered_third _ _ _ NA) (head_lt _ _ _ _ _ _ (zero_lt _ _ _))).
  * case (is_succ (cons g1 ng g2)) eqn:UG.
    --  destruct (ord_not_succ_is_mul _ NA UA) as [delta [EQ ND]].
        rewrite EQ.
        rewrite (ord_2_exp_eval _ ND).
        rewrite <- (ord_succ_pred_if_succ _ NG UG).
        rewrite (ord_2_exp_succ_mult _ (nf_pred _ NG)).
        pose proof (IND2 _ (nf_pred _ NG) (ord_pred_lt _ NG UG) (ord_lt_trans _ _ _ (ord_pred_lt _ NG UG) LT')) as IE.
        rewrite EQ in IE.
        rewrite (ord_2_exp_eval _ ND) in IE.
        case (ord_2_exp (ord_pred (cons g1 ng g2))) eqn:Y.
        ++  apply zero_lt.
        ++  destruct (cons_lt_aux _ _ _ _ _ _ IE) as [IE1 | [[EQO IE1] | [EQO [EQN IE1]]]].
            **  apply head_lt.
                apply IE1.
            **  inversion IE1.
            **  inversion IE1.
    --  destruct (ord_not_succ_is_mul _ NA UA) as [delta [EQ ND]].
        rewrite EQ in *.
        rewrite (ord_2_exp_eval _ ND).
        destruct (ord_not_succ_is_mul _ NG UG) as [epsilon [EQ' NE]].
        rewrite EQ' in *.
        rewrite (ord_2_exp_eval _ NE).
        apply (mult_right_incr_conv _ _ _ (zero_lt _ _ _) NE) in LT'.
        apply head_lt.
        apply LT'.
Qed.

Lemma ord_max_exp_comm :
    forall (alpha beta : ord),
        nf alpha ->
            nf beta ->
                (ord_max (ord_2_exp alpha) (ord_2_exp beta)) = (ord_2_exp (ord_max alpha beta)).
Proof.
intros alpha beta NA NB.
unfold ord_max.
destruct (ord_semiconnex_bool alpha beta) as [LT | [GT | EQ]].
- rewrite (ord_lt_ltb _ _ (ord_2_exp_monot _ NB _ NA (ord_ltb_lt _ _ LT))).
  rewrite LT.
  reflexivity.
- rewrite (ord_ltb_asymm _ _ (ord_lt_ltb _ _ (ord_2_exp_monot _ NA _ NB (ord_ltb_lt _ _ GT)))).
  rewrite (ord_ltb_asymm _ _ GT).
  reflexivity.
- apply ord_eqb_eq in EQ.
  destruct EQ.
  repeat rewrite ord_ltb_irrefl.
  reflexivity.
Qed.

Lemma dub_succ_geb_exp_succ_eqb :
    forall (alpha : ord),
        ord_lt Zero alpha ->
            nf alpha ->
                ord_ltb (ord_succ (ord_succ (ord_2_exp alpha))) (ord_2_exp (ord_succ alpha)) = false ->
                    ord_eqb (ord_succ (ord_succ (ord_2_exp alpha))) (ord_2_exp (ord_succ alpha)) = true.
Proof.
intros alpha LTZA NA GE.
destruct alpha.
- inversion LTZA.
- pose proof (ord_succ_lt_exp_succ _ NA LTZA) as LT.
  apply ord_lt_succ in LT.
  destruct (ord_lt_succ_cases _ _ LT (nf_nf_succ _ (nf_nf_succ _ (nf_2_exp _ NA))) (nf_2_exp _ (nf_nf_succ _ NA))) as [EQ | LT'].
  + rewrite EQ.
    apply ord_eqb_refl.
  + apply ord_lt_ltb in LT'.
    rewrite LT' in GE.
    inversion GE.
Qed.

Lemma exp_succ_lt_add :
    forall (alpha beta : ord),
        nf alpha ->
            nf beta ->
                ord_ltb (ord_2_exp (ord_succ (ord_max alpha beta))) (ord_add (ord_2_exp alpha) (ord_2_exp beta)) = false.
Proof.
intros alpha beta NA NB.
rewrite (ord_2_exp_succ_mult _ (nf_ord_max _ _ NA NB)).
rewrite <- (ord_max_exp_comm _ _ NA NB).
apply (twice_max_ge_add _ _ (nf_2_exp _ NA) (nf_2_exp _ NB)).
Qed.

Lemma dub_succ_exp_lt_exp_dub_succ:
    forall (alpha : ord),
        nf alpha ->
            (ord_succ (ord_succ (ord_2_exp alpha))) < (ord_2_exp (ord_succ (ord_succ alpha))).
Proof.
intros alpha NA.
destruct alpha.
- unfold ord_succ, ord_2_exp, nat_ord, pow, mul, plus.
  apply coeff_lt.
  unfold lt.
  reflexivity.
- apply (ord_lt_trans _ _ _ (ord_lt_succ _ _ (ord_succ_lt_exp_succ _ NA (zero_lt _ _ _)))).
  apply (ord_succ_lt_exp_succ _ (nf_nf_succ _ NA) (ord_lt_trans _ _ _ (zero_lt _ _ _) (ord_succ_monot _))).
Qed.

Close Scope cantor_scope. 