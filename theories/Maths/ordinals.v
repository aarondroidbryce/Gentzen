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

Lemma plus_succ_ne : forall n m, ~(S(n + m) = n).
Proof.
intros. lia.
Qed.


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
| cons (cons Zero 0 _) n b =>
    ord_mult (cons (cons Zero n Zero) 0 Zero) (ord_2_exp b)
| cons (cons Zero (S n) _) m b =>
    ord_mult (cons (cons (cons Zero n Zero) m Zero) 0 Zero) (ord_2_exp b)
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

Lemma ord_succ_is_succ : forall alpha, nf alpha -> is_succ (ord_succ alpha) = true.
Proof.
intros. induction alpha.
- unfold ord_succ. auto.
- destruct alpha1.
  + inversion H. symmetry in H0. destruct H0,H2,H3. auto. inversion H3.
  + unfold ord_succ. fold ord_succ. unfold is_succ. fold is_succ. destruct alpha2; auto. pose (IHalpha1 (nf_hered_first _ _ _ H)).  pose (IHalpha2 (nf_hered_third _ _ _ H)). unfold ord_succ. fold ord_succ. destruct alpha2_1; auto. 
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

Lemma ord_pred_succ : forall alpha, nf alpha -> ord_pred (ord_succ alpha) = alpha.
Proof.
intros. induction alpha.
- auto.
- destruct alpha1.
  + inversion H. destruct H2,H3. auto. inversion H3.
  + pose (IHalpha2 (nf_hered_third _ _ _ H)). unfold ord_succ. fold ord_succ. unfold ord_pred. fold ord_pred. case (ord_succ alpha2) eqn:X.
    * unfold ord_pred in e. rewrite e. auto.
    * rewrite e. auto.
Qed.

Lemma ord_succ_pred_if_succ : forall alpha, nf alpha -> is_succ alpha = true -> ord_succ (ord_pred alpha) = alpha.
Proof.
intros. induction alpha. inversion H0. unfold ord_pred. fold ord_pred. destruct alpha2.
- destruct alpha1.
  + destruct n; auto.
  + inversion H0.
- unfold ord_succ. fold ord_succ. destruct alpha1. inversion H. inversion H4. pose (IHalpha2 (nf_hered_third _ _ _ H)). rewrite e. auto. simpl in H0. destruct alpha2_2. destruct alpha2_1. auto. inversion H0. auto.
Qed.

Lemma ord_mult_omega_not_succ : forall alpha, nf alpha -> is_succ (ord_mult (cons (cons Zero 0 Zero) 0 Zero) alpha) = false.
Proof.
intros. induction alpha. auto. pose (IHalpha1 (nf_hered_first _ _ _ H)). pose (IHalpha2 (nf_hered_third _ _ _ H)).
unfold ord_mult. fold ord_mult. destruct alpha1.
- inversion H. auto. inversion H3.
- unfold is_succ. fold is_succ. case (ord_mult (cons (cons Zero 0 Zero) 0 Zero) alpha2) eqn:X; auto. case (ord_add (cons Zero 0 Zero) (cons alpha1_1 n0 alpha1_2)) eqn:X1; auto.
  unfold ord_add in X1. destruct alpha1_1. rewrite ord_ltb_irrefl in X1. rewrite ord_eqb_refl in X1. inversion X1. rewrite (ord_lt_ltb _ _ (zero_lt _ _ _)) in X1. inversion X1.
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
- apply (lt_trans _(ord_max alpha beta)); auto. apply ord_succ_monot.
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


Declare Module R : rpo.RPO.
Import R.

Inductive nf2 : ord -> ord -> Prop :=
| nf2_z : forall a, nf2 Zero a
| nf2_c : forall a a' n' b', ord_lt a' a ->
                             nf2 (cons a' n' b') a.

Lemma nf_of_finite : forall  n b, nf (cons Zero n b) ->
b = Zero.
Proof.
intros n b H; inversion_clear H.
- trivial.
- case (zero_minimal a');auto.
Qed.     

Definition nf_rect : forall P : ord -> Type,
  P Zero ->
    (forall n: nat,  P (cons Zero n Zero)) ->
        (forall a n b n' b', nf (cons a n b) -> P (cons a n b)-> nf2 b' (cons a n b) ->
                        nf b' -> P b' -> P (cons (cons a n b) n' b')) ->
          forall a, nf a -> P a.
Proof.
intros P H0 Hfinite Hcons. induction a.
- trivial.
- generalize IHa1; case a1.
  + intros IHc0 H. rewrite (nf_of_finite _ _ H). apply Hfinite.
  + intros c n0 c0 IHc0 H2; apply Hcons.
    * inversion H2; auto.
    * apply IHc0. inversion H2; auto.
    * inversion H2. apply nf2_z. apply nf2_c. auto.
    * inversion H2; auto. apply zero_nf.
    * apply IHa2. inversion H2; auto. apply zero_nf.
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
Hint Resolve R1.

Remark R2 : Acc P.prec ord_zero. 
 split.
 destruct y; try contradiction; auto.
Qed.
Hint Resolve R2.

Remark R3 : Acc P.prec nat_S.
 split.
 destruct y; try contradiction;auto.
Qed.
Hint Resolve R3.

Remark R4 : Acc P.prec ord_cons.
 split.
 destruct y; try contradiction;auto.
Qed.
Hint Resolve R4.

Theorem well_founded_rpo : well_founded rpo.
Proof.
apply wf_rpo. red. destruct a; auto.
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
      { apply ord_lt_first. auto. }
      { inversion H4; auto. }
    * simpl in H7. decompose [or] H7.
      { subst s'. apply nat_lt_cons. }
      { subst s'. change (rpo (ord_2_term b) (ord_2_term (cons a' n' b'))). apply IHn;auto.
        { subst o;subst o'. unfold ord_size in *. fold ord_size in *. lia. }
        { inversion H4. apply zero_lt. apply head_lt. apply (lt_trans _ _ _ H10 H1). }
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
      { apply (lt_trans _ _ _ H1). apply ord_lt_third_nf. auto. }
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
    * simpl. case n'.
      { case_eq alpha2; intros.
        { repeat apply single_nf. apply zero_nf. }
        { rewrite <- H. apply nf_mult.
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

Lemma one_left_mult_ident : forall (alpha : ord), nf alpha -> alpha = ord_mult (nat_ord 1) alpha.
Proof.
intros.
induction alpha as [| alpha1 IHalpha1 n_alpha alpha2 IHalpha2].
- auto.
- destruct alpha1.
  + simpl. inversion H. rewrite plus_n_0. rewrite minus_n_0. auto. inversion H3.
  + simpl. simpl in IHalpha2. rewrite <- (IHalpha2 (nf_hered_third _ _ _ H)). auto.
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
    * simpl. case n''.
      { case_eq b'; intros.
        { apply zero_lt. }
        { rewrite <- H. apply nf_hered_third in nf_b. apply ord_mult_nonzero.
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
intros. apply ord_mult_exp_monot_aux2.
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
    * destruct n'.
      { case_eq b; intros.
        { assert (b' = Zero). { inversion nf_alpha. inversion H1. auto. inversion H7. inversion H4. auto. inversion H9. } rewrite H0. destruct n.
          { right. auto. }
          { left. apply ord_mult_exp_monot. apply Zero_nf. apply head_lt. apply coeff_lt. lia. } }
        { assert (b' = Zero). { inversion nf_alpha. inversion H1. auto. inversion H7. inversion H4. auto. inversion H9. } rewrite H0 in *.
          left. rewrite <- H. assert (exists p, b = cons Zero p Zero).  { inversion nf_alpha. rewrite <- H4 in H. inversion H. inversion H4; inversion H9. symmetry in H8,H9,H10,H11. destruct H7,H8,H9,H10,H11. inversion H6. exists n'. auto. inversion H10. }
          destruct H1 as [p Hp]. rewrite Hp. simpl. case_eq (2^p + (2^p + 0)). intros. rewrite plus_n_0 in H1. pose (exp_succ p). lia. intros. simpl. destruct n. destruct n1. pose (nat_2_exp_succ_not_one p). lia. apply coeff_lt. lia. apply head_lt. apply coeff_lt. lia. } }
      { pose (nf_hered_first _ _ _ nf_alpha). inversion n0.
        { symmetry in H. destruct H,H1,H2. left. apply ord_mult_exp_monot. apply (nf_hered_third _ _ _ nf_alpha). apply head_lt. apply head_lt. apply zero_lt. }
        { left. apply ord_mult_exp_monot.
          { apply (nf_hered_third _ _ _ nf_alpha). }
          { repeat apply head_lt. apply omega_exp_incr'. } } }
    * left. apply ord_mult_exp_monot.
      { apply (nf_hered_third _ _ _ nf_alpha). }
      { repeat apply head_lt. apply omega_exp_incr'. }
Qed.


Lemma nat_lt_omega : forall n alpha, Zero < alpha -> nat_ord n < (cons alpha 0 Zero).
Proof.
intros. destruct n. simpl. apply zero_lt. simpl. apply head_lt. auto.
Qed.

Arguments ord_2_exp : simpl nomatch.

Lemma ord_lt_nat_is_nat : forall alpha n beta m, nf (cons alpha n beta) -> ord_lt (cons alpha n beta) (cons Zero m Zero) -> (n < m)%nat /\ Zero = alpha /\ Zero = beta.
Proof.
intros. inversion H0. inversion H2. symmetry in H5,H7. destruct H1,H3,H4,H5,H6,H7. repeat split; auto. inversion H. auto. inversion H5. inversion H2.
Qed.

Lemma ord_lt_nat_type : forall alpha n, nf alpha -> ord_lt alpha (cons Zero n Zero) -> (Zero = alpha) + {m : nat & (m < n)%nat /\ cons Zero m Zero = alpha}.
Proof.
intros. destruct alpha.
- auto.
- right. destruct (ord_lt_nat_is_nat _ _ _ _ H H0) as [X1 [X2 X3]]. destruct X2,X3. exists n0. repeat split; auto.
Qed.

Lemma ord_eq_split : forall alpha1 beta1 alpha2 beta2 n1 n2, alpha1 = alpha2 -> beta1 = beta2 -> n1 = n2 ->  (cons alpha1 n1 beta1) = (cons alpha2 n2 beta2).
Proof.
intros. apply ord_eqb_eq. simpl. rewrite H,H0,H1. repeat rewrite ord_eqb_refl. rewrite eq_nat_refl. auto.
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

Lemma ord_lt_ne : forall beta alpha, ord_ltb alpha beta = true -> ord_eqb beta alpha = false.
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
        { simpl. rewrite ord_eqb_symm in H3. rewrite H3. case (eq_nat n n0) eqn:H5.
           { apply nat_eq_decid in H5. destruct H5. rewrite lt_nat_irrefl in H4. inversion H4. }
           { auto. } }
        { case (lt_nat n n0) eqn:H5.
          { inversion H1. }
          { simpl. rewrite ord_eqb_symm in H3. rewrite H3. case (eq_nat n n0) eqn:H6.
            { apply (IHbeta2 _ H1). }
            { auto. } } } }
      { inversion H1. }
Qed.

Lemma ord_add_assoc : forall alpha beta gamma, ord_add (ord_add alpha beta) gamma = ord_add alpha (ord_add beta gamma).
Proof.
intros alpha. induction alpha. intros. rewrite ord_zero_add. rewrite ord_zero_add. auto.
intros. unfold ord_add. fold ord_add. destruct beta.
- rewrite ord_zero_add. destruct gamma. rewrite ord_add_zero. auto. unfold ord_add. fold ord_add. auto.
- destruct (ord_semiconnex_bool alpha1 beta1) as [X | [X | X]].
  + rewrite X. unfold ord_add. fold ord_add. destruct gamma. rewrite X. auto. destruct (ord_semiconnex_bool beta1 gamma1) as [X1 | [X1 | X1]].
    * rewrite X1. rewrite (ord_ltb_trans _ _ _ X X1). auto.
    * rewrite (ltb_asymm _ _ X1). rewrite (ord_lt_ne _ _ X1). rewrite X. auto.
    * apply ord_eqb_eq in X1. destruct X1. rewrite ord_ltb_irrefl. rewrite ord_eqb_refl. rewrite X. auto.
  + rewrite (ltb_asymm _ _ X). rewrite (ord_lt_ne _ _ X). unfold ord_add. fold ord_add. destruct gamma. rewrite (ltb_asymm _ _ X). rewrite (ord_lt_ne _ _ X). auto. destruct (ord_semiconnex_bool beta1 gamma1) as [X1 | [X1 | X1]].
    * rewrite X1. destruct (ord_semiconnex_bool alpha1 gamma1) as [X2 | [X2 | X2]].
      { rewrite X2. auto. }
      { rewrite (ltb_asymm _ _ X2). rewrite (ord_lt_ne _ _ X2). rewrite IHalpha2. unfold ord_add. fold ord_add. rewrite X1. auto. }
      { apply ord_eqb_eq in X2. destruct X2. rewrite ord_ltb_irrefl. rewrite ord_eqb_refl. auto. }
    * rewrite (ltb_asymm _ _ X1). rewrite (ord_lt_ne _ _ X1). rewrite (ltb_asymm _ _ (ord_ltb_trans _ _ _ X1 X)). rewrite (ord_lt_ne _ _ (ord_ltb_trans _ _ _ X1 X)). rewrite (ltb_asymm _ _ X). rewrite (ord_lt_ne _ _ X). rewrite IHalpha2. unfold ord_add. fold ord_add. rewrite (ltb_asymm _ _ X1). rewrite (ord_lt_ne _ _ X1). auto.
    * apply ord_eqb_eq in X1. destruct X1. rewrite (ltb_asymm _ _ X). rewrite (ord_lt_ne _ _ X). rewrite ord_ltb_irrefl. rewrite ord_eqb_refl. rewrite (ltb_asymm _ _ X). rewrite (ord_lt_ne _ _ X). rewrite IHalpha2. unfold ord_add. fold ord_add. rewrite ord_ltb_irrefl. rewrite ord_eqb_refl. auto.
  + apply ord_eqb_eq in X. destruct X. rewrite ord_ltb_irrefl. rewrite ord_eqb_refl. unfold ord_add. fold ord_add. destruct gamma. rewrite ord_ltb_irrefl. rewrite ord_eqb_refl. auto. destruct (ord_semiconnex_bool alpha1 gamma1) as [X | [X | X]].
    * rewrite X. rewrite X. auto.
    * rewrite (ltb_asymm _ _ X). rewrite (ord_lt_ne _ _ X). rewrite ord_ltb_irrefl. rewrite ord_eqb_refl. auto.
    * apply ord_eqb_eq in X. destruct X. repeat rewrite ord_ltb_irrefl. repeat rewrite ord_eqb_refl. rewrite ord_ltb_irrefl. apply ord_eq_split; auto. lia.
Qed.

Lemma ord_mult_assoc : forall alpha beta gamma, ord_mult (ord_mult alpha beta) gamma = ord_mult alpha (ord_mult beta gamma).
Proof.
intros. induction gamma.
- destruct beta; destruct alpha; auto. destruct beta1; auto.
- unfold ord_mult. fold ord_mult. destruct beta.
  + rewrite ord_mult_zero_right. auto.
  + destruct alpha.
    * rewrite ord_mult_zero_left. rewrite ord_mult_zero_left. auto.
    * destruct gamma1.
      --  unfold ord_mult. fold ord_mult. destruct beta1.
          ++  apply ord_eq_split; auto. simpl. repeat rewrite minus_n_0. lia.
          ++  auto.
      --  unfold ord_mult. fold ord_mult. destruct beta1.
          ++  rewrite ord_zero_add. apply ord_eq_split; auto.
          ++  case (ord_add (cons beta1_1 n3 beta1_2) (cons gamma1_1 n2 gamma1_2)) eqn:Y.
              **  simpl in Y. destruct (ord_semiconnex_bool beta1_1 gamma1_1) as [X | [X | X]]. rewrite X in Y. inversion Y. rewrite (ltb_asymm _ _ X) in Y. rewrite (ord_lt_ne _ _ X) in Y. inversion Y.
                  apply ord_eqb_eq in X. destruct X. rewrite ord_ltb_irrefl in Y. rewrite ord_eqb_refl in Y. inversion Y.
              **  destruct Y. rewrite ord_add_assoc. apply ord_eq_split; auto.
Qed.

Lemma ord_2_exp_succ_mult : forall alpha, nf alpha -> ord_2_exp (ord_succ alpha) = ord_mult (ord_2_exp alpha) (nat_ord 2).
Proof.
apply (transfinite_induction (fun alpha => ord_2_exp (ord_succ alpha) = ord_mult (ord_2_exp alpha) (nat_ord 2))). intros. destruct x as [| beta1 n beta2]. auto. destruct beta1.
- unfold ord_succ. unfold ord_2_exp. unfold nat_ord. case (2 ^ (S (S n))) eqn:Y. pose (nat_exp_monot_lem n). simpl in Y. lia. case (2 ^ (S n)) eqn:Y1. pose (nat_exp_monot_lem n). simpl in Y1. lia. simpl. apply ord_eq_split; auto.
  apply eq_succ. destruct Y. simpl. rewrite two_mul. rewrite plus_n_Sm. rewrite <- (plus_comm (S n1)). rewrite plus_n_Sm. destruct Y1. simpl. lia.
- unfold ord_succ. fold ord_succ. unfold ord_2_exp. fold ord_2_exp. destruct beta1_1.
  + destruct n0.
    * destruct beta2.
      -- auto.
      -- rewrite H0. rewrite ord_mult_assoc. auto. apply (nf_hered_third _ _ _ H). inversion H. apply head_lt. auto.
    * rewrite H0. rewrite ord_mult_assoc. auto. apply (nf_hered_third _ _ _ H). inversion H. apply zero_lt. apply head_lt. auto.
  + rewrite H0. rewrite ord_mult_assoc. auto. apply (nf_hered_third _ _ _ H). inversion H. apply zero_lt. apply head_lt. auto.
Qed.

Lemma exp_2_simpl : forall n m p r q, 2^(S n) = S q -> 2^(S m) = S r -> 2^(S (n + m + 1)) = S p -> S p = q * S r + S r.
Proof.
intros. rewrite succ_distrib. destruct H,H0,H1. rewrite plus_n_1. simpl. repeat rewrite plus_n_0. induction m.
- induction n.
  + simpl. auto.
  + repeat rewrite plus_n_0 in *. simpl in *. lia.
- rewrite <- plus_n_Sm. simpl in *. lia.
Qed.

Lemma ord_nf_cons_add : forall alpha n beta, nf (cons alpha n beta) -> cons alpha n beta = ord_add (cons alpha n Zero) beta.
Proof.
intros. inversion H. auto. simpl. rewrite (ltb_asymm _ _ (ord_lt_ltb _ _ H3)). rewrite (ord_lt_ne _ _ (ord_lt_ltb _ _ H3)). auto.
Qed.

Lemma ord_2_exp_eval : forall alpha, nf alpha -> ord_2_exp (ord_mult (cons (cons Zero 0 Zero) 0 Zero) alpha) = cons alpha 0 Zero.
Proof.
apply transfinite_induction. intros. destruct x. auto. destruct x1.
- simpl. rewrite plus_n_0. rewrite minus_n_0. inversion H. auto. inversion H4.
- destruct x1_1.
  + simpl. rewrite plus_n_1. simpl. rewrite H0. destruct x2.
    * inversion H. inversion H2. auto. inversion H7.
    * inversion H. inversion H7. symmetry in H1,H9. destruct H1,H2,H3,H5,H6,H9,H11,H12. destruct a'.
      --  auto.
      --  destruct a'1.
          ++  inversion H4. inversion H2. simpl. rewrite (lt_nat_decid_conv _ _ H2). rewrite (lt_nat_asymm _ _ (lt_nat_decid_conv _ _ H2)). case_eq (eq_nat n3 n).
              **  intros. apply nat_eq_decid in H11. destruct H11. apply lt_nat_decid_conv in H2. rewrite lt_nat_irrefl in H2. inversion H2.
              **  intros. auto.
              **  inversion H2.
          ++ inversion H4. inversion H2.
      --  inversion H12.
    * apply (nf_hered_third _ _ _ H).
    * inversion H. apply zero_lt. apply head_lt. auto.
  + simpl. rewrite H0.
    * destruct x2.
      --  auto.
      --  rewrite nf_mult_eval. rewrite ord_mult_zero_right. rewrite <- ord_nf_cons_add; auto. apply zero_lt.
    * apply (nf_hered_third _ _ _ H).
    * inversion H. apply zero_lt. apply head_lt. auto.
Qed.

Lemma ord_add_one_succ : forall alpha, nf alpha -> ord_add alpha (cons Zero 0 Zero) = ord_succ alpha.
Proof.
intros. induction alpha.
- auto.
- destruct alpha1.
  + simpl. rewrite plus_n_1. rewrite plus_n_0. inversion H. auto. inversion H3.
  + simpl. rewrite (IHalpha2 (nf_hered_third _ _ _ H)). auto.
Qed.

Lemma ord_add_succ_nat_succ_add : forall alpha n, nf alpha -> ord_add alpha (nat_ord (S n)) = ord_add (ord_succ alpha) (nat_ord n).
Proof.
intros. induction alpha. destruct n. auto. simpl. rewrite plus_n_1. auto. simpl. unfold ord_add. fold ord_add. destruct alpha1.
- rewrite ord_ltb_irrefl. rewrite ord_eqb_refl. inversion H; inversion H3. destruct n. rewrite plus_n_0. rewrite plus_n_1. auto. simpl. rewrite plus_n_1. rewrite plus_n_1. rewrite <- plus_n_Sm. auto.
- rewrite (ltb_asymm _ _ (ord_lt_ltb _ _ (zero_lt _ _ _))). rewrite (ord_lt_ne _ _ (ord_lt_ltb _ _ (zero_lt _ _ _))). simpl in IHalpha2. rewrite IHalpha2. unfold ord_add. fold ord_add. destruct n.
  + simpl. rewrite ord_add_zero. auto.
  + simpl. auto.
  + inversion H. apply zero_nf. auto.
Qed.

Lemma is_succ_mult_rule : forall alpha beta, nf alpha -> nf beta -> is_succ (ord_mult alpha beta) = is_succ alpha && is_succ beta.
Proof.
intros. induction beta. rewrite ord_mult_zero_right. case (is_succ alpha); auto. destruct alpha. auto. destruct beta1.
- destruct alpha2.
  + destruct alpha1.
    * inversion H0. auto. inversion H4.
    * auto.
  +  simpl. inversion H0; inversion H4. destruct alpha2_2.
    * destruct alpha2_1. auto. auto.
    * case (is_succ (cons alpha2_2_1 n3 alpha2_2_2)); auto.
- rewrite nf_mult_eval. destruct alpha1.
  + unfold ord_add. unfold is_succ. fold is_succ. rewrite IHbeta2. destruct beta2.
    * rewrite ord_mult_zero_right. destruct alpha2. auto. case (is_succ (cons alpha2_1 n2 alpha2_2)); auto.
    * unfold ord_mult. fold ord_mult. destruct beta2_1.
      --  inversion H. pose (nf_hered_third _ _ _ H0). inversion n4. auto. inversion H8. inversion H4.
      --  destruct alpha2; auto.
    * apply (nf_hered_third _ _ _ H0).
  + unfold is_succ. fold is_succ. rewrite IHbeta2. destruct beta2.
    * simpl. case (ord_ltb alpha1_1 beta1_1).
      --  destruct alpha2. auto. case (is_succ (cons alpha2_1 n3 alpha2_2)); auto.
      --  case (ord_eqb alpha1_1 beta1_1); destruct alpha2; try case (is_succ (cons alpha2_1 n3 alpha2_2)); auto.
    * unfold ord_mult. fold ord_mult. destruct beta2_1.
    --  inversion H. pose (nf_hered_third _ _ _ H0). inversion n5. auto. inversion H8. simpl. destruct b; destruct a'; auto.
    --  destruct alpha2; auto.
    * apply (nf_hered_third _ _ _ H0).
  + apply zero_lt.
Qed.

Lemma exp_2_not_succ : forall alpha, nf alpha -> ord_ltb alpha (cons (cons Zero 0 Zero) 0 Zero) = false -> is_succ (ord_2_exp alpha) = false.
Proof.
intros. induction alpha. inversion H0. destruct alpha1. inversion H0. destruct alpha1_1.
- inversion H0. destruct n0.
  + rewrite lt_nat_irrefl in *. rewrite eq_nat_refl in *. destruct alpha1_2.
    * rewrite ord_ltb_irrefl in *. rewrite ord_eqb_refl in *. destruct n.
      --  rewrite lt_nat_irrefl in *. destruct alpha2. auto. simpl. rewrite ord_mult_omega_not_succ. auto. apply nf_2_exp. apply (nf_hered_third _ _ _ H).
      --  simpl in *. apply is_succ_mult_rule. apply single_nf. apply single_nf. apply zero_nf. apply nf_2_exp. apply (nf_hered_third _ _ _ H).
    * simpl in *. apply is_succ_mult_rule. apply single_nf. apply single_nf. apply zero_nf. apply nf_2_exp. apply (nf_hered_third _ _ _ H).
  + simpl in *. apply is_succ_mult_rule. apply single_nf. apply single_nf. apply single_nf. apply zero_nf. apply nf_2_exp. apply (nf_hered_third _ _ _ H).
- simpl in *. apply is_succ_mult_rule. apply single_nf. apply single_nf. apply (nf_hered_first _ _ _ H). apply nf_2_exp. apply (nf_hered_third _ _ _ H). 
Qed.

Lemma ord_not_succ_is_mul : forall alpha, nf alpha -> is_succ alpha = false -> { beta : ord & alpha = ord_mult (cons (cons Zero 0 Zero) 0 Zero) beta /\ nf beta}.
Proof.
intros. induction alpha. exists Zero. auto. unfold is_succ in H0. fold is_succ in H0. destruct alpha2.
- destruct alpha1. inversion H0. destruct alpha1_1.
  + exists (cons (ord_pred (cons Zero n0 alpha1_2)) n Zero). inversion H. inversion H2; inversion H7. destruct n0.
    * simpl. rewrite plus_n_0. rewrite minus_n_0. split. auto. apply single_nf. apply zero_nf.
    * rewrite nf_mult_eval. rewrite ord_mult_zero_right. simpl. rewrite plus_n_1. split. auto. apply single_nf. apply single_nf. auto. simpl. apply zero_lt.
  + exists (cons (cons (cons alpha1_1_1 n1 alpha1_1_2) n0 alpha1_2) n Zero). rewrite nf_mult_eval. auto. apply zero_lt.
- destruct (IHalpha2 (nf_hered_third _ _ _ H) H0) as [beta [HB1 HB2]]. rewrite HB1. destruct alpha1.
  + exists Zero. inversion H. inversion H4.
  + destruct alpha1_1.
    * destruct n1.
      --  exists Zero. inversion H. inversion H7; inversion H12. destruct H13. inversion H4; inversion H15. destruct H13. inversion H8. destruct H20. simpl in H0. inversion H0. inversion H20.
      --  exists (cons (ord_pred (cons Zero (S n1) alpha1_2)) n beta). inversion H. inversion H7;inversion H12. rewrite nf_mult_eval. simpl. rewrite plus_n_1. split. auto.
          { destruct beta. inversion HB1. apply cons_nf; auto. destruct beta1. apply zero_lt. destruct beta1_1. simpl in HB1. rewrite plus_n_1 in HB1. inversion HB1.
            symmetry in H1,H9,H15,H17. destruct H1,H2,H3,H5,H6,H9,H12,H13,H15,H16,H17. inversion H4. inversion H2. apply coeff_lt. lia. inversion H2.
            simpl in HB1. inversion HB1. symmetry in H1,H9,H15,H17. destruct H1,H2,H3,H5,H6,H9,H12,H13,H15,H16,H17. inversion H4. inversion H2. apply single_nf. auto. } simpl. apply zero_lt.
    * exists (cons (cons (cons alpha1_1_1 n2 alpha1_1_2) n1 alpha1_2) n beta). rewrite nf_mult_eval. split. auto.
      { destruct beta. inversion HB1. apply cons_nf; auto. destruct beta1. apply zero_lt. destruct beta1_1. apply head_lt. apply zero_lt. simpl in HB1. inversion HB1.
        symmetry in H2,H4. destruct H2,H3,H4. inversion H. auto. apply (nf_hered_first _ _ _ H). }
       apply zero_lt.
Qed.

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

Lemma ord_nf_pred : forall alpha, nf alpha -> nf (ord_pred alpha).
intros. induction alpha. auto. unfold ord_pred. fold ord_pred. destruct alpha2. destruct alpha1. destruct n. apply zero_nf. apply single_nf. apply zero_nf. auto. pose (IHalpha2 (nf_hered_third _ _ _ H)).
inversion H. destruct alpha1. inversion H3. case (ord_pred (cons alpha2_1 n0 alpha2_2)) eqn:X. apply single_nf. auto. apply cons_nf; auto. unfold ord_pred in X. fold ord_pred in X. destruct alpha2_2.
- destruct alpha2_1.
  + destruct n0; inversion X. apply zero_lt.
  + inversion X. auto.
- inversion X. destruct H9. auto.
Qed.

Lemma ord_pred_lt : forall alpha, nf alpha -> is_succ alpha = true -> ord_lt (ord_pred alpha) alpha.
Proof.
intros. rewrite <- ord_succ_pred_if_succ; auto. apply ord_succ_monot.
Qed.

Definition exp_monot (alpha : ord ) : Prop := forall beta, nf beta -> ord_lt beta alpha -> ord_lt (ord_2_exp beta) (ord_2_exp alpha).

Definition exp_monot_2 (alpha beta : ord ) : Prop := ord_lt beta alpha -> ord_lt (ord_2_exp beta) (ord_2_exp alpha).

Lemma mult_right_incr_conv :  forall beta gamma alpha : ord, Zero < alpha -> nf beta -> ord_mult alpha beta < ord_mult alpha gamma -> beta < gamma.
Proof.
intros. destruct (ord_semiconnex beta gamma) as [X | [X | X]]. auto. pose (mult_right_incr _ _ _ X H H0). apply lt_asymm in o. contradiction. destruct X. apply lt_irrefl in H1. inversion H1.
Qed.

Lemma ord_2_exp_monot : forall alpha, nf alpha -> forall beta, nf beta -> beta < alpha -> ord_2_exp beta < ord_2_exp alpha.
Proof.
apply (transfinite_induction exp_monot). unfold exp_monot. intros. destruct x. inversion H2. case (is_succ (cons x1 n x2)) eqn:X.
- rewrite <- (ord_succ_pred_if_succ _ H X) in H2. destruct (ord_lt_succ_cases _ _ H2 H1 (ord_nf_pred _ H)).
  + rewrite <- (ord_succ_pred_if_succ _ H X). destruct H3. rewrite ord_2_exp_succ_mult. apply ord_mult_monot. apply coeff_lt. lia. apply single_nf. apply zero_nf. apply exp_geq_1. auto. auto.
  + rewrite <- (ord_succ_pred_if_succ _ H X). apply (lt_trans _ (ord_2_exp (ord_pred (cons x1 n x2)))). apply H0; auto. apply ord_nf_pred. auto. apply ord_pred_lt; auto.
    rewrite ord_2_exp_succ_mult. apply ord_mult_monot. apply coeff_lt. lia. apply single_nf. apply zero_nf. apply exp_geq_1. apply ord_nf_pred. auto. apply ord_nf_pred. auto. 
- apply (transfinite_induction (exp_monot_2 (cons x1 n x2))); auto. unfold exp_monot_2. intros. rename x into gamma. destruct gamma.
  + destruct x1. inversion H. destruct H9. inversion X. inversion H9. destruct x1_1. 
    * destruct n0. simpl. destruct x2. apply head_lt. apply zero_lt. apply ord_mult_exp_monot. apply (nf_hered_third _ _ _ H). apply head_lt. apply zero_lt. apply ord_mult_exp_monot. apply (nf_hered_third _ _ _ H). apply head_lt. apply zero_lt.
    * destruct x2. simpl. apply head_lt. apply zero_lt. apply ord_mult_exp_monot.  apply (nf_hered_third _ _ _ H). apply head_lt. apply zero_lt.
  + case (is_succ (cons gamma1 n0 gamma2)) eqn:X1.
    * destruct (ord_not_succ_is_mul _ H X) as [alpha [Ha1 Ha2]]. rewrite Ha1. rewrite ord_2_exp_eval; auto. rewrite <- (ord_succ_pred_if_succ _ H3 X1). rewrite ord_2_exp_succ_mult.
      pose (H4 _ (ord_nf_pred _ H3) (ord_pred_lt _ H3 X1) (lt_trans _ _ _ (ord_pred_lt _ H3 X1) H5)). rewrite Ha1 in o. rewrite ord_2_exp_eval in o; auto.
      case (ord_2_exp (ord_pred (cons gamma1 n0 gamma2))) eqn:Y. apply zero_lt. inversion o. simpl. apply head_lt. auto. inversion H7. inversion H7. apply ord_nf_pred. auto.
    * destruct (ord_not_succ_is_mul _ H X) as [alpha [Ha1 Ha2]]. rewrite Ha1. rewrite ord_2_exp_eval; auto. destruct (ord_not_succ_is_mul _ H3 X1) as [delta [Hd1 Hd2]]. rewrite Hd1. rewrite ord_2_exp_eval; auto.
      rewrite Ha1 in H5. rewrite Hd1 in H5. apply mult_right_incr_conv in H5; auto. apply head_lt. auto. apply zero_lt.
Qed.

Lemma ord_add_ne : forall alpha beta gamma n, ord_eqb alpha (ord_add alpha (cons beta n gamma)) = false.
Proof.
intros.
pose proof (add_right_incr alpha _ _ (zero_lt beta n gamma)).
rewrite ord_add_zero in H.
apply ord_lt_ltb in H.
apply ord_ltb_neb.
auto.
Qed.

Fixpoint w_tower (n : nat) : ord :=
match n with
| 0 => cons Zero 0 Zero
| S n' => cons (w_tower n') 0 Zero
end.

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

Lemma w_tower_succ3 : forall n, ord_lt (ord_succ (ord_succ (ord_succ (w_tower n)))) (w_tower (S n)).
Proof.
intros.
destruct n.
- simpl. apply ord_ltb_lt. auto.
- simpl. destruct (w_tower n).
  + apply ord_ltb_lt. auto.
  + simpl. apply head_lt. apply ord_lt_self.
Qed.

Lemma w_tower_lt : forall n m,  (m < n)%nat -> ord_lt (w_tower m) (w_tower n).
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

Lemma ord_succ_not_exp_fp : forall alpha, nf (ord_succ alpha) -> ord_lt (ord_succ alpha) (ord_2_exp (ord_succ alpha)).
Proof.
intros. destruct (ord_2_exp_fp (ord_succ alpha)); auto. destruct alpha. inversion H0. destruct alpha1; inversion H0. destruct alpha2. inversion H6. destruct alpha2_1; inversion H6.
Qed.

Lemma ord_succ_non_Zero : forall alpha, ord_eqb (ord_succ alpha) Zero = false.
Proof.
intros. induction alpha. auto. simpl. destruct alpha1. auto. auto.
Qed.

Lemma ord_max_0 : forall alpha beta, Zero = ord_max alpha beta -> Zero = alpha /\ Zero = beta.
intros. induction alpha. induction beta. auto. inversion H. destruct beta. inversion H. inversion H. destruct (ord_semiconnex_bool alpha1 beta1) as [X | [X | X]].
- rewrite X in H1. inversion H1.
- rewrite (ltb_asymm _ _ X) in H1. rewrite (ord_lt_ne _ _ X) in H1. inversion H1.
- apply ord_eqb_eq in X. destruct X. rewrite ord_ltb_irrefl in H1. rewrite ord_eqb_refl in H1. destruct (nat_semiconnex_bool n n0) as [X1 | [X1 | X1]].
  + rewrite X1 in H1. inversion H1.
  + rewrite (lt_nat_asymm _ _ X1) in H1. rewrite X1 in H1. inversion H1.
  + apply nat_eq_decid in X1. destruct X1. rewrite lt_nat_irrefl in H1. case (ord_ltb alpha2 beta2) eqn:X; inversion H1.
Qed.


Lemma ord_max_split : forall alpha beta gamma, ord_lt (ord_max alpha beta) gamma -> ord_lt alpha gamma /\ ord_lt beta gamma.
intros. destruct (ord_semiconnex_bool alpha beta) as [X | [X | X]].
- pose (ord_max_lem1 _ _ X). split. apply (lt_trans _ beta). apply ord_ltb_lt. auto. rewrite e in H. auto. rewrite e in H. auto.
- pose (ord_max_lem2 _ _ (ltb_asymm _ _ X)). split. rewrite e in H. auto. apply (lt_trans _ alpha). apply ord_ltb_lt. auto. rewrite e in H. auto.
- apply ord_eqb_eq in X. destruct X. rewrite (ord_max_lem2 _ _ (ord_ltb_irrefl _)) in H. auto.
Qed.

Lemma one_nf : nf (cons Zero 0 Zero).
Proof.
assert (cons Zero 0 Zero = nat_ord 1). auto.
rewrite H.
apply nf_nat.
Qed.

Lemma ord_lt_one : forall alpha, ord_lt alpha (nat_ord 1) -> alpha = Zero.
Proof.
intros. induction alpha. auto.
inversion H; inversion H1.
Qed.

Lemma ord_succ_one : forall alpha, ord_succ alpha = cons Zero 0 Zero -> Zero = alpha.
Proof.
intros. unfold ord_succ in H. destruct alpha. auto. fold ord_succ in H. destruct alpha1. inversion H. inversion H.
Qed.

Lemma nf_cons_zero_is_zero : forall n beta, nf (cons Zero n beta) -> Zero = beta.
Proof.
intros. inversion H. auto. inversion H3.
Qed.

Lemma is_succ_scalar' : forall alpha beta n m, is_succ (cons alpha n beta) = is_succ (cons alpha m beta). induction alpha; intros; destruct beta; auto. Qed.

Lemma is_succ_scalar : forall alpha beta n m, is_succ (cons alpha n beta) = true -> is_succ (cons alpha m beta) = true. intros. rewrite  (is_succ_scalar' _ _ _ n). auto. Qed.

Lemma not_is_succ_scalar : forall alpha beta n m, is_succ (cons alpha n beta) = false -> is_succ (cons alpha m beta) = false. intros. rewrite  (is_succ_scalar' _ _ _ n). auto. Qed.

Lemma ord_gt_one_succ_lt_dub : forall alpha, nf alpha -> ord_lt (cons Zero 0 Zero) alpha -> ord_lt (ord_succ alpha) (ord_mult alpha (nat_ord 2)).
Proof.
intros. induction alpha. inversion H0. destruct alpha1. inversion H. destruct H4. destruct n. inversion H0; inversion H5. apply coeff_lt. lia. inversion H4. simpl. apply coeff_lt. lia.
Qed.

Lemma ord_gt_zero_exp_gt_one : forall alpha, nf alpha -> ord_lt Zero alpha -> ord_lt (cons Zero 0 Zero) (ord_2_exp alpha).
Proof.
intros. induction alpha. inversion H0. destruct alpha1. inversion H. destruct H4. destruct n. apply coeff_lt. lia.
unfold ord_2_exp. case (2^(S(S n))) eqn:X. pose (exp_succ (S(S n))). lia. destruct n1. pose (nat_2_exp_succ_not_one (S n)). lia. apply coeff_lt. lia. inversion H4. destruct alpha1_1.
- inversion H.
  + inversion H2. symmetry in H1,H5. destruct H1,H3,H4,H5,H7,H8. destruct n2; apply head_lt; apply zero_lt. inversion H8. 
  + inversion H5. symmetry in H1,H7. destruct H1,H2,H3,H7,H9,H10. destruct n2; apply ord_mult_exp_monot; auto; apply head_lt; apply zero_lt. inversion H10.
- simpl. apply ord_mult_exp_monot. apply (nf_hered_third _ _ _ H). apply head_lt. apply zero_lt.
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

Lemma ord_succ_lt_exp_succ : forall alpha, nf alpha -> ord_lt Zero alpha -> ord_lt (ord_succ (ord_2_exp alpha)) (ord_2_exp (ord_succ alpha)).
Proof.
intros. rewrite ord_2_exp_succ_mult; auto. apply ord_gt_one_succ_lt_dub. apply nf_2_exp. auto. apply ord_gt_zero_exp_gt_one; auto. 
Qed.

Lemma ord_max_exp_equiv : forall alpha beta, nf alpha -> nf beta -> (ord_max (ord_2_exp alpha) (ord_2_exp beta)) = (ord_2_exp (ord_max alpha beta)).
Proof.
intros. destruct (ord_semiconnex_bool alpha beta) as [X | [X | X]].
- pose (ord_lt_ltb _ _ (ord_2_exp_monot _ H0 _ H (ord_ltb_lt _ _ X))). rewrite ord_max_lem1; auto. rewrite ord_max_lem1; auto.
- pose (ltb_asymm _ _ (ord_lt_ltb _ _ (ord_2_exp_monot _ H _ H0 (ord_ltb_lt _ _ X)))). pose (ltb_asymm _ _ X). rewrite ord_max_lem2; auto. rewrite ord_max_lem2; auto.
- apply ord_eqb_eq in X. destruct X. rewrite ord_max_lem2; auto. rewrite ord_max_lem2; auto. apply ord_ltb_irrefl. apply ord_ltb_irrefl.
Qed.

Lemma succ_gt_one_gt_zero : forall alpha, ord_lt (cons Zero 0 Zero) (ord_succ alpha) -> ord_lt Zero alpha. intros. destruct alpha. inversion H; inversion H1. apply zero_lt. Qed.

Lemma ord_max_exp_both : forall alpha beta, nf alpha -> nf beta -> ord_lt (cons Zero 0 Zero) (ord_succ (ord_max alpha beta)) -> ord_lt (ord_succ (ord_max (ord_2_exp alpha) (ord_2_exp beta))) (ord_2_exp (ord_succ (ord_max alpha beta))).
intros. rewrite ord_max_exp_equiv; auto. apply ord_succ_lt_exp_succ. apply ord_max_nf; auto. apply succ_gt_one_gt_zero. auto.
Qed.



Lemma ord_max_exp_r : forall alpha beta, nf alpha -> nf beta -> ord_lt (cons Zero 0 Zero) (ord_succ (ord_max alpha beta)) -> ord_lt (ord_succ (ord_max alpha (ord_2_exp beta))) (ord_2_exp (ord_succ (ord_max alpha beta))).
intros. destruct (ord_semiconnex_bool alpha (ord_2_exp beta)) as [X | [X | X]].
- rewrite ord_max_lem1; auto. case (ord_eqb beta (ord_max alpha beta)) eqn:X1.
  + apply ord_eqb_eq in X1. destruct X1. apply ord_succ_lt_exp_succ. auto. apply succ_gt_one_gt_zero. auto.
  + destruct beta.
    * simpl in X. apply ord_ltb_lt in X. inversion X; inversion H4. destruct H2. inversion X1.
    * pose (ord_max_lt2 _ _ X1). apply (lt_trans _ (ord_2_exp (ord_succ (cons beta1 n beta2)))). apply ord_succ_lt_exp_succ. auto. apply zero_lt. apply ord_2_exp_monot. apply ord_succ_nf. apply ord_max_nf; auto. apply ord_succ_nf. auto. apply ord_lt_succ. auto.
- inversion X. apply ltb_asymm in H3. rewrite ord_max_lem2; auto. assert (ord_ltb alpha beta = false). destruct (ord_2_exp_fp beta H0). apply ltb_asymm. apply ord_lt_ltb in H2. apply (ord_ltb_trans _ _ _ H2 X). symmetry in H2. destruct H2. unfold nat_ord in X. unfold ord_2_exp in X. rewrite <- one_right_mult_ident in X. apply ltb_asymm. auto. rewrite ord_max_lem2; auto. destruct (ord_2_exp_fp alpha H).
  + apply (lt_trans _ (ord_succ (ord_2_exp alpha))). apply ord_lt_succ. auto. apply ord_succ_lt_exp_succ. auto. destruct alpha. destruct beta. inversion X. inversion H2. apply zero_lt.
  + symmetry in H4. destruct H4. apply coeff_lt. lia.
- apply ord_eqb_eq in X. symmetry in X. destruct X. rewrite ord_max_lem2; auto. rewrite ord_max_lem2; auto. apply ord_succ_not_exp_fp. apply ord_succ_nf. auto. destruct (ord_2_exp_fp beta H0). apply ord_lt_ltb in H2. apply ltb_asymm in H2. auto. symmetry in H2. destruct H2. auto. apply ord_ltb_irrefl.
Qed.

Lemma ord_max_exp_l : forall alpha beta, nf alpha -> nf beta -> ord_lt (cons Zero 0 Zero) (ord_succ (ord_max alpha beta)) -> ord_lt (ord_succ (ord_max (ord_2_exp alpha) beta)) (ord_2_exp (ord_succ (ord_max alpha beta))).
intros. rewrite (ord_max_symm alpha). rewrite ord_max_symm. apply ord_max_exp_r; auto. rewrite ord_max_symm. auto.
Qed.

Definition exp_omega_le (alpha : ord) : Type := ord_lt (cons Zero 0 Zero) alpha -> ord_lt (cons (ord_2_exp alpha) 0 Zero) (ord_2_exp (cons alpha 0 Zero)) \/ cons (ord_2_exp alpha) 0 Zero = ord_2_exp (cons alpha 0 Zero).

Definition exp_omega_lt (alpha : ord) : Type := ord_lt (cons Zero 0 Zero) alpha -> ord_lt (cons (ord_2_exp alpha) 0 Zero) (ord_2_exp (cons alpha 0 Zero)).

Lemma ord_2_exp_omega: forall alpha, nf alpha -> ord_lt (cons (cons Zero 0 Zero) 0 Zero) alpha -> (ord_2_exp (cons alpha 0 Zero)) = cons (cons alpha 0 Zero) 0 Zero.
Proof.
intros. destruct alpha. inversion H0. destruct alpha1. inversion H0. inversion H2. auto.
Qed.

Lemma add_left_non_decr : forall alpha beta, ord_ltb (ord_add beta alpha) alpha = false.
Proof.
intros. destruct beta. rewrite ord_zero_add. apply ord_ltb_irrefl. destruct alpha. auto. simpl. destruct (ord_semiconnex_bool beta1 alpha1) as [X | [X | X]].
rewrite X. apply ord_ltb_irrefl. rewrite (ltb_asymm _ _ X). rewrite ord_eqb_symm. rewrite (ord_ltb_neb _ _ X). apply ltb_asymm. apply ord_lt_ltb. apply head_lt. apply ord_ltb_lt. auto.
apply ord_eqb_eq in X. destruct X. rewrite ord_ltb_irrefl. rewrite ord_eqb_refl. apply ltb_asymm. apply ord_lt_ltb. apply coeff_lt. lia.
Qed.

Lemma add_left_lt_false : forall alpha beta gamma, ord_ltb alpha beta = false -> ord_ltb (ord_add alpha gamma) (ord_add beta gamma) = false.
Proof.
intros alpha. induction alpha.
- intros. destruct beta. apply ord_ltb_irrefl. inversion H.
- intros. destruct gamma. rewrite ord_add_zero. rewrite ord_add_zero. auto. destruct beta.
  + simpl. destruct (ord_semiconnex_bool alpha1 gamma1) as [X | [X | X]].
    * rewrite X. apply ord_ltb_irrefl.
    * rewrite (ltb_asymm _ _ X). rewrite ord_eqb_symm. rewrite (ord_ltb_neb _ _ X). apply ltb_asymm. apply ord_lt_ltb. apply head_lt. apply ord_ltb_lt. auto.
    * apply ord_eqb_eq in X. destruct X. rewrite ord_ltb_irrefl. rewrite ord_eqb_refl. apply ltb_asymm. apply ord_lt_ltb. apply coeff_lt. lia.
  + simpl. inversion H. rewrite H1. destruct (ord_semiconnex_bool alpha1 beta1) as [Y | [Y | Y]].
    * rewrite Y in H1. inversion H1.
    * destruct (ord_semiconnex_bool alpha1 gamma1) as [X | [X | X]].
      --  rewrite X. rewrite (ord_ltb_trans _ _ _ Y X). apply ord_ltb_irrefl.
      --  rewrite (ltb_asymm _ _ X). rewrite ord_eqb_symm. rewrite (ord_ltb_neb _ _ X). destruct (ord_semiconnex_bool beta1 gamma1) as [X1 | [X1 | X1]].
          ++  rewrite X1. simpl. rewrite (ltb_asymm _ _ X). rewrite ord_eqb_symm. rewrite (ord_ltb_neb _ _ X). auto.
          ++  rewrite (ltb_asymm _ _ X1). rewrite ord_eqb_symm. rewrite (ord_ltb_neb _ _ X1). simpl. rewrite (ltb_asymm _ _ Y). rewrite ord_eqb_symm. rewrite (ord_ltb_neb _ _ Y). auto.
          ++  apply ord_eqb_eq in X1. destruct X1. rewrite ord_ltb_irrefl. rewrite ord_eqb_refl. simpl. rewrite (ltb_asymm _ _ Y). rewrite ord_eqb_symm. rewrite (ord_ltb_neb _ _ Y). auto.
      --  apply ord_eqb_eq in X. destruct X. rewrite ord_ltb_irrefl. rewrite ord_eqb_refl. rewrite Y. apply ltb_asymm. apply ord_lt_ltb. apply coeff_lt. lia.
    * apply ord_eqb_eq in Y. destruct Y. rewrite ord_ltb_irrefl in H1. rewrite ord_eqb_refl in H1. destruct (nat_semiconnex_bool n n1) as [Y | [Y | Y]]; try rewrite Y in *. inversion H1.
      --  destruct (ord_semiconnex_bool alpha1 gamma1) as [X | [X | X]].
          ++  rewrite X. apply ord_ltb_irrefl.
          ++  rewrite (ltb_asymm _ _ X). rewrite ord_eqb_symm. rewrite (ord_ltb_neb _ _ X). apply ltb_asymm. apply ord_lt_ltb. apply coeff_lt. apply lt_nat_decid. auto.
          ++  apply ord_eqb_eq in X. destruct X. rewrite ord_ltb_irrefl. rewrite ord_eqb_refl. apply ltb_asymm. apply ord_lt_ltb. apply coeff_lt. apply lt_nat_decid in Y. lia.
      --  apply nat_eq_decid in Y. destruct Y. destruct (ord_semiconnex_bool alpha1 gamma1) as [X | [X | X]].
          ++  rewrite X. apply ord_ltb_irrefl.
          ++  rewrite (ltb_asymm _ _ X). rewrite ord_eqb_symm. rewrite (ord_ltb_neb _ _ X). rewrite lt_nat_irrefl in H1. simpl. rewrite ord_ltb_irrefl. rewrite ord_eqb_refl. rewrite lt_nat_irrefl. auto. 
          ++  apply ord_eqb_eq in X. destruct X. rewrite ord_ltb_irrefl. rewrite ord_eqb_refl. apply ord_ltb_irrefl.
Qed.

Lemma add_right_non_decr : forall alpha beta, ord_ltb (ord_add alpha beta) alpha = false.
Proof.
intros. destruct beta. rewrite ord_add_zero. apply ord_ltb_irrefl. induction alpha. auto. simpl. destruct (ord_semiconnex_bool alpha1 beta1) as [X | [X | X]].
- rewrite X. apply ltb_asymm. apply ord_lt_ltb. apply head_lt. apply ord_ltb_lt. auto.
- rewrite (ltb_asymm _ _ X). rewrite ord_eqb_symm. rewrite (ord_ltb_neb _ _ X). destruct (ord_semiconnex_bool (ord_add alpha2 (cons beta1 n beta2)) alpha2) as [X1 | [X1 | X1]].
  + rewrite X1 in IHalpha2. inversion IHalpha2.
  + apply ltb_asymm. apply ord_lt_ltb. apply tail_lt. apply ord_ltb_lt. auto.
  + apply ord_eqb_eq in X1. rewrite X1. apply ord_ltb_irrefl. 
- apply ord_eqb_eq in X. destruct X. rewrite ord_ltb_irrefl. rewrite ord_eqb_refl. apply ltb_asymm. apply ord_lt_ltb. apply coeff_lt. lia.
Qed.

Lemma ord_mult_non_decr1 : forall alpha beta, nf alpha -> ord_lt Zero beta -> ord_ltb (ord_mult alpha beta) alpha = false.
Proof.
intros. induction beta. inversion H0. destruct alpha. auto. simpl. destruct beta1. destruct n. rewrite minus_n_0. rewrite mult1_r. apply ord_ltb_irrefl. apply ltb_asymm. apply ord_lt_ltb. apply coeff_lt. lia.
simpl. rewrite (ltb_asymm _ _ (ord_lt_ltb _ _ (add_right_incr_corr _ _ (zero_lt _ _ _)))). rewrite ord_eqb_symm. rewrite (ord_ltb_neb _ _ (ord_lt_ltb _ _ (add_right_incr_corr _ _ (zero_lt _ _ _)))). auto.
Qed.

Lemma ord_mult_non_decr2 : forall alpha beta, nf alpha -> ord_lt Zero beta -> ord_ltb (ord_mult beta alpha) alpha = false.
Proof.
intros. destruct beta. inversion H0. induction alpha. auto. simpl. destruct alpha1. destruct n0. rewrite minus_n_0. rewrite mult1_r. destruct beta1.
- destruct n. simpl. inversion H. destruct beta2; auto. inversion H4. auto.
- apply ltb_asymm. apply ord_lt_ltb. apply head_lt. apply zero_lt.
- simpl. destruct beta1.
  + rewrite ord_ltb_irrefl. rewrite ord_eqb_refl. destruct (nat_semiconnex_bool (S (n0 + n * S (S n0))) (S n0)) as [X | [X | X]].
    * apply lt_nat_decid in X. lia.
    * rewrite X. rewrite (lt_nat_asymm _ _ X). auto.
    * apply nat_eq_decid in X. rewrite X. rewrite lt_nat_irrefl. inversion H. destruct beta2; auto. inversion H4.
  + auto.
- simpl. rewrite (add_left_non_decr _ _). rewrite lt_nat_irrefl. rewrite (IHalpha2 (nf_hered_third _ _ _ H)). case (ord_eqb (ord_add beta1 (cons alpha1_1 n1 alpha1_2)) (cons alpha1_1 n1 alpha1_2)); auto.
Qed.

Lemma ord_exp_omega_le : forall alpha, nf alpha -> ord_lt (cons Zero 0 Zero) alpha -> ord_lt (cons (ord_2_exp alpha) 0 Zero) (ord_2_exp (cons alpha 0 Zero)) \/ cons (ord_2_exp alpha) 0 Zero = ord_2_exp (cons alpha 0 Zero).
Proof.
apply (transfinite_induction exp_omega_le). unfold exp_omega_le. intros. rename x into alpha. rename H0 into IH. rename H1 into H0. destruct (ord_2_exp_fp alpha H) as [O | O].
- case (is_succ alpha) eqn:X.
  + destruct (ord_semiconnex (cons Zero 0 Zero) (ord_pred alpha)) as [X1 | [X1 | X1]].
    * destruct (ord_semiconnex (cons (cons Zero 0 Zero) 0 Zero) alpha) as [X2 | [X2 | X2]].
      --  rewrite ord_2_exp_omega; auto. rewrite <- (ord_succ_pred_if_succ alpha) at 1; auto. rewrite ord_2_exp_succ_mult. destruct (IH _ (ord_nf_pred _ H) (ord_pred_lt _ H X) X1) as [X3 | X3].
          ++  case (ord_eqb (cons (cons Zero 0 Zero) 0 Zero) (ord_pred alpha)) eqn:X4.
              **  apply ord_eqb_eq in X4. rewrite <- (ord_succ_pred_if_succ alpha) at 2; auto. destruct X4. left. apply head_lt. apply head_lt. apply head_lt. apply zero_lt.
              **  left. assert (ord_lt (cons (cons Zero 0 Zero) 0 Zero) (ord_pred alpha)).
                  { destruct (ord_semiconnex (cons (cons Zero 0 Zero) 0 Zero) (ord_pred alpha)) as [Y | [Y | Y]]. auto. inversion Y; inversion H3. destruct H2. inversion X1. destruct H6.
                    destruct alpha. inversion H0. destruct alpha1. inversion H; inversion H12. destruct H13. destruct n1; inversion H1. inversion X2; inversion H16. destruct alpha2; inversion H1. inversion H8. inversion H8. inversion H8. destruct Y. inversion X4. }
                  rewrite ord_2_exp_omega in X3; auto. inversion X3.
                  { simpl. case (ord_2_exp (ord_pred alpha)) eqn:X5. apply head_lt. apply zero_lt. apply head_lt. apply head_lt. inversion H3. apply (lt_trans _ (ord_pred alpha)); auto.
                    rewrite <- ord_succ_pred_if_succ; auto. apply ord_succ_monot. inversion H10. inversion H10. }
                  { inversion H3. }
                  { inversion H3. }
                  { apply ord_nf_pred. auto. }
          ++  case (ord_eqb (cons (cons Zero 0 Zero) 0 Zero) (ord_pred alpha)) eqn:X4.
              **  apply ord_eqb_eq in X4. rewrite <- (ord_succ_pred_if_succ alpha) at 2; auto. destruct X4. left. apply head_lt. apply head_lt. apply head_lt. apply zero_lt.
              **  left. assert (ord_lt (cons (cons Zero 0 Zero) 0 Zero) (ord_pred alpha)). 
                  { destruct (ord_semiconnex (cons (cons Zero 0 Zero) 0 Zero) (ord_pred alpha)) as [Y | [Y | Y]]. auto. inversion Y; inversion H3. destruct H2. inversion X1. destruct H6.
                    destruct alpha. inversion H0. destruct alpha1. inversion H; inversion H12. destruct H13. destruct n1; inversion H1. inversion X2; inversion H16. destruct alpha2; inversion H1. inversion H8. inversion H8. inversion H8. destruct Y. inversion X4. }
                  rewrite ord_2_exp_omega in X3; auto. inversion X3.
                  { simpl. case (ord_2_exp (ord_pred alpha)) eqn:X5. apply head_lt. apply zero_lt. apply head_lt. apply head_lt. inversion H3. rewrite <- ord_succ_pred_if_succ; auto. apply ord_succ_monot. }
                  { apply ord_nf_pred. auto. }
          ++  apply ord_nf_pred. auto.
      --  inversion X2. destruct H1. inversion H0. inversion H3; inversion H8. symmetry in H1,H4,H5,H10,H7,H8,H9. destruct H1,H2,H4,H5,H6,H10,H7,H8,H9. inversion H. destruct H5.
          destruct n. inversion X1. simpl. left. apply head_lt. case (2 ^ n + (2 ^ n + 0) + (2 ^ n + (2 ^ n + 0) + 0)) eqn:X4. apply zero_lt. apply head_lt. apply zero_lt. inversion H5. inversion H3. inversion H3.
      --  destruct X2. inversion X.
    * left. inversion X1; inversion H3. destruct alpha. inversion X. destruct alpha1. destruct alpha2. destruct n0. simpl. inversion H0; inversion H7. inversion H2. inversion H2. destruct alpha2; inversion H2.
    * left. destruct alpha. inversion X1. destruct alpha1. destruct alpha2. destruct n; inversion X1. destruct H2. apply head_lt. apply head_lt. apply zero_lt.
      destruct alpha2_1; destruct alpha2_2; destruct n0; inversion X1. inversion H; inversion H5. destruct alpha2; inversion X1.
  + destruct (ord_not_succ_is_mul _ H X) as [beta [HB1 HB2]].  case (ord_eqb alpha beta) eqn:X1.
    * right. rewrite HB1 at 1. rewrite ord_2_exp_eval; auto. apply ord_eqb_eq in X1. destruct X1. destruct alpha. inversion H0. rewrite ord_2_exp_omega; auto. rewrite HB1. apply ord_mult_monot; auto. apply zero_lt.
    * left. rewrite HB1 at 1. rewrite ord_2_exp_eval; auto. destruct (ord_semiconnex (nat_ord 1) beta) as [X2 | [X2 | X2]].
      --  rewrite ord_2_exp_omega; auto. apply head_lt. apply head_lt. apply ord_ltb_lt. pose (ord_mult_non_decr2 beta (cons (cons Zero 0 Zero) 0 Zero) HB2 (zero_lt _ _ _)). rewrite <- HB1 in e. destruct (ord_semiconnex_bool alpha beta) as [X3 | [X3 | X3]].
          rewrite e in X3. inversion X3. auto. rewrite X1 in X3. inversion X3. rewrite HB1.  apply ord_mult_monot;auto. apply zero_lt.
      --  inversion X2; inversion H3. destruct H1. simpl in HB1. rewrite HB1 in X1. inversion X1.
      --  destruct X2. simpl in *. rewrite HB1. simpl. repeat apply head_lt. apply zero_lt.
- rewrite O. left. apply head_lt. apply head_lt. apply head_lt. apply zero_lt.
Qed.

Lemma ord_succ_lt_exp_succ_max_left : forall alpha beta, nf alpha -> nf beta -> ord_lt (ord_succ alpha) (ord_2_exp (ord_succ (ord_max alpha beta))).
Proof.
intros. case (ord_ltb alpha beta) eqn:X1.
- rewrite (ord_max_lem1 _ _ X1). destruct (ord_2_exp_fp (ord_succ alpha)).
  + apply ord_succ_nf. auto.
  + apply (lt_trans _ _ _ H1). apply ord_2_exp_monot; try apply ord_succ_nf; auto. apply ord_lt_succ. apply ord_ltb_lt. auto.
  + pose (ord_succ_is_succ  _ H). rewrite H1 in e. inversion e.
- rewrite (ord_max_lem2 _ _ X1). destruct (ord_2_exp_fp (ord_succ alpha)); auto.
  + apply ord_succ_nf. auto.
  + pose (ord_succ_is_succ  _ H). rewrite H1 in e. inversion e.
Qed.

Lemma ord_succ_lt_exp_succ_max_right : forall alpha beta, nf alpha -> nf beta -> ord_lt (ord_succ beta) (ord_2_exp (ord_succ (ord_max alpha beta))).
Proof.
intros. destruct (ord_semiconnex_bool alpha beta) as [X1 | [X1 | X1]].
- rewrite (ord_max_lem1 _ _ X1). destruct (ord_2_exp_fp (ord_succ beta)); auto.
  + apply ord_succ_nf. auto.
  + pose (ord_succ_is_succ  _ H0). rewrite H1 in e. inversion e.
- rewrite (ord_max_lem2 _ _ (ltb_asymm _ _ X1)). destruct (ord_2_exp_fp (ord_succ alpha)); auto.
  + apply ord_succ_nf. auto.
  + refine (lt_trans _ _ _ _ H1). apply ord_lt_succ. apply ord_ltb_lt. auto.
  + pose (ord_succ_is_succ  _ H). rewrite H1 in e. inversion e.
- apply ord_eqb_eq in X1. destruct X1. rewrite (ord_max_lem2 _ _ (ord_ltb_irrefl _)). destruct (ord_2_exp_fp (ord_succ alpha)); auto.
  + apply ord_succ_nf. auto.
  + pose (ord_succ_is_succ  _ H). rewrite H1 in e. inversion e.
Qed.

Lemma ord_succ_lt_exp_succ_dub_succ : forall alpha, nf alpha -> ord_ltb (ord_succ alpha) (ord_2_exp (ord_succ alpha)) = true -> ord_ltb  (ord_2_exp (ord_succ alpha)) (ord_succ (ord_succ alpha)) = false.
Proof.
intros alpha. induction alpha. intros. auto. intros. simpl. destruct alpha1. inversion H; inversion H4.
- symmetry in H1. destruct H1,H3,H4,H5. unfold ord_2_exp. unfold ord_succ. apply ltb_asymm. apply ord_lt_ltb. case (2 ^ (S (S n0))) eqn:Y. pose (exp_succ (S (S n0))). lia. apply coeff_lt. pose (nat_exp_monot_lem n0). simpl in *. lia.
- destruct alpha1_1.
  + destruct n0.
    * pose (IHalpha2 (nf_hered_third _ _ _ H)). simpl. pose (ord_succ_not_exp_fp alpha2 (ord_succ_nf _ (nf_hered_third _ _ _ H))). inversion H.
      --  inversion H2; inversion H8. symmetry in H1,H5,H7. destruct H1,H3,H4,H5,H7,H8,H9. simpl. destruct n0; auto.
      --  inversion H5; inversion H10. symmetry in H1,H7,H9. destruct H1,H2,H3,H7,H9,H10,H11. apply ord_lt_one in H4. symmetry in H4. destruct H4. 
          unfold ord_2_exp. unfold ord_succ. apply ltb_asymm. apply ord_lt_ltb. case (2 ^ (S (S n'))) eqn:Y. pose (exp_succ (S (S n'))). lia. simpl. destruct n0.
          destruct n. pose (nat_2_exp_succ_not_one (S n')). lia. apply coeff_lt. lia. apply head_lt. apply coeff_lt. lia.
    * simpl. inversion H. auto. inversion H5; inversion H10. symmetry in H1,H7,H9. destruct H1,H2,H3,H7,H9,H10,H11. apply ltb_asymm. apply ord_lt_ltb. apply (lt_trans _ (cons (cons (cons Zero n0 Zero) n1 Zero) 0 Zero)).
      --  apply head_lt. apply head_lt. apply zero_lt.
      --  apply ord_mult_monot. apply ord_gt_zero_exp_gt_one. apply ord_succ_nf. auto. destruct a'; apply zero_lt. apply nf_2_exp. apply ord_succ_nf. auto. apply zero_lt.
  + simpl. apply ltb_asymm. apply ord_lt_ltb. apply (lt_trans _ (cons (cons (cons (cons alpha1_1_1 n1 alpha1_1_2) n0 alpha1_2) n Zero) 0 Zero)).
  --  repeat apply head_lt. apply ord_lt_self.
  --  apply ord_mult_monot. apply ord_gt_zero_exp_gt_one. apply ord_succ_nf. apply (nf_hered_third _ _ _ H). destruct alpha2. apply zero_lt. destruct alpha2_1; apply zero_lt. apply nf_2_exp. apply ord_succ_nf. apply (nf_hered_third _ _ _ H). apply zero_lt.
Qed.

Lemma ord_max_succ_succ : forall alpha beta, ord_max (ord_succ alpha) (ord_succ beta) = ord_succ (ord_max alpha beta).
Proof.
intros. destruct (ord_semiconnex_bool alpha beta) as [H | [H | H]].
- rewrite ord_max_lem1. rewrite ord_max_lem1; auto. apply ord_lt_ltb. apply ord_lt_succ. apply ord_ltb_lt. auto.
- rewrite ord_max_lem2. rewrite ord_max_lem2; auto. rewrite ltb_asymm; auto. rewrite ltb_asymm; auto. apply ord_lt_ltb. apply ord_lt_succ. apply ord_ltb_lt. auto.
- apply ord_eqb_eq in H. destruct H. rewrite ord_max_lem2. rewrite ord_max_lem2; auto. apply ord_ltb_irrefl. apply ord_ltb_irrefl.
Qed.

Lemma ord_max_nat : forall n m, ord_max (nat_ord n) (nat_ord m) = nat_ord (max n m).
Proof.
intros n. induction n.
- destruct m; auto.
- destruct m; auto. unfold max. fold max. repeat rewrite <- ord_succ_nat. rewrite ord_max_succ_succ. rewrite IHn. auto. 
Qed.

Lemma ord_trans_inv : forall alpha beta gamma, ord_ltb alpha beta = false -> ord_ltb beta gamma = false -> ord_ltb alpha gamma = false.
Proof.
intros. destruct (ord_semiconnex_bool alpha beta) as [X | [X | X]].
- rewrite X in H. inversion H.
- destruct (ord_semiconnex_bool beta gamma) as [Y | [Y | Y]].
  + rewrite Y in H0. inversion H0.
  + apply ltb_asymm. apply (ord_ltb_trans _ _ _ Y X).
  + apply ord_eqb_eq in Y. destruct Y. auto.
- apply ord_eqb_eq in X. destruct X. auto.
Qed.

Lemma ord_ltb_succ_false : forall alpha beta, ord_ltb alpha beta = false -> ord_ltb (ord_succ alpha) (ord_succ beta)= false.
Proof.
intros. destruct (ord_semiconnex_bool alpha beta) as [X | [X | X]].
- rewrite X in H. inversion H.
- apply ltb_asymm. apply ord_ltb_lt in X. apply ord_lt_ltb. apply ord_lt_succ. auto.
- apply ord_eqb_eq in X. destruct X. apply ord_ltb_irrefl.
Qed.

Lemma ord_ltb_excp_succ_false : forall alpha, nf alpha -> ord_ltb (ord_2_exp (ord_succ alpha)) (ord_succ (ord_2_exp alpha)) = false.
Proof.
intros. destruct alpha. auto. apply ltb_asymm. apply ord_lt_ltb. apply ord_succ_lt_exp_succ; auto. apply zero_lt.
Qed.

Lemma exp_succ_max_false_right : forall alpha beta, nf alpha -> nf beta -> ord_ltb (ord_2_exp (ord_succ (ord_max beta alpha))) alpha = false.
Proof.
intros. apply ltb_asymm. apply ord_lt_ltb. apply (lt_trans _ _ _ (ord_succ_monot _)). apply ord_succ_lt_exp_succ_max_right; auto. 
Qed.

Lemma exp_succ_max_false_left : forall alpha beta, nf alpha -> nf beta -> ord_ltb (ord_2_exp (ord_succ (ord_max alpha beta))) alpha = false.
Proof.
intros. apply ltb_asymm. apply ord_lt_ltb. apply (lt_trans _ _ _ (ord_succ_monot _)). apply ord_succ_lt_exp_succ_max_left; auto. 
Qed.

Lemma exp_max_lt_left_succ : forall alpha beta gamma, nf beta -> nf gamma -> ord_ltb alpha (ord_2_exp (ord_succ (ord_max beta gamma))) = true -> ord_ltb alpha (ord_2_exp (ord_succ (ord_max (ord_succ beta) gamma))) = true.
Proof.
intros. destruct (ord_semiconnex_bool (ord_succ beta) gamma) as [X | [X | X]].
- rewrite (ord_max_lem1 _ _ X). rewrite ord_max_lem1 in H1. auto. apply (ord_ltb_trans _ _ _ (ord_lt_ltb _ _ (ord_succ_monot _)) X).
- destruct (ord_lt_succ_cases _ _ (ord_ltb_lt _ _ X) H0 H).
  + destruct H2. rewrite ord_max_lem2. rewrite ord_max_lem2 in H1. apply (ord_ltb_trans _ _ _ H1). apply ord_lt_ltb. apply ord_2_exp_monot; repeat apply ord_succ_nf; auto.
    apply ord_succ_monot. apply ord_ltb_irrefl. apply ltb_asymm. apply ord_lt_ltb. apply ord_succ_monot.
  + rewrite (ord_max_lem2 _ _ (ltb_asymm _ _ X)). rewrite (ord_max_lem2 _ _ (ltb_asymm _ _ (ord_lt_ltb _ _ H2))) in H1. apply (ord_ltb_trans _ _ _ H1). apply ord_lt_ltb. apply ord_2_exp_monot; repeat apply ord_succ_nf; auto. apply ord_succ_monot. 
- apply ord_eqb_eq in X. destruct X. rewrite (ord_max_lem2 _ _ (ord_ltb_irrefl _)). rewrite (ord_max_lem1 _ _ (ord_lt_ltb _ _ (ord_succ_monot _))) in H1. auto.
Qed.

Lemma exp_max_lt_right_succ : forall alpha beta gamma, nf beta -> nf gamma -> ord_ltb alpha (ord_2_exp (ord_succ (ord_max beta gamma))) = true -> ord_ltb alpha (ord_2_exp (ord_succ (ord_max beta (ord_succ gamma)))) = true.
Proof.
intros. rewrite ord_max_symm in H1. rewrite ord_max_symm. apply exp_max_lt_left_succ; auto.
Qed.

Lemma ord_succ_decr : forall alpha beta, ord_ltb (ord_succ alpha) beta = true -> ord_ltb alpha beta = true.
Proof.
intros alpha. induction alpha.
- intros. destruct beta. inversion H. auto.
- intros. apply ord_ltb_lt in H. destruct alpha1.
  + simpl in H. apply ord_lt_ltb. inversion H. apply head_lt. auto. apply coeff_lt. lia. apply coeff_lt. lia.
  + simpl in H. apply ord_lt_ltb. inversion H. apply head_lt. auto. apply coeff_lt. lia. apply tail_lt. apply ord_ltb_lt. apply IHalpha2. apply ord_lt_ltb. auto.
Qed.

Lemma ord_succ_decr_false : forall alpha beta, nf alpha -> nf beta -> ord_ltb beta (ord_succ alpha) = true -> ord_ltb alpha beta = false.
Proof.
intros. apply ord_ltb_lt in H1. destruct (ord_lt_succ_cases _ _ H1); auto. destruct H2. apply ord_ltb_irrefl. apply ltb_asymm. apply ord_lt_ltb. auto.
Qed.

Lemma ord_ltb_exp_succ : forall alpha, nf alpha -> ord_lt alpha (ord_2_exp (ord_succ alpha)).
Proof.
intros. destruct (ord_2_exp_fp alpha); auto. apply (lt_trans _ _ _ H0). apply ord_2_exp_monot. apply ord_succ_nf. auto. auto. apply ord_succ_monot. rewrite H0. apply coeff_lt. lia. 
Qed.

Lemma ord_succ_add_succ : forall alpha beta, nf alpha -> nf beta -> ord_add alpha (ord_succ beta) = ord_succ (ord_add alpha beta).
Proof.
intros. rewrite <- ord_add_one_succ; auto. rewrite <- ord_add_assoc. rewrite ord_add_one_succ; auto. apply nf_add; auto.
Qed.

Lemma ord_max_le_add : forall alpha beta, nf alpha -> nf beta -> ord_ltb (ord_add alpha beta) (ord_max alpha beta) = false.
Proof.
intros. destruct (ord_semiconnex_bool alpha beta) as [X | [X | X]].
- rewrite ord_max_lem1; auto. apply add_left_non_decr.
- rewrite (ord_max_lem2 _ _ (ltb_asymm _ _ X)). destruct beta. rewrite ord_add_zero. apply ord_ltb_irrefl. apply ltb_asymm. apply ord_lt_ltb. apply add_right_incr_corr. apply zero_lt.
- apply ord_eqb_eq in X. destruct X. rewrite (ord_max_lem2 _ _ (ord_ltb_irrefl _ )). destruct alpha. auto. simpl. rewrite ord_ltb_irrefl. rewrite ord_eqb_refl. apply ltb_asymm. apply ord_lt_ltb. apply coeff_lt. lia.
Qed.

Lemma ord_max_add_comm : forall alpha beta gamma, ord_add alpha (ord_max beta gamma) = ord_max (ord_add alpha beta) (ord_add alpha gamma).
Proof.
intros. destruct (ord_semiconnex_bool beta gamma) as [X | [X | X]].
- rewrite (ord_max_lem1 _ _ X). rewrite (ord_max_lem1 _ _ (ord_lt_ltb _ _ (add_right_incr _ _ _ (ord_ltb_lt _ _ X)))). auto.
- rewrite (ord_max_lem2 _ _ (ltb_asymm _ _ X)). rewrite (ord_max_lem2 _ _ (ltb_asymm _ _ (ord_lt_ltb _ _ (add_right_incr _ _ _ (ord_ltb_lt _ _ X))))). auto.
- apply ord_eqb_eq in X. destruct X. rewrite (ord_max_lem2 _ _ (ord_ltb_irrefl _)). rewrite (ord_max_lem2 _ _ (ord_ltb_irrefl _)). auto.
Qed.

Lemma ord_max_split_false : forall alpha beta gamma delta, ord_ltb alpha gamma = false -> ord_ltb beta delta = false -> ord_ltb (ord_max alpha beta) (ord_max gamma delta) = false.
Proof.
intros. destruct (ord_semiconnex_bool alpha beta) as [X | [X | X]].
- rewrite (ord_max_lem1 _ _ X). case (ord_ltb gamma delta) eqn:X1.
  + rewrite (ord_max_lem1 _ _ X1). auto.
  + rewrite (ord_max_lem2 _ _ X1). apply (ord_trans_inv _ _ _ (ltb_asymm _ _ X) H).
- rewrite (ord_max_lem2 _ _ (ltb_asymm _ _ X)). case (ord_ltb gamma delta) eqn:X1.
  + rewrite (ord_max_lem1 _ _ X1).  apply (ord_trans_inv _ _ _ (ltb_asymm _ _ X) H0).
  + rewrite (ord_max_lem2 _ _ X1). auto.
- apply ord_eqb_eq in X. destruct X. rewrite (ord_max_lem2 _ _ (ord_ltb_irrefl _)). case (ord_ltb gamma delta) eqn:X1.
  + rewrite (ord_max_lem1 _ _ X1). auto.
  + rewrite (ord_max_lem2 _ _ X1). auto.
Qed.
Close Scope cantor_scope.