Add LoadPath "theories/Casteran" as Ordering.
Add LoadPath "theories/Maths" as Maths_Facts.
Add LoadPath "theories/Logic" as Systems.

Require Import Lia.
Require Import Nat.
Require Import Wellfounded.

From Maths_Facts Require Import naturals.
From Maths_Facts Require Import lists.
From Maths_Facts Require Import ordinals.

From Systems Require Import definitions.
From Systems Require Import fol.
From Systems Require Import PA_omega.

Notation "b1 && b2" := (andb b1 b2).
Notation "b1 || b2" := (orb b1 b2).
Notation eq_nat := Nat.eqb.

Definition impl (A B : formula) := (lor (neg A) B).
Notation "A1 ~> A2" := (impl A1 A2) (at level 60).
Notation "t # s" := (atom (equ t s)) (at level 80).

Inductive Peano_Theorems_Base : formula -> Type :=
| FOL1 : forall (A B : formula),
            Peano_Theorems_Base (A ~> (B ~> A))

| FOL2 : forall (A B C : formula),
            Peano_Theorems_Base ((A ~> (B ~> C)) ~> ((A ~> B) ~> (A ~> C)))

| FOL3 : forall (A B : formula),
            Peano_Theorems_Base ((neg A ~> neg B) ~> ((neg A ~> B) ~> A))

| FOL4 : forall (A : formula) (n : nat) (t : term),
            closed_t t = true ->
                Peano_Theorems_Base (lor (neg(univ n A)) (substitution A n t))

| FOL5 : forall (A B : formula) (n : nat),
            member n (free_list A) = false ->
                Peano_Theorems_Base ((univ n (A ~> B)) ~> (A ~> (univ n B)))

| MP : forall (A B : formula),
          Peano_Theorems_Base (A ~> B) ->
              Peano_Theorems_Base A ->
                  Peano_Theorems_Base B

| UG : forall (A : formula) (n : nat),
          Peano_Theorems_Base A ->
              Peano_Theorems_Base (univ n A)

| equ_trans : Peano_Theorems_Base  (univ 0 (univ 1 (univ 2 ((var 0 # var 1) ~> ((var 1 # var 2) ~> (var 0 # var 2))))))

| equ_succ : Peano_Theorems_Base (univ 0 (univ 1 ((var 0 # var 1) ~> ((succ (var 0)) # (succ (var 1))))))

| non_zero : Peano_Theorems_Base (univ 0 (neg (zero # (succ (var 0)))))

| succ_equ : Peano_Theorems_Base (univ 0 (univ 1 ((succ (var 0) # succ (var 1)) ~> (var 0 # var 1))))

| pl0 : Peano_Theorems_Base (univ 0 ((plus (var 0) zero) # (var 0)))

| plS : Peano_Theorems_Base (univ 0 (univ 1 ((plus (var 0) (succ (var 1))) # (succ (plus (var 0) (var 1))))))

| ml0 : Peano_Theorems_Base (univ 0 ((times (var 0) zero) # zero))

| mlS : Peano_Theorems_Base (univ 0 (univ 1 ((times (var 0) (succ (var 1))) # (plus (times (var 0) (var 1)) (var 0)))))

| induct : forall (A : formula) (n : nat),
              Peano_Theorems_Base (substitution A n zero ~> ((univ n (A ~> (substitution A n (succ (var n))))) ~> (univ n A))).

Inductive Peano_Theorems_Implication : formula -> nat -> ord -> Type :=
| I_FOL1 : forall (A B : formula),
              Peano_Theorems_Implication (A ~> (B ~> A))
                  0 (ord_succ (ord_succ (nat_ord (num_conn A + num_conn A))))

| I_FOL2 : forall (A B C : formula),
              Peano_Theorems_Implication ((A ~> (B ~> C)) ~> ((A ~> B) ~> (A ~> C)))
                  (num_conn (neg B)) (ord_succ (ord_max (ord_succ (nat_ord (num_conn (lor (neg A) B) + num_conn (lor (neg A) B))))
                                                        ((ord_succ (nat_ord (num_conn (lor (neg A) (lor (neg B) C)) + num_conn (lor (neg A) (lor (neg B) C))))))))

| I_FOL3 : forall (A B : formula),
              Peano_Theorems_Implication ((neg A ~> neg B) ~> ((neg A ~> B) ~> A))
                  0 (ord_succ (ord_max (ord_succ (ord_succ (ord_succ (nat_ord (num_conn (A) + num_conn (A))))))
                                        ((ord_succ (ord_max (ord_succ (ord_succ (ord_succ (nat_ord (num_conn A + num_conn A)))))
                                                            (ord_succ (ord_succ (nat_ord (num_conn (neg B) + num_conn (neg B))))))))))

| I_FOL4 : forall (A : formula) (n : nat) (t : term),
              closed_t t = true ->
                  Peano_Theorems_Implication (lor (neg(univ n A)) (substitution A n t))
                      0 (ord_succ (ord_succ (nat_ord (num_conn (substitution A n t) + num_conn (substitution A n t)))))

| I_FOL5 : forall (A B : formula) (n : nat),
              member n (free_list A) = false ->
                  Peano_Theorems_Implication ((univ n (A ~> B)) ~> (A ~> (univ n B)))
                      0 (ord_succ (ord_succ (ord_succ (nat_ord (num_conn (lor (neg A) B) + num_conn (lor (neg A) B))))))

| I_MP : forall (A B : formula) (d1 d2 : nat) (alpha beta : ord),
            Peano_Theorems_Implication (A ~> B) d1 alpha ->
                Peano_Theorems_Implication A d2 beta ->
                    Peano_Theorems_Implication B
                        (max (max d2 d1) (num_conn (neg A))) (ord_succ (ord_succ (ord_max beta alpha)))

| I_UG : forall (A : formula) (n d : nat) (alpha : ord),
            Peano_Theorems_Implication A d alpha ->
                (forall t, closed_t t = true -> Peano_Theorems_Implication (substitution A n t) d alpha) ->
                    Peano_Theorems_Implication (univ n A) d (ord_succ alpha) 

| I_equ_trans : forall (t s r : term),
                  Peano_Theorems_Implication  ((t # s) ~> ((s # r) ~> (t # r)))
                      0 (ord_succ (ord_succ (nat_ord (num_conn (atom (equ s t))))))

| I_equ_succ : forall (t s : term),
                  Peano_Theorems_Implication ((t # s) ~> ((succ t) # (succ s))) 0 (ord_succ Zero)

| I_non_zero : forall (t : term),
                  Peano_Theorems_Implication (neg (zero # (succ t))) 0 Zero

| I_succ_equ : forall (t s : term),
                  Peano_Theorems_Implication ((succ t # succ s) ~> (t # s)) 0 (ord_succ Zero)

| I_pl0 : forall (t : term),
              Peano_Theorems_Implication ((plus t zero) # t) 0 Zero

| I_plS : forall (t s : term),
              Peano_Theorems_Implication ((plus t (succ s)) # (succ (plus t s))) 0 Zero

| I_ml0 : forall (t : term),
              Peano_Theorems_Implication ((times t zero) # zero) 0 Zero

| I_mlS : forall (t s : term),
              Peano_Theorems_Implication ((times t (succ s)) # (plus (times t s) t)) 0 Zero

| I_induct : forall (A : formula) (n : nat),
                Peano_Theorems_Implication (substitution A n zero ~> ((univ n (A ~> (substitution A n (succ (var n))))) ~> (univ n A)))
                    (num_conn A + 1) (ord_succ (ord_succ (cons (nat_ord 1) 0 Zero))).

Fixpoint inductive_chain (A : formula) (n m : nat) : formula :=
match m with
| 0 => neg ((substitution A n (represent 0)) ~> (substitution A n (succ (represent 0))))
| (S m') => (lor (inductive_chain A n m')
                  (neg ((substitution A n (represent (S m'))) ~> (substitution A n (succ (represent (S m')))))))
end.

Definition inductive_implication (A : formula) (n m : nat) : formula :=
match m with
| 0 => (lor (substitution A n (represent m)) (neg (substitution A n (represent 0))))
| S m' => lor (lor (inductive_chain A n m') (substitution A n (represent m))) (neg (substitution A n (represent 0)))
end.

Lemma ind_chain_closed :
    forall A n m,
        closed (univ n A) = true ->
            closed (inductive_chain A n m) = true.
Proof.
intros A n m CA.
induction m;
unfold inductive_chain, closed; fold inductive_chain closed;
try rewrite IHm;
unfold "&&", "~>", closed; fold closed;
rewrite succ_repr;
repeat rewrite (closed_univ_sub_repr _ _ CA _);
unfold "&&";
reflexivity.
Qed.

Lemma inductive_implication_theorem :
    forall A n (c : c_term),
        closed (univ n A) = true ->
            PA_omega_theorem (inductive_implication A n (value c))
                0 (ord_add (nat_ord (S (num_conn A + num_conn A))) (nat_ord (3 * (S (value c))))).
Proof.
intros A n c CA.
induction (value c).

- apply (ord_incr _ _ (ord_succ (nat_ord (num_conn A + num_conn A)))).
  + rewrite <- (num_conn_sub _ n (represent 0)).
    apply exchange1.
    apply LEM.
    apply (closed_univ_sub_repr _ _ CA).
  + rewrite <- ord_add_nat.
    rewrite ord_succ_nat.
    apply nat_ord_lt.
    lia.
  + apply nf_add;
    apply nf_nat.

- assert ((ord_add (nat_ord (S (num_conn A + num_conn A))) (nat_ord (3 * S (S n0)))) = (ord_succ (ord_max (ord_succ (ord_succ (ord_add (nat_ord (S (num_conn A + num_conn A))) (nat_ord (3 * (S (n0))))))) (ord_succ (ord_succ (nat_ord (num_conn A + num_conn A))))))) as EQ.
  { repeat rewrite <- ord_add_nat.
    repeat rewrite ord_max_succ_succ.
    rewrite ord_max_lem2.
    { repeat rewrite ord_succ_nat.
      unfold mul.
      repeat rewrite plus_n_0.
      repeat rewrite plus_assoc.
      repeat rewrite <- plus_n_Sm.
      reflexivity. }
    { apply ltb_asymm.
      apply ord_lt_ltb.
      apply nat_ord_lt.
      lia. } }
  rewrite EQ.
  assert (max 0 0 = 0) as EQ1. lia. destruct EQ1.
  destruct n0;
  unfold inductive_implication, inductive_chain;
  fold inductive_chain;
  unfold "~>".    
    + apply associativity2.
      apply demorgan2. 
      * apply negation2.
        apply exchange1.
        apply exchange2.
        apply associativity2.
        apply (weakening _ _ _ _ (closed_univ_sub_repr _ _ CA _) IHn0).
      * apply associativity1.
        apply exchange1.
        apply weakening.
        --  unfold closed; fold closed.
            apply (closed_univ_sub_repr _ _ CA).
        --  rewrite <- (num_conn_sub A n (represent (S 0))).
            apply LEM.
            apply (closed_univ_sub_repr _ _ CA).
    + apply exchange4.
      apply exchange2.
      apply exchange1.
      apply demorgan2.
      * apply negation2.
        apply exchange1.
        apply exchange2.
        apply exchange4.
        apply exchange2.
        apply exchange1.
        apply (weakening _ _ _ _ (closed_univ_sub_repr _ _ CA _) IHn0).
      * apply exchange1.
        apply exchange4.
        apply exchange2.
        apply associativity2.
        apply weakening.
        --  unfold closed; fold closed.
            rewrite (ind_chain_closed _ _ _ CA).
            rewrite (closed_univ_sub_repr _ _ CA).
            unfold "&&".
            reflexivity.
        --  rewrite <- (num_conn_sub A n (represent (S (S n0)))).
            apply LEM.
            apply (closed_univ_sub_repr _ _ CA).
Qed.

Lemma inductive_implication_single_theorem :
    forall A n (c : c_term),
        free_list A = [n] ->
            PA_omega_theorem (inductive_implication A n (value c))
                0 (ord_add (nat_ord (S (num_conn A + num_conn A))) (nat_ord (3 * (S (value c))))).
intros A n c LIST.
apply inductive_implication_theorem.
unfold closed; fold closed.
rewrite LIST.
rewrite eq_nat_refl.
rewrite eq_list_refl.
unfold "&&".
destruct (closed A);
reflexivity.
Qed.

Lemma inductive_implication_closed_theorem :
    forall A n (c : c_term),
        closed A = true ->
            PA_omega_theorem (inductive_implication A n (value c))
                0 (ord_add (nat_ord (S (num_conn A + num_conn A))) (nat_ord (3 * (S (value c))))).
intros A n c CA.
apply inductive_implication_theorem.
unfold closed; fold closed.
rewrite CA.
reflexivity.
Qed.

Lemma induction_iterate_general :
    forall (A : formula) (n m : nat) (t : term) (alpha : ord),
        PA_omega_theorem (lor (lor (lor (inductive_chain A n (S m)) (substitution A n t))
                                    (neg (substitution A n zero)))
                              (neg (univ n (lor (neg A) (substitution A n (succ (var n)))))))
            0 alpha ->
                PA_omega_theorem (lor (lor (lor (inductive_chain A n m) (substitution A n t))
                                            (neg (substitution A n zero)))
                                      (neg (univ n (lor (neg A) (substitution A n (succ (var n)))))))
                    0 (ord_succ alpha).
Proof.
intros A n m c alpha T1.
unfold inductive_chain in T1. fold inductive_chain in T1. unfold "~>" in T1.
apply exchange1.
apply contraction2.
apply associativity2.
apply (quantification2 _ _ _ (closing (represent (S m)) (repr_closed _))).
unfold represent in *. fold represent in *.
unfold closing. unfold projT1.
unfold substitution. fold substitution.
rewrite sub_succ_self.
repeat apply associativity1.
apply exchange1.
apply associativity1.
apply associativity1.
apply exchange4.
apply associativity2.
apply exchange3.
apply associativity1.
apply exchange4.
apply associativity2.
apply exchange2.
apply associativity1.
apply exchange2.
apply exchange4.
apply exchange2.
apply exchange4.
apply associativity1.
apply exchange4.
apply exchange2.
apply exchange4.
apply T1.
Qed.

Lemma induction_terminate :
    forall (A : formula) (n m : nat) (t : term) (alpha : ord),
        PA_omega_theorem (lor (lor (lor (inductive_chain A n m) (substitution A n t))
                                    (neg (substitution A n zero)))
                              (neg (univ n (lor (neg A) (substitution A n (succ (var n)))))))
            0 alpha ->
                PA_omega_theorem (lor (lor (lor (inductive_chain A n 0) (substitution A n t))
                                            (neg (substitution A n zero)))
                                      (neg (univ n (lor (neg A) (substitution A n (succ (var n)))))))
                    0 (ord_add alpha (nat_ord m)).
Proof.
intros A n m.
induction m;
intros c alpha T1.

- rewrite ord_add_zero.
  apply T1.

- rewrite (ord_add_succ_nat_succ_add _ _ (ord_nf _ _ _ T1)).
  apply (IHm _ _ (induction_iterate_general _ _ _ _ _ T1)).
Qed.

Lemma induction_final :
  forall (A : formula) (n m : nat) (t : term) (alpha : ord),
    PA_omega_theorem (lor (lor  (lor  (inductive_chain A n m)
                                      (substitution A n t))
                                (neg (substitution A n zero)))
                          (neg (univ n (lor (neg A) (substitution A n (succ (var n)))))))
                      0 alpha ->
        PA_omega_theorem (lor (lor  (substitution A n t)
                                    (neg (substitution A n zero)))
                              (neg (univ n (lor (neg A) (substitution A n (succ (var n)))))))
                          0 (ord_succ (ord_add alpha (nat_ord m))).
Proof.
intros A n m t alpha T1.
apply exchange1.
apply contraction2.
apply associativity2.
apply (quantification2 _ _ _ (closing (represent 0) (repr_closed _))).
unfold substitution; fold substitution.
rewrite sub_succ_self.
apply associativity1.
apply associativity1.
apply exchange4.
apply exchange2.
apply (induction_terminate _ _ _ _ _ T1). 
Qed.


Lemma induction_single_aux :
  forall (A : formula) (n : nat) (c : c_term),
    free_list A = [n] ->
      PA_omega_theorem (lor (lor  (substitution A n (represent (value c)))
                                  (neg (substitution A n zero)))
                            (neg (univ n (lor (neg A) (substitution A n (succ (var n)))))))
                        0 (cons (nat_ord 1) 0 Zero).
Proof.
intros A n c LIST.
pose proof (inductive_implication_single_theorem _ _  c LIST) as Y1.
destruct (value c) eqn:V.

- apply (ord_incr _ _  (ord_succ (ord_add (ord_succ (ord_succ (nat_ord (S (S (num_conn A + num_conn A)))))) (nat_ord (S 0))))).
  + apply exchange1.
    apply weakening.
    * unfold closed; fold closed.
      case (closed A) eqn:CA.
      --  rewrite (closed_free_list _ CA) in LIST.
          inversion LIST.
      --  unfold "&&".
          unfold free_list; fold free_list.
          rewrite LIST.
          rewrite (free_list_sub_self_eq _ _ (var n) LIST).
          unfold concat.
          unfold remove_dups.
          unfold remove.
          rewrite eq_nat_refl.
          apply eq_list_refl.
    * apply exchange1.
      apply (ord_incr _ _ (ord_succ (nat_ord (num_conn A + num_conn A)))).
      --  rewrite <- (num_conn_sub _ n zero).
          apply LEM.
          apply (one_var_free_lemma _ _ _ (repr_closed 0) LIST).
      --  rewrite ord_add_one_succ.
          ++  repeat rewrite ord_succ_nat.
              apply nat_ord_lt.
              lia.
          ++  repeat apply ord_succ_nf.
              apply nf_nat.
      --  refine (nf_add _ _ _ (nf_nat _)).
          repeat apply ord_succ_nf.
          apply nf_nat. 
  + unfold nat_ord.
    unfold ord_succ.
    unfold ord_add.
    rewrite ord_ltb_irrefl.
    rewrite ord_eqb_refl.
    apply head_lt.
    apply ord_lt_self.
  + apply single_nf.
    apply nf_nat.

- apply (ord_incr _ _  (ord_succ (ord_add (ord_succ (ord_add (nat_ord (S (num_conn A + num_conn A))) (nat_ord (3 * (S (S n0)))))) (nat_ord n0)))).
  + unfold inductive_implication in *.
    apply induction_final.
    apply exchange1.
    refine (weakening _ _ _ _ _ Y1).
    unfold closed; fold closed.
    unfold free_list; fold free_list.
    rewrite (free_list_sub_self _ _ (var n));
    rewrite LIST.
    * unfold concat.
      unfold remove_dups.
      unfold remove.
      rewrite eq_nat_refl.
      rewrite eq_list_refl.
      unfold "&&".
      case (closed A);
      case (closed (substitution A n (succ (var n))));
      reflexivity.
    * unfold member.
      rewrite eq_nat_refl.
      reflexivity.
  + rewrite <- ord_add_succ_nat_succ_add.
    * repeat rewrite <- ord_add_nat.
      rewrite ord_succ_nat.
      apply nat_lt_omega.
      apply zero_lt.
    * apply nf_add;
      apply nf_nat.
  + apply single_nf.
    apply nf_nat. 
Qed.

Lemma induction_closed_aux :
  forall (A : formula) (n : nat) (c : c_term),
    closed A = true ->
      PA_omega_theorem (lor (substitution A n (projT1 c))
                            (lor (neg (substitution A n zero))
                                 (neg (univ n (lor (neg A)
                                                   (substitution A n (succ (var n))))))))
                        0 (ord_succ (ord_add (nat_ord (S (num_conn A + num_conn A))) (nat_ord (3 * (S (value c)))))).
Proof.
intros A n c CA.
pose proof (inductive_implication_closed_theorem _ n c CA) as Y1.
unfold inductive_implication in Y1.
repeat rewrite (closed_subst_eq _ _ _ CA) in Y1.
repeat rewrite (closed_subst_eq _ _ _ CA).
destruct (value c) eqn:V.

- apply exchange1.
  apply exchange2.
  apply exchange1.
  apply weakening.
  + unfold closed.
    fold closed.
    rewrite CA.
    unfold "&&".
    reflexivity.
  + apply exchange1.
    apply Y1.

- apply associativity1.
  apply exchange1.
  apply weakening.
  + unfold closed.
    fold closed.
    rewrite CA.
    unfold "&&".
    reflexivity.
  + apply exchange1.
    apply (ord_incr _ _ _ _ (LEM _ CA)).
    * rewrite ord_succ_nat.
      rewrite <- ord_add_nat.
      apply nat_ord_lt.
      lia.
    * apply single_nf.
      apply zero_nf.
Qed.

Lemma PA_closed_PA_omega :
  forall (A : formula) (d : nat) (alpha : ord),
    Peano_Theorems_Implication A d alpha ->
      (forall (c : c_term), PA_omega_theorem (closure A c) d alpha).
Proof.
intros A d alpha T1.
induction T1;
intros c; unfold "~>" in *.

- pose proof (closure_closed (neg B) c) as Y1.
  pose proof (closure_closed A c) as Y2.
  rewrite (num_conn_closure_eq A c).  
  repeat rewrite closure_lor in *.
  repeat rewrite closure_neg in *.
  apply associativity1.
  apply exchange2.
  apply exchange1.
  apply weakening.
  + apply Y1.
  + apply (LEM _ Y2).  

- pose proof (closure_closed (lor (neg A) B) c) as Y1.
  pose proof (closure_closed (lor (neg A) (lor (neg B) C)) c) as Y2.
  rewrite (num_conn_closure_eq (neg B) c).
  repeat rewrite (num_conn_closure_eq (lor _ _) c).
  repeat rewrite closure_lor in *.
  repeat rewrite closure_neg in *.
  repeat rewrite closure_lor in *.
  repeat rewrite closure_neg in *.
  assert ((max (max 0 0) (num_conn (neg (closure B c)))) = num_conn (neg (closure B c))) as Z. { unfold max. reflexivity. }
  destruct Z.
  apply associativity1.
  apply associativity1.
  apply exchange2.
  apply exchange3.
  apply exchange2.
  apply exchange3.
  apply exchange1.
  apply exchange3.
  apply exchange2.
  apply exchange3.
  apply exchange4.
  apply associativity2.
  apply associativity2.
  apply contraction2.
  apply associativity1.
  apply exchange4.
  apply exchange2.
  apply associativity2.
  apply cut3.
  + apply exchange2.
    apply exchange1.
    apply (LEM _ Y1).
  + apply exchange1.
    apply exchange4.
    apply exchange2.
    apply exchange4.
    apply exchange2.
    apply associativity2.
    apply exchange3.
    apply exchange1.
    apply associativity2.
    apply (LEM _ Y2).    

- pose proof (closure_closed (lor (neg (neg A)) (neg B)) c) as Y1.
  pose proof (closure_closed A c) as Y2.
  pose proof (closure_closed (neg B) c) as Y3.
  rewrite (num_conn_closure_eq A c).
  rewrite (num_conn_closure_eq (neg B) c).
  repeat rewrite closure_lor in *.
  repeat rewrite closure_neg in *.
  repeat rewrite closure_lor in *.
  repeat rewrite closure_neg in *.
  assert (max 0 (max 0 0) = 0) as Z. { unfold max. reflexivity. }
  destruct Z.
  apply demorgan2.
  + apply associativity1.
    apply exchange2.
    apply exchange1.
    apply weakening.
    * apply Y1.
    * apply negation2. apply (LEM _ Y2).
  + apply exchange1.
    apply associativity2.
    apply demorgan2.
    * apply negation2.
      apply associativity1.
      apply exchange1.
      apply weakening.
      -- apply Y3.
      -- apply (LEM _ Y2).
    * apply associativity1.
      apply exchange2.
      apply exchange1.
      apply weakening.
      -- apply Y2.
      -- apply exchange1. apply (LEM _ Y3).

- rename e into Ht.
  rewrite (num_conn_closure_eq _ c).
  pose proof (closure_closed (univ n A) c) as Y1.
  rewrite closure_lor.
  rewrite closure_neg.
  rewrite closure_univ in *.
  pose proof (closed_univ_sub _ _ Y1 _ Ht) as Y2.
  apply (quantification2 _ _ _ (closing t Ht)).
  rewrite <- (closure_subst _ c (closing _ Ht)).
  apply (LEM _ Y2).

- rename e into LIST.
  rewrite (num_conn_closure_eq _ c).
  repeat rewrite closure_lor.
  repeat rewrite closure_neg.
  repeat rewrite closure_univ.
  apply associativity1.
  apply exchange1.
  apply w_rule2.
  intros [m Hm].
  pose proof (closure_closed (lor (neg A) (substitution B n m)) c) as Y1.
  assert (num_conn (lor (neg (closure A c)) (closure (substitution B n m) c)) = num_conn (lor (neg (closure A c)) (closure B c))) as Z.
  { unfold num_conn. fold num_conn.
    repeat rewrite <- num_conn_closure_eq.
    rewrite num_conn_sub.
    reflexivity. }
  destruct Z.
  apply exchange1. 
  apply associativity2.
  apply (quantification2 _ _ _ (closing m Hm) _ _).
  repeat rewrite closure_subst.
  unfold substitution; fold substitution.
  rewrite (closed_subst_eq_aux _ _ _ LIST).
  repeat rewrite closure_lor in *.
  repeat rewrite closure_neg in *.
  apply (LEM _ Y1).

- rewrite (num_conn_closure_eq _ c).  
  rewrite closure_neg.
  apply cut2.
  + apply IHT1_2.
  + rewrite <- closure_neg.
    rewrite <- closure_lor.
    apply IHT1_1.

- rewrite closure_univ.
  apply w_rule1.
  intros [m Hm].
  rewrite closure_subst.
  apply (X _ Hm).

- repeat rewrite closure_lor.
  repeat rewrite closure_neg.
  case (correct_a (equ (closure_t t c) (closure_t s c))) eqn:X. 
  + pose (atom (equ (var 0) (closure_type_t r c (free_list_t r)))) as F.
    assert (closure (atom (equ t r)) c = substitution F 0 (closure_t t c)) as EQ1.
    { unfold F.
      unfold substitution.
      unfold substitution_a.
      unfold substitution_t; fold substitution_t.
      unfold eq_nat.
      rewrite closure_type_equiv.
      rewrite closed_subst_eq_t. reflexivity.
      apply closure_closed_t. }
    assert (closure (atom (equ s r)) c = substitution F 0 (closure_t s c)) as EQ2.
    { unfold F.
      unfold substitution.
      unfold substitution_a.
      unfold substitution_t; fold substitution_t.
      unfold eq_nat.
      rewrite closure_type_equiv.
      rewrite closed_subst_eq_t. reflexivity.
      apply closure_closed_t. }
    rewrite EQ1, EQ2.
    apply weakening.
    * rewrite <- closure_neg.
      apply closure_closed.
    * apply LEM_term.
      --  unfold correct_a in *.
          unfold correctness in *.
          destruct (correct_eval _ _ X) as [Xa Xb].
          destruct (eval (closure_t s c)).
          ++  inversion Xb.
          ++  destruct (eval (closure_t t c)).
              **  inversion Xa.
              **  case (eq_nat (S n0) (S n)) eqn:X1.
                  { rewrite eq_nat_symm in X1. rewrite X1. reflexivity. }
                  { inversion X. }
      --  unfold F.
          unfold free_list.
          unfold free_list_a.
          unfold free_list_t; fold free_list_t.
          unfold concat.
          rewrite closed_free_list_t.
          ++  unfold remove_dups.
              unfold remove.
              reflexivity.
          ++  apply closure_closed_t.
  + apply exchange1.
    apply weakening.
    * unfold closed; fold closed.
      repeat rewrite closure_closed.
      unfold "&&".
      reflexivity.
    * apply (ord_incr _ _ Zero).
      --  apply axiom.
          unfold PA_omega_axiom.
          destruct (correctness_decid (equ (closure_t t c) (closure_t s c))) as [X1 | X1].
          ++  unfold closed_a.
              repeat rewrite closure_closed_t.
              unfold "&&".
              reflexivity.
          ++  rewrite X1 in X.
              inversion X.
          ++  rewrite closure_type_equiv.
              apply X1.
      --  rewrite ord_succ_nat.
          apply zero_lt.
      --  apply ord_succ_nf.
          apply nf_nat.

- rewrite closure_lor.
  rewrite closure_neg. 
  case (correct_a (equ (closure_t t c) (closure_t s c))) eqn:X. 
  + apply weakening.
    * apply closure_closed.
    * apply axiom.
      rewrite closure_type_equiv.
      unfold PA_omega_axiom.
      unfold correct_a in *.
      unfold correctness in *.
      destruct (correct_eval _ _ X) as [Xa Xb].
      repeat rewrite closure_t_succ.
      unfold eval. fold eval.
      destruct (eval (closure_t s c)).
      --  inversion Xb.
      --  destruct (eval (closure_t t c)).
          ++  inversion Xa.
          ++  unfold eq_nat in *; fold eq_nat in *.
              apply X.
  + apply exchange1.
    apply weakening.
    * apply closure_closed.
    * apply axiom.
      unfold PA_omega_axiom. 
      destruct (correctness_decid (equ (closure_t t c) (closure_t s c))) as [X1 | X1].
      --  unfold closed_a.
          repeat rewrite closure_closed_t.
          unfold "&&".
          reflexivity.
      --  rewrite X1 in X.
          inversion X.
      --  rewrite closure_type_equiv.
          apply X1.

- rewrite closure_neg.
  rewrite closure_type_equiv.
  rewrite (closure_closed_id_t _ _ (repr_closed 0)).
  apply axiom.
  unfold PA_omega_axiom. 
  destruct (correctness_decid (equ zero (closure_t (succ t) c))) as [X | X].
  + unfold closed_a.
    rewrite closure_closed_t.
    unfold closed_t.
    unfold "&&".
    reflexivity.
  + unfold correct_a in X.
    unfold correctness in X.
    rewrite closure_t_succ in X.
    unfold eval in X; fold eval in X.
    destruct (eval (closure_t t c));
    inversion X.
  + apply X.
 
- rewrite closure_lor.
  rewrite closure_neg. 
  case (correct_a (equ (closure_t t c) (closure_t s c))) eqn:X. 
  + apply weakening.
    * apply closure_closed.
    * apply axiom.
      rewrite closure_type_equiv.
      unfold PA_omega_axiom.
      unfold correct_a in *.
      unfold correctness in *.
      destruct (correct_eval _ _ X) as [Xa Xb].
      repeat rewrite closure_t_succ.
      unfold eval; fold eval.
      destruct (eval (closure_t s c)).
      --  inversion Xb.
      --  destruct (eval (closure_t t c)).
          ++  inversion Xa.
          ++  unfold eq_nat in *; fold eq_nat in *.
              apply X.
  + apply exchange1.
    apply weakening.
    * apply closure_closed.
    * apply axiom.
      unfold PA_omega_axiom. 
      destruct (correctness_decid (equ (closure_t t c) (closure_t s c))) as [X1 | X1].
      --  unfold closed_a.
          repeat rewrite closure_closed_t.
          unfold "&&".
          reflexivity.
      --  rewrite X1 in X.
          inversion X.
      --  rewrite closure_type_equiv.
          unfold incorrect_a in *. 
          unfold correctness in *.
          repeat rewrite closure_t_succ in *.
          unfold eval; fold eval.
          destruct (eval (closure_t t c)).
          ++  inversion X1.
          ++  destruct (eval (closure_t s c)).
              **  inversion X1.
              **  apply X1.

- rewrite closure_type_equiv.
  rewrite closure_t_plus.
  rewrite (closure_closed_id_t _ _ (repr_closed 0)).
  apply axiom.
  unfold PA_omega_axiom.
  destruct (correctness_decid (equ (plus (closure_t t c) zero) (closure_t t c))) as [X | X].
  + unfold closed_a.
    unfold closed_t; fold closed_t.
    repeat rewrite closure_closed_t.
    unfold "&&".
    reflexivity.
  + apply X.
  + unfold incorrect_a in X.
    unfold correctness in X.
    unfold eval in X; fold eval in X.
    destruct (eval (closure_t t c)).
    * inversion X.
    * rewrite plus_n_0 in X.
      rewrite eq_nat_refl in X.
      inversion X.

- rewrite closure_type_equiv.
  rewrite closure_t_succ.
  repeat rewrite closure_t_plus.
  rewrite closure_t_succ.
  apply axiom.
  unfold PA_omega_axiom.
  destruct (correctness_decid (equ (plus (closure_t t c) (succ (closure_t s c))) (succ (plus (closure_t t c) (closure_t s c))))) as [X | X].
  + unfold closed_a.
    unfold closed_t; fold closed_t.
    repeat rewrite closure_closed_t.
    unfold "&&".
    reflexivity.
  + apply X.
  + unfold incorrect_a in X.
    unfold correctness in X.
    unfold eval in X; fold eval in X.
    destruct (eval (closure_t t c)).
    * inversion X.
    * destruct (eval (closure_t s c)).
      --  inversion X.
      --  rewrite <- plus_n_Sm in X.
          rewrite eq_nat_refl in X.
          inversion X.

- rewrite closure_type_equiv.
  rewrite closure_t_times.
  rewrite (closure_closed_id_t _ _ (repr_closed 0)).
  apply axiom.
  unfold PA_omega_axiom.
  destruct (correctness_decid (equ (times (closure_t t c) zero) zero)) as [X | X].
  + unfold closed_a.
    unfold closed_t; fold closed_t.
    repeat rewrite closure_closed_t.
    unfold "&&".
    reflexivity.
  + apply X.
  + unfold incorrect_a in X.
    unfold correctness in X.
    unfold eval in X; fold eval in X.
    destruct (eval (closure_t t c)).
    * inversion X.
    * rewrite mult_0_r in X.
      rewrite eq_nat_refl in X.
      inversion X.

- rewrite closure_type_equiv.
  rewrite closure_t_plus.
  repeat rewrite closure_t_times. 
  rewrite closure_t_succ.
  apply axiom.
  unfold PA_omega_axiom.
  destruct (correctness_decid (equ (times (closure_t t c) (succ (closure_t s c))) (plus (times (closure_t t c) (closure_t s c)) (closure_t t c))) ) as [X | X].
  + unfold closed_a.
    unfold closed_t; fold closed_t.
    repeat rewrite closure_closed_t.
    unfold "&&".
    reflexivity.
  + apply X.
  + unfold incorrect_a in X.
    unfold correctness in X.
    unfold eval in X. fold eval in X.
    destruct (eval (closure_t t c)).
    * inversion X.
    * destruct (eval (closure_t s c)).
      --  inversion X.
      --  rewrite mult_n_Sm in X.
          rewrite eq_nat_refl in X.
          inversion X.
  
- repeat rewrite closure_lor.
  repeat rewrite closure_neg.
  repeat rewrite closure_univ.
  rewrite <- (closure_subst _ _ czero).
  repeat rewrite closure_type_lor.
  rewrite closure_neg_list.
  rewrite closure_type_sub_remove.
  apply associativity1.
  apply exchange1.
  apply w_rule2.
  intros [m Hm].
  case (closed (closure_type A c (free_list (univ n A)))) eqn:X.
  + assert ( (free_list (univ n (lor (neg A) (substitution A n (succ (var n)))))) = free_list (univ n A)) as LIST.
    { unfold free_list; fold free_list.
      case (member n (free_list A)) eqn:X1.
      { rewrite (free_list_sub_self _ _ m X1).
        rewrite remove_dups_concat_self.
        rewrite <- free_list_remove_dups.
        reflexivity. }
      { rewrite (closed_subst_eq_aux _ _ _ X1).
        rewrite remove_dups_concat_self.
        rewrite <- free_list_remove_dups.
        reflexivity. } }
    rewrite LIST.
    refine (ord_incr _ _ _ _ (deg_incr _ _ _ _ (induction_closed_aux _ _ (closing m Hm) X) _) _ _).
    * lia.
    * apply ord_lt_succ.
      rewrite <- ord_add_nat.
      apply nat_lt_omega.
      apply zero_lt.
    * apply ord_succ_nf.
      apply single_nf.
      apply nf_nat.
  + assert (free_list (closure_type A c (free_list (univ n A))) = [n]) as HL.
    { unfold free_list; fold free_list.
      destruct (free_list_univ_closure A c n) as [L1 | L2].
      { apply L1. }
      { apply free_list_closed in L2.
        rewrite L2 in X.
        inversion X. } } 
    assert (free_list (univ n A) = (free_list (univ n (lor (neg A) (substitution A n (succ (var n))))))) as Z1.
    { unfold free_list; fold free_list.
      case (member n (free_list A)) eqn:X1. 
      { rewrite (free_list_sub_self _ _ m X1).
        rewrite remove_dups_concat_self.
        rewrite <- free_list_remove_dups.
        reflexivity. }
      { rewrite (closed_subst_eq_aux _ _ _ X1).
        rewrite remove_dups_concat_self.
        rewrite <- free_list_remove_dups.
        reflexivity. } }
    assert ((max (max 0 0) (num_conn (neg (substitution (closure_type A c (free_list (univ n A))) n (represent (value (closing m Hm))))))) = (num_conn A + 1)) as Z2.
      { unfold max.
        unfold num_conn; fold num_conn.
        rewrite num_conn_sub.
        rewrite <- num_conn_closure_eq_list.
        rewrite plus_n_1.
        reflexivity. }
    assert ((ord_max (cons (nat_ord 1) 0 Zero) (ord_succ (nat_ord (num_conn (closure_type A c (free_list (univ n A))) + num_conn (closure_type A c (free_list (univ n A))))))) = (cons (nat_ord 1) 0 Zero)) as Z3.
    { rewrite ord_max_lem2.
      { reflexivity. }
      { apply ltb_asymm.
        rewrite ord_succ_nat.
        apply ord_lt_ltb.
        apply nat_lt_omega.
        apply zero_lt. } }
    destruct Z1,Z2,Z3.
    pose proof (induction_single_aux _ _ (closing m Hm) HL) as Y1.
    pose proof (LEM_term (closure_type A c (free_list (univ n A))) n _ _ (cterm_equiv_correct (closing m Hm)) HL) as Y2.
    apply associativity1 in Y1.
    apply exchange1 in Y1.
    apply exchange1.
    apply (cut3 _ _ _ _ _ _ _ Y1 Y2).
Qed.

Lemma PA_Implication_null_impl :
  forall (A : formula) (d n : nat) (alpha : ord) (t : term),
    closed_t t = true ->
      Peano_Theorems_Implication A d alpha ->
        Peano_Theorems_Implication (substitution A n t) d alpha.
Proof.
intros A d n alpha c HC H0.
induction H0; unfold "~>" in *;
unfold substitution in *; fold substitution in *;
unfold num_conn; fold num_conn.
  
- rewrite <- (num_conn_sub _ n c).
  apply I_FOL1.

- rewrite <- (num_conn_sub A n c).
  rewrite <- (num_conn_sub B n c).
  rewrite <- (num_conn_sub C n c).
  apply I_FOL2.

- rewrite <- (num_conn_sub A n c).
  rewrite <- (num_conn_sub B n c).
  apply I_FOL3.

- rename e into Ht.
  case (eq_nat n0 n) eqn:X.
  + apply nat_eq_decid in X.
    destruct X.
    rewrite closed_subst_eq_aux.
    apply (I_FOL4 _ _ _ Ht).
    rewrite (subst_remove _ _ _ Ht).
    apply remove_not_member.
  + rewrite eq_nat_symm in X.
    rewrite (substitution_order _ _ _ _ _ Ht HC X).
    rewrite num_conn_sub.
    rewrite <- (num_conn_sub A n c).
    rewrite <- (num_conn_sub (substitution A n c) n0 t).
    apply (I_FOL4 _ _ _ Ht).

- rename e into LIST.
  case (eq_nat n0 n) eqn:X.
  + apply nat_eq_decid in X.
    destruct X.
    rewrite (closed_subst_eq_aux _ _ _ LIST). 
    apply (I_FOL5 _ _ _ LIST).
  + rewrite <- (num_conn_sub A n c).
    rewrite <- (num_conn_sub B n c).
    apply I_FOL5.
    rewrite (subst_remove _ _ _ HC).
    apply (remove_member_false _ _ _ LIST).

- rewrite <- (num_conn_sub A n c).
  apply I_MP.
  + apply IHPeano_Theorems_Implication1.
  + apply IHPeano_Theorems_Implication2.
  
- case (eq_nat n0 n) eqn:X.
  + apply nat_eq_decid in X.
    destruct X.
    apply (I_UG _ _ _ _ H0 p).
  + apply (I_UG _ _ _ _ IHPeano_Theorems_Implication).
    intros t Ht.
    rewrite weak_substitution_order.
    * apply (H _ Ht).
    * rewrite (closed_free_list_t _ HC).
      unfold member.
      reflexivity.
    * rewrite (closed_free_list_t _ Ht).
      unfold member.
      reflexivity.
    * apply X.

- apply I_equ_trans.

- apply I_equ_succ.

- apply I_non_zero.

- apply I_succ_equ.

- apply I_pl0.

- apply I_plS.

- apply I_ml0.

- apply I_mlS.

- case (eq_nat n0 n) eqn:X.
  + apply nat_eq_decid in X.
    destruct X.
    rewrite closed_subst_eq_aux.
    * apply I_induct.
    * rewrite (subst_remove _ _ _ (repr_closed 0)).
      apply remove_not_member.
  + rewrite eq_nat_symm in X.
    rewrite (substitution_order _ _ _ _ _ (repr_closed 0) HC X).
    rewrite (weak_substitution_order _ _ _ (succ (var n0))).
    * rewrite <- (num_conn_sub A n c).
      apply I_induct.
    * unfold free_list_t.
      unfold member.
      rewrite eq_nat_symm in X.
      rewrite X.
      reflexivity.
    * rewrite (closed_free_list_t _ HC).
      unfold member.
      reflexivity.
    * apply X.
Qed.

Lemma PA_Base_equiv_PA_Implication :
  forall (A : formula),
    Peano_Theorems_Base A ->
      {d : nat & {alpha : ord & Peano_Theorems_Implication A d alpha}}.
Proof.
intros A T. induction T.

- exists 0.
  exists (ord_succ (ord_succ (nat_ord (num_conn A + num_conn A)))).
  apply I_FOL1.

- exists (num_conn (neg B)).
  exists (ord_succ (ord_max (ord_succ (nat_ord (num_conn (lor (neg A) B) + num_conn (lor (neg A) B))))
                            ((ord_succ (nat_ord (num_conn (lor (neg A) (lor (neg B) C)) + num_conn (lor (neg A) (lor (neg B) C)))))))).
  apply I_FOL2.

- exists 0.
  exists (ord_succ (ord_max (ord_succ (ord_succ (ord_succ (nat_ord (num_conn (A) + num_conn (A))))))
                            ((ord_succ (ord_max (ord_succ (ord_succ (ord_succ (nat_ord (num_conn A + num_conn A)))))
                                                (ord_succ (ord_succ (nat_ord (num_conn (neg B) + num_conn (neg B)))))))))).
  apply I_FOL3.

- exists 0.
  exists (ord_succ (ord_succ (nat_ord (num_conn (substitution A n t) + num_conn (substitution A n t))))).
  apply (I_FOL4 _ _ _ e).

- exists 0.
  exists (ord_succ (ord_succ (ord_succ (nat_ord (num_conn (lor (neg A) B) + num_conn (lor (neg A) B)))))).
  apply (I_FOL5 _ _ _ e).

- destruct IHT1 as [d1 [alpha1 IHT1]].
  destruct IHT2 as [d2 [alpha2 IHT2]].
  exists (max (max d2 d1) (num_conn (neg A))).
  exists (ord_succ (ord_succ (ord_max alpha2 alpha1))).
  apply I_MP.
  + apply IHT1.
  + apply IHT2.

- destruct IHT as [d [alpha IHT]].
  exists d.
  exists (ord_succ alpha).    
  apply I_UG.
  + apply IHT.
  + intros t Ht.
    apply (PA_Implication_null_impl _ _ _ _ _ Ht IHT). 

- exists 0.
  exists (ord_succ (ord_succ (ord_succ (ord_succ (ord_succ (nat_ord 0)))))).
  apply I_UG; intros;
    unfold substitution;
    fold substitution;
    unfold eq_nat;
    apply I_UG; intros;
      unfold substitution;
      fold substitution;
      unfold eq_nat;
      apply I_UG; intros;
  apply I_equ_trans.

- exists 0.
  exists (ord_succ (ord_succ (ord_succ (nat_ord 0)))).
  apply I_UG; intros;
    unfold substitution;
    fold substitution;
    unfold eq_nat;
    apply I_UG; intros;
      unfold substitution;
      fold substitution;
      unfold eq_nat;
  apply I_equ_succ.

- exists 0.
  exists (ord_succ (nat_ord 0)).
  apply I_UG; intros;
    unfold substitution;
    fold substitution;
    unfold eq_nat;
  apply I_non_zero.

- exists 0.
  exists (ord_succ (ord_succ (ord_succ (nat_ord 0)))).
  apply I_UG; intros;
    unfold substitution;
    fold substitution;
    unfold eq_nat;
    apply I_UG; intros;
      unfold substitution;
      fold substitution;
      unfold eq_nat;
  apply I_succ_equ.

- exists 0.
  exists (ord_succ (nat_ord 0)).
  apply I_UG; intros;
    unfold substitution;
    fold substitution;
    unfold eq_nat;
  apply I_pl0.

- exists 0.
  exists (ord_succ (ord_succ (nat_ord 0))).
  apply I_UG; intros;
    unfold substitution;
    fold substitution;
    unfold eq_nat;
    apply I_UG; intros;
      unfold substitution;
      fold substitution;
      unfold eq_nat;
  apply I_plS.

- exists 0.
  exists (ord_succ (nat_ord 0)).
  apply I_UG; intros;
    unfold substitution;
    fold substitution;
    unfold eq_nat;
  apply I_ml0.

- exists 0.
  exists (ord_succ (ord_succ (nat_ord 0))).
  apply I_UG; intros;
    unfold substitution;
    fold substitution;
    unfold eq_nat;
    apply I_UG; intros;
      unfold substitution;
      fold substitution;
      unfold eq_nat;
  apply I_mlS.

- exists (num_conn A + 1).
  exists (ord_succ (ord_succ (cons (nat_ord 1) 0 Zero))).
  apply I_induct.
Qed.

Lemma PA_Base_closed_PA_omega :
  forall (A : formula),
    Peano_Theorems_Base A ->
      (forall (c : c_term), {d : nat & {alpha : ord & PA_omega_theorem (closure A c) d alpha}}).
Proof.
intros A T c.
destruct (PA_Base_equiv_PA_Implication _ T) as [d [alpha TI]].
exists d.
exists alpha.
apply (PA_closed_PA_omega _ _ _ TI c).
Qed.