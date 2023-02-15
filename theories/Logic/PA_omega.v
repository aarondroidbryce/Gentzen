Add LoadPath "theories/Casteran" as Ordering.
Add LoadPath "theories/Maths" as Maths_Facts.
Add LoadPath "theories/Logic" as Systems.

Require Import Lia.
Require Import Nat.
Require Import Wellfounded.
Require Import Arith.

From Maths_Facts Require Import naturals.
From Maths_Facts Require Import lists.
From Maths_Facts Require Import ordinals.

From Systems Require Import definitions.
From Systems Require Import fol.

Definition PA_omega_axiom (A : formula) : bool :=
match A with
| atom a => correct_a a
| neg (atom a) => incorrect_a a
| _ => false
end.

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

| quantification1 : forall (A : formula) (n : nat) (c : c_term)
                           (d : nat) (alpha : ord),
    PA_omega_theorem (neg (substitution A n (projT1 c))) d alpha ->
    PA_omega_theorem (neg (univ n A)) d (ord_succ alpha)

| quantification2 : forall (A D : formula) (n : nat) (c : c_term)
                           (d : nat) (alpha : ord),
    PA_omega_theorem (lor (neg (substitution A n (projT1 c))) D) d alpha ->
    PA_omega_theorem (lor (neg (univ n A)) D) d (ord_succ alpha)

| w_rule1 : forall (A : formula) (n : nat) (d : nat) (alpha : ord)
  (g : forall (c : c_term), PA_omega_theorem (substitution A n (projT1 c)) d alpha),
  PA_omega_theorem (univ n A) d (ord_succ alpha)

| w_rule2 : forall (A D : formula) (n : nat) (d : nat) (alpha : ord)
  (g : forall (c : c_term), PA_omega_theorem (lor (substitution A n (projT1 c)) D) d alpha),
  PA_omega_theorem (lor (univ n A) D) d (ord_succ alpha)

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
                     (ord_succ (ord_succ (ord_max alpha1 alpha2)))

| cut3 : forall (C A D : formula) (d1 d2 : nat) (alpha1 alpha2 : ord),
    PA_omega_theorem (lor C A) d1 alpha1 ->
    PA_omega_theorem (lor (neg A) D) d2 alpha2 ->
    PA_omega_theorem (lor C D)
                     (max (max d1 d2) (num_conn (neg A)))
                     (ord_succ (ord_max alpha1 alpha2)).


Lemma associativity1 :
  forall (C A B : formula) (d : nat) (alpha : ord),
    PA_omega_theorem (lor (lor C A) B) d alpha ->
      PA_omega_theorem (lor C (lor A B)) d alpha.
Proof.
intros C A B d alpha T.
apply exchange1.
apply exchange2.
apply exchange3.
apply T.
Qed.

Lemma associativity2 :
  forall (C A B : formula) (d : nat) (alpha : ord),
    PA_omega_theorem (lor C (lor A B)) d alpha ->
      PA_omega_theorem (lor (lor C A) B) d alpha.
Proof.
intros C A B d alpha T.
apply exchange3.
apply exchange2.
apply exchange1.
apply T.
Qed.


Lemma deg_monot :
  forall (A : formula) (d d' : nat) (alpha : ord),
      d' >= d ->
          PA_omega_theorem A d alpha ->
              PA_omega_theorem A d' alpha.
Proof.
intros A d d' alpha IE T.
destruct (nat_ge_case_type _ _ IE) as [LT | EQ].

- apply (deg_incr A d d' _ T LT).

- destruct EQ.
  apply T.
Qed.

Lemma ord_nf :
    forall (A : formula) (d : nat) (alpha : ord),
        PA_omega_theorem A d alpha ->
            nf alpha.
Proof.
intros A d alpha T.
induction T;
repeat apply nf_nf_succ;
try apply nf_ord_max;
try apply zero_nf;
try apply IHT;
try apply IHT1;
try apply IHT2.

- apply n.

- apply (H czero).

- apply (H czero).
Qed.

Lemma ord_monot : forall (A : formula) (d : nat) (alpha beta : ord),
  (((ord_lt alpha beta) /\ (nf beta)) + (alpha = beta)) ->
    PA_omega_theorem A d alpha ->
      PA_omega_theorem A d beta.
Proof.
intros A d alpha beta [[I N] | I] T.
- apply (ord_incr A d alpha).
  + apply T.
  + apply I.
  + apply N.

- destruct I.
  apply T.
Qed.


Lemma closed_sub_theorem :
  forall (A : formula) (n d : nat) (t : term) (alpha : ord),
    closed A = true ->
      PA_omega_theorem A d alpha ->
        PA_omega_theorem (substitution A n t) d alpha.
Proof.
intros A n d t alpha CA T.
rewrite closed_subst_eq.
apply T.
apply CA.
Qed.

Lemma LEM_atomic :
  forall (a : atomic_formula),
    closed_a a = true ->
      PA_omega_theorem (lor (neg (atom a)) (atom a)) 0 (ord_succ Zero).
Proof.
intros a HC.
destruct (correctness_decid a HC) as [X1 | X1].
- apply weakening.
  + unfold closed.
    apply HC.
  + apply axiom.
    apply X1.

- apply exchange1.
  apply weakening.
  + unfold closed.
    apply HC.
  + apply axiom.
    apply X1.
Qed.

Definition P1 (A : formula) : Type :=
  closed A = true ->
    PA_omega_theorem (lor (neg A) A) 0 (ord_succ (nat_ord ((num_conn A) + (num_conn A)))).

Definition P2 (A : formula) (n : nat) : Type :=
  num_conn A = n -> P1 A.

Definition P3 (n : nat) : Type :=
  forall (A : formula), P2 A n.

Lemma P3_0 : P3 0.
Proof.
unfold P3, P2.
intros A NA.
destruct A as [a | | | ];
inversion NA.
unfold P1.
intros HC.
apply LEM_atomic.
apply HC.
Qed.

Lemma P3_strongind_aux :
  P3 0 ->
    (forall n, ((forall m, m <= n -> P3 m) -> P3 (S n))) ->
      (forall n m, m <= n -> P3 m).
Proof.
intros Ind0 Ind.
induction n as [ | n' IHn' ];
intros m IE.
- destruct m.
  + apply Ind0.
  + exfalso.
    inversion IE.
- destruct (nat_ge_case_type _ _ IE) as [LT | EQ].
  + apply IHn'.
    lia.
  + destruct EQ.
    apply (Ind _ IHn').
Qed.

Lemma P3_strongind :
  P3 0 ->
    (forall n, ((forall m, m <= n -> P3 m) -> P3 (S n))) ->
      (forall n, P3 n).
Proof.
intros Ind0 Ind n.
apply (P3_strongind_aux Ind0 Ind n n).
reflexivity.
Qed.

Lemma P3_inductive :
  forall n, (forall m, m <= n -> P3 m) ->
    P3 (S n).
Proof.
unfold P3,P2,P1. intros n Ind A NA CA.
destruct A as [a | B | B C | m B].

- inversion NA.

- inversion NA as [NA1].
  apply (ord_incr _ _ (ord_succ (ord_succ (nat_ord ((num_conn B) + (num_conn B)))))).
  + apply negation2.
    apply exchange1.
    apply (Ind _ (nat_le_refl _) _ NA1 CA).
  + apply ord_lt_succ.
    unfold num_conn. fold num_conn.
    repeat rewrite ord_succ_nat.
    apply nat_ord_lt.
    rewrite <- plus_n_Sm.
    unfold lt.
    reflexivity.
  + apply nf_nf_succ.
    apply nf_nat.

- destruct (closed_lor _ _ CA) as [CB CC].
  destruct (num_conn_lor _ _ _ NA) as [NB NC].
  pose proof (Ind (num_conn B) NB B (eq_refl (num_conn B)) CB) as T1.
  apply (weakening C _ _ _ CC) in T1.
  apply exchange1 in T1.
  apply associativity1 in T1.
  pose proof (Ind (num_conn C) NC C (eq_refl (num_conn C)) CC) as T2.
  apply (weakening B _ _ _ CB) in T2.
  apply exchange1 in T2.
  apply exchange2 in T2.
  apply associativity1 in T2.
  pose proof (demorgan2 B C (lor B C) 0 0 _ _ T1 T2) as T3.
  case (num_conn C) eqn:X1;
  case (num_conn B) eqn:X2;
  unfold num_conn in *; fold num_conn in *;
  rewrite X1,X2.
  + unfold ord_max in T3.
    rewrite ord_ltb_irrefl in T3.
    apply T3.
  + rewrite <- plus_n_O in *.
    repeat rewrite <- plus_n_Sm in *.
    repeat rewrite ord_succ_nat in *.
    rewrite ord_max_ltb_not_l in T3.
    * apply T3.
    * apply ord_ltb_asymm.
      apply ord_lt_ltb.
      apply nat_ord_lt.
      lia.
  + unfold add in *. fold add in *.
    repeat rewrite <- plus_n_Sm in *.
    repeat rewrite ord_succ_nat in *.
    rewrite ord_max_symm in T3.
    rewrite ord_max_ltb_not_l in T3.
    * apply T3.
    * apply ord_ltb_asymm.
      apply ord_lt_ltb.
      apply nat_ord_lt.
      lia.
    
  + unfold add in *; fold add in *.
    repeat rewrite <- plus_n_Sm in *.
    repeat rewrite ord_succ_nat in *.
    rewrite plus_assoc.
    rewrite plus_comm.
    rewrite plus_assoc.
    rewrite <- plus_n_Sm.
    rewrite (plus_comm n0).
    rewrite plus_comm.
    rewrite <- plus_n_Sm.
    rewrite plus_assoc.
    rewrite plus_assoc.
    rewrite <- (plus_assoc _ n0 n0).
    rewrite plus_n_Sm.
    rewrite plus_n_Sm.
    rewrite plus_comm.
    repeat rewrite plus_n_Sm in *.
    case (ord_ltb (nat_ord (n1 + S (S (S (S n1))))) (nat_ord (n0 + S (S (S (S n0)))))) eqn:X3.
    * rewrite (ord_max_ltb_is_r _ _ X3) in T3 .
      apply (ord_incr _ _ _ _ T3).
      --  repeat rewrite ord_succ_nat.
          apply nat_ord_lt.
          lia.
      --  apply nf_nat.
    * rewrite (ord_max_ltb_not_l _ _ X3) in T3. 
      apply (ord_incr _ _ _ _ T3).
      --  repeat rewrite ord_succ_nat.
          apply nat_ord_lt.
          lia.
      --  apply nf_nat.
      
- inversion NA as [NB].
  apply exchange1.
  unfold num_conn. fold num_conn.
  rewrite <- plus_n_Sm.
  unfold "+". fold add.
  repeat rewrite <- ord_succ_nat.
  apply w_rule2.
  intros c.
  destruct NB.
  rewrite <- (num_conn_sub _ m (projT1 c)).
  apply exchange1.
  apply (quantification2 _ _ _ c).
  apply (Ind _ (nat_le_refl _) _ (num_conn_sub _ _ _) (closed_univ_sub _ _ CA _ (projT2 c))).
Qed.

Lemma P3_lemma :
  forall n, P3 n.
Proof.
apply P3_strongind.
apply P3_0.
apply P3_inductive.
Qed.

Lemma P2_lemma :
  forall (n : nat) (A : formula), P2 A n.
Proof.
apply P3_lemma.
Qed.

Lemma P1_lemma :
  forall (A : formula), P1 A.
Proof.
intros.
pose proof P2_lemma as Lemma.
unfold P2 in Lemma.
apply (Lemma (num_conn A) A).
reflexivity.
Qed.

Lemma LEM :
  forall (A : formula),
    closed A = true ->
      PA_omega_theorem (lor (neg A) A) 0 (ord_succ (nat_ord ((num_conn A) + (num_conn A)))).
Proof.
intros A CA.
apply (P1_lemma A CA).
Qed.



Lemma LEM_term_atomic' :
  forall (s t : term) (a : atomic_formula) (n : nat),
    correct_a (equ s t) = true ->
      PA_omega_axiom (substitution (atom a) n s) = true ->
        PA_omega_axiom (substitution (atom a) n t) = true.
Proof.
intros s t a n COR T.
unfold PA_omega_axiom in *.
unfold substitution in *.
unfold correct_a.
unfold correct_a in T.
case (correctness (substitution_a a n s)) eqn:COR1;
inversion T.
rewrite (eval_eq_subst_cor_eq _ s).
- reflexivity.
- apply (equ_cor_eval_eq _ _ COR).
- apply COR1. 
Qed.

Lemma LEM_term_atomic :
  forall (a : atomic_formula) (n : nat) (s t : term),
    correct_a (equ s t) = true ->
      free_list_a a = [n] ->
        PA_omega_theorem (lor (neg (atom (substitution_a a n s)))
                              (atom (substitution_a a n t)))
                          0 (ord_succ Zero).
Proof.
intros a n s t COR FREE.
destruct (correctness_decid (substitution_a a n s)) as [COR1 | COR1].
- apply one_var_free_lemma_a.
  + apply eval_closed.
    destruct (correct_eval s t COR) as [E1 E2].
    apply E1.
  + apply FREE.
- apply weakening.
  + unfold closed.
    apply (correct_closed _ COR1).
  + apply axiom.
    apply (LEM_term_atomic' _ _ _ _ COR COR1).
- apply exchange1.
  apply weakening.
  + unfold closed.
    apply (incorrect_subst_closed _ _ s).
    * apply eval_closed.
      destruct (correct_eval s t COR) as [E1 E2].
      apply E2.
    * apply COR1.
  + apply axiom.
    unfold PA_omega_axiom.
    apply COR1.
Qed.


Definition Q1 (A : formula) : Type :=
  forall (n : nat) (s t : term),
    correct_a (equ s t) = true ->
      free_list A = [n] ->
        PA_omega_theorem (lor (neg (substitution A n s)) (substitution A n t))
                         0 (ord_succ (nat_ord ((num_conn A)+(num_conn A)))).

Definition Q2 (A : formula) (n : nat) : Type := num_conn A = n -> Q1 A.

Definition Q3 (m : nat) : Type := forall (A : formula), Q2 A m.

Lemma Q3_strongind_aux :
  Q3 0 ->
    (forall n, ((forall m, m <= n -> Q3 m) -> Q3 (S n))) ->
        (forall n m, m <= n -> Q3 m).
Proof.
intros Ind0 Ind.
induction n as [| n' IHn' ].

- intros m I. 
  assert (0 = m) as Z.
  { inversion I. reflexivity. }
  destruct Z.
  apply Ind0.

- intros m I.
  destruct (nat_ge_case_type _ _ I) as [I1 | I1].
  + apply IHn'.
    lia.
+ destruct I1.
  apply Ind.
  apply IHn'.
Qed.

Lemma Q3_strongind :
  Q3 0 ->
    (forall n, ((forall m, m <= n -> Q3 m) -> Q3 (S n))) ->
      (forall n, Q3 n).
Proof.
intros Ind0 Ind n.
apply (Q3_strongind_aux Ind0 Ind n n).
reflexivity.
Qed.

Lemma Q3_0 : Q3 0.
Proof.
unfold Q3, Q2. intros A NA.
destruct A as [a | | | ];
inversion NA.
unfold Q1.
intros n s t COR LIST.
apply (LEM_term_atomic _ _ _ _ COR LIST).
Qed.

Lemma Q3_inductive :
  forall n, (forall m, m <= n -> Q3 m) -> Q3 (S n).
Proof.
unfold Q3,Q2,Q1. intros n Ind A NA i s t COR LIST.
destruct A as [| B | B C | m B].

- inversion NA.

- inversion NA as [NB].
  apply negation2.
  fold substitution.
  apply exchange1.
  unfold num_conn. fold num_conn.
  apply (ord_incr _ _ (ord_succ (nat_ord ((num_conn B)+(num_conn B))))).
  + apply (Ind _ (nat_le_refl _) _ NB _ _ _ (correct_atom_symm _ _ COR) LIST).
  + repeat rewrite ord_succ_nat.
    apply nat_ord_lt.
    lia.
  + apply nf_nat.

- destruct (num_conn_lor _ _ _ NA) as [NB NC].
  destruct (correct_closed_t _ _ COR) as [CS CT].
  pose proof (subst_remove (lor B C) i _ CT) as LISTSUB.
  rewrite LIST in LISTSUB.
  unfold remove in LISTSUB.
  rewrite nat_eqb_refl in LISTSUB.
  unfold substitution in LISTSUB. fold substitution in LISTSUB.
  apply free_list_closed in LISTSUB.
  unfold closed in LISTSUB. fold closed in LISTSUB.
  apply and_bool_prop in LISTSUB.
  destruct LISTSUB as [CB CC].
  case (ord_eqb (ord_succ (ord_max (ord_succ (ord_succ (nat_ord (num_conn B + num_conn B)))) (ord_succ (ord_succ (nat_ord (num_conn C + num_conn C)))))) (ord_succ (nat_ord (num_conn (lor B C) + num_conn (lor B C))))) eqn:X1.
  + apply ord_eqb_eq in X1.
    destruct X1.
    unfold substitution. fold substitution.
    apply (demorgan2 _ _ (lor (substitution B i t) (substitution C i t)) 0 0).
    * apply associativity1.
      apply exchange1.
      apply weakening.
      --  apply CC.
      --  destruct (free_list_lor B C i LIST) as [[LISTB | LISTB] [LISTC | LISTC]].
          ++  apply (Ind (num_conn B) NB B (eq_refl (num_conn B)) _ _ _ COR LISTB).
          ++  apply (Ind (num_conn B) NB B (eq_refl (num_conn B)) _ _ _ COR LISTB).
          ++  unfold substitution. fold substitution.
              repeat rewrite (closed_subst_eq _ _ _ LISTB).
              apply (LEM B LISTB).
          ++  unfold substitution. fold substitution.
              repeat rewrite (closed_subst_eq _ _ _ LISTB).
              apply (LEM B LISTB).
    * apply associativity1.
      apply exchange2.
      apply exchange1.
      apply weakening.
      --  apply CB.
      --  destruct (free_list_lor B C i LIST) as [[LISTB | LISTB] [LISTC | LISTC]].
          ++  apply (Ind (num_conn C) NC C (eq_refl (num_conn C)) _ _ _ COR LISTC).
          ++  unfold substitution. fold substitution.
              repeat rewrite (closed_subst_eq _ _ _ LISTC).
              apply (LEM C LISTC).
          ++  apply (Ind (num_conn C) NC C (eq_refl (num_conn C)) _ _ _ COR LISTC).
          ++  unfold substitution. fold substitution.
              repeat rewrite (closed_subst_eq _ _ _ LISTC).
              apply (LEM C LISTC).

  + unfold substitution. fold substitution.
    refine (ord_incr _ _ _ _ (demorgan2 _ _ (lor (substitution B i t) (substitution C i t)) 0 0 _ _ _ _) _ _).
    * apply associativity1.
      apply exchange1.
      apply weakening.
      --  apply CC.
      --  destruct (free_list_lor B C i LIST) as [[LISTB | LISTB] [LISTC | LISTC]].
          ++  apply (Ind (num_conn B) NB B (eq_refl (num_conn B)) _ _ _ COR LISTB).
          ++  apply (Ind (num_conn B) NB B (eq_refl (num_conn B)) _ _ _ COR LISTB).
          ++  unfold substitution. fold substitution.
              repeat rewrite (closed_subst_eq _ _ _ LISTB).
              apply (LEM B LISTB).
          ++  unfold substitution. fold substitution.
              repeat rewrite (closed_subst_eq _ _ _ LISTB).
              apply (LEM B LISTB).
    * apply associativity1.
      apply exchange2.
      apply exchange1.
      apply weakening.
      --  apply CB.
      --  destruct (free_list_lor B C i LIST) as [[LISTB | LISTB] [LISTC | LISTC]].
          ++  apply (Ind (num_conn C) NC C (eq_refl (num_conn C)) _ _ _ COR LISTC).
          ++  unfold substitution. fold substitution.
              repeat rewrite (closed_subst_eq _ _ _ LISTC).
              apply (LEM C LISTC).
          ++  apply (Ind (num_conn C) NC C (eq_refl (num_conn C)) _ _ _ COR LISTC).
          ++  unfold substitution. fold substitution.
              repeat rewrite (closed_subst_eq _ _ _ LISTC).
              apply (LEM C LISTC).
    * rewrite <- ord_max_succ_succ in *.
      repeat rewrite ord_succ_nat in *.
      rewrite ord_max_nat in *.
      apply nat_ord_lt.
      unfold num_conn in *. fold num_conn in *.
      unfold max in *. fold max in *.
      rewrite <- plus_n_Sm in *.
      unfold nat_ord in X1.
      unfold ord_eqb in X1.
      destruct (num_conn B);
      destruct (num_conn C);
      unfold add in *; fold add in *;
      unfold max in *; fold max in *;
      try rewrite <- plus_n_O in *;
      try rewrite nat_eqb_refl in X1; inversion X1.
      lia.
    * rewrite ord_succ_nat.
      apply nf_nat.
  
- apply exchange1.
  inversion NA as [NB].
  unfold substitution. fold substitution.
  pose proof (univ_free_var _ _ _ LIST) as Heq.
  rewrite Heq.
  unfold num_conn. fold num_conn.
  rewrite <- plus_n_Sm.
  rewrite plus_comm.
  rewrite <- plus_n_Sm.
  repeat rewrite <- ord_succ_nat.
  apply w_rule2.
  intros c.
  apply exchange1.
  apply (quantification2 _ _ _ c).
  destruct (correct_closed_t _ _ COR) as [CS CT].
  rewrite (substitution_order B m i s _ CS (projT2 c) Heq).
  rewrite (substitution_order B m i t _ CT (projT2 c) Heq).
  rewrite <- (num_conn_sub B m (projT1 c)).
  apply (Ind n (nat_le_refl n) (substitution B m (projT1 c))).
  + rewrite num_conn_sub.
    apply NB.
  + apply COR.
  + apply free_list_univ_sub.
    * destruct c as [c CC].
      unfold projT1.
      apply CC.
    * apply LIST.
Qed.

Lemma Q3_lemma : forall n, Q3 n.
Proof.
apply Q3_strongind.
apply Q3_0.
apply Q3_inductive.
Qed.

Lemma Q2_lemma : forall (n : nat) (A : formula), Q2 A n.
Proof.
apply Q3_lemma.
Qed.

Lemma Q1_lemma : forall (A : formula), Q1 A.
Proof.
intros.
pose proof (Q2_lemma) as LEMMA.
unfold Q2 in LEMMA.
apply (LEMMA (num_conn A) A).
reflexivity.
Qed.

Lemma LEM_term :
  forall (A : formula) (n : nat) (s t : term),
    correct_a (equ s t) = true ->
      free_list A = [n] ->
        PA_omega_theorem (lor (neg (substitution A n s)) (substitution A n t))
                         0 (ord_succ (nat_ord ((num_conn A)+(num_conn A)))).
Proof.
apply Q1_lemma.
Qed.

