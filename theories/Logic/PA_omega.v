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
Notation "b1 && b2" := (andb b1 b2).
Notation "b1 || b2" := (orb b1 b2).
Notation eq_nat := Nat.eqb.


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
  (g : forall (t : term), closed_t t = true ->
      PA_omega_theorem (substitution A n t) d alpha),
  PA_omega_theorem (univ n A) d (ord_succ alpha)

| w_rule2 : forall (A D : formula) (n : nat) (d : nat) (alpha : ord)
  (g : forall (t : term), closed_t t = true ->
    PA_omega_theorem (lor (substitution A n t) D) d alpha),
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
  PA_omega_theorem (univ n (atom (equ (var n) (var n)))) 0 (ord_succ Zero).
Proof.
intros.
apply w_rule1. intros. apply axiom. simpl. rewrite eq_nat_refl. unfold correct_a. unfold correctness. pose proof (closed_eval _ H). destruct (eval t). inversion H0. rewrite eq_nat_refl. auto.
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

Lemma ord_nf : forall (A : formula) (d : nat) (alpha : ord),
  PA_omega_theorem A d alpha -> nf alpha.
Proof.
intros. induction H; try apply ord_succ_nf; try apply ord_max_nf; auto.
- apply zero_nf.
- apply (H zero). auto.
- apply (H zero). auto.
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




Lemma closed_sub_theorem :
  forall (A : formula) (n d : nat) (t : term) (alpha : ord),
  closed A = true ->
  PA_omega_theorem A d alpha ->
  PA_omega_theorem (substitution A n t) d alpha.
Proof. intros. rewrite closed_subst_eq. apply H0. apply H. Qed.

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
  closed A = true -> PA_omega_theorem (lor (neg A) A) 0 (ord_succ (nat_ord ((num_conn A) + (num_conn A)))).

Definition P2 (A : formula) (n : nat) : Type :=
  num_conn A = n -> P1 A.

Definition P3 (n : nat) : Type :=
  forall (A : formula), P2 A n.

Lemma P3_0 : P3 0.
Proof.
unfold P3, P2. intros.
destruct A as [a | | | ].
- unfold P1. intros. apply LEM_atomic. auto.
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

(* The (strong) inductive step for LEM *)
(* *)
Lemma P3_inductive : forall n, (forall m, m <= n -> P3 m) -> P3 (S n).
Proof.
unfold P3,P2,P1. intros.
destruct A as [a | B | B C | m B].
- inversion H0.
- inversion H0. pose proof (H n (leq_refl n) B H3 H1).
  apply (ord_incr _ _ (ord_succ (ord_succ (nat_ord ((num_conn B) + (num_conn B)))))).
  + apply negation2. apply exchange1. apply H2.
  + apply ord_lt_succ. unfold num_conn. fold num_conn. repeat rewrite ord_succ_nat. apply nat_ord_lt. lia.
  + repeat apply ord_succ_nf. apply nf_nat.

- destruct (closed_lor _ _ H1) as [HB HC].
  destruct (num_conn_lor _ _ _ H0) as [HB' HC'].
  pose proof (H (num_conn B) HB' B (eq_refl (num_conn B)) HB).
  apply (weakening C _ _ _ HC) in H2. apply exchange1 in H2. apply associativity1 in H2.
  pose proof (H (num_conn C) HC' C (eq_refl (num_conn C)) HC).
  apply (weakening B _ _ _ HB) in H3. apply exchange1 in H3. apply exchange2 in H3. apply associativity1 in H3.
  pose proof (demorgan2 B C (lor B C) 0 0 _ _ H2 H3).
  case (num_conn C) eqn:X.
  + case (num_conn B) eqn:X1.
    * unfold num_conn in *. fold num_conn in *. rewrite plus_n_0 in *. rewrite <- plus_n_Sm in *. rewrite <- ord_succ_nat in *. rewrite plus_comm. rewrite <- plus_n_Sm in *. rewrite <- ord_succ_nat in *.
      repeat rewrite ord_max_succ_succ in H4. rewrite X,X1. repeat rewrite plus_n_0 in *. rewrite ord_max_lem2 in H4. apply H4. apply ord_ltb_irrefl.
    * unfold num_conn in *. fold num_conn in *. rewrite X,X1. rewrite plus_n_0 in *. repeat rewrite <- plus_n_Sm in *. repeat rewrite ord_succ_nat in *.
      repeat rewrite <- ord_add_nat in H4. rewrite <- ord_succ_nat in *. repeat rewrite ord_max_succ_succ in H4; try rewrite plus_n_0 in *; rewrite ord_max_lem2 in H4; try apply H4;
      repeat rewrite ord_succ_nat; try apply nf_nat; apply ltb_asymm; apply ord_lt_ltb; repeat rewrite <- ord_add_nat; apply nat_ord_lt; lia.
  + case (num_conn B) eqn:X1.
    * unfold num_conn in *. fold num_conn in *. rewrite X,X1. unfold add in *. fold add in *. repeat rewrite <- plus_n_Sm in *. repeat rewrite ord_succ_nat in *.
      repeat rewrite <- ord_add_nat in H4. rewrite <- ord_succ_nat in *. repeat rewrite ord_max_succ_succ in H4. rewrite ord_max_symm in H4. rewrite ord_max_lem2 in H4; try apply H4;
      repeat rewrite ord_succ_nat; try apply nf_nat; apply ltb_asymm; apply ord_lt_ltb; repeat rewrite <- ord_add_nat; apply nat_ord_lt; lia.
    * unfold num_conn in *; fold num_conn in *; rewrite X,X1 in *; unfold add in *; fold add in *; repeat rewrite <- plus_n_Sm in *; repeat rewrite ord_succ_nat in *;
      repeat rewrite <- ord_add_nat in *; repeat rewrite ord_max_succ_succ in H4; repeat rewrite <- plus_n_Sm in *; rewrite plus_assoc; rewrite plus_comm;
      rewrite plus_assoc; rewrite <- plus_n_Sm; rewrite (plus_comm n0 _); rewrite plus_comm; rewrite <- plus_n_Sm; rewrite plus_assoc; rewrite plus_assoc; rewrite <- (plus_assoc _ n0 n0); rewrite plus_n_Sm; rewrite plus_n_Sm; rewrite plus_comm; repeat rewrite plus_n_Sm in *. rewrite plus_comm in H4.
      case (ord_ltb (nat_ord (n1 + S (S (S (S n1))))) (nat_ord (n0 + S (S (S (S n0)))))) eqn:X2.
      --  rewrite ord_max_lem1 in H4; auto. apply (ord_incr _ _ _ _ H4).
          ++  repeat rewrite ord_succ_nat. apply nat_ord_lt. lia.
          ++  apply nf_nat.
          ++  rewrite plus_comm. auto.
      --  rewrite ord_max_lem2 in H4; auto. apply (ord_incr _ _ _ _ H4).
          ++  repeat rewrite ord_succ_nat. apply nat_ord_lt. lia.
          ++  apply nf_nat.
          ++  rewrite plus_comm. auto.
- inversion H0. apply exchange1.
  unfold num_conn. fold num_conn. rewrite <- plus_n_Sm. rewrite <- ord_succ_nat. rewrite plus_comm. rewrite <- plus_n_Sm. rewrite <- ord_succ_nat.
  apply w_rule2. intros k Hk. destruct H3. pose proof (H _ (leq_refl _) _ (num_conn_sub _ _ _) (closed_univ_sub _ _ H1 _ Hk)).
  rewrite num_conn_sub in H2. apply exchange1. apply (quantification2 _ _ _ k _ _ Hk H2).
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
  PA_omega_theorem (lor (neg A) A) 0 (ord_succ (nat_ord ((num_conn A)+(num_conn A)))).
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
  assert (ord_succ (ord_add Zero (nat_ord (num_conn (neg (substitution (atom a) n s))))) = ord_succ (ord_succ Zero)). auto.
  destruct H2. apply weakening; auto.
- apply exchange1. assert (ord_succ (ord_add Zero (nat_ord (num_conn (substitution (atom a) n t)))) = (ord_succ Zero)). auto.
  destruct H1. unfold substitution. apply weakening; auto.
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
                   0 (ord_succ (nat_ord ((num_conn A)+(num_conn A)))).

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
- unfold Q1. intros. apply LEM_term_atomic; auto.
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
  apply (ord_incr _ _ (ord_succ (nat_ord ((num_conn B)+(num_conn B))))).
  + apply (H n (leq_refl n) B H4 n0 t s); auto. apply equ_symm,H1.
  + repeat rewrite ord_succ_nat. apply nat_ord_lt. lia.
  + apply nf_nat.
- destruct (num_conn_lor _ _ _ H0) as [HB' HC'].
  destruct (correct_closed_t _ _ H1) as [Hs Ht].
  destruct (free_list_lor B C n0 H2) as [[HB | HB] [HC | HC]].
  + pose proof (H (num_conn B) HB' B (eq_refl (num_conn B)) _ _ _ H1 HB).
    apply (weakening (substitution C n0 t)) in H3. apply exchange1 in H3. apply associativity1 in H3.
    pose proof (H (num_conn C) HC' C (eq_refl (num_conn C)) _ _ _ H1 HC).
    apply (weakening (substitution B n0 t) _ _ _) in H4. apply exchange1 in H4. apply exchange2 in H4. apply associativity1 in H4.
    case (ord_eqb (ord_succ (ord_max (ord_succ (ord_succ (nat_ord (num_conn B + num_conn B)))) (ord_succ (ord_succ (nat_ord (num_conn C + num_conn C)))))) (ord_succ (nat_ord (num_conn (lor B C) + num_conn (lor B C))))) eqn:X.
    * apply ord_eqb_eq in X. destruct X. unfold substitution. fold substitution. apply (demorgan2 _ _ (lor (substitution B n0 t) (substitution C n0 t)) 0 0 _ _ H3 H4).
    * unfold substitution. fold substitution. apply (ord_incr _ _ _ _ (demorgan2 _ _ (lor (substitution B n0 t) (substitution C n0 t)) 0 0 _ _ H3 H4)).
      --  unfold num_conn. fold num_conn. repeat rewrite ord_max_succ_succ in *. rewrite <- plus_n_Sm. repeat rewrite <- ord_succ_nat. apply ord_lt_succ. apply ord_lt_succ. rewrite plus_n_Sm. rewrite (plus_comm _ (S _)). rewrite <- plus_assoc.
          rewrite (plus_comm (S _)). rewrite <- plus_n_Sm. rewrite <- ord_succ_nat. apply ord_lt_succ. repeat rewrite ord_succ_nat in *.
          rewrite ord_max_nat in *. apply nat_ord_lt. simpl in *. destruct (num_conn B); destruct (num_conn C).
          ++  simpl in X. inversion X.
          ++  rewrite <- plus_n_Sm in X. rewrite plus_n_0 in *. rewrite max_split1 in X. simpl in X. repeat rewrite <- plus_n_Sm in X. rewrite eq_nat_refl in X. inversion X. apply lt_nat_decid_conv. lia.
          ++  rewrite <- plus_n_Sm in X. rewrite plus_n_0 in *. rewrite max_split2 in X. simpl in X. repeat rewrite <- plus_n_Sm in X. repeat rewrite <- plus_n_O in X. rewrite eq_nat_refl in X. inversion X. apply lt_nat_decid_conv. lia.
          ++  lia.
      --  repeat apply ord_succ_nf. apply nf_nat.
    * apply closed_univ_sub; auto. apply free_list_closed. simpl. rewrite HB. simpl. rewrite eq_nat_refl. auto.
    * apply closed_univ_sub; auto. apply free_list_closed. simpl. rewrite HC. simpl. rewrite eq_nat_refl. auto.
  + pose proof (H (num_conn B) HB' B (eq_refl (num_conn B)) _ _ _ H1 HB).
    apply (weakening C _ _ _ HC) in H3. apply exchange1 in H3. apply associativity1 in H3.
    pose proof (LEM C HC).
    apply (weakening (substitution B n0 t) _ _ _) in H4. apply exchange1 in H4. apply exchange2 in H4. apply associativity1 in H4.
    unfold substitution. fold substitution. repeat rewrite (closed_subst_eq _ _ _ HC).
    case (ord_eqb (ord_succ (ord_max (ord_succ (ord_succ (nat_ord (num_conn B + num_conn B)))) (ord_succ (ord_succ (nat_ord (num_conn C + num_conn C)))))) (ord_succ (nat_ord (num_conn (lor B C) + num_conn (lor B C))))) eqn:X.
    * apply ord_eqb_eq in X. destruct X. apply (demorgan2 _ _ (lor (substitution B n0 t) C) 0 0 _ _ H3 H4).
    * unfold substitution. fold substitution. apply (ord_incr _ _ _ _ (demorgan2 _ _ (lor (substitution B n0 t) C) 0 0 _ _ H3 H4)).
      --  unfold num_conn. fold num_conn. repeat rewrite ord_max_succ_succ in *. rewrite <- plus_n_Sm. repeat rewrite <- ord_succ_nat. apply ord_lt_succ. apply ord_lt_succ. rewrite plus_n_Sm. rewrite (plus_comm _ (S _)). rewrite <- plus_assoc.
          rewrite (plus_comm (S _)). rewrite <- plus_n_Sm. rewrite <- ord_succ_nat. apply ord_lt_succ. repeat rewrite ord_succ_nat in *.
          rewrite ord_max_nat in *. apply nat_ord_lt. simpl in *. destruct (num_conn B); destruct (num_conn C).
          ++  simpl in X. inversion X.
          ++  rewrite <- plus_n_Sm in X. rewrite plus_n_0 in *. rewrite max_split1 in X. simpl in X. repeat rewrite <- plus_n_Sm in X. rewrite eq_nat_refl in X. inversion X. apply lt_nat_decid_conv. lia.
          ++  rewrite <- plus_n_Sm in X. rewrite plus_n_0 in *. rewrite max_split2 in X. simpl in X. repeat rewrite <- plus_n_Sm in X. repeat rewrite <- plus_n_O in X. rewrite eq_nat_refl in X. inversion X. apply lt_nat_decid_conv. lia.
          ++  lia.
      --  repeat apply ord_succ_nf. apply nf_nat. 
    * apply closed_univ_sub; auto. apply free_list_closed. simpl. rewrite HB. simpl. rewrite eq_nat_refl. auto.
  + pose proof (LEM B HB).
    apply (weakening (substitution C n0 t) _ _ _) in H3. apply exchange1 in H3. apply associativity1 in H3.  
    pose proof (H (num_conn C) HC' C (eq_refl (num_conn C)) _ _ _ H1 HC).
    apply (weakening B _ _ _ HB) in H4. apply exchange1 in H4. apply exchange2 in H4. apply associativity1 in H4.
    unfold substitution. fold substitution. repeat rewrite (closed_subst_eq _ _ _ HB).
    case (ord_eqb (ord_succ (ord_max (ord_succ (ord_succ (nat_ord (num_conn B + num_conn B)))) (ord_succ (ord_succ (nat_ord (num_conn C + num_conn C)))))) (ord_succ (nat_ord (num_conn (lor B C) + num_conn (lor B C))))) eqn:X.
    * apply ord_eqb_eq in X. destruct X. apply (demorgan2 _ _ (lor B (substitution C n0 t)) 0 0 _ _ H3 H4).
    * unfold substitution. fold substitution. apply (ord_incr _ _ _ _ (demorgan2 _ _ (lor B (substitution C n0 t)) 0 0 _ _ H3 H4)).
      --  unfold num_conn. fold num_conn. repeat rewrite ord_max_succ_succ in *. rewrite <- plus_n_Sm. repeat rewrite <- ord_succ_nat. apply ord_lt_succ. apply ord_lt_succ. rewrite plus_n_Sm. rewrite (plus_comm _ (S _)). rewrite <- plus_assoc.
          rewrite (plus_comm (S _)). rewrite <- plus_n_Sm. rewrite <- ord_succ_nat. apply ord_lt_succ. repeat rewrite ord_succ_nat in *.
          rewrite ord_max_nat in *. apply nat_ord_lt. simpl in *. destruct (num_conn B); destruct (num_conn C).
          ++  simpl in X. inversion X.
          ++  rewrite <- plus_n_Sm in X. rewrite plus_n_0 in *. rewrite max_split1 in X. simpl in X. repeat rewrite <- plus_n_Sm in X. rewrite eq_nat_refl in X. inversion X. apply lt_nat_decid_conv. lia.
          ++  rewrite <- plus_n_Sm in X. rewrite plus_n_0 in *. rewrite max_split2 in X. simpl in X. repeat rewrite <- plus_n_Sm in X. repeat rewrite <- plus_n_O in X. rewrite eq_nat_refl in X. inversion X. apply lt_nat_decid_conv. lia.
          ++  lia.
      --  repeat apply ord_succ_nf. apply nf_nat.
    * apply closed_univ_sub; auto. apply free_list_closed. simpl. rewrite HC. simpl. rewrite eq_nat_refl. auto.  
  + unfold substitution. fold substitution. repeat rewrite (closed_subst_eq _ _ _ HB). repeat rewrite (closed_subst_eq _ _ _ HC). apply LEM. simpl. rewrite HB,HC. auto.
- apply exchange1. inversion H0.
  unfold substitution. fold substitution. pose proof (univ_free_var _ _ _ H2) as Heq. rewrite Heq.
  unfold num_conn. fold num_conn. rewrite <- plus_n_Sm. rewrite plus_comm. rewrite <- plus_n_Sm. repeat rewrite <- ord_succ_nat.
  apply w_rule2. intros k Hk. apply exchange1. apply (quantification2 _ _ _ k _ _ Hk).
  destruct (correct_closed_t _ _ H1) as [Hs Ht].
  rewrite (substitution_order B m n0 s _ Hs Hk Heq).
  rewrite (substitution_order B m n0 t _ Ht Hk Heq).
  rewrite <- (num_conn_sub B m k).
  apply (H n (leq_refl n) (substitution B m k)); auto.
  + rewrite num_conn_sub. auto.
  + apply free_list_univ_sub; auto.
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
                   0 (ord_succ (nat_ord ((num_conn A)+(num_conn A)))).
Proof. apply Q1_lemma. Qed.

Lemma eval_correct : forall (s t : term),
   eval s > 0 -> eval s = eval t -> correct_a (equ s t) = true.
Proof.
intros s t.
unfold correct_a.
unfold correctness.
intros.
case (eval s) eqn:X; inversion H; case (eval t) eqn:X1; inversion H0.
- simpl. destruct H2,H3. auto.
- rewrite eq_nat_refl. auto. 
Qed.


(*
Definition C1 (A : formula) : Type :=
  closed A = true -> PA_omega_theorem A 0 (nat_ord (num_conn A)) + PA_omega_theorem (neg A) 0 (nat_ord (num_conn A)).

Definition C2 (A : formula) (n : nat) : Type :=
  num_conn A = n -> C1 A.

Definition C3 (n : nat) : Type :=
  forall (A : formula), C2 A n.

Lemma C3_0 : C3 0.
Proof.
unfold C3, C2. intros.
destruct A; inversion H.
unfold C1. intros. destruct (correctness_decid a); auto.
+ left. apply axiom. auto.
+ right. apply axiom. auto.
Qed.

(* Prove strong induction holds for P3, adapted from
pldev.blogspot.com/2012/02/proving-strong-induction-principle-for.html *)
Lemma C3_strongind_aux :
  C3 0 ->
  (forall n,
    ((forall m, m <= n -> C3 m) -> C3 (S n))) ->
  (forall n m, m <= n -> C3 m).
Proof.
induction n as [| n' IHn' ].
- intros m H1. assert (m = 0). { inversion H1. auto. } rewrite H. apply X.
- intros. assert ((m = S n') + (m <= n')). { apply leq_prop_sum. lia. }
  destruct H0 as [H1 | H1].
  + rewrite H1. apply X0. apply IHn'.
  + apply IHn'. apply H1.
Qed.

Lemma C3_strongind :
  C3 0 ->
  (forall n,
    ((forall m, m <= n -> C3 m) -> C3 (S n))) ->
  (forall n, C3 n).
Proof. intros. apply (C3_strongind_aux X X0 n n). auto. Qed.

(* The (strong) inductive step for LEM *)
(* *)
Lemma C3_inductive : forall n, (forall m, m <= n -> C3 m) -> C3 (S n).
Proof.
unfold C3,C2,C1. intros.
destruct A; inversion H0; unfold num_conn; fold num_conn.
- destruct (H _ (leq_refl n) _ H3 H1).
  + right. rewrite <- ord_succ_nat. apply negation1. auto.
  + left. apply (ord_incr _ _ (nat_ord (num_conn A))); auto. rewrite <- ord_succ_nat. apply ord_succ_monot. apply nf_nat.
- inversion H1. apply and_bool_prop in H4. destruct H4. assert (num_conn A1 <= n). lia. assert (num_conn A2 <= n). lia. destruct (H _ H5 _ (nat_eq_decid _ _ (eq_nat_refl _)) H2) as [HA1 | HA1].
  + left. destruct (num_conn A2).
    * rewrite plus_n_0. apply exchange1. rewrite <- ord_succ_nat. apply weakening; auto.
    * apply (ord_incr _ _ (nat_ord (S (num_conn A1)))); auto. apply exchange1. rewrite <- ord_succ_nat. apply weakening; auto. apply nat_ord_lt. lia. apply nf_nat.
  + destruct (H _ H6 _ (nat_eq_decid _ _ (eq_nat_refl _)) H4) as [HA2 | HA2].
    * left. destruct (num_conn A1).
      --  unfold "+". rewrite <- ord_succ_nat. apply weakening; auto.
      --  apply (ord_incr _ _ (nat_ord (S (num_conn A2)))); auto. rewrite <- ord_succ_nat. apply weakening; auto. apply nat_ord_lt. lia. apply nf_nat.
    * right. assert ((max 0 0) = 0). lia. destruct H7. case (num_conn A2) eqn:Y.
      --  assert (ord_succ (ord_max (nat_ord (num_conn A1)) (nat_ord 0)) = nat_ord (S (num_conn A1 + 0))). rewrite plus_n_0. simpl. destruct (num_conn A1); auto. destruct H7. apply demorgan1; auto.
      --  rewrite <- Y in *. case (num_conn A1) eqn:Y1.
          ++  assert (ord_succ (ord_max (nat_ord 0) (nat_ord (num_conn A2))) = nat_ord (S (0 + num_conn A2))). simpl. destruct (num_conn A2); auto. destruct H7. apply demorgan1; auto.
          ++  rewrite <- Y1 in *. apply (ord_incr _ _ (ord_succ (ord_max (nat_ord (num_conn A1)) (nat_ord (num_conn A2))))); auto. apply demorgan1; auto. case (ord_ltb (nat_ord (num_conn A1)) (nat_ord (num_conn A2))) eqn:X.
              **  rewrite ord_max_lem1; auto. rewrite ord_succ_nat. apply nat_ord_lt. lia.
              **  rewrite ord_max_lem2; auto. rewrite ord_succ_nat. apply nat_ord_lt. lia.
              **  apply nf_nat.
- assert ((forall (m : nat), (PA_omega_theorem (substitution A n0 (represent m))) 0 (nat_ord (num_conn A))) + {p : nat & PA_omega_theorem (neg (substitution A n0 (represent p))) 0 (nat_ord (num_conn A)) }).
  
  destruct H2 as [IHp | [t IHt]].
  + left. apply (ord_incr _ _ (cons (nat_ord (num_conn A)) 0 Zero)). apply w_rule1; auto. admit. admit.
  + right. rewrite <- ord_succ_nat. apply (quantification1 _ _ (represent t)); auto. apply repr_closed. 
Admitted.

Lemma C3_lemma : forall n, C3 n.
Proof. apply C3_strongind. apply C3_0. apply C3_inductive. Qed.

Lemma C2_lemma : forall (n : nat) (A : formula), C2 A n.
Proof. apply C3_lemma. Qed.

Lemma C1_lemma : forall (A : formula), C1 A.
Proof.
intros.
pose proof C2_lemma.
unfold C2 in X.
apply (X (num_conn A) A). auto.
Qed.

Lemma LEM_cases : forall (A : formula),
  closed A = true ->
  PA_omega_theorem A 0 (nat_ord (num_conn A)) + PA_omega_theorem (neg A) 0 (nat_ord (num_conn A)).
Proof. intros. apply (C1_lemma A H). Qed. 

*)