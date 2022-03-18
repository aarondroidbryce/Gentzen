Add LoadPath "theories/Maths" as Maths_Facts.
Add LoadPath "theories/Logic" as Systems.

From Maths_Facts Require Import naturals.
From Maths_Facts Require Import lists.
From Systems Require Import definitions.
Require Import Lia.

Notation "b1 && b2" := (andb b1 b2).
Notation "b1 || b2" := (orb b1 b2).
Notation eq_nat := Nat.eqb.

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
| lor B D => remove_dups (concat (free_list B) (free_list D))
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
| lor B D => closed B && closed D
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
| lor B D => lor (substitution B n t) (substitution D n t)
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