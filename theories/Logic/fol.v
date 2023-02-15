Add LoadPath "theories/Maths" as Maths_Facts.
Add LoadPath "theories/Logic" as Systems.

From Maths_Facts Require Import naturals.
From Maths_Facts Require Import lists.
From Systems Require Import definitions.

Require Import Lia.
Require Import Nat.

Open Scope bool.

(*Language*)
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

(*Logical Connectives*)
Fixpoint num_conn (a : formula) : nat :=
match a with
| atom a' => 0
| neg a' => S (num_conn a')
| lor a1 a2 => S ((num_conn a1) + (num_conn a2))
| univ n a' => S (num_conn a')
end.

(*Boolean Equality*)
Fixpoint term_eqb (s t : term) : bool :=
match s, t with
| zero, zero => true
| succ s', succ t' => term_eqb s' t'
| plus s1 s2, plus t1 t2 => term_eqb s1 t1 && term_eqb s2 t2
| times s1 s2, times t1 t2 => term_eqb s1 t1 && term_eqb s2 t2
| var m, var n => nat_eqb m n
| _, _ => false
end.

Definition atom_eqb (a b : atomic_formula) : bool :=
match a, b with
| equ s1 s2, equ t1 t2 => term_eqb s1 t1 && term_eqb s2 t2
end.

Fixpoint form_eqb (a b : formula) : bool :=
match a, b with
| atom a', atom b' => atom_eqb a' b'
| neg a', neg b' => form_eqb a' b'
| lor a1 a2, lor b1 b2 => form_eqb a1 b1 && form_eqb a2 b2
| univ m a', univ n b' => nat_eqb m n && form_eqb a' b'
| _, _ => false
end.

(*Given some term t, returns t+1 if the formula is closed, 0 otherwise*)
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

(*Natural Numbers as terms*)
Fixpoint represent (n : nat) : term :=
match n with
| O => zero
| S n' => succ (represent n')
end.

(*Decidability Prediate*)
Inductive ternary : Type :=
| correct : ternary
| incorrect : ternary
| undefined : ternary.

Definition correctness (a : atomic_formula) : ternary :=
match a with
| equ t1 t2 =>
    (match eval t1, eval t2 with
    | S n, S m =>
        (match nat_eqb (eval t1) (eval t2) with
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

(*Closedness*)
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
    | m :: l => nat_eqb m n && list_eqb l []
    end)
  end)
end.

(*Closed Terms*)
Definition c_term : Type := {t : term & closed_t t = true}.

Definition closing (t : term) (Ht : closed_t t = true) : c_term. exists t. exact Ht. Defined.

Definition value (c : c_term) : nat := eval (projT1 c) - 1.

(*Substitution of free occurrences of x_n with t in a formula f*)
Fixpoint substitution_t (T : term) (n : nat) (t : term) : term :=
match T with
| zero => T
| succ T1 => succ (substitution_t T1 n t)
| plus T1 T2 => plus (substitution_t T1 n t) (substitution_t T2 n t)
| times T1 T2 => times (substitution_t T1 n t) (substitution_t T2 n t)
| var m =>
    (match nat_eqb m n with
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
    (match nat_eqb m n with
    | true => A
    | false => univ m (substitution B n t)
    end)
end.

Fixpoint closure_type_t (t : term) (c : c_term) (L : list nat) : term :=
match L with
| [] => t
| x :: L' => closure_type_t (substitution_t t x (projT1 c)) c L'
end.

Definition closure_t (t : term) (c : c_term) := closure_type_t t c (free_list_t t).

Fixpoint closure_type (A : formula) (c : c_term) (L : list nat) : formula :=
match L with
| [] => A
| x :: L' => closure_type (substitution A x (projT1 c)) c L'
end.

Definition closure (A : formula) (c : c_term) := closure_type A c (free_list A).

(*Equality Lemmas*)
Lemma term_eqb_refl :
    forall (t : term),
        term_eqb t t = true.
Proof.
induction t;
unfold term_eqb; fold term_eqb;
try rewrite IHt;
try rewrite IHt1,IHt2;
try reflexivity.
apply nat_eqb_refl.
Qed.

Lemma atom_eqb_refl :
    forall (a : atomic_formula),
        atom_eqb a a = true.
Proof.
destruct a as [t1 t2].
unfold atom_eqb.
rewrite term_eqb_refl.
apply term_eqb_refl.
Qed.

Lemma form_eqb_refl :
    forall (f : formula),
        form_eqb f f = true.
Proof.
induction f as [a | f IH | f1 IH1 f2 IH2 | n f IH].
- apply atom_eqb_refl.
- apply IH.
- unfold form_eqb; fold form_eqb.
  rewrite IH1.
  apply IH2.
- unfold form_eqb; fold form_eqb.
  rewrite nat_eqb_refl.
  apply IH.
Qed.

Lemma term_beq_eq :
    forall (s t : term),
        term_eqb s t = true ->
            s = t.
Proof.
induction s;
intros t EQ;
destruct t;
inversion EQ as [EQ'];
try destruct (and_bool_prop _ _ EQ') as [EQ1 EQ2];
try rewrite (IHs _ EQ');
try rewrite (IHs1 _ EQ1),(IHs2 _ EQ2);
try rewrite (nat_eqb_eq _ _ EQ');
reflexivity.
Qed.

Lemma atom_beq_eq :
    forall (a b : atomic_formula),
        atom_eqb a b = true ->
            a = b.
Proof.
intros a b EQ.
destruct a as [al ar],b as [bl br].
destruct (and_bool_prop _ _ EQ) as [EQ1 EQ2].
rewrite (term_beq_eq _ _ EQ1),(term_beq_eq _ _ EQ2).
reflexivity.
Qed.

Lemma form_eqb_eq :
    forall (A B : formula),
        form_eqb A B = true ->
            A = B.
Proof.
induction A;
intros B EQ;
destruct B;
inversion EQ as [EQ'];
try destruct (and_bool_prop _ _ EQ') as [EQ1 EQ2].
- rewrite (atom_beq_eq _ _ EQ').
  reflexivity.
- rewrite (IHA _ EQ').
  reflexivity.
- rewrite (IHA1 _ EQ1),(IHA2 _ EQ2).
  reflexivity.
- rewrite (nat_eqb_eq _ _ EQ1),(IHA _ EQ2).
  reflexivity.
Qed.

(*Properties of the evaluation function*)
Lemma eval_succ_lemma :
    forall (t : term),
        eval (succ t) > 0 ->
            eval t > 0.
Proof.
intros t Et.
unfold eval in Et;
fold eval in Et.
destruct (eval t).
- inversion Et.
- lia.
Qed.

Lemma eval_plus_lemma :
    forall (t1 t2 : term),
        eval (plus t1 t2) > 0 ->
            eval t1 > 0 /\ eval t2 > 0.
Proof.
intros t1 t2 Et.
unfold eval in Et;
fold eval in Et.
destruct (eval t1);
destruct (eval t2);
inversion Et as [];
split;
lia.
Qed.

Lemma eval_times_lemma :
    forall (t1 t2 : term),
        eval (times t1 t2) > 0 ->
            eval t1 > 0 /\ eval t2 > 0.
Proof.
intros t1 t2 Et.
unfold eval in Et;
fold eval in Et.
destruct (eval t1);
destruct (eval t2);
inversion Et as [];
split;
lia.
Qed.

Lemma eval_closed :
    forall (t : term),
        eval t > 0 ->
            closed_t t = true.
Proof.
intros t Et.
induction t.
- reflexivity.
- apply IHt.
  apply eval_succ_lemma.
  apply Et.
- destruct (eval_plus_lemma _ _ Et) as [Et1 Et2].
  unfold closed_t;
  fold closed_t.
  rewrite (IHt1 Et1).
  rewrite (IHt2 Et2).
  reflexivity.
- destruct (eval_times_lemma _ _ Et) as [Et1 Et2].
  unfold closed_t;
  fold closed_t.
  rewrite (IHt1 Et1).
  rewrite (IHt2 Et2).
  reflexivity.
- inversion Et.
Qed.

Lemma closed_eval :
    forall (t : term),
        closed_t t = true ->
            eval t > 0.
Proof.
intros t Ct.
induction t.
- unfold eval, gt, lt.
  reflexivity.
- apply IHt in Ct.
  unfold eval; fold eval.
  destruct (eval t).
  + inversion Ct.
  + lia.
- apply and_bool_prop in Ct.
  destruct Ct as [Ct1 Ct2].
  apply IHt1 in Ct1.
  apply IHt2 in Ct2.
  unfold eval; fold eval.
  destruct (eval t1);
  destruct (eval t2).
  + inversion Ct1.
  + inversion Ct1.
  + inversion Ct2.
  + lia.
- apply and_bool_prop in Ct.
  destruct Ct as [Ct1 Ct2].
  apply IHt1 in Ct1.
  apply IHt2 in Ct2.
  unfold eval; fold eval.
  destruct (eval t1);
  destruct (eval t2).
  + inversion Ct1.
  + inversion Ct1.
  + inversion Ct2.
  + lia.
- inversion Ct.
Qed.

Lemma eval_eq_eval_subst_eq :
  forall (T s t : term) (n : nat),
      eval s = eval t ->
          eval (substitution_t T n s) = eval (substitution_t T n t).
Proof.
intros T s t n EQ.
induction T;
unfold substitution_t; fold substitution_t;
unfold eval; fold eval.
- reflexivity.
- rewrite IHT.
  reflexivity. 
- rewrite IHT1,IHT2.
  reflexivity.
- rewrite IHT1,IHT2.
  reflexivity.
- case (nat_eqb n0 n).
  + apply EQ.
  + reflexivity.
Qed.

Lemma eval_eq_subst_cor_eq :
  forall (a : atomic_formula) (s t : term) (n : nat),
      eval s = eval t ->
          correctness (substitution_a a n s) = correct ->
              correctness (substitution_a a n t) = correct.
Proof.
intros [t1 t2] s t n EQ COR.
unfold substitution_a, correctness in *.
destruct (eval_eq_eval_subst_eq t1 s t n EQ).
destruct (eval_eq_eval_subst_eq t2 s t n EQ).
apply COR.
Qed.

Lemma equ_cor_eval_eq :
  forall (s t : term),
      correct_a (equ s t) = true ->
          eval s = eval t.
Proof.
intros s t COR.
unfold correct_a, correctness in *.
destruct (eval s);
destruct (eval t);
inversion COR.
case (nat_eqb (S n) (S n0)) eqn:EQ.
- apply (nat_eqb_eq _ _ EQ).
- inversion COR.
Qed.

(*Lemmas about representing natural numbers*)
Lemma succ_represent_comm :
    forall (n : nat),
        succ (represent n) = represent (S n).
Proof.
intros n.
unfold represent.
reflexivity.
Qed.

Lemma eval_represent_non_zero :
    forall (n : nat),
        eval (represent n) > 0.
Proof.
induction n.
- unfold represent,eval,gt,lt.
  reflexivity.
- unfold represent,eval,gt,lt.
  fold eval represent.
  destruct (eval (represent n)).
  + inversion IHn.
  + lia.
Qed.

Lemma eval_represent_is_succ :
    forall (n : nat),
        eval (represent n) = (S n).
Proof.
induction n.
- reflexivity.
- unfold eval, represent.
  fold eval represent.
  destruct (eval (represent n)).
  + inversion IHn.
  + rewrite IHn.
    reflexivity.
Qed.

Lemma represent_closed :
    forall (n : nat),
        closed_t (represent n) = true.
Proof.
intros n.
apply eval_closed, eval_represent_non_zero.
Qed.

Lemma represent_eval :
    forall (t : term),
        closed_t t = true ->
            eval (represent ((eval t) - 1)) = (eval t).
Proof.
intros t Ct.
destruct t;
unfold eval, represent;
fold eval represent;
unfold closed_t in Ct;
fold closed_t in Ct;
try destruct (and_bool_prop _ _ Ct) as [Ct1 Ct2].
- reflexivity.
- pose proof (closed_eval _ Ct) as Et.
  destruct (eval t).
  + inversion Et.
  + apply eval_represent_is_succ.
- pose proof (closed_eval _ Ct1) as Et1.
  pose proof (closed_eval _ Ct2) as Et2.
  destruct (eval t1).
  + inversion Et1.
  + destruct (eval t2).
    * inversion Et2.
    * unfold sub; fold sub.
      rewrite minus_n_0.
      apply eval_represent_is_succ.
- pose proof (closed_eval _ Ct1) as Et1.
  pose proof (closed_eval _ Ct2) as Et2.
  destruct (eval t1).
  + inversion Et1.
  + destruct (eval t2).
    * inversion Et2.
    * unfold sub; fold sub.
      rewrite minus_n_0.
      apply eval_represent_is_succ.
- inversion Ct. 
Qed.

(*Results about lists of free variables*)
Lemma free_list_remove_dups_idem_t :
    forall (t : term),
        free_list_t t = remove_dups (free_list_t t).
Proof.
induction t;
unfold free_list_t;
fold free_list_t;
try rewrite remove_dups_twice;
try reflexivity.
apply IHt.
Qed.

Lemma free_list_remove_dups_idem_a :
    forall (a : atomic_formula),
        free_list_a a = remove_dups (free_list_a a).
Proof.
intros [t1 t2].
unfold free_list_a.
rewrite remove_dups_twice.
reflexivity.
Qed.

Lemma free_list_remove_dups_idem :
    forall (A : formula),
        free_list A = remove_dups (free_list A).
Proof.
induction A.
- apply free_list_remove_dups_idem_a.
- apply IHA.
- unfold free_list; fold free_list.
  rewrite remove_dups_twice.
  reflexivity.
- unfold free_list; fold free_list.
  rewrite IHA at 1.
  apply remove_dups_order.
Qed.

Lemma free_list_univ_empty_cases :
    forall (A : formula) (n : nat),
        free_list (univ n A) = [] ->
            free_list A = [n] \/ free_list A = [].
Proof.
intros A n FREE.
induction A;
unfold free_list in *; fold free_list in *.
- rewrite free_list_remove_dups_idem_a in FREE.
  rewrite free_list_remove_dups_idem_a.
  apply remove_n_dups_empty.
  apply FREE.
- apply IHA.
  apply FREE.
- apply remove_n_dups_empty.
  apply FREE.
- rewrite free_list_remove_dups_idem.
  rewrite remove_dups_order.
  apply remove_n_dups_empty.
  rewrite <- remove_dups_order.
  rewrite <- free_list_remove_dups_idem.
  apply FREE.
Qed.

(*Closed and Free List interrelations*)
Lemma free_list_closed_t :
    forall (t : term),
        free_list_t t = [] ->
            closed_t t = true.
Proof.
intros t FREE.
induction t;
unfold closed_t; fold closed_t;
unfold free_list_t in FREE; fold free_list_t in FREE.
- reflexivity.
- apply IHt.
  apply FREE.
- apply remove_dups_empty in FREE.
  destruct (empty_concat_split_empty _ _ _ FREE) as [L1 L2].
  rewrite (IHt1 L1).
  apply (IHt2 L2).
- apply remove_dups_empty in FREE.
  destruct (empty_concat_split_empty _ _ _ FREE) as [L1 L2].
  rewrite (IHt1 L1).
  apply (IHt2 L2).
- inversion FREE.
Qed.

Lemma free_list_closed_a :
    forall (a : atomic_formula),
        free_list_a a = [] ->
            closed_a a = true.
Proof.
intros [t1 t2] FREE.
unfold closed_a.
apply remove_dups_empty in FREE.
destruct (empty_concat_split_empty _ _ _ FREE) as [L1 L2].
rewrite (free_list_closed_t _ L1).
apply (free_list_closed_t _ L2).
Qed.

Lemma free_list_closed :
    forall (A : formula),
        free_list A = [] ->
            closed A = true.
Proof.
intros A FREE.
induction A;
unfold closed; fold closed;
unfold free_list in FREE; fold free_list in FREE.
- apply free_list_closed_a, FREE.
- apply IHA, FREE.
- destruct (empty_concat_split_empty _ _ _ (remove_dups_empty _ FREE)) as [L1 L2].
  rewrite (IHA1 L1).
  apply (IHA2 L2).
- rewrite free_list_remove_dups_idem in FREE.
  destruct (remove_n_dups_empty _ _ FREE) as [Ln | LE].
  + rewrite <- free_list_remove_dups_idem in Ln.
    destruct (closed A) eqn:CA.
    * reflexivity.
    * rewrite Ln.
      rewrite nat_eqb_refl.
      apply list_eqb_refl.
  + rewrite IHA.
    * reflexivity.
    * rewrite free_list_remove_dups_idem.
      apply LE.
Qed.

Lemma closed_free_list_t :
    forall (t : term),
        closed_t t = true ->
            free_list_t t = [].
Proof.
intros t Ct.
induction t;
unfold closed_t in Ct; fold closed_t in Ct;
unfold free_list_t; fold free_list_t;
try destruct (and_bool_prop _ _ Ct) as [Ct1 Ct2].
- reflexivity.
- apply (IHt Ct).
- rewrite (IHt1 Ct1).
  rewrite (IHt2 Ct2).
  reflexivity.
- rewrite (IHt1 Ct1).
  rewrite (IHt2 Ct2).
  reflexivity.
- inversion Ct.
Qed.

Lemma closed_free_list_a :
    forall (a : atomic_formula),
        closed_a a = true ->
            free_list_a a = [].
Proof.
intros [t1 t2] Ca.
unfold free_list_a.
destruct (and_bool_prop _ _ Ca) as [Ct1 Ct2].
rewrite (closed_free_list_t _ Ct1), (closed_free_list_t _ Ct2).
reflexivity.
Qed.

Lemma closed_free_list :
    forall (A : formula),
        closed A = true ->
            free_list A = [].
Proof.
intros A CA.
induction A;
unfold closed in CA; fold closed in CA;
unfold free_list; fold free_list.
- apply closed_free_list_a, CA.
- apply IHA, CA.
- destruct (and_bool_prop _ _ CA) as [CA1 CA2].
  rewrite (IHA1 CA1), (IHA2 CA2).
  reflexivity.
- destruct (closed A).
  + rewrite (IHA CA).
    reflexivity.
  + destruct (free_list A).
    * inversion CA.
    * destruct (and_bool_prop _ _ CA) as [EQ1 EQ2].
      apply list_eqb_eq in EQ2.
      rewrite EQ2.
      unfold remove.
      rewrite EQ1.
      reflexivity.
Qed.

Lemma closed_univ :
    forall (A : formula) (n : nat),
        closed (univ n A) = true ->
            closed A = true \/ free_list A = [n].
Proof.
intros A n CuA.
destruct (free_list_univ_empty_cases _ _ (closed_free_list _ CuA)) as [Ln | LE].
- right.
  apply Ln.
- left.
  apply free_list_closed, LE.
Qed.

(*Correctness Lemmas*)
Lemma correctness_decid :
    forall (a : atomic_formula),
        closed_a a = true ->
            sum (correct_a a = true) (incorrect_a a = true).
Proof.
intros [t1 t2] Ca.
destruct (and_bool_prop _ _ Ca) as [Ct1 Ct2].
apply closed_eval in Ct1.
apply closed_eval in Ct2.
unfold correct_a.
unfold incorrect_a.
unfold correctness.
destruct (eval t1).
- exfalso.
  inversion Ct1.
- destruct (eval t2).
  + exfalso.
    inversion Ct2. 
  + destruct (nat_eqb (S n) (S n0)).
    * left.
      reflexivity.
    * right.
      reflexivity.
Qed.

Lemma correct_atom_symm :
    forall (s t : term),
        correct_a (equ s t) = true ->
            correct_a (equ t s) = true.
Proof.
intros s t COR.
unfold correct_a in *.
unfold correctness in *.
destruct (eval s);
destruct (eval t);
inversion COR as [COR1].
rewrite nat_eqb_symm.
unfold nat_eqb. fold nat_eqb.
repeat rewrite COR1.
reflexivity.
Qed.

(*Substitution Lemmas*)
Lemma subst_remove_t : forall (T t : term) (n : nat),
  closed_t t = true ->
  free_list_t (substitution_t T n t) = remove n (free_list_t T).
Proof.
intros. induction T; auto.
- simpl. rewrite IHT1, IHT2.
  rewrite remove_dups_order. rewrite remove_concat. auto.
- simpl. rewrite IHT1, IHT2.
  rewrite remove_dups_order. rewrite remove_concat. auto.
- simpl. case_eq (nat_eqb n0 n); intros; auto.
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
- destruct (nat_eqb n0 n) eqn:Hn.
  + rewrite (nat_eqb_eq _ _ Hn). rewrite remove_idem. auto.
  + simpl. rewrite IHA. apply remove_comm.
Qed.

Lemma one_var_free_lemma_a : forall (a : atomic_formula) (n : nat) (t : term),
  closed_t t = true ->
  free_list_a a = [n] ->
  closed_a (substitution_a a n t) = true.
Proof.
intros.
apply free_list_closed_a. 
rewrite (subst_remove_a _ _ _ H).
rewrite H0. simpl. rewrite nat_eqb_refl. auto.
Qed.

Lemma one_var_free_lemma : forall (A : formula) (n : nat) (t : term),
  closed_t t = true ->
  free_list A = [n] ->
  closed (substitution A n t) = true.
Proof.
intros.
apply free_list_closed.
rewrite (subst_remove _ _ _ H).
rewrite H0. simpl. rewrite nat_eqb_refl. auto.
Qed.

Lemma subst_one_var_free : forall (A : formula) (n : nat) (t : term),
  closed_t t = true ->
  closed (substitution A n t) = true ->
  free_list A = [n] \/ free_list A = [].
Proof.
intros.
pose proof (subst_remove A n t H).
apply closed_free_list in H0. rewrite H0 in H1. symmetry in H1.
rewrite free_list_remove_dups_idem in H1. apply remove_n_dups_empty in H1.
destruct H1.
- left. rewrite free_list_remove_dups_idem. apply H1.
- right. rewrite free_list_remove_dups_idem. apply H1.
Qed.

Lemma closed_lor : forall (B D : formula),
  closed (lor B D) = true -> closed B = true /\ closed D = true.
Proof.
intros. simpl in H. split.
- case_eq (closed B); case_eq (closed D); intros; auto;
  rewrite H0 in H; rewrite H1 in H; inversion H.
- case_eq (closed B); case_eq (closed D); intros; auto;
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
- simpl in H. simpl. case_eq (nat_eqb n0 n); intros.
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
- simpl. case_eq (nat_eqb n0 n); intros; auto.
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

Lemma closed_subst_closed_t : forall (s t : term) (n : nat), closed_t s = true -> closed_t (substitution_t s n t) = true.
Proof.
intros s t n CS.
induction s;
unfold substitution_t; fold substitution_t.
3, 4: unfold closed_t in *; fold closed_t in *;
      destruct (and_bool_prop _ _ CS) as [CS1 CS2];
      rewrite (IHs1 CS1);
      rewrite (IHs2 CS2);
      unfold "&&";
      reflexivity.
- apply CS.
- unfold closed_t in *; fold closed_t in *.
  apply (IHs CS).
- unfold closed_t in CS; fold closed_t in CS.
  inversion CS.
Qed.

Lemma closed_subst_closed_a : forall (a : atomic_formula) (n : nat) (t : term), closed_a a = true -> closed_a (substitution_a a n t) = true.
Proof.
intros a n t CA.
destruct a.
unfold closed_a in *.
unfold substitution_a.
destruct (and_bool_prop _ _ CA) as [CA1 CA2].
rewrite (closed_subst_closed_t _ _ _ CA1).
rewrite (closed_subst_closed_t _ _ _ CA2).
unfold "&&".
reflexivity.
Qed.

Lemma closed_subst_closed : forall (A : formula) (n : nat) (t : term), closed A = true -> closed (substitution A n t) = true.
Proof.
intros A n t CA.
rewrite (closed_subst_eq _ _ _ CA).
apply CA.
Qed.

Lemma closed_univ_sub : forall (B : formula) (n : nat),
  closed (univ n B) = true ->
  (forall (t : term), closed_t t = true -> closed (substitution B n t) = true).
Proof.
intros.
destruct (closed_univ B n H).
- rewrite (closed_subst_eq _ _ _ H1). apply H1.
- apply free_list_closed. rewrite (subst_remove B n t H0).
  rewrite H1. simpl. rewrite nat_eqb_refl. auto.
Qed.


Lemma closed_univ_sub_repr : forall (B : formula) (n : nat),
  closed (univ n B) = true ->
  (forall (m : nat), closed (substitution B n (represent m)) = true).
Proof.
intros.
apply closed_univ_sub.
- apply H.
- apply eval_closed, eval_represent_non_zero.
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
  + left. rewrite free_list_remove_dups_idem. apply HB'.
  + right. apply free_list_closed, HB'.
- destruct (remove_dups_repeated_element _ _ HC) as [HC' | HC'].
  + left. rewrite free_list_remove_dups_idem. apply HC'.
  + right. apply free_list_closed, HC'.
Qed.

Lemma substitution_order_t : forall (T : term) (m n : nat) (s t : term),
  closed_t s = true ->
  closed_t t = true ->
  nat_eqb m n = false ->
  substitution_t (substitution_t T n s) m t =
  substitution_t (substitution_t T m t) n s.
Proof.
intros T m n s t Hs Ht Hmn. induction T; auto; simpl.
- rewrite IHT. auto.
- rewrite IHT1, IHT2. auto.
- rewrite IHT1, IHT2. auto.
- destruct (nat_eqb n0 n) eqn:Hn.
  + rewrite <- (nat_eqb_eq _ _ Hn) in Hmn. rewrite nat_eqb_symm.
    rewrite Hmn.
    simpl. rewrite Hn. apply closed_subst_eq_t, Hs.
  + destruct (nat_eqb n0 m) eqn:Hm; simpl; rewrite Hm.
    * symmetry. apply closed_subst_eq_t, Ht.
    * rewrite Hn. auto.
Qed.

Lemma substitution_order_a :
  forall (a : atomic_formula) (m n : nat) (s t : term),
  closed_t s = true ->
  closed_t t = true ->
  nat_eqb m n = false ->
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
  nat_eqb m n = false ->
  substitution (substitution B n s) m t =
  substitution (substitution B m t) n s.
Proof.
intros B m n s t Hs Ht Hmn. induction B; simpl.
- rewrite (substitution_order_a _ _ _ _ _ Hs Ht Hmn). auto.
- rewrite IHB. auto.
- rewrite IHB1, IHB2. auto.
- destruct (nat_eqb n0 n) eqn:Hn.
  + apply nat_eqb_eq in Hn. rewrite Hn.
    rewrite nat_eqb_symm. rewrite Hmn. simpl.
    rewrite nat_eqb_symm. rewrite Hmn. rewrite nat_eqb_refl. auto.
  + destruct (nat_eqb n0 m) eqn:Hm; simpl; rewrite Hm, Hn; auto.
    rewrite IHB. auto.
Qed.

Lemma univ_free_var : forall (B : formula) (m n : nat),
  free_list (univ m B) = [n] -> nat_eqb m n = false.
Proof.
intros. simpl in H.
destruct (nat_eqb m n) eqn:Hm; auto.
apply nat_eqb_eq in Hm. rewrite Hm in H.
pose proof (remove_idem (free_list B) n).
rewrite H in H0. simpl in H0. rewrite nat_eqb_refl in H0. inversion H0.
Qed.

Lemma free_list_univ_sub :
  forall (B : formula) (m : nat) (t : term) (l : list nat),
  closed_t t = true ->
  free_list (univ m B) = l ->
  free_list (substitution B m t) = l.
Proof. intros. rewrite (subst_remove _ _ _ H). apply H0. Qed.

Lemma num_conn_sub : forall (B : formula) (m : nat) (t : term),
  num_conn (substitution B m t) = num_conn B.
Proof.
intros.
induction B; auto; simpl.
- rewrite IHB. auto.
- rewrite IHB1, IHB2. auto.
- destruct (nat_eqb n m).
  + auto.
  + simpl. rewrite IHB. auto.
Qed.

Lemma num_conn_lor : forall (B C : formula) (n : nat),
  num_conn (lor B C) = S n -> num_conn B <= n /\ num_conn C <= n.
Proof. intros. simpl in H. lia. Qed.

Lemma free_list_sub_sef_t_eq : forall (n : nat) (t : term), free_list_t t = [n] -> free_list_t (substitution_t t n (succ (var n))) = [n].
Proof.
intros n t. induction t; intros.
- inversion H.
- simpl in *. apply IHt. auto.
- simpl in *. case (free_list_t t1) eqn:X.
  + rewrite (closed_subst_eq_t _ _ _ (free_list_closed_t _ X)). rewrite X. simpl. case (free_list_t t2) eqn:X1. inversion H. unfold concat in H. destruct X1. rewrite <- free_list_remove_dups_idem_t in H. rewrite <- free_list_remove_dups_idem_t. rewrite IHt2; auto.
  + case (free_list_t t2) eqn:X1.
    * rewrite (closed_subst_eq_t _ _ _ (free_list_closed_t _ X1)). rewrite X1. destruct X. rewrite concat_empty_right in *. rewrite <- free_list_remove_dups_idem_t in H. rewrite <- free_list_remove_dups_idem_t. rewrite IHt1; auto.
    * destruct X,X1. destruct (remove_dup_single_left _ _ _ H); destruct (remove_dup_single_right _ _ _ H). 
      --  rewrite <- free_list_remove_dups_idem_t in H0,H1. rewrite IHt1,IHt2; auto. simpl. rewrite nat_eqb_refl. auto.
      --  rewrite <- free_list_remove_dups_idem_t in H0,H1. rewrite IHt1; auto. rewrite (closed_subst_eq_t _ _ _ (free_list_closed_t _ H1)). rewrite H1. auto.
      --  rewrite <- free_list_remove_dups_idem_t in H0,H1. rewrite IHt2; auto. rewrite (closed_subst_eq_t _ _ _ (free_list_closed_t _ H0)). rewrite H0. auto.
      --  rewrite <- free_list_remove_dups_idem_t in H0,H1. rewrite H0,H1 in H. inversion H.
- simpl in *. case (free_list_t t1) eqn:X.
  + rewrite (closed_subst_eq_t _ _ _ (free_list_closed_t _ X)). rewrite X. simpl. case (free_list_t t2) eqn:X1. inversion H. unfold concat in H. destruct X1. rewrite <- free_list_remove_dups_idem_t in H. rewrite <- free_list_remove_dups_idem_t. rewrite IHt2; auto.
  + case (free_list_t t2) eqn:X1.
    * rewrite (closed_subst_eq_t _ _ _ (free_list_closed_t _ X1)). rewrite X1. destruct X. rewrite concat_empty_right in *. rewrite <- free_list_remove_dups_idem_t in H. rewrite <- free_list_remove_dups_idem_t. rewrite IHt1; auto.
    * destruct X,X1. destruct (remove_dup_single_left _ _ _ H); destruct (remove_dup_single_right _ _ _ H). 
      --  rewrite <- free_list_remove_dups_idem_t in H0,H1. rewrite IHt1,IHt2; auto. simpl. rewrite nat_eqb_refl. auto.
      --  rewrite <- free_list_remove_dups_idem_t in H0,H1. rewrite IHt1; auto. rewrite (closed_subst_eq_t _ _ _ (free_list_closed_t _ H1)). rewrite H1. auto.
      --  rewrite <- free_list_remove_dups_idem_t in H0,H1. rewrite IHt2; auto. rewrite (closed_subst_eq_t _ _ _ (free_list_closed_t _ H0)). rewrite H0. auto.
      --  rewrite <- free_list_remove_dups_idem_t in H0,H1. rewrite H0,H1 in H. inversion H.
- simpl in *. inversion H. destruct H1. rewrite nat_eqb_refl. auto.
Qed.

Lemma free_list_sub_sef_t : forall (n : nat) (t : term), member n (free_list_t t) = true -> free_list_t (substitution_t t n (succ (var n))) = free_list_t t.
Proof.
intros n t. induction t; intros.
- inversion H.
- simpl in *. apply IHt. auto.
- simpl in *. case (free_list_t t1) eqn:X.
  + rewrite (closed_subst_eq_t _ _ _ (free_list_closed_t _ X)). rewrite X. simpl. case (free_list_t t2) eqn:X1. inversion H. unfold concat in H. destruct X1. rewrite <- free_list_remove_dups_idem_t in H. rewrite <- free_list_remove_dups_idem_t. rewrite IHt2; auto. rewrite <- free_list_remove_dups_idem_t. auto.
  + case (free_list_t t2) eqn:X1.
    * rewrite (closed_subst_eq_t _ _ _ (free_list_closed_t _ X1)). rewrite X1. destruct X. rewrite concat_empty_right in *. rewrite <- free_list_remove_dups_idem_t in H. rewrite <- free_list_remove_dups_idem_t. rewrite IHt1; auto. rewrite concat_empty_right. rewrite <- free_list_remove_dups_idem_t. auto.
    * destruct X,X1. case (member n (free_list_t t1)) eqn:X; destruct (member n (free_list_t t2)) eqn:X1. 
      --  rewrite IHt1,IHt2; auto.
      --  rewrite IHt1; auto. rewrite closed_subst_eq_aux_t; auto.
      --  rewrite IHt2; auto. rewrite closed_subst_eq_aux_t; auto.
      --  apply member_remove_dups_true in H. destruct (member_concat' _ _ _ H). rewrite H0 in X. inversion X. rewrite H0 in X1. inversion X1.
- simpl in *. case (free_list_t t1) eqn:X.
  + rewrite (closed_subst_eq_t _ _ _ (free_list_closed_t _ X)). rewrite X. simpl. case (free_list_t t2) eqn:X1. inversion H. unfold concat in H. destruct X1. rewrite <- free_list_remove_dups_idem_t in H. rewrite <- free_list_remove_dups_idem_t. rewrite IHt2; auto. rewrite <- free_list_remove_dups_idem_t. auto.
  + case (free_list_t t2) eqn:X1.
    * rewrite (closed_subst_eq_t _ _ _ (free_list_closed_t _ X1)). rewrite X1. destruct X. rewrite concat_empty_right in *. rewrite <- free_list_remove_dups_idem_t in H. rewrite <- free_list_remove_dups_idem_t. rewrite IHt1; auto. rewrite concat_empty_right. rewrite <- free_list_remove_dups_idem_t. auto.
    * destruct X,X1. case (member n (free_list_t t1)) eqn:X; destruct (member n (free_list_t t2)) eqn:X1. 
      --  rewrite IHt1,IHt2; auto.
      --  rewrite IHt1; auto. rewrite closed_subst_eq_aux_t; auto.
      --  rewrite IHt2; auto. rewrite closed_subst_eq_aux_t; auto.
      --  apply member_remove_dups_true in H. destruct (member_concat' _ _ _ H). rewrite H0 in X. inversion X. rewrite H0 in X1. inversion X1.
- simpl in *. case (nat_eqb n0 n) eqn:X. apply nat_eqb_eq in X. destruct X. auto. inversion H.
Qed.

Lemma free_list_sub_self : forall (A : formula) (n : nat) (t : term), member n (free_list A) = true -> free_list (substitution A n (succ (var n))) = free_list A.
Proof.
intros. induction A.
- destruct a. simpl in *. case (free_list_t t0) eqn:X.
  + rewrite (closed_subst_eq_t _ _ _ (free_list_closed_t _ X)). rewrite X. case (free_list_t t1) eqn:X1. inversion H. unfold concat in H. destruct X1. rewrite <- free_list_remove_dups_idem_t in H. simpl. repeat rewrite <- free_list_remove_dups_idem_t. apply free_list_sub_sef_t. auto.
  + case (free_list_t t1) eqn:X1.
    * rewrite (closed_subst_eq_t _ _ _ (free_list_closed_t _ X1)). rewrite X1. destruct X. rewrite concat_empty_right in *. rewrite <- free_list_remove_dups_idem_t in H. rewrite concat_empty_right. repeat rewrite <- free_list_remove_dups_idem_t. apply free_list_sub_sef_t. auto.
    * destruct X,X1. case (member n (free_list_t t0)) eqn:X; destruct (member n (free_list_t t1)) eqn:X1. 
      --  rewrite free_list_sub_sef_t,free_list_sub_sef_t; auto.
      --  rewrite free_list_sub_sef_t; auto. rewrite closed_subst_eq_aux_t; auto.
      --  rewrite (free_list_sub_sef_t _ _ X1); auto. rewrite closed_subst_eq_aux_t; auto.
      --  apply member_remove_dups_true in H. destruct (member_concat' _ _ _ H). rewrite H0 in X. inversion X. rewrite H0 in X1. inversion X1.
- simpl. apply IHA. auto.
- simpl in *. case (free_list A1) eqn:X.
+ rewrite (closed_subst_eq _ _ _ (free_list_closed _ X)). rewrite X. case (free_list A2) eqn:X1. inversion H. unfold concat in H. destruct X1. rewrite <- free_list_remove_dups_idem in H. simpl. repeat rewrite <- free_list_remove_dups_idem. apply IHA2. auto.
+ case (free_list A2) eqn:X1.
  * rewrite (closed_subst_eq _ _ _ (free_list_closed _ X1)). rewrite X1. destruct X. rewrite concat_empty_right in *. rewrite <- free_list_remove_dups_idem in H. rewrite concat_empty_right. repeat rewrite <- free_list_remove_dups_idem. apply IHA1. auto.
  * destruct X,X1. case (member n (free_list A1)) eqn:X; destruct (member n (free_list A2)) eqn:X1. 
      --  rewrite IHA1,IHA2; auto.
      --  rewrite IHA1; auto. rewrite closed_subst_eq_aux; auto.
      --  rewrite IHA2; auto. rewrite closed_subst_eq_aux; auto.
      --  apply member_remove_dups_true in H. destruct (member_concat' _ _ _ H). rewrite H0 in X. inversion X. rewrite H0 in X1. inversion X1.
- simpl in *. case (nat_eqb n0 n) eqn:X. apply nat_eqb_eq in X. destruct X. rewrite remove_not_member in H. inversion H. simpl. rewrite (IHA (member_remove_true _ _ _ H)). auto.
Qed.

Lemma free_list_sub_self_eq : forall (A : formula) (n : nat) (t : term), free_list A = [n] -> free_list (substitution A n (succ (var n))) = [n].
Proof.
intros. induction A.
- destruct a. simpl in *. case (free_list_t t0) eqn:X.
  + rewrite (closed_subst_eq_t _ _ _ (free_list_closed_t _ X)). rewrite X. case (free_list_t t1) eqn:X1. inversion H. unfold concat in H. destruct X1. rewrite <- free_list_remove_dups_idem_t in H. simpl. rewrite <- free_list_remove_dups_idem_t. apply free_list_sub_sef_t_eq. auto.
  + case (free_list_t t1) eqn:X1.
    * rewrite (closed_subst_eq_t _ _ _ (free_list_closed_t _ X1)). rewrite X1. destruct X. rewrite concat_empty_right in *. rewrite <- free_list_remove_dups_idem_t in H. rewrite <- free_list_remove_dups_idem_t. apply free_list_sub_sef_t_eq. auto.
    * destruct X,X1. destruct (remove_dup_single_left _ _ _ H); destruct (remove_dup_single_right _ _ _ H). 
      --  rewrite <- free_list_remove_dups_idem_t in H0,H1. repeat rewrite free_list_sub_sef_t_eq; auto. simpl. rewrite nat_eqb_refl. auto.
      --  rewrite <- free_list_remove_dups_idem_t in H0,H1. rewrite free_list_sub_sef_t_eq; auto. rewrite (closed_subst_eq_t _ _ _ (free_list_closed_t _ H1)). rewrite H1. auto.
      --  rewrite <- free_list_remove_dups_idem_t in H0,H1. rewrite (free_list_sub_sef_t_eq _ t1); auto. rewrite (closed_subst_eq_t _ _ _ (free_list_closed_t _ H0)). rewrite H0. auto.
      --  rewrite <- free_list_remove_dups_idem_t in H0,H1. rewrite H0,H1 in H. inversion H.
- simpl. apply IHA. auto.
- simpl in *. case (free_list A1) eqn:X.
+ rewrite (closed_subst_eq _ _ _ (free_list_closed _ X)). rewrite X. case (free_list A2) eqn:X1. inversion H. unfold concat in H. destruct X1. rewrite <- free_list_remove_dups_idem in H. simpl. rewrite <- free_list_remove_dups_idem. apply IHA2. auto.
+ case (free_list A2) eqn:X1.
  * rewrite (closed_subst_eq _ _ _ (free_list_closed _ X1)). rewrite X1. destruct X. rewrite concat_empty_right in *. rewrite <- free_list_remove_dups_idem in H. rewrite <- free_list_remove_dups_idem. apply IHA1. auto.
  * destruct X,X1. destruct (remove_dup_single_left _ _ _ H); destruct (remove_dup_single_right _ _ _ H). 
    --  rewrite <- free_list_remove_dups_idem in H0,H1. rewrite IHA1,IHA2; auto. simpl. rewrite nat_eqb_refl. auto.
    --  rewrite <- free_list_remove_dups_idem in H0,H1. rewrite IHA1; auto. rewrite (closed_subst_eq _ _ _ (free_list_closed _ H1)). rewrite H1. auto.
    --  rewrite <- free_list_remove_dups_idem in H0,H1. rewrite IHA2; auto. rewrite (closed_subst_eq _ _ _ (free_list_closed _ H0)). rewrite H0. auto.
    --  rewrite <- free_list_remove_dups_idem in H0,H1. rewrite H0,H1 in H. inversion H.
- simpl in *. pose proof (univ_free_var _ _ _ H). rewrite H0. simpl. rewrite free_list_sub_self; auto. apply (member_remove_true _ _ n0). rewrite H. simpl. rewrite nat_eqb_refl. auto.
Qed.

Lemma sub_succ_self_t : forall (t s : term) (n : nat), substitution_t (substitution_t t n (succ (var n))) n s = substitution_t t n (succ s).
Proof.
intros t. induction t; intros.
- auto.
- simpl. rewrite IHt. auto.
- simpl. rewrite IHt1. rewrite IHt2. auto.
- simpl. rewrite IHt1. rewrite IHt2. auto.
- simpl. case (nat_eqb n n0) eqn:X. apply nat_eqb_eq in X. destruct X. simpl. rewrite nat_eqb_refl. auto. simpl. rewrite X. auto.
Qed.

Lemma sub_succ_self : forall (A : formula) (n : nat) (t : term), substitution (substitution A n (succ (var n))) n t = substitution A n (succ t).
Proof.
intros A. induction A; intros.
- destruct a. simpl. rewrite sub_succ_self_t. rewrite sub_succ_self_t. auto.
- simpl. rewrite IHA. auto.
- simpl. rewrite IHA1. rewrite IHA2. auto.
- simpl. case (nat_eqb n n0) eqn:X. apply nat_eqb_eq in X. destruct X. simpl. rewrite nat_eqb_refl. auto. simpl. rewrite X. rewrite IHA. auto.
Qed.



Lemma closure_closed' : forall (L : list nat) (A : formula) (c : c_term), free_list A = L -> closed (closure_type A c L) = true.
Proof.
intros L. induction L; intros A [c Hc] FREE.
- simpl. apply free_list_closed. auto.
- simpl. rewrite IHL; auto. rewrite subst_remove; auto. rewrite FREE. apply remove_dups_idem_remove_triv. destruct FREE. symmetry. apply free_list_remove_dups_idem.
Qed.

Lemma closure_closed : forall (A : formula) (c : c_term), closed (closure A c) = true.
Proof.
intros. apply closure_closed'; auto.
Qed.

Lemma closure_type_lor : forall (L : list nat) (A B : formula) (c : c_term), closure_type (lor A B) c L = lor (closure_type A c L) (closure_type B c L).
Proof.
induction L; intros; simpl; auto.
Qed.

Lemma closure_closed_id : forall (A : formula) (c : c_term), closed A = true -> closure A c = A.
intros. unfold closure. rewrite closed_free_list; auto.
Qed.

Lemma closure_closed_list_id : forall (L : list nat) (A : formula) (c : c_term), closed A = true -> closure_type A c L = A.
intros L. induction L; auto. intros. simpl. rewrite closed_subst_eq; auto. 
Qed.

Lemma closure_type_symm : forall (A : formula) (c : c_term) (n m : nat) (L : list nat), closure_type A c (n :: m :: L) = closure_type A c (m :: n :: L).
Proof.
intros A [c Hc] n m L. case (nat_eqb m n) eqn:X.
- apply nat_eqb_eq in X. destruct X. auto.
- simpl. rewrite substitution_order; auto.
Qed.

Lemma closure_type_concat_symm : forall (L1 L2 : list nat) (A : formula) (c : c_term), closure_type A c (concat L1 L2) = closure_type A c (concat L2 L1).
Proof.
induction L1.
- intros. simpl. rewrite concat_empty_right. auto.
- intros L2. simpl. induction L2; intros A [c Hc].
  + simpl. rewrite concat_empty_right. auto.
  + rewrite IHL1; auto. simpl. rewrite <- IHL2; auto. rewrite IHL1; auto. case (nat_eqb x0 x) eqn:X.
   * apply nat_eqb_eq in X. destruct X. auto.
   * rewrite substitution_order; auto.
Qed.

Lemma closure_type_concat : forall (L1 L2 : list nat) (A : formula) (c : c_term), closure_type A c (concat L1 L2) = closure_type (closure_type A c L1) c L2.
Proof.
intros L1. induction L1. auto. intros. simpl. rewrite IHL1; auto.
Qed.


Lemma closure_type_not_used : forall (L : list nat) (A : formula) (c : c_term) (n : nat), member n (free_list A) = false -> closure_type A c (n :: L) = closure_type A c L.
Proof.
intros L. induction L.
- intros. simpl. apply closed_subst_eq_aux. auto.
- intros A [ Hc] n LIST. simpl. case (nat_eqb x n) eqn:X.
  + apply nat_eqb_eq in X. destruct X. repeat rewrite (closed_subst_eq_aux _ _ _ LIST). auto.
  + rewrite substitution_order; auto. rewrite closed_subst_eq_aux. auto. rewrite subst_remove; auto. apply remove_member_false. auto.
Qed.

Lemma closure_type_not_used_any : forall (L1 L2 : list nat) (A : formula) (c : c_term) (n : nat), member n (free_list A) = false -> closure_type A c (concat L1 (n :: L2)) = closure_type A c (concat L1 L2).
Proof.
intros. rewrite (closure_type_concat_symm _ L2); auto. rewrite closure_type_concat_symm; auto. apply closure_type_not_used; auto.
Qed.

Lemma closure_type_not_used_remove : forall (L : list nat) (A : formula) (c : c_term) (n : nat), member n (free_list A) = false -> closure_type A c (remove n L) = closure_type A c L.
Proof.
intros L. induction L. auto. intros A [c Hc] n LIST. simpl. case (nat_eqb x n) eqn:X.
- apply nat_eqb_eq in X. destruct X. rewrite IHL; auto. rewrite closed_subst_eq_aux; auto.
- simpl. rewrite IHL; auto. rewrite subst_remove; auto. apply remove_member_false. auto.
Qed.

Lemma closure_type_dupes : forall (L : list nat) (A : formula) (c : c_term), closure_type A c L = closure_type A c (remove_dups L).
Proof.
intros L. induction L. auto. intros A [c Hc]. simpl. rewrite IHL; auto. rewrite closure_type_not_used_remove; auto. rewrite subst_remove; auto. apply remove_not_member.
Qed.

Lemma closure_lor : forall A B c, closure (lor A B) c = lor (closure A c) (closure B c).
Proof.
intros A. unfold closure. simpl. induction (free_list A) eqn:X.
- intros. simpl. rewrite <- free_list_remove_dups_idem. rewrite closure_type_lor; auto. rewrite closure_closed_list_id; auto. apply free_list_closed. auto.
- intros. rewrite <- closure_type_dupes; auto. rewrite closure_type_lor; auto. rewrite closure_type_concat; auto. rewrite closure_type_concat_symm; auto. rewrite closure_type_concat; auto.
  destruct X. rewrite closure_closed_list_id. rewrite (closure_closed_list_id (free_list A) (closure_type B c (free_list B))). auto. apply closure_closed; auto. apply closure_closed; auto.
Qed.

Lemma closure_neg_list : forall L A c, closure_type (neg A) c L = neg (closure_type A c L).
Proof.
intros L. induction L. auto. intros. simpl. rewrite IHL; auto.
Qed.

Lemma closure_univ_list : forall L A c n, closure_type (univ n A) c L = univ n (closure_type A c (remove n L)).
Proof.
intros L. induction L. auto. intros. simpl. case (nat_eqb n x) eqn:X.
- rewrite nat_eqb_symm. rewrite X. auto.
- rewrite IHL; auto. rewrite nat_eqb_symm. rewrite X. auto.
Qed.

Lemma closure_neg : forall A c, closure (neg A) c = neg (closure A c).
Proof.
intros. apply closure_neg_list.
Qed.

Lemma closure_univ : forall A c n, closure (univ n A) c = univ n (closure_type A c (free_list (univ n A))).
Proof.
intros. unfold closure. simpl. rewrite <- remove_idem at 2. apply closure_univ_list.
Qed.

Lemma num_conn_closure_eq_list : forall (L : list nat) (A : formula) (c : c_term), num_conn A = num_conn (closure_type A c L).
Proof.
intros L. induction L. auto. intros. simpl. rewrite <- IHL. rewrite num_conn_sub. auto.
Qed.

Lemma num_conn_closure_eq : forall (A : formula) (c : c_term), num_conn A = num_conn (closure A c).
Proof.
intros. apply num_conn_closure_eq_list.
Qed.

Lemma closure_subst_list :  forall (L : list nat) (A : formula) (c1 c2 : c_term) (n : nat), (substitution (closure_type A c1 (remove n L)) n (projT1 c2)) = (closure_type (substitution A n (projT1 c2)) c1 L).
Proof.
intros L. induction L. auto. intros A c1 c2 n. simpl. case (nat_eqb x n) eqn:X.
- apply nat_eqb_eq in X. destruct X. rewrite IHL; auto. rewrite (closed_subst_eq_aux (substitution A x (projT1 c2))). auto. rewrite subst_remove; auto. apply remove_not_member. destruct c2 as [c2 Hc2]. auto.
- simpl. rewrite IHL; auto. rewrite nat_eqb_symm in X. rewrite substitution_order; destruct c1 as [c1 Hc1]; destruct c2 as [c2 Hc2]; auto. 
Qed.

Lemma closure_subst :  forall (A : formula) (c1 c2 : c_term) (n : nat), (substitution (closure_type A c1 (free_list (univ n A))) n (projT1 c2)) = (closure (substitution A n (projT1 c2)) c1).
Proof.
intros. unfold closure. rewrite <- closure_subst_list; auto. rewrite remove_not_mem_idem. rewrite (free_list_univ_sub _ _ _ (free_list (univ n A))); auto. destruct c2 as [c2 Hc2]. auto. rewrite subst_remove; auto. apply remove_not_member. destruct c2 as [c2 Hc2]. auto.
Qed.



Lemma closure_closed_t' : forall (L : list nat) (t : term) (c : c_term), free_list_t t = L -> closed_t (closure_type_t t c L) = true.
Proof.
intros L. induction L; intros t [c Hc] LIST.
- simpl. apply free_list_closed_t. auto.
- simpl. rewrite IHL; auto. rewrite subst_remove_t; auto. rewrite LIST. rewrite remove_dups_idem_remove_triv. auto. destruct LIST. rewrite <- free_list_remove_dups_idem_t. auto.
Qed.

Lemma closure_closed_t : forall (t : term) (c : c_term), closed_t (closure_t t c) = true.
Proof.
intros. unfold closure_t. rewrite closure_closed_t'; auto.
Qed.

Lemma closure_type_equiv_list : forall L t1 t2 s, closure_type (atom (equ t1 t2)) s L = atom (equ (closure_type_t t1 s L) (closure_type_t t2 s L)).
Proof.
intros L. induction L; simpl; auto.
Qed.

Lemma closure_type_concat_t : forall (L1 L2 : list nat) (t : term) (c : c_term), closure_type_t t c (concat L1 L2) = closure_type_t (closure_type_t t c L1) c L2.
Proof.
intros L1. induction L1. auto. intros. simpl. rewrite IHL1; auto.
Qed.

Lemma closure_type_concat_symm_t : forall (L1 L2 : list nat) (t : term) (c : c_term), closure_type_t t c (concat L1 L2) = closure_type_t t c (concat L2 L1).
Proof.
intros L1. induction L1.
- intros. simpl. rewrite concat_empty_right. auto.
- intros L2. simpl. induction L2; intros.
  + simpl. rewrite concat_empty_right. auto.
  + rewrite IHL1; auto. simpl. rewrite <- IHL2; auto. rewrite IHL1; auto. case (nat_eqb x0 x) eqn:X.
   * apply nat_eqb_eq in X. destruct X. auto.
   * rewrite substitution_order_t; destruct c; auto.
Qed.

Lemma closure_closed_id_t : forall (t : term) (c : c_term), closed_t t = true -> closure_t t c = t.
intros. unfold closure_t. rewrite closed_free_list_t; auto.
Qed.

Lemma closure_closed_list_id_t : forall (L : list nat) (t : term) (c : c_term), closed_t t = true -> closure_type_t t c L = t.
intros L. induction L; auto. intros. simpl. rewrite closed_subst_eq_t; auto. 
Qed.

Lemma closure_type_not_used_remove_t : forall (L : list nat) (t : term) (c : c_term) (n : nat), member n (free_list_t t) = false -> closure_type_t t c (remove n L) = closure_type_t t c L.
Proof.
intros L. induction L. auto. intros. simpl. case (nat_eqb x n) eqn:X.
- apply nat_eqb_eq in X. destruct X. rewrite IHL; auto. rewrite closed_subst_eq_aux_t; auto.
- simpl. rewrite IHL; auto. rewrite subst_remove_t; auto. apply remove_member_false. auto. destruct c; auto.
Qed.

Lemma closure_type_dupes_t : forall (L : list nat) (t : term) (c : c_term), closure_type_t t c L = closure_type_t t c (remove_dups L).
Proof.
intros L. induction L. auto. intros. simpl. rewrite IHL; auto. rewrite closure_type_not_used_remove_t; auto. rewrite subst_remove_t; auto. apply remove_not_member. destruct c; auto.
Qed.

Lemma closure_type_equiv : forall t1 t2 c, closure (atom (equ t1 t2)) c = atom (equ (closure_t t1 c) (closure_t t2 c)).
Proof.
intros. unfold closure. rewrite closure_type_equiv_list. simpl. rewrite <- closure_type_dupes_t; auto. rewrite <- closure_type_dupes_t; auto.
rewrite closure_type_concat_t; auto. rewrite closure_type_concat_symm_t; auto. rewrite closure_type_concat_t; auto.
rewrite (closure_closed_list_id_t (free_list_t t2)). rewrite (closure_closed_list_id_t (free_list_t t1) (closure_type_t t2 c _)); auto. apply closure_closed_t; auto. apply closure_closed_t; auto.
Qed.

Lemma closure_t_succ_list : forall L t s, closure_type_t (succ t) s L = succ (closure_type_t t s L).
Proof.
intros L. induction L. auto. intros. simpl. rewrite IHL. auto.
Qed.

Lemma closure_t_succ : forall t s, closure_t (succ t) s = succ (closure_t t s).
Proof.
intros. apply closure_t_succ_list.
Qed.

Lemma closure_t_plus_list : forall L t1 t2 s, closure_type_t (plus t1 t2) s L = plus (closure_type_t t1 s L) (closure_type_t t2 s L).
Proof.
intros L. induction L. auto. intros. simpl. rewrite IHL. auto.
Qed.

Lemma closure_t_plus : forall t1 t2 c, closure_t (plus t1 t2) c = plus (closure_t t1 c) (closure_t t2 c).
Proof.
intros. unfold closure_t. rewrite closure_t_plus_list. simpl. rewrite <- closure_type_dupes_t; auto. rewrite <- closure_type_dupes_t; auto.
rewrite closure_type_concat_t; auto. rewrite closure_type_concat_symm_t; auto. rewrite closure_type_concat_t; auto.
rewrite (closure_closed_list_id_t (free_list_t t2)). rewrite (closure_closed_list_id_t (free_list_t t1) (closure_type_t t2 c _)); auto. apply closure_closed_t; auto. apply closure_closed_t; auto.
Qed.

Lemma closure_t_times_list : forall L t1 t2 s, closure_type_t (times t1 t2) s L = times (closure_type_t t1 s L) (closure_type_t t2 s L).
Proof.
intros L. induction L. auto. intros. simpl. rewrite IHL. auto.
Qed.

Lemma closure_t_times : forall t1 t2 s, closure_t (times t1 t2) s = times (closure_t t1 s) (closure_t t2 s).
Proof.
intros. unfold closure_t. rewrite closure_t_times_list. simpl. rewrite <- closure_type_dupes_t; auto. rewrite <- closure_type_dupes_t; auto.
rewrite closure_type_concat_t; auto. rewrite closure_type_concat_symm_t; auto. rewrite closure_type_concat_t; auto.
rewrite (closure_closed_list_id_t (free_list_t t2)). rewrite (closure_closed_list_id_t (free_list_t t1) (closure_type_t t2 s _)); auto. apply closure_closed_t; auto. apply closure_closed_t; auto.
Qed.

Lemma weak_substitution_order_t : forall (T : term) (m n : nat) (s t : term),
  member m (free_list_t s) = false ->
  member n (free_list_t t) = false ->
  nat_eqb m n = false ->
  substitution_t (substitution_t T n s) m t =
  substitution_t (substitution_t T m t) n s.
Proof.
intros T m n s t Hs Ht Hmn. induction T; auto; simpl.
- rewrite IHT. auto.
- rewrite IHT1, IHT2. auto.
- rewrite IHT1, IHT2. auto.
- destruct (nat_eqb n0 n) eqn:Hn.
  + rewrite <- (nat_eqb_eq _ _ Hn) in Hmn. rewrite nat_eqb_symm. rewrite Hmn.
    simpl. rewrite Hn. rewrite closed_subst_eq_aux_t; auto.
  + destruct (nat_eqb n0 m) eqn:Hm; simpl; rewrite Hm.
    * rewrite closed_subst_eq_aux_t; auto.
    * rewrite Hn. auto.
Qed.

Lemma weak_substitution_order_a :
  forall (a : atomic_formula) (m n : nat) (s t : term),
  member m (free_list_t s) = false ->
  member n (free_list_t t) = false ->
  nat_eqb m n = false ->
  substitution_a (substitution_a a n s) m t =
  substitution_a (substitution_a a m t) n s.
Proof.
intros a m n s t Hs Ht Hmn. destruct a as [t1 t2]. simpl.
rewrite (weak_substitution_order_t _ _ _ _ _ Hs Ht Hmn).
rewrite (weak_substitution_order_t _ _ _ _ _ Hs Ht Hmn). auto.
Qed.

Lemma weak_substitution_order : forall (B : formula) (m n : nat) (s t : term),
  member m (free_list_t s) = false ->
  member n (free_list_t t) = false ->
  nat_eqb m n = false ->
  substitution (substitution B n s) m t =
  substitution (substitution B m t) n s.
Proof.
intros B m n s t Hs Ht Hmn. induction B; simpl.
- rewrite (weak_substitution_order_a _ _ _ _ _ Hs Ht Hmn). auto.
- rewrite IHB. auto.
- rewrite IHB1, IHB2. auto.
- destruct (nat_eqb n0 n) eqn:Hn.
  + apply nat_eqb_eq in Hn. rewrite Hn.
    rewrite nat_eqb_symm. rewrite Hmn. simpl.
    rewrite nat_eqb_symm. rewrite Hmn. rewrite nat_eqb_refl. auto.
  + destruct (nat_eqb n0 m) eqn:Hm; simpl; rewrite Hm, Hn; auto.
    rewrite IHB. auto.
Qed.

Lemma closure_type_sub_remove_list : forall (L : list nat) (A : formula) (c : c_term) (n : nat), (closure_type (substitution A n (succ (var n))) c (remove n L)) = substitution (closure_type A c (remove n L)) n (succ (var n)).
Proof.
intros L. induction L. auto. intros. simpl. case (nat_eqb x n) eqn:X. rewrite IHL; auto. simpl. rewrite <- IHL; auto. rewrite weak_substitution_order; simpl; auto. rewrite nat_eqb_symm in X. rewrite X. auto. rewrite closed_free_list_t; auto. destruct c. auto.
Qed.

Lemma closure_type_sub_remove : forall (A : formula) (c : c_term) (n : nat), (closure_type (substitution A n (succ (var n))) c (free_list (univ n (lor (neg A) (substitution A n (succ (var n))))))) = substitution (closure_type A c (free_list (univ n A))) n (succ (var n)).
Proof.
intros A [c Hc] n. case (member n (free_list A)) eqn:X.
- simpl. rewrite free_list_sub_self; auto. rewrite remove_dups_concat_self. rewrite <- free_list_remove_dups_idem. rewrite closure_type_sub_remove_list; auto.
- simpl. rewrite closed_subst_eq_aux; auto. rewrite remove_dups_concat_self. rewrite <- free_list_remove_dups_idem. rewrite <- closure_type_sub_remove_list; auto. rewrite closed_subst_eq_aux; auto.
Qed.

Lemma closure_type_list_remove : forall (L : list nat) (A : formula) (c : c_term) (n : nat), L = free_list A -> free_list (closure_type A c (remove n L)) = [n] \/ free_list (closure_type A c (remove n L)) = [].
Proof.
intros L. induction L. auto. intros. simpl. assert (L = free_list (substitution A x (projT1 c))) as Y. rewrite subst_remove; auto. rewrite <- H. rewrite remove_dups_idem_remove_triv; auto. rewrite H. rewrite <- free_list_remove_dups_idem. auto. destruct c. auto. case (nat_eqb x n) eqn:X. 
- apply nat_eqb_eq in X. destruct X. destruct (IHL (substitution A x (projT1 c)) c x Y).
  + rewrite closure_type_not_used_remove in H0; auto.
    * rewrite <- closure_subst_list in H0; auto. rewrite subst_remove in H0; auto. pose proof (remove_not_member (free_list (closure_type A c (remove x L))) x). rewrite H0 in H1. simpl in H1. rewrite nat_eqb_refl in H1. inversion H1. destruct c. auto.
    * rewrite subst_remove; auto. apply remove_not_member. destruct c. auto.
  + rewrite <- closure_subst_list in H0; auto. rewrite subst_remove in H0; auto. rewrite remove_idem in H0. rewrite free_list_remove_dups_idem in H0. rewrite free_list_remove_dups_idem. destruct (remove_n_dups_empty _ _ H0); auto. destruct c; auto.
- simpl. apply IHL; auto. 
Qed.

Lemma free_list_univ_closure : forall (A : formula) (c : c_term) (n : nat), free_list (closure_type A c (free_list (univ n A))) = [n] \/ free_list (closure_type A c (free_list (univ n A))) = [].
Proof.
intros. simpl. apply closure_type_list_remove; auto.
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
- case_eq (nat_eqb n0 n); intros; simpl; rewrite H1.
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


Lemma correct_closed_t : forall (s t : term),
  correct_a (equ s t) = true -> closed_t s = true /\ closed_t t = true.
Proof.
intros.
destruct (correct_eval _ _ H). split; apply eval_closed.
apply H0. apply H1.
Qed.

Definition czero := (closing zero (represent_closed 0)).

Definition cterm_equiv_correct : forall c : c_term, correct_a (equ (represent (value c)) (projT1 c)) = true.
Proof.
intros. unfold correct_a. unfold correctness. pose proof eval_represent_non_zero (value c). case (eval (represent (value c))) eqn:X. inversion H.
pose proof (closed_eval (projT1 c) (projT2 c)). case (eval (projT1 c)) eqn:X1. inversion H0. unfold value in X. rewrite represent_eval in X.
destruct X. destruct X1. rewrite nat_eqb_refl. auto. destruct c. auto.
Qed.