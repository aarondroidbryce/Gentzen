Require Import Omega.
Require Import Arith.
Require Import Lia.

Notation "b1 && b2" := (andb b1 b2).
Notation "b1 || b2" := (orb b1 b2).

(* Basic properties of natural numbers *)
(* *)
Notation beq_nat := Nat.eqb.

Theorem beq_nat_refl : forall (n : nat), true = beq_nat n n.
Proof.
intros n.
induction n as [| n IH].
- reflexivity.
- simpl. apply IH.
Qed.

Fixpoint bgeq_nat (n m : nat) : bool :=
  match (n, m) with
    (0, 0) => true
  | (S n', 0) => true
  | (0, S m') => false
  | (S n', S m') => bgeq_nat n' m'
  end.

Theorem succ_geq : forall (n : nat), bgeq_nat (S n) n = true.
Proof.
intros. induction n.
- simpl. reflexivity.
- rewrite <- IHn. auto.
Qed.

Definition lt_nat (n m : nat) : bool := (bgeq_nat m n) && negb (beq_nat n m).

Lemma lt_nat_irrefl : forall (n : nat), lt_nat n n = false.
Proof.
intros.
induction n.
- auto.
- rewrite <- IHn. auto.
Qed.

Theorem succ_beq : forall (n : nat), beq_nat n (S n) = false.
Proof.
intros. induction n.
- auto.
- rewrite <- IHn. auto.
Qed.


Definition nat_lt_aux' (n : nat) :=
  forall (m : nat), n < m -> lt_nat n m = true.

Lemma nat_lt_aux : forall (n : nat), nat_lt_aux' n.
Proof.
intros.
induction n.
- unfold nat_lt_aux'. intros. destruct m.
  + inversion H.
  + auto.
- unfold nat_lt_aux'. intros. destruct m.
  + inversion H.
  + unfold nat_lt_aux' in IHn.
    assert (n < m). { omega. }
    specialize IHn with m. apply IHn in H0.
    simpl. 
    inversion H. unfold lt_nat. rewrite (succ_geq (S n)). simpl.
    rewrite (succ_beq n). auto.
    unfold lt_nat. simpl.
    unfold lt_nat in H0. apply H0.
Qed.

Definition nat_eq_beq' (n : nat) :=
  forall (m : nat), beq_nat n m = true -> n = m.

Lemma nat_eq_beq : forall (n : nat), nat_eq_beq' n.
Proof.
intros.
induction n.
- unfold nat_eq_beq'. intros. destruct m.
  + auto.
  + inversion H.
- unfold nat_eq_beq'. intros. destruct m.
  + inversion H.
  + simpl in H. unfold nat_eq_beq' in IHn. specialize IHn with m.
    apply IHn in H. rewrite H. auto.
Qed.


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
  lt_nat n m = true -> ~(lt_nat m n = true).
Proof.
intros. unfold not. intros.
pose proof (lt_nat_trans n).
unfold nat_trans in H1.
specialize H1 with m n.
assert (lt_nat n n = true). { apply H1. apply H. apply H0. }
rewrite (lt_nat_irrefl n) in H2.
inversion H2.
Qed.

Lemma mult_right_incr_aux_aux : forall (n m p : nat),
  n < m -> n + p * (S n) < m + p * (S m).
Proof. intros. induction p; lia. Qed.

Lemma mult_left_incr_aux_aux : forall (n m p : nat),
  n < m -> p + n * (S p) < p + m * (S p).
Proof. intros. induction p; lia. Qed.

Theorem minus_n_0 : forall (n : nat), n - 0 = n.
Proof. intros. omega. Qed.

Theorem plus_n_0 : forall n:nat,
  n + 0 = n.
Proof.
intros n.
induction n as [| n' IH].
- reflexivity.
- simpl.
  rewrite IH.
  reflexivity.
Qed.

Theorem plus_n_1 : forall n:nat,
  n + 1 = S n.
Proof.
intros n.
induction n as [| n' IH].
- reflexivity.
- simpl.
  rewrite IH.
  reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
intros m n.
induction m as [| m' IH].
- reflexivity.
- simpl.
  rewrite IH.
  reflexivity.
Qed.

Lemma nat_exp_monot_lem : forall (n : nat), S n < 2 ^ n + 2 ^ n.
Proof.
intros.
induction n.
- auto.
- simpl. rewrite plus_n_0. lia.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
intros m n.
induction m as [| m' IH].
- simpl.
  rewrite <- plus_n_O.
  reflexivity.
- induction n as [| n' IHn].
  + simpl.
    rewrite <- plus_n_O.
    reflexivity.
  + simpl.
    rewrite IH.
    simpl.
    rewrite plus_n_Sm.
    reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
intros n m p.
induction n as [| n IHn].
- simpl.
  reflexivity.
- simpl.
  rewrite IHn.
  reflexivity.
Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
intros n.
induction n as [| n' IH].
- reflexivity.
- simpl.
  rewrite IH.
  reflexivity.
Qed.

Lemma mult_1_r : forall (n : nat), n * 1 = n.
Proof.
intros n.
induction n as [| n' IH].
- reflexivity.
- simpl. rewrite IH. reflexivity.
Qed.

(* Definition of PA formulas *)
(* *)
Inductive term : Type :=
    zero : term
  | succ : term -> term
  | plus : term -> term -> term
  | times : term -> term -> term
  | f_var : nat -> term
  | b_var : nat -> term.

Inductive atomic_formula : Type :=
    equ : term -> term -> atomic_formula.

Inductive formula : Type :=
    atom : atomic_formula -> formula
  | neg : formula -> formula
  | lor : formula -> formula -> formula
  | univ : nat -> formula -> formula.


(* Count number of connectives and quantifiers appearing in a formula *)
(* *)
Fixpoint num_conn (a : formula) : nat :=
  match a with
  | atom a' => 0
  | neg a' => 1 + (num_conn a')
  | lor a1 a2 => 1 + (num_conn a1) + (num_conn a2)
  | univ n a' => 1 + (num_conn a')
  end.

(* Check syntactic equality of formulas *)
(* *)
Fixpoint eq_term (s t : term) : bool :=
  match (s, t) with
  | (zero, zero) => true
  | (succ s', succ t') => eq_term s' t'
  | (plus s1 s2, plus t1 t2) => (eq_term s1 t1) && (eq_term s2 t2)
  | (times s1 s2, times t1 t2) => (eq_term s1 t1) && (eq_term s2 t2)
  | (f_var m, f_var n) => beq_nat m n
  | (b_var m, b_var n) => beq_nat m n
  | (_,_) => false
end.

Compute eq_term zero zero.
Compute eq_term (succ zero) (succ zero).

Fixpoint eq_atom (a b : atomic_formula) : bool :=
  match (a, b) with
    (equ s1 s2, equ t1 t2) => (eq_term s1 t1) && (eq_term s2 t2)
  end.

Compute eq_atom (equ zero (succ zero)) (equ zero (succ zero)).

Fixpoint eq_f (a b : formula) : bool :=
  match (a, b) with
  | (atom a', atom b') => eq_atom a' b'
  | (neg a', neg b') => eq_f a' b'
  | (lor a1 a2, lor b1 b2) => (eq_f a1 b1) && (eq_f a2 b2)
  | (univ m a', univ n b') => (beq_nat m n) && (eq_f a' b')
  | (_, _) => false
  end.

Compute eq_f (atom (equ zero (succ zero))) (atom (equ zero (succ zero))).

Theorem eq_term_refl : forall (t : term), true = eq_term t t.
Proof.
intros t.
induction t.
- reflexivity.
- simpl. apply IHt.
- simpl. rewrite <- IHt1. apply IHt2.
- simpl. rewrite <- IHt1. apply IHt2.
- simpl. apply beq_nat_refl.
- simpl. apply beq_nat_refl.
Qed.

Theorem eq_atom_refl : forall (a : atomic_formula), true = eq_atom a a.
Proof.
intros a.
destruct a as [t1 t2].
unfold eq_atom.
rewrite <- eq_term_refl.
apply eq_term_refl.
Qed.

Theorem eq_f_refl : forall (a : formula), true = eq_f a a.
Proof.
intros a.
induction a as [a | a IH | a1 IH1 a2 IH2 | n a IH].
- unfold eq_f. apply eq_atom_refl.
- simpl. apply IH.
- simpl. rewrite <- IH1. apply IH2.
- simpl. rewrite <- beq_nat_refl. apply IH.
Qed.


(* Given some term t, returns t+1 if the formula is closed, 0 otherwise *)
(* *)
Fixpoint eval (t : term) : nat :=
  match t with
    zero => S O
  | succ t_1 =>
      (match (eval t_1) with
        O => O
      | S n => S (S n)
      end)
  | plus t_1 t_2 =>
      (match (eval t_1, eval t_2) with
        (O, O) => O
      | (S n, O) => O
      | (O, S m) => O
      | (S n, S m) => S (n + m)
      end)
  | times t_1 t_2 =>
      (match (eval t_1, eval t_2) with
        (O, O) => O
      | (S n, O) => O
      | (O, S m) => O
      | (S n, S m) => S (n * m)
      end)
  | f_var n => O
  | b_var n => O
  end.

Compute eval zero.
Compute eval (f_var O).
Compute eval (succ zero).
Compute eval (succ (f_var O)).
Compute eval (plus (succ zero) (f_var O)).

Inductive ternary : Type :=
    correct : ternary
  | incorrect : ternary
  | undefined : ternary.

Fixpoint represent (n : nat) : term :=
  match n with
    O => zero
  | S n' => succ (represent n')
  end.

Compute represent 0.
Compute represent 1.
Compute represent 2.
Compute represent 5.


(* Given some atomic formula a, returns whether the statement is correct,
incorrect, or undefined (i.e. not closed) *)
Definition correctness (a : atomic_formula) : ternary :=
  match a with
    equ t_1 t_2 =>
      (match (eval t_1, eval t_2) with
        (O, O) => undefined
      | (S n, O) => undefined
      | (O, S m) => undefined
      | (S n, S m) =>
          (match (beq_nat (eval t_1) (eval t_2)) with
            true => correct
          | false => incorrect
          end)
      end)
  end.

Compute correctness (equ zero zero).
Compute correctness (equ zero (succ zero)).
Compute correctness (equ (plus (succ zero) (succ zero)) (succ (succ zero))).
Compute correctness (equ zero (f_var O)).


Definition correct_a (a : atomic_formula) : bool :=
match (correctness a) with
| correct => true
| _ => false
end.

Definition incorrect_a (a : atomic_formula) : bool :=
match (correctness a) with
| incorrect => true
| _ => false
end.



(* Basic properties of lists and lists of nats *)
(* *)

Inductive list (X:Type) : Type :=
  | nil : list X
  | constr : X -> list X -> list X.

Arguments nil {X}.
Arguments constr {X} _ _.
Notation "x :: l" := (constr x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (constr x .. (constr y nil) ..).

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
    nil => O
  | n :: l' => S (length l')
  end.

Fixpoint concat {X : Type} (l_1 l_2 : list X) : list X :=
  match l_1 with
    nil => l_2
  | n :: l_1' => n :: (concat l_1' l_2)
  end.

Fixpoint beq_list {X : Type} (l1 l2 : list X) : bool :=
  match l1,l2 with
    [],[] => true
  | m :: l1',[] => false
  | [], n :: l2' => false
  | m :: l1', n :: l2' => beq_list l1' l2'
  end.

Fixpoint remove (n : nat) (l : list nat) : list nat :=
  match l with
    nil => nil
  | m :: l' => (match (beq_nat n m) with
                  true => remove n l'
                | false => m :: (remove n l')
                end)
  end.

Fixpoint member (n : nat) (l : list nat) : bool :=
  match l with
    nil => false
  | m :: l' => (match (beq_nat n m) with
                  true => true
                | false => member n l'
                end)
  end.

Fixpoint remove_dups (l : list nat) : list nat :=
  match l with
    [] => []
  | n :: l' => n :: (remove n (remove_dups l'))
  end.




(* Free variable lists *)
(* *)
Fixpoint free_list_t (t : term) : list nat :=
  match t with
    zero => nil
  | succ t_1 => free_list_t t_1
  | plus t_1 t_2 => concat (free_list_t t_1) (free_list_t t_2)
  | times t_1 t_2 => concat (free_list_t t_1) (free_list_t t_2)
  | f_var n => nil
  | b_var n => [n]
  end.

Definition free_list_a (a : atomic_formula) : list nat :=
  match a with
    equ t_1 t_2 => concat (free_list_t t_1) (free_list_t t_2)
  end.

Fixpoint free_list (f : formula) : list nat :=
  match f with
    atom a => free_list_a a
  | neg f_1 => free_list f_1
  | lor f_1 f_2 => concat (free_list f_1) (free_list f_2)
  | univ n f_1 => remove n (free_list f_1)
  end.

Compute remove 1 [1,2,3].
Compute free_list_a (equ(b_var 1)(b_var 2)).

Definition closed_t (t : term) : bool :=
  match (free_list_t t) with
  | nil => true
  | n :: l => false
  end.

Definition closed_a (a : atomic_formula) : bool :=
  match (free_list_a a) with
  | nil => true
  | n :: l => false
  end.

Definition closed (f : formula) : bool :=
  match (free_list f) with
  | nil => true
  | n :: l => false
  end.

Inductive sentence : Type :=
  sent : forall (f : formula), formula -> (free_list f = []) -> sentence.

Check sentence.
Check sent.

Fixpoint closed_term_list_t (t : term) : list term :=
  match (t, closed_t t)  with
  | (zero, _) => [t]
  | (succ t', true) => t :: closed_term_list_t t'
  | (succ t', false) => closed_term_list_t t'
  | (plus t1 t2, true) => t :: (concat (closed_term_list_t t1)
                                      (closed_term_list_t t2))
  | (plus t1 t2, false) => (concat (closed_term_list_t t1)
                                  (closed_term_list_t t2))
  | (times t1 t2, true) => t :: (concat (closed_term_list_t t1)
                                      (closed_term_list_t t2))
  | (times t1 t2, false) => (concat (closed_term_list_t t1)
                                  (closed_term_list_t t2))
  | (_, _) => nil
  end.

Compute closed_term_list_t (plus (b_var 3) zero).
Compute closed_term_list_t (succ (succ zero)).
Compute closed_term_list_t (plus (times zero (succ (succ zero))) zero).

Definition closed_term_list_a (a : atomic_formula) : list term :=
  match a with
  | equ t1 t2 => concat (closed_term_list_t t1) (closed_term_list_t t2)
  end.

Fixpoint closed_term_list (a : formula) : list term :=
  match a with
  | atom a' => closed_term_list_a a'
  | neg a' => closed_term_list a'
  | lor a1 a2 => concat (closed_term_list a1) (closed_term_list a2)
  | univ n a' => closed_term_list a'
  end.




(* Defining substitution of a term t for all free occurrences of a
   variable x_n in a formula f *)
(* *)
Fixpoint substitution_t (f : term) (n : nat) (t : term) : term :=
  match f with
    zero => f
  | succ f_1 => succ (substitution_t f_1 n t)
  | plus f_1 f_2 => plus (substitution_t f_1 n t) (substitution_t f_2 n t)
  | times f_1 f_2 => times (substitution_t f_1 n t) (substitution_t f_2 n t)
  | f_var m =>
      (match (beq_nat m n) with
        true => t
      | false => f
      end)
  | b_var m =>
      (match (beq_nat m n) with
        true => t
      | false => f
      end)
  end.

Definition substitution_a (f : atomic_formula) (n : nat) (t : term)
  : atomic_formula :=
  match f with
    equ t_1 t_2 => equ (substitution_t t_1 n t) (substitution_t t_2 n t)
  end.

Fixpoint substitution (f : formula) (n : nat) (t : term) : formula :=
  match f with
    atom a => atom (substitution_a a n t)
  | neg f_1 => neg (substitution f_1 n t)
  | lor f_1 f_2 => lor (substitution f_1 n t) (substitution f_2 n t)
  | univ m f_1 => 
      (match (beq_nat m n) with
        true => f
      | false => univ m (substitution f_1 n t)
      end)
  end.

(* Given a list of closed terms and a variable x_n in formula a, check if any
of those terms can be substituted for x_n to obtain the formula b *)
Fixpoint transformable_with_list (a b : formula) (n : nat) (l : list term)
          : bool :=
  match l with
  | nil => false
  | t :: l' => if (eq_f (substitution a n t) b)
              then true
              else transformable_with_list a b n l'
  end.

(* Determine if some formula a can be transformed into formula b by an
appropriate substitution of some closed term for all instances of x_n in a *)
Definition transformable (a b : formula) (n : nat) : bool :=
  transformable_with_list a b n (closed_term_list b).

Compute transformable (atom (equ zero (f_var 9)))
                      (atom (equ zero (succ zero))) 9.
Compute transformable (atom (equ zero (f_var 9)))
                      (atom (equ (succ zero) (succ zero))) 9.

(* Define inductively what it means for a term t to be free for a variable x_n
in a formula f; namely, that no free occurrence of x_n in f is in the scope of
some (univ m), where x_m is a variable in t. *)
(* *)
Fixpoint free_for (t : term) (n : nat) (f : formula) : bool :=
  match f with
    atom a => true
  | neg f_1 => free_for t n f_1
  | lor f_1 f_2 => (free_for t n f_1) && (free_for t n f_2)
  | univ m f_1 =>
      if member m (free_list_t t)
      then negb (member n (free_list f_1))
      else free_for t n f_1
  end.

Compute free_for zero 0 (univ 1 (atom (equ (b_var 0) (b_var 0)))).
Compute free_for (b_var 1) 0 (univ 1 (atom (equ (b_var 0) (b_var 0)))).


(* Logical axioms of FOL *)
(* *)
Definition implies (a b : formula) : formula :=
  lor (neg a) b.

Definition land (a b : formula) : formula :=
  neg (lor (neg a) (neg b)).

Definition exis (n : nat) (f : formula) :=
  neg (univ n (neg f)).


Definition logical_axiom_1 (a b : formula) : formula :=
  implies a (implies b a).

Definition logical_axiom_2 (a b c : formula) : formula :=
  implies (implies a (implies b c)) (implies (implies a b) (implies b c)).

Definition logical_axiom_3 (a b : formula) : formula :=
  implies (implies (neg b) (neg a)) (implies (implies (neg b) a) b).

Definition logical_axiom_4 (a : formula) (n : nat) (t : term) : formula :=
  if free_for t n a
  then implies (univ n a) (substitution a n t)
  else atom (equ zero zero).

Compute logical_axiom_4 (atom (equ (b_var 0) (b_var 0))) 0 zero.
Compute logical_axiom_4 (atom (equ zero zero)) 0 zero.
Compute logical_axiom_4 (atom (equ (b_var 1) (b_var 1))) 0 zero.
Compute logical_axiom_4 (atom (equ (b_var 0) (b_var 0))) 0 zero.
Compute logical_axiom_4 (exis 1 (atom (equ (b_var 1) (plus (b_var 0) (succ zero)))))
                        1 (succ (b_var 1)).


Definition logical_axiom_5 (a b : formula) (n : nat) : formula :=
  if negb (member n (free_list a))
  then implies (univ n (implies a b)) (implies a (univ n b))
  else atom (equ zero zero).

Compute logical_axiom_5 (atom (equ zero zero)) (atom (equ zero zero)) 0.
Compute logical_axiom_5 (atom (equ (b_var 1) zero)) (atom (equ zero zero)) 1.

Definition logical_axiom_6 (a : formula) (x y : nat) : formula :=
  if (member y (free_list a)) && (negb (member x (free_list a)))
  then implies a (univ x (substitution a y (b_var x)))
  else atom (equ zero zero).

Compute logical_axiom_6 (atom (equ (b_var 1) (b_var 1))) 0 1.
Compute logical_axiom_6 (univ 1 (atom (equ (b_var 1) (b_var 1)))) 0 1.
Compute logical_axiom_6 (atom (equ (b_var 1) (b_var 0))) 0 1.
Compute logical_axiom_6 (atom (equ (b_var 0) zero)) 0 1.
Compute logical_axiom_6 (atom (equ (b_var 1) zero)) 0 1.



(* Axioms of Peano Arithmetic (PA) *)
(* *)
Definition peano_axiom_1 (x y z : nat) : formula :=
  univ x (univ y (univ z (
    implies (land (atom (equ (b_var x) (b_var y)))
                  (atom (equ (b_var y) (b_var z))))
            (atom (equ (b_var x) (b_var z)))))).

Definition peano_axiom_2 (x y : nat) : formula :=
  univ x (univ y (
    implies (atom (equ (b_var x) (b_var y)))
            (atom (equ (succ (b_var x)) (succ (b_var y)))))).

Definition peano_axiom_3 (x : nat) : formula :=
  univ x (neg (atom (equ (succ (b_var x)) zero))).

Definition peano_axiom_4 (x y : nat) : formula :=
  univ x (univ y (
    implies (atom (equ (succ (b_var x)) (succ (b_var y))))
            (atom (equ (b_var x) (b_var y))))).

Definition peano_axiom_5 (x : nat) : formula :=
  univ x (atom (equ (plus (b_var x) zero) (b_var x))).

Definition peano_axiom_6 (x y : nat) : formula :=
  univ x (univ y (
    atom (equ (plus (b_var x) (succ (b_var y)))
                    (succ (plus (b_var x) (b_var y)))))).

Definition peano_axiom_7 (x : nat) : formula :=
  univ x (atom (equ (times (b_var x) zero) zero)).

Definition peano_axiom_8 (x y : nat) : formula :=
  univ x (univ y (
    atom (equ (times (b_var x) (succ (b_var y)))
              (plus (times (b_var x) (b_var y)) (b_var x))))).

Definition peano_axiom_9 (f : formula) (x : nat) : formula :=
  if member x (free_list f)
  then implies (land (substitution f x zero)
                     (univ x (implies f (substitution f x (succ (b_var x))))))
               (univ x f)
  else atom (equ zero zero).






Theorem nat_semiconnex : forall (m n : nat), m < n \/ n < m \/ m = n.
Proof.
intros. omega.
Qed.

Lemma nat_transitive : forall (n n' n'' : nat), n < n' -> n' < n'' -> n < n''.
Proof.
intros. omega.
Qed.

(* Defining ordinals *)
(* *)

(** cons a n b represents  omega^a *(S n)  + b *)

Inductive ord : Set :=
  Zero : ord
| cons : ord -> nat -> ord -> ord.

(* A total strict order on ord *)

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

Definition semiconnex (alpha : ord) :=
  forall (beta : ord), alpha < beta \/ beta < alpha \/ alpha = beta.


Theorem ordinal_semiconnex : forall (alpha : ord), semiconnex alpha.
Proof.
intros alpha.
induction alpha.
- unfold semiconnex.
  induction beta.
  + right. right. reflexivity.
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


Theorem lt_trans' : forall (alpha : ord), transitive alpha.
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


Theorem lt_trans : forall (alpha beta gamma : ord),
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
  + omega.
  + apply IHb. apply H1.
Qed.

Lemma lt_asymm : forall (alpha beta : ord),
  alpha < beta -> ~(beta < alpha).
Proof.
intros. intros H0.
pose proof (lt_trans alpha beta alpha H H0).
apply (lt_irrefl alpha H1).
Qed.





(* The predicate "to be in normal form" *)

(* The real Cantor normal form needs the exponents of omega to be
   in strict decreasing order *)


Inductive nf : ord -> Prop :=
| zero_nf : nf Zero
| single_nf : forall a n, nf a ->  nf (cons a n Zero)
| cons_nf : forall a n a' n' b, a' < a ->
                             nf a ->
                             nf (cons a' n' b)->
                             nf (cons a n (cons a' n' b)).
Hint Resolve zero_nf single_nf cons_nf : ord.

Definition e0 : Type := {a : ord | nf a}.

Check cons Zero O (cons Zero O Zero).

Theorem Zero_nf : nf Zero.
Proof. apply zero_nf. Qed.

Check exist nf Zero Zero_nf.
Check exist.
Check exist nf.

Definition lt_e0 (alpha beta : e0) : Prop :=
  match (alpha, beta) with
  | (exist _ alpha' _, exist _ beta' _) => alpha' < beta'
  end.

Definition leq_e0 (alpha beta : e0) : Prop := lt_e0 alpha beta \/ alpha = beta.
Definition gt_e0 (alpha beta : e0) : Prop := lt_e0 beta alpha.
Definition geq_e0 (alpha beta : e0) : Prop := leq_e0 beta alpha.

Definition nat_ord (n : nat) : ord :=
  match n with
  | O => Zero
  | S n' => cons Zero n' Zero
  end.


(* defining boolean equality and less than, assuming normal form. *)
(* *)
Fixpoint ord_eqb (alpha beta : ord) : bool :=
match (alpha, beta) with
| (Zero, Zero) => true
| (_, Zero) => false
| (Zero, _) => false
| (cons a n b, cons a' n' b') =>
    (match (ord_eqb a a') with
    | false => false
    | true =>
        (match (beq_nat n n') with
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
    (match (ord_ltb a a', ord_eqb a a') with
    | (true, _) => true
    | (_, false) => false
    | (_, true) =>
        (match (lt_nat n n', lt_nat n' n) with
        | (true, _) => true
        | (_, true) => false
        | (_, _) => ord_ltb b b'
        end)
    end)
end.

Lemma ord_eqb_refl : forall (alpha : ord), ord_eqb alpha alpha = true.
Proof.
intros.
induction alpha.
- auto.
- simpl. rewrite IHalpha1. rewrite <- beq_nat_refl. rewrite IHalpha2. auto.
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
      assert (lt_nat n n0 = true). { apply (nat_lt_aux n). apply H1. }
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
Proof.
intros.
apply ord_lt_ltb_aux.
apply H.
Qed.

Lemma ltb_trans_aux : forall (a a' b b' : ord) (n n' : nat),
  ord_ltb (cons a n b) (cons a' n' b') = true ->
  (ord_ltb a a' = true \/ (ord_eqb a a' = true /\ lt_nat n n' = true) \/
  (ord_eqb a a' = true /\ n = n' /\ ord_ltb b b' = true)).
Proof.
intros.
inversion H.
case_eq (ord_ltb a a').
- auto.
- intros. rewrite H0 in H1. case_eq (ord_eqb a a').
  + intros. right. rewrite H2 in H1. case_eq (lt_nat n n').
    * intros. rewrite H3 in H1. auto.
    * intros. rewrite H3 in H1. case_eq (lt_nat n' n).
      { intros. rewrite H4 in H1. inversion H1. }
      { intros. rewrite H4 in H1. right. split. rewrite H1. auto. split.
        { pose proof (nat_semiconnex n n'). destruct H5.
          { pose proof (nat_lt_aux n). unfold nat_lt_aux' in H6.
            specialize H6 with n'. apply H6 in H5. rewrite H5 in H3.
            inversion H3. }
          { destruct H5.
            { pose proof (nat_lt_aux n'). unfold nat_lt_aux' in H6.
              specialize H6 with n. apply H6 in H5. rewrite H5 in H4.
              inversion H4. }
            { apply H5. } } }
        { auto. } }
  + intros. left. auto.
Qed.

Definition ord_eqb_eq_aux' (alpha : ord) := forall (beta : ord),
  ord_eqb alpha beta = true -> alpha = beta.

Lemma ord_eqb_eq_aux : forall (alpha : ord), ord_eqb_eq_aux' alpha.
Proof.
intros.
induction alpha.
- unfold ord_eqb_eq_aux'. intros. destruct beta.
  + auto.
  + inversion H.
- unfold ord_eqb_eq_aux'. intros. destruct beta.
  + inversion H.
  + inversion H.
    * case_eq (ord_eqb alpha1 beta1).
      { intros. unfold ord_eqb_eq_aux' in IHalpha1. specialize IHalpha1 with beta1.
        assert (alpha1 = beta1). { apply IHalpha1. apply H0. } rewrite H2.
        case_eq (beq_nat n n0).
        { intros. assert (n = n0). { apply (nat_eq_beq n n0 H3). } rewrite H4.
          case_eq (ord_eqb alpha2 beta2).
          { intros. assert (alpha2 = beta2). { apply IHalpha2. apply H5. }
            rewrite H6. auto. }
          { intros. rewrite H0 in H1. rewrite H3 in H1. rewrite H5 in H1.
            inversion H1. } }
        { intros. rewrite H0 in H1. rewrite H3 in H1. inversion H1. } }
      { intros. rewrite H0 in H1. inversion H1. }
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




(* ord_add, ord_mult, and ord_exp will all assume normal form *)
(* *)
Fixpoint ord_add (alpha beta : ord) : ord :=
match alpha, beta with
| _, Zero => alpha
| Zero, _ => beta
| cons a n b, cons a' n' b' =>
    (match (ord_ltb a a') with
    | true => beta
    | false =>
      (match (ord_eqb a a') with
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

| cons (cons Zero n Zero) 0 Zero =>
      cons (cons (cons Zero n Zero) 0 Zero) 0 Zero

| cons (cons a n b) n' b' =>
    ord_mult
      (cons (cons (cons a n b) n' Zero) 0 Zero)
      (ord_2_exp b')
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
  reflexivity.
- induction n as [| n' IHn].
  + simpl.
    reflexivity.
  + simpl.
    rewrite <- (plus_n_1 m').
    rewrite plus_assoc.
    reflexivity.
Qed.

Lemma nat_ord_0 : nat_ord 0 = Zero.
Proof. simpl. reflexivity. Qed.


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
  + unfold leq. left. reflexivity.
  + unfold leq. right. apply tail_lt. apply zero_lt.
- unfold leq. right. apply coeff_lt. omega.
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



(* Carry over the ordinal arithmetic results to the e0 type *)
(* *)

Definition e0_ord (alpha : e0) : ord :=
match alpha with
| exist _ alpha' pf => alpha'
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

Definition nat_e0 (n : nat) : e0 := exist nf (nat_ord n) (nf_nat n).

Definition e0_eq (alpha : e0) (beta : e0) : bool :=
  ord_eqb (e0_ord alpha) (e0_ord beta).

Definition e0_lt (alpha : e0) (beta : e0) : bool :=
  ord_ltb (e0_ord alpha) (e0_ord beta).


Lemma nf_add_aux2 : forall (a a' a'' b b' b'' : ord) (n n' n'' : nat),
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

Definition nf_add_aux' (alpha : ord) :=
  forall (beta : ord), nf alpha -> nf beta -> nf (ord_add alpha beta).

Lemma nf_add_aux : forall (alpha : ord), nf_add_aux' alpha.
Proof.
intros.
induction alpha.
- unfold nf_add_aux'.
  intros.
  simpl.
  destruct beta.
  + simpl. apply zero_nf.
  + apply H0.
- unfold nf_add_aux'.
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
              { apply (nf_add_aux2 A1 a'' beta1 A2 b'' beta2 n1 n'' n0) in HeqA.
                destruct HeqA.
                { rewrite H3. inversion H. apply H7. }
                { rewrite H3. apply (ord_ltb_lt _ _ H1). } }
              { apply (nf_add_aux2 A1 a'' beta1 A2 b'' beta2 n1 n'' n0) in HeqA.
                destruct HeqA.
                { rewrite H3. inversion H. apply H7. }
                { rewrite H3. apply (ord_ltb_lt _ _ H1). } } } }
          { inversion H. apply H3. apply H6. }
          { rewrite HeqA. unfold nf_add_aux' in IHalpha2.
            specialize IHalpha2 with (cons beta1 n0 beta2). apply IHalpha2.
            inversion H. apply Zero_nf. apply H7. apply H0. } } }
Qed.

Lemma nf_add : forall (alpha beta : ord),
  nf alpha -> nf beta -> nf (ord_add alpha beta).
Proof. intros. apply (nf_add_aux alpha). apply H. apply H0. Qed.

Lemma nf_multy_aux : forall (a a' b b' : ord) (n n' : nat),
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


Definition add_right_nice (gamma : ord) := forall (alpha beta : ord),
  alpha < beta -> ord_add gamma alpha < ord_add gamma beta.

Definition add_right_nice2 (alpha gamma : ord) := forall (beta : ord),
  alpha < beta -> ord_add gamma alpha < ord_add gamma beta.


Lemma add_right_incr_aux : forall (gamma : ord), add_right_nice gamma.
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
        rewrite ord_ltb_irrefl. rewrite ord_eqb_refl. apply coeff_lt. omega. }

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
          rewrite ord_eqb_refl. apply coeff_lt. omega. } }

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
Proof. apply add_right_incr_aux. Qed.

Lemma add_right_incr_corr : forall (alpha beta : ord),
  Zero < beta -> alpha < ord_add alpha beta.
Proof.
intros.
pose proof (add_right_incr alpha Zero beta H).
rewrite (ord_add_zero alpha) in H0.
apply H0.
Qed.

Definition mult_right_nice (gamma : ord) := 
  gamma = Zero \/ forall (alpha beta : ord),
  alpha < beta -> nf beta -> ord_mult gamma alpha < ord_mult gamma beta.

Definition mult_right_nice2 (alpha gamma : ord) := 
  gamma = Zero \/ forall (beta : ord),
  alpha < beta -> nf beta -> ord_mult gamma alpha < ord_mult gamma beta.

Lemma mult_right_incr_aux : forall (gamma : ord), mult_right_nice gamma.
Proof.
intros.
induction gamma as [| gamma1 IHgamma1 n_gamma gamma2 IHgamma2].
- unfold mult_right_nice. left. auto.
- assert (forall (alpha : ord), mult_right_nice2 alpha
              (cons gamma1 n_gamma gamma2)).
  { intros. induction alpha as [| alpha1 IHalpha1 n_alpha alpha2 IHalpha2].
    { unfold mult_right_nice2. right. intros.
      destruct beta as [| beta1 n_beta beta2].
      { inversion H. }
      { destruct beta1.
        { simpl. destruct gamma1.
          { unfold nat_ord. apply zero_lt. }
          { apply zero_lt. } }
        { simpl. apply zero_lt. } } }
    { unfold mult_right_nice2. right. intros beta H nf_beta.
      destruct beta as [| beta1 n_beta beta2].
      { inversion H. }
      { destruct alpha1.
        { destruct beta1.
          { assert (beta2 = Zero). { inversion nf_beta. auto. inversion H3. }
            rewrite H0 in H. inversion H.
            { inversion H2. }
            { simpl. apply coeff_lt.
              rewrite minus_n_0. rewrite minus_n_0.
              apply mult_right_incr_aux_aux. apply H2. }
            { inversion H2. } }
          { simpl. apply head_lt. apply add_right_incr_corr. apply zero_lt. } }
        { destruct beta1.
          { inversion H. inversion H1. }
          { rewrite nf_multy_aux. rewrite nf_multy_aux.
            { inversion H.
              { apply head_lt. apply add_right_incr. apply H1. }
              { apply coeff_lt. apply H1. }
              { apply tail_lt. unfold mult_right_nice2 in IHalpha2.
                inversion IHalpha2.
                { inversion H9. }
                { apply (H9 beta2).
                  { apply H1. }
                  { apply (nf_hered_third _ _ _ nf_beta). } } } }
            { apply zero_lt. }
            { apply zero_lt. } } } } } }
  unfold mult_right_nice. right. intros alpha. unfold mult_right_nice2 in H.
  specialize H with alpha. destruct H. inversion H. apply H.
Qed.

Lemma mult_left_zero : forall (alpha : ord), ord_mult Zero alpha = Zero.
Proof. intros. destruct alpha; auto. Qed.

Lemma mult_right_incr : forall (alpha beta gamma : ord),
  alpha < beta -> Zero < gamma -> nf beta ->
  ord_mult gamma alpha < ord_mult gamma beta.
Proof.
intros.
pose proof (mult_right_incr_aux gamma).
unfold mult_right_nice in H2.
destruct H2.
- rewrite H2 in H0. inversion H0.
- apply (H2 _ _ H H1).
Qed.



Definition nf_mult_aux' (alpha : ord) := forall (beta : ord),
  nf alpha -> nf beta -> nf (ord_mult alpha beta).

Lemma nf_mult_aux : forall (alpha : ord), nf_mult_aux' alpha.
Proof.
intros.
induction alpha as [| a IHa n b IHb].
- unfold nf_mult_aux'. intros. destruct beta as [| a' n' b'].
  + auto.
  + auto.
- unfold nf_mult_aux'. intros. induction beta as [| a' IHa' n' b' IHb'].
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
           { rewrite nf_multy_aux in H3.
              { inversion H3. inversion H0.
                apply add_right_incr. apply H10. }
              { apply zero_lt. } } } }
      { apply nf_add.
        apply (nf_hered_first a b n H).
        apply (nf_hered_first a' b' n' H0). }
      { rewrite <- H3. apply IHb'. apply (nf_hered_third _ _ _ H0). } } } }
    destruct a' as [| a'' n'' b''].
    { simpl. apply (nf_scalar _ _ _ _ H). }
    { rewrite nf_multy_aux. apply H1. apply zero_lt. }
Qed.

Lemma nf_mult : forall (alpha beta : ord),
  nf alpha -> nf beta -> nf (ord_mult alpha beta).
Proof. intros. apply (nf_mult_aux alpha). apply H. apply H0. Qed.




Lemma one_right_mult_ident : forall (alpha : ord),
  alpha = ord_mult alpha (nat_ord 1).
Proof.
intros.
induction alpha as [| alpha1 IHalpha1 n_alpha alpha2 IHalpha2].
- auto.
- simpl. assert (n_alpha * 1 - 0 = n_alpha). { omega. } rewrite H. auto.
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


Lemma nf_2_exp : forall (alpha : ord), nf alpha -> nf (ord_2_exp alpha).
Proof.
intros alpha nf_alpha.
induction alpha as [| alpha1 IHalpha1 n_alpha alpha2 IHalpha2].
- simpl. apply single_nf. apply zero_nf.
- destruct alpha1 as [| a' n' b'].
  + simpl. apply nf_nat.
  + destruct a' as [| a'' n'' b''].
    * simpl. assert (b' = Zero).
      { apply nf_hered_first in nf_alpha. inversion nf_alpha.
        auto. inversion H2. }
      rewrite H. case n_alpha.
      { case_eq alpha2; intros.
        { repeat apply single_nf. apply zero_nf. }
        { rewrite <- H0. apply nf_mult.
          { repeat apply single_nf. apply zero_nf. }
          { apply IHalpha2. apply (nf_hered_third _ _ _ nf_alpha). } } }
      { intros. apply nf_mult.
        { repeat apply single_nf. apply zero_nf. }
        { apply IHalpha2. apply (nf_hered_third _ _ _ nf_alpha). } }
    * simpl. apply nf_mult.
      { apply single_nf, single_nf. apply (nf_hered_first _ _ _ nf_alpha). }
      { apply IHalpha2. apply (nf_hered_third _ _ _ nf_alpha). }
Qed.

Lemma nat_ord_eq : forall (n m : nat), (n < m)%nat -> nat_ord n < nat_ord m.
Proof.
intros.
induction n; destruct m.
- inversion H.
- simpl. apply zero_lt.
- inversion H.
- simpl. apply coeff_lt. omega.
Qed.




Lemma exp_geq_1 : forall (b : ord), nf b -> Zero < ord_2_exp b.
Proof.
intros b nf_b.
induction b as [| a' IHa' n' b' IHb'].
- simpl. apply zero_lt.
- destruct a' as [| a'' n'' b''].
  + simpl. assert (Zero = nat_ord 0). { auto. } rewrite H.
    apply nat_ord_eq. rewrite plus_n_0.
    pose proof (nat_exp_monot_lem n'). omega.
  + destruct a'' as [| a''' n''' b'''].
    * simpl. assert (b'' = Zero).
      { apply nf_hered_first in nf_b. inversion nf_b. auto. inversion H2. }
      rewrite H. case n'.
      { case_eq b'; intros.
        { apply zero_lt. }
        { rewrite <- H0. apply nf_hered_third in nf_b. apply ord_mult_nonzero.
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
intros.
pose proof (exp_geq_1).
pose proof (ord_mult_exp_monot_aux1).
apply ord_mult_exp_monot_aux2.
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


Theorem ord_2_exp_fp : forall (alpha : ord), nf alpha ->
  alpha < ord_2_exp alpha \/ alpha = cons (nat_ord 1) 0 Zero.
Proof.
intros alpha nf_alpha.
induction alpha as [| a IHa n b IHb].
- left. simpl. apply zero_lt.
- destruct a as [| a' n' b'].
  + left. assert (b = Zero). { inversion nf_alpha. auto. inversion H2. }
    rewrite H. simpl.
    simpl. assert (cons Zero n Zero = nat_ord (S n)). { auto. }
    rewrite H0. apply nat_ord_eq. rewrite plus_n_0.
    apply nat_exp_monot_lem.
  + simpl. destruct a' as [| a'' n'' b''].
    * destruct b' as [| a''' n''' b'''].
      { destruct n.
        { case_eq b; intros.
          { destruct n'.
            { right. auto. }
            { left. apply head_lt, head_lt, zero_lt. } }
          { left. rewrite <- H. apply ord_mult_exp_monot.
            { apply (nf_hered_third _ _ _ nf_alpha). }
            { repeat apply head_lt. apply zero_lt. } } }
        { left. apply ord_mult_exp_monot.
          { apply (nf_hered_third _ _ _ nf_alpha). }
          { repeat apply head_lt. apply omega_exp_incr'. } } }
      { apply nf_hered_first in nf_alpha. inversion nf_alpha. inversion H2. }
    * left. apply ord_mult_exp_monot.
      { apply (nf_hered_third _ _ _ nf_alpha). }
      { repeat apply head_lt. apply omega_exp_incr'. }
Qed.









Definition e0_pf (alpha : e0) : (nf (e0_ord alpha)) :=
match alpha with
| exist _ alpha' pf => pf
end.

Definition e0_add (alpha beta : e0) : e0 :=
  exist nf (ord_add (e0_ord alpha) (e0_ord beta))
    (nf_add (e0_ord alpha) (e0_ord beta) (e0_pf alpha) (e0_pf beta)).

Definition e0_mult (alpha beta : e0) : e0 :=
  exist nf (ord_mult (e0_ord alpha) (e0_ord beta))
    (nf_mult (e0_ord alpha) (e0_ord beta) (e0_pf alpha) (e0_pf beta)).



(* Determine if a formula c follows from some premises based on the
inference rules *)
Fixpoint exchange (c p : formula) : bool :=
  match (c, p) with
  | (lor (lor (lor c b) a) d, lor (lor (lor c' a') b') d') =>
        (eq_f a a') && (eq_f b b') && (eq_f c c') && (eq_f d d')
  | (_,_) => false
end.

Fixpoint contraction (c p : formula) : bool :=
  match (c, p) with
  | (lor a d, lor (lor a' a'') d') =>
        (eq_f a a') && (eq_f a' a'') && (eq_f d d')
  | (_,_) => false
end.

Fixpoint weakening (c p : formula) : bool :=
  match (c, p) with
  | (lor a d, d') => eq_f d d'
  | (_,_) => false
end.

Fixpoint negation (c p : formula) : bool :=
  match (c, p) with
  | (lor (neg (neg a)) d, lor a' d') => (eq_f a a') && (eq_f d d')
  | (_,_) => false
end.

Fixpoint quantification (c p : formula) : bool :=
  match (c, p) with
  | (lor (neg (univ n a)) d, lor (neg a') d') =>
        (eq_f a a') && (eq_f d d') && (transformable a a' n)
  | (_,_) => false
end.

Fixpoint demorgan (c p1 p2 : formula) : bool :=
  match (c, p1, p2) with
  | (lor (neg (lor a b)) d, lor (neg a') d', lor (neg b') d'') =>
      (eq_f a a') && (eq_f b b') && (eq_f d d') && (eq_f d' d'')
  | (_,_,_) => false
end.

(* we define the degree of a cut; if this returns 0 its not a cut *)
Fixpoint cut_degree (c p1 p2 : formula) : nat :=
  match (c, p1, p2) with
  | (lor c d, lor c' a, lor (neg a') d') =>
      (match (eq_f a a' && eq_f c c' && eq_f d d') with
      | true => 1 + (num_conn a)
      | false => 0
      end)
  | (_, _, _) => 0
end.



(*
Defining proof-trees, which are decorated with ordinals as well as formulas.
This allows us to define the infinite-induction rule.
*)
(* *)
Inductive ptree : Type :=
| node : formula -> nat -> e0 -> ptree
| one_prem : formula -> nat -> e0 -> ptree -> ptree
| two_prem : formula -> nat -> e0 -> ptree -> ptree -> ptree
| inf_prem : formula -> nat -> e0 -> (nat -> ptree) -> ptree.

Fixpoint tree_form (t : ptree) : formula :=
match t with
| node f deg alpha => f
| one_prem f deg alpha t' => f
| two_prem f deg alpha t1 t2 => f
| inf_prem f deg alpha g => f
end.

Fixpoint tree_degree (t : ptree) : nat :=
match t with
| node f deg alpha => deg
| one_prem f deg alpha t' => deg
| two_prem f deg alpha t1 t2 => deg
| inf_prem f deg alpha g => deg
end.

Fixpoint tree_ord (t : ptree) : e0 :=
match t with
| node f deg alpha => alpha
| one_prem f deg alpha t' => alpha
| two_prem f deg alpha t1 t2 => alpha
| inf_prem f deg alpha g => alpha
end.


Fixpoint infinite_induction (f : formula) (g : nat -> ptree) : Prop :=
  match f with
  | lor (univ n a) d => forall (m : nat),
          true = transformable_with_list
                  (lor a d) (tree_form (g m)) n [represent m]
  | _ => False
end.


(* Determine if a given ptree is a valid proof tree, with or without
the cut and infinite induction rules. This involves verifying that:
1) Any parent-child pair matches an inference rule
2) The number of connectives in a cut formula is no bigger than the bound b
3) The bound of the subtree(s) are no larger than the bound b
4) The subtree(s) are valid *)
(* *)
Definition node_valid (f : formula) : Prop :=
  match f with
  | atom a => true = correct_a a
  | neg a => (match a with
             | atom a' => true = incorrect_a a'
             | _ => False
              end)
  | _ => False
    end.

Definition one_prem_valid (f : formula) (deg : nat) (alpha : e0)
                          (t' : ptree) : Prop :=

  ((true = (exchange f (tree_form t') || contraction f (tree_form t'))
          /\ alpha = tree_ord t')
  \/
  (true = (weakening f (tree_form t') || negation f (tree_form t')
              || quantification f (tree_form t'))
          /\ gt_e0 alpha (tree_ord t')))

/\ deg >= tree_degree t'.


Definition two_prem_valid (f : formula) (deg : nat) (alpha : e0)
                          (t1 t2 : ptree) : Prop :=

  (true = demorgan f (tree_form t1) (tree_form t2)
  \/ 0 < cut_degree f (tree_form t1) (tree_form t2) < deg)

/\ deg >= tree_degree t1
/\ deg >= tree_degree t2
/\ gt_e0 alpha (tree_ord t1)
/\ gt_e0 alpha (tree_ord t2).


Definition inf_prem_valid (f : formula) (deg : nat) (alpha : e0)
                          (g : nat -> ptree) : Prop :=

infinite_induction f g
/\ forall (n : nat), deg >= tree_degree (g 5)
/\ forall (n : nat), gt_e0 alpha (tree_ord (g n)).


Fixpoint valid (t : ptree) : Prop :=
  match t with
  | node f deg alpha => node_valid f

  | one_prem f deg alpha t' => one_prem_valid f deg alpha t' /\ valid t'

  | two_prem f deg alpha t1 t2 =>
      two_prem_valid f deg alpha t1 t2 /\ valid t1 /\ valid t2

  | inf_prem f deg alpha g =>
      inf_prem_valid f deg alpha g /\ forall (n : nat), valid (g n)
  end.


Definition x : e0 := exist nf Zero Zero_nf.
Definition f_exmp : formula := (atom (equ zero zero)).
Definition t_exmp_0 : ptree := node f_exmp 0 x.

Theorem a : exists (T : ptree), T = node f_exmp 0 x.
Proof.
pose (witness := t_exmp_0).
refine (ex_intro _ witness _).
unfold witness.
unfold t_exmp_0.
reflexivity.
Qed.


(* Axiom of induction up to epsilon_0 *)
(* *)
(*
Axiom transfinite_induction_e0 :=
*)






(* Exercise 1 *)
(* *)



(* Lemma 1 *)
(* *)
Definition nat_e0 (n : nat) : e0 :=



Lemma nat_e0 : forall (n : nat)


Theorem lemma_1 : forall (A : formula) (n : nat), n = (num_conn A) ->
    exists (t : ptree), (tree_form T = (lor (neg A lor A)))
                    /\  (leq_e0 (tree_ord T) 






