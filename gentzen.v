Require Import Omega.
Require Import Arith.

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

Fixpoint lt_nat (n m : nat) : bool := (bgeq_nat m n) && negb (beq_nat n m).

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

Compute length [1+5,2,3].


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

Compute remove_dups [5, 4, 5].
Compute remove_dups [1, 2, 1, 2].


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


Theorem ordinal_transitivity : forall (alpha : ord), transitive alpha.
Proof.
intros.
induction alpha as [| a IHa n b IHb].
- unfold transitive.
  intros.
  destruct gamma as [| a'' n'' b''].
  * inversion H.
  * apply zero_lt.
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
Fixpoint ord_eqb (alpha : ord) (beta : ord) : bool :=
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

Fixpoint ord_ltb (alpha : ord) (beta : ord) : bool :=
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

Definition ord_semiconnex_bool_aux' (alpha : ord) :=
  forall (beta : ord), alpha < beta -> ord_ltb alpha beta = true.

Lemma ord_semiconnex_bool_aux :
  forall (alpha : ord), ord_semiconnex_bool_aux' alpha.
Proof.
intros.
induction alpha.
- unfold ord_semiconnex_bool_aux'.
  intros.
  destruct beta.
  + inversion H.
  + simpl. auto.
- unfold ord_semiconnex_bool_aux'.
  intros.
  destruct beta.
  + inversion H.
  + inversion H.
    * unfold ord_semiconnex_bool_aux' in IHalpha1. simpl.
      specialize IHalpha1 with beta1.
      apply IHalpha1 in H1.
      rewrite H1. auto.
    * simpl. case (ord_ltb beta1 beta1). auto. simpl.
      assert (ord_eqb beta1 beta1 = true). { admit. }
      rewrite H7.
      assert rewrite H1.





Lemma ord_semiconnex_bool_aux : forall (alpha beta : ord),
  alpha < beta -> ord_ltb alpha beta = true.
Proof.
intros.
induction alpha.
- inversion H. simpl. auto.
- simpl.


induction alpha.
- destruct beta.
  + inversion H.



Lemma ord_semiconnex_bool : forall (alpha beta : ord),
  ord_ltb alpha beta = true \/ ord_ltb beta alpha = true \/
  ord_eqb alpha beta = true.
Proof.
intros.
pose proof (ordinal_semiconnex alpha).
unfold semiconnex in H.
specialize H with beta.
inversion H.
- left.




(* ord_succ, ord_add, and ord_mult will all assume normal form *)
(* *)
Fixpoint ord_succ (alpha : ord) : ord :=
  match alpha with
  | Zero => nat_ord 1
  | cons Zero n b => cons Zero (S n) b
  | cons a n b => cons a n (ord_succ b)
  end.

Fixpoint ord_add (alpha : ord) (beta : ord) : ord :=
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

Fixpoint ord_mult_by_n (alpha : ord) (m : nat) : ord :=
match alpha with
| Zero => Zero
| cons Zero n b => nat_ord ((n + 1) * m)
| cons a n b => 
    (match m with
    | 0 => Zero
    | _ => cons a ((n + 1) * m - 1) (ord_mult_by_n b m)
    end)
end.

Fixpoint ord_mult (alpha : ord) (beta : ord) : ord :=
match alpha, beta with
| _, Zero => Zero
| Zero, _ => Zero
| cons a n b, cons Zero n' b' => ord_mult_by_n alpha (n' + 1)
| cons a n b, cons a' n' b' => cons (ord_add a a') n' (ord_mult alpha b')
end.

(* Here we show that addition and multiplication for ordinal numbers
agrees with the usual definitions for natural numbers *)
(* *)
Lemma ord_add_zero : forall (alpha : ord), ord_add alpha Zero = alpha.
Proof.
intros alpha.
destruct alpha.
- simpl. reflexivity.
- simpl. reflexivity.
Qed.

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

Lemma ord_mult_succ : forall (n m : nat),
  ord_mult (nat_ord n) (ord_succ (nat_ord m)) = nat_ord (n * (S m)).
Proof.
intros n m.
induction n as [| n' IH].
- simpl.
  destruct m.
  + simpl. reflexivity.
  + simpl. reflexivity.
- simpl.
  destruct m.
  + simpl.
    rewrite mult_1_r.
    rewrite mult_1_r.
    rewrite plus_n_1.
    simpl.
    reflexivity.
  + simpl.
    assert ((n' + 1) * S (m + 1) = S (S (m + n' * S (S m)))) as aux. { ring. }
    rewrite aux.
    simpl.
    reflexivity.
Qed.

Lemma ord_succ_nat : forall (n : nat),
  nat_ord (S n) = ord_succ (nat_ord n).
Proof.
intros n.
induction n.
- simpl. reflexivity.
- simpl. reflexivity.
Qed.

Lemma ord_mult_nat : forall (n m : nat),
  nat_ord (n * m) = ord_mult (nat_ord n) (nat_ord m).
Proof.
intros n m.
induction m as [| m' IH].
- rewrite nat_ord_0.
  rewrite mult_0_r.
  rewrite nat_ord_0.
  destruct n.
  + simpl. reflexivity.
  + simpl. reflexivity.
- rewrite ord_succ_nat.
  rewrite ord_mult_succ.
  reflexivity.
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

Lemma zero_minimal : forall (alpha : ord), ~ (alpha < Zero).
intros alpha.
destruct alpha as [Zero | a n b].
- apply lt_irrefl.
- intros H. inversion H.
Qed.

Lemma nf_cons_decr : forall (a a' b b' : ord) (n n' : nat),
  nf (cons a n (cons a' n' b')) -> cons a' n' b' < cons a n b.
Proof.
intros a a' b b' n n' H.
inversion H.
apply head_lt.
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

(* lt is a strict total order *)
(* *)
Lemma lt_strict : forall (alpha beta : ord),
  alpha < beta -> ~ (alpha = beta).
Proof.
intros alpha beta H_a H_b.
destruct alpha as [Zero | a n b].
- rewrite <- H_b in H_a. inversion H_a.
- rewrite H_b in H_a. apply lt_irrefl in H_a. inversion H_a.
Qed.

Lemma lt_trans : forall (alpha beta gamma : ord),
  alpha < beta -> beta < gamma -> alpha < gamma.
Admitted.


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

Lemma lt_asymm : forall (alpha beta : ord),
  alpha < beta -> (~(beta < alpha) /\ ~(alpha = beta)).
Proof.
intros alpha beta H.
split.
- intros H0.
  pose proof (lt_trans alpha beta alpha H H0).
  apply (lt_irrefl alpha H1).
- intros H0.
  rewrite H0 in H.
  apply (lt_irrefl beta H).
Qed.



Lemma nf_add_one : forall (alpha : ord),
  nf alpha -> ord_succ alpha = ord_add alpha (cons Zero 0 Zero).
Proof.
intros alpha nf_alpha.
induction alpha as [Zero | a IHa n b IHb].
- simpl. reflexivity.
- destruct a as [Zero | a' n' b'].
  + simpl. assert (S n = n + 0 + 1). { omega. } rewrite H.
    assert (b = Zero).
    { inversion nf_alpha. reflexivity. inversion H3. }
    rewrite H0. reflexivity.
  + simpl. rewrite IHb. reflexivity. inversion nf_alpha.
    * apply Zero_nf.
    * apply H4.
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

Lemma nf_succ : forall (alpha : ord), nf alpha -> nf (ord_succ alpha).
Proof.
intros alpha H.
induction alpha as [Zero | a IHa n b IHb].
- simpl. apply single_nf. apply Zero_nf.
- destruct b as [Zero | a' n' b'].
  + destruct a as [Zero | a' n' b'].
    * simpl. apply single_nf. apply Zero_nf.
    * inversion H. simpl. apply cons_nf.
        { apply zero_lt. }
        { apply H1. }
        { apply single_nf. apply Zero_nf. }
  + destruct a as [Zero | a'' n'' b''].
    * simpl. inversion H. inversion H3.
    * assert (ord_succ (cons (cons a'' n'' b'') n (cons a' n' b')) = 
                    (cons (cons a'' n'' b'') n (ord_succ (cons a' n' b')))).
      { simpl. reflexivity. }
      rewrite H0.
      destruct a' as [Zero | a''' n''' b'''].
      { simpl. apply cons_nf.
        { apply zero_lt. }
        { inversion H. apply H7. }
        { inversion H. inversion H8.
          { apply single_nf. apply Zero_nf. }
          rewrite <- H11 in H8.
          inversion H8.
          inversion H12. }
      }
      { assert (nf (ord_succ (cons (cons a''' n''' b''') n' b'))).
        { apply IHb. inversion H. apply H8. }
          apply cons_nf.
        { inversion H. apply H5. }
        { inversion H. apply H8. }
        { apply H1. }
      }
Qed.

Lemma ord_add_aux : forall (a a' a'' b b' b'' : ord) (n n' n'' : nat),
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

Definition normal_add (alpha : ord) :=
  forall (beta : ord), nf alpha -> nf beta -> nf (ord_add alpha beta).

Lemma nf_add : forall (alpha : ord), normal_add alpha.
Proof.
intros.
induction alpha.
- unfold normal_add.
  intros.
  simpl.
  destruct beta.
  + simpl. apply zero_nf.
  + apply H0.
- unfold normal_add.
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
      { assert (ord_ltb beta1 alpha1 = true). { admit. }
        remember (ord_add alpha2 (cons beta1 n0 beta2)) as A.
        destruct A.
        { apply single_nf. inversion H. apply H3. apply H6. }
        { apply cons_nf.
          { destruct alpha2 as [| a'' n'' b''].
            { simpl in HeqA. assert (A1 = beta1). { inversion HeqA. auto. }
              rewrite H2. admit. }
            { destruct (ordinal_trichotomy a'' beta1).
              { apply (ord_add_aux A1 a'' beta1 A2 b'' beta2 n1 n'' n0) in HeqA.
                destruct HeqA.
                { rewrite H3. inversion H. apply H7. }
                { rewrite H3. admit. } }
              { apply (ord_add_aux A1 a'' beta1 A2 b'' beta2 n1 n'' n0) in HeqA.
                destruct HeqA.
                { rewrite H3. inversion H. apply H7. }
                { rewrite H3. admit. } } } }
          { inversion H. apply H3. apply H6. }
          { rewrite HeqA. unfold normal_add in IHalpha2.
            specialize IHalpha2 with (cons beta1 n0 beta2). apply IHalpha2.
            inversion H. apply Zero_nf. apply H7. apply H0. }


Lemma ord_trich : forall (alpha beta : ord),
  


Lemma nf_mult_by_n : forall (alpha : ord) (m : nat),
  nf alpha -> nf (ord_mult_by_n alpha m).
Admitted.


Lemma nf_mult : forall (alpha beta : ord),
  nf alpha -> nf beta -> nf (ord_mult alpha beta).
Admitted.

Definition e0_pf (alpha : e0) : (nf (e0_ord alpha)) :=
match alpha with
| exist _ alpha' pf => pf
end.

Definition e0_succ (alpha : e0) : e0 :=
  exist nf (ord_succ (e0_ord alpha)) (nf_succ (e0_ord alpha) (e0_pf alpha)).

Definition e0_add (alpha beta : e0) : e0 :=
  exist nf (ord_add (e0_ord alpha) (e0_ord beta))
    (nf_add (e0_ord alpha) (e0_ord beta) (e0_pf alpha) (e0_pf beta)).

Definition e0_mult_by_n (alpha : e0) (m : nat) : e0 :=
  exist nf (ord_mult_by_n (e0_ord alpha) m)
    (nf_mult_by_n (e0_ord alpha) m (e0_pf alpha)).

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
Axiom stuff 

Axiom transfinite_induction_e0        :=
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









