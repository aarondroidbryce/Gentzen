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




(* Defining ordinals *)
(* *)

(** cons a n b represents  omega^a *(S n)  + b *)

Inductive ord : Set :=
  Zero : ord
| cons : ord -> nat -> ord -> ord.

Definition finite (n:nat) : ord :=
 match n with  0 => Zero
             | S p => cons Zero p Zero
         end.

Notation "'F' n" := (finite n)(at level 29) : cantor_scope.

(* A total strict order on ord *)

Open Scope cantor_scope.

Inductive lt : ord -> ord -> Prop :=
|  zero_lt : forall a n b, Zero < cons a n b
|  head_lt :
    forall a a' n n' b b', lt a a' ->
                           cons a n b < cons a' n' b'
|  coeff_lt : forall a n n' b b', (n < n')%nat ->
                                 cons a n b < cons a n' b'
|  tail_lt : forall a n b b', b < b' ->
                             cons a n b < cons a n b'
where  "o < o'" := (lt o o') : cantor_scope.



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

Definition e_0 : Type := {a : ord | nf a}.


Theorem Zero_nf : nf Zero.
Proof. apply zero_nf. Qed.

Check exist nf Zero Zero_nf.



Check exist.
Check exist nf.


(*
Check (Zero Zero_nf).
*)


(* Defining formula trees *)
(* *)

(*
Each tree will get a bound b on the degree of any cuts within its
*)
Inductive ftree : Type :=
| node : formula -> nat -> ftree
| one_prem : formula -> nat -> ftree -> ftree
| two_prem : formula -> nat -> ftree -> ftree -> ftree
| inf_prem : formula -> nat -> (nat -> ftree) -> ftree.

Fixpoint root_f (t : ftree) : formula :=
match t with
| node f n => f
| one_prem f n t' => f
| two_prem f n t1 t2 => f
| inf_prem f n g => f
end.

Fixpoint bound (t : ftree) : nat :=
match t with
| node f n => n
| one_prem f n t' => n
| two_prem f n t1 t2 => n
| inf_prem f n g => n
end.

(* Determine if a formula c follows from some premises based on the
inference rules *)
Fixpoint demorgan (c p1 p2 : formula) : bool :=
  match (c, p1, p2) with
  | (lor (neg (lor a b)) d, lor (neg a') d', lor (neg b') d'') =>
      (eq_f a a') && (eq_f b b') && (eq_f d d') && (eq_f d' d'')
  | (_,_,_) => false
end.

Fixpoint cut (c p1 p2 : formula) : bool :=
  match (c, p1, p2) with
  | (lor c d, lor c' a, lor (neg a') d') =>
        (eq_f a a') && (eq_f c c') && (eq_f d d')
  | (_, _, _) => false
end.

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

Fixpoint infinite_induction (c : formula) (f : nat -> ftree) : Prop :=
  match c with
  | lor (univ n a) d => forall (m : nat),
          true = transformable_with_list
                  (lor a d) (root_f (f m)) n [represent m]
  | _ => False
end.


(* Determine if a given ftree is a valid proof tree, with or without
the cut and infinite induction rules. This involves verifying that:
1) Any parent-child pair matches an inference rule
2) The number of connectives in a cut formula is no bigger than the bound b
3) The bound of the subtree(s) are no larger than the bound b
4) The subtree(s) are valid
 *)
Fixpoint finite_valid (t : ftree) : bool :=
  match t with
  | node f n =>
    (match f with
    | atom a => correct_a a
    | neg a => (match a with
               | atom a' => incorrect_a a'
               | _ => false
                end)
    | _ => false
      end)

  | one_prem f n t' => (exchange f (root_f t')
                        || contraction f (root_f t')
                        || weakening f (root_f t')
                        || negation f (root_f t')
                        || quantification f (root_f t'))
                    && finite_valid t'
                    && bgeq_nat n (num_conn f)
                    && bgeq_nat n (bound t')

  | two_prem f n t1 t2 => demorgan f (root_f t1) (root_f t2)
                    && finite_valid t1
                    && finite_valid t2
                    && bgeq_nat n (num_conn f)
                    && bgeq_nat n (bound t1)
                    && bgeq_nat n (bound t2)

  | inf_prem f g n => false
  end.


Fixpoint cut_free_valid (t : ftree) : Prop :=
  match t with
  | node f n =>
    (match f with
    | atom a => true = correct_a a
    | neg a => (match a with
               | atom a' => true = incorrect_a a'
               | _ => False
                end)
    | _ => False
      end)

  | one_prem f n t' => (true = (exchange f (root_f t')
                                || contraction f (root_f t')
                                || weakening f (root_f t')
                                || negation f (root_f t')
                                || quantification f (root_f t')))
                      /\ cut_free_valid t'
                      /\ n >= bound t'

  | two_prem f n t1 t2 =>
                    true = demorgan f (root_f t1) (root_f t2)
                    /\ cut_free_valid t1
                    /\ cut_free_valid t2
                    /\ n >= num_conn f
                    /\ n >= bound t1
                    /\ n >= bound t2

  | inf_prem f n g =>
                    infinite_induction f g
                    /\ forall (m : nat), cut_free_valid (g m)
                    /\ forall (m : nat), n >= bound (g m)
  end.


Fixpoint valid (t : ftree) : Prop :=
  match t with
  | node f n =>
    (match f with
    | atom a => true = correct_a a
    | neg a => (match a with
               | atom a' => true = incorrect_a a'
               | _ => False
                end)
    | _ => False
      end)

  | one_prem f n t' => (true = (exchange f (root_f t')
                                || contraction f (root_f t')
                                || weakening f (root_f t')
                                || negation f (root_f t')
                                || quantification f (root_f t')))
                    /\ valid t'
                    /\ n >= bound t'

  | two_prem f n t1 t2 => true = (demorgan f (root_f t1) (root_f t2)
                                  || (cut f (root_f t1) (root_f t2)
                                      && bgeq_nat n (num_conn f)))
                          /\ valid t1
                          /\ valid t2
                          /\ n >= bound t1
                          /\ n >= bound t2

  | inf_prem f n g =>
                    infinite_induction f g
                    /\ forall (m : nat), valid (g m)
                    /\ forall (m : nat), n >= bound (g m)
  end.


(*
Here we prove some simple lemmas showing that if a tree is valid,
then so are its subtrees
*)

Theorem hered_one : forall (t t' : ftree) (f : formula),
                valid t -> t = one_prem f t' -> valid t'.
Proof.
intros t t' f.
intros H H1.
unfold valid in H.
rewrite H1 in H.
destruct H.
apply H0.
Qed.

Theorem hered_two : forall (t t1 t2 : ftree) (f : formula),
                valid t -> t = two_prem f t1 t2 -> (valid t1 /\ valid t2).
Proof.
intros t t1 t2 f.
intros H H1.
unfold valid in H.
rewrite H1 in H.
destruct H.
apply H0.
Qed.

Theorem hered_inf : forall (t : ftree) (f : formula) (g : nat -> ftree),
                valid t -> t = inf_prem f g -> forall (n : nat), valid (g n).
Proof.
intros t f g.
intros H H1.
unfold valid in H.
rewrite H1 in H.
destruct H.
apply H0.
Qed.

Theorem hered : forall (t t1 t2: ftree) (f : formula) (g : nat -> ftree),
                valid t ->
                (t = one_prem f t1 -> valid t1) /\
                (t = two_prem f t1 t2 -> (valid t1 /\ valid t2)) /\
                (t = inf_prem f g -> forall (n : nat), valid (g n)).
Proof.
intros t t1 t2 f g H.
split.
- intros H1.
  unfold valid in H.
  rewrite H1 in H.
  destruct H.
  apply H0.
- split.
  + intros H1.
    unfold valid in H.
    rewrite H1 in H.
    destruct H.
    apply H0.
  + intros H1.
    unfold valid in H.
    rewrite H1 in H.
    destruct H.
    apply H0.
Qed.

Theorem hered_one' : forall (t : ftree) (f : formula),
                valid (one_prem f t) -> valid t.
Proof.
intros t f.
intros H.
unfold valid in H.
simpl.
destruct H.
apply H0.
Qed.

Theorem hered_two' : forall (t1 t2 : ftree) (f : formula),
                valid (two_prem f t1 t2) -> valid t1.
Proof.
intros t1 t2 f.
intros H.
unfold valid in H.
simpl.
destruct H.
apply H0.
Qed.

Theorem hered_two'' : forall (t1 t2 : ftree) (f : formula),
                valid (two_prem f t1 t2) -> valid t2.
Proof.
intros t1 t2 f.
intros H.
unfold valid in H.
simpl.
destruct H.
apply H0.
Qed.

Definition f_exmp : formula := (atom (equ zero zero)).
Definition t_exmp_0 : ftree := node f_exmp.
Definition t_exmp : ftree := one_prem (lor f_exmp f_exmp) t_exmp_0.

Theorem correct_exmp : true = correct_a (equ zero zero).
Proof.
unfold correct_a.
simpl.
reflexivity.
Qed.

Theorem valid_t_exmp : valid t_exmp.
Proof.
unfold t_exmp.
unfold valid.
simpl.
split.
- tauto.
- apply correct_exmp.
Qed.

Theorem valid_t_exmp_0 : valid t_exmp_0.
Proof.
apply valid_t_exmp.
Qed.

Theorem x : t_exmp = one_prem (lor f_exmp f_exmp) t_exmp_0.
Proof.
tauto.
Qed.

Check x.
Compute x.

Check hered_one t_exmp t_exmp_0 (lor f_exmp f_exmp) valid_t_exmp.

Check hered_one'.

Check hered_one' t_exmp_0 (lor f_exmp f_exmp) valid_t_exmp.


(* Compute degree of an ftree. The degree function demands a proof that the
ftree is valid, then passes its recursive descendents to degree', which doesn't *)
(* *)

(*

Fixpoint degree (t : ftree) : (valid t) -> nat :=
  match t return (valid t -> nat) with
  | node f => fun (p : valid (node f)) => 0

  | one_prem f t' => fun (p : valid (one_prem f t')) =>
                        degree t' (hered_one' t' f p)

  | two_prem f t1 t2 => fun (p : valid (two_prem f t1 t2)) =>
                          (match (cut f (root_f t1) (root_f t2)) with
                          | true =>
                            (match (root_f t1, root_f t2) with
                            | (lor c a, lor (neg a') d) =>
                                max (1 + (num_conn a))
                                  (max (degree t1 (hered_two' t1 t2 f p))
                                       (degree t2 (hered_two'' t1 t2 f p)))
                            | _ => 0
                            end)
                          | false => max (degree t1 (hered_two' t1 t2 f p))
                                         (degree t2 (hered_two'' t1 t2 f p))
                          end)

  | inf_prem f g => fun (p : valid _) => 0
    (* need to deal with maximum cut of infinitely many trees *)

  end.

*)


(*
Fixpoint degree (t : ftree) (p : valid t) : nat :=
  match t with
  | node f => 0
  | one_prem f t' => degree t' (hered_one' t' f p)
  (* how to insert a proof of [t = one_prem f t']? *)
  | two_prem f t1 t2 =>
    (match (cut f (root_f t1) (root_f t2)) with
    | true =>
      (match (root_f t1) with
      | lor c a => 1 + (num_conn a)
      | _ => 0
      end)
    | _ => 0
    end)
  | _ => 0
  end.
*)


(* Defining proof-trees, which are decorated with ordinals as well as formulas *)
(* *)
Inductive ptree : Type :=
| node_p : formula -> e_0 -> ptree
| one_prem_p : formula -> e_0 -> ptree -> ptree
| two_prem_p : formula -> e_0 -> ptree -> ptree -> ptree
| inf_prem_p : formula -> e_0 -> (nat -> ptree) -> ptree.


Fixpoint finite_valid_p (t : ptree) : Prop :=
  match t with
  | node_p f alpha =>
    (match f with
    | atom a => (correct_a a = true) /\ (alpha = (exist nf Zero Zero_nf))
    | neg a => (match a with
               | atom a' => (incorrect_a a' = true)
                            /\ (alpha = (exist nf Zero Zero_nf))
               | _ => False
                end)
    | _ => False
      end)
  | one_prem_p f n t' => ((true = exchange f (root_f t')) \/
                          (true = contraction f (root_f t')) \/
                          (true = weakening f (root_f t')) \/
                          (true = negation f (root_f t')) \/
                          (true = quantification f (root_f t')))






Fixpoint cut_free_valid (t : ftree) : Prop :=
  match t with
  | node f =>
    (match f with
    | atom a => true = correct_a a
    | neg a => (match a with
               | atom a' => true = incorrect_a a'
               | _ => False
                end)
    | _ => False
      end)
  | one_prem f t' => ((true = exchange f (root_f t')) \/
                      (true = contraction f (root_f t')) \/
                      (true = weakening f (root_f t')) \/
                      (true = negation f (root_f t')) \/
                      (true = quantification f (root_f t')))
                    /\ (cut_free_valid t')
  | two_prem f t1 t2 => (true = demorgan f (root_f t1) (root_f t2))
                    /\ (cut_free_valid t1) /\ (cut_free_valid t2)
  | inf_prem f g => (infinite_induction f g)
                    /\ (forall (n : nat), cut_free_valid (g n))
  end.


Fixpoint valid (t : ftree) : Prop :=
  match t with
  | node f =>
    (match f with
    | atom a => true = correct_a a
    | neg a => (match a with
               | atom a' => true = incorrect_a a'
               | _ => False
                end)
    | _ => False
      end)
  | one_prem f t' => ((true = exchange f (root_f t')) \/
                      (true = contraction f (root_f t')) \/
                      (true = weakening f (root_f t')) \/
                      (true = negation f (root_f t')) \/
                      (true = quantification f (root_f t')))
                    /\ (valid t')
  | two_prem f t1 t2 => ((true = demorgan f (root_f t1) (root_f t2)) \/
                         (true = cut f (root_f t1) (root_f t2)))
                        /\ (valid t1) /\ (valid t2)
  | inf_prem f g => (infinite_induction f g)
                    /\ (forall (n : nat), valid (g n))
  end.







Inductive ptree : Type :=
| node : formula -> ord -> ptree
| one_prem : formula -> -> ord -> ptree -> ptree
| two_prem : formula -> ord -> ptree -> ptree -> ptree
| inf_prem : formula -> ord -> (nat -> ptree) -> ptree.

Fixpoint root_form (t : ptree) : formula :=
match t with
| node f a | one_prem f a t' | two_prem f a t1 t2 | inf_prem f a g => f
end.

Fixpoint root_ord (t : ptree) : ord :=
match t with
| node f a | one_prem f a t' | two_prem f a t1 t2 | inf_prem f a g => a
end.


Fixpoint finite_valid_p (t : ptree) : bool :=
  match t with
  | node f a =>
    (match f with
    | atom a => correct_a a
    | neg a => (match a with
               | atom a' => incorrect_a a'
               | _ => false
                end)
    | _ => false
      end)
  | weak_one_prem f t' => ((exchange f (root_f t')) || (contraction f (root_f t'))
                    && (finite_valid_p t') && (leq_ord a (root_ord t'))

  | strong_one_prem f t' => ((exchange f (root_f t')) || (contraction f (root_f t'))
                      || (weakening f (root_f t')) || (negation f (root_f t'))
                        || (quantification f (root_f t')))
                    && (finite_valid_p t')

  | two_prem f t1 t2 => demorgan f (root_f t1) (root_f t2)
                    && (finite_valid t1) && (finite_valid t2)
  | inf_prem f g => false
  end.





