Add LoadPath "theories/Casteran" as Ordering.
Add LoadPath "theories/Maths" as Maths_Facts.
Add LoadPath "theories/Logic" as Systems.

Require Import Lia.
Require Import Nat.
Require Import Wellfounded.
From Ordering Require Import rpo.
From Maths_Facts Require Import naturals.
From Systems Require Import definitions.
From Systems Require Import fol.
From Systems Require Import proof_trees.
From Systems Require Import substitute.
Notation "b1 && b2" := (andb b1 b2).
Notation "b1 || b2" := (orb b1 b2).
Notation eq_nat := Nat.eqb.



  (*
###############################################################################
Section 12: Here we define the cut_elimination algorithm.
This is a complicated operation on ptrees, and we will define the many cases
separately before piecing them together.
###############################################################################
*)


(* Defining cut_elimination_0, the case where the ordinal alpha = 0 *)
(* *)

























(*
###############################################################################
Section 13: The consistency of PA
###############################################################################
*)
Fixpoint disjunction_of (A E : formula) : bool :=
match A with
| lor B C0 =>
  (match eq_f B E, eq_f C0 E with
  | true, true => true
  | true, false => disjunction_of C0 E
  | false, true => disjunction_of B E
  | false, false => disjunction_of B E && disjunction_of C0 E
  end)
| _ => eq_f A E
end.

Definition danger : formula := atom (equ zero (succ zero)).

Definition dangerous_disjunct (A : formula) : bool := disjunction_of A danger.
