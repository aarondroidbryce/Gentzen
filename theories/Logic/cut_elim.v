Add LoadPath "theories/Casteran" as Ordering.
Add LoadPath "theories/Maths" as Maths_Facts.
Add LoadPath "theories/Logic" as Systems.

Require Import Lia.
Require Import Nat.
From Maths_Facts Require Import naturals.
From Maths_Facts Require Import ordinals.
From Systems Require Import definitions.
From Systems Require Import fol.
From Systems Require Import PA_omega.
From Systems Require Import proof_trees.
From Systems Require Import substitute.

From Systems Require Import formula_sub.
From Systems Require Import inverse_neg.
From Systems Require Import inverse_dem_1.
From Systems Require Import inverse_dem_2.
From Systems Require Import inverse_omega.
From Systems Require Import inverse_quantif.


Notation "b1 && b2" := (andb b1 b2).
Notation "b1 || b2" := (orb b1 b2).
Notation eq_nat := Nat.eqb.

(*
Definition cut_elimination_0 (P : ptree) : ptree :=
match P with
| ord_up alpha P' => P'
| deg_up d P' => P'
| _ => P
end.
*)

(* Defining cut_elimination_atom, the case where the cut formula is atom a *)
(* *)
Fixpoint cut_elimination_atom (P : ptree) : ptree :=
match P with
| cut_ca C (atom a) d1 d2 alpha1 alpha2 P1 P2 =>
  (match PA_omega_axiom (atom a) with
  | true =>
      formula_sub_ptree P2 (neg (atom a)) C (1)
  | false =>
      contraction_a
        C d1 alpha1
        (formula_sub_ptree P1 (atom a) C (lor_ind (non_target C) (1)))
  end)

| cut_ad (atom a) D d1 d2 alpha1 alpha2 P1 P2 =>
  (match PA_omega_axiom (atom a) with
  | true =>
      contraction_a
        D d2 alpha2
        (formula_sub_ptree P2 (neg (atom a)) D (lor_ind (1) (non_target D)))
  | false =>
      formula_sub_ptree P1 (atom a) D (1)
  end)

| cut_cad C (atom a) D d1 d2 alpha1 alpha2 P1 P2 =>
  (match PA_omega_axiom (atom a) with
  | true =>
      weakening_ad C D d2 alpha2
        (contraction_a
          D d2 alpha2
          (formula_sub_ptree P2 (neg (atom a)) D (lor_ind (1) (non_target D))))
  | false =>
      exchange_ab
        D C d1 (ord_succ alpha1)
        (weakening_ad
          D C d1 alpha1
          (contraction_a
            C d1 alpha1
            (formula_sub_ptree P1 (atom a) C (lor_ind (non_target C) (1)))))
  end)
| deg_up d P' => cut_elimination_atom P'
| ord_up alpha P' => cut_elimination_atom P'
| _ => P
end.


(* Defining cut_elimination_neg, the case where the cut formula is ~E *)
(* *)
Fixpoint cut_elimination_neg (P : ptree) : ptree :=
match P with
| cut_ca C (neg E) d1 d2 alpha1 alpha2 P1 P2 =>
    cut_ad
      E C d2 d1 alpha2 alpha1
      (dub_neg_sub_ptree P2 E (1))
      (exchange_ab C (neg E) d1 alpha1 P1)

| cut_ad (neg E) D d1 d2 alpha1 alpha2 P1 P2 =>
    cut_ca
      D E d2 d1 alpha2 alpha1
      (exchange_ab
        E D d2 alpha2
        (dub_neg_sub_ptree P2 E (lor_ind (1) (non_target D))))
      P1

| cut_cad C (neg E) D d1 d2 alpha1 alpha2 P1 P2 =>
    exchange_ab
      D C (ptree_deg (cut_cad
      D E C d2 d1 alpha2 alpha1
      (exchange_ab
      E D d2 alpha2
        (dub_neg_sub_ptree P2 E (lor_ind (1) (non_target D))))
          (exchange_ab C (neg E) d1 alpha1 P1))) (ptree_ord P)
        (cut_cad
          D E C d2 d1 alpha2 alpha1
          (exchange_ab
          E D d2 alpha2
            (dub_neg_sub_ptree P2 E (lor_ind (1) (non_target D))))
              (exchange_ab C (neg E) d1 alpha1 P1))
| deg_up d P' => cut_elimination_neg P'
| ord_up alpha P' => cut_elimination_neg P'
| _ => P
end.


(* Defining cut_elimination_lor, the case where the cut formula is E \/ F *)
(* *)
Definition associativity_1' (P : ptree) : ptree :=
match ptree_formula P, ptree_deg P, ptree_ord P with
| lor (lor C A) B, d, alpha =>
    exchange_ab
      (lor A B) C d alpha
      (exchange_cab
        A C B d alpha
        (exchange_abd C A B d alpha P))

| _, _, _ => P
end.

Definition associativity_2' (P : ptree) : ptree :=
match ptree_formula P, ptree_deg P, ptree_ord P with
| lor C (lor A B), d, alpha =>
    exchange_abd
      A C B d alpha
      (exchange_cab
        A B C d alpha
        (exchange_ab C (lor A B) d alpha P))

| _, _, _ => P
end.

Lemma associativity1_valid :
    forall (P : ptree),
        valid P ->
            valid (associativity_1' P).
Proof.
intros P PV.
unfold associativity_1'.
destruct (ptree_formula P) eqn:PF;
try apply PV.
destruct f1;
try apply PV.
repeat split.
apply PF.
apply PV.
Qed.

Lemma associativity2_valid :
    forall (P : ptree),
        valid P ->
            valid (associativity_2' P).
Proof.
intros P PV.
unfold associativity_2'.
destruct (ptree_formula P) eqn:PF;
try apply PV.
destruct f2;
try apply PV.
repeat split.
apply PF.
apply PV.
Qed.

Definition contraction_help (P : ptree) : ptree :=
match ptree_formula P, ptree_deg P, ptree_ord P with
| lor (lor C D) E, d, alpha =>
    (match eq_f D E with
    | true =>
        exchange_ab
          D C d alpha
          (contraction_ad
            D C d alpha
            (exchange_cab
              D C D d alpha
              (exchange_abd C D D d alpha P)))

    | false => P
    end)

| _, _, _ => P
end.

Fixpoint cut_elimination_lor (P : ptree) : ptree :=
match P with
| cut_ca C (lor E F) d1 d2 alpha1 alpha2 P1 P2 =>
    cut_ca
      C E
      (max (max d1 d2) (S (num_conn F)))
      d2
      (ord_succ (ord_max alpha1 alpha2))
      alpha2
      (cut_ca (lor C E) F d1 d2 alpha1 alpha2
        (associativity_2' P1)
        (demorgan2_sub_ptree P2 E F (1)))
      (demorgan1_sub_ptree P2 E F (1))

| cut_ad (lor E F) D d1 d2 alpha1 alpha2 P1 P2 =>
    contraction_a
      D
      (max (max d1 d2) (max (S (num_conn E)) (S (num_conn F))))
      (ord_succ (ord_succ (ord_max alpha1 alpha2)))
      (cut_cad
        D E D
        (max (max d1 d2) (S (num_conn F)))
        d2
        (ord_succ (ord_max alpha1 alpha2))
        alpha2
        (exchange_ab
          E D
          (max (max d1 d2) (S (num_conn F)))
          (ord_succ (ord_max alpha1 alpha2))
          (cut_cad
            E F D d1 d2 alpha1 alpha2 P1
            (demorgan2_sub_ptree P2 E F (lor_ind (1) (non_target D)))))
        (demorgan1_sub_ptree P2 E F (lor_ind (1) (non_target D))))

| cut_cad C (lor E F) D d1 d2 alpha1 alpha2 P1 P2 =>
    contraction_help
      (cut_cad
        (lor C D) E D
        (max (max d1 d2) (S (num_conn F)))
        d2
        (ord_succ (ord_max alpha1 alpha2))
        alpha2
        (exchange_cab
          C E D
          (max (max d1 d2) (S (num_conn F)))
          (ord_succ (ord_max alpha1 alpha2))
          (cut_cad (lor C E) F D d1 d2 alpha1 alpha2
            (associativity_2' P1)
            (demorgan2_sub_ptree P2 E F (lor_ind (1) (non_target D)))))
        (demorgan1_sub_ptree P2 E F (lor_ind (1) (non_target D))))

| deg_up d P' => cut_elimination_lor P'
| ord_up alpha P' => cut_elimination_lor P'
| _ => P
end.

(* Define cut_elimination, an operation on ptrees *)
(* *)
Fixpoint cut_elimination (P : ptree) : ptree :=
match P with
| cut_ca C A d1 d2 alpha1 alpha2 P1 P2 =>
  (match A with
  | atom a => cut_elimination_atom P
  | neg E => cut_elimination_neg P
  | lor E F => cut_elimination_lor P
  | univ n E => P
  end)
| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 =>
  (match A with
  | atom a => cut_elimination_atom P
  | neg E => cut_elimination_neg P
  | lor E F => cut_elimination_lor P
  | univ n E => P
  end)
| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2 =>
  (match A with
  | atom a => cut_elimination_atom P
  | neg E => cut_elimination_neg P
  | lor E F => cut_elimination_lor P
  | univ n E => P
  end)
| deg_up d P' => cut_elimination P'
| ord_up alpha P' => cut_elimination P'
| _ => P
end.


(*
###############################################################################
Section 12:
Here we prove that if P is a valid ptree with ordinal alpha and degree d+1,
then cut_elimination(P) is a valid ptree with ordinal 2^alpha and degree d
###############################################################################
*)
(* *)

Theorem cut_elimination_formula :
    forall (P : ptree),
        valid P ->
            ptree_formula (cut_elimination P) = ptree_formula P.
Proof.
intros P PV.
induction P;
unfold cut_elimination, cut_elimination_atom, cut_elimination_neg, cut_elimination_lor; fold cut_elimination.

1,2 : apply IHP;
      apply PV.

all : try reflexivity;
      destruct PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O];
      unfold PA_omega_axiom.

2 : destruct f.
1,6 : destruct f0.
1,5,9 : destruct (correct_a a).

all : unfold ptree_formula;
      fold ptree_formula;
      try reflexivity.

3 : { unfold contraction_help, ptree_formula;
      rewrite eq_f_refl;
      reflexivity. }
2 : { rewrite (formula_sub_ptree_formula_atom P1 a f0 P1V (1)).
      rewrite P1F.
      apply formula_sub_ind_1.
      unfold subst_ind_fit.
      reflexivity. }

1 : { rewrite (formula_sub_ptree_formula_neg P2 a f P2V (1));
      rewrite P2F.
      apply formula_sub_ind_1.
      unfold subst_ind_fit.
      reflexivity. }
Qed.



Theorem cut_elimination_ord :
    forall (P : ptree),
        valid P ->
            ord_ltb (ord_2_exp (ptree_ord P)) (ptree_ord (cut_elimination P)) = false.
Proof.
intros P PV.
pose (ptree_ord P) as alpha.
pose proof (ptree_ord_nf _ PV) as Na.
induction P;
unfold cut_elimination, cut_elimination_atom, cut_elimination_neg, cut_elimination_lor; fold cut_elimination.

1 : destruct PV as [ID PV].
2 : destruct PV as [[IO PV] NO].
4-9 : destruct PV as [[[PF PV] PD] PO].
10 :  destruct PV as [[[[PF FC] PV] PD] PO].
11,12 : destruct PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].
13-16 : destruct PV as [[[PF PV] PD] PO].
19-21 : destruct PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].

2 : { fold cut_elimination cut_elimination_atom cut_elimination_neg cut_elimination_lor. fold cut_elimination.
      unfold ptree_ord; fold ptree_ord.
      pose proof (IHP PV (ptree_ord_nf _ PV)) as IHPV.
      destruct (ord_semiconnex_bool (ord_2_exp (ptree_ord P)) (ptree_ord (cut_elimination P))) as [LT | [ GT | EQ]].
    + rewrite LT in IHPV.
      inversion IHPV.
    + apply (ltb_asymm _ _ (ord_ltb_trans _ _ _ GT (ord_lt_ltb _ _ (ord_2_exp_monot _ NO _ (ptree_ord_nf _ PV) IO)))).
    + apply ord_eqb_eq in EQ.
      destruct EQ.
      apply (ltb_asymm _ _ (ord_lt_ltb _ _ (ord_2_exp_monot _ NO _ (ptree_ord_nf _ PV) IO))). }

1 : { fold cut_elimination cut_elimination_atom cut_elimination_neg cut_elimination_lor. fold cut_elimination.
      unfold ptree_ord; fold ptree_ord.
      apply (IHP PV Na). }

all : unfold ptree_ord in *; fold ptree_ord in *;
      try apply (ord_ltb_exp_false _ Na);
      unfold PA_omega_axiom.

2 : destruct f.
1,6 : destruct f0.
1,5,9 : destruct (correct_a a).

all : unfold contraction_help, ptree_formula, ptree_ord;
      try rewrite eq_f_refl;
      try rewrite formula_sub_ptree_ord_atom;
      try rewrite formula_sub_ptree_ord_neg;
      try rewrite P1O in *;
      try rewrite P2O in *;
      try apply P1V;
      try apply P2V;
      fold ptree_ord;
      try apply ord_ltb_exp_false;
      try apply Na.

7,10 : rewrite (ord_max_symm (ptree_ord P2)).
9,10 : rewrite (ord_max_lem2 _ _ (ltb_asymm _ _ (ord_lt_ltb _ _ (ord_max_succ_r _ _)))).
7,9,10 : apply (ord_succ_lt_exp_succ_dub_succ _ (ord_nf_succ _ Na) (ord_lt_ltb _ _ (ord_succ_not_exp_fp _ Na))).

- apply (ltb_asymm _ _  (ord_lt_ltb _ _ (lt_trans _ _ _ (ord_succ_monot _) (ord_succ_lt_exp_succ_max_right _ _ (ptree_ord_nf _ P1V) (ptree_ord_nf _ P2V))))).
- apply (ltb_asymm _ _  (ord_lt_ltb _ _ (lt_trans _ _ _ (ord_succ_monot _) (ord_succ_lt_exp_succ_max_left _ _ (ptree_ord_nf _ P1V) (ptree_ord_nf _ P2V))))).
- apply (ltb_asymm _ _  (ord_lt_ltb _ _ (ord_succ_lt_exp_succ_max_right _ _ (ptree_ord_nf _ P1V) (ptree_ord_nf _ P2V)))).
- apply (ltb_asymm _ _  (ord_lt_ltb _ _ (ord_succ_lt_exp_succ_max_left _ _ (ptree_ord_nf _ P1V) (ptree_ord_nf _ P2V)))).
- apply (ltb_asymm _ _  (ord_lt_ltb _ _ (lt_trans _ _ _ (ord_succ_monot _) (lt_trans _ _ _ (ord_succ_lt_exp_succ_max_right _ _ (ptree_ord_nf _ P1V) (ptree_ord_nf _ P2V)) (ord_2_exp_monot _ Na _ (ord_nf_succ _ Na) (ord_succ_monot _)))))).
- apply (ltb_asymm _ _  (ord_lt_ltb _ _ (lt_trans _ _ _ (ord_succ_monot _) (lt_trans _ _ _ (ord_succ_lt_exp_succ_max_left _ _ (ptree_ord_nf _ P1V) (ptree_ord_nf _ P2V)) (ord_2_exp_monot _ Na _ (ord_nf_succ _ Na) (ord_succ_monot _)))))).
- apply (ltb_asymm _ _  (ord_lt_ltb _ _ (lt_trans _ _ _ (ord_succ_monot _) (ord_succ_not_exp_fp _ Na)))).
Qed.

Theorem cut_elimination_valid :
    forall (P : ptree),
        valid P ->
            valid (cut_elimination P).
Proof.
intros P PV.
pose (ptree_ord P) as alpha.
pose proof (ptree_ord_nf _ PV) as Na.
induction P;
unfold cut_elimination, cut_elimination_atom, cut_elimination_neg, cut_elimination_lor; fold cut_elimination.

1 : destruct PV as [ID PV].
2 : destruct PV as [[IO PV] NO].
4-9 : destruct PV as [[[PF PV] PD] PO].
10 :  destruct PV as [[[[PF FC] PV] PD] PO].
11,12 : destruct PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].
13-16 : destruct PV as [[[PF PV] PD] PO].
19-21 : destruct PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].

1,2 : apply (IHP PV (ptree_ord_nf _ PV)).

17,18,19 : unfold PA_omega_axiom.
19 :  destruct f0; try case (correct_a a) eqn:Ra;
      unfold contraction_help, ptree_formula;
      try rewrite eq_f_refl.
18 : destruct f; try case (correct_a a) eqn:Ra.
17 : destruct f0; try case (correct_a a) eqn:Ra.

all : unfold associativity_1', associativity_2';
      try rewrite P1F;
      try rewrite P2F;
      repeat split;
      unfold ptree_ord, ptree_deg, ptree_formula;
      fold ptree_ord ptree_deg ptree_formula;
      try apply dub_neg_valid;
      try apply demorgan1_valid;
      try apply demorgan2_valid;
      try rewrite (formula_sub_ptree_deg_atom _ _ _ P1V);
      try rewrite (formula_sub_ptree_deg_neg _ _ _ P2V);
      try rewrite (dub_neg_ptree_deg _ _ P2V);
      try rewrite (demorgan1_ptree_deg _ _ _ P2V);
      try rewrite (demorgan2_ptree_deg _ _ _ P2V);
      try rewrite (formula_sub_ptree_ord_atom _ _ _ P1V);
      try rewrite (formula_sub_ptree_ord_neg _ _ _ P2V);
      try rewrite (dub_neg_ptree_ord _ _ P2V);
      try rewrite (demorgan1_ptree_ord _ _ _ P2V);
      try rewrite (demorgan2_ptree_ord _ _ _ P2V);
      try rewrite (formula_sub_ptree_formula_atom _ _ _ P1V);
      try rewrite (formula_sub_ptree_formula_neg _ _ _ P2V);
      try rewrite (dub_neg_ptree_formula _ _ P2V);
      try rewrite (demorgan1_ptree_formula _ _ _ P2V);
      try rewrite (demorgan2_ptree_formula _ _ _ P2V);
      try apply PF;
      try apply P1F;
      try apply P2F;
      try rewrite P1F;
      try rewrite P2F;
      unfold dub_neg_sub_formula, demorgan1_sub_formula, demorgan2_sub_formula, formula_sub_ind, num_conn;
      unfold subst_ind_fit; fold subst_ind_fit;
      unfold formula_sub_ind_fit; fold formula_sub_ind_fit;
      try rewrite non_target_fit;
      try rewrite eq_f_refl;
      unfold "&&";
      try rewrite non_target_sub';
      try apply PV;
      try apply P1V;
      try apply P2V;
      try apply PD;
      try apply P1D;
      try apply P2D;
      try apply PO;
      try apply P1O;
      try apply P2O;
      try apply FC;
      try reflexivity;
      try lia.

10 :  rewrite ord_max_symm;
      reflexivity.

5 : rewrite (ord_max_lem2 _ _ (ltb_asymm _ _ (ord_lt_ltb _ _ (ord_max_succ_r _ _))));
    reflexivity.

all : try apply (formula_sub_valid_atom _ _ _ P1V Ra);
      try apply (formula_sub_valid_neg _ _ _ P2V Ra);
      pose proof (provable_closed' _ _ P1V P1F) as Cfa;
      pose proof (provable_closed' _ _ P2V P2F) as Cf0a0;
      try destruct (and_bool_prop _ _ Cfa) as [Cf Ca];
      try destruct (and_bool_prop _ _ Cf0a0) as [Ca0 Cf0];
      try apply Cf;
      try apply Cf0;
      try rewrite P1F;
      try rewrite P2F;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      try rewrite non_target_fit;
      try reflexivity.
Qed.


Lemma cut_elim_ord_Zero :
    forall (P : ptree) (A : formula) (d : nat),
        P_proves P A (S d) Zero ->
            provable A d (ord_2_exp Zero).
Proof.
unfold provable, P_proves.
intros P.
induction P;
intros A d [[[PF' PV] PD'] PO'];
unfold ptree_deg, ptree_ord, ptree_formula in *;
fold ptree_deg ptree_ord ptree_formula in *.

1 : destruct PV as [ID PV];
    exists (ord_up (ord_2_exp Zero) P).
3 : exists (ord_up (ord_2_exp Zero) (node f)).

1,3 : repeat split;
      unfold ptree_formula;
      try apply PF';
      try destruct PO';
      try apply zero_lt;
      try apply PV;
      try apply nf_2_exp;
      try apply zero_nf;
      unfold ptree_deg; fold ptree_deg;
      lia.
1 : { destruct PV as [[IO PV] NO].
      destruct PO'.
      apply zero_minimal in IO.
      inversion IO. }

7-18 :  try pose proof (ord_succ_non_Zero o) as NZ1;
        try pose proof (ord_succ_non_Zero (ord_max o o0)) as NZ2;
        try pose proof (ord_succ_non_Zero (ord_succ (ord_max o o0))) as NZ3;
        destruct PO';
        inversion NZ1;
        inversion NZ2;
        inversion NZ3.

1-6 : destruct PV as [[[PF PV] PD] PO];
      destruct PF',PO',PD.

1 : destruct (IHP _ _ (PF , PV , PD' , PO)) as [P1 [[[P1F P1V] P1D] P1O]];
    exists (exchange_ab f f0 (ptree_deg P1) (ptree_ord P1) P1).
  
2 : destruct (IHP _ _ (PF , PV , PD' , PO)) as [P1 [[[P1F P1V] P1D] P1O]];
    exists (exchange_cab f f0 f1 (ptree_deg P1) (ptree_ord P1) P1).

3 : destruct (IHP _ _ (PF , PV , PD' , PO)) as [P1 [[[P1F P1V] P1D] P1O]];
    exists (exchange_abd f f0 f1 (ptree_deg P1) (ptree_ord P1) P1).

4 : destruct (IHP _ _ (PF , PV , PD' , PO)) as [P1 [[[P1F P1V] P1D] P1O]];
    exists (exchange_cabd f f0 f1 f2 (ptree_deg P1) (ptree_ord P1) P1).

5 : destruct (IHP _ _ (PF , PV , PD' , PO)) as [P1 [[[P1F P1V] P1D] P1O]];
    exists (contraction_a f (ptree_deg P1) (ptree_ord P1) P1).

6 : destruct (IHP _ _ (PF , PV , PD' , PO)) as [P1 [[[P1F P1V] P1D] P1O]];
    exists (contraction_ad f f0 (ptree_deg P1) (ptree_ord P1) P1).

all : repeat split;
      try apply P1F;
      try apply P1V;
      try apply P1D;
      apply P1O.
Qed.

Lemma height_zero_not_lor :
    forall (P : ptree),
        valid P ->
            Zero = (ptree_ord P) ->
                forall (A B : formula),
                    (ptree_formula P) <> lor A B.
Proof.
intros P PV PO'.
induction P.

1 : destruct PV as [ID PV].
2 : destruct PV as [[IO PV] NO].
4-9 : destruct PV as [[[PF PV] PD] PO].
10 :  destruct PV as [[[[PF FC] PV] PD] PO].
11,12 : destruct PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].
13-16 : destruct PV as [[[PF PV] PD] PO].
19-21 : destruct PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].

all : unfold ptree_ord in PO'; fold ptree_ord in PO'.

1 : { apply (IHP PV PO'). }
1 : { destruct PO'.
      inversion IO. }

1 : { intros A B.
      unfold ptree_formula.
      unfold valid, PA_omega_axiom in PV.
      destruct f;
      discriminate. }

7-18 :  try pose proof (ord_succ_non_Zero o) as NZ1;
        try pose proof (ord_succ_non_Zero (ord_max o o0)) as NZ2;
        try pose proof (ord_succ_non_Zero (ord_succ (ord_max o o0))) as NZ3;
        destruct PO';
        inversion NZ1;
        inversion NZ2;
        inversion NZ3.

all : try assert (ptree_formula P = ptree_formula P) as EQ;
      try reflexivity;
      unfold "<>" in *;
      intros A B PF';
      destruct PO';
      try rewrite PF in *;
      refine (IHP PV PO _ _ EQ).
Qed.


Lemma cut_elim_ord_one :
    forall (P : ptree) (A : formula) (d : nat),
        P_proves P A (S d) (cons Zero 0 Zero) ->
            provable A d (ord_2_exp (cons Zero 0 Zero)).
Proof.
unfold provable, P_proves.
intros P.
induction P;
intros A d [[[PF' PV] PD'] PO'];
unfold ptree_deg, ptree_ord, ptree_formula in *;
fold ptree_deg ptree_ord ptree_formula in *.

1 : destruct PV as [ID PV].
2 : destruct PV as [[IO PV] NO].
4-9 : destruct PV as [[[PF PV] PD] PO].
10 :  destruct PV as [[[[PF FC] PV] PD] PO].
11,12 : destruct PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].
13-16 : destruct PV as [[[PF PV] PD] PO].
18 : destruct (PV czero) as [[[PF PzV] PD] PO].
19-21 : destruct PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].

1 : { exists (ord_up (ord_2_exp (cons Zero 0 Zero)) P).
      repeat split.
      - apply PF'.
      - destruct PO'.
        apply coeff_lt.
        lia.
      - apply PV.
      - apply single_nf.
        apply zero_nf.
      - unfold ptree_deg; fold ptree_deg.
        lia. }

1 : { rewrite <- PO' in *.
      pose proof (ord_lt_one _ IO) as EQ.
      rewrite <- EQ in *.
      unfold P_proves in *.
      destruct (cut_elim_ord_Zero P A _ (PF' , PV , PD' , EQ)) as [P1 [[[P1F P1V] P1D] P1O]].
      exists (ord_up (ord_2_exp (ord_2_exp Zero)) P1).
      repeat split.
      - apply P1F.
      - destruct P1O.
        apply coeff_lt.
        lia.
      - apply P1V.
      - apply single_nf.
        apply zero_nf.
      - unfold ptree_deg; fold ptree_deg.
        lia. }

1 : { inversion PO'. }

9,15,16,18 :  apply ord_succ_one in PO';
              try destruct (ord_max_0 _ _ PO') as [OZ1 OZ2];
              try destruct PO';
              try destruct OZ1,OZ2;
              try pose proof (height_zero_not_lor _ P1V P1O (neg f) f1) as NE1;
              try pose proof (height_zero_not_lor _ P1V P1O f f0) as NE2;
              try pose proof (height_zero_not_lor _ PzV PO (substitution f n (projT1 czero)) f0) as NE3;
              try rewrite P1F in *;
              try rewrite PF in *;
              contradiction.

14 :  { apply ord_succ_one in PO'.
        pose proof (ord_succ_non_Zero (ord_max o o0)) as NE. 
        destruct PO'.
        inversion NE. }

8 : { apply ord_succ_one in PO'.
      try destruct (ord_max_0 _ _ PO') as [OZ1 OZ2].
      try destruct OZ1,OZ2.
      assert (S (pred n) >= ptree_deg P1) as IE1. lia.
      destruct (cut_elim_ord_Zero _ _ _ (P1F, P1V, IE1, P1O)) as [P3 [[[P3F P3V] P3D] P3O]].
      assert (S (pred n0) >= ptree_deg P2) as IE2. lia.
      destruct (cut_elim_ord_Zero _ _ _ (P2F, P2V, IE2, P2O)) as [P4 [[[P4F P4V] P4D] P4O]].
      exists (demorgan_ab f f0 (ptree_deg P3) (ptree_deg P4) (ptree_ord P3) (ptree_ord P4) P3 P4).
      repeat split.
      - apply PF'.
      - apply P3F.
      - apply P3V.
      - apply P4F.
      - apply P4V.
      - unfold ptree_deg; fold ptree_deg.
        lia.
      - destruct P3O,P4O.
        reflexivity. }

7-12 : apply ord_succ_one in PO';
      try destruct (ord_max_0 _ _ PO') as [OZ1 OZ2];
      try destruct OZ1,OZ2;
      try rewrite PD,PO in *;
      try destruct (cut_elim_ord_Zero P _ _ (PF, PV, PD', PO')) as [P1 [[[P1F P1V] P1D] P1O]].

1-6 : try destruct PF',PO';
      try rewrite PD in PD';
      destruct (IHP _ _ (PF , PV , PD' , PO)) as [P1 [[[P1F P1V] P1D] P1O]].

12 :  assert (forall c, P_proves (p c) (substitution f n (projT1 c)) (S d) Zero) as IND.

12 :  destruct PO';
      intros c;
      unfold P_proves;
      destruct (PV c) as [[[PF PcV] PD] PO].

1 : exists (exchange_ab f f0 (ptree_deg P1) (ptree_ord P1) P1).

2 : exists (exchange_cab f f0 f1 (ptree_deg P1) (ptree_ord P1) P1).

3 : exists (exchange_abd f f0 f1 (ptree_deg P1) (ptree_ord P1) P1).

4 : exists (exchange_cabd f f0 f1 f2 (ptree_deg P1) (ptree_ord P1) P1).

5 : exists (contraction_a f (ptree_deg P1) (ptree_ord P1) P1).

6 : exists (contraction_ad f f0 (ptree_deg P1) (ptree_ord P1) P1).

7 : exists (weakening_ad f f0 (ptree_deg P1) (ptree_ord P1) P1).

8 : exists (negation_a f (ptree_deg P1) (ptree_ord P1) P1).

9 : exists (negation_ad f f0 (ptree_deg P1) (ptree_ord P1) P1).

10 : exists (quantification_a f n c (ptree_deg P1) (ptree_ord P1) P1).

11 : exists (quantification_ad f f0 n c (ptree_deg P1) (ptree_ord P1) P1).

13 : exists (w_rule_a f n d (cons Zero 0 Zero) (fun m => projT1(cut_elim_ord_Zero (p m) _ _ (IND m)))).

all : repeat split;
      try destruct (cut_elim_ord_Zero _ _ _ (IND t)) as [P1 [[[P1F P1V] P1D] P1O]];
      try apply PF;
      try apply P1F;
      try apply PV;
      try apply P1V;
      try apply P1D;
      try apply P1O;
      try destruct PF';
      unfold ptree_formula, ptree_ord, ptree_deg;
      fold ptree_formula ptree_ord ptree_deg;
      try destruct P1O;
      try reflexivity;
      try apply FC;
      try lia.
Qed.


(* *)
Definition cut_remove (alpha : ord) : Type :=
    (forall (P : ptree) (A : formula) (d : nat),
        P_proves P A (S d) alpha ->
            provable A d (ord_2_exp alpha)).

Lemma cut_elim_aux0 :
    forall (alpha : ord),
        nf alpha ->
            forall (P : ptree) (A : formula) (d : nat),
                P_proves P A (S d) alpha ->
                    provable A d (ord_2_exp alpha).
Proof.
apply (transfinite_induction cut_remove).
intros alpha NA IND.
unfold cut_remove.
destruct alpha as [| alpha1 n alpha2].

1 : intros P A d PP.
    apply (cut_elim_ord_Zero P _ _ PP).

case (ord_eqb (cons Zero 0 Zero) (cons alpha1 n alpha2)) eqn:EQO.

1 : intros P A d PP.
    apply ord_eqb_eq in EQO.
    destruct EQO.
    apply (cut_elim_ord_one P _ _ PP).
    
assert (ord_lt (cons Zero 0 Zero) (cons alpha1 n alpha2)) as IEO.
{ destruct (ord_semiconnex (cons Zero 0 Zero) (cons alpha1 n alpha2)) as [O1 | [O1 | O1]].
  - apply O1.
  - inversion O1 as [ | a1h a2h a1c a2c a1t a2t LT O1H O2H | a1h a1c a2c a1t a2t LT O1H O2H | a1h a1c a1t a2t LT O1H O2H ];
    inversion LT.
  - destruct O1.
    inversion EQO. }

assert (forall y : ord, nf y -> ord_lt y (cons alpha1 n alpha2) -> forall (P : ptree) (A : formula) (d : nat), P_proves P A d y -> provable A (pred d) (ord_2_exp y)) as IHP_PRED.
{ intros beta NB LT P A d PP.
  destruct d.
  - unfold pred.
    exists (weak_ord_up P (ord_2_exp beta)).
    unfold weak_ord_up.
    destruct PP as [[[PF PV] PD] PO].
    case (ord_ltb (ptree_ord P) (ord_2_exp beta)) eqn:IE;
    repeat split;
    try apply PF;
    try apply PV;
    try apply PD.
    apply (ord_ltb_lt _ _ IE).
    apply (nf_2_exp _ NB).
    destruct PO.
    destruct (ord_2_exp_fp (beta) NB) as [LTB | EQ].
    + apply ord_lt_ltb in LTB.
      rewrite IE in LTB.
      inversion LTB.
    + rewrite EQ.
      reflexivity.
  - apply (IND _ NB LT P _ _ PP). }

intros P.
induction P;
intros A d PP.

all : destruct PP as [[[PF' PV] PD'] PO'];
      unfold ptree_formula, ptree_deg, ptree_ord in *;
      fold ptree_formula ptree_deg ptree_ord in *;
      unfold cut_remove in IND.

1 : destruct PV as [ID PV].
2 : destruct PV as [[IO PV] NO].
4-9 : destruct PV as [[[PF PV] PD] PO].
10 :  destruct PV as [[[[PF FC] PV] PD] PO].
11,12 : destruct PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].
13-16 : destruct PV as [[[PF PV] PD] PO].
17,18 : destruct (PV czero) as [[[PF PzV] PD] PO].
19-21 : destruct PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].

1 : apply IHP;
    repeat split.
    apply PF'.
    apply PV.
    lia.
    apply PO'.

1 : destruct PO'.
    assert (ptree_ord P = ptree_ord P) as EQ. reflexivity.
    destruct (IND (ptree_ord P) (ptree_ord_nf _ PV) IO P A d (PF', PV, PD', EQ)) as [P1 [[[P1F P1V] P1D] P1O]].
    exists (ord_up (ord_2_exp (cons alpha1 n alpha2)) P1).
    repeat split.
    apply P1F.
    destruct P1O.
    apply (ord_2_exp_monot _ NO _ (ptree_ord_nf _ PV) IO).
    apply P1V.
    apply (nf_2_exp _ NO).
    unfold ptree_deg; fold ptree_deg.
    lia.

1 : inversion PO'.

1-6 : destruct PO';
      try rewrite PD in *;
      try destruct (IHP _ _ (PF, PV, PD', PO)) as [P1 [[[P1F P1V] P1D] P1O]].

7 : rewrite PD,PO' in *;
    destruct (IND _ (ord_nf_succ _ NA) (ord_succ_monot _) _ _ _ (PF, PV, PD', PO)) as [P1 [[[P1F P1V] P1D] P1O]].

8,9 : assert (S d >= n0) as IE1;
      assert (S d >= n1) as IE2;
      rewrite P1D,P2D,PO' in *;
      try lia;
      destruct (IND _ (ptree_ord_nf_hyp _ _ P1O P1V) (ord_max_succ_l _ _) _ _ _ (P1F, P1V, IE1, P1O)) as [P3 [[[P3F P3V] P3D] P3O]];
      destruct (IND _ (ptree_ord_nf_hyp _ _ P2O P2V) (ord_max_succ_r _ _) _ _ _ (P2F, P2V, IE2, P2O)) as [P4 [[[P4F P4V] P4D] P4O]].

10-13 : rewrite PD,PO' in *;
        destruct (IND _ (ord_nf_succ _ NA) (ord_succ_monot _) _ _ _ (PF, PV, PD', PO)) as [P1 [[[P1F P1V] P1D] P1O]].

14 :  assert (forall c, P_proves (p c) (substitution f n0 (projT1 c)) (S d) o) as IHP.

14 :  destruct PO';
      intros c;
      unfold P_proves;
      destruct (PV c) as [[[PcF PcV] PcD] PcO].

15 : rewrite PO' in *.

16 : assert (forall m, P_proves (p m) (lor (substitution f n0 (projT1 m)) f0) (S d) o) as IHP.

16 :  destruct PO';
      intros c;
      unfold P_proves;
      destruct (PV c) as [[[PcF PcV] PcD] PcO].

17 : rewrite PO' in *.

1 : exists (exchange_ab f f0 (ptree_deg P1) (ptree_ord P1) P1).

2 : exists (exchange_cab f f0 f1 (ptree_deg P1) (ptree_ord P1) P1).

3 : exists (exchange_abd f f0 f1 (ptree_deg P1) (ptree_ord P1) P1).

4 : exists (exchange_cabd f f0 f1 f2 (ptree_deg P1) (ptree_ord P1) P1).

5 : exists (contraction_a f (ptree_deg P1) (ptree_ord P1) P1).

6 : exists (contraction_ad f f0 (ptree_deg P1) (ptree_ord P1) P1).

7 : exists (ord_up (ord_2_exp (ord_succ o)) (weakening_ad f f0 (ptree_deg P1) (ptree_ord P1) P1)).

8 : exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (demorgan_ab f f0 (ptree_deg P3) (ptree_deg P4) (ord_2_exp o) (ord_2_exp o0) P3 P4)).

9 : exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (demorgan_abd f f0 f1 (ptree_deg P3) (ptree_deg P4) (ord_2_exp o) (ord_2_exp o0) P3 P4)).

10 : exists (ord_up (ord_2_exp (ord_succ o)) (negation_a f (ptree_deg P1) (ptree_ord P1) P1)).

11 : exists (ord_up (ord_2_exp (ord_succ o)) (negation_ad f f0 (ptree_deg P1) (ptree_ord P1) P1)).

12 : exists (ord_up (ord_2_exp (ord_succ o)) (quantification_a f n0 c (ptree_deg P1) (ptree_ord P1) P1)).

13 : exists (ord_up (ord_2_exp (ord_succ o)) (quantification_ad f f0 n0 c (ptree_deg P1) (ptree_ord P1) P1)).

15 : exists (ord_up (ord_2_exp (ord_succ o)) (w_rule_a f n0 d (ord_2_exp o) (fun m => projT1(IND _ (ptree_ord_nf_hyp _ _ PO PzV) (ord_succ_monot _) (p m) _ _ (IHP m))))).

17 : exists (ord_up (ord_2_exp (ord_succ o)) (w_rule_ad f f0 n0 d (ord_2_exp o) (fun m => projT1(IND _ (ptree_ord_nf_hyp _ _ PO PzV) (ord_succ_monot _) (p m) _ _ (IHP m))))).

all : repeat split;
      try destruct IND as [P1 [[[P1F P1V] P1D] P1O]];
      unfold projT1;
      try apply PcF;
      try apply PF';
      try apply P1F;
      try apply P3F;
      try apply P4F;
      try apply PcV;
      try apply P1V;
      try apply P3V;
      try apply P4V;
      try destruct PF';
      unfold ptree_formula, ptree_ord, ptree_deg;
      fold ptree_formula ptree_ord ptree_deg;
      try lia;
      try apply PcO;
      try apply P1O;
      try apply P3O;
      try apply P4O;
      try apply FC;
      try rewrite <- P1O;
      try apply nf_2_exp;
      try apply NA.

1,4-9 : apply ord_succ_lt_exp_succ;
        try apply (ord_nf_succ _ NA);
        try apply (succ_gt_one_gt_zero _ IEO).

1,2 : rewrite ord_max_exp_equiv;
      try apply ord_succ_lt_exp_succ;
      try apply (succ_gt_one_gt_zero _ IEO);
      try apply ord_max_nf;
      try apply (ptree_ord_nf_hyp _ _ P1O P1V);
      try apply (ptree_ord_nf_hyp _ _ P2O P2V).

3 : case (eq_nat (max (max n0 n1) (S (num_conn f0))) (S (num_conn f0))) eqn:E1.
2 : case (eq_nat (max (max n0 n1) (S (num_conn f))) (S (num_conn f))) eqn:E1.
1 : case (eq_nat (max (max n0 n1) (S (num_conn f0))) (S (num_conn f0))) eqn:E1.

1 : { rewrite PO' in *.
      assert (S d >= ptree_deg P1) as IE1;
      assert (S d >= ptree_deg P2) as IE2;
      try lia.
      destruct (IHP_PRED _ (ptree_ord_nf_hyp _ _ P1O P1V) (ord_max_succ_l _ _) P1 _ _ (P1F, P1V, IE1, P1O)) as [T1 [[[T1F T1V] T1D] T1O]].
      destruct (IHP_PRED _ (ptree_ord_nf_hyp _ _ P2O P2V) (ord_max_succ_r _ _) P2 _ _ (P2F, P2V, IE2, P2O)) as [T2 [[[T2F T2V] T2D] T2O]].
      unfold pred in T1D,T2D.

      unfold provable.
      destruct f0.
      - exists (weak_ord_up (cut_elimination (cut_ca f (atom a) (ptree_deg T1) (ptree_deg T2) (ptree_ord T1) (ptree_ord T2) T1 T2)) (ord_2_exp (ord_succ (ord_max o o0)))).
        repeat split;
        try rewrite weak_ord_formula;
        try rewrite weak_ord_deg;
        try apply weak_ord_valid;
        unfold ptree_formula, ptree_deg, ptree_ord, valid;
        fold ptree_formula ptree_deg ptree_ord valid;
        try apply cut_elimination_formula;
        try apply cut_elimination_valid;
        try refine (T1F, T1V, T2F, T2V, _, _, _, _);
        try reflexivity;
        try apply nf_2_exp;
        try apply NA;
        unfold cut_elimination, cut_elimination_atom, PA_omega_axiom, weak_ord_up;
        case (correct_a a) eqn:Ra;
        unfold ptree_deg, ptree_ord; fold ptree_deg ptree_ord;
        try rewrite (formula_sub_ptree_deg_neg _ _ _ T2V);
        try rewrite (formula_sub_ptree_ord_neg _ _ _ T2V);
        try rewrite <- T1O;
        try rewrite <- T2O;
        try rewrite (ord_lt_ltb _ _ (ord_2_exp_monot _ NA _ (ptree_ord_nf_hyp _ _ P2O P2V) (ord_max_succ_r _ _)));
        try rewrite (ord_lt_ltb _ _ (ord_2_exp_monot _ NA _ (ptree_ord_nf_hyp _ _ P1O P1V) (ord_max_succ_l _ _)));
        unfold ptree_ord; fold ptree_ord;
        try lia;
        try reflexivity.
      -


 }


Admitted.      

exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_elimination (cut_ca f (atom a) (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))).
exists (ord_up (ord_2_exp (ord_succ (ord_succ (ord_max o o0)))) (cut_elimination (cut_ad (atom a) f0 (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))).
exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_elimination (cut_cad f (atom a) f1 (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))).

- case (eq_nat (max (max n0 n1) (S (num_conn f0))) (S (num_conn f0))) eqn:E1.
  + assert (P_proves P2 (neg f0) n1 o0) as HP5. repeat split; auto. lia.
    assert (P_proves P1 (lor f f0) n0 o) as HP6. repeat split; auto. lia.
    assert (nf o). rewrite X7. apply ptree_ord_nf. auto.
    assert (nf o0). rewrite X8. apply ptree_ord_nf. auto.
    destruct (IHP_PRED _ H1 (ord_max_succ_l _ _) P1 _ _ HP6) as [PY [[[Y1 Y2] Y3] Y4]].
    destruct (IHP_PRED _ H2 (ord_max_succ_r _ _) P2 _ _ HP5) as [PZ [[[Z1 Z2] Z3] Z4]].
    assert (valid (cut_ca f f0 (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ)) as HYZ. repeat split; auto.
    assert (num_conn f0 <= d). lia.
    assert (ptree_deg PY <= d). lia.
    assert (ptree_deg PZ <= d). lia.
    destruct f0.
    * exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_elimination (cut_ca f (atom a) (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))). 
      case (ord_succ (ord_max (ord_2_exp o) (ord_2_exp o0))) eqn:I1. pose proof (ord_succ_non_Zero (ord_max (ord_2_exp o) (ord_2_exp o0))). rewrite I1 in H6. inversion H6. repeat split; auto.
      --  unfold ptree_formula. fold ptree_formula. rewrite cut_elimination_formula; auto.
      --  simpl. rewrite I1. case (correct_a a) eqn:C.
          ++  rewrite formula_sub_ptree_ord_neg; auto. destruct Z4. apply ord_2_exp_monot; auto. apply ord_max_succ_r.
          ++  simpl. apply ord_2_exp_monot; auto. apply ord_max_succ_l.
      --  apply cut_elimination_valid; auto.
      --  apply nf_2_exp. auto.
      --  simpl. rewrite I1. case (correct_a a) eqn:C.
          { rewrite formula_sub_ptree_deg_neg; auto. }
          { simpl. lia. }
    * exists (weak_ord_up (cut_elimination (cut_ca f (neg f0) (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ)) (ord_2_exp (ord_succ (ord_max o o0)))).
      case (ord_succ (ord_max (ord_2_exp o) (ord_2_exp o0))) eqn:I1. pose proof (ord_succ_non_Zero (ord_max (ord_2_exp o) (ord_2_exp o0))). rewrite I1 in H6. inversion H6. repeat split; auto.
      --  rewrite weak_ord_formula. unfold ptree_formula. fold ptree_formula. rewrite cut_elimination_formula; auto.
      --  apply weak_ord_valid. apply nf_2_exp. auto. apply cut_elimination_valid. auto. 
      --  rewrite weak_ord_deg. simpl. rewrite I1. simpl in *. lia.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (cut_elimination (cut_ca f (neg f0) (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I2; auto.
          simpl. rewrite I1. simpl. destruct (ord_semiconnex_bool (ord_succ (ord_succ (ord_max (ord_2_exp o0) (ord_2_exp o)))) (ord_2_exp (ord_succ (ord_max o o0)))) as [I3 | [I3 |I3]].
          ++  simpl in I2. rewrite I1 in I2. simpl in I2. rewrite I3 in I2. inversion I2.
          ++  simpl in I2. rewrite I1 in I2. simpl in I2. rewrite ord_max_symm in I2. rewrite ord_max_exp_equiv in I2; auto. destruct (ord_max o o0) eqn:O2. inversion O. rewrite <- O2 in *.
              rewrite ord_max_exp_equiv; auto. assert (ord_lt Zero (ord_max o o0)). rewrite O2. apply zero_lt. 
              pose proof (dub_succ_exp_eq _ H6 (ord_max_nf _ _ H1 H2) I2). apply ord_eqb_eq in H7. rewrite (ord_max_symm o0). auto.
          ++  apply ord_eqb_eq in I3. auto.
    * exists (weak_ord_up (cut_elimination (cut_ca f (lor f0_1 f0_2) (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ)) (ord_2_exp (ord_succ (ord_max o o0)))).
      case (ord_succ (ord_max (ord_2_exp o) (ord_2_exp o0))) eqn:I1. pose proof (ord_succ_non_Zero (ord_max (ord_2_exp o) (ord_2_exp o0))). rewrite I1 in H6. inversion H6. repeat split; auto.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (cut_elimination (cut_ca f (lor f0_1 f0_2) (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I2.
          ++  unfold ptree_formula. fold ptree_formula. rewrite cut_elimination_formula; auto.
          ++  unfold ptree_formula. fold ptree_formula. rewrite cut_elimination_formula; auto.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (cut_elimination (cut_ca f (lor f0_1 f0_2) (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I2.
          ++  repeat split; auto.
              **  apply ord_ltb_lt. auto.
              **  apply cut_elimination_valid; auto.
              **  apply nf_2_exp. auto.
          ++  apply cut_elimination_valid; auto.
      --  simpl. rewrite I1. unfold weak_ord_up. case (ord_ltb (ptree_ord (cut_ca f f0_1 (max (max (ptree_deg PY) (ptree_deg PZ)) (S (num_conn f0_2))) (ptree_deg PZ) (cons o1_1 n2 o1_2) (ord_2_exp o0) (cut_ca (lor f f0_1) f0_2 (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) (associativity_2' PY) (demorgan2_sub_ptree PZ f0_1 f0_2 (1))) (demorgan1_sub_ptree PZ f0_1 f0_2 (1)))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I2.
          ++ simpl in *. lia.
          ++ simpl in *. lia.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (cut_elimination (cut_ca f (lor f0_1 f0_2) (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I2; auto.
          simpl. rewrite I1. unfold ptree_ord. rewrite <- I1.
          simpl in I2. rewrite I1 in I2. unfold ptree_ord in I2. rewrite <- I1 in I2.
          rewrite ord_max_lem2. rewrite ord_max_lem2 in I2.
          ++  rewrite ord_max_exp_equiv in *; auto. apply ord_eqb_eq. assert (ord_lt Zero (ord_max o o0)). destruct (ord_max o o0). inversion H0; inversion H7. apply zero_lt. apply (dub_succ_exp_eq _ H6 (ord_nf_succ _ H) I2). 
          ++  apply ltb_asymm. apply ord_lt_ltb. apply ord_max_succ_r.
          ++  apply ltb_asymm. apply ord_lt_ltb. apply ord_max_succ_r.
    * assert (P_proves PY (lor f (univ n2 f0)) (ptree_deg PY) (ord_2_exp o)) as PY1. repeat split; auto.
      assert (max (ptree_deg PY) (ptree_deg PZ) < num_conn f0 + 2).
      { simpl in *. apply nat_eq_decid in E1. lia. }
      assert (max (max (ptree_deg PY) (ptree_deg PZ)) (num_conn f0 + 1) <= d).
      { simpl in *. apply nat_eq_decid in E1. lia. }
      exists (weak_ord_up (neg_w_rule_sub_ptree PZ _ _ _ _ _ _ PY1 (1)) (ord_2_exp (ord_succ (ord_max o o0)))). repeat split; auto.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (neg_w_rule_sub_ptree PZ PY f0 f n2 (ptree_deg PY) (ord_2_exp o) PY1 (1))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I1.
          ++  simpl. rewrite neg_w_rule_ptree_formula; auto. rewrite Z1. unfold neg_w_rule_sub_formula. simpl. rewrite eq_nat_refl. rewrite eq_f_refl. auto.
          ++  rewrite neg_w_rule_ptree_formula; auto. rewrite Z1. unfold neg_w_rule_sub_formula. simpl. rewrite eq_nat_refl. rewrite eq_f_refl. auto.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (neg_w_rule_sub_ptree PZ PY f0 f n2 (ptree_deg PY) (ord_2_exp o) PY1 (1))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I1.
          ++  repeat split. apply ord_ltb_lt. auto. apply neg_w_rule_valid; auto.
              { pose proof (provable_closed' PY _ Y2 Y1). simpl in H7. destruct (and_bool_prop _ _ H8). auto. }
              { rewrite Z1. auto. }
              { apply nf_2_exp. auto. }
          ++  apply neg_w_rule_valid; auto.
              { pose proof (provable_closed' PY _ Y2 Y1). simpl in H7. destruct (and_bool_prop _ _ H8). auto. }
              { rewrite Z1. auto. }
      --  pose proof (neg_w_rule_ptree_deg PZ _ _ _ _ _ _ PY1 Z2 H6 (1)).
          unfold weak_ord_up. case (ord_ltb (ptree_ord (neg_w_rule_sub_ptree PZ PY f0 f n2 (ptree_deg PY) (ord_2_exp o) PY1 (1))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I1; simpl; lia.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (neg_w_rule_sub_ptree PZ PY f0 f n2 (ptree_deg PY) (ord_2_exp o) PY1 (1))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I1; simpl; auto. 
          pose proof (neg_w_rule_ptree_ord PZ _ _ _ _ _ _ PY1 Z2 (1)).
          rewrite Z4 in H8.
          pose proof (ord_trans_inv _ _ _ (ord_add_exp_le_exp_max _ _ H1 H2) H8) as I2.
          destruct (ord_semiconnex_bool (ord_2_exp (ord_succ (ord_max o o0))) (ptree_ord (neg_w_rule_sub_ptree PZ PY f0 f n2 (ptree_deg PY) (ord_2_exp o) PY1 (1)))) as [I3 | [I3 | I3]].
          ++  rewrite I3 in I2. inversion I2.
          ++  rewrite I3 in I1. inversion I1.
          ++  apply ord_eqb_eq in I3. auto. 
    + assert ((S (num_conn f0)) < (max n0 n1)) as E2. rewrite eq_nat_symm in E1. rewrite (nat_eq_decid _ _ (nat_max_right_not _ _ E1)). apply (max_lem2 _ _ E1).
      intros. destruct X0 as [[[X1 X2] X3] X4]. simpl in X1,X3,X4. destruct X4. destruct X2 as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8]. unfold cut_remove in X. case (eq_nat (max (max n0 n1) (S (num_conn f0))) (S d)) eqn:E.
      * assert ((S (num_conn f0)) < (max n0 n1)). rewrite eq_nat_symm in E1. rewrite (nat_eq_decid _ _ (nat_max_right_not _ _ E1)). apply (max_lem2 _ _ E1).
        apply nat_eq_decid in E. case (lt_nat n0 n1) eqn:Y.
        --  rewrite (max_split1 _ _ Y) in E. symmetry in E. destruct E. assert (P_proves P2 (neg f0) (S d) o0). { unfold P_proves. repeat split; simpl; auto. lia. } assert (nf o0). rewrite H8. apply ptree_ord_nf. auto.
            destruct (X _ H10 (ord_max_succ_r _ _) _ _ _ X0) as [P7 [[[HP1 HP2] HP3] HP4]]. exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_ca f f0 n0 (ptree_deg P7) o (ord_2_exp o0) P1 P7)). repeat split; simpl; auto.
            apply ord_max_exp_r; auto. rewrite H7. apply ptree_ord_nf. auto. apply nf_2_exp. auto. apply lt_nat_decid in Y. lia.
        --  case (lt_nat n1 n0) eqn:Y1.
            ++  rewrite (max_split2 _ _ Y1) in E. symmetry in E. destruct E. assert (P_proves P1 (lor f f0) (S d) o). { unfold P_proves. repeat split; simpl; auto. lia. } assert (nf o). rewrite H7. apply ptree_ord_nf. auto.
                destruct (X _ H10 (ord_max_succ_l _ _) _ _ _ X0) as [P6 [[[HP1 HP2] HP3] HP4]]. exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_ca f f0 (ptree_deg P6) n1 (ord_2_exp o) o0 P6 P2)). repeat split; simpl; auto.
                apply ord_max_exp_l; auto. rewrite H8. apply ptree_ord_nf. auto. apply nf_2_exp. auto. apply lt_nat_decid in Y1. lia.
            ++  assert (n0 = n1). destruct (nat_semiconnex n0 n1) as [Y2 | [Y2 | Y2]]; try apply lt_nat_decid_conv in Y2. rewrite Y2 in Y. inversion Y. rewrite Y2 in Y1. inversion Y1. auto. destruct H10. rewrite max_n_n in E. symmetry in E. destruct E.
                assert (P_proves P1 (lor f f0) (S d) o). { unfold P_proves. repeat split; simpl; auto. lia. } assert (nf o). rewrite H7. apply ptree_ord_nf. auto.
                assert (P_proves P2 (neg f0) (S d) o0). { unfold P_proves. repeat split; simpl; auto. lia. } assert (nf o0). rewrite H8. apply ptree_ord_nf. auto.
                destruct (X _ H10 (ord_max_succ_l _ _) _ _ _ X0) as [P6 [[[HP1 Hp2] HP3] HP4]]. destruct (X _ H11 (ord_max_succ_r _ _) _ _ _ X2) as [P7 [[[HQ1 HQ2] HQ3] HQ4]].
                exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_ca f f0 (ptree_deg P6) (ptree_deg P7) (ord_2_exp o) (ord_2_exp o0) P6 P7)). repeat split; simpl; auto.
                apply ord_max_exp_both; auto. apply nf_2_exp. auto. lia.
      * assert (d >= max (max n0 n1) (S (num_conn f0))). { inversion X3. destruct H10. rewrite eq_nat_refl in E. inversion E. lia. } exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_ca f f0 n0 n1 o o0 P1 P2)). repeat split; simpl; auto. apply ord_succ_not_exp_fp. auto. apply nf_2_exp. auto.
- case (eq_nat (max (max n0 n1) (S (num_conn f))) (S (num_conn f))) eqn:E1.
  + intros. inversion X0 as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. destruct HP1. destruct HP4. inversion HP2 as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8].
    assert (P_proves P2 (lor (neg f) f0) n1 o0) as HP5. repeat split; auto. lia. assert (P_proves P1 f n0 o) as HP6. repeat split; auto. lia.
    unfold cut_remove in X.
    assert (forall y : ord, nf y -> ord_lt y (ord_succ (ord_max o o0)) -> forall (P : ptree) (A : formula) (d : nat), P_proves P A d y -> provable A (pred d) (ord_2_exp y)) as IHP_PRED.
    { intros. destruct d0.
      { simpl. exists (weak_ord_up P (ord_2_exp y)). unfold weak_ord_up. destruct X9 as [[[Z1 Z2] Z3] Z4]. case (ord_ltb (ptree_ord P) (ord_2_exp y)) eqn:Y.
        { repeat split; simpl; auto. apply ord_ltb_lt. auto. apply nf_2_exp. auto. }
        { repeat split; simpl; auto. destruct Z4. destruct (ord_2_exp_fp (ptree_ord P)).
          { apply ptree_ord_nf. auto. }
          { apply ord_lt_ltb in H3. rewrite Y in H3. inversion H3. }
          { rewrite H3. auto. } } }
      { simpl. apply (X _ H1 (lt_trans _ _ _ H2 (ord_succ_monot _)) P _ _ X9). } }
    assert (nf o). rewrite X7. apply ptree_ord_nf. auto.
    assert (nf o0). rewrite X8. apply ptree_ord_nf. auto.
    destruct (IHP_PRED _ H1 (ord_max_succ_l _ _) P1 _ _ HP6) as [PY [[[Y1 Y2] Y3] Y4]].
    destruct (IHP_PRED _ H2 (ord_max_succ_r _ _) P2 _ _ HP5) as [PZ [[[Z1 Z2] Z3] Z4]].
    assert (valid (cut_ad f f0 (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ)) as HYZ. repeat split; auto.
    assert (num_conn f <= d). lia.
    assert (ptree_deg PY <= d). lia.
    assert (ptree_deg PZ <= d). lia.
    destruct f.
    * exists (ord_up (ord_2_exp (ord_succ (ord_succ (ord_max o o0)))) (cut_elimination (cut_ad (atom a) f0 (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))). 
      case (ord_succ (ord_succ (ord_max (ord_2_exp o) (ord_2_exp o0)))) eqn:I1. pose proof (ord_succ_non_Zero (ord_succ (ord_max (ord_2_exp o) (ord_2_exp o0)))). rewrite I1 in H6. inversion H6. repeat split; auto.
      --  unfold ptree_formula. fold ptree_formula. rewrite cut_elimination_formula; auto.
      --  simpl. rewrite I1. case (correct_a a) eqn:C.
          ++  simpl. apply ord_2_exp_monot; auto. apply (lt_trans _ _ _ (ord_succ_monot _)). apply ord_lt_succ. apply ord_max_succ_r. 
          ++  rewrite formula_sub_ptree_ord_atom; auto. rewrite Y4. apply ord_2_exp_monot; auto. apply (lt_trans _ _ _ (ord_succ_monot _)). apply ord_lt_succ. apply ord_max_succ_l.
      --  apply cut_elimination_valid; auto.
      --  apply nf_2_exp. repeat apply ord_succ_nf. apply ord_max_nf; auto.
      --  simpl. rewrite I1. case (correct_a a) eqn:C.
          { simpl. lia. }
          { rewrite formula_sub_ptree_deg_atom; auto. }
    * exists (ord_up (ord_2_exp (ord_succ (ord_succ (ord_max o o0)))) (cut_elimination (cut_ad (neg f) f0 (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))).
      case (ord_succ (ord_succ (ord_max (ord_2_exp o) (ord_2_exp o0)))) eqn:I1. pose proof (ord_succ_non_Zero (ord_succ (ord_max (ord_2_exp o) (ord_2_exp o0)))). rewrite I1 in H6. inversion H6. repeat split; auto.
      --  unfold ptree_formula. fold ptree_formula. rewrite cut_elimination_formula; auto.
      --  simpl. rewrite I1. simpl. rewrite ord_max_exp_equiv; auto. rewrite ord_max_symm. case (ord_max o o0) eqn:Y. simpl. apply coeff_lt. lia. refine (lt_trans _ _ _ (ord_succ_lt_exp_succ _ _ _) _); try rewrite <- Y; try apply ord_max_nf; auto. rewrite Y. apply zero_lt. apply ord_2_exp_monot; try repeat apply ord_succ_nf; try apply ord_max_nf; auto. apply ord_succ_monot.
      --  apply cut_elimination_valid; auto.
      --  apply nf_2_exp. auto.
      --  simpl. rewrite I1. simpl in *. lia.
    * exists (weak_ord_up (cut_elimination (cut_ad (lor f1 f2) f0 (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ)) (ord_2_exp (ord_succ (ord_succ (ord_max o o0))))).
      case (ord_succ (ord_succ (ord_max (ord_2_exp o) (ord_2_exp o0)))) eqn:I1. pose proof (ord_succ_non_Zero (ord_succ (ord_max (ord_2_exp o) (ord_2_exp o0)))). rewrite I1 in H6. inversion H6. repeat split; auto.
      --  rewrite weak_ord_formula. unfold ptree_formula. fold ptree_formula. rewrite cut_elimination_formula; auto.
      --  apply weak_ord_valid.
          ++  apply nf_2_exp. repeat apply ord_succ_nf. apply ord_max_nf; auto.
          ++  apply cut_elimination_valid; auto.
      --  rewrite weak_ord_deg. simpl in *. rewrite I1. simpl. lia.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (cut_elimination (cut_ad (lor f1 f2) f0 (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))) (ord_2_exp (ord_succ (ord_succ (ord_max o o0))))) eqn:I2; auto.
          simpl. rewrite I1. unfold ptree_ord. rewrite <- I1.
          simpl in I2. rewrite I1 in I2. unfold ptree_ord in I2. rewrite <- I1 in I2.
          rewrite ord_max_exp_equiv in *; auto. apply ord_eqb_eq. destruct (ord_max o o0). simpl in *. inversion I2. rewrite (ord_lt_ltb _ _ (plus_two_lt_times_four _ (ord_nf_succ _ (ord_nf_succ _ H)) (zero_lt _ _ _))) in I2. inversion I2.
    * assert (P_proves (weakening_ad f0 (univ n2 f) (ptree_deg PY) (ord_2_exp o) PY) (lor f0 (univ n2 f)) (ptree_deg PY) (ord_succ (ord_2_exp o))) as PY1. repeat split; simpl; auto. pose proof (provable_closed' _ _ Z2 Z1). simpl in H6. destruct (and_bool_prop _ _ H6). apply H8.
      assert (max (ptree_deg PY) (ptree_deg PZ) < num_conn f + 2).
      { simpl in *. apply nat_eq_decid in E1. lia. }
      assert (max (max (ptree_deg PY) (ptree_deg PZ)) (num_conn f + 1) <= d).
      { simpl in *. apply nat_eq_decid in E1. lia. }
      exists (weak_ord_up (contraction_a f0 (ptree_deg (neg_w_rule_sub_ptree PZ _ _ _ _ _ _ PY1 (lor_ind (1) (non_target f0)))) (ord_add (ord_succ (ord_2_exp o)) (ord_2_exp o0)) (weak_ord_up (neg_w_rule_sub_ptree PZ _ _ _ _ _ _ PY1 (lor_ind (1) (non_target f0))) (ord_add (ord_succ (ord_2_exp o)) (ord_2_exp o0)))) (ord_2_exp (ord_succ (ord_succ (ord_max o o0))))). repeat split; auto.
      --  rewrite weak_ord_formula. auto.
      --  apply weak_ord_valid. apply nf_2_exp. auto. repeat split; auto.
          ++  rewrite weak_ord_formula. rewrite neg_w_rule_ptree_formula; auto. unfold neg_w_rule_sub_formula. rewrite Z1. simpl. rewrite non_target_fit. rewrite eq_nat_refl. rewrite eq_f_refl. simpl. rewrite non_target_sub'. auto.
          ++  apply weak_ord_valid. apply nf_add; try apply ord_succ_nf; apply nf_2_exp; auto. apply neg_w_rule_valid; auto. pose proof (provable_closed'  _ _ Z2 Z1). destruct (and_bool_prop _ _ H8). auto. rewrite Z1. simpl. apply non_target_fit.
          ++  rewrite weak_ord_deg. auto.
          ++  unfold weak_ord_up. case (ord_ltb (ptree_ord (neg_w_rule_sub_ptree PZ (weakening_ad f0 (univ n2 f) (ptree_deg PY) (ord_2_exp o) PY) f f0 n2 (ptree_deg PY) (ord_succ (ord_2_exp o)) PY1 (lor_ind (1) (non_target f0)))) (ord_add (ord_succ (ord_2_exp o)) (ord_2_exp o0))) eqn:I1.
              **  simpl. auto.
              **  pose proof (neg_w_rule_ptree_ord PZ _ _ _ _ _ _ PY1 Z2 (lor_ind (1) (non_target f0))). destruct (ord_semiconnex_bool (ord_add (ord_succ (ord_2_exp o)) (ptree_ord PZ)) (ptree_ord (neg_w_rule_sub_ptree PZ (weakening_ad f0 (univ n2 f) (ptree_deg PY) (ord_2_exp o) PY) f f0 n2 (ptree_deg PY) (ord_succ (ord_2_exp o)) PY1 (lor_ind (1) (non_target f0))))) as [I2 | [I2 | I2]]; rewrite Z4 in *.
                  { rewrite I2 in H8. inversion H8. }
                  { rewrite I2 in I1. inversion I1. }
                  { apply ord_eqb_eq in I2. rewrite I2. auto. }
      --  rewrite weak_ord_deg. simpl. pose proof (neg_w_rule_ptree_deg PZ _ _ _ _ _ _ PY1 Z2 H6 (lor_ind (1) (non_target f0))). lia.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (contraction_a f0 (ptree_deg (neg_w_rule_sub_ptree PZ (weakening_ad f0 (univ n2 f) (ptree_deg PY) (ord_2_exp o) PY) f f0 n2 (ptree_deg PY) (ord_succ (ord_2_exp o)) PY1 (lor_ind (1) (non_target f0)))) (ord_add (ord_succ (ord_2_exp o)) (ord_2_exp o0)) ((weak_ord_up (neg_w_rule_sub_ptree PZ (weakening_ad f0 (univ n2 f) (ptree_deg PY) (ord_2_exp o) PY) f f0 n2 (ptree_deg PY) (ord_succ (ord_2_exp o)) PY1 (lor_ind (1) (non_target f0)))) (ord_add (ord_succ (ord_2_exp o)) (ord_2_exp o0))))) (ord_2_exp (ord_succ (ord_succ (ord_max o o0))))) eqn:I1; unfold weak_ord_up; unfold weak_ord_up in I1; try rewrite I1; auto.
          simpl in *. rewrite ord_2_exp_succ_mult in I1; try apply ord_succ_nf; try apply ord_max_nf; auto. rewrite ord_2_exp_succ_mult in I1; try apply ord_max_nf; auto. rewrite times_four_lt in I1; auto. inversion I1.
    + assert ((S (num_conn f)) < (max n0 n1)) as E2. rewrite eq_nat_symm in E1. rewrite (nat_eq_decid _ _ (nat_max_right_not _ _ E1)). apply (max_lem2 _ _ E1).
      intros. destruct X0 as [[[X1 X2] X3] X4]. simpl in X1,X3,X4. destruct X4. destruct X2 as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8]. unfold cut_remove in X. case (eq_nat (max (max n0 n1) (S (num_conn f))) (S d)) eqn:E.
      * assert ((S (num_conn f)) < (max n0 n1)). rewrite eq_nat_symm in E1. rewrite (nat_eq_decid _ _ (nat_max_right_not _ _ E1)). lia.
        apply nat_eq_decid in E. case (lt_nat n0 n1) eqn:Y.
        --  rewrite (max_split1 _ _ Y) in E. symmetry in E. destruct E. assert (P_proves P2 (lor (neg f) f0) (S d) o0). { unfold P_proves. repeat split; simpl; auto. lia. } assert (nf o0). rewrite H8. apply ptree_ord_nf. auto.
            destruct (X _ H10 (lt_trans _ _ _ (ord_max_succ_r _ _) (ord_succ_monot _)) _ _ _ X0) as [P7 [[[HP1 HP2] HP3] HP4]]. exists (ord_up (ord_2_exp (ord_succ (ord_succ (ord_max o o0)))) (cut_ad f f0 n0 (ptree_deg P7) o (ord_2_exp o0) P1 P7)). repeat split; simpl; auto.
            ++  destruct (ord_max o o0) eqn:O2.
                **  symmetry in O2. destruct (ord_max_0 _ _ O2). destruct H11,H12. simpl. apply coeff_lt. lia.
                **  rewrite <- O2. refine (lt_trans _ _ _ _ (ord_succ_lt_exp_succ _ _ _)). apply ord_lt_succ. apply ord_max_exp_r; auto. rewrite H7. apply ptree_ord_nf. auto. rewrite O2. simpl. destruct o1_1. apply coeff_lt. lia. apply head_lt. apply zero_lt. apply ord_succ_nf. rewrite H7,H8. apply ord_max_nf; apply ptree_ord_nf; auto. destruct (ord_max o o0); try destruct o1_3; apply zero_lt. 
            ++  apply nf_2_exp; auto.
            ++  apply lt_nat_decid in Y. simpl in *. lia.
        --  case (lt_nat n1 n0) eqn:Y1.
            ++  rewrite (max_split2 _ _ Y1) in E. symmetry in E. destruct E. assert (P_proves P1 f (S d) o). { unfold P_proves. repeat split; simpl; auto. lia. } assert (nf o). rewrite H7. apply ptree_ord_nf. auto.
                destruct (X _ H10 (lt_trans _ _ _ (ord_max_succ_l _ _) (ord_succ_monot _)) _ _ _ X0) as [P6 [[[HP1 HP2] HP3] HP4]]. exists (ord_up (ord_2_exp (ord_succ (ord_succ (ord_max o o0)))) (cut_ad f f0 (ptree_deg P6) n1 (ord_2_exp o) o0 P6 P2)). repeat split; simpl; auto.
                **  destruct (ord_max o o0) eqn:O2.
                    { symmetry in O2. destruct (ord_max_0 _ _ O2). destruct H11,H12. simpl. apply coeff_lt. lia. }
                    { rewrite <- O2. refine (lt_trans _ _ _ _ (ord_succ_lt_exp_succ _ _ _)). apply ord_lt_succ. apply ord_max_exp_l; auto. rewrite H8. apply ptree_ord_nf. auto. rewrite O2. simpl. destruct o1_1. apply coeff_lt. lia. apply head_lt. apply zero_lt. apply ord_succ_nf. rewrite H7,H8. apply ord_max_nf; apply ptree_ord_nf; auto. destruct (ord_max o o0); try destruct o1_3; apply zero_lt. }
                ** apply nf_2_exp. auto.
                **  apply lt_nat_decid in Y1. lia.
            ++  assert (n0 = n1). destruct (nat_semiconnex n0 n1) as [Y2 | [Y2 | Y2]]; try apply lt_nat_decid_conv in Y2. rewrite Y2 in Y. inversion Y. rewrite Y2 in Y1. inversion Y1. auto. destruct H10. rewrite max_n_n in E. symmetry in E. destruct E.
                assert (P_proves P1 f (S d) o). { unfold P_proves. repeat split; simpl; auto. lia. } assert (nf o). rewrite H7. apply ptree_ord_nf. auto.
                assert (P_proves P2 (lor (neg f) f0) (S d) o0). { unfold P_proves. repeat split; simpl; auto. lia. } assert (nf o0). rewrite H8. apply ptree_ord_nf. auto.
                destruct (X _ H10 (lt_trans _ _ _ (ord_max_succ_l _ _) (ord_succ_monot _)) _ _ _ X0) as [P6 [[[HP1 Hp2] HP3] HP4]]. destruct (X _ H11 (lt_trans _ _ _ (ord_max_succ_r _ _) (ord_succ_monot _)) _ _ _ X2) as [P7 [[[HQ1 HQ2] HQ3] HQ4]].
                exists (ord_up (ord_2_exp (ord_succ (ord_succ (ord_max o o0)))) (cut_ad f f0 (ptree_deg P6) (ptree_deg P7) (ord_2_exp o) (ord_2_exp o0) P6 P7)). repeat split; simpl; auto.
                **  rewrite ord_max_exp_equiv; auto. destruct (ord_max o o0) eqn:O2. simpl. apply coeff_lt. lia. rewrite <- O2. refine (lt_trans _ _ _ _ (ord_succ_lt_exp_succ _ _ _)). apply ord_lt_succ. apply ord_succ_lt_exp_succ. apply ord_max_nf; auto. rewrite O2. apply zero_lt. apply ord_succ_nf; apply ord_max_nf; auto. destruct (ord_max o o0); try destruct o1_3; apply zero_lt.
                **  apply nf_2_exp. auto.
                **  lia.
      * assert (d >= max (max n0 n1) (S (num_conn f))). { inversion X3. destruct H10. rewrite eq_nat_refl in E. inversion E. lia. } exists (ord_up (ord_2_exp (ord_succ (ord_succ (ord_max o o0)))) (cut_ad f f0 n0 n1 o o0 P1 P2)). repeat split; simpl; auto. apply ord_succ_not_exp_fp. auto. apply nf_2_exp. auto.
    
- case (eq_nat (max (max n0 n1) (S (num_conn f0))) (S (num_conn f0))) eqn:E1.
  + intros. inversion X0 as [[[HP1 HP2] HP3] HP4]. simpl in HP1,HP3,HP4. destruct HP4. inversion HP2 as [[[[[[[X1 X2] X3] X4] X5] X6] X7] X8].
    assert (P_proves P2 (lor(neg f0) f1) n1 o0) as HP5. repeat split; auto. lia. assert (P_proves P1 (lor f f0) n0 o) as HP6. repeat split; auto. lia.
    unfold cut_remove in X.
    assert (forall y : ord, nf y -> ord_lt y (ord_succ (ord_max o o0)) -> forall (P : ptree) (A : formula) (d : nat), P_proves P A d y -> provable A (pred d) (ord_2_exp y)) as IHP_PRED.
    { intros. destruct d0.
      { simpl. exists (weak_ord_up P (ord_2_exp y)). unfold weak_ord_up. destruct X9 as [[[Z1 Z2] Z3] Z4]. case (ord_ltb (ptree_ord P) (ord_2_exp y)) eqn:Y.
        { repeat split; simpl; auto. apply ord_ltb_lt. auto. apply nf_2_exp. auto. }
        { repeat split; simpl; auto. destruct Z4. destruct (ord_2_exp_fp (ptree_ord P)).
          { apply ptree_ord_nf. auto. }
          { apply ord_lt_ltb in H3. rewrite Y in H3. inversion H3. }
          { rewrite H3. auto. } } }
      { simpl. apply (X _ H1 H2 P _ _ X9). } }
    assert (nf o). rewrite X7. apply ptree_ord_nf. auto.
    assert (nf o0). rewrite X8. apply ptree_ord_nf. auto.
    destruct (IHP_PRED _ H1 (ord_max_succ_l _ _) P1 _ _ HP6) as [PY [[[Y1 Y2] Y3] Y4]].
    destruct (IHP_PRED _ H2 (ord_max_succ_r _ _) P2 _ _ HP5) as [PZ [[[Z1 Z2] Z3] Z4]].
    assert (valid (cut_cad f f0 f1 (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ)) as HYZ. repeat split; auto.
    assert (num_conn f0 <= d). lia.
    assert (ptree_deg PY <= d). lia.
    assert (ptree_deg PZ <= d). lia.
    destruct f0.
    * exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_elimination (cut_cad f (atom a) f1 (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))). 
      case (ord_succ (ord_max (ord_2_exp o) (ord_2_exp o0))) eqn:I1. pose proof (ord_succ_non_Zero (ord_max (ord_2_exp o) (ord_2_exp o0))). rewrite I1 in H6. inversion H6. repeat split; auto.
      --  unfold ptree_formula. fold ptree_formula. rewrite cut_elimination_formula; auto.
      --  simpl. rewrite I1. case (correct_a a) eqn:C.
          ++  simpl. apply ord_exp_succ_shuffle; auto. destruct (ord_max o o0). inversion O. apply zero_lt.
          ++  simpl. rewrite ord_max_symm. apply ord_exp_succ_shuffle; auto. rewrite ord_max_symm. destruct (ord_max o o0). inversion O. apply zero_lt.
      --  apply cut_elimination_valid; auto.
      --  apply nf_2_exp. auto.
      --  simpl. rewrite I1. case (correct_a a) eqn:C.
          { simpl. auto. }
          { simpl. lia. }
    * exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_elimination (cut_cad f (neg f0) f1 (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))).
      case (ord_succ (ord_max (ord_2_exp o) (ord_2_exp o0))) eqn:I1. pose proof (ord_succ_non_Zero (ord_max (ord_2_exp o) (ord_2_exp o0))). rewrite I1 in H6. inversion H6. repeat split; auto.
      --  unfold ptree_formula. fold ptree_formula. rewrite cut_elimination_formula; auto.
      --  simpl. rewrite I1. case (eq_nat (max (max (ptree_deg PZ) (ptree_deg PY)) (S (num_conn f0))) (S (num_conn f0))); simpl; rewrite <- I1; rewrite ord_max_exp_equiv; auto; apply ord_succ_lt_exp_succ; try apply ord_nf_succ; auto; destruct (ord_max o o0); inversion O; apply zero_lt.
      --  apply cut_elimination_valid; auto.
      --  apply nf_2_exp. auto.
      --  simpl. rewrite I1. simpl in *. lia.
    * exists (weak_ord_up (cut_elimination (cut_cad f (lor f0_1 f0_2) f1 (ptree_deg PY) (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ)) (ord_2_exp (ord_succ (ord_max o o0)))).
      case (ord_succ (ord_max (ord_2_exp o) (ord_2_exp o0))) eqn:I1. pose proof (ord_succ_non_Zero (ord_max (ord_2_exp o) (ord_2_exp o0))). rewrite I1 in H6. inversion H6. repeat split; auto.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (cut_elimination (cut_cad f (lor f0_1 f0_2) f1 (ptree_deg PY)  (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I2.
          ++  unfold ptree_formula. fold ptree_formula. rewrite cut_elimination_formula; auto.
          ++  unfold ptree_formula. fold ptree_formula. rewrite cut_elimination_formula; auto.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (cut_elimination (cut_cad f (lor f0_1 f0_2) f1 (ptree_deg PY)  (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I2.
          ++  repeat split; auto.
              **  apply ord_ltb_lt. auto.
              **  apply cut_elimination_valid; auto.
              **  apply nf_2_exp. auto.
          ++  apply cut_elimination_valid; auto.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (cut_elimination (cut_cad f (lor f0_1 f0_2) f1 (ptree_deg PY)  (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I2.
          ++ simpl in *. rewrite I1. unfold contraction_help. unfold ptree_formula. rewrite eq_f_refl. unfold ptree_deg. fold ptree_deg. simpl in *. lia.
          ++ simpl in *. rewrite I1. unfold contraction_help. unfold ptree_formula. rewrite eq_f_refl. unfold ptree_deg. fold ptree_deg. simpl in *. lia.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (cut_elimination (cut_cad f (lor f0_1 f0_2) f1 (ptree_deg PY)  (ptree_deg PZ) (ord_2_exp o) (ord_2_exp o0) PY PZ))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I2; auto.
          simpl. rewrite I1. unfold contraction_help. unfold ptree_formula. rewrite eq_f_refl. unfold ptree_ord. rewrite <- I1.
          simpl in I2. rewrite I1 in I2. unfold contraction_help in I2. unfold ptree_formula in I2. rewrite eq_f_refl in I2. unfold ptree_ord in I2. rewrite <- I1 in I2.
          rewrite ord_max_lem2. rewrite ord_max_lem2 in I2.
          ++  rewrite ord_max_exp_equiv in *; auto. apply ord_eqb_eq. assert (ord_lt Zero (ord_max o o0)). destruct (ord_max o o0). inversion H0; inversion H7. apply zero_lt. apply (dub_succ_exp_eq _ H6 (ord_nf_succ _ H) I2). 
          ++  apply ltb_asymm. apply ord_lt_ltb. apply ord_max_succ_r.
          ++  apply ltb_asymm. apply ord_lt_ltb. apply ord_max_succ_r.
    * assert (P_proves PY (lor f (univ n2 f0)) (ptree_deg PY) (ord_2_exp o)) as PY1. repeat split; auto.
      assert (max (ptree_deg PY) (ptree_deg PZ) < num_conn f0 + 2).
      { simpl in *. apply nat_eq_decid in E1. lia. }
      assert (max (max (ptree_deg PY) (ptree_deg PZ)) (num_conn f0 + 1) <= d).
      { simpl in *. apply nat_eq_decid in E1. lia. }
      exists (weak_ord_up (neg_w_rule_sub_ptree PZ _ _ _ _ _ _ PY1 (lor_ind (1) (non_target f1))) (ord_2_exp (ord_succ (ord_max o o0)))). repeat split; auto.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (neg_w_rule_sub_ptree PZ PY f0 f n2 (ptree_deg PY) (ord_2_exp o) PY1 (lor_ind (1) (non_target f1)))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I1.
          ++  simpl. rewrite neg_w_rule_ptree_formula; auto. rewrite Z1. unfold neg_w_rule_sub_formula. simpl. rewrite non_target_fit. rewrite eq_nat_refl. rewrite eq_f_refl. simpl. rewrite non_target_sub'. auto.
          ++  simpl. rewrite neg_w_rule_ptree_formula; auto. rewrite Z1. unfold neg_w_rule_sub_formula. simpl. rewrite non_target_fit. rewrite eq_nat_refl. rewrite eq_f_refl. simpl. rewrite non_target_sub'. auto.
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (neg_w_rule_sub_ptree PZ PY f0 f n2 (ptree_deg PY) (ord_2_exp o) PY1 (lor_ind (1) (non_target f1)))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I1.
          ++  repeat split. apply ord_ltb_lt. auto. apply neg_w_rule_valid; auto.
              { pose proof (provable_closed' PY _ Y2 Y1). simpl in H7. destruct (and_bool_prop _ _ H8). auto. }
              { rewrite Z1. simpl; auto. apply non_target_fit. }
              { apply nf_2_exp. auto. }
          ++  apply neg_w_rule_valid; auto.
              { pose proof (provable_closed' PY _ Y2 Y1). simpl in H7. destruct (and_bool_prop _ _ H8). auto. }
              { rewrite Z1. simpl; auto. apply non_target_fit. }
      --  pose proof (neg_w_rule_ptree_deg PZ _ _ _ _ _ _ PY1 Z2 H6 (lor_ind (1) (non_target f1))).
          unfold weak_ord_up. case (ord_ltb (ptree_ord (neg_w_rule_sub_ptree PZ PY f0 f n2 (ptree_deg PY) (ord_2_exp o) PY1 (lor_ind (1) (non_target f1)))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I1; simpl; lia. 
      --  unfold weak_ord_up. case (ord_ltb (ptree_ord (neg_w_rule_sub_ptree PZ PY f0 f n2 (ptree_deg PY) (ord_2_exp o) PY1 (lor_ind (1) (non_target f1)))) (ord_2_exp (ord_succ (ord_max o o0)))) eqn:I1; simpl; auto. 
          pose proof (neg_w_rule_ptree_ord PZ _ _ _ _ _ _ PY1 Z2 (lor_ind (1) (non_target f1))).
          rewrite Z4 in H8.
          pose proof (ord_trans_inv _ _ _ (ord_add_exp_le_exp_max _ _ H1 H2) H8) as I2.
          destruct (ord_semiconnex_bool (ord_2_exp (ord_succ (ord_max o o0))) (ptree_ord (neg_w_rule_sub_ptree PZ PY f0 f n2 (ptree_deg PY) (ord_2_exp o) PY1 (lor_ind (1) (non_target f1))))) as [I3 | [I3 | I3]].
          ++  rewrite I3 in I2. inversion I2.
          ++  rewrite I3 in I1. inversion I1.
          ++  apply ord_eqb_eq in I3. auto. 
    + assert ((S (num_conn f0)) < (max n0 n1)) as E2. rewrite eq_nat_symm in E1. rewrite (nat_eq_decid _ _ (nat_max_right_not _ _ E1)). apply (max_lem2 _ _ E1).
      intros. destruct X0 as [[[X1 X2] X3] X4]. simpl in X1,X3,X4. destruct X4. destruct X2 as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8]. unfold cut_remove in X. case (eq_nat (max (max n0 n1) (S (num_conn f0))) (S d)) eqn:E.
      * assert ((S (num_conn f0)) < (max n0 n1)). rewrite eq_nat_symm in E1. rewrite (nat_eq_decid _ _ (nat_max_right_not _ _ E1)). apply (max_lem2 _ _ E1).
        apply nat_eq_decid in E. case (lt_nat n0 n1) eqn:Y.
        --  rewrite (max_split1 _ _ Y) in E. symmetry in E. destruct E. assert (P_proves P2 (lor (neg f0) f1) (S d) o0). { unfold P_proves. repeat split; simpl; auto. lia. } assert (nf o0). rewrite H8. apply ptree_ord_nf. auto.
            destruct (X _ H10 (ord_max_succ_r _ _) _ _ _ X0) as [P7 [[[HP1 HP2] HP3] HP4]]. exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_cad f f0 f1 n0 (ptree_deg P7) o (ord_2_exp o0) P1 P7)). repeat split; simpl; auto.
            apply ord_max_exp_r; auto. rewrite H7. apply ptree_ord_nf. auto. apply nf_2_exp. auto. apply lt_nat_decid in Y. lia.
        --  case (lt_nat n1 n0) eqn:Y1.
            ++  rewrite (max_split2 _ _ Y1) in E. symmetry in E. destruct E. assert (P_proves P1 (lor f f0) (S d) o). { unfold P_proves. repeat split; simpl; auto. lia. } assert (nf o). rewrite H7. apply ptree_ord_nf. auto.
                destruct (X _ H10 (ord_max_succ_l _ _) _ _ _ X0) as [P6 [[[HP1 HP2] HP3] HP4]]. exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_cad f f0 f1 (ptree_deg P6) n1 (ord_2_exp o) o0 P6 P2)). repeat split; simpl; auto.
                apply ord_max_exp_l; auto. rewrite H8. apply ptree_ord_nf. auto. apply nf_2_exp. auto. apply lt_nat_decid in Y1. lia.
            ++  assert (n0 = n1). destruct (nat_semiconnex n0 n1) as [Y2 | [Y2 | Y2]]; try apply lt_nat_decid_conv in Y2. rewrite Y2 in Y. inversion Y. rewrite Y2 in Y1. inversion Y1. auto. destruct H10. rewrite max_n_n in E. symmetry in E. destruct E.
                assert (P_proves P1 (lor f f0) (S d) o). { unfold P_proves. repeat split; simpl; auto. lia. } assert (nf o). rewrite H7. apply ptree_ord_nf. auto.
                assert (P_proves P2 (lor (neg f0) f1) (S d) o0). { unfold P_proves. repeat split; simpl; auto. lia. } assert (nf o0). rewrite H8. apply ptree_ord_nf. auto.
                destruct (X _ H10 (ord_max_succ_l _ _) _ _ _ X0) as [P6 [[[HP1 Hp2] HP3] HP4]]. destruct (X _ H11 (ord_max_succ_r _ _) _ _ _ X2) as [P7 [[[HQ1 HQ2] HQ3] HQ4]].
                exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_cad f f0 f1 (ptree_deg P6) (ptree_deg P7) (ord_2_exp o) (ord_2_exp o0) P6 P7)). repeat split; simpl; auto.
                apply ord_max_exp_both; auto. apply nf_2_exp. auto. lia.
      * assert (d >= max (max n0 n1) (S (num_conn f0))). { inversion X3. destruct H10. rewrite eq_nat_refl in E. inversion E. lia. } exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_cad f f0 f1 n0 n1 o o0 P1 P2)). repeat split; simpl; auto. apply ord_succ_not_exp_fp. auto. apply nf_2_exp. auto.
Qed.

Lemma cut_elim_aux1 : forall (alpha : ord) (P : ptree) (A : formula) (d : nat), P_proves P A (S d) alpha -> provable A d (ord_2_exp alpha).
Proof.
intros alpha P A d X. inversion X as [[[X1 X2] X3] X4]. destruct X4. apply (cut_elim_aux0 _ (ptree_ord_nf _ X2) P _ _ X).
Qed.

Lemma cut_elim_aux2 : forall (A : formula) (d : nat),
  {alpha : ord & provable A d alpha} -> {beta : ord & provable A 0 beta}.
Proof.
intros. induction d.
- destruct X as [alpha H]. exists alpha. auto.
- apply IHd. destruct X as [alpha H]. exists (ord_2_exp alpha). destruct H as [P H]. apply (cut_elim_aux1 _ _ _ _ H).
Qed.

Lemma cut_elim_aux3 : forall (A : formula) (d : nat) (alpha : ord),
  provable A d alpha -> {beta : ord & provable A 0 beta}.
Proof. intros. apply (cut_elim_aux2 A d). exists alpha. auto. Qed.

Fixpoint cut_free (P : ptree) : Type :=
match P with
| deg_up d P' => cut_free P'

| ord_up alpha P' => cut_free P'

| node A => True


| exchange_ab A B d alpha P' => cut_free P'

| exchange_cab C A B d alpha P' => cut_free P'

| exchange_abd A B D d alpha P' => cut_free P'

| exchange_cabd C A B D d alpha P' => cut_free P'

| contraction_a A d alpha P' => cut_free P'

| contraction_ad A D d alpha P' => cut_free P'


| weakening_ad A D d alpha P' => cut_free P'

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2 => (cut_free P1) * (cut_free P2)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2 => (cut_free P1) * (cut_free P2)

| negation_a A d alpha P' => cut_free P'

| negation_ad A D d alpha P' => cut_free P'


| quantification_a A n t d alpha P' => cut_free P'

| quantification_ad A D n t d alpha P' => cut_free P'

| w_rule_a A n d alpha g => forall (c : c_term), cut_free (g c)

| w_rule_ad A D n d alpha g => forall (c : c_term), cut_free (g c)


| cut_ca C A d1 d2 alpha1 alpha2 P1 P2 => False

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 => False

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2 => False

end.


Lemma cut_elim_aux4 : forall (P : ptree),
  valid P -> ptree_deg P = 0 -> cut_free P.
Proof.
intros. induction P; simpl; auto.
- destruct X as [H1 H2]. simpl in H. rewrite H in H1. lia.
- destruct X as [[H1 H2] H3]. simpl in H. apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  simpl in H. rewrite H5 in H. rewrite H6 in H.
  destruct (max_0 _ _ H). split.
  + apply IHP1; auto.
  + apply IHP2; auto.
- destruct X as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  simpl in H. rewrite H5 in H. rewrite H6 in H.
  destruct (max_0 _ _ H). split.
  + apply IHP1; auto.
  + apply IHP2; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- destruct X as [[[H1 H2] H3] H4]. simpl in H. rewrite H in H3.
  apply IHP; auto.
- rename f into A. rename p into g. rename n0 into d. rename o into alpha.
  intros. simpl in H. simpl in X. destruct (X c) as [[[H1 H2] H3] H4].
  rewrite H in H3. apply X0; auto. lia.
- rename f into A. rename f0 into D. rename p into g.
  rename n0 into d. rename o into alpha.
  intros. simpl in H. simpl in X. destruct (X c) as [[[H1 H2] H3] H4].
  rewrite H in H3. apply X0; auto. lia.
- simpl in H. apply max_succ_0 in H. auto.
- simpl in H. apply max_succ_0 in H. auto.
- simpl in H. apply max_succ_0 in H. auto.
Qed.


Definition P_proves' (P : ptree) (A : formula) : Type :=
  (ptree_formula P = A) * (valid P) *
  {d : nat & ptree_deg P = d & {alpha : ord & ptree_ord P = alpha}}.

Lemma cut_elim_aux5 : forall (A : formula) (d : nat) (alpha : ord),
  provable A d alpha -> {P : ptree & P_proves' P A & cut_free P}.
Proof.
intros. apply cut_elim_aux3 in X. destruct X as [gamma [P [[[H1 H2] H3] H4]]].
exists P.
- unfold P_proves'. repeat split; auto.
  exists 0; auto. lia. exists gamma; auto.
- apply cut_elim_aux4; auto. lia.
Qed.