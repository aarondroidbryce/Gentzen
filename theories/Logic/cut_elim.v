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
    (match form_eqb D E with
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
      rewrite form_eqb_refl;
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

(*********TEMPORARY***********)

Lemma weak_ord_height :
    forall (P : ptree) (alpha : ord),
        ord_ltb alpha (ptree_ord P) = false ->
            ptree_ord (weak_ord_up P alpha) = alpha .
Proof.
intros P alpha IO.
unfold weak_ord_up.
destruct (ord_semiconnex_bool (ptree_ord P) alpha) as [LT | [GT | EQ]].
rewrite LT. reflexivity.
rewrite GT in IO. inversion IO.
apply ord_eqb_eq in EQ. destruct EQ.
rewrite ord_ltb_irrefl.
reflexivity.
Qed.


Theorem cut_elimination_ord :
    forall (P : ptree),
        valid P ->
            ord_ltb (ord_2_exp (ptree_ord P)) (ptree_ord (cut_elimination P)) = false.
Proof.
intros P PV.
pose (ptree_ord P) as alpha.
pose proof (ptree_ord_nf _ PV) as NA.
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
    + apply (ord_ltb_asymm _ _ (ord_ltb_trans _ _ _ GT (ord_lt_ltb _ _ (ord_2_exp_monot _ NO _ (ptree_ord_nf _ PV) IO)))).
    + apply ord_eqb_eq in EQ.
      destruct EQ.
      apply (ord_ltb_asymm _ _ (ord_lt_ltb _ _ (ord_2_exp_monot _ NO _ (ptree_ord_nf _ PV) IO))). }

1 : { fold cut_elimination cut_elimination_atom cut_elimination_neg cut_elimination_lor. fold cut_elimination.
      unfold ptree_ord; fold ptree_ord.
      apply (IHP PV NA). }

all : unfold ptree_ord in *; fold ptree_ord in *;
      try apply (ord_ltb_exp_false _ NA);
      unfold PA_omega_axiom.

2 : destruct f.
1,6 : destruct f0.
1,5,9 : destruct (correct_a a).

all : unfold contraction_help, ptree_formula, ptree_ord;
      try rewrite form_eqb_refl;
      try rewrite formula_sub_ptree_ord_atom;
      try rewrite formula_sub_ptree_ord_neg;
      try rewrite P1O in *;
      try rewrite P2O in *;
      try apply P1V;
      try apply P2V;
      fold ptree_ord;
      try apply ord_ltb_exp_false;
      try apply NA.

7,10 : rewrite (ord_max_symm (ptree_ord P2)).
9,10 : rewrite (ord_max_ltb_not_l _ _ (ord_ltb_asymm _ _ (ord_lt_ltb _ _ (ord_lt_max_succ_r _ _)))).
7,9,10 : apply (ord_ltb_succ_leb _ _ NA (nf_2_exp _ NA) (ord_lt_ltb _ _ (ord_succ_not_exp_fp _ NA))).

all : apply (ord_geb_trans _ (ord_succ (ord_max (ptree_ord P1) (ptree_ord P2))));
      try apply (ord_geb_trans (ord_2_exp (ord_succ (ord_succ (ord_max (ptree_ord P1) (ptree_ord P2))))) (ord_succ (ord_succ (ord_max (ptree_ord P1) (ptree_ord P2)))) (ord_succ (ord_max (ptree_ord P1) (ptree_ord P2))));
      try apply (ord_ltb_asymm _ _ (ord_lt_ltb _ _ (ord_succ_monot _)));
      try apply (ord_ltb_exp_false _ NA);
      try apply ord_geb_succ;
      try apply (ord_ltb_asymm _ _ (ord_lt_ltb _ _ (ord_lt_max_succ_l _ _)));
      try apply (ord_ltb_asymm _ _ (ord_lt_ltb _ _ (ord_lt_max_succ_r _ _)));
      try apply ord_ltb_irrefl;
      try apply ord_max_geb_l;
      try apply ord_max_geb_r.
Qed.

Theorem cut_elimination_valid :
    forall (P : ptree),
        valid P ->
            valid (cut_elimination P).
Proof.
intros P PV.
pose (ptree_ord P) as alpha.
pose proof (ptree_ord_nf _ PV) as NA.
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
      try rewrite form_eqb_refl.
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
      try rewrite form_eqb_refl;
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

5 : rewrite (ord_max_ltb_not_l _ _ (ord_ltb_asymm _ _ (ord_lt_ltb _ _ (ord_lt_max_succ_r _ _))));
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
      exfalso.
      inversion IO. }

7-18 :  try pose proof (ord_succ_neb_zero o) as NZ1;
        try pose proof (ord_succ_neb_zero (ord_max o o0)) as NZ2;
        try pose proof (ord_succ_neb_zero (ord_succ (ord_max o o0))) as NZ3;
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

7-18 :  try pose proof (ord_succ_neb_zero o) as NZ1;
        try pose proof (ord_succ_neb_zero (ord_max o o0)) as NZ2;
        try pose proof (ord_succ_neb_zero (ord_succ (ord_max o o0))) as NZ3;
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
              try destruct (ord_max_zero _ _ PO') as [OZ1 OZ2];
              try destruct PO';
              try destruct OZ1,OZ2;
              try pose proof (height_zero_not_lor _ P1V P1O (neg f) f1) as NE1;
              try pose proof (height_zero_not_lor _ P1V P1O f f0) as NE2;
              try pose proof (height_zero_not_lor _ PzV PO (substitution f n (projT1 czero)) f0) as NE3;
              try rewrite P1F in *;
              try rewrite PF in *;
              contradiction.

14 :  { apply ord_succ_one in PO'.
        pose proof (ord_succ_neb_zero (ord_max o o0)) as NE. 
        destruct PO'.
        inversion NE. }

8 : { apply ord_succ_one in PO'.
      try destruct (ord_max_zero _ _ PO') as [OZ1 OZ2].
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
      try destruct (ord_max_zero _ _ PO') as [OZ1 OZ2];
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
    destruct (IND _ (nf_succ_nf _ NA) (ord_succ_monot _) _ _ _ (PF, PV, PD', PO)) as [P1 [[[P1F P1V] P1D] P1O]].

8,9 : assert (S d >= n0) as IE1;
      assert (S d >= n1) as IE2;
      rewrite P1D,P2D,PO' in *;
      try lia;
      destruct (IND _ (ptree_ord_nf_hyp _ _ P1O P1V) (ord_lt_max_succ_l _ _) _ _ _ (P1F, P1V, IE1, P1O)) as [P3 [[[P3F P3V] P3D] P3O]];
      destruct (IND _ (ptree_ord_nf_hyp _ _ P2O P2V) (ord_lt_max_succ_r _ _) _ _ _ (P2F, P2V, IE2, P2O)) as [P4 [[[P4F P4V] P4D] P4O]].

10-13 : rewrite PD,PO' in *;
        destruct (IND _ (nf_succ_nf _ NA) (ord_succ_monot _) _ _ _ (PF, PV, PD', PO)) as [P1 [[[P1F P1V] P1D] P1O]].

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
        try apply (nf_succ_nf _ NA);
        try apply (ord_succ_lt Zero _ IEO).


1,2 : rewrite ord_max_exp_comm;
      try apply ord_succ_lt_exp_succ;
      try apply (ord_succ_lt Zero _ IEO);
      try apply nf_ord_max;
      try apply (ptree_ord_nf_hyp _ _ P1O P1V);
      try apply (ptree_ord_nf_hyp _ _ P2O P2V).

3 : case (nat_eqb (max (max n0 n1) (S (num_conn f0))) (S (num_conn f0))) eqn:E1.
2 : case (nat_eqb (max (max n0 n1) (S (num_conn f))) (S (num_conn f))) eqn:E1.
1 : case (nat_eqb (max (max n0 n1) (S (num_conn f0))) (S (num_conn f0))) eqn:E1.

2,6 : rewrite PO' in *;
      assert (S d >= ptree_deg P1) as IE1;
      assert (S d >= ptree_deg P2) as IE2;
      try lia;
      assert ((S (num_conn f0)) < (max n0 n1)) as E2;
      rewrite nat_eqb_symm in E1;
      try rewrite (nat_eqb_eq _ _ (nat_max_neb_r_eqb_l _ _ E1));
      try apply (max_lem2 _ _ E1);
      destruct (IND _ (ptree_ord_nf_hyp _ _ P1O P1V) (ord_lt_max_succ_l _ _) _ _ _ (P1F, P1V, IE1, P1O)) as [T1 [[[T1F T1V] T1D] T1O]];
      destruct (IND _ (ptree_ord_nf_hyp _ _ P2O P2V) (ord_lt_max_succ_r _ _) _ _ _ (P2F, P2V, IE2, P2O)) as [T2 [[[T2F T2V] T2D] T2O]].
      
5 : rewrite PO' in *;
    assert (S d >= ptree_deg P1) as IE1;
    assert (S d >= ptree_deg P2) as IE2;
    try lia;
    assert ((S (num_conn f)) < (max n0 n1)) as E2;
    rewrite nat_eqb_symm in E1;
    try rewrite (nat_eqb_eq _ _ (nat_max_neb_r_eqb_l _ _ E1));
    try apply (max_lem2 _ _ E1);
    destruct (IND _ (ptree_ord_nf_hyp _ _ P1O P1V) (ord_lt_trans _ _ _ (ord_lt_max_succ_l _ _) (ord_succ_monot _)) _ _ _ (P1F, P1V, IE1, P1O)) as [T1 [[[T1F T1V] T1D] T1O]];
    destruct (IND _ (ptree_ord_nf_hyp _ _ P2O P2V) (ord_lt_trans _ _ _ (ord_lt_max_succ_r _ _) (ord_succ_monot _)) _ _ _ (P2F, P2V, IE2, P2O)) as [T2 [[[T2F T2V] T2D] T2O]].


2 : exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_ca f f0 (ptree_deg T1) (ptree_deg T2) (ptree_ord T1) (ptree_ord T2) T1 T2)).

3 : exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_cad f f0 f1 (ptree_deg T1) (ptree_deg T2) (ptree_ord T1) (ptree_ord T2) T1 T2)).

5 : exists (ord_up (ord_2_exp (ord_succ (ord_succ (ord_max o o0)))) (cut_ad f f0 (ptree_deg T1) (ptree_deg T2) (ptree_ord T1) (ptree_ord T2) T1 T2)).

2,3,5 : repeat split;
        unfold ptree_ord, ptree_deg; fold ptree_ord ptree_deg;
        try apply T1F;
        try apply T2F;
        try apply T1V;
        try apply T2V;
        try apply nf_2_exp;
        try apply NA;
        unfold num_conn in *; fold num_conn in *;
        try lia;
        rewrite <- T1O, <- T2O;
        rewrite ord_max_exp_comm;
        try apply ord_succ_lt_exp_succ;
        try apply dub_succ_exp_lt_exp_dub_succ;
        try apply (ord_succ_lt Zero _ IEO);
        try apply nf_ord_max;
        try apply (ptree_ord_nf_hyp _ _ P1O P1V);
        try apply (ptree_ord_nf_hyp _ _ P2O P2V).

1,3 : rewrite PO' in *;
      assert (n0 >= ptree_deg P1) as IE1;
      assert (n1 >= ptree_deg P2) as IE2;
      try lia;
      apply nat_eqb_eq in E1;
      destruct (IHP_PRED _ (ptree_ord_nf_hyp _ _ P1O P1V) (ord_lt_max_succ_l _ _) P1 _ _ (P1F, P1V, IE1, P1O)) as [T1 [[[T1F T1V] T1D] T1O]];
      destruct (IHP_PRED _ (ptree_ord_nf_hyp _ _ P2O P2V) (ord_lt_max_succ_r _ _) P2 _ _ (P2F, P2V, IE2, P2O)) as [T2 [[[T2F T2V] T2D] T2O]];
      unfold provable;
      destruct f0.

9 : rewrite PO' in *;
    assert (n0 >= ptree_deg P1) as IE1;
    assert (n1 >= ptree_deg P2) as IE2;
    try lia;
    apply nat_eqb_eq in E1;
    destruct (IHP_PRED _ (ptree_ord_nf_hyp _ _ P1O P1V) (ord_lt_trans _ _ _ (ord_lt_max_succ_l _ _) (ord_succ_monot _ )) P1 _ _ (P1F, P1V, IE1, P1O)) as [T1 [[[T1F T1V] T1D] T1O]];
    destruct (IHP_PRED _ (ptree_ord_nf_hyp _ _ P2O P2V) (ord_lt_trans _ _ _ (ord_lt_max_succ_r _ _) (ord_succ_monot _ )) P2 _ _ (P2F, P2V, IE2, P2O)) as [T2 [[[T2F T2V] T2D] T2O]];
    unfold provable;
    destruct f.

1 : exists (weak_ord_up (cut_elimination (cut_ca f (atom a) (ptree_deg T1) (ptree_deg T2) (ptree_ord T1) (ptree_ord T2) T1 T2)) (ord_2_exp (ord_succ (ord_max o o0)))).
2 : exists (weak_ord_up (cut_elimination (cut_ca f (neg f0) (ptree_deg T1) (ptree_deg T2) (ptree_ord T1) (ptree_ord T2) T1 T2)) (ord_2_exp (ord_succ (ord_max o o0)))).
3 : exists (weak_ord_up (cut_elimination (cut_ca f (lor f0_1 f0_2) (ptree_deg T1) (ptree_deg T2) (ptree_ord T1) (ptree_ord T2) T1 T2)) (ord_2_exp (ord_succ (ord_max o o0)))).

5 : exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_elimination (cut_cad f (atom a) f1 (ptree_deg T1) (ptree_deg T2) (ptree_ord T1) (ptree_ord T2) T1 T2))).
6 : exists (ord_up (ord_2_exp (ord_succ (ord_max o o0))) (cut_elimination (cut_cad f (neg f0) f1 (ptree_deg T1) (ptree_deg T2) (ptree_ord T1) (ptree_ord T2) T1 T2))).
7 : exists (weak_ord_up (cut_elimination (cut_cad f (lor f0_1 f0_2) f1 (ptree_deg T1) (ptree_deg T2) (ptree_ord T1) (ptree_ord T2) T1 T2)) (ord_2_exp (ord_succ (ord_max o o0)))).

9 : exists (ord_up (ord_2_exp (ord_succ (ord_succ (ord_max o o0)))) (cut_elimination (cut_ad (atom a) f0 (ptree_deg T1) (ptree_deg T2) (ptree_ord T1) (ptree_ord T2) T1 T2))).
10 : exists (ord_up (ord_2_exp (ord_succ (ord_succ (ord_max o o0)))) (cut_elimination (cut_ad (neg f) f0 (ptree_deg T1) (ptree_deg T2) (ptree_ord T1) (ptree_ord T2) T1 T2))).
11 : exists (weak_ord_up (cut_elimination (cut_ad (lor f1 f2) f0 (ptree_deg T1) (ptree_deg T2) (ptree_ord T1) (ptree_ord T2) T1 T2)) (ord_2_exp (ord_succ (ord_succ (ord_max o o0))))).

1-3,5-7,9-11 :  repeat split;
                try rewrite weak_ord_formula;
                try rewrite weak_ord_deg;
                try apply weak_ord_valid;
                unfold ptree_formula, ptree_deg, ptree_ord, valid;
                fold ptree_formula ptree_deg ptree_ord valid;
                try apply cut_elimination_formula;
                try apply cut_elimination_valid;
                try refine (T1F, T1V, T2F, T2V, _, _, _, _);
                try reflexivity;
                try apply dub_neg_valid;
                try rewrite dub_neg_ptree_deg;
                try rewrite dub_neg_ptree_formula;
                try rewrite dub_neg_ptree_ord;
                unfold dub_neg_sub_formula;
                try apply T1V;
                try apply T2V;
                try apply T1O;
                try apply T2O;
                try rewrite T1F;
                try rewrite T2F;
                try rewrite formula_sub_ind_lor;
                try rewrite non_target_sub;
                unfold formula_sub_ind, subst_ind_fit;
                fold subst_ind_fit;
                unfold formula_sub_ind_fit;
                try rewrite non_target_fit;
                try apply nf_2_exp;
                try apply NA;
                unfold cut_elimination, cut_elimination_atom, cut_elimination_neg, cut_elimination_lor, contraction_help, PA_omega_axiom, weak_ord_up;
                unfold ptree_formula; fold ptree_formula;
                try rewrite form_eqb_refl;
                try case (correct_a a) eqn:Ra;
                unfold ptree_deg, ptree_ord; fold ptree_deg ptree_ord;
                try rewrite (formula_sub_ptree_deg_neg _ _ _ T2V);
                try rewrite (formula_sub_ptree_ord_neg _ _ _ T2V);
                try rewrite (formula_sub_ptree_deg_atom _ _ _ T1V);
                try rewrite (formula_sub_ptree_ord_atom _ _ _ T1V);
                try rewrite <- T1O;
                try rewrite <- T2O;
                try rewrite (ord_lt_ltb _ _ (ord_2_exp_monot _ NA _ (ptree_ord_nf_hyp _ _ P2O P2V) (ord_lt_max_succ_r _ _)));
                try rewrite (ord_lt_ltb _ _ (ord_2_exp_monot _ NA _ (ptree_ord_nf_hyp _ _ P1O P1V) (ord_lt_max_succ_l _ _)));
                try rewrite (ord_max_ltb_not_l _ _ (ord_ltb_asymm _ _ (ord_lt_ltb _ _ (ord_lt_max_succ_r _ _))));
                unfold ptree_ord; fold ptree_ord;
                unfold num_conn in *; fold num_conn in *;
                try lia;
                try reflexivity;
                try rewrite (ord_max_symm o o0) in *;
                try rewrite (ord_max_symm (ord_2_exp o) _) in *;
                case (ord_ltb (ord_succ (ord_succ (ord_max (ord_2_exp o0) (ord_2_exp o)))) (ord_2_exp (ord_succ (ord_max o0 o)))) eqn:IO1;
                unfold ptree_ord; fold ptree_ord;
                try refine (ord_lt_trans _ _ _ _ (ord_ltb_lt _ _ IO1));
                try rewrite (ord_max_exp_comm _ _ (ptree_ord_nf_hyp _ _ P2O P2V) (ptree_ord_nf_hyp _ _ P1O P1V)) in *;
                try rewrite <- (ord_eqb_eq _ _ (dub_succ_geb_exp_succ_eqb _ (ord_succ_lt Zero _ IEO) (nf_succ_nf _ NA) IO1));
                try apply (ord_lt_trans _ _ _ (ord_succ_monot _) (dub_succ_exp_lt_exp_dub_succ _ (nf_succ_nf _ (nf_succ_nf _ NA))));
                try rewrite (ord_lt_ltb _ _ (dub_succ_exp_lt_exp_dub_succ _ (nf_succ_nf _ (nf_succ_nf _ NA))));
                try rewrite <- (ord_max_exp_comm _ _ (ptree_ord_nf_hyp _ _ P2O P2V) (ptree_ord_nf_hyp _ _ P1O P1V));
                repeat apply ord_lt_succ;
                try rewrite (ord_max_ltb_not_l _ _ (ord_ltb_asymm _ _ (ord_lt_ltb _ _ (ord_lt_max_succ_l _ _))));
                try apply (ord_lt_max_succ_l _ _);
                try apply (ord_lt_max_succ_r _ _);
                try apply ord_succ_monot;
                try apply (ord_2_exp_monot _ NA _ (ptree_ord_nf_hyp _ _ P2O P2V) (ord_lt_trans _ _ _ (ord_lt_max_succ_l _ _) (ord_succ_monot _)));
                try apply (ord_2_exp_monot _ NA _ (ptree_ord_nf_hyp _ _ P1O P1V) (ord_lt_trans _ _ _ (ord_lt_max_succ_r _ _) (ord_succ_monot _)));
                try reflexivity.

all : try destruct (and_bool_prop _ _ (provable_closed' _ _ T1V T1F)) as [Cf Cuf];
      try destruct (and_bool_prop _ _ (provable_closed' _ _ T2V T2F)) as [Cuf0 Cf0];
      unfold num_conn in *; fold closed num_conn in *;
      assert (ptree_deg T1 >= ptree_deg T1) as T1DE;
      try lia.

1,2 : assert (max (ptree_deg T1) (ptree_deg T2) < num_conn f0 + 2) as DLT; try lia.

3 : assert (max (ptree_deg T1) (ptree_deg T2) < num_conn f + 2) as DLT; try lia;
    assert (P_proves (weakening_ad f0 (univ n2 f) (ptree_deg T1) (ord_2_exp o) T1) (lor f0 (univ n2 f)) (ptree_deg T1) (ord_succ (ord_2_exp o))) as T3P.

3 : { repeat split.
      apply T1F.
      apply Cf0.
      apply T1V.
      apply T1O.
      unfold ptree_deg. lia. }

1 : pose proof (quantif_ptree_deg _ _ _ _ _ _ _ (T1F, T1V, T1DE, T1O) T2V DLT (1)) as QSD;
    exists (weak_ord_up (quantif_sub_ptree T2 _ _ _ _ _ _ (T1F, T1V, T1DE, T1O) (1)) (ord_2_exp (ord_succ (ord_max o o0)))).

2 : pose proof (quantif_ptree_deg _ _ _ _ _ _ _ (T1F, T1V, T1DE, T1O) T2V DLT (lor_ind (1) (non_target f1))) as QSD;
    exists (weak_ord_up (quantif_sub_ptree T2 _ _ _ _ _ _ (T1F, T1V, T1DE, T1O) (lor_ind (1) (non_target f1))) (ord_2_exp (ord_succ (ord_max o o0)))).

3 : pose proof (quantif_ptree_deg _ _ _ _ _ _ _ T3P T2V DLT (lor_ind (1) (non_target f0))) as QSD;
    exists (weak_ord_up (contraction_a f0 (ptree_deg (quantif_sub_ptree T2 _ _ _ _ _ _ T3P (lor_ind (1) (non_target f0)))) (ord_add (ord_succ (ord_2_exp o)) (ord_2_exp o0)) (weak_ord_up (quantif_sub_ptree T2 _ _ _ _ _ _ T3P (lor_ind (1) (non_target f0))) (ord_add (ord_succ (ord_2_exp o)) (ord_2_exp o0)))) (ord_2_exp (ord_succ (ord_succ (ord_max o o0))))).

all : repeat split;
      try apply weak_ord_valid;
      repeat split;
      try apply weak_ord_valid;
      try apply (quantif_valid _ _ _ _ _ _ _ _ T2V Cf DLT);
      try apply (quantif_valid _ _ _ _ _ _ _ _ T2V Cf0 DLT);
      try rewrite weak_ord_formula;
      try rewrite (quantif_ptree_formula _ _ _ _ _ _ _ _ T2V);
      try rewrite T2F;
      unfold quantif_sub_formula;
      unfold formula_sub_ind, subst_ind_fit, formula_sub_ind_fit;
      fold subst_ind_fit formula_sub_ind_fit;
      try rewrite non_target_fit;
      try rewrite non_target_sub';
      try rewrite form_eqb_refl;
      try reflexivity;
      try apply nf_2_exp;
      try apply NA;
      try rewrite weak_ord_deg;
      unfold ptree_deg; fold ptree_deg;
      try lia;
      try rewrite weak_ord_height;
      unfold ptree_ord; fold ptree_ord;
      try reflexivity.

3 : { apply nf_add;
      try apply nf_nf_succ;
      try apply (ptree_ord_nf_hyp _ _ T1O T1V);
      try apply (ptree_ord_nf_hyp _ _ T2O T2V). }

all : try refine (ord_geb_trans _ _ _ _ (quantif_ptree_ord _ _ _ _ _ _ _ _ T2V _));
      try rewrite <- T2O;
      try rewrite ord_ltb_irrefl;
      try apply (exp_succ_lt_add _ _ (ptree_ord_nf_hyp _ _ P1O P1V) (ptree_ord_nf_hyp _ _ P2O P2V));
      try reflexivity.

1 : rewrite <- ord_max_succ_succ.
    apply (ord_geb_trans _ _ _ (exp_succ_lt_add _ _ (nf_nf_succ _ (ptree_ord_nf_hyp _ _ P1O P1V)) (nf_nf_succ _ (ptree_ord_nf_hyp _ _ P2O P2V)))).
    apply (ord_geb_trans _ _ _ (ord_ltb_asymm _ _ (ord_lt_ltb _ _ (add_right_incr _ _ _ (ord_2_exp_monot _ (nf_nf_succ _ (ptree_ord_nf_hyp _ _ P2O P2V)) _ (ptree_ord_nf_hyp _ _ P2O P2V) (ord_succ_monot _)))))).
    apply add_left_weak_monot.
    destruct o.
    apply ord_ltb_irrefl.
    apply ord_ltb_asymm.
    apply ord_lt_ltb.
    apply ord_succ_lt_exp_succ.
    apply (ptree_ord_nf_hyp _ _ P1O P1V).
    apply zero_lt.
Qed.

Lemma cut_elim_aux1 :
    forall (alpha : ord) (P : ptree) (A : formula) (d : nat),
        P_proves P A (S d) alpha ->
            provable A d (ord_2_exp alpha).
Proof.
intros alpha P A d [[[PF' PV] PD'] PO'].
rewrite PO'.
apply (cut_elim_aux0 _ (ptree_ord_nf _ PV) P _ _ (PF', PV, PD', (eq_refl _))).
Qed.

Lemma cut_elim_aux2 :
    forall (A : formula) (d : nat),
        {alpha : ord & provable A d alpha} ->
            {beta : ord & provable A 0 beta}.
Proof.
intros A d aAP.
induction d.
- apply aAP.
- apply IHd.
  destruct aAP as [alpha [P PP]].
  exists (ord_2_exp alpha).
  apply (cut_elim_aux1 _ _ _ _ PP).
Qed.

Theorem cut_elim :
    forall (A : formula) (d : nat) (alpha : ord),
        provable A d alpha ->
            {beta : ord & provable A 0 beta}.
Proof.
intros.
apply (cut_elim_aux2 A d).
exists alpha.
auto.
Qed.