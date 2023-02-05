Add LoadPath "theories/Casteran" as Ordering.
Add LoadPath "theories/Maths" as Maths_Facts.
Add LoadPath "theories/Logic" as Systems.

From Maths_Facts Require Import naturals.
From Maths_Facts Require Import ordinals.

From Systems Require Import definitions.
From Systems Require Import fol.
From Systems Require Import PA_omega.
From Systems Require Import proof_trees.
From Systems Require Import substitute.
Require Import Lia.

Definition w_rule_sub_formula
  (A E : formula) (n : nat) (c : c_term) (S : subst_ind) : formula :=
  formula_sub_ind A (univ n E) (substitution E n (projT1 c)) S.

Lemma w_rule_sub_formula_closed :
    forall (A : formula),
        closed A = true ->
            forall (E : formula) (n : nat) (c : c_term) (S : subst_ind),
                closed (w_rule_sub_formula A E n c S) = true.
Proof.
intros A CA E n c S.
unfold w_rule_sub_formula.
apply (formula_sub_ind_closed _ _ _ CA).
intros CuE.
apply (closed_univ_sub E n CuE (projT1 c)).
destruct c as [t Ct].
apply Ct.
Qed.


Fixpoint w_rule_sub_ptree_fit
  (P : ptree) (E : formula) (n : nat) (c : c_term) (S : subst_ind) : ptree :=
match P, S with
| deg_up d P', _ => deg_up d (w_rule_sub_ptree_fit P' E n c S)

| ord_up alpha P', _ => ord_up alpha (w_rule_sub_ptree_fit P' E n c S)

| node A, _ => P

| exchange_ab A B d alpha P', lor_ind S_B S_A =>
    exchange_ab
      (w_rule_sub_formula A E n c S_A)
      (w_rule_sub_formula B E n c S_B)
      d alpha
      (w_rule_sub_ptree_fit P' E n c (lor_ind S_A S_B))

| exchange_cab C A B d alpha P', lor_ind (lor_ind S_C S_B) S_A =>
    exchange_cab
      (w_rule_sub_formula C E n c S_C)
      (w_rule_sub_formula A E n c S_A)
      (w_rule_sub_formula B E n c S_B)
      d alpha
      (w_rule_sub_ptree_fit P' E n c (lor_ind (lor_ind S_C S_A) S_B))

| exchange_abd A B D d alpha P', lor_ind (lor_ind S_B S_A) S_D =>
    exchange_abd
      (w_rule_sub_formula A E n c S_A)
      (w_rule_sub_formula B E n c S_B)
      (w_rule_sub_formula D E n c S_D)
      d alpha
      (w_rule_sub_ptree_fit P' E n c (lor_ind (lor_ind S_A S_B) S_D))

| exchange_cabd C A B D d alpha P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D =>
    exchange_cabd
      (w_rule_sub_formula C E n c S_C)
      (w_rule_sub_formula A E n c S_A)
      (w_rule_sub_formula B E n c S_B)
      (w_rule_sub_formula D E n c S_D)
      d alpha
      (w_rule_sub_ptree_fit
        P' E n c
        (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D))

| contraction_a A d alpha P', _ =>
    contraction_a
      (w_rule_sub_formula A E n c S)
      d alpha
      (w_rule_sub_ptree_fit P' E n c (lor_ind S S))

| contraction_ad A D d alpha P', lor_ind S_A S_D =>
    contraction_ad
      (w_rule_sub_formula A E n c S_A)
      (w_rule_sub_formula D E n c S_D)
      d alpha
      (w_rule_sub_ptree_fit P' E n c (lor_ind (lor_ind S_A S_A) S_D))

| weakening_ad A D d alpha P', lor_ind S_A S_D =>
    weakening_ad
      (w_rule_sub_formula A E n c S_A)
      (w_rule_sub_formula D E n c S_D)
      d alpha
      (w_rule_sub_ptree_fit P' E n c S_D)

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, _ => P

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_AB S_D =>
    demorgan_abd
      A B
      (w_rule_sub_formula D E n c S_D)
      d1 d2 alpha1 alpha2
      (w_rule_sub_ptree_fit P1 E n c (lor_ind (0) S_D))
      (w_rule_sub_ptree_fit P2 E n c (lor_ind (0) S_D))

| negation_a A d alpha P', _ => P

| negation_ad A D d alpha P', lor_ind S_A S_D =>
    negation_ad
      A
      (w_rule_sub_formula D E n c S_D)
      d alpha
      (w_rule_sub_ptree_fit P' E n c (lor_ind (non_target A) S_D))

| quantification_a A k t d alpha P', _ => P

| quantification_ad A D k t d alpha P', lor_ind S_A S_D =>
    quantification_ad
      A
      (w_rule_sub_formula D E n c S_D)
      k t d alpha
      (w_rule_sub_ptree_fit P' E n c (lor_ind (0) S_D))

| w_rule_a A k d alpha g, _ =>
    (match eq_f A E, eq_nat d (ptree_deg (g c)), eq_nat k n, S with
    | true, true, true, (1) => ord_up (ord_succ alpha) (g c)
    | true, false, true, (1) => deg_up d (ord_up (ord_succ alpha) (g c))
    | _, _, _, _ => P
    end)

| w_rule_ad A D k d alpha g, lor_ind S_A S_D =>
    (match eq_f A E, eq_nat d (ptree_deg (g c)), eq_nat k n, S_A with
    | true, true, true, (1) =>
        ord_up (ord_succ alpha) (w_rule_sub_ptree_fit (g c) E n c (lor_ind (non_target A) S_D))
    | true, false, true, (1) =>
        deg_up d (ord_up (ord_succ alpha) (w_rule_sub_ptree_fit (g c) E n c (lor_ind (non_target A) S_D)))
    
    | _, _, _, _ => 
        w_rule_ad
          A
          (w_rule_sub_formula D E n c S_D)
          k d alpha
          (fun (t : c_term) =>
            w_rule_sub_ptree_fit (g t) E n c (lor_ind (non_target A) S_D))
    end)

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ca
      (w_rule_sub_formula C E n c S)
      A d1 d2 alpha1 alpha2
      (w_rule_sub_ptree_fit P1 E n c (lor_ind S (non_target A)))
      P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ad
      A
      (w_rule_sub_formula D E n c S)
      d1 d2 alpha1 alpha2
      P1
      (w_rule_sub_ptree_fit P2 E n c (lor_ind (0) S))

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_D =>
    cut_cad
      (w_rule_sub_formula C E n c S_C)
      A
      (w_rule_sub_formula D E n c S_D)
      d1 d2 alpha1 alpha2
      (w_rule_sub_ptree_fit P1 E n c (lor_ind S_C (non_target A)))
      (w_rule_sub_ptree_fit P2 E n c (lor_ind (0) S_D))

| _, _ => P
end.

Definition w_rule_sub_ptree
  (P : ptree) (E : formula) (n : nat) (c : c_term) (S : subst_ind) : ptree :=
match subst_ind_fit (ptree_formula P) S with
| false => P
| true => w_rule_sub_ptree_fit P E n c S
end.


(*
Lemma w_rule_simp :
    forall (P : ptree) (E : formula) (n : nat) (c : c_term) (S : subst_ind),
          subst_ind_fit (ptree_formula P) S = true ->
              w_rule_sub_ptree P E n c S = w_rule_sub_ptree_fit P E n c S .
Proof.
intros.
destruct P; simpl; simpl in H; rewrite H; auto.
Qed.
*)

(*
Lemma w_rule_ptree_formula_aux' :
  forall (P : ptree) (E : formula) (n : nat) (c : c_term) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
    w_rule_sub_ptree P E n c S = P.
Proof. intros. unfold w_rule_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma w_rule_ptree_formula_aux :
  forall (P : ptree) (E : formula) (n : nat) (c : c_term) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
      ptree_formula (w_rule_sub_ptree P E n c S) =
      w_rule_sub_formula (ptree_formula P) E n c S.
Proof.
intros. rewrite w_rule_ptree_formula_aux'.
- unfold w_rule_sub_formula. rewrite sub_fit_false. auto. apply H.
- apply H.
Qed.
*)

Lemma w_rule_ptree_formula_true :
    forall (P : ptree) (E : formula) (n : nat) (c : c_term) (S : subst_ind),
        subst_ind_fit (ptree_formula P) S = true ->
            w_rule_sub_ptree_fit P E n c S = w_rule_sub_ptree P E n c S.
Proof.
intros P E n c S FS.
unfold w_rule_sub_ptree.
rewrite FS.
reflexivity.
Qed.

Lemma w_rule_ptree_formula' :
    forall (P : ptree) (E : formula) (n : nat) (c : c_term),
        valid P ->
            forall (S : subst_ind),
                subst_ind_fit (ptree_formula P) S = true ->
                    ptree_formula (w_rule_sub_ptree P E n c S) =
                        w_rule_sub_formula (ptree_formula P) E n c S.
Proof.
intros P E n c.
induction P; try intros PV S FS;
unfold w_rule_sub_ptree;
rewrite FS;
unfold ptree_formula in *; fold ptree_formula in *;
unfold w_rule_sub_ptree_fit; fold w_rule_sub_ptree_fit.
  
1 : destruct PV as [ID PV].
2 : destruct PV as [[IO PV] NO].

1-2 : rewrite (w_rule_ptree_formula_true _ _ _ _ _ FS);
      unfold ptree_formula; fold ptree_formula;
      apply (IHP PV _ FS).

1 : { inversion PV as [PX].
      unfold w_rule_sub_ptree, w_rule_sub_formula, formula_sub_ind.
      rewrite FS.
      unfold ptree_formula; fold ptree_formula.
      destruct (axiom_atomic _ PX) as [[a fa] | [a fa]];
      rewrite fa;
      unfold formula_sub_ind_fit; fold formula_sub_ind_fit;
      unfold eq_f;
      reflexivity. }

all : destruct S; inversion FS as [FS'];
      try reflexivity.

1,5,6,13 :  apply and_bool_prop in FS';
            destruct FS' as [FS1 FS2];
            unfold ptree_formula, w_rule_sub_formula, formula_sub_ind, formula_sub_ind_fit;
            fold formula_sub_ind_fit;
            rewrite FS,FS1,FS2;
            reflexivity.

9 : destruct (PV c) as [[[PF PCV ] PD] PO];
    assert (subst_ind_fit (ptree_formula (p c)) (lor_ind (non_target f) S2) = true) as FSP.
9 : { rewrite PF.
      unfold subst_ind_fit; fold subst_ind_fit.
      rewrite non_target_sub_fit.
      unfold "&&".
      destruct S1;
      try inversion FS' as [FS''];
      reflexivity. }


8 : { destruct (PV c) as [[[PF PCV ] PD] PO].
      case (eq_f f E) eqn:EQ1;
      case (eq_nat n0 n) eqn:EQ2;
      case (eq_nat n1 (ptree_deg (p c))) eqn:E3;
      unfold ptree_formula, w_rule_sub_formula;
      fold ptree_formula;
      try rewrite PF;
      try apply f_eq_decid in EQ1;
      try rewrite EQ1;
      try apply nat_eq_decid in EQ2;
      try rewrite EQ2;
      try rewrite (formula_sub_ind_1 _ _ FS);
      unfold formula_sub_ind, subst_ind_fit, formula_sub_ind_fit, eq_f;
      fold eq_f;
      try rewrite eq_nat_refl;
      try rewrite eq_f_refl;
      try rewrite EQ1;
      try rewrite EQ2;
      unfold "&&";
      try reflexivity. }

7 : { case (eq_f f E) eqn:EQ1;
      case (eq_nat n0 n) eqn:EQ2;
      case (eq_nat n1 (ptree_deg (p c))) eqn:E3;
      unfold ptree_formula, w_rule_sub_formula;
      fold ptree_formula;
      try rewrite formula_sub_ind_0;
      try reflexivity. }

all : destruct S1; inversion FS' as [FS''].

1-3 : apply and_bool_prop in FS';
      destruct FS' as [FS1 FS2];
      apply and_bool_prop in FS1;
      destruct FS1 as [FS1_1 FS1_2].

3 : destruct S1_1; inversion FS'' as [FS'''];
    apply and_bool_prop in FS1_1;
    destruct FS1_1 as [FS1_1_1 FS1_1_2].
  

10,11 : case (eq_f f E) eqn:EQ1;
        case (eq_nat n0 n) eqn:EQ2;
        case (eq_nat n1 (ptree_deg (p c))) eqn:E3.

all : unfold ptree_formula, w_rule_sub_formula, formula_sub_ind, formula_sub_ind_fit, eq_f;
      fold ptree_formula eq_f formula_sub_ind_fit;
      try rewrite FS;
      try rewrite FS'';
      try rewrite EQ1;
      try rewrite EQ2;
      try rewrite FS1_1,FS1_2,FS2;
      try rewrite FS1_1_1,FS1_1_2,FS1_2,FS2;      
      unfold "&&";
      try reflexivity.

all : apply f_eq_decid in EQ1;
      destruct EQ1;
      apply nat_eq_decid in EQ2;
      destruct EQ2;
      rewrite (w_rule_ptree_formula_true _ _ _ _ _ FSP);
      rewrite (H _ PCV _ FSP);
      rewrite PF in *;
      unfold w_rule_sub_formula, formula_sub_ind, formula_sub_ind_fit;
      fold formula_sub_ind_fit;
      rewrite FSP;
      rewrite (non_target_term_sub _ n0 (projT1 c));
      rewrite non_target_sub';
      reflexivity.
Qed.

Lemma w_rule_ptree_formula :
    forall (P : ptree) (E : formula) (n : nat) (c : c_term),
        valid P ->
            forall (S : subst_ind),
                ptree_formula (w_rule_sub_ptree P E n c S) =
                    w_rule_sub_formula (ptree_formula P) E n c S.
Proof.
intros P E n c VP S.
destruct (subst_ind_fit (ptree_formula P) S) eqn:FS.
- apply (w_rule_ptree_formula' _ _ _ _ VP _ FS).
- unfold w_rule_sub_ptree, w_rule_sub_formula, formula_sub_ind.
  rewrite FS.
  reflexivity.
Qed.

Lemma w_rule_ptree_deg :
    forall (P : ptree) (E : formula) (n : nat) (c : c_term),
        valid P ->
            forall (S : subst_ind),
                ptree_deg (w_rule_sub_ptree P E n c S) = ptree_deg P.
Proof.
intros P E n c PV.
unfold w_rule_sub_ptree.
pose (ptree_formula P) as A.
induction P; intros S;
case (subst_ind_fit A S) eqn:FS;
unfold A in FS;
try rewrite FS;
unfold w_rule_sub_ptree_fit; fold w_rule_sub_ptree_fit;
unfold ptree_deg in *; fold ptree_deg in *;
try reflexivity.

1 : destruct PV as [[IO PV] NO].

11,12 : destruct (PV c) as [[[PF PCV] PD] PO].

1 : unfold ptree_formula in FS; fold ptree_formula in FS.
    pose proof (IHP PV S) as IHPS.
    rewrite FS in IHPS.
    apply IHPS.

all : destruct S; inversion FS as [FS'];
      try reflexivity.

4-6 : case (eq_f f E) eqn:EQ1;
      case (eq_nat n0 n) eqn:EQ2;
      case (eq_nat n1 (ptree_deg (p c))) eqn:EQ3;
      unfold ptree_deg; fold ptree_deg;
      try apply f_eq_decid in EQ1;
      try destruct EQ1;
      try apply nat_eq_decid in EQ2,EQ3;
      try rewrite EQ3;
      try reflexivity.

all : destruct S1; inversion FS' as [FS''].

3 : destruct S1_1; inversion FS'' as [FS'''].

all : unfold ptree_deg; fold ptree_deg;
      try reflexivity.

- assert (subst_ind_fit (ptree_formula (p c)) (lor_ind (non_target f) S2) = true) as FSP.
  { rewrite PF.
    unfold subst_ind_fit; fold subst_ind_fit.
    rewrite non_target_sub_fit.
    unfold "&&".
    apply FS''. }
  pose proof (H _ PCV (lor_ind (non_target f) S2)) as IHPS.
  rewrite FSP in IHPS.
  apply IHPS.
Qed.

(* *)
Lemma w_rule_ptree_ord :
    forall (P : ptree) (E : formula) (n : nat) (c : c_term),
        valid P ->
            forall (S : subst_ind),
                ptree_ord (w_rule_sub_ptree P E n c S) = ptree_ord P.
Proof.
intros P E n c PV.
unfold w_rule_sub_ptree.
pose (ptree_formula P) as A.
induction P; intros S;
case (subst_ind_fit A S) eqn:FS;
unfold A in FS;
try rewrite FS;
unfold w_rule_sub_ptree_fit; fold w_rule_sub_ptree_fit;
unfold ptree_ord in *; fold ptree_ord in *;
try reflexivity.

1 : destruct PV as [ID PV].

11,12 : destruct (PV c) as [[[PF PCV] PD] PO].

1 : unfold ptree_formula in FS; fold ptree_formula in FS.
    pose proof (IHP PV S) as IHPS.
    rewrite FS in IHPS.
    apply IHPS.

all : destruct S; inversion FS as [FS'];
      try reflexivity.

4-6 : case (eq_f f E) eqn:EQ1;
      case (eq_nat n0 n) eqn:EQ2;
      case (eq_nat n1 (ptree_deg (p c))) eqn:EQ3;
      unfold ptree_deg; fold ptree_deg;
      try apply f_eq_decid in EQ1;
      try destruct EQ1;
      try apply nat_eq_decid in EQ2,EQ3;
      try apply EQ3;
      try reflexivity.

all : destruct S1; inversion FS' as [FS''].

3 : destruct S1_1; inversion FS'' as [FS'''].

all : unfold ptree_deg; fold ptree_deg;
      try reflexivity.
Qed.

(* *)
Lemma w_rule_valid :
    forall (P : ptree) (E : formula) (n : nat) (c : c_term),
        valid P ->
            forall (S : subst_ind),
                subst_ind_fit (ptree_formula P) S = true ->
                    valid (w_rule_sub_ptree P E n c S).
Proof.
intros P E n c PV.
induction P; try intros S FS;
unfold w_rule_sub_ptree;
rewrite FS;
unfold ptree_formula in *; fold ptree_formula in *;
unfold w_rule_sub_ptree_fit; fold w_rule_sub_ptree_fit.

all : try apply PV.

1 : destruct PV as [ID PV].
2 : destruct PV as [[IO PV] NO].
3-8 : destruct PV as [[[PF PV] PD] PO].
9 : destruct PV as [[[[PF FC] PV] PD] PO].
11-12 : destruct PV as [[[PF PV] PD] PO].
10,15,16,17: destruct PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].

3,4,5,6,8,9,10,13,14,15,16,17 : destruct S; inversion FS as [FS'];
                                try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

15 :  assert (valid (w_rule_ad f (w_rule_sub_formula f0 E n c S2) n0 n1 o (fun t : c_term => w_rule_sub_ptree_fit (p t) E n c (lor_ind (non_target f) S2)))) as VSC.
15 :  { assert (forall t, subst_ind_fit (ptree_formula (p t)) (lor_ind (non_target f) S2) = true) as FSt.
        { intros t.
          destruct (PV t) as [[[PF PTV] PD] PO].
          rewrite PF.
          unfold subst_ind_fit; fold subst_ind_fit.
          rewrite non_target_sub_fit.
          unfold "&&".
          apply FS2. }
        repeat split;
        destruct (PV t) as [[[PF PTV] PD] PO];
        rewrite (w_rule_ptree_formula_true _ _ _ _ _ (FSt t)).
        - rewrite (w_rule_ptree_formula _ _ _ _ PTV).
          rewrite PF.
          unfold w_rule_sub_formula.
          rewrite (non_target_term_sub _ n0 (projT1 t)).
          rewrite non_target_sub_lor.
          reflexivity.
        - apply (X _ PTV _ (FSt t)).
        - rewrite (w_rule_ptree_deg _ _ _ _ PTV).
          apply PD.
        - rewrite (w_rule_ptree_ord _ _ _ _ PTV).
          apply PO. }

4,5,6,15 :  destruct S1; inversion FS' as [FS''];
            try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

6 : destruct S1_1; inversion FS'' as [FS'''];
    destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

10 :  assert (closed (univ n E) = true -> closed (substitution E n (projT1 c)) = true) as CIMP.
10 :  { intros CE.
        apply (closed_univ_sub _ _ CE).
        destruct c as [t Ct].
        apply Ct. }

7,8,15,16 : destruct (PV c) as [[[PF PCV] PD] PO].

9,10 :  case (eq_f f E) eqn:EQ1;
        case (eq_nat n0 n) eqn:EQ2;
        case (eq_nat n1 (ptree_deg (p c))) eqn:EQ3;
        try apply PV;
        repeat split;
        try rewrite PO;
        unfold ptree_deg;fold ptree_deg;
        try apply ord_succ_monot;
        try apply ord_succ_nf;
        try apply ptree_ord_nf;
        try apply PCV;
        inversion PD as [EQ4 | ];
        try destruct EQ4;
        try rewrite eq_nat_refl in EQ3;
        inversion EQ3;
        try lia.

7,8 : case (eq_f f E) eqn:EQ1;
      case (eq_nat n0 n) eqn:EQ2;
      case (eq_nat n1 (ptree_deg (p c))) eqn:EQ3;
      try apply VSC.

all : try apply f_eq_decid in EQ1;
      try destruct EQ1;
      repeat rewrite w_rule_ptree_formula_true;
      repeat split;
      try apply IHP;
      try apply IHP1;
      try apply IHP2;
      unfold ptree_deg; fold ptree_deg;
      try rewrite w_rule_ptree_deg;
      try rewrite w_rule_ptree_ord;
      try rewrite w_rule_ptree_formula;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold w_rule_sub_formula, formula_sub_ind;
      try apply PV;
      try rewrite PD;
      try rewrite PO;
      try apply P1V;
      try rewrite P1D;
      try rewrite P1O;
      try apply P2V;
      try rewrite P2D;
      try rewrite P2O;
      try apply ID;
      try apply IO;
      try apply NO;
      try apply (X _ PCV);
      try rewrite PF;
      unfold subst_ind_fit; fold subst_ind_fit;
      try rewrite non_target_fit;
      try rewrite non_target_sub_fit;
      try rewrite FS;
      try rewrite FS';
      try rewrite FS'';
      try rewrite FS1;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      try rewrite FS2;
      unfold "&&";
      unfold formula_sub_ind_fit; fold formula_sub_ind_fit;
      unfold eq_f; fold eq_f;
      try rewrite non_target_sub';
      try rewrite <- (sub_fit_true _ _ _ _ FS1);
      try apply (formula_sub_ind_closed _ _ _ FC CIMP);
      try apply ord_succ_monot;
      try apply ord_succ_nf;
      try apply ptree_ord_nf;
      try apply PCV;
      unfold subst_ind_fit; fold subst_ind_fit;
      try reflexivity.
      inversion PD as [EQ4 | ];
      try destruct EQ4;
      try rewrite eq_nat_refl in EQ3;
      try lia.
Qed.


(*

(* We finally show that if the formulas (univ n E) and/or (univ n E) \/ D are provable,
so are the formulas E(m) and/or E(m) \/ D for any c *)
(* *)
Lemma w_rule_invertible_a :
  forall (A : formula) (n d : nat) (alpha : ord) (c : c_term),
  provable (univ n A) d alpha ->
  provable (substitution A n (projT1 c)) d alpha.
Proof.
unfold provable. intros A n d alpha c H.
destruct H as [t [[[Ht1 Ht2] Ht3] Ht4]].
exists (w_rule_sub_ptree t A n c (1)). unfold P_proves. repeat split.
- rewrite w_rule_ptree_formula; auto. rewrite Ht1. unfold w_rule_sub_formula.
  simpl. rewrite eq_nat_refl,eq_f_refl. auto.
- apply w_rule_valid; auto. rewrite Ht1. auto.
- rewrite <- (w_rule_ptree_deg t); auto.
- rewrite w_rule_ptree_ord; auto.
Qed.

Lemma w_rule_invertible_ad :
  forall (A D : formula) (n d : nat) (alpha : ord) (c : c_term),
  provable (lor (univ n A) D) d alpha ->
  provable (lor (substitution A n (projT1 c)) D) d alpha.
Proof.
unfold provable. intros A D n d alpha c H.
destruct H as [t [[[Ht1 Ht2] Ht3] Ht4]].
pose proof (w_rule_ptree_deg t A n c Ht2 (lor_ind (1) (non_target D))).
exists (w_rule_sub_ptree t A n c (lor_ind (1) (non_target D))). unfold P_proves. repeat split.
- rewrite w_rule_ptree_formula; auto. rewrite Ht1. unfold w_rule_sub_formula.
  simpl. rewrite eq_nat_refl,eq_f_refl,non_target_fit. simpl.
  rewrite non_target_sub'. auto.
- apply w_rule_valid; auto. rewrite Ht1. simpl. rewrite non_target_fit. auto.
- rewrite <- (w_rule_ptree_deg t); auto.
- rewrite w_rule_ptree_ord; auto.
Qed. *)

Lemma w_rule_invertible_cut_ad :
    forall (P : ptree) (A : formula) (n d : nat) (alpha : ord) (c : c_term),
        P_proves P (univ n A) d alpha ->
            provable (substitution A n (projT1 c)) d alpha.
Proof.
unfold provable.
intros P A n d alpha c [[[PF PV] PD] PO].
exists (w_rule_sub_ptree P A n c (1)).
repeat split.
- rewrite (w_rule_ptree_formula _ _ _ _ PV).
  rewrite PF.
  unfold w_rule_sub_formula, formula_sub_ind, formula_sub_ind_fit, subst_ind_fit.
  rewrite eq_f_refl.
  reflexivity.
- apply (w_rule_valid _ _ _ _ PV).
  rewrite PF.
  unfold subst_ind_fit.
  reflexivity.
- rewrite ((w_rule_ptree_deg P) _ _ _ PV).
  apply PD.
- rewrite ((w_rule_ptree_ord P) _ _ _ PV).
  apply PO.
Defined.

Lemma w_rule_invertible_cut_cad :
    forall (P : ptree) (A D : formula) (n d : nat) (alpha : ord) (c : c_term),
        P_proves P (lor D (univ n A)) d alpha ->
            provable (lor D (substitution A n (projT1 c))) d alpha.
Proof.
unfold provable.
intros P A D n d alpha c [[[PF PV] PD] PO].
assert (valid (exchange_ab D (univ n A) (ptree_deg P) alpha P)).
{ repeat split. apply PF. apply PV. symmetry. apply PO. }
exists (exchange_ab (substitution A n (projT1 c)) D (ptree_deg P) alpha (w_rule_sub_ptree (exchange_ab D (univ n A) (ptree_deg P) alpha P) A n c (lor_ind (1) (non_target D)))).
repeat split.
- unfold w_rule_sub_ptree, subst_ind_fit, ptree_formula, w_rule_sub_ptree_fit;
  fold subst_ind_fit w_rule_sub_ptree_fit.
  unfold w_rule_sub_formula, "&&".
  rewrite non_target_sub, non_target_fit.
  unfold formula_sub_ind, formula_sub_ind_fit, subst_ind_fit.
  rewrite eq_f_refl.
  reflexivity.
- apply (w_rule_valid _ _ _ _ X).
  unfold ptree_formula, subst_ind_fit.
  fold subst_ind_fit.
  unfold "&&".
  apply non_target_fit.
- rewrite (w_rule_ptree_deg _ _ _ _ X).
  unfold ptree_deg.
  reflexivity.
- rewrite (w_rule_ptree_ord _ _ _ _ X).
  unfold ptree_ord.
  reflexivity.
- apply PD.
Defined.
