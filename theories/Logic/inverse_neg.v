Add LoadPath "theories/Casteran" as Ordering.
Add LoadPath "theories/Maths" as Maths_Facts.
Add LoadPath "theories/Logic" as Systems.

From Maths_Facts Require Import naturals.
From Maths_Facts Require Import ordinals.

From Systems Require Import definitions.
From Systems Require Import fol.
From Systems Require Import proof_trees.
From Systems Require Import substitute.


Definition dub_neg_sub_formula (A E : formula) (S : subst_ind) : formula :=
  formula_sub_ind A (neg (neg E)) E S.

Lemma dub_neg_sub_formula_closed :
    forall (A : formula),
        closed A = true ->
            forall (E : formula) (S : subst_ind),
                closed (dub_neg_sub_formula A E S) = true.
Proof.
intros A CA E S.
unfold dub_neg_sub_formula.
apply (formula_sub_ind_closed _ _ _ CA).
unfold closed; fold closed.
intros CE.
apply CE.
Qed.


Fixpoint dub_neg_sub_ptree_fit
  (P : ptree) (E : formula) (S : subst_ind) : ptree :=
match P, S with
| deg_up d P', _ => deg_up d (dub_neg_sub_ptree_fit P' E S)

| ord_up alpha P', _ => ord_up alpha (dub_neg_sub_ptree_fit P' E S)

| node A, _ => P

| exchange_ab A B d alpha P', lor_ind S_B S_A =>
    exchange_ab
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula B E S_B)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind S_A S_B))

| exchange_cab C A B d alpha P', lor_ind (lor_ind S_C S_B) S_A =>
    exchange_cab
      (dub_neg_sub_formula C E S_C)
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula B E S_B)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind (lor_ind S_C S_A) S_B))

| exchange_abd A B D d alpha P', lor_ind (lor_ind S_B S_A) S_D =>
    exchange_abd
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula B E S_B)
      (dub_neg_sub_formula D E S_D)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind (lor_ind S_A S_B) S_D))

| exchange_cabd C A B D d alpha P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D =>
    exchange_cabd
      (dub_neg_sub_formula C E S_C)
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula B E S_B)
      (dub_neg_sub_formula D E S_D)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D))

| contraction_a A d alpha P', _ =>
    contraction_a
      (dub_neg_sub_formula A E S)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind S S))

| contraction_ad A D d alpha P', lor_ind S_A S_D =>
    contraction_ad
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula D E S_D)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind (lor_ind S_A S_A) S_D))

| weakening_ad A D d alpha P', lor_ind S_A S_D =>
    (weakening_ad
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula D E S_D)
      d alpha
      (dub_neg_sub_ptree_fit P' E S_D))

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, _ => P

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_AB S_D =>
    demorgan_abd
      A B (dub_neg_sub_formula D E S_D) d1 d2 alpha1 alpha2
      (dub_neg_sub_ptree_fit P1 E (lor_ind (0) S_D))
      (dub_neg_sub_ptree_fit P2 E (lor_ind (0) S_D))

| negation_a A d alpha P', _ =>
    (match eq_f A E, S with
    | true, (1) => ord_up (ord_succ alpha) P'
    | _, _ => P
    end)

| negation_ad A D d alpha P', lor_ind S_A S_D =>
    (match eq_f A E, S_A with
    | true, (1) => ord_up (ord_succ alpha) (dub_neg_sub_ptree_fit P' E (lor_ind (non_target A) S_D))
    | _, _ => 
        negation_ad
          A
          (dub_neg_sub_formula D E S_D)
          d alpha
          (dub_neg_sub_ptree_fit P' E (lor_ind (non_target A) S_D))
    end)

| quantification_a A n t d alpha P', _ => P

| quantification_ad A D n t d alpha P', lor_ind S_A S_D =>
    quantification_ad
      A
      (dub_neg_sub_formula D E S_D)
      n t d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind (0) S_D))


| w_rule_a A n d alpha g, _ => P

| w_rule_ad A D n d alpha g, lor_ind S_A S_D =>
    w_rule_ad
      A
      (dub_neg_sub_formula D E S_D)
      n
      d alpha
      (fun (t : c_term) =>
          dub_neg_sub_ptree_fit (g t) E (lor_ind (non_target A) S_D))

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ca
      (dub_neg_sub_formula C E S)
      A d1 d2 alpha1 alpha2
      (dub_neg_sub_ptree_fit P1 E (lor_ind S (non_target A)))
      P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ad
      A (dub_neg_sub_formula D E S) d1 d2 alpha1 alpha2
      P1
      (dub_neg_sub_ptree_fit P2 E (lor_ind (0) S))

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_D =>
    cut_cad
      (dub_neg_sub_formula C E S_C)
      A (dub_neg_sub_formula D E S_D) d1 d2 alpha1 alpha2
      (dub_neg_sub_ptree_fit P1 E (lor_ind S_C (non_target A)))
      (dub_neg_sub_ptree_fit P2 E (lor_ind (0) S_D))

| _, _ => P
end.

Definition dub_neg_sub_ptree (P : ptree) (E : formula) (S : subst_ind) : ptree :=
match subst_ind_fit (ptree_formula P) S with
| false => P
| true => dub_neg_sub_ptree_fit P E S
end.


(* First, we must prove that dub_neg_sub_ptree simply changes the base formula
of an ptree the way we expect with dub_neg_sub_formula *)
(* *)

(*
Lemma dub_neg_ptree_formula_aux' :
    forall (P : ptree) (E : formula) (S : subst_ind),
      subst_ind_fit (ptree_formula P) S = false ->
          dub_neg_sub_ptree P E S = P.
Proof.
intros P E S FS.
unfold dub_neg_sub_ptree.
rewrite FS.
reflexivity.
Qed.
*)
(*
Lemma dub_neg_ptree_formula_aux :
  forall (P : ptree) (E : formula) (S : subst_ind),
      subst_ind_fit (ptree_formula P) S = false ->
          ptree_formula (dub_neg_sub_ptree P E S) =
              dub_neg_sub_formula (ptree_formula P) E S.
Proof.
intros P E S FS.
rewrite (dub_neg_ptree_formula_aux' _ _ _ FS).
unfold dub_neg_sub_formula.
symmetry.
apply (sub_fit_false _ _ _ _ FS). 
Qed.
*)

Lemma dub_neg_ptree_formula_true :
    forall (P : ptree) (E : formula) (S : subst_ind),
        subst_ind_fit (ptree_formula P) S = true ->
            dub_neg_sub_ptree_fit P E S = dub_neg_sub_ptree P E S.
Proof. intros. unfold dub_neg_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma dub_neg_ptree_formula' : forall (P : ptree) (E : formula),
  valid P ->
      forall (S : subst_ind),
          subst_ind_fit (ptree_formula P) S = true ->
              ptree_formula (dub_neg_sub_ptree P E S) =
                  dub_neg_sub_formula (ptree_formula P) E S.
Proof.
intros P E.
induction P; try intros PV S FS;
unfold dub_neg_sub_ptree;
rewrite FS;
unfold ptree_formula in *; fold ptree_formula in *;
unfold dub_neg_sub_ptree_fit; fold dub_neg_sub_ptree_fit.
  
1 : destruct PV as [ID PV].
2 : destruct PV as [[IO PV] NO].
13-14 : destruct PV as [[[PF PV] PD] PO].

1-2 : rewrite (dub_neg_ptree_formula_true _ _ _ FS);
      unfold ptree_formula; fold ptree_formula;
      apply (IHP PV _ FS).

1 : { inversion PV as [PX].
      unfold dub_neg_sub_ptree, dub_neg_sub_formula, formula_sub_ind.
      rewrite FS.
      unfold ptree_formula; fold ptree_formula.
      destruct (axiom_atomic _ PX) as [[a fa] | [a fa]];
      rewrite fa;
      unfold formula_sub_ind_fit; fold formula_sub_ind_fit;
      unfold eq_f;
      reflexivity. }

5 : reflexivity.

all : destruct S; inversion FS as [FS'];
      try reflexivity.

1,5,6,13 :  apply and_bool_prop in FS';
            destruct FS' as [FS1 FS2];
            unfold ptree_formula, dub_neg_sub_formula, formula_sub_ind, formula_sub_ind_fit;
            fold formula_sub_ind_fit;
            rewrite FS,FS1,FS2;
            reflexivity.

5-6 : case (eq_f f E) eqn:EQ;
      unfold ptree_formula, dub_neg_sub_formula, formula_sub_ind, subst_ind_fit, formula_sub_ind_fit, eq_f;
      fold ptree_formula eq_f;
      rewrite EQ;
      try reflexivity.

5 : apply f_eq_decid in EQ;
    destruct EQ;
    apply PF.

all : destruct S1; inversion FS' as [FS''].

1-3 : apply and_bool_prop in FS';
      destruct FS' as [FS1 FS2];
      apply and_bool_prop in FS1;
      destruct FS1 as [FS1_1 FS1_2].

3 : destruct S1_1; inversion FS'' as [FS'''];
    apply and_bool_prop in FS1_1;
    destruct FS1_1 as [FS1_1_1 FS1_1_2].

5-7 : case (eq_f f E) eqn:EQ.

all : unfold ptree_formula, dub_neg_sub_formula, formula_sub_ind, formula_sub_ind_fit, eq_f;
      fold ptree_formula eq_f formula_sub_ind_fit;
      try rewrite FS;
      try rewrite FS'';
      try rewrite EQ;
      try rewrite FS1_1,FS1_2,FS2;
      try rewrite FS1_1_1,FS1_1_2,FS1_2,FS2;      
      unfold "&&";
      try reflexivity.

- apply f_eq_decid in EQ.
  destruct EQ.
  assert (subst_ind_fit (ptree_formula P) (lor_ind (non_target f) S2) = true) as FSP.
  { rewrite PF.
    unfold subst_ind_fit; fold subst_ind_fit.
    rewrite non_target_fit.
    unfold "&&".
    apply FS''. }
  rewrite (dub_neg_ptree_formula_true _ _ _ FSP).
  rewrite (IHP PV _ FSP).
  rewrite PF in *.
  unfold dub_neg_sub_formula, formula_sub_ind, formula_sub_ind_fit.
  fold formula_sub_ind_fit.
  rewrite FSP.
  rewrite non_target_sub'.
  reflexivity.
Qed.


Lemma dub_neg_ptree_formula :
    forall (P : ptree) (E : formula),
        valid P ->
            forall (S : subst_ind),
                ptree_formula (dub_neg_sub_ptree P E S) =
                    dub_neg_sub_formula (ptree_formula P) E S.
Proof.
intros P E PV S.
destruct (subst_ind_fit (ptree_formula P) S) eqn:FS.
- apply (dub_neg_ptree_formula' _ _ PV _ FS).
- unfold dub_neg_sub_ptree, dub_neg_sub_formula, formula_sub_ind.
  rewrite FS.
  reflexivity.
Qed.





(* Second, we must prove that dub_neg_sub_ptree does not change the degree
of an ptree. *)
(* *)
Lemma dub_neg_ptree_deg :
    forall (P : ptree) (E : formula),
        valid P ->
            forall (S : subst_ind),
                ptree_deg (dub_neg_sub_ptree P E S) = ptree_deg P.
Proof.
intros P E PV.
unfold dub_neg_sub_ptree.
pose (ptree_formula P) as A.
induction P; intros S;
case (subst_ind_fit A S) eqn:FS;
unfold A in FS;
try rewrite FS;
unfold dub_neg_sub_ptree_fit; fold dub_neg_sub_ptree_fit;
unfold ptree_deg in *; fold ptree_deg in *;
try reflexivity.

1 : destruct PV as [[IO PV] NO].

9,10 : destruct PV as [[[PF PV] PD] PO].

1 : unfold ptree_formula in FS; fold ptree_formula in FS.
    pose proof (IHP PV S) as IHPS.
    rewrite FS in IHPS.
    apply IHPS.

all : destruct S; inversion FS as [FS'];
      try reflexivity.

4-6 : case (eq_f f E) eqn:EQ;
      unfold ptree_deg; fold ptree_deg;
      try rewrite PD;
      try reflexivity.

all : destruct S1; inversion FS' as [FS''].

3 : destruct S1_1; inversion FS'' as [FS'''].

all : unfold ptree_deg; fold ptree_deg;
      try reflexivity.

- assert (subst_ind_fit (ptree_formula P) (lor_ind (non_target f) S2) = true) as FSP.
  { rewrite PF.
    unfold subst_ind_fit; fold subst_ind_fit.
    rewrite non_target_fit.
    unfold "&&".
    apply FS''. }
  pose proof (IHP PV (lor_ind (non_target f) S2)) as IHPS.
  rewrite FSP in IHPS.
  apply IHPS.
Qed.

(* Third, we must prove that dub_neg_sub_ptree does not change the ordinal
of an ptree. *)
(* *)
Lemma dub_neg_ptree_ord :
    forall (P : ptree) (E : formula),
        valid P ->
            forall (S : subst_ind),
                (ptree_ord (dub_neg_sub_ptree P E S)) = (ptree_ord P).
Proof.
intros P E PV.
unfold dub_neg_sub_ptree.
pose (ptree_formula P) as A.
induction P; intros S;
case (subst_ind_fit A S) eqn:FS;
unfold A in FS;
try rewrite FS;
unfold dub_neg_sub_ptree_fit; fold dub_neg_sub_ptree_fit;
unfold ptree_ord in *; fold ptree_ord in *;
try reflexivity.

1 : destruct PV as [ID PV].

9,10 : destruct PV as [[[PF PV] PD] PO].

1 : unfold ptree_formula in FS; fold ptree_formula in FS.
    pose proof (IHP PV S) as IHPS.
    rewrite FS in IHPS.
    apply IHPS.

all : destruct S; inversion FS as [FS'];
      try reflexivity.

4-6 : case (eq_f f E) eqn:EQ;
      unfold ptree_deg; fold ptree_deg;
      try rewrite PD;
      try reflexivity.

all : destruct S1; inversion FS' as [FS''].

3 : destruct S1_1; inversion FS'' as [FS'''].

all : unfold ptree_deg; fold ptree_deg;
      try reflexivity.
Qed.

(* Now we prove that if we have a valid ptree, performing our
double negation substitution on it results in a valid ptree *)
(* *)
Lemma dub_neg_valid :
    forall (P : ptree) (E : formula),
        valid P ->
            forall (S : subst_ind),
                subst_ind_fit (ptree_formula P) S = true ->
                    valid (dub_neg_sub_ptree P E S).
Proof.
intros P E PV.
induction P; try intros S FS;
unfold dub_neg_sub_ptree;
rewrite FS;
unfold ptree_formula in *; fold ptree_formula in *;
unfold dub_neg_sub_ptree_fit; fold dub_neg_sub_ptree_fit.

all : try apply PV.

1 : destruct PV as [ID PV].
2 : destruct PV as [[IO PV] NO].
3-8 : destruct PV as [[[PF PV] PD] PO].
9 : destruct PV as [[[[PF FC] PV] PD] PO].
11-13 : destruct PV as [[[PF PV] PD] PO].
10,15,16,17: destruct PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].

3,4,5,6,8,9,10,13,14,15,16,17 : destruct S; inversion FS as [FS'];
                                try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

4,5,6,13 :  destruct S1; inversion FS' as [FS''];
            try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

6 : destruct S1_1; inversion FS'' as [FS'''];
    destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

16 :  { assert (forall t, subst_ind_fit (ptree_formula (p t)) (lor_ind (non_target f) S2) = true) as FSt.
        { intros t.
          destruct (PV t) as [[[PF PVt] PD] PO].
          rewrite PF.
          unfold subst_ind_fit; fold subst_ind_fit.
          rewrite (non_target_term_sub _ n (projT1 t)).
          rewrite non_target_fit.
          unfold "&&".
          apply FS2. }

        repeat split;
        destruct (PV t) as [[[PF PVt] PD] PO];
        rewrite (dub_neg_ptree_formula_true _ _ _ (FSt t)).
        - rewrite (dub_neg_ptree_formula _ _ PVt).
          rewrite PF.
          unfold dub_neg_sub_formula.
          rewrite (non_target_term_sub _ n (projT1 t)).
          rewrite non_target_sub_lor.
          reflexivity.
        - apply (X _ PVt _ (FSt t)).
        - rewrite (dub_neg_ptree_deg _ _ PVt).
          apply PD.
        - rewrite (dub_neg_ptree_ord _ _ PVt).
          apply PO. }

10 :  assert (closed (neg (neg E)) = true -> closed E = true) as CIMP.
10 :  { unfold closed; fold closed;
        intros CE;
        apply CE. }

7,8,13,14 : case (eq_f f E) eqn:EQ.

all : try apply f_eq_decid in EQ;
      try destruct EQ;
      repeat rewrite dub_neg_ptree_formula_true;
      repeat split;
      try apply IHP;
      try apply IHP1;
      try apply IHP2;
      try rewrite dub_neg_ptree_deg;
      try rewrite dub_neg_ptree_ord;
      try rewrite dub_neg_ptree_formula;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold dub_neg_sub_formula, formula_sub_ind;
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
      unfold subst_ind_fit; fold subst_ind_fit;
      try rewrite non_target_fit;
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
      try case (eq_f f (neg E));
      try case (eq_f f0 (neg E));
      try case (eq_f (substitution f n (projT1 c)) (neg E));
      try reflexivity.

1,3 : apply ord_succ_monot.

all : apply ord_succ_nf;
      apply ptree_ord_nf;
      apply PV.
Qed.



(*

(* We finally show that if the formulas ~~A and/or ~~A \/ D are provable,
so are the formulas A and/or A \/ D *)
(* *)
Lemma double_negation_invertible_a :
  forall (A : formula) (d : nat) (alpha : ord),
  provable (neg (neg A)) d alpha -> provable A d alpha.
Proof.
unfold provable. intros A d alpha H. destruct H as [t [[[Ht1 Ht2] Ht3] Ht4]].
exists (dub_neg_sub_ptree t A (1)). unfold P_proves. repeat split.
- rewrite dub_neg_ptree_formula; auto.
  rewrite Ht1. unfold dub_neg_sub_formula. simpl. rewrite eq_f_refl. auto.
- apply dub_neg_valid; auto. rewrite Ht1. auto.
- rewrite dub_neg_ptree_deg; auto.
- rewrite dub_neg_ptree_ord; auto.
Qed.

Lemma double_negation_invertible_ad :
  forall (A D : formula) (d : nat) (alpha : ord),
  provable (lor (neg (neg A)) D) d alpha -> provable (lor A D) d alpha.
Proof.
unfold provable. intros A D d alpha H. destruct H as [t [[[Ht1 Ht2] Ht3] Ht4]].
exists (dub_neg_sub_ptree t A (lor_ind (1) (non_target D))).
unfold P_proves. repeat split.
- rewrite dub_neg_ptree_formula; auto.
  rewrite Ht1. unfold dub_neg_sub_formula. simpl. rewrite eq_f_refl.
  rewrite non_target_fit. rewrite non_target_sub'. auto.
- apply dub_neg_valid; auto. rewrite Ht1. simpl. rewrite non_target_fit. auto.
- rewrite dub_neg_ptree_deg; auto.
- rewrite dub_neg_ptree_ord; auto.
Qed.
*)