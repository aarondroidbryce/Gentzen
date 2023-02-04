
Add LoadPath "theories/Casteran" as Ordering.
Add LoadPath "theories/Maths" as Maths_Facts.
Add LoadPath "theories/Logic" as Systems.

From Maths_Facts Require Import naturals.
From Maths_Facts Require Import ordinals.

From Systems Require Import definitions.
From Systems Require Import fol.
From Systems Require Import proof_trees.
From Systems Require Import substitute.


Definition demorgan2_sub_formula (A E F : formula) (S : subst_ind) : formula :=
    formula_sub_ind A (neg (lor E F)) (neg F) S.
  
Lemma demorgan2_sub_formula_closed :
    forall (A : formula),
        closed A = true ->
            forall (E F : formula) (S : subst_ind),
                closed (demorgan2_sub_formula A E F S) = true.
Proof.
intros A CA E F S.
unfold demorgan2_sub_formula.
apply (formula_sub_ind_closed _ _ _ CA).
unfold closed; fold closed.
apply and_bool_prop.
Qed.
  
Fixpoint demorgan2_sub_ptree_fit
  (P : ptree) (E F : formula) (S : subst_ind) : ptree :=
match P, S with
| deg_up d P', _ => deg_up d (demorgan2_sub_ptree_fit P' E F S)

| ord_up alpha P', _ => ord_up alpha (demorgan2_sub_ptree_fit P' E F S)

| node A, _ => P

| exchange_ab A B d alpha P', lor_ind S_B S_A =>
    exchange_ab
      (demorgan2_sub_formula A E F S_A)
      (demorgan2_sub_formula B E F S_B)
      d alpha
      (demorgan2_sub_ptree_fit P' E F (lor_ind S_A S_B))

| exchange_cab C A B d alpha P', lor_ind (lor_ind S_C S_B) S_A =>
    exchange_cab
      (demorgan2_sub_formula C E F S_C)
      (demorgan2_sub_formula A E F S_A)
      (demorgan2_sub_formula B E F S_B)
      d alpha
      (demorgan2_sub_ptree_fit P' E F (lor_ind (lor_ind S_C S_A) S_B))

| exchange_abd A B D d alpha P', lor_ind (lor_ind S_B S_A) S_D =>
    exchange_abd
      (demorgan2_sub_formula A E F S_A)
      (demorgan2_sub_formula B E F S_B)
      (demorgan2_sub_formula D E F S_D)
      d alpha
      (demorgan2_sub_ptree_fit P' E F (lor_ind (lor_ind S_A S_B) S_D))

| exchange_cabd C A B D d alpha P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D =>
    exchange_cabd
      (demorgan2_sub_formula C E F S_C)
      (demorgan2_sub_formula A E F S_A)
      (demorgan2_sub_formula B E F S_B)
      (demorgan2_sub_formula D E F S_D)
      d alpha
      (demorgan2_sub_ptree_fit P' E F (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D))

| contraction_a A d alpha P', _ =>
    contraction_a
      (demorgan2_sub_formula A E F S)
      d alpha
      (demorgan2_sub_ptree_fit P' E F (lor_ind S S))

| contraction_ad A D d alpha P', lor_ind S_A S_D =>
    contraction_ad
      (demorgan2_sub_formula A E F S_A)
      (demorgan2_sub_formula D E F S_D)
      d alpha
      (demorgan2_sub_ptree_fit P' E F (lor_ind (lor_ind S_A S_A) S_D))

| weakening_ad A D d alpha P', lor_ind S_A S_D =>
    weakening_ad
      (demorgan2_sub_formula A E F S_A)
      (demorgan2_sub_formula D E F S_D)
      d alpha
      (demorgan2_sub_ptree_fit P' E F S_D)

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, _ =>
    (match eq_f A E, eq_f B F, S with
    | true, true, (1) =>
      (match eq_nat d2 (ptree_deg P) with
      | true => ord_up (ptree_ord P) P2
      | false => deg_up (ptree_deg P) (ord_up (ptree_ord P) P2)
      end)
    | _, _, _ => P
    end)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_AB S_D =>
    (match eq_f A E, eq_f B F, S_AB with
    | true, true, (1) =>
      (match eq_nat d2 (ptree_deg P) with
      | true =>
          ord_up
            (ptree_ord P)
            (demorgan2_sub_ptree_fit P2 E F (lor_ind (non_target (neg A)) S_D))
      | false =>
          deg_up
            (ptree_deg P)
              (ord_up
                (ptree_ord P)
                (demorgan2_sub_ptree_fit
                  P2 E F
                  (lor_ind (non_target (neg A)) S_D)))
      end)
    | _, _, _ =>
        demorgan_abd
          A B
          (demorgan2_sub_formula D E F S_D)
          d1 d2 alpha1 alpha2
          (demorgan2_sub_ptree_fit P1 E F (lor_ind (non_target (neg A)) S_D))
          (demorgan2_sub_ptree_fit P2 E F (lor_ind (non_target (neg B)) S_D))
    end)

| negation_a A d alpha P', _ => P

| negation_ad A D d alpha P', lor_ind S_A S_D =>
    negation_ad
      A
      (demorgan2_sub_formula D E F S_D)
      d alpha
      (demorgan2_sub_ptree_fit P' E F (lor_ind (non_target A) S_D))

| quantification_a A n t d alpha P', _ => P

| quantification_ad A D n t d alpha P', lor_ind S_A S_D =>
    quantification_ad
      A
      (demorgan2_sub_formula D E F S_D)
      n t d alpha
      (demorgan2_sub_ptree_fit P' E F (lor_ind (0) S_D))

| w_rule_a A n d alpha g, _ => P

| w_rule_ad A D n d alpha g, lor_ind S_A S_D =>
    w_rule_ad
      A
      (demorgan2_sub_formula D E F S_D)
      n d alpha
      (fun (t : c_term) =>
          demorgan2_sub_ptree_fit (g t) E F (lor_ind (non_target A) S_D))

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ca
      (demorgan2_sub_formula C E F S)
      A d1 d2 alpha1 alpha2
      (demorgan2_sub_ptree_fit P1 E F (lor_ind S (non_target A)))
      P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ad
      A
      (demorgan2_sub_formula D E F S)
      d1 d2 alpha1 alpha2
      P1
      (demorgan2_sub_ptree_fit P2 E F (lor_ind (0) S))

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_D =>
    cut_cad
      (demorgan2_sub_formula C E F S_C)
      A
      (demorgan2_sub_formula D E F S_D)
      d1 d2 alpha1 alpha2
      (demorgan2_sub_ptree_fit P1 E F (lor_ind S_C (non_target A)))
      (demorgan2_sub_ptree_fit P2 E F (lor_ind (0) S_D))

| _, _ => P
end.
  
Definition demorgan2_sub_ptree
  (P : ptree) (E F : formula) (S : subst_ind) : ptree :=
match subst_ind_fit (ptree_formula P) S with
| false => P
| true => demorgan2_sub_ptree_fit P E F S
end.


(* 
Lemma demorgan2_ptree_formula_aux' :
  forall (P : ptree) (E F : formula) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
    demorgan2_sub_ptree P E F S = P.
Proof. intros. unfold demorgan2_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma demorgan2_ptree_formula_aux :
  forall (P : ptree) (E F : formula) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
      ptree_formula (demorgan2_sub_ptree P E F S) =
      demorgan2_sub_formula (ptree_formula P) E F S.
Proof.
intros. rewrite demorgan2_ptree_formula_aux'.
- unfold demorgan2_sub_formula. rewrite sub_fit_false. auto. apply H.
- apply H.
Qed.
*)

Lemma demorgan2_ptree_formula_true :
    forall (P : ptree) (E F : formula) (S : subst_ind),
        subst_ind_fit (ptree_formula P) S = true ->
            demorgan2_sub_ptree_fit P E F S = demorgan2_sub_ptree P E F S.
Proof.
intros P E F S FS.
unfold demorgan2_sub_ptree.
rewrite FS.
reflexivity.
Qed.

Lemma demorgan2_ptree_formula' :
    forall (P : ptree) (E F : formula),
        valid P ->
            forall (S : subst_ind),
                subst_ind_fit (ptree_formula P) S = true ->
                    ptree_formula (demorgan2_sub_ptree P E F S) =
                        demorgan2_sub_formula (ptree_formula P) E F S.
Proof.
intros P E F.
induction P; try intros PV S FS;
unfold demorgan2_sub_ptree;
rewrite FS;
unfold ptree_formula in *; fold ptree_formula in *;
unfold demorgan2_sub_ptree_fit; fold demorgan2_sub_ptree_fit.
  
1 : destruct PV as [ID PV].
2 : destruct PV as [[IO PV] NO].
13-14 : destruct PV as [[[PF PV] PD] PO].

1-2 : rewrite (demorgan2_ptree_formula_true _ _ _ _ FS);
      unfold ptree_formula; fold ptree_formula;
      apply (IHP PV _ FS).

1 : { inversion PV as [PX].
      unfold demorgan2_sub_ptree, demorgan2_sub_formula, formula_sub_ind.
      rewrite FS.
      unfold ptree_formula; fold ptree_formula.
      destruct (axiom_atomic _ PX) as [[a fa] | [a fa]];
      rewrite fa;
      unfold formula_sub_ind_fit; fold formula_sub_ind_fit;
      unfold eq_f;
      reflexivity. }

5 : reflexivity.

9,11,13,15,16 : unfold ptree_formula, demorgan2_sub_formula, formula_sub_ind, formula_sub_ind_fit, eq_f;
                destruct S;
                try reflexivity.

all : destruct S; inversion FS as [FS'];
      try reflexivity.

1,5,6,13 :  apply and_bool_prop in FS';
            destruct FS' as [FS1 FS2];
            unfold ptree_formula, demorgan2_sub_formula, formula_sub_ind, formula_sub_ind_fit;
            fold formula_sub_ind_fit;
            rewrite FS,FS1,FS2;
            reflexivity.

4-6 : case (eq_f f E) eqn:EQ1;
      case (eq_f f0 F) eqn:EQ2;
      unfold ptree_formula, demorgan2_sub_formula, formula_sub_ind, subst_ind_fit, formula_sub_ind_fit, eq_f;
      fold ptree_formula eq_f formula_sub_ind_fit subst_ind_fit;
      try rewrite EQ1;
      try rewrite EQ2;
      try reflexivity.

all : unfold "&&".

4 : { destruct PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].
      apply f_eq_decid in EQ1,EQ2.
      destruct EQ1,EQ2.
      case (eq_nat n0 (ptree_deg (demorgan_ab f f0 n n0 o o0 P1 P2))) eqn:EQ;
      unfold ptree_formula; fold ptree_formula;
      apply P2F. }

all : destruct S1; inversion FS' as [FS''].

5 : { destruct PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].
      apply f_eq_decid in EQ1,EQ2.
      destruct EQ1,EQ2.
      assert (subst_ind_fit (ptree_formula P2) (lor_ind (non_target (neg f0)) S2) = true) as FS2.
      { rewrite P2F.
        unfold subst_ind_fit, non_target; fold subst_ind_fit.
        apply FS'. }
      case (eq_nat n0 (ptree_deg (demorgan_abd f f0 f1 n n0 o o0 P1 P2))) eqn:EQ;
      unfold ptree_formula; fold ptree_formula;
      rewrite (demorgan2_ptree_formula_true _ _ _ _ FS2);
      rewrite (IHP2 P2V _ FS2);
      unfold demorgan2_sub_formula;
      rewrite P2F;
      rewrite non_target_sub_lor;
      unfold formula_sub_ind;
      rewrite FS'';
      reflexivity. }

1-3 : apply and_bool_prop in FS';
      destruct FS' as [FS1 FS2];
      apply and_bool_prop in FS1;
      destruct FS1 as [FS1_1 FS1_2].

3 : destruct S1_1; inversion FS'' as [FS'''];
    apply and_bool_prop in FS1_1;
    destruct FS1_1 as [FS1_1_1 FS1_1_2].

all : unfold ptree_formula, demorgan2_sub_formula, formula_sub_ind, formula_sub_ind_fit, eq_f;
      fold ptree_formula eq_f formula_sub_ind_fit;
      try rewrite FS;
      try rewrite FS'';
      try rewrite EQ;
      try rewrite FS1_1,FS1_2,FS2;
      try rewrite FS1_1_1,FS1_1_2,FS1_2,FS2;      
      unfold "&&";
      try reflexivity.
Qed.


Lemma demorgan2_ptree_formula :
    forall (P : ptree) (E F : formula),
        valid P ->
            forall (S : subst_ind),
                ptree_formula (demorgan2_sub_ptree P E F S) =
                    demorgan2_sub_formula (ptree_formula P) E F S.
Proof.
intros P E F PV S.
destruct (subst_ind_fit (ptree_formula P) S) eqn:FS.
- apply (demorgan2_ptree_formula' _ _ _ PV _ FS).
- unfold demorgan2_sub_ptree, demorgan2_sub_formula, formula_sub_ind.
  rewrite FS.
  reflexivity.
Qed.


Lemma demorgan2_ptree_deg :
    forall (P : ptree) (E F : formula),
        valid P ->
            forall (S : subst_ind),
                ptree_deg (demorgan2_sub_ptree P E F S) = ptree_deg P.
Proof.
intros P E F PV.
unfold demorgan2_sub_ptree.
pose (ptree_formula P) as A.
induction P; intros S;
case (subst_ind_fit A S) eqn:FS;
unfold A in FS;
try rewrite FS;
unfold demorgan2_sub_ptree_fit; fold demorgan2_sub_ptree_fit;
unfold ptree_deg in *; fold ptree_deg in *;
try reflexivity.

1 : destruct PV as [[IO PV] NO].

8,9 : destruct PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].

1 : unfold ptree_formula in FS; fold ptree_formula in FS.
    pose proof (IHP PV S) as IHPS.
    rewrite FS in IHPS.
    apply IHPS.

all : destruct S; inversion FS as [FS'];
      try reflexivity.

4-6 : case (eq_f f E) eqn:EQ1;
      case (eq_f f0 F) eqn:EQ2;
      unfold ptree_deg; fold ptree_deg;
      try rewrite P1D;
      try rewrite P2D;
      case (eq_nat (ptree_deg P2) (Nat.max (ptree_deg P1) (ptree_deg P2))) eqn:EQ;
      unfold ptree_deg; fold ptree_deg;
      try reflexivity.

4 : apply nat_eq_decid in EQ;
    destruct EQ;
    reflexivity.

all : destruct S1; inversion FS' as [FS''].

3 : destruct S1_1; inversion FS'' as [FS'''].

all : unfold ptree_deg; fold ptree_deg;
      try reflexivity.

- apply nat_eq_decid in EQ;
  destruct EQ.
  rewrite <- (IHP2 P2V (lor_ind (non_target (neg f0)) S2)).
  rewrite P2F.
  unfold subst_ind_fit, non_target; fold subst_ind_fit.
  rewrite FS'.
  reflexivity.
Qed.



Lemma demorgan2_ptree_ord :
    forall (P : ptree) (E F : formula),
        valid P ->
            forall (S : subst_ind),
                ptree_ord (demorgan2_sub_ptree P E F S) = ptree_ord P.
Proof.
intros P E F PV.
unfold demorgan2_sub_ptree.
pose (ptree_formula P) as A.
induction P; intros S;
case (subst_ind_fit A S) eqn:FS;
unfold A in FS;
try rewrite FS;
unfold demorgan2_sub_ptree_fit; fold demorgan2_sub_ptree_fit;
unfold ptree_ord in *; fold ptree_ord in *;
try reflexivity.

1 : destruct PV as [ID PV].

8,9 : destruct PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].

1 : unfold ptree_formula in FS; fold ptree_formula in FS.
    pose proof (IHP PV S) as IHPS.
    rewrite FS in IHPS.
    apply IHPS.

all : destruct S; inversion FS as [FS'];
      try reflexivity.

4-6 : case (eq_f f E) eqn:EQ1;
      case (eq_f f0 F) eqn:EQ2;
      unfold ptree_deg; fold ptree_deg;
      case (eq_nat n0 (Nat.max n n0)) eqn:EQ;
      try reflexivity.

all : destruct S1; inversion FS' as [FS''].

3 : destruct S1_1; inversion FS'' as [FS'''].

all : unfold ptree_ord; fold ptree_ord;
      try reflexivity.
Qed.

(* *)
Lemma demorgan2_valid :
    forall (P : ptree) (E F : formula),
        valid P ->
            forall (S : subst_ind),
                subst_ind_fit (ptree_formula P) S = true ->
                    valid (demorgan2_sub_ptree P E F S).
Proof.
intros P E F PV.
induction P; try intros S FS;
unfold demorgan2_sub_ptree;
rewrite FS;
unfold ptree_formula in *; fold ptree_formula in *;
unfold demorgan2_sub_ptree_fit; fold demorgan2_sub_ptree_fit.

all : try apply PV.

1 : destruct PV as [ID PV].
2 : destruct PV as [[IO PV] NO].
3-8 : destruct PV as [[[PF PV] PD] PO].
9 : destruct PV as [[[[PF FC] PV] PD] PO].
12-13 : destruct PV as [[[PF PV] PD] PO].
10,11,15,16,17: inversion PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].

3,4,5,6,8,9,10,11,14,15,16,17 : destruct S; inversion FS as [FS'];
                                try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

4,5,6,11 :  destruct S1; inversion FS' as [FS''];
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
        rewrite (demorgan2_ptree_formula_true _ _ _ _ (FSt t)).
        - rewrite (demorgan2_ptree_formula _ _ _ PVt).
          rewrite PF.
          unfold demorgan2_sub_formula.
          rewrite (non_target_term_sub _ n (projT1 t)).
          rewrite non_target_sub_lor.
          reflexivity.
        - apply (X _ PVt _ (FSt t)).
        - rewrite (demorgan2_ptree_deg _ _ _ PVt).
          apply PD.
        - rewrite (demorgan2_ptree_ord _ _ _ PVt).
          apply PO. }

10 :  assert (closed (neg (lor E F)) = true -> closed (neg F) = true) as CIMP.
10 :  { unfold closed; fold closed;
        apply and_bool_prop. }

7,8,11,12 : case (eq_f f E) eqn:EQ1;
            case (eq_f f0 F) eqn:EQ2;
            unfold ptree_deg; fold ptree_deg;
            try apply PV.

11,15 : case (eq_nat n0 (Nat.max n n0)) eqn:EQ.
            
all : try apply f_eq_decid in EQ1;
      try destruct EQ1;
      try apply f_eq_decid in EQ2;
      try destruct EQ2;
      repeat rewrite demorgan2_ptree_formula_true;
      repeat split;
      try apply IHP;
      try apply IHP1;
      try apply IHP2;
      unfold ptree_deg; fold ptree_deg;
      try rewrite demorgan2_ptree_deg;
      try rewrite demorgan2_ptree_ord;
      try apply ptree_ord_nf;
      unfold ptree_ord; fold ptree_ord;
      try rewrite demorgan2_ptree_formula;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold demorgan2_sub_formula, formula_sub_ind;
      try apply PV;
      try apply PD;
      try rewrite PO;
      try apply P1V;
      try rewrite P1D in *;
      try rewrite P1O;
      try apply P2V;
      try rewrite P2D in *;
      try rewrite P2O;
      try apply FS;
      try apply ID;
      try apply IO;
      try apply NO;
      unfold subst_ind_fit, non_target; fold subst_ind_fit;
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
      try reflexivity;
      unfold formula_sub_ind_fit; fold formula_sub_ind_fit;
      unfold eq_f; fold eq_f;
      try rewrite non_target_sub';
      try reflexivity;
      try rewrite <- (sub_fit_true _ _ _ _ FS1);
      try apply (formula_sub_ind_closed _ _ _ FC CIMP);
      try apply max_lem2;
      try apply EQ;
      try apply ord_max_succ_r;
      try case (eq_f f (lor E F));
      try case (eq_f f0 (lor E F));
      try case (eq_f (substitution f n (projT1 c)) (lor E F));
      try case (eq_f f (lor f f0));
      try case (eq_f f0 (lor f f0));
      try case (eq_f f (lor f F));
      try case (eq_f f0 (lor f F));
      try case (eq_f f (lor E f0));
      try case (eq_f f0 (lor E f0));
      try reflexivity.
Qed.



(* 
Lemma demorgan2_invertible_a :
  forall (A B : formula) (d : nat) (alpha : ord),
  provable (neg (lor A B)) d alpha -> provable (neg A) d alpha.
Proof.
unfold provable. intros A B d alpha H. destruct H as [t [[[Ht1 Ht2] Ht3] Ht4]].
exists (demorgan2_sub_ptree t A B (1)). unfold P_proves. repeat split.
- rewrite demorgan2_ptree_formula; auto. rewrite Ht1.
  unfold demorgan2_sub_formula. simpl. repeat rewrite eq_f_refl. auto.
- apply demorgan2_valid; auto. rewrite Ht1. auto.
- rewrite demorgan2_ptree_deg; auto.
- rewrite demorgan2_ptree_ord; auto.
Qed.

Lemma demorgan2_invertible_ad :
  forall (A B D : formula) (d : nat) (alpha : ord),
  provable (lor (neg (lor A B)) D) d alpha -> provable (lor (neg A) D) d alpha.
Proof.
unfold provable. intros A B D d alpha H. destruct H as [t [[[Ht1 Ht2] Ht3] Ht4]].
exists (demorgan2_sub_ptree t A B (lor_ind (1) (non_target D))).
unfold P_proves. repeat split.
- rewrite demorgan2_ptree_formula; auto. rewrite Ht1.
  unfold demorgan2_sub_formula. simpl. rewrite non_target_fit.
  repeat rewrite eq_f_refl. simpl. rewrite <- sub_fit_true.
  + rewrite non_target_sub. auto.
  + apply non_target_fit.
- apply demorgan2_valid; auto. rewrite Ht1. simpl. apply non_target_fit.
- rewrite demorgan2_ptree_deg; auto.
- rewrite demorgan2_ptree_ord; auto.
Qed.


  (* First, we must prove that demorgan2_sub_ptree simply changes the base formula
  of an ptree the way we expect with demorgan2_sub_formula *)
  (* *)
  Lemma demorgan2_ptree_formula_aux' :
    forall (P : ptree) (E F : formula) (S : subst_ind),
      subst_ind_fit (ptree_formula P) S = false ->
      demorgan2_sub_ptree P E F S = P.
  Proof. intros. unfold demorgan2_sub_ptree. destruct P; rewrite H; auto. Qed.
  
  Lemma demorgan2_ptree_formula_aux :
    forall (P : ptree) (E F : formula) (S : subst_ind),
      subst_ind_fit (ptree_formula P) S = false ->
        ptree_formula (demorgan2_sub_ptree P E F S) =
        demorgan2_sub_formula (ptree_formula P) E F S.
  Proof.
  intros. rewrite demorgan2_ptree_formula_aux'.
  - unfold demorgan2_sub_formula. rewrite sub_fit_false. auto. apply H.
  - apply H.
  Qed.
  
  Lemma demorgan2_ptree_formula_true :
    forall (P : ptree) (E F : formula) (S : subst_ind),
      subst_ind_fit (ptree_formula P) S = true ->
      demorgan2_sub_ptree_fit P E F S = demorgan2_sub_ptree P E F S.
  Proof. intros. unfold demorgan2_sub_ptree. destruct P; rewrite H; auto. Qed.
  
  Lemma demorgan2_ptree_formula' : forall (P : ptree) (E F : formula),
    valid P ->
    forall (S : subst_ind),
      subst_ind_fit (ptree_formula P) S = true ->
      ptree_formula (demorgan2_sub_ptree P E F S) =
      demorgan2_sub_formula (ptree_formula P) E F S.
  Proof.
  intros P E F.
  induction P; try intros H S Hs.
  
  - simpl in Hs. simpl. rewrite Hs. simpl.
    rewrite (demorgan2_ptree_formula_true _ _ _ _ Hs).
    destruct H as [H1 H2]. apply (IHP H2). auto.
  
  - simpl in Hs. simpl. rewrite Hs. simpl.
    rewrite (demorgan2_ptree_formula_true _ _ _ _ Hs).
    destruct H as [[H1 H2] H3]. apply (IHP H2). auto.
  
  - simpl. inversion H.
    destruct (axiom_atomic _ H1); destruct H0; rewrite H0;
    unfold demorgan2_sub_formula; simpl; destruct S; auto.
  
  - simpl.
    destruct S; inversion Hs; rewrite H1; simpl; unfold demorgan2_sub_formula.
    rewrite formula_sub_ind_lor; auto.
  
  - simpl.
    destruct S; try destruct S1; inversion Hs; rewrite H1;
    simpl; unfold demorgan2_sub_formula.
    rewrite formula_sub_ind_lor, formula_sub_ind_lor; auto.
    apply (and_bool_prop _ _ H1).
  
  - simpl.
    destruct S; try destruct S1; inversion Hs; rewrite H1;
    simpl; unfold demorgan2_sub_formula.
    rewrite formula_sub_ind_lor, formula_sub_ind_lor; auto.
    apply (and_bool_prop _ _ H1).
  
  - simpl. destruct S; simpl.
    + unfold demorgan2_sub_formula. auto.
    + unfold demorgan2_sub_formula. auto.
    + destruct S1; try destruct S1_1; inversion Hs.
      rewrite H1. simpl. unfold demorgan2_sub_formula.
      destruct (and_bool_prop _ _ H1). destruct (and_bool_prop _ _ H0).
      repeat rewrite formula_sub_ind_lor; auto.
  
  - simpl. inversion Hs. rewrite H1. auto.
  
  - simpl. destruct S; inversion Hs.
    rewrite H1. simpl. unfold demorgan2_sub_formula.
    rewrite formula_sub_ind_lor. auto. apply H1.
  
  - simpl. destruct S; auto. inversion Hs. rewrite H1. simpl.
    unfold demorgan2_sub_formula. rewrite formula_sub_ind_lor. auto. apply H1.
  
  - simpl. destruct S; auto; destruct (eq_f f E) eqn:HE.
    + destruct (eq_f f0 F) eqn:HF; simpl;
      unfold demorgan2_sub_formula; rewrite formula_sub_ind_0; auto.
    + simpl. unfold demorgan2_sub_formula. rewrite formula_sub_ind_0. auto.
    + destruct (eq_f f0 F) eqn:HF.
      * inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
        clear IHP1. clear IHP2.
        case (eq_nat n0 (Init.Nat.max n n0)) eqn:Hn;
        simpl; rewrite H3; unfold demorgan2_sub_formula; simpl; rewrite HE,HF;
        simpl; rewrite (f_eq_decid _ _ HF); auto.
      * simpl. unfold demorgan2_sub_formula. simpl. rewrite HE,HF. auto.
    + simpl. unfold demorgan2_sub_formula. simpl. rewrite HE. auto.
  
  - simpl. destruct S; auto.
    destruct S1; auto.
    + destruct (eq_f f E) eqn:HE; destruct (eq_f f0 F) eqn:HF;
      destruct (subst_ind_fit f1 S2) eqn:HS2; simpl; unfold demorgan2_sub_formula;
      simpl; rewrite HE,HF,HS2; auto; rewrite sub_fit_true; auto.
    + destruct (eq_f f E) eqn:HE.
      * destruct (eq_f f0 F) eqn:HF.
        { destruct (subst_ind_fit f1 S2) eqn:HS2.
          { clear IHP1. simpl.
            inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
            rewrite demorgan2_ptree_formula_true; auto.
            { case (eq_nat n0 (Init.Nat.max n n0)) eqn:Hn0;
              simpl; rewrite IHP2; auto; rewrite H3; auto;
              unfold demorgan2_sub_formula; simpl; rewrite HE,HF,HS2;
              destruct (eq_f f0 (lor E F)); rewrite (f_eq_decid _ _ HF); auto. }
            { rewrite H3. auto. } }
          { simpl. unfold demorgan2_sub_formula. simpl. rewrite HE,HF,HS2. auto. } }
        { destruct (subst_ind_fit f1 S2) eqn:HS2; simpl;
          unfold demorgan2_sub_formula; simpl; rewrite HE,HF,HS2; auto;
          rewrite sub_fit_true; auto. }
      * destruct (eq_f f0 F) eqn:HF; destruct (subst_ind_fit f1 S2) eqn:HS2; simpl;
          unfold demorgan2_sub_formula; simpl; rewrite HE,HF,HS2; auto;
          rewrite sub_fit_true; auto.
  
  - simpl. destruct S; auto.
  
  - simpl. destruct S; auto. destruct S1; auto;
    destruct (subst_ind_fit f0 S2) eqn:HS2; simpl; unfold demorgan2_sub_formula;
    simpl; rewrite HS2; auto; rewrite sub_fit_true; auto.
  
  - simpl. destruct S; simpl; unfold demorgan2_sub_formula; auto.
  
  - simpl. destruct S.
    + simpl. unfold demorgan2_sub_formula. simpl. auto.
    + simpl. unfold demorgan2_sub_formula. simpl. auto.
    + destruct S1; inversion Hs; rewrite H1; simpl; unfold demorgan2_sub_formula.
      * rewrite formula_sub_ind_lor; auto.
      * simpl. rewrite H1. rewrite sub_fit_true; auto.
  
  - intros. simpl. destruct S; simpl; unfold demorgan2_sub_formula; auto.
  
  - intros. simpl. destruct S; try destruct S1; inversion H0;
    rewrite H2; unfold demorgan2_sub_formula; rewrite formula_sub_ind_lor; auto.
  
  - simpl. inversion Hs. rewrite H1. auto.
  
  - simpl. inversion Hs. rewrite H1. auto.
  
  - simpl. destruct S; inversion Hs.
    rewrite H1. simpl. unfold demorgan2_sub_formula.
    rewrite formula_sub_ind_lor; auto.
  Qed.
  
  
  Lemma demorgan2_ptree_formula : forall (P : ptree) (E F : formula),
    valid P ->
    forall (S : subst_ind),
      ptree_formula (demorgan2_sub_ptree P E F S) =
      demorgan2_sub_formula (ptree_formula P) E F S.
  Proof.
  intros. destruct (subst_ind_fit (ptree_formula P) S) eqn:Hs.
  - apply demorgan2_ptree_formula'. apply X. apply Hs.
  - apply demorgan2_ptree_formula_aux. apply Hs.
  Qed.
  
  
  
  
  
  (* Second, we must prove that demorgan2_sub_ptree does not change the degree
  of an ptree. *)
  (* *)
  Lemma demorgan2_ptree_deg : forall (P : ptree) (E F : formula),
    valid P ->
    forall (S : subst_ind), ptree_deg (demorgan2_sub_ptree P E F S) = ptree_deg P.
  Proof.
  intros P E F H. induction P; intros S.
  - simpl. case (subst_ind_fit (ptree_formula P) S); auto.
  - simpl. case (subst_ind_fit (ptree_formula P) S) eqn:Hfit; auto. simpl.
    rewrite (demorgan2_ptree_formula_true _ _ _ _ Hfit).
    apply IHP. inversion H. destruct X. auto.
  - simpl. case (subst_ind_fit f S); auto.
  - simpl.
    destruct S; auto. case (subst_ind_fit f0 S1 && subst_ind_fit f S2); auto.
  - simpl. destruct S; auto. destruct S1; auto.
    case (subst_ind_fit f S1_1 && subst_ind_fit f1 S1_2 && subst_ind_fit f0 S2);
    auto.
  - simpl. destruct S; auto. destruct S1; auto.
    case (subst_ind_fit f0 S1_1 && subst_ind_fit f S1_2 && subst_ind_fit f1 S2);
    auto.
  - simpl. destruct S; auto. destruct S1; auto. destruct S1_1; auto.
    case (subst_ind_fit f S1_1_1 && subst_ind_fit f1 S1_1_2 &&
          subst_ind_fit f0 S1_2 && subst_ind_fit f2 S2); auto.
  - simpl. destruct (subst_ind_fit f S); auto.
  - simpl.
    destruct S; auto. destruct (subst_ind_fit f S1 && subst_ind_fit f0 S2); auto.
  - simpl.
    destruct S; auto. destruct (subst_ind_fit f S1 && subst_ind_fit f0 S2); auto.
  - simpl. destruct S; auto.
    + case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
    + inversion H as [[[[[H1 H2] H3] H4] H5] H6].
      case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
      case (eq_nat n0 (Init.Nat.max n n0)) eqn:Hn0;
      simpl; auto; rewrite <- (nat_eq_decid _ _ Hn0); auto.
  - simpl. destruct S; auto.
    destruct S1; auto; destruct (subst_ind_fit f1 S2) eqn:HS2; auto; simpl.
    + case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
    + inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
      case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
      case (eq_nat n0 (Init.Nat.max n n0)) eqn:Hn0;
      simpl; auto; rewrite <- (nat_eq_decid _ _ Hn0); auto;
      rewrite demorgan2_ptree_formula_true;
      try rewrite IHP2; auto; rewrite H3; simpl; auto.
  - simpl. destruct S; auto.
  - simpl. destruct S; auto.
    destruct S1; auto; destruct (subst_ind_fit f0 S2); auto.
  - simpl. destruct S; auto.
  - simpl.
    destruct S; auto; destruct S1; auto; destruct (subst_ind_fit f0 S2); auto.
  - simpl. destruct S; auto.
  - simpl.
    destruct S; auto; destruct S1; auto; destruct (subst_ind_fit f0 S2); auto.
  - simpl. destruct (subst_ind_fit f S); auto.
  - simpl. destruct (subst_ind_fit f0 S); auto.
  - simpl.
    destruct S; auto. destruct (subst_ind_fit f S1 && subst_ind_fit f1 S2); auto.
  Qed.
  
  
  
  Lemma demorgan2_ptree_ord : forall (P : ptree) (E F : formula),
    valid P ->
    forall (S : subst_ind), ptree_ord (demorgan2_sub_ptree P E F S) = ptree_ord P.
  Proof.
  intros P E F H. induction P; intros S.
  - simpl. case (subst_ind_fit (ptree_formula P) S) eqn:Hfit; auto. simpl.
    rewrite (demorgan2_ptree_formula_true _ _ _ _ Hfit).
    apply IHP. inversion H. auto.
  - simpl. case (subst_ind_fit (ptree_formula P) S); auto.
  - simpl. case (subst_ind_fit f S); auto.
  - simpl.
    destruct S; auto. case (subst_ind_fit f0 S1 && subst_ind_fit f S2); auto.
  - simpl. destruct S; auto. destruct S1; auto.
    case (subst_ind_fit f S1_1 && subst_ind_fit f1 S1_2 && subst_ind_fit f0 S2);
    auto.
  - simpl. destruct S; auto. destruct S1; auto.
    case (subst_ind_fit f0 S1_1 && subst_ind_fit f S1_2 && subst_ind_fit f1 S2);
    auto.
  - simpl. destruct S; auto. destruct S1; auto. destruct S1_1; auto.
    case (subst_ind_fit f S1_1_1 && subst_ind_fit f1 S1_1_2 &&
          subst_ind_fit f0 S1_2 && subst_ind_fit f2 S2); auto.
  - simpl. destruct (subst_ind_fit f S); auto.
  - simpl.
    destruct S; auto. destruct (subst_ind_fit f S1 && subst_ind_fit f0 S2); auto.
  - simpl.
    destruct S; auto. destruct (subst_ind_fit f S1 && subst_ind_fit f0 S2); auto.
  - simpl. destruct S; auto.
    + case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
    + inversion H as [[[[[H1 H2] H3] H4] H5] H6].
      case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
      case (eq_nat n0 (Init.Nat.max n n0)) eqn:Hn0;
      simpl; auto; rewrite <- (ord_eqb_eq _ _ Ho0); auto.
  - simpl. destruct S; auto.
    destruct S1; auto; destruct (subst_ind_fit f1 S2) eqn:HS2; auto; simpl.
    + case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
    + inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
      case (eq_f f E) eqn:HE; case (eq_f f0 F) eqn:HF; auto.
      case (eq_nat n0 (Init.Nat.max n n0)) eqn:Hn0;
      simpl; auto; rewrite <- (ord_eqb_eq _ _ Ho0); auto;
      rewrite demorgan2_ptree_formula_true;
      try rewrite IHP2; auto; rewrite H3; simpl; auto.
  - simpl. destruct S; auto.
  - simpl. destruct S; auto.
    destruct S1; auto; destruct (subst_ind_fit f0 S2); auto.
  - simpl. destruct S; auto.
  - simpl.
    destruct S; auto; destruct S1; auto; destruct (subst_ind_fit f0 S2); auto.
  - simpl. destruct S; auto.
  - simpl.
    destruct S; auto; destruct S1; auto; destruct (subst_ind_fit f0 S2); auto.
  - simpl. destruct (subst_ind_fit f S); auto.
  - simpl. destruct (subst_ind_fit f0 S); auto.
  - simpl.
    destruct S; auto. destruct (subst_ind_fit f S1 && subst_ind_fit f1 S2); auto.
  Qed.
  
  
  
  (* Now we prove that if we have a valid ptree, performing our
  double negation substitution on it results in a valid ptree *)
  (* *)
  Lemma demorgan2_valid : forall (P : ptree) (E F : formula),
    valid P ->
    forall (S : subst_ind),
      subst_ind_fit (ptree_formula P) S = true ->
      valid (demorgan2_sub_ptree P E F S).
  Proof.
  intros P E F. induction P; try intros H S Hs.
  
  - simpl. inversion H as [H1 H2]. inversion Hs. rewrite H3.
    rewrite demorgan2_ptree_formula_true; auto. split.
    + rewrite demorgan2_ptree_deg; auto.
    + apply (IHP H2 S H3).
  
  - simpl. inversion H as [[H1 H2] H3]. inversion Hs. rewrite H4.
    rewrite demorgan2_ptree_formula_true; auto. split.
    + rewrite demorgan2_ptree_ord; auto.
    + auto.
  
  - simpl. destruct (subst_ind_fit f S); apply H.
  
  - simpl. destruct S; inversion Hs. rewrite H1. simpl.
    inversion H as [[[H2 H3] H4] H5].
    repeat split; rewrite demorgan2_ptree_formula_true.
    + rewrite demorgan2_ptree_formula; auto.
      rewrite H2. unfold demorgan2_sub_formula.
      rewrite formula_sub_ind_lor; auto. apply (and_bool_symm _ _ H1).
    + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
    + apply IHP. apply H. rewrite H2. simpl. apply (and_bool_symm _ _ H1).
    + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
    + rewrite demorgan2_ptree_deg; auto.
    + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
    + rewrite demorgan2_ptree_ord; auto.
    + rewrite H2. simpl. apply (and_bool_symm _ _ H1).
  
  - simpl. destruct S; try destruct S1; inversion Hs.
    rewrite H1. simpl. inversion H as [[[H4 H5] H6] H7].
    destruct (and_bool_prop _ _ H1). clear H1.
    destruct (and_bool_prop _ _ H0). clear H0.
    repeat split; rewrite demorgan2_ptree_formula_true.
    + rewrite demorgan2_ptree_formula; auto.
      rewrite H4. unfold demorgan2_sub_formula.
      repeat rewrite formula_sub_ind_lor; auto.
      * rewrite H1, H2. auto.
      * simpl. rewrite H1, H2, H3. auto.
    + rewrite H4. simpl. rewrite H1, H2, H3. auto.
    + apply IHP; auto. rewrite H4. simpl. rewrite H1, H2, H3. auto.
    + rewrite H4. simpl. rewrite H1, H2, H3. auto.
    + rewrite demorgan2_ptree_deg; auto.
    + rewrite H4. simpl. rewrite H1, H2, H3. auto.
    + rewrite demorgan2_ptree_ord; auto.
    + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  
  - simpl. destruct S; try destruct S1; inversion Hs.
    rewrite H1. simpl. inversion H as [[[H4 H5] H6] H7].
    destruct (and_bool_prop _ _ H1). clear H1.
    destruct (and_bool_prop _ _ H0). clear H0.
    repeat split; rewrite demorgan2_ptree_formula_true.
    + rewrite demorgan2_ptree_formula; auto.
      rewrite H4. unfold demorgan2_sub_formula.
      repeat rewrite formula_sub_ind_lor; auto.
      * rewrite H1, H3. auto.
      * simpl. rewrite H1, H2, H3. auto.
    + rewrite H4. simpl. rewrite H1, H2, H3. auto.
    + apply IHP; auto. rewrite H4. simpl. rewrite H1, H2, H3. auto.
    + rewrite H4. simpl. rewrite H1, H2, H3. auto.
    + rewrite demorgan2_ptree_deg; auto.
    + rewrite H4. simpl. rewrite H1, H2, H3. auto.
    + rewrite demorgan2_ptree_ord; auto.
    + rewrite H4. simpl. rewrite H1, H2, H3. auto.
  
  - simpl. destruct S; try destruct S1; try destruct S1_1; inversion Hs.
    rewrite H1. simpl. inversion H as [[[H5 H6] H7] H8].
    destruct (and_bool_prop _ _ H1). clear H1.
    destruct (and_bool_prop _ _ H0). clear H0.
    destruct (and_bool_prop _ _ H1). clear H1.
    repeat split; rewrite demorgan2_ptree_formula_true.
    + rewrite demorgan2_ptree_formula; auto.
      rewrite H5. unfold demorgan2_sub_formula.
      repeat rewrite formula_sub_ind_lor; auto.
      * rewrite H0,H3. auto.
      * simpl. rewrite H0, H3, H4. auto.
      * simpl. rewrite H0, H2, H3, H4. auto.
    + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
    + apply IHP; auto. rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
    + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
    + rewrite demorgan2_ptree_deg; auto.
    + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
    + rewrite demorgan2_ptree_ord; auto.
    + rewrite H5. simpl. rewrite H0, H2, H3, H4. auto.
  
  - simpl. inversion Hs. rewrite H1. inversion H as [[[H2 H3] H4] H5].
    repeat split; rewrite demorgan2_ptree_formula_true.
    + rewrite demorgan2_ptree_formula; auto.
      unfold demorgan2_sub_formula. rewrite H2.
      rewrite formula_sub_ind_lor; auto. rewrite H1. auto.
    + rewrite H2. simpl. rewrite H1. auto.
    + apply IHP. apply H. rewrite H2. simpl. rewrite H1. auto.
    + rewrite H2. simpl. rewrite H1. auto.
    + rewrite demorgan2_ptree_deg; auto.
    + rewrite H2. simpl. rewrite H1. auto.
    + rewrite demorgan2_ptree_ord; auto.
    + rewrite H2. simpl. rewrite H1. auto.
  
  - simpl. destruct S; inversion Hs. rewrite H1.
    inversion H as [[[H2 H3] H4] H5]. destruct (and_bool_prop _ _ H1).
    repeat split; rewrite demorgan2_ptree_formula_true.
    + rewrite demorgan2_ptree_formula; auto.
      unfold demorgan2_sub_formula. rewrite H2.
      repeat rewrite formula_sub_ind_lor; auto.
      * rewrite H0. auto.
      * simpl. rewrite H0, H6. auto.
    + rewrite H2. simpl. rewrite H0, H6. auto.
    + apply IHP. apply H. rewrite H2. simpl. rewrite H0, H6. auto.
    + rewrite H2. simpl. rewrite H0, H6. auto.
    + rewrite demorgan2_ptree_deg; auto.
    + rewrite H2. simpl. rewrite H0, H6. auto.
    + rewrite demorgan2_ptree_ord; auto.
    + rewrite H2. simpl. rewrite H0, H6. auto.
  
  - simpl. destruct S; inversion Hs. rewrite H1. simpl.
    inversion H as [[[[H2 H3] H4] H5] H6]. destruct (and_bool_prop _ _ H1).
    repeat split.
    + rewrite demorgan2_ptree_formula_true.
      * rewrite demorgan2_ptree_formula; auto. rewrite H2. auto.
      * rewrite H2. auto.
    + apply demorgan2_sub_formula_closed. auto.
    + rewrite demorgan2_ptree_formula_true.
      * apply IHP; auto. rewrite H2. auto.
      * rewrite H2. auto.
    + rewrite demorgan2_ptree_formula_true.
      * rewrite demorgan2_ptree_deg; auto.
      * rewrite H2. auto.
    + rewrite demorgan2_ptree_formula_true.
      * rewrite demorgan2_ptree_ord; auto.
      * rewrite H2. auto.
  
  - simpl. inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
    destruct S; auto; destruct (eq_f f E); destruct (eq_f f0 F);
    simpl; repeat split; auto.
    case (eq_nat n0 (Init.Nat.max n n0)) eqn:Hn0;
    simpl; repeat split; auto.
    + rewrite <- H8. apply ord_max_succ_r.
    + apply ord_succ_nf. apply ord_max_nf.
      * rewrite H7. apply ptree_ord_nf. auto.
      * rewrite H8. apply ptree_ord_nf. auto.
    + rewrite <- H6. apply max_lem2. auto.
    + rewrite <- H8. apply ord_max_succ_r.
    + apply ord_succ_nf. apply ord_max_nf.
      * rewrite H7. apply ptree_ord_nf. auto.
      * rewrite H8. apply ptree_ord_nf. auto.
  - simpl. inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
    destruct S; auto.
    destruct S1; auto; destruct (subst_ind_fit f1 S2) eqn:HS2;
    destruct (eq_f f E) eqn:HE; destruct (eq_f f0 F) eqn:HF;
    simpl; repeat split; auto; rewrite demorgan2_ptree_formula_true;
    try rewrite demorgan2_ptree_deg; try rewrite demorgan2_ptree_ord;
    try rewrite demorgan2_ptree_formula;
    try apply IHP1; try apply IHP2; try rewrite H1; try rewrite H3;
    auto; unfold demorgan2_sub_formula; simpl; try rewrite HS2;
    try destruct (eq_f f0 (lor E F)); try destruct (eq_f f (lor E F));
    try rewrite sub_fit_true; auto;
    case (eq_nat n0 (Init.Nat.max n n0)) eqn:Hn0;
    simpl; repeat split; auto;
    try apply IHP2; auto; try rewrite H3; auto;
    try rewrite demorgan2_ptree_ord; auto;
    try rewrite <- H8; try apply ord_max_succ_r; auto;
    try rewrite demorgan2_ptree_deg; auto; try rewrite <- H6; try apply max_lem2; auto;
    try apply ord_succ_nf; try apply ord_max_nf; try rewrite H7; try rewrite H8; try apply ptree_ord_nf; auto.
  
  - simpl. destruct S; auto.
  
  - simpl. inversion H as [[[H1 H2] H3] H4]. destruct S; auto.
    destruct S1; auto; destruct (subst_ind_fit f0 S2) eqn:HS2; simpl;
    repeat split; auto; rewrite demorgan2_ptree_formula_true;
    try apply IHP; auto; try rewrite H1; simpl; try rewrite non_target_fit,HS2;
    try rewrite demorgan2_ptree_deg; try rewrite demorgan2_ptree_ord; auto.
    + rewrite demorgan2_ptree_formula; auto. rewrite H1.
      unfold demorgan2_sub_formula. simpl. rewrite non_target_fit,HS2.
      simpl. rewrite <- sub_fit_true; auto.
      * rewrite non_target_sub. rewrite <- sub_fit_true; auto.
      * apply non_target_fit.
    + rewrite demorgan2_ptree_formula; auto. rewrite H1.
      unfold demorgan2_sub_formula. simpl. rewrite non_target_fit,HS2.
      simpl. rewrite <- sub_fit_true; auto.
      * rewrite non_target_sub. rewrite <- sub_fit_true; auto.
      * apply non_target_fit.
  
  - simpl. destruct S; apply H.
  
  - simpl. destruct S; try apply H. inversion H as [[[H0 H1] H2] H3].
    destruct S1; inversion Hs; rewrite H5; simpl.
    + repeat split; auto.
      * rewrite demorgan2_ptree_formula_true, demorgan2_ptree_formula; auto.
        { rewrite H0. unfold demorgan2_sub_formula.
          { rewrite formula_sub_ind_lor. simpl.
            { destruct (eq_f (substitution f n (projT1 c))); auto. }
            { simpl. apply H5. } } }
        { rewrite H0. simpl. apply H5. }
      * rewrite demorgan2_ptree_formula_true.
        { apply IHP; auto. rewrite H0. simpl. apply H5. }
        { rewrite H0. simpl. apply H5. }
      * rewrite demorgan2_ptree_formula_true.
        { rewrite demorgan2_ptree_deg; auto. }
        { rewrite H0. simpl. auto. }
      * rewrite demorgan2_ptree_formula_true.
        { rewrite demorgan2_ptree_ord; auto. }
        { rewrite H0. simpl. auto. }
    + repeat split; auto.
      * rewrite demorgan2_ptree_formula_true, demorgan2_ptree_formula; auto.
        { rewrite H0. unfold demorgan2_sub_formula.
          { rewrite formula_sub_ind_lor. simpl.
            { destruct (eq_f (substitution f n (projT1 c))); auto. }
            { simpl. apply H5. } } }
        { rewrite H0. simpl. apply H5. }
      * rewrite demorgan2_ptree_formula_true.
        { apply IHP; auto. rewrite H0. simpl. apply H5. }
        { rewrite H0. simpl. apply H5. }
      * rewrite demorgan2_ptree_formula_true.
        { rewrite demorgan2_ptree_deg; auto. }
        { rewrite H0. simpl. auto. }
      * rewrite demorgan2_ptree_formula_true.
        { rewrite demorgan2_ptree_ord; auto. }
        { rewrite H0. simpl. auto. }
  
  - intros. simpl. destruct S; apply H.
  
  - rename H into H0. rename X into H. rename Hs into H1.
    simpl. destruct S; try apply H0. destruct S1; inversion H1.
    + rewrite H3. simpl. intros. destruct (valid_w_rule_ad _ _ _ _ _ _ H0 t)  as [[[H4 H5] H6] H7].
      repeat split.
      * rewrite demorgan2_ptree_formula_true, demorgan2_ptree_formula; auto.
        { rewrite H4. unfold demorgan2_sub_formula. rewrite formula_sub_ind_lor.
          { rewrite (non_target_term_sub f n (projT1 t)).
            rewrite non_target_sub. auto. }
          { rewrite (non_target_term_sub f n (projT1 t)).
            rewrite non_target_fit. apply H3. } }
        { rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
          rewrite non_target_fit. apply H3. }
      * rewrite demorgan2_ptree_formula_true.
        { apply H. apply H5. rewrite H4. simpl.
          rewrite (non_target_term_sub f n (projT1 t)).
          rewrite non_target_fit. apply H3. }
        { rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
          rewrite non_target_fit. apply H3. }
      * rewrite demorgan2_ptree_formula_true.
        { rewrite demorgan2_ptree_deg; auto. }
        { rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
          rewrite non_target_fit. rewrite H3. auto. }
      * rewrite demorgan2_ptree_formula_true.
        { rewrite demorgan2_ptree_ord; auto. }
        { rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
          rewrite non_target_fit. rewrite H3. auto. }
    + rewrite H3. simpl. intros. destruct (valid_w_rule_ad _ _ _ _ _ _ H0 t) as [[[H4 H5] H6] H7].
      repeat split.
      * rewrite demorgan2_ptree_formula_true, demorgan2_ptree_formula; auto.
        { rewrite H4. unfold demorgan2_sub_formula. rewrite formula_sub_ind_lor.
          { rewrite (non_target_term_sub f n (projT1 t)).
            rewrite non_target_sub. auto. }
          { rewrite (non_target_term_sub f n (projT1 t)).
            rewrite non_target_fit. apply H3. } }
        { rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
          rewrite non_target_fit. apply H3. }
      * rewrite demorgan2_ptree_formula_true.
        { apply H. apply H5. rewrite H4. simpl.
          rewrite (non_target_term_sub f n (projT1 t)).
          rewrite non_target_fit. apply H3. }
        { rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
          rewrite non_target_fit. apply H3. }
      * rewrite demorgan2_ptree_formula_true.
        { rewrite demorgan2_ptree_deg; auto. }
        { rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
          rewrite non_target_fit. rewrite H3. auto. }
      * rewrite demorgan2_ptree_formula_true.
        { rewrite demorgan2_ptree_ord; auto. }
        { rewrite H4. simpl. rewrite (non_target_term_sub f n (projT1 t)).
          rewrite non_target_fit. rewrite H3. auto. }
  - clear IHP2. simpl. destruct (subst_ind_fit f S) eqn:Heq; try apply H. simpl.
    inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
    repeat split; auto; rewrite demorgan2_ptree_formula_true.
    + rewrite demorgan2_ptree_formula; auto.
      rewrite H1. unfold demorgan2_sub_formula. rewrite formula_sub_ind_lor.
      * rewrite non_target_sub. auto.
      * rewrite Heq, non_target_fit. auto.
    + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
    + apply IHP1; auto. rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
    + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
    + rewrite demorgan2_ptree_deg; auto.
    + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
    + rewrite demorgan2_ptree_ord; auto.
    + rewrite H1. simpl. rewrite Heq, non_target_fit. auto.
  
  - clear IHP1. simpl. destruct (subst_ind_fit f0 S) eqn:Heq; try apply H. simpl.
    inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
    repeat split; auto; rewrite demorgan2_ptree_formula_true.
    + rewrite demorgan2_ptree_formula; auto.
      rewrite H3. unfold demorgan2_sub_formula. rewrite formula_sub_ind_lor.
      * rewrite non_target_sub. auto.
      * rewrite Heq, non_target_fit. auto.
    + rewrite H3. simpl. auto.
    + apply IHP2; auto. rewrite H3. simpl. auto.
    + rewrite H3. simpl. auto.
    + rewrite demorgan2_ptree_deg; auto.
    + rewrite H3. simpl. auto.
    + rewrite demorgan2_ptree_ord; auto.
    + rewrite H3. simpl. auto.
  
  - simpl. inversion H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
    destruct S; try inversion Hs. rewrite H9.
    destruct (and_bool_prop _ _ H9) as [H10 H11].
    simpl. repeat split; rewrite demorgan2_ptree_formula_true.
    + rewrite demorgan2_ptree_formula; auto.
      rewrite H1. unfold demorgan2_sub_formula. rewrite formula_sub_ind_lor.
      * rewrite non_target_sub. auto.
      * rewrite H10, non_target_fit. auto.
    + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
    + apply IHP1; auto. rewrite H1. simpl. rewrite H10, non_target_fit. auto.
    + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
    + rewrite demorgan2_ptree_formula; auto.
      rewrite H3. unfold demorgan2_sub_formula. rewrite formula_sub_ind_lor.
      * rewrite non_target_sub. auto.
      * rewrite H11, non_target_fit. auto.
    + rewrite H3. simpl. auto.
    + apply IHP2; auto. rewrite H3. simpl. auto.
    + rewrite H3. simpl. auto.
    + rewrite demorgan2_ptree_deg; auto.
    + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
    + rewrite demorgan2_ptree_deg; auto.
    + rewrite H3. simpl. auto.
    + rewrite demorgan2_ptree_ord; auto.
    + rewrite H1. simpl. rewrite H10, non_target_fit. auto.
    + rewrite demorgan2_ptree_ord; auto.
    + rewrite H3. simpl. auto.
  Qed.
  
  
  
  
  
  (* We finally show that if the formulas ~~A and/or ~~A \/ D are provable,
  so are the formulas A and/or A \/ D *)
  (* *)
  Lemma demorgan2_invertible_a :
    forall (A B : formula) (d : nat) (alpha : ord),
    provable (neg (lor A B)) d alpha -> provable (neg B) d alpha.
  Proof.
  unfold provable. intros A B d alpha H. destruct H as [t [[[Ht1 Ht2] Ht3] Ht4]].
  exists (demorgan2_sub_ptree t A B (1)). unfold P_proves. repeat split.
  - rewrite demorgan2_ptree_formula; auto. rewrite Ht1.
    unfold demorgan2_sub_formula. simpl. repeat rewrite eq_f_refl. auto.
  - apply demorgan2_valid; auto. rewrite Ht1. auto.
  - rewrite demorgan2_ptree_deg; auto.
  - rewrite demorgan2_ptree_ord; auto.
  Qed.
  
  Lemma demorgan2_invertible_ad :
    forall (A B D : formula) (d : nat) (alpha : ord),
    provable (lor (neg (lor A B)) D) d alpha -> provable (lor (neg B) D) d alpha.
  Proof.
  unfold provable. intros A B D d alpha H. destruct H as [t [[[Ht1 Ht2] Ht3] Ht4]].
  exists (demorgan2_sub_ptree t A B (lor_ind (1) (non_target D))).
  unfold P_proves. repeat split.
  - rewrite demorgan2_ptree_formula; auto. rewrite Ht1.
    unfold demorgan2_sub_formula. simpl. rewrite non_target_fit.
    repeat rewrite eq_f_refl. simpl. rewrite <- sub_fit_true.
    + rewrite non_target_sub. auto.
    + apply non_target_fit.
  - apply demorgan2_valid; auto. rewrite Ht1. simpl. apply non_target_fit.
  - rewrite demorgan2_ptree_deg; auto.
  - rewrite demorgan2_ptree_ord; auto.
  Qed.
*)