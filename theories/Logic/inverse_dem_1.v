Add LoadPath "theories/Casteran" as Ordering.
Add LoadPath "theories/Maths" as Maths_Facts.
Add LoadPath "theories/Logic" as Systems.

From Maths_Facts Require Import naturals.
From Maths_Facts Require Import ordinals.

From Systems Require Import definitions.
From Systems Require Import fol.
From Systems Require Import proof_trees.
From Systems Require Import substitute.

Definition demorgan1_sub_formula (A E F : formula) (S : subst_ind) : formula :=
  formula_sub_ind A (neg (lor E F)) (neg E) S.

Lemma demorgan1_sub_formula_closed :
    forall (A : formula),
        closed A = true ->
            forall (E F : formula) (S : subst_ind),
                closed (demorgan1_sub_formula A E F S) = true.
Proof.
intros A CA E F S.
unfold demorgan1_sub_formula.
apply (formula_sub_ind_closed _ _ _ CA).
unfold closed; fold closed.
apply and_bool_prop.
Qed.

Fixpoint demorgan1_sub_ptree_fit
  (P : ptree) (E F : formula) (S : subst_ind) : ptree :=
match P, S with
| deg_up d P', _ => deg_up d (demorgan1_sub_ptree_fit P' E F S)

| ord_up alpha P', _ => ord_up alpha (demorgan1_sub_ptree_fit P' E F S)

| node A, _ => P

| exchange_ab A B d alpha P', lor_ind S_B S_A =>
    exchange_ab
      (demorgan1_sub_formula A E F S_A)
      (demorgan1_sub_formula B E F S_B)
      d alpha
      (demorgan1_sub_ptree_fit P' E F (lor_ind S_A S_B))

| exchange_cab C A B d alpha P', lor_ind (lor_ind S_C S_B) S_A =>
    exchange_cab
      (demorgan1_sub_formula C E F S_C)
      (demorgan1_sub_formula A E F S_A)
      (demorgan1_sub_formula B E F S_B)
      d alpha
      (demorgan1_sub_ptree_fit P' E F (lor_ind (lor_ind S_C S_A) S_B))

| exchange_abd A B D d alpha P', lor_ind (lor_ind S_B S_A) S_D =>
    exchange_abd
      (demorgan1_sub_formula A E F S_A)
      (demorgan1_sub_formula B E F S_B)
      (demorgan1_sub_formula D E F S_D)
      d alpha
      (demorgan1_sub_ptree_fit P' E F (lor_ind (lor_ind S_A S_B) S_D))

| exchange_cabd C A B D d alpha P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D =>
    exchange_cabd
      (demorgan1_sub_formula C E F S_C)
      (demorgan1_sub_formula A E F S_A)
      (demorgan1_sub_formula B E F S_B)
      (demorgan1_sub_formula D E F S_D)
      d alpha
      (demorgan1_sub_ptree_fit P' E F (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D))

| contraction_a A d alpha P', _ =>
    contraction_a
      (demorgan1_sub_formula A E F S)
      d alpha
      (demorgan1_sub_ptree_fit P' E F (lor_ind S S))

| contraction_ad A D d alpha P', lor_ind S_A S_D =>
    contraction_ad
      (demorgan1_sub_formula A E F S_A)
      (demorgan1_sub_formula D E F S_D)
      d alpha
      (demorgan1_sub_ptree_fit P' E F (lor_ind (lor_ind S_A S_A) S_D))

| weakening_ad A D d alpha P', lor_ind S_A S_D =>
    weakening_ad
      (demorgan1_sub_formula A E F S_A)
      (demorgan1_sub_formula D E F S_D)
      d alpha
      (demorgan1_sub_ptree_fit P' E F S_D)

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, _ =>
    (match form_eqb A E, form_eqb B F, S with
    | true, true, (1) =>
      (match nat_eqb d1 (ptree_deg P) with
      | true => ord_up (ptree_ord P) P1
      | false => deg_up (ptree_deg P) (ord_up (ptree_ord P) P1)
      end)
    | _, _, _ => P
    end)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_AB S_D =>
    (match form_eqb A E, form_eqb B F, S_AB with
    | true, true, (1) =>
      (match nat_eqb d1 (ptree_deg P) with
      | true =>
          ord_up
            (ptree_ord P)
            (demorgan1_sub_ptree_fit P1 E F (lor_ind (non_target (neg A)) S_D))
      | false =>
          deg_up
            (ptree_deg P)
              (ord_up
                (ptree_ord P)
                (demorgan1_sub_ptree_fit
                  P1 E F
                  (lor_ind (non_target (neg A)) S_D)))
      end)
    | _, _, _ =>
        demorgan_abd
          A B
          (demorgan1_sub_formula D E F S_D)
          d1 d2 alpha1 alpha2
          (demorgan1_sub_ptree_fit P1 E F (lor_ind (non_target (neg A)) S_D))
          (demorgan1_sub_ptree_fit P2 E F (lor_ind (non_target (neg B)) S_D))
    end)

| negation_a A d alpha P', _ => P

| negation_ad A D d alpha P', lor_ind S_A S_D =>
    negation_ad
      A
      (demorgan1_sub_formula D E F S_D)
      d alpha
      (demorgan1_sub_ptree_fit P' E F (lor_ind (non_target A) S_D))

| quantification_a A n t d alpha P', _ => P

| quantification_ad A D n t d alpha P', lor_ind S_A S_D =>
    quantification_ad
      A
      (demorgan1_sub_formula D E F S_D)
      n t d alpha
      (demorgan1_sub_ptree_fit P' E F (lor_ind (0) S_D))

| w_rule_a A n d alpha g, _ => P

| w_rule_ad A D n d alpha g, lor_ind S_A S_D =>
    w_rule_ad
      A
      (demorgan1_sub_formula D E F S_D)
      n d alpha
      (fun (t : c_term) =>
          demorgan1_sub_ptree_fit (g t) E F (lor_ind (non_target A) S_D))

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ca
      (demorgan1_sub_formula C E F S)
      A d1 d2 alpha1 alpha2
      (demorgan1_sub_ptree_fit P1 E F (lor_ind S (non_target A)))
      P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ad
      A
      (demorgan1_sub_formula D E F S)
      d1 d2 alpha1 alpha2
      P1
      (demorgan1_sub_ptree_fit P2 E F (lor_ind (0) S))

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_D =>
    cut_cad
      (demorgan1_sub_formula C E F S_C)
      A
      (demorgan1_sub_formula D E F S_D)
      d1 d2 alpha1 alpha2
      (demorgan1_sub_ptree_fit P1 E F (lor_ind S_C (non_target A)))
      (demorgan1_sub_ptree_fit P2 E F (lor_ind (0) S_D))

| _, _ => P
end.

Definition demorgan1_sub_ptree
  (P : ptree) (E F : formula) (S : subst_ind) : ptree :=
match subst_ind_fit (ptree_formula P) S with
| false => P
| true => demorgan1_sub_ptree_fit P E F S
end.

Lemma demorgan1_ptree_formula_true :
    forall (P : ptree) (E F : formula) (S : subst_ind),
        subst_ind_fit (ptree_formula P) S = true ->
            demorgan1_sub_ptree_fit P E F S = demorgan1_sub_ptree P E F S.
Proof.
intros P E F S FS.
unfold demorgan1_sub_ptree.
rewrite FS.
reflexivity.
Qed.

Lemma demorgan1_ptree_formula' :
    forall (P : ptree) (E F : formula),
        valid P ->
            forall (S : subst_ind),
                subst_ind_fit (ptree_formula P) S = true ->
                    ptree_formula (demorgan1_sub_ptree P E F S) =
                        demorgan1_sub_formula (ptree_formula P) E F S.
Proof.
intros P E F.
induction P; try intros PV S FS;
unfold demorgan1_sub_ptree;
rewrite FS;
unfold ptree_formula in *; fold ptree_formula in *;
unfold demorgan1_sub_ptree_fit; fold demorgan1_sub_ptree_fit.
  
1 : destruct PV as [ID PV].
2 : destruct PV as [[IO PV] NO].
13-14 : destruct PV as [[[PF PV] PD] PO].

1-2 : rewrite (demorgan1_ptree_formula_true _ _ _ _ FS);
      unfold ptree_formula; fold ptree_formula;
      apply (IHP PV _ FS).

1 : { inversion PV as [PX].
      unfold demorgan1_sub_ptree, demorgan1_sub_formula, formula_sub_ind.
      rewrite FS.
      unfold ptree_formula; fold ptree_formula.
      destruct (axiom_atomic _ PX) as [[a fa] | [a fa]];
      rewrite fa;
      unfold formula_sub_ind_fit; fold formula_sub_ind_fit;
      unfold form_eqb;
      reflexivity. }

5 : reflexivity.

9,11,13,15,16 : unfold ptree_formula, demorgan1_sub_formula, formula_sub_ind, formula_sub_ind_fit, form_eqb;
                destruct S;
                try reflexivity.

all : destruct S; inversion FS as [FS'];
      try reflexivity.

1,5,6,13 :  apply and_bool_prop in FS';
            destruct FS' as [FS1 FS2];
            unfold ptree_formula, demorgan1_sub_formula, formula_sub_ind, formula_sub_ind_fit;
            fold formula_sub_ind_fit;
            rewrite FS,FS1,FS2;
            reflexivity.

4-6 : case (form_eqb f E) eqn:EQ1;
      case (form_eqb f0 F) eqn:EQ2;
      unfold ptree_formula, demorgan1_sub_formula, formula_sub_ind, subst_ind_fit, formula_sub_ind_fit, form_eqb;
      fold ptree_formula form_eqb formula_sub_ind_fit subst_ind_fit;
      try rewrite EQ1;
      try rewrite EQ2;
      try reflexivity.

all : unfold "&&".

4 : { destruct PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].
      apply form_eqb_eq in EQ1,EQ2.
      destruct EQ1,EQ2.
      case (nat_eqb n (ptree_deg (demorgan_ab f f0 n n0 o o0 P1 P2))) eqn:EQ;
      unfold ptree_formula; fold ptree_formula;
      apply P1F. }

all : destruct S1; inversion FS' as [FS''].

5 : { destruct PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].
      apply form_eqb_eq in EQ1,EQ2.
      destruct EQ1,EQ2.
      assert (subst_ind_fit (ptree_formula P1) (lor_ind (non_target (neg f)) S2) = true) as FS1.
      { rewrite P1F.
        unfold subst_ind_fit, non_target; fold subst_ind_fit.
        apply FS'. }
      case (nat_eqb n (ptree_deg (demorgan_abd f f0 f1 n n0 o o0 P1 P2))) eqn:EQ;
      unfold ptree_formula; fold ptree_formula;
      rewrite (demorgan1_ptree_formula_true _ _ _ _ FS1);
      rewrite (IHP1 P1V _ FS1);
      unfold demorgan1_sub_formula;
      rewrite P1F;
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

all : unfold ptree_formula, demorgan1_sub_formula, formula_sub_ind, formula_sub_ind_fit, form_eqb;
      fold ptree_formula form_eqb formula_sub_ind_fit;
      try rewrite FS;
      try rewrite FS'';
      try rewrite EQ;
      try rewrite FS1_1,FS1_2,FS2;
      try rewrite FS1_1_1,FS1_1_2,FS1_2,FS2;      
      unfold "&&";
      try reflexivity.
Qed.

Lemma demorgan1_ptree_formula :
    forall (P : ptree) (E F : formula),
        valid P ->
            forall (S : subst_ind),
                ptree_formula (demorgan1_sub_ptree P E F S) =
                    demorgan1_sub_formula (ptree_formula P) E F S.
Proof.
intros P E F PV S.
destruct (subst_ind_fit (ptree_formula P) S) eqn:FS.
- apply (demorgan1_ptree_formula' _ _ _ PV _ FS).
- unfold demorgan1_sub_ptree, demorgan1_sub_formula, formula_sub_ind.
  rewrite FS.
  reflexivity.
Qed.

Lemma demorgan1_ptree_deg :
    forall (P : ptree) (E F : formula),
        valid P ->
            forall (S : subst_ind),
                ptree_deg (demorgan1_sub_ptree P E F S) = ptree_deg P.
Proof.
intros P E F PV.
unfold demorgan1_sub_ptree.
pose (ptree_formula P) as A.
induction P; intros S;
case (subst_ind_fit A S) eqn:FS;
unfold A in FS;
try rewrite FS;
unfold demorgan1_sub_ptree_fit; fold demorgan1_sub_ptree_fit;
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

4-6 : case (form_eqb f E) eqn:EQ1;
      case (form_eqb f0 F) eqn:EQ2;
      unfold ptree_deg; fold ptree_deg;
      try rewrite P1D;
      try rewrite P2D;
      case (nat_eqb (ptree_deg P1) (Nat.max (ptree_deg P1) (ptree_deg P2))) eqn:EQ;
      unfold ptree_deg; fold ptree_deg;
      try reflexivity.

4 : apply nat_eqb_eq in EQ;
    destruct EQ;
    reflexivity.

all : destruct S1; inversion FS' as [FS''].

3 : destruct S1_1; inversion FS'' as [FS'''].

all : unfold ptree_deg; fold ptree_deg;
      try reflexivity.

- apply nat_eqb_eq in EQ;
  destruct EQ.
  rewrite <- (IHP1 P1V (lor_ind (non_target (neg f)) S2)).
  rewrite P1F.
  unfold subst_ind_fit, non_target; fold subst_ind_fit.
  rewrite FS'.
  reflexivity.
Qed.

Lemma demorgan1_ptree_ord :
    forall (P : ptree) (E F : formula),
        valid P ->
            forall (S : subst_ind),
                ptree_ord (demorgan1_sub_ptree P E F S) = ptree_ord P.
Proof.
intros P E F PV.
unfold demorgan1_sub_ptree.
pose (ptree_formula P) as A.
induction P; intros S;
case (subst_ind_fit A S) eqn:FS;
unfold A in FS;
try rewrite FS;
unfold demorgan1_sub_ptree_fit; fold demorgan1_sub_ptree_fit;
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

4-6 : case (form_eqb f E) eqn:EQ1;
      case (form_eqb f0 F) eqn:EQ2;
      unfold ptree_deg; fold ptree_deg;
      case (nat_eqb n (Nat.max n n0)) eqn:EQ;
      try reflexivity.

all : destruct S1; inversion FS' as [FS''].

3 : destruct S1_1; inversion FS'' as [FS'''].

all : unfold ptree_ord; fold ptree_ord;
      try reflexivity.
Qed.

(* *)
Lemma demorgan1_valid :
    forall (P : ptree) (E F : formula),
        valid P ->
            forall (S : subst_ind),
                subst_ind_fit (ptree_formula P) S = true ->
                    valid (demorgan1_sub_ptree P E F S).
Proof.
intros P E F PV.
induction P; try intros S FS;
unfold demorgan1_sub_ptree;
rewrite FS;
unfold ptree_formula in *; fold ptree_formula in *;
unfold demorgan1_sub_ptree_fit; fold demorgan1_sub_ptree_fit.

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
          rewrite non_target_sub_fit.
          unfold "&&".
          apply FS2. }

        repeat split;
        destruct (PV t) as [[[PF PVt] PD] PO];
        rewrite (demorgan1_ptree_formula_true _ _ _ _ (FSt t)).
        - rewrite (demorgan1_ptree_formula _ _ _ PVt).
          rewrite PF.
          unfold demorgan1_sub_formula.
          rewrite (non_target_term_sub _ n (projT1 t)).
          rewrite non_target_sub_lor.
          reflexivity.
        - apply (X _ PVt _ (FSt t)).
        - rewrite (demorgan1_ptree_deg _ _ _ PVt).
          apply PD.
        - rewrite (demorgan1_ptree_ord _ _ _ PVt).
          apply PO. }

10 :  assert (closed (neg (lor E F)) = true -> closed (neg E) = true) as CIMP.
10 :  { unfold closed; fold closed;
        apply and_bool_prop. }

7,8,11,12 : case (form_eqb f E) eqn:EQ1;
            case (form_eqb f0 F) eqn:EQ2;
            unfold ptree_deg; fold ptree_deg;
            try apply PV.

11,15 : case (nat_eqb n (Nat.max n n0)) eqn:EQ.
            
all : try apply form_eqb_eq in EQ1;
      try destruct EQ1;
      try apply form_eqb_eq in EQ2;
      try destruct EQ2;
      repeat rewrite demorgan1_ptree_formula_true;
      repeat split;
      try apply IHP;
      try apply IHP1;
      try apply IHP2;
      unfold ptree_deg; fold ptree_deg;
      try rewrite demorgan1_ptree_deg;
      try rewrite demorgan1_ptree_ord;
      try apply ptree_ord_nf;
      unfold ptree_ord; fold ptree_ord;
      try rewrite demorgan1_ptree_formula;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold demorgan1_sub_formula, formula_sub_ind;
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
      unfold form_eqb; fold form_eqb;
      try rewrite non_target_sub';
      try reflexivity;
      try rewrite <- (sub_fit_true _ _ _ _ FS1);
      try apply (formula_sub_ind_closed _ _ _ FC CIMP);
      try apply max_lem1;
      try apply EQ;
      try apply ord_lt_max_succ_l;
      try case (form_eqb f (lor E F));
      try case (form_eqb f0 (lor E F));
      try case (form_eqb (substitution f n (projT1 c)) (lor E F));
      try case (form_eqb f (lor f f0));
      try case (form_eqb f0 (lor f f0));
      try case (form_eqb f (lor f F));
      try case (form_eqb f0 (lor f F));
      try case (form_eqb f (lor E f0));
      try case (form_eqb f0 (lor E f0));
      try reflexivity.
Qed.