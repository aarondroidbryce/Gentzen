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
From Systems Require Import inverse_omega.

Require Import Lia.

Definition quantif_sub_formula
  (A E F : formula) (n : nat) (S : subst_ind) : formula :=
  formula_sub_ind A (neg (univ n E)) F S.

Lemma quantif_sub_formula_closed :
    forall (A : formula),
        closed A = true ->
            forall (E F : formula) (n : nat) (S : subst_ind), closed F = true ->
                closed (quantif_sub_formula A E F n S) = true.
Proof.
intros A CA E F n S CF.
unfold quantif_sub_formula.
apply (formula_sub_ind_closed _ _ _ CA).
intros CnuE.
apply CF.
Qed.

Definition weak_ord_up (P: ptree) (alpha : ord) :=
match ord_ltb (ptree_ord P) alpha with
| true => ord_up alpha P
| false => P
end.

Lemma weak_ord_formula :
    forall (P : ptree) (alpha : ord),
        ptree_formula (weak_ord_up P alpha) = ptree_formula P.
Proof.
intros P alpha.
unfold weak_ord_up.
case (ord_ltb (ptree_ord P) alpha);
unfold ptree_formula;
reflexivity.
Qed.

Lemma weak_ord_deg :
    forall (P : ptree) (alpha : ord),
        ptree_deg (weak_ord_up P alpha) = ptree_deg P.
Proof.
intros P alpha.
unfold weak_ord_up.
case (ord_ltb (ptree_ord P) alpha);
unfold ptree_deg;
reflexivity.
Qed.

Lemma weak_ord_valid :
    forall (P : ptree) (alpha : ord),
        nf alpha ->
            valid P ->
                valid (weak_ord_up P alpha).
Proof.
intros P alpha NO VP.
unfold weak_ord_up.
case (ord_ltb (ptree_ord P) alpha) eqn:IO.
- repeat split.
  + apply ord_ltb_lt in IO.
    apply IO.
  + apply VP.
  + apply NO.
- apply VP.
Qed.

Fixpoint quantif_sub_ptree_fit
  (P Q : ptree) (E F : formula) (n dQ : nat) (beta : ord) (QP : P_proves Q (lor F (univ n E)) dQ beta) (S : subst_ind) : ptree :=
  match P, S with
| deg_up d P', _ => match nat_ltb (ptree_deg (quantif_sub_ptree_fit P' Q E F n dQ beta QP S)) d with
    | true => deg_up d (quantif_sub_ptree_fit P' Q E F n dQ beta QP S)
    | false => (quantif_sub_ptree_fit P' Q E F n dQ beta QP S)
    end
| ord_up alpha P', _ => match ord_ltb (ptree_ord (quantif_sub_ptree_fit P' Q E F n dQ beta QP S)) alpha with
    | true => ord_up alpha (quantif_sub_ptree_fit P' Q E F n dQ beta QP S)
    | false => (quantif_sub_ptree_fit P' Q E F n dQ beta QP S)
    end

| node A, _ => P

| exchange_ab A B d alpha P', lor_ind S_B S_A =>
    exchange_ab
      (quantif_sub_formula A E F n S_A)
      (quantif_sub_formula B E F n S_B)
      (ptree_deg (quantif_sub_ptree_fit P' Q E F n dQ beta QP (lor_ind S_A S_B)))
      (ptree_ord (quantif_sub_ptree_fit P' Q E F n dQ beta QP (lor_ind S_A S_B)))
      (quantif_sub_ptree_fit P' Q E F n dQ beta QP (lor_ind S_A S_B))

| exchange_cab C A B d alpha P', lor_ind (lor_ind S_C S_B) S_A =>
    exchange_cab
      (quantif_sub_formula C E F n S_C)
      (quantif_sub_formula A E F n S_A)
      (quantif_sub_formula B E F n S_B)
      (ptree_deg (quantif_sub_ptree_fit P' Q E F n dQ beta QP (lor_ind (lor_ind S_C S_A) S_B)))
      (ptree_ord (quantif_sub_ptree_fit P' Q E F n dQ beta QP (lor_ind (lor_ind S_C S_A) S_B)))
      (quantif_sub_ptree_fit P' Q E F n dQ beta QP (lor_ind (lor_ind S_C S_A) S_B))

| exchange_abd A B D d alpha P', lor_ind (lor_ind S_B S_A) S_D =>
    exchange_abd
      (quantif_sub_formula A E F n S_A)
      (quantif_sub_formula B E F n S_B)
      (quantif_sub_formula D E F n S_D)
      (ptree_deg (quantif_sub_ptree_fit P' Q E F n dQ beta QP (lor_ind (lor_ind S_A S_B) S_D)))
      (ptree_ord (quantif_sub_ptree_fit P' Q E F n dQ beta QP (lor_ind (lor_ind S_A S_B) S_D)))
      (quantif_sub_ptree_fit P' Q E F n dQ beta QP (lor_ind (lor_ind S_A S_B) S_D))

| exchange_cabd C A B D d alpha P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D =>
    exchange_cabd
      (quantif_sub_formula C E F n S_C)
      (quantif_sub_formula A E F n S_A)
      (quantif_sub_formula B E F n S_B)
      (quantif_sub_formula D E F n S_D)
      (ptree_deg (quantif_sub_ptree_fit P' Q E F n dQ beta QP (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D)))
      (ptree_ord (quantif_sub_ptree_fit P' Q E F n dQ beta QP (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D)))
      (quantif_sub_ptree_fit P' Q E F n dQ beta QP (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D))

| contraction_a A d alpha P', _ =>
    contraction_a
      (quantif_sub_formula A E F n S)
      (ptree_deg (quantif_sub_ptree_fit P' Q E F n dQ beta QP (lor_ind S S)))
      (ptree_ord (quantif_sub_ptree_fit P' Q E F n dQ beta QP (lor_ind S S)))
      (quantif_sub_ptree_fit P' Q E F n dQ beta QP (lor_ind S S))

| contraction_ad A D d alpha P', lor_ind S_A S_D =>
    contraction_ad
      (quantif_sub_formula A E F n S_A)
      (quantif_sub_formula D E F n S_D)
      (ptree_deg (quantif_sub_ptree_fit P' Q E F n dQ beta QP (lor_ind (lor_ind S_A S_A) S_D)))
      (ptree_ord (quantif_sub_ptree_fit P' Q E F n dQ beta QP (lor_ind (lor_ind S_A S_A) S_D)))
      (quantif_sub_ptree_fit P' Q E F n dQ beta QP (lor_ind (lor_ind S_A S_A) S_D))

| weakening_ad A D d alpha P', lor_ind S_A S_D =>
    weakening_ad
      (quantif_sub_formula A E F n S_A)
      (quantif_sub_formula D E F n S_D)
      (ptree_deg (quantif_sub_ptree_fit P' Q E F n dQ beta QP S_D))
      (ptree_ord (quantif_sub_ptree_fit P' Q E F n dQ beta QP S_D))
      (quantif_sub_ptree_fit P' Q E F n dQ beta QP S_D)

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, _ => P

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_AB S_D =>
    demorgan_abd
      A B
      (quantif_sub_formula D E F n S_D)
      (ptree_deg (quantif_sub_ptree_fit P1 Q E F n dQ beta QP (lor_ind (0) S_D)))
      (ptree_deg (quantif_sub_ptree_fit P2 Q E F n dQ beta QP (lor_ind (0) S_D)))
      (ptree_ord (quantif_sub_ptree_fit P1 Q E F n dQ beta QP (lor_ind (0) S_D)))
      (ptree_ord (quantif_sub_ptree_fit P2 Q E F n dQ beta QP (lor_ind (0) S_D)))
      (quantif_sub_ptree_fit P1 Q E F n dQ beta QP (lor_ind (0) S_D))
      (quantif_sub_ptree_fit P2 Q E F n dQ beta QP (lor_ind (0) S_D))

| negation_a A d alpha P', _ => P

| negation_ad A D d alpha P', lor_ind S_A S_D =>
    negation_ad
      A
      (quantif_sub_formula D E F n S_D)
      (ptree_deg (quantif_sub_ptree_fit P' Q E F n dQ beta QP (lor_ind (non_target A) S_D)))
      (ptree_ord (quantif_sub_ptree_fit P' Q E F n dQ beta QP (lor_ind (non_target A) S_D)))
      (quantif_sub_ptree_fit P' Q E F n dQ beta QP (lor_ind (non_target A) S_D))

| quantification_a A k t d alpha P', _ =>
    (match form_eqb A E, nat_eqb k n, S with
    | true, true, (1) => (cut_ca F (substitution E n (projT1 t)) (ptree_deg (w_rule_sub_ptree Q E n t (lor_ind (non_target F) (1)))) d beta alpha (w_rule_sub_ptree Q E n t (lor_ind (non_target F) (1))) P')
    | _, _, _ => P
    end)

| quantification_ad A D k t d alpha P', lor_ind S_A S_D =>
    (match form_eqb A E, nat_eqb k n, S_A with
    | true, true, (1) => (cut_cad F (substitution E n (projT1 t)) (quantif_sub_formula D E F n S_D)
                              (ptree_deg (w_rule_sub_ptree Q E n t (lor_ind (non_target F) (1))))
                              (ptree_deg (quantif_sub_ptree_fit P' Q E F n dQ beta QP (lor_ind (0) S_D)))
                              beta (ptree_ord (quantif_sub_ptree_fit P' Q E F n dQ beta QP (lor_ind (0) S_D)))
                              (w_rule_sub_ptree Q E n t (lor_ind (non_target F) (1)))) (quantif_sub_ptree_fit P' Q E F n dQ beta QP (lor_ind (0) S_D))
    | _, _, _ => quantification_ad
                    A (quantif_sub_formula D E F n S_D) k t
                    (ptree_deg (quantif_sub_ptree_fit P' Q E F n dQ beta QP (lor_ind (0) S_D)))
                    (ptree_ord (quantif_sub_ptree_fit P' Q E F n dQ beta QP (lor_ind (0) S_D)))
                    (quantif_sub_ptree_fit P' Q E F n dQ beta QP (lor_ind (0) S_D))
    end)

| w_rule_a A k d alpha g, _ => P

| w_rule_ad A D k d alpha g, lor_ind S_A S_D =>
    w_rule_ad
          A (quantif_sub_formula D E F n S_D) k
          (Nat.max (Nat.max dQ d) (num_conn E + 1))
          (ord_add beta alpha)
          (fun (c : c_term) =>
            (weak_ord_up (quantif_sub_ptree_fit (g c) Q E F n dQ beta QP (lor_ind (non_target A) S_D)) (ord_add beta alpha)))

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ca
      (quantif_sub_formula C E F n S) A
      (ptree_deg (quantif_sub_ptree_fit P1 Q E F n dQ beta QP (lor_ind S (non_target A)))) d2
      (ptree_ord (quantif_sub_ptree_fit P1 Q E F n dQ beta QP (lor_ind S (non_target A)))) alpha2
      (quantif_sub_ptree_fit P1 Q E F n dQ beta QP (lor_ind S (non_target A)))  P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ad
      A (quantif_sub_formula D E F n S)
      d1 (ptree_deg (quantif_sub_ptree_fit P2 Q E F n dQ beta QP (lor_ind (0) S)))
      alpha1 (ptree_ord (quantif_sub_ptree_fit P2 Q E F n dQ beta QP (lor_ind (0) S)))
      P1   (quantif_sub_ptree_fit P2 Q E F n dQ beta QP (lor_ind (0) S))

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_D =>
    cut_cad
      (quantif_sub_formula C E F n S_C) A (quantif_sub_formula D E F n S_D)
      (ptree_deg (quantif_sub_ptree_fit P1 Q E F n dQ beta QP (lor_ind S_C (non_target A))))
      (ptree_deg (quantif_sub_ptree_fit P2 Q E F n dQ beta QP (lor_ind (0) S_D)))
      (ptree_ord (quantif_sub_ptree_fit P1 Q E F n dQ beta QP (lor_ind S_C (non_target A))))
      (ptree_ord (quantif_sub_ptree_fit P2 Q E F n dQ beta QP (lor_ind (0) S_D)))
      (quantif_sub_ptree_fit P1 Q E F n dQ beta QP (lor_ind S_C (non_target A)))
      (quantif_sub_ptree_fit P2 Q E F n dQ beta QP (lor_ind (0) S_D))

| _, _ => P
end.

Definition quantif_sub_ptree
  (P Q : ptree) (E F : formula) (n dQ : nat) (beta : ord) (QP : P_proves Q (lor F (univ n E)) dQ beta) (S : subst_ind) : ptree :=
match subst_ind_fit (ptree_formula P) S with
| false => P
| true => quantif_sub_ptree_fit P Q E F n dQ beta QP S
end.

Lemma quantif_ptree_formula_true :
    forall (P Q : ptree) (E F : formula) (n dQ : nat) (beta : ord) (QP : P_proves Q (lor F (univ n E)) dQ beta) (S : subst_ind),
        subst_ind_fit (ptree_formula P) S = true ->
            quantif_sub_ptree_fit P Q E F n dQ beta QP S = quantif_sub_ptree P Q E F n dQ beta QP S.
Proof.
intros P Q E F n dQ beta QP S FS.
unfold quantif_sub_ptree.
rewrite FS.
reflexivity.
Qed.

Lemma quantif_ptree_formula' :
    forall (P Q : ptree) (E F : formula) (n dQ : nat) (beta : ord) (QP : P_proves Q (lor F (univ n E)) dQ beta),
        valid P ->
            forall (S : subst_ind),
                subst_ind_fit (ptree_formula P) S = true ->
                    ptree_formula (quantif_sub_ptree P Q E F n dQ beta QP S) =
                        quantif_sub_formula (ptree_formula P) E F n S.
Proof.
intros P Q E F n dQ beta QP PV.
induction P; try intros S FS;
unfold quantif_sub_ptree;
rewrite FS;
unfold ptree_formula in *; fold ptree_formula in *;
unfold quantif_sub_ptree_fit; fold quantif_sub_ptree_fit.
  
1 : destruct PV as [ID PV];
    case (nat_ltb (ptree_deg (quantif_sub_ptree_fit P Q E F n dQ beta QP S)) n0) eqn:IE.
3 : destruct PV as [[IO PV] NO];
    case (ord_ltb (ptree_ord (quantif_sub_ptree_fit P Q E F n dQ beta QP S)) o) eqn:IE.

1-4 : rewrite (quantif_ptree_formula_true _ _ _ _ _ _ _ _ _ FS);
      unfold ptree_formula; fold ptree_formula;
      apply (IHP PV _ FS).

1 : { inversion PV as [PX].
      unfold quantif_sub_ptree, quantif_sub_formula, formula_sub_ind.
      rewrite FS.
      unfold ptree_formula; fold ptree_formula.
      destruct (axiom_atomic _ PX) as [[a fa] | [a fa]];
      rewrite fa;
      unfold formula_sub_ind_fit; fold formula_sub_ind_fit;
      unfold form_eqb;
      reflexivity. }

all : destruct S; inversion FS as [FS'];
      try reflexivity.

1,5,6,13 :  apply and_bool_prop in FS';
            destruct FS' as [FS1 FS2];
            unfold ptree_formula, quantif_sub_formula, formula_sub_ind, formula_sub_ind_fit;
            fold formula_sub_ind_fit;
            rewrite FS,FS1,FS2;
            reflexivity.

6,7 : case (form_eqb f E) eqn:EQ1;
      case (nat_eqb n0 n) eqn:EQ2;
      unfold ptree_formula, quantif_sub_formula, formula_sub_ind, subst_ind_fit, formula_sub_ind_fit, form_eqb;
      fold form_eqb;
      rewrite EQ1,EQ2;
      reflexivity.

all : destruct S1; inversion FS' as [FS''].

1-3 : apply and_bool_prop in FS';
      destruct FS' as [FS1 FS2];
      apply and_bool_prop in FS1;
      destruct FS1 as [FS1_1 FS1_2].

3 : destruct S1_1; inversion FS'' as [FS'''];
    apply and_bool_prop in FS1_1;
    destruct FS1_1 as [FS1_1_1 FS1_1_2].
  

8,9 : case (form_eqb f E) eqn:EQ1;
      case (nat_eqb n0 n) eqn:EQ2.

all : unfold ptree_formula, quantif_sub_formula, formula_sub_ind, formula_sub_ind_fit, form_eqb;
      fold ptree_formula form_eqb formula_sub_ind_fit;
      try rewrite FS;
      try rewrite FS'';
      try rewrite EQ1;
      try rewrite EQ2;
      try rewrite FS1_1,FS1_2,FS2;
      try rewrite FS1_1_1,FS1_1_2,FS1_2,FS2;      
      reflexivity.
Qed.

Lemma quantif_ptree_formula :
    forall (P Q : ptree) (E F : formula) (n dQ : nat) (beta : ord) (QP : P_proves Q (lor F (univ n E)) dQ beta),
        valid P ->
            forall (S : subst_ind),
                ptree_formula (quantif_sub_ptree P Q E F n dQ beta QP S) =
                    quantif_sub_formula (ptree_formula P) E F n S.
Proof.
intros P Q E F n dQ beta QP VP S.
destruct (subst_ind_fit (ptree_formula P) S) eqn:FS.
- apply quantif_ptree_formula'.
  apply VP.
  apply FS.
- unfold quantif_sub_ptree, quantif_sub_formula, formula_sub_ind.
  rewrite FS.
  reflexivity.
Qed.

Lemma quantif_ptree_deg :
    forall (P Q : ptree) (E F : formula) (n dQ : nat) (beta : ord) (QP : P_proves Q (lor F (univ n E)) dQ beta),
        valid P ->
            Nat.max dQ (ptree_deg P) < (num_conn E + 2) ->
                forall (S : subst_ind),
                    ptree_deg (quantif_sub_ptree P Q E F n dQ beta QP S) <= (Nat.max (Nat.max dQ (ptree_deg P)) (num_conn E + 1)).
Proof.
intros P Q E F n dQ beta QP PV IE.
inversion QP as [[[QF QV] QD] QO].
pose (ptree_formula P) as A.
induction P; intros S;
unfold quantif_sub_ptree;
case (subst_ind_fit A S) eqn:FS;
unfold A in FS;
try rewrite FS;
unfold quantif_sub_ptree_fit; fold quantif_sub_ptree_fit;
unfold ptree_deg in *; fold ptree_deg in *;
try lia.

1 : destruct PV as [ID PV].
2 : destruct PV as [[IO PV] NO].
3-8 : destruct PV as [[[PF PV] PD] PO].
9 : destruct PV as [[[[PF FC] PV] PD] PO].
11-13 : destruct PV as [[[PF PV] PD] PO].
10,15,16,17: destruct PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].

1 : { unfold ptree_formula in FS; fold ptree_formula in FS.
      case (nat_ltb (ptree_deg (quantif_sub_ptree_fit P Q E F n dQ beta QP S)) n0) eqn:EQ.
      - unfold ptree_deg. lia.
      - rewrite (quantif_ptree_formula_true _ _ _ _ _ _ _ _ _ FS).
        assert (Nat.max dQ (ptree_deg P) < num_conn E + 2) as IE1.
        { lia. }
        pose proof (IHP PV IE1 S);
        try lia. }

1 : { unfold ptree_formula in FS; fold ptree_formula in FS.
      case (ord_ltb (ptree_ord (quantif_sub_ptree_fit P Q E F n dQ beta QP S)) o) eqn:EQ;
      unfold ptree_deg; fold ptree_deg;
      rewrite (quantif_ptree_formula_true _ _ _ _ _ _ _ _ _ FS);
      pose proof (IHP PV IE S);
      try lia. }

5 : rewrite quantif_ptree_formula_true;
    rewrite <- PD in IHP;
    pose proof (IHP PV IE (lor_ind S S));
    try lia.

9 : rewrite quantif_ptree_formula_true;
    rewrite <- P1D in IHP1;
    pose proof (IHP1 P1V (nat_lt_max_shuffle_l _ _ _ _ _ IE) (lor_ind S (non_target f0)));
    try lia.

10 :  rewrite quantif_ptree_formula_true;
      rewrite <- P2D in IHP2;
      pose proof (IHP2 P2V (nat_lt_max_shuffle_r _ _ _ _ _ IE) (lor_ind (0) S));
      try lia.

5,9,10 :  try rewrite PF;
          try rewrite P1F;
          try rewrite P2F;
          unfold subst_ind_fit, ptree_formula in *; fold subst_ind_fit ptree_formula in *;
          try rewrite FS;
          try rewrite non_target_fit;
          reflexivity.

all : destruct S; inversion FS as [FS'];
      try destruct (and_bool_prop _ _ FS') as [FS1 FS2];
      try reflexivity.

10-12 : case (form_eqb f E) eqn:EQ1;
        case (nat_eqb n0 n) eqn:EQ2;
        unfold ptree_deg; fold ptree_deg;
        try lia;
        try rewrite (w_rule_ptree_deg _ _ _ _ QV);
        try destruct S1; inversion FS' as [FS''];
        unfold ptree_deg; fold ptree_deg;
        try rewrite quantif_ptree_formula_true;
        rewrite <- PD in IHP;
        try pose proof (IHP PV IE (lor_ind (0) S2));
        try lia;
        try rewrite PF;
        unfold subst_ind_fit; fold subst_ind_fit;
        try apply FS';
        unfold w_rule_invertible_cut_cad;
        destruct QP; repeat destruct p;
        unfold projT1;
        unfold ptree_deg; fold ptree_deg;
        unfold num_conn; fold num_conn;
        rewrite num_conn_sub;
        try lia.

2,3,4,7,9 : destruct S1; inversion FS' as [FS''];
            try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

4 : destruct S1_1; inversion FS'' as [FS'''];
    try destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

all : unfold ptree_deg; fold ptree_deg;
      try rewrite <- PD in IHP;
      try rewrite <- P1D in IHP1;
      try rewrite <- P2D in IHP2;
      try pose proof (IHP PV IE (lor_ind S2 S1));
      try pose proof (IHP PV IE (lor_ind (lor_ind S1_1 S2) S1_2));
      try pose proof (IHP PV IE (lor_ind (lor_ind S1_2 S1_1) S2));
      try pose proof (IHP PV IE (lor_ind (lor_ind (lor_ind S1_1_1 S1_2) S1_1_2) S2));
      try pose proof (IHP1 P1V (nat_lt_max_max_l _ _ _ _ IE) (lor_ind (0) S2));
      try pose proof (IHP2 P2V (nat_lt_max_max_r _ _ _ _ IE) (lor_ind (0) S2));
      try pose proof (IHP PV IE (lor_ind (non_target f) S2));
      try pose proof (IHP PV IE (lor_ind (lor_ind S1 S1) S2));
      try pose proof (IHP PV IE (S2));
      try pose proof (IHP1 P1V (nat_lt_max_shuffle_l _ _ _ _ _ IE) (lor_ind S1 (non_target f0)));
      try pose proof (IHP2 P2V (nat_lt_max_shuffle_r _ _ _ _ _ IE) (lor_ind (0) S2));
      repeat rewrite quantif_ptree_formula_true;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      try lia;
      unfold subst_ind_fit; fold subst_ind_fit;
      try rewrite non_target_fit;
      try rewrite FS;
      try rewrite FS'';
      try rewrite FS1;
      try rewrite FS2;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      reflexivity.
Qed.

Lemma quantif_ptree_ord :
    forall (P Q : ptree) (E F : formula) (n dQ : nat) (beta : ord) (QP : P_proves Q (lor F (univ n E)) dQ beta),
        valid P ->
            forall (S : subst_ind),
                ord_ltb (ord_add beta (ptree_ord P)) (ptree_ord (quantif_sub_ptree P Q E F n dQ beta QP S)) = false.
Proof.
intros P Q E F n dQ beta QP PV.
inversion QP as [[[QF QV] QD] QO].
pose (ptree_formula P) as A.
induction P; intros S;
unfold quantif_sub_ptree;
case (subst_ind_fit A S) eqn:FS;
unfold A in FS;
try rewrite FS;
unfold quantif_sub_ptree_fit; fold quantif_sub_ptree_fit;
unfold ptree_ord in *; fold ptree_ord in *;
try apply add_left_non_decr.

1 : destruct PV as [ID PV].
2 : destruct PV as [[IO PV] NO].
3-8 : destruct PV as [[[PF PV] PD] PO].
9 : destruct PV as [[[[PF FC] PV] PD] PO].
11-13 : destruct PV as [[[PF PV] PD] PO].
10,15,16,17: destruct PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].

1 : { unfold ptree_formula in FS; fold ptree_formula in FS.
      case (nat_ltb (ptree_deg (quantif_sub_ptree_fit P Q E F n dQ beta QP S)) n0) eqn:EQ;
      rewrite (quantif_ptree_formula_true _ _ _ _ _ _ _ _ _ FS);
      unfold ptree_ord; fold ptree_ord;
      apply (IHP PV). }

1 : { unfold ptree_formula in FS; fold ptree_formula in FS.
      case (ord_ltb (ptree_ord (quantif_sub_ptree_fit P Q E F n dQ beta QP S)) o) eqn:EQ;
      unfold ptree_ord; fold ptree_ord.
      - apply add_left_non_decr.
      - rewrite (quantif_ptree_formula_true _ _ _ _ _ _ _ _ _ FS).
        apply (ord_geb_trans _ (ord_add beta (ptree_ord P))).
        + apply ord_ltb_asymm.
          apply ord_lt_ltb.
          apply add_right_incr.
          apply IO.
        + apply (IHP PV). }

5 : rewrite quantif_ptree_formula_true;
    rewrite <- PO in IHP;
    try apply (IHP PV).

9,10 :  rewrite quantif_ptree_formula_true;
        rewrite <- P1O in IHP1;
        rewrite <- P2O in IHP2;
        pose (IHP1 P1V (lor_ind S (non_target f0))) as IHnP1;
        pose (IHP2 P2V (lor_ind (0) S)) as IHnP2;
        try rewrite (ord_succ_add_succ _ _ (ptree_ord_nf_hyp _ _ QO QV) (nf_nf_succ _ (nf_ord_max _ _ (ptree_ord_nf_hyp _ _ P1O P1V) (ptree_ord_nf_hyp _ _ P2O P2V))));
        try rewrite (ord_succ_add_succ _ _ (ptree_ord_nf_hyp _ _ QO QV) (nf_ord_max _ _ (ptree_ord_nf_hyp _ _ P1O P1V) (ptree_ord_nf_hyp _ _ P2O P2V)));
        try rewrite ord_max_add_comm;
        repeat apply ord_geb_succ;
        try apply (ord_max_geb_split _ _ _ _ IHnP1 (add_left_non_decr _ _));
        try apply (ord_max_geb_split _ _ _ _ (add_left_non_decr _ _) IHnP2).

5,9,10 :  try rewrite PF;
          try rewrite P1F;
          try rewrite P2F;
          unfold subst_ind_fit, ptree_formula in *; fold subst_ind_fit ptree_formula in *;
          try rewrite FS;
          try rewrite non_target_fit;
          reflexivity.

all : destruct S; inversion FS as [FS'];
      try destruct (and_bool_prop _ _ FS') as [FS1 FS2];
      unfold ptree_ord; fold ptree_ord.

13 : { destruct (PV czero) as [[[PF PcV] PD] PO].
       rewrite (ord_succ_add_succ _ _ (ptree_ord_nf_hyp _ _ QO QV) (ptree_ord_nf_hyp _ _ PO PcV)).
       apply ord_ltb_irrefl. }

10-12 : case (form_eqb f E) eqn:EQ1;
        case (nat_eqb n0 n) eqn:EQ2;
        unfold ptree_ord; fold ptree_ord;
        try apply add_left_non_decr.

10 :  { rewrite (ord_succ_add_succ _ _ (ptree_ord_nf_hyp _ _ QO QV) (ptree_ord_nf_hyp _ _ PO PV)).
        apply ord_geb_succ.  
        apply (ord_max_le_add _ _ (ptree_ord_nf_hyp _ _ QO QV) (ptree_ord_nf_hyp _ _ PO PV)). }

2,3,4,10 :  destruct S1; inversion FS' as [FS''];
            try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

4 : destruct S1_1; inversion FS'' as [FS'''];
    try destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

all : unfold ptree_ord; fold ptree_ord;
      try rewrite <- PO in IHP;
      try rewrite <- P1O in IHP1;
      try rewrite <- P2O in IHP2;
      repeat rewrite quantif_ptree_formula_true;
      try rewrite (ord_succ_add_succ _ _ (ptree_ord_nf_hyp _ _ QO QV) (ptree_ord_nf_hyp _ _ PO PV));
      try rewrite (ord_succ_add_succ _ _ (ptree_ord_nf_hyp _ _ QO QV) (nf_ord_max _ _ (ptree_ord_nf_hyp _ _ P1O P1V) (ptree_ord_nf_hyp _ _ P2O P2V)));
      try rewrite ord_max_add_comm;
      repeat apply ord_geb_succ;
      try apply ord_max_geb_split;
      try apply (IHP PV);
      try apply (IHP1 P1V);
      try apply (IHP2 P2V);
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold subst_ind_fit; fold subst_ind_fit;
      try rewrite non_target_fit;
      try rewrite FS;
      try rewrite FS'';
      try rewrite FS1;
      try rewrite FS2;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      try reflexivity.

1 : { rewrite (ord_max_self (ord_add beta o)).
      apply ord_max_geb_split.
      apply add_right_non_decr.
      apply (IHP PV). }
Qed.

Lemma quantif_valid :
    forall (P Q : ptree) (E F : formula) (n dQ : nat) (beta : ord) (QP : P_proves Q (lor F (univ n E)) dQ beta),
        valid P ->
            closed F = true ->
                Nat.max dQ (ptree_deg P) < (num_conn E + 2) ->
                    forall (S : subst_ind),
                        subst_ind_fit (ptree_formula P) S = true ->
                            valid (quantif_sub_ptree P Q E F n dQ beta QP S).
Proof.
intros P Q E F n dQ beta QP PV CF IE.
inversion QP as [[[QF QV] QD] QO].
pose (ptree_formula P) as A.
induction P; intros S FS;
unfold quantif_sub_ptree;
rewrite FS;
unfold quantif_sub_ptree_fit; fold quantif_sub_ptree_fit;
unfold ptree_formula in *; fold ptree_formula in *;
try apply PV.

1 : destruct PV as [ID PV].
2 : destruct PV as [[IO PV] NO].
3-8 : destruct PV as [[[PF PV] PD] PO].
9 : destruct PV as [[[[PF FC] PV] PD] PO].
11-13 : destruct PV as [[[PF PV] PD] PO].
10,15,16,17: destruct PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].

1 : { unfold ptree_formula in FS; fold ptree_formula in FS.
      unfold ptree_deg in IE.
      rewrite (quantif_ptree_formula_true _ _ _ _ _ _ _ _ _ FS).
      case (nat_ltb (ptree_deg (quantif_sub_ptree P Q E F n dQ beta QP S)) n0) eqn:EQ.
      split.
      1 : { apply nat_ltb_lt. apply EQ. } 
      all : refine (IHP PV _ _ FS);
            lia. }

1 : { unfold ptree_formula in FS; fold ptree_formula in FS.
      rewrite (quantif_ptree_formula_true _ _ _ _ _ _ _ _ _ FS).
      case (ord_ltb (ptree_ord (quantif_sub_ptree P Q E F n dQ beta QP S)) o) eqn:EQ;
      unfold ptree_ord; fold ptree_ord.
      split. split.
      3 : apply NO.
      1 : apply ord_ltb_lt. apply EQ.
      all : refine (IHP PV IE _ FS). } 

1-4,6-8,11-15 : destruct S; inversion FS as [FS'];
                try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

2-4,12 :  destruct S1; inversion FS' as [FS''];
          try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

4 : destruct S1_1; inversion FS'' as [FS'''];
    try destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

14 :  { repeat split;
        try rewrite weak_ord_formula;
        try rewrite weak_ord_deg;
        try apply weak_ord_valid;
        destruct (PV t) as [[[PF PcV] PD] PO];
        try apply (nf_add _ _ (ptree_ord_nf_hyp _ _ QO QV) (ptree_ord_nf_hyp _ _ PO PcV));
        rewrite quantif_ptree_formula_true;
        try rewrite PF;
        unfold subst_ind_fit;fold subst_ind_fit;
        try rewrite non_target_sub_fit;
        try rewrite FS2;
        try reflexivity;
        fold valid in *.
        - rewrite (quantif_ptree_formula _ _ _ _ _ _ _ _ PcV).
          rewrite PF.
          unfold quantif_sub_formula.
          rewrite (non_target_term_sub _ n0 (projT1 t)).
          rewrite non_target_sub_lor.
          reflexivity.
        
        - assert (Nat.max dQ (ptree_deg (p t)) < num_conn E + 2) as IE1.
          { unfold ptree_deg in IE. lia. }
          apply (X _ PcV IE1).
          rewrite PF.
          unfold subst_ind_fit; fold subst_ind_fit.
          rewrite non_target_sub_fit.
          apply FS2.
        
        - assert (Nat.max dQ (ptree_deg (p t)) < num_conn E + 2) as IE1.
          { unfold ptree_deg in IE. lia. }
          pose proof (quantif_ptree_deg _ _ _ _ _ _ _ QP PcV IE1 (lor_ind (non_target f) S2)) as IE2.
          lia.
        
        - unfold weak_ord_up.
          destruct (ord_semiconnex_bool (ptree_ord (quantif_sub_ptree (p t) Q E F n dQ beta QP (lor_ind (non_target f) S2))) (ord_add beta o)) as [OLT | [OGT | OEQ]].

          + rewrite OLT.
            unfold ptree_ord.
            reflexivity.
        
          + rewrite PO in OGT.
            rewrite quantif_ptree_ord in OGT.
            inversion OGT.
            apply PcV.
        
          + apply ord_eqb_eq in OEQ.
            destruct OEQ.
            rewrite ord_ltb_irrefl.
            reflexivity. }

5,6,12,13 : case (form_eqb f E) eqn:EQ1;
            case (nat_eqb n0 n) eqn:EQ2.

all : repeat rewrite quantif_ptree_formula_true;
      try apply form_eqb_eq in EQ1;
      try apply nat_eqb_eq in EQ2;
      try destruct EQ1;
      try destruct EQ2;
      repeat split;
      try rewrite (w_rule_ptree_formula _ _ _ _ QV);
      try rewrite (w_rule_ptree_ord _ _ _ _ QV);
      try rewrite (quantif_ptree_formula _ _ _ _ _ _ _ _ PV);
      try rewrite (quantif_ptree_formula _ _ _ _ _ _ _ _ P1V);
      try rewrite (quantif_ptree_formula _ _ _ _ _ _ _ _ P2V);
      try rewrite QF;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold w_rule_sub_formula;
      unfold quantif_sub_formula;
      try apply non_target_sub_lor;
      repeat rewrite formula_sub_ind_lor;
      try rewrite non_target_sub;
      try apply (w_rule_valid _ _ _ _ QV);
      try rewrite (quantif_ptree_formula _ _ _ _ _ _ _ _ PV);  
      try apply IHP;
      try apply IHP1;
      try apply IHP2;
      try apply PV;
      try apply P1V;
      try apply P2V;
      try unfold ptree_deg in IE;
      try lia;
      try rewrite QF;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold subst_ind_fit; 
      fold subst_ind_fit;
      try rewrite non_target_fit;
      try rewrite FS;
      try rewrite FS1;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      try rewrite FS2;
      try apply QO;
      try apply PO;
      try apply P1O;
      try apply P2O;
      unfold formula_sub_ind, formula_sub_ind_fit, subst_ind_fit;
      fold formula_sub_ind_fit subst_ind_fit;
      try rewrite form_eqb_refl;
      try rewrite FS1;
      try reflexivity.

1 : { rewrite <- (sub_fit_true _ _ _ _ FS1).
      apply formula_sub_ind_closed.
      apply FC.
      intros CnuE.
      apply CF. }
Qed.
