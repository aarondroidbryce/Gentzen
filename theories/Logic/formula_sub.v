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

Fixpoint formula_sub_ptree_fit
  (P : ptree) (E F : formula) (S : subst_ind) : ptree :=
match P, S with
| deg_up d P', _ => deg_up d (formula_sub_ptree_fit P' E F S)

| ord_up alpha P', _ => ord_up alpha (formula_sub_ptree_fit P' E F S)

| node A, _ => node (formula_sub_ind_fit A E F S)

| exchange_ab A B d alpha P', lor_ind S_B S_A =>
    exchange_ab
      (formula_sub_ind_fit A E F S_A)
      (formula_sub_ind_fit B E F S_B)
      d alpha
      (formula_sub_ptree_fit P' E F (lor_ind S_A S_B))

| exchange_cab C A B d alpha P', lor_ind (lor_ind S_C S_B) S_A =>
    exchange_cab
      (formula_sub_ind_fit C E F S_C)
      (formula_sub_ind_fit A E F S_A)
      (formula_sub_ind_fit B E F S_B)
      d alpha
      (formula_sub_ptree_fit P' E F (lor_ind (lor_ind S_C S_A) S_B))

| exchange_abd A B D d alpha P', lor_ind (lor_ind S_B S_A) S_D =>
    exchange_abd
      (formula_sub_ind_fit A E F S_A)
      (formula_sub_ind_fit B E F S_B)
      (formula_sub_ind_fit D E F S_D)
      d alpha
      (formula_sub_ptree_fit P' E F (lor_ind (lor_ind S_A S_B) S_D))

| exchange_cabd C A B D d alpha P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D =>
    exchange_cabd
      (formula_sub_ind_fit C E F S_C)
      (formula_sub_ind_fit A E F S_A)
      (formula_sub_ind_fit B E F S_B)
      (formula_sub_ind_fit D E F S_D)
      d alpha
      (formula_sub_ptree_fit P' E F (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D))

| contraction_a A d alpha P', _ =>
    contraction_a
      (formula_sub_ind_fit A E F S)
      d alpha
      (formula_sub_ptree_fit P' E F (lor_ind S S))

| contraction_ad A D d alpha P', lor_ind S_A S_D =>
    contraction_ad
      (formula_sub_ind_fit A E F S_A)
      (formula_sub_ind_fit D E F S_D)
      d alpha
      (formula_sub_ptree_fit P' E F (lor_ind (lor_ind S_A S_A) S_D))

| weakening_ad A D d alpha P', lor_ind S_A S_D =>
    weakening_ad
      (formula_sub_ind_fit A E F S_A)
      (formula_sub_ind_fit D E F S_D)
      d alpha
      (formula_sub_ptree_fit P' E F S_D)

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, _ => P

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_AB S_D =>
    demorgan_abd
      A B
      (formula_sub_ind_fit D E F S_D)
      d1 d2 alpha1 alpha2
      (formula_sub_ptree_fit P1 E F (lor_ind (0) S_D))
      (formula_sub_ptree_fit P2 E F (lor_ind (0) S_D))

| negation_a A d alpha P', _ => P

| negation_ad A D d alpha P', lor_ind S_A S_D =>
    negation_ad
      A
      (formula_sub_ind_fit D E F S_D)
      d alpha
      (formula_sub_ptree_fit P' E F (lor_ind (non_target A) S_D))

| quantification_a A n t d alpha P', _ => P

| quantification_ad A D n t d alpha P', lor_ind S_A S_D =>
    quantification_ad
      A
      (formula_sub_ind_fit D E F S_D)
      n t d alpha
      (formula_sub_ptree_fit P' E F (lor_ind (0) S_D))

| w_rule_a A n d alpha g, _ => P

| w_rule_ad A D n d alpha g, lor_ind S_A S_D =>
    w_rule_ad
      A
      (formula_sub_ind_fit D E F S_D)
      n d alpha
      (fun (t : c_term) =>
          formula_sub_ptree_fit (g t) E F (lor_ind (non_target A) S_D))

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ca
      (formula_sub_ind_fit C E F S)
      A d1 d2 alpha1 alpha2
      (formula_sub_ptree_fit P1 E F (lor_ind S (non_target A)))
      P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ad
      A
      (formula_sub_ind_fit D E F S)
      d1 d2 alpha1 alpha2
      P1
      (formula_sub_ptree_fit P2 E F (lor_ind (0) S))

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_D =>
    cut_cad
      (formula_sub_ind_fit C E F S_C)
      A
      (formula_sub_ind_fit D E F S_D)
      d1 d2 alpha1 alpha2
      (formula_sub_ptree_fit P1 E F (lor_ind S_C (non_target A)))
      (formula_sub_ptree_fit P2 E F (lor_ind (0) S_D))

| _, _ => P
end.

Definition formula_sub_ptree
  (P : ptree) (E F : formula) (S : subst_ind) : ptree :=
match subst_ind_fit (ptree_formula P) S with
| false => P
| true => formula_sub_ptree_fit P E F S
end.

Lemma formula_sub_ptree_formula_true :
    forall (P : ptree) (E F : formula) (S : subst_ind),
        subst_ind_fit (ptree_formula P) S = true ->
            formula_sub_ptree_fit P E F S = formula_sub_ptree P E F S.
Proof.
intros P E F S FS.
unfold formula_sub_ptree.
rewrite FS.
reflexivity.
Qed.

Lemma formula_sub_ptree_fit_false :
    forall (P : ptree) (E F : formula) (S : subst_ind),
        subst_ind_fit (ptree_formula P) S = false -> 
            formula_sub_ptree P E F S = P.
Proof.
intros P E F S FS.
unfold formula_sub_ptree.
rewrite FS.
reflexivity.
Qed.

Lemma formula_sub_ind_fit_closed :
    forall (A B C : formula),
        closed A = true ->
            (closed B = true -> closed C = true) ->
                forall (S : subst_ind),
                    subst_ind_fit A S = true ->
                        closed (formula_sub_ind_fit A B C S) = true.
Proof.
intros A B C CA CBC S FS.
destruct (closed (formula_sub_ind A B C S)) eqn:CFC.
- rewrite (sub_fit_true _ _ _ _ FS) in CFC.
  apply CFC.
- rewrite (formula_sub_ind_closed _ _ _ CA CBC) in CFC.
  inversion CFC.
Qed.

Lemma formula_sub_ptree_formula_atom' :
    forall (P : ptree) (a : atomic_formula) (F : formula),
        valid P ->
            forall (S : subst_ind),
                subst_ind_fit (ptree_formula P) S = true ->
                    ptree_formula (formula_sub_ptree P (atom a) F S) =
                        formula_sub_ind (ptree_formula P) (atom a) F S.
Proof.
intros P a F PV.
induction P; intros S FS;
unfold formula_sub_ptree;
rewrite FS;
unfold formula_sub_ptree_fit;
fold formula_sub_ptree_fit.

1 : destruct PV as [ID PV].

2 : destruct PV as [[IO PV] NO].

1,2 : unfold ptree_formula in *; fold ptree_formula in *;
      rewrite (formula_sub_ptree_formula_true _ _ _ _ FS);
      apply (IHP PV _ FS).

1 : { unfold ptree_formula, formula_sub_ind in *.
      rewrite FS.
      reflexivity. }

1-4,6-15,18 : destruct S; inversion FS as [FS'];
              try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

2-4,9,12,15,18 : destruct S1; inversion FS' as [FS''];
      try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

4 : destruct S1_1; inversion FS'' as [FS'''];
    try destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

all : unfold ptree_formula in *; fold ptree_formula in *;
      unfold formula_sub_ind, subst_ind_fit; fold subst_ind_fit;
      try rewrite FS;
      try rewrite FS1;
      try rewrite FS2;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      try reflexivity.
Qed.

Lemma formula_sub_ptree_formula_atom :
    forall (P : ptree) (a : atomic_formula) (F : formula),
        valid P ->
            forall (S : subst_ind),
                ptree_formula (formula_sub_ptree P (atom a) F S) =
                    formula_sub_ind (ptree_formula P) (atom a) F S.
Proof.
intros P a F PV S.
destruct (subst_ind_fit (ptree_formula P) S) eqn:FS.
- apply (formula_sub_ptree_formula_atom' _ _ _ PV _ FS).
- unfold formula_sub_ptree, formula_sub_ind.
  rewrite FS.
  reflexivity.
Qed.

Lemma formula_sub_ptree_deg_atom :
    forall (P : ptree) (a : atomic_formula) (F : formula),
        valid P ->
            forall (S : subst_ind),
                ptree_deg (formula_sub_ptree P (atom a) F S) = ptree_deg P.
Proof.
intros P a F PV.
pose (ptree_formula P) as A.
induction P; intros S;
case (subst_ind_fit A S) eqn:FS;
unfold formula_sub_ptree;
unfold A in FS;
try rewrite FS;
unfold formula_sub_ptree_fit;
fold formula_sub_ptree_fit;
try reflexivity.

1 : destruct PV as [[IO PV] NO].
    unfold ptree_formula in *; fold ptree_formula in *.
    rewrite (formula_sub_ptree_formula_true _ _ _ _ FS).
    apply (IHP PV).

all : destruct S; inversion FS as [FS'];
      try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

2-4,7-11 : destruct S1; inversion FS' as [FS''];
      try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

4 : destruct S1_1; inversion FS'' as [FS'''];
    try destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

all : unfold ptree_deg; fold ptree_deg;
      reflexivity.
Qed.

Lemma formula_sub_ptree_ord_atom :
    forall (P : ptree) (a : atomic_formula) (F : formula),
        valid P ->
            forall (S : subst_ind),
                ptree_ord (formula_sub_ptree P (atom a) F S) = ptree_ord P.
Proof.
intros P a F PV.
pose (ptree_formula P) as A.
induction P; intros S;
case (subst_ind_fit A S) eqn:FS;
unfold formula_sub_ptree;
unfold A in FS;
try rewrite FS;
unfold formula_sub_ptree_fit;
fold formula_sub_ptree_fit;
try reflexivity.

1 : destruct PV as [ID PV].
    unfold ptree_formula in *; fold ptree_formula in *.
    rewrite (formula_sub_ptree_formula_true _ _ _ _ FS).
    apply (IHP PV).

all : destruct S; inversion FS as [FS'];
      try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

2-4,7-11 : destruct S1; inversion FS' as [FS''];
      try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

4 : destruct S1_1; inversion FS'' as [FS'''];
    try destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

all : unfold ptree_deg; fold ptree_deg;
      reflexivity.
Qed.

Lemma formula_sub_valid_atom :
    forall (P : ptree) (a : atomic_formula) (F : formula),
        valid P ->
            correct_a a = false ->
                closed F =true ->
                    forall (S : subst_ind),
                        subst_ind_fit (ptree_formula P) S = true ->
                            valid (formula_sub_ptree P (atom a) F S).
Proof.
intros P a F PV Aa CF.
induction P; intros S FS;
unfold formula_sub_ptree;
rewrite FS;
unfold formula_sub_ptree_fit;
fold formula_sub_ptree_fit.

1 : destruct PV as [ID PV].
2 : destruct PV as [[IO PV] NO].
4-9 : destruct PV as [[[PF PV] PD] PO].
10 : destruct PV as [[[[PF FC] PV] PD] PO].
11,12 : destruct PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].
13-16 : destruct PV as [[[PF PV] PD] PO].
19-21 : destruct PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].

4-7,9,10,12,14,16,18,21 : destruct S; inversion FS as [FS'];
                          try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

5-7,9-13 :  destruct S1; inversion FS' as [FS''];
            try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

7 : destruct S1_1; inversion FS'' as [FS'''];
    try destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

3 : { unfold valid in *.
      destruct f.
      3,4 : inversion PV.
      2 : unfold formula_sub_ind_fit, form_eqb;
          apply PV.
      1 : destruct S;
          unfold formula_sub_ind_fit, form_eqb;
          fold formula_sub_ind_fit;
          case (atom_eqb a0 a) eqn:EQ;
          try apply PV.
          apply atom_beq_eq in EQ.
          destruct EQ.
          unfold PA_omega_axiom in PV.
          rewrite PV in Aa.
          inversion Aa. }

16,17 : repeat split;
        destruct (PV t) as [[[PF PcV] PD] PO];
        rewrite formula_sub_ptree_formula_true;
        try rewrite PF;
        try rewrite formula_sub_ptree_deg_atom;
        try apply PD;
        try rewrite formula_sub_ptree_ord_atom;
        try apply PO;
        try apply X;
        try rewrite formula_sub_ptree_formula_atom;
        try rewrite PF;
        try apply PV;
        try rewrite formula_sub_ind_lor;
        try rewrite (non_target_term_sub _ n (projT1 t));
        try rewrite non_target_sub;
        unfold formula_sub_ind;
        unfold subst_ind_fit; fold subst_ind_fit;
        try rewrite FS;
        try rewrite FS1;
        try rewrite FS2;
        try rewrite non_target_fit;
        reflexivity.

all : repeat rewrite formula_sub_ptree_formula_true;
      unfold ptree_formula in FS; fold ptree_formula in FS;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      repeat split;
      try rewrite formula_sub_ptree_deg_atom;
      try apply PD;
      try apply P1D;
      try apply P2D;
      try rewrite formula_sub_ptree_ord_atom;
      try apply PO;
      try apply P1O;
      try apply P2O;
      try apply IHP;
      try apply IHP1;
      try apply IHP2;
      try rewrite formula_sub_ptree_formula_atom;
      try apply PV;
      try apply P1V;
      try apply P2V;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      try rewrite formula_sub_ind_lor;
      try rewrite non_target_sub;
      unfold formula_sub_ind;
      unfold subst_ind_fit; fold subst_ind_fit;
      try rewrite FS;
      try rewrite FS1;
      try rewrite FS2;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      try rewrite non_target_fit;
      unfold "&&";
      try reflexivity;
      try apply ID;
      try apply IO;
      try apply NO.

all : refine (formula_sub_ind_fit_closed _ _ _ FC _ _ FS1);
      intros Caa;
      apply CF.
Qed.

Lemma formula_sub_ptree_formula_neg' :
    forall (P : ptree) (a : atomic_formula) (F : formula),
        valid P ->
            forall (S : subst_ind),
                subst_ind_fit (ptree_formula P) S = true ->
                    ptree_formula (formula_sub_ptree P (neg (atom a)) F S) =
                        formula_sub_ind (ptree_formula P) (neg (atom a)) F S.
Proof.
intros P a F PV.
induction P; intros S FS;
unfold formula_sub_ptree;
rewrite FS;
unfold formula_sub_ptree_fit;
fold formula_sub_ptree_fit.

1 : destruct PV as [ID PV].

2 : destruct PV as [[IO PV] NO].

1,2 : unfold ptree_formula in *; fold ptree_formula in *;
      rewrite (formula_sub_ptree_formula_true _ _ _ _ FS);
      apply (IHP PV _ FS).

1 : { unfold ptree_formula, formula_sub_ind in *.
      rewrite FS.
      reflexivity. }

1-4,6-15,18 : destruct S; inversion FS as [FS'];
              try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

2-4,9,12,15,18 : destruct S1; inversion FS' as [FS''];
      try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

4 : destruct S1_1; inversion FS'' as [FS'''];
    try destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

all : unfold ptree_formula in *; fold ptree_formula in *;
      unfold formula_sub_ind, subst_ind_fit; fold subst_ind_fit;
      try rewrite FS;
      try rewrite FS1;
      try rewrite FS2;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      try reflexivity.
Qed.

Lemma formula_sub_ptree_formula_neg :
    forall (P : ptree) (a : atomic_formula) (F : formula),
        valid P ->
            forall (S : subst_ind),
                ptree_formula (formula_sub_ptree P (neg (atom a)) F S) =
                    formula_sub_ind (ptree_formula P) (neg (atom a)) F S.
Proof.
intros P a F PV S.
destruct (subst_ind_fit (ptree_formula P) S) eqn:FS.
- apply (formula_sub_ptree_formula_neg' _ _ _ PV _ FS).
- unfold formula_sub_ptree,formula_sub_ind.
  rewrite FS.
  reflexivity.
Qed.

Lemma formula_sub_ptree_deg_neg :
    forall (P : ptree) (a : atomic_formula) (F : formula),
        valid P ->
            forall (S : subst_ind),
                ptree_deg (formula_sub_ptree P (neg (atom a)) F S) = ptree_deg P.
Proof.
intros P a F PV.
pose (ptree_formula P) as A.
induction P; intros S;
case (subst_ind_fit A S) eqn:FS;
unfold formula_sub_ptree;
unfold A in FS;
try rewrite FS;
unfold formula_sub_ptree_fit;
fold formula_sub_ptree_fit;
try reflexivity.

1 : destruct PV as [[IO PV] NO].
    unfold ptree_formula in *; fold ptree_formula in *.
    rewrite (formula_sub_ptree_formula_true _ _ _ _ FS).
    apply (IHP PV).

all : destruct S; inversion FS as [FS'];
      try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

2-4,7-11 : destruct S1; inversion FS' as [FS''];
      try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

4 : destruct S1_1; inversion FS'' as [FS'''];
    try destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

all : unfold ptree_deg; fold ptree_deg;
      reflexivity.
Qed.

Lemma formula_sub_ptree_ord_neg :
    forall (P : ptree) (a : atomic_formula) (F : formula),
        valid P ->
            forall (S : subst_ind),
                ptree_ord (formula_sub_ptree P (neg (atom a)) F S) = ptree_ord P.
Proof.
intros P a F PV.
pose (ptree_formula P) as A.
induction P; intros S;
case (subst_ind_fit A S) eqn:FS;
unfold formula_sub_ptree;
unfold A in FS;
try rewrite FS;
unfold formula_sub_ptree_fit;
fold formula_sub_ptree_fit;
try reflexivity.

1 : destruct PV as [ID PV].
    unfold ptree_formula in *; fold ptree_formula in *.
    rewrite (formula_sub_ptree_formula_true _ _ _ _ FS).
    apply (IHP PV).

all : destruct S; inversion FS as [FS'];
      try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

2-4,7-11 : destruct S1; inversion FS' as [FS''];
      try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

4 : destruct S1_1; inversion FS'' as [FS'''];
    try destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

all : unfold ptree_deg; fold ptree_deg;
      reflexivity.
Qed.

Lemma formula_sub_valid_neg :
    forall (P : ptree) (a : atomic_formula) (F : formula),
      valid P ->
          correct_a a = true ->
              closed F = true ->
                  forall (S : subst_ind),
                      subst_ind_fit (ptree_formula P) S = true ->
                          valid (formula_sub_ptree P (neg (atom a)) F S).
Proof.
intros P a F PV Aa CF.
induction P; intros S FS;
unfold formula_sub_ptree;
rewrite FS;
unfold formula_sub_ptree_fit;
fold formula_sub_ptree_fit.

1 : destruct PV as [ID PV].
2 : destruct PV as [[IO PV] NO].
4-9 : destruct PV as [[[PF PV] PD] PO].
10 : destruct PV as [[[[PF FC] PV] PD] PO].
11,12 : destruct PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].
13-16 : destruct PV as [[[PF PV] PD] PO].
19-21 : destruct PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].

4-7,9,10,12,14,16,18,21 : destruct S; inversion FS as [FS'];
                          try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

5-7,9-13 :  destruct S1; inversion FS' as [FS''];
            try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

7 : destruct S1_1; inversion FS'' as [FS'''];
    try destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

3 : { unfold valid in *.
      destruct f.
      3,4 : inversion PV.
      1 : unfold formula_sub_ind_fit, form_eqb;
          apply PV.
      1 : destruct S;
          unfold formula_sub_ind_fit, form_eqb;
          fold formula_sub_ind_fit form_eqb;
          case (form_eqb f (atom a)) eqn:EQ;
          try apply PV.
          apply form_eqb_eq in EQ.
          rewrite EQ in *.
          unfold PA_omega_axiom in PV.
          pose proof (correct_correctness _ Aa) as Ra.
          rewrite (incorrect_correctness _ PV) in Ra.
          inversion Ra. }

16,17 : repeat split;
        destruct (PV t) as [[[PF PcV] PD] PO];
        rewrite formula_sub_ptree_formula_true;
        try rewrite PF;
        try rewrite formula_sub_ptree_deg_neg;
        try apply PD;
        try rewrite formula_sub_ptree_ord_neg;
        try apply PO;
        try apply X;
        try rewrite formula_sub_ptree_formula_neg;
        try rewrite PF;
        try apply PV;
        try rewrite formula_sub_ind_lor;
        try rewrite (non_target_term_sub _ n (projT1 t));
        try rewrite non_target_sub;
        unfold formula_sub_ind;
        unfold subst_ind_fit; fold subst_ind_fit;
        try rewrite FS;
        try rewrite FS1;
        try rewrite FS2;
        try rewrite non_target_fit;
        try reflexivity.

all : repeat rewrite formula_sub_ptree_formula_true;
      unfold ptree_formula in FS; fold ptree_formula in FS;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      repeat split;
      try rewrite formula_sub_ptree_deg_neg;
      try apply PD;
      try apply P1D;
      try apply P2D;
      try rewrite formula_sub_ptree_ord_neg;
      try apply PO;
      try apply P1O;
      try apply P2O;
      try apply IHP;
      try apply IHP1;
      try apply IHP2;
      try rewrite formula_sub_ptree_formula_neg;
      try apply PV;
      try apply P1V;
      try apply P2V;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      try rewrite formula_sub_ind_lor;
      try rewrite non_target_sub;
      unfold formula_sub_ind;
      unfold subst_ind_fit; fold subst_ind_fit;
      try rewrite FS;
      try rewrite FS1;
      try rewrite FS2;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      try rewrite non_target_fit;
      unfold "&&";
      try reflexivity;
      try apply ID;
      try apply IO;
      try apply NO.

all : refine (formula_sub_ind_fit_closed _ _ _ FC _ _ FS1);
      intros Caa;
      apply CF.
Qed.



(* 
(* *)
Lemma neg_sub_valid :
  forall (D : formula) (a : atomic_formula) (d : nat) (alpha : ord),
  PA_omega_axiom (neg (atom a)) = false ->
  provable (lor (neg (atom a)) D) d alpha ->
  provable (lor D D) d alpha.
Proof.
unfold provable. intros D a d alpha Ha H. destruct H as [P [[[HP1 HP2] HP3] HP4]].
exists (formula_sub_ptree P (neg (atom a)) D (lor_ind (1) (non_target D))).
unfold P_proves. repeat split.
- rewrite formula_sub_ptree_formula_neg; auto. rewrite HP1.
  unfold formula_sub_ind. simpl. rewrite non_target_fit. simpl.
  rewrite eq_atom_refl. rewrite non_target_sub'. auto.
- apply formula_sub_valid_neg; auto.
  + pose proof (provable_closed' P (lor (neg (atom a)) D) HP2 HP1).
    simpl in H. destruct (and_bool_prop _ _ H). auto.
  + rewrite HP1. simpl. rewrite non_target_fit. auto.
- rewrite formula_sub_ptree_deg_neg; auto.
- rewrite formula_sub_ptree_ord_neg; auto.
Qed.
*)
