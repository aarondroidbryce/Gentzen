Add LoadPath "theories/Casteran" as Ordering.
Add LoadPath "theories/Maths" as Maths_Facts.
Add LoadPath "theories/Logic" as Systems.

From Maths_Facts Require Import naturals.
From Maths_Facts Require Import ordinals.
From Maths_Facts Require Import lists.

From Systems Require Import definitions.
From Systems Require Import fol.
From Systems Require Import PA_omega.
From Systems Require Import proof_trees.
From Systems Require Import substitute.

(* Defining formula substitution for multiple formulas *)
(* *)
Fixpoint eq_length_list {X Y : Type} (lX : list X) (lY : list Y) : bool :=
match lX, lY with
| [], [] => true
| x :: lX', y :: lY' => eq_length_list lX' lY'
| _, _ => false
end.

Fixpoint formula_sub_ind_list_len
  (A : formula) (l1 l2 : list formula) (ls : list subst_ind) : formula :=
match l1, l2, ls with
| E :: l1', F :: l2', s :: ls' =>
    formula_sub_ind_list_len (formula_sub_ind A E F s) l1' l2' ls'
| _, _, _ => A
end.

Definition formula_sub_ind_list
  (A : formula) (l1 l2 : list formula) (ls : list subst_ind) : formula :=
match eq_length_list l1 l2, eq_length_list l1 ls with
| true, true => formula_sub_ind_list_len A l1 l2 ls
| _, _ => A
end.


(* Defining term substitution on multiple formulas *)
(* *)
Fixpoint sub_list (l : list formula) (n : nat) (t : term) : list formula :=
match l with
| [] => []
| E :: l' => (substitution E n t) :: sub_list l' n t
end.

Definition term_sub_ind_list_len
  (A : formula) (l : list formula) (ls : list subst_ind)
  (n : nat) (s t : term) : formula :=
formula_sub_ind_list_len A (sub_list l n s) (sub_list l n t) ls.

Definition term_sub_ind_list
  (A : formula) (l : list formula) (ls : list subst_ind)
  (n : nat) (s t : term) : formula :=
match eq_length_list l ls with
| true => term_sub_ind_list_len A l ls n s t
| _ => A
end.

Lemma formula_sub_ind_list_single :
  forall (A : formula) (E F : formula) (S : subst_ind),
  formula_sub_ind_list A [E] [F] [S] = formula_sub_ind A E F S.
Proof. intros. unfold formula_sub_ind_list. simpl. auto. Qed.

(*
(* Defining term substitution on proof trees *)
(* *)
Program Fixpoint term_sub_ptree_fit_list
  (P : ptree) (l : list formula) (ls : list subst_ind) (n : nat) (s t : term)
  : ptree :=
match P, S with
| deg_up d P', _ => deg_up d (term_sub_ptree_fit_list P' l ls n s t)

| ord_up alpha P', _ => ord_up alpha (term_sub_ptree_fit_list P' l ls n s t)

| node A, _ => node (term_sub_ind_fit A l ls n s t)

| exchange_ab A B d alpha P', lor_ind S_B S_A =>
    exchange_ab
      (term_sub_ind_fit A E n s t S_A)
      (term_sub_ind_fit B E n s t S_B)
      d alpha
      (term_sub_ptree_fit P' l ls n s t (lor_ind S_A S_B))

| exchange_cab C A B d alpha P', lor_ind (lor_ind S_C S_B) S_A =>
    exchange_cab
      (term_sub_ind_fit C E n s t S_C)
      (term_sub_ind_fit A E n s t S_A)
      (term_sub_ind_fit B E n s t S_B)
      d alpha
      (term_sub_ptree_fit P' E n s t (lor_ind (lor_ind S_C S_A) S_B))

| exchange_abd A B D d alpha P', lor_ind (lor_ind S_B S_A) S_D =>
    exchange_abd
      (term_sub_ind_fit A E n s t S_A)
      (term_sub_ind_fit B E n s t S_B)
      (term_sub_ind_fit D E n s t S_D)
      d alpha
      (term_sub_ptree_fit P' E n s t (lor_ind (lor_ind S_A S_B) S_D))

| exchange_cabd C A B D d alpha P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D =>
    exchange_cabd
      (term_sub_ind_fit C E n s t S_C)
      (term_sub_ind_fit A E n s t S_A)
      (term_sub_ind_fit B E n s t S_B)
      (term_sub_ind_fit D E n s t S_D)
      d alpha
      (term_sub_ptree_fit P' E n s t (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D))

| contraction_a A d alpha P', _ =>
    contraction_a
      (term_sub_ind_fit A E n s t S)
      d alpha
      (term_sub_ptree_fit P' E n s t (lor_ind S S))

| contraction_ad A D d alpha P', lor_ind S_A S_D =>
    contraction_ad
      (term_sub_ind_fit A E n s t S_A)
      (term_sub_ind_fit D E n s t S_D)
      d alpha
      (term_sub_ptree_fit P' E n s t (lor_ind (lor_ind S_A S_A) S_D))

| weakening_ad A D d alpha P', lor_ind S_A S_D =>
    weakening_ad
      (term_sub_ind_fit A E n s t S_A)
      (term_sub_ind_fit D E n s t S_D)
      d alpha
      (term_sub_ptree_fit P' E n s t S_D)

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, (1) =>
    (match eq_f (neg (lor A B)) (substitution E n s) with
    | true =>
        demorgan_ab
          (substitution A n t)
          (substitution B n t)
          d1 d2 alpha1 alpha2
          (term_sub_ptree_fit P1 A n s t (target A))
          (term_sub_ptree_fit P2 B n s t (target B))
    | false => P
    end)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, lor_ind (1) S_D =>
    (match eq_f (neg (lor A B)) (substitution E n s) with
    | true =>
        demorgan_abd
          (substitution A n t)
          (substitution B n t)
          (term_sub_ind_fit D E n s t S_D)
          d1 d2 alpha1 alpha2
          (term_sub_ptree_fit
            (term_sub_ptree_fit P1 E n s t (lor_ind (0) S_D))
            A n s t (lor_ind (1) (non_target D)))
          (term_sub_ptree_fit
            (term_sub_ptree_fit P2 E n s t (lor_ind (0) S_D))
            B n s t (lor_ind (1) (non_target D)))
    | false =>
        demorgan_abd
          A B
          (term_sub_ind_fit D E n s t S_D)
          d1 d2 alpha1 alpha2
          (term_sub_ptree_fit P1 E n s t (lor_ind (0) S_D))
          (term_sub_ptree_fit P2 E n s t (lor_ind (0) S_D))
    end)

| _, _ => P
end.

(*


| negation_a A d alpha P', (1) =>
    (match eq_f (neg (neg A)) (substitution E n s) with
    | true =>
        negation_a
          (substitution A n t)
          d alpha
          (term_sub_ptree_fit P' A n s t (1))
    | false => P
    end)

| negation_ad A D d alpha P', lor_ind (1) S_D =>
    (match eq_f (neg (neg A)) (substitution E n s) with
    | true =>
        negation_ad
          (substitution A n t)
          (term_sub_ind_fit D E n s t S_D)
          d alpha
          (term_sub_ptree_fit
            (term_sub_ptree_fit P' E n s t (lor_ind (0) S_D))
            A n s t (lor_ind (1) (non_target D)))
    | false =>
        negation_ad
          A
          (term_sub_ind_fit D E n s t S_D)
          d alpha
          (term_sub_ptree_fit P E n s t (lor_ind (0) S_D))
    end)



| quantification_a A k t d alpha P', (1) =>
    quantification_a
      (substitution A n t)
      d alpha
      (term_sub_ptree_fit P' E n s t S)

| quantification_ad A D k t d alpha P', lor_ind (1) S_D =>
    quantification_ad
      (substitution A n t)
      (term_sub_ind_fit D E n s t S_D)
      d alpha
      (term_sub_ptree_fit P' E n s t S)

| w_rule_a A k d alpha g, _ =>
    w_rule_a
      (substitution A n t)
      n d alpha
      (fun (p : nat) =>
        term_sub_ptree_fit (g p) E n s t S)

| w_rule_ad A D k d alpha g, lor_ind S_A S_D =>
    w_rule_a
      (substitution A n t)
      (term_sub_ind_fit D E F S_D)
      n d alpha
      (fun (p : nat) =>
        term_sub_ptree_fit (g p) E n s t S)

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ca
      (term_sub_ind_fit C E F S)
      A d1 d2 alpha1 alpha2
      (term_sub_ptree_fit P1 E F (lor_ind S (non_target A)))
      P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ad
      A
      (term_sub_ind_fit D E F S)
      d1 d2 alpha1 alpha2
      P1
      (term_sub_ptree_fit P2 E F (lor_ind (0) S))

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_D =>
    cut_cad
      (term_sub_ind_fit C E F S_C)
      A
      (term_sub_ind_fit D E F S_D)
      d1 d2 alpha1 alpha2
      (term_sub_ptree_fit P1 E F (lor_ind S_C (non_target A)))
      (term_sub_ptree_fit P2 E F (lor_ind (0) S_D))

| _, _ => P
end.

*)




(* Defining term substitution on proof trees *)
(* *)
Program Fixpoint term_sub_ptree_fit
  (P : ptree) (E : formula) (n : nat) (s t : term) (S : subst_ind) : ptree :=
match P, S with
| deg_up d P', _ => deg_up d (term_sub_ptree_fit P' E n s t S)

| ord_up alpha P', _ => ord_up alpha (term_sub_ptree_fit P' E n s t S)

| node A, _ => node (term_sub_ind_fit A E n s t S)

| exchange_ab A B d alpha P', lor_ind S_B S_A =>
    exchange_ab
      (term_sub_ind_fit A E n s t S_A)
      (term_sub_ind_fit B E n s t S_B)
      d alpha
      (term_sub_ptree_fit P' E n s t (lor_ind S_A S_B))

| exchange_cab C A B d alpha P', lor_ind (lor_ind S_C S_B) S_A =>
    exchange_cab
      (term_sub_ind_fit C E n s t S_C)
      (term_sub_ind_fit A E n s t S_A)
      (term_sub_ind_fit B E n s t S_B)
      d alpha
      (term_sub_ptree_fit P' E n s t (lor_ind (lor_ind S_C S_A) S_B))

| exchange_abd A B D d alpha P', lor_ind (lor_ind S_B S_A) S_D =>
    exchange_abd
      (term_sub_ind_fit A E n s t S_A)
      (term_sub_ind_fit B E n s t S_B)
      (term_sub_ind_fit D E n s t S_D)
      d alpha
      (term_sub_ptree_fit P' E n s t (lor_ind (lor_ind S_A S_B) S_D))

| exchange_cabd C A B D d alpha P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D =>
    exchange_cabd
      (term_sub_ind_fit C E n s t S_C)
      (term_sub_ind_fit A E n s t S_A)
      (term_sub_ind_fit B E n s t S_B)
      (term_sub_ind_fit D E n s t S_D)
      d alpha
      (term_sub_ptree_fit P' E n s t (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D))

| contraction_a A d alpha P', _ =>
    contraction_a
      (term_sub_ind_fit A E n s t S)
      d alpha
      (term_sub_ptree_fit P' E n s t (lor_ind S S))

| contraction_ad A D d alpha P', lor_ind S_A S_D =>
    contraction_ad
      (term_sub_ind_fit A E n s t S_A)
      (term_sub_ind_fit D E n s t S_D)
      d alpha
      (term_sub_ptree_fit P' E n s t (lor_ind (lor_ind S_A S_A) S_D))

| weakening_ad A D d alpha P', lor_ind S_A S_D =>
    weakening_ad
      (term_sub_ind_fit A E n s t S_A)
      (term_sub_ind_fit D E n s t S_D)
      d alpha
      (term_sub_ptree_fit P' E n s t S_D)

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, (1) =>
    (match eq_f (neg (lor A B)) (substitution E n s) with
    | true =>
        demorgan_ab
          (substitution A n t)
          (substitution B n t)
          d1 d2 alpha1 alpha2
          (term_sub_ptree_fit P1 A n s t (target A))
          (term_sub_ptree_fit P2 B n s t (target B))
    | false => P
    end)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, lor_ind (1) S_D =>
    (match eq_f (neg (lor A B)) (substitution E n s) with
    | true =>
        demorgan_abd
          (substitution A n t)
          (substitution B n t)
          (term_sub_ind_fit D E n s t S_D)
          d1 d2 alpha1 alpha2
          (term_sub_ptree_fit
            (term_sub_ptree_fit P1 E n s t (lor_ind (0) S_D))
            A n s t (lor_ind (1) (non_target D)))
          (term_sub_ptree_fit
            (term_sub_ptree_fit P2 E n s t (lor_ind (0) S_D))
            B n s t (lor_ind (1) (non_target D)))
    | false =>
        demorgan_abd
          A B
          (term_sub_ind_fit D E n s t S_D)
          d1 d2 alpha1 alpha2
          (term_sub_ptree_fit P1 E n s t (lor_ind (0) S_D))
          (term_sub_ptree_fit P2 E n s t (lor_ind (0) S_D))
    end)

| _, _ => P
end.

(*


| negation_a A d alpha P', (1) =>
    (match eq_f (neg (neg A)) (substitution E n s) with
    | true =>
        negation_a
          (substitution A n t)
          d alpha
          (term_sub_ptree_fit P' A n s t (1))
    | false => P
    end)

| negation_ad A D d alpha P', lor_ind (1) S_D =>
    (match eq_f (neg (neg A)) (substitution E n s) with
    | true =>
        negation_ad
          (substitution A n t)
          (term_sub_ind_fit D E n s t S_D)
          d alpha
          (term_sub_ptree_fit
            (term_sub_ptree_fit P' E n s t (lor_ind (0) S_D))
            A n s t (lor_ind (1) (non_target D)))
    | false =>
        negation_ad
          A
          (term_sub_ind_fit D E n s t S_D)
          d alpha
          (term_sub_ptree_fit P E n s t (lor_ind (0) S_D))
    end)



| quantification_a A k t d alpha P', (1) =>
    quantification_a
      (substitution A n t)
      d alpha
      (term_sub_ptree_fit P' E n s t S)

| quantification_ad A D k t d alpha P', lor_ind (1) S_D =>
    quantification_ad
      (substitution A n t)
      (term_sub_ind_fit D E n s t S_D)
      d alpha
      (term_sub_ptree_fit P' E n s t S)

| w_rule_a A k d alpha g, _ =>
    w_rule_a
      (substitution A n t)
      n d alpha
      (fun (p : nat) =>
        term_sub_ptree_fit (g p) E n s t S)

| w_rule_ad A D k d alpha g, lor_ind S_A S_D =>
    w_rule_a
      (substitution A n t)
      (term_sub_ind_fit D E F S_D)
      n d alpha
      (fun (p : nat) =>
        term_sub_ptree_fit (g p) E n s t S)

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ca
      (term_sub_ind_fit C E F S)
      A d1 d2 alpha1 alpha2
      (term_sub_ptree_fit P1 E F (lor_ind S (non_target A)))
      P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ad
      A
      (term_sub_ind_fit D E F S)
      d1 d2 alpha1 alpha2
      P1
      (term_sub_ptree_fit P2 E F (lor_ind (0) S))

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_D =>
    cut_cad
      (term_sub_ind_fit C E F S_C)
      A
      (term_sub_ind_fit D E F S_D)
      d1 d2 alpha1 alpha2
      (term_sub_ptree_fit P1 E F (lor_ind S_C (non_target A)))
      (term_sub_ptree_fit P2 E F (lor_ind (0) S_D))

| _, _ => P
end.

*)

Fixpoint term_sub_ptree
  (P : ptree) (E : formula) (n : nat) (s t : term) (S : subst_ind) : ptree :=
match subst_ind_fit (ptree_formula P) S with
| false => P
| true => term_sub_ptree_fit P E n s t S
end.


(* Some preliminary lemmas *)
(* *)
Lemma term_sub_fit_false :
  forall (A E : formula) (n : nat) (s t : term) (S : subst_ind),
  subst_ind_fit A S = false ->
  term_sub_ind A E n s t S = A.
Proof. intros. unfold term_sub_ind. destruct A; rewrite H; auto. Qed.

Lemma term_sub_ptree_term_aux' :
  forall (P : ptree) (E : formula) (n : nat) (s t : term) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
    term_sub_ptree P E n s t S = P.
Proof. intros. unfold term_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma term_sub_ptree_term_aux :
  forall (P : ptree) (E : formula) (n : nat) (s t : term) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = false ->
      ptree_formula (term_sub_ptree P E n s t S) =
      term_sub_ind (ptree_formula P) E n s t S.
Proof.
intros. rewrite term_sub_ptree_term_aux'; auto.
unfold term_sub_ind. rewrite term_sub_fit_false. auto. apply H.
Qed.

Lemma term_sub_fit_true :
  forall (A E : formula) (n : nat) (s t : term) (S : subst_ind),
    subst_ind_fit A S = true ->
    term_sub_ind_fit A E n s t S = term_sub_ind A E n s t S.
Proof. intros. unfold term_sub_ind. destruct A; rewrite H; auto. Qed.

Lemma term_sub_ptree_formula_true :
  forall (P : ptree) (E : formula) (n : nat) (s t : term) (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    term_sub_ptree_fit P E n s t S = term_sub_ptree P E n s t S.
Proof. intros. unfold term_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma term_sub_ptree_fit_false :
  forall (P : ptree) (E : formula) (n : nat) (s t : term) (S : subst_ind),
  subst_ind_fit (ptree_formula P) S = false -> 
  term_sub_ptree P E n s t S = P.
Proof. intros. unfold term_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma term_sub_formula_sub :
  forall (A E : formula) (n : nat) (s t : term) (S : subst_ind),
  term_sub_ind_fit A E n s t S =
  formula_sub_ind_fit A (substitution E n s) (substitution E n t) S.
Proof. intros. unfold term_sub_ind_fit. destruct A; auto. Qed.

Lemma subst_closed_a : forall (a : atomic_formula) (n : nat) (s t : term),
  closed_t t = true ->
  closed_a (substitution_a a n s) = true ->
  closed_a (substitution_a a n t) = true.
Proof.
intros. destruct a. simpl. destruct (and_bool_prop _ _ H0).
rewrite (subst_closed_t n t0 s t H H1), (subst_closed_t n t1 s t H H2). auto.
Qed.

Lemma subst_closed : forall (A : formula) (n : nat) (s t : term),
  closed_t t = true ->
  closed (substitution A n s) = true ->
  closed (substitution A n t) = true.
Proof.
intros. induction A.
- simpl. apply (subst_closed_a _ _ s); auto.
- simpl. apply IHA. apply H0.
- simpl. simpl in H0. destruct (and_bool_prop _ _ H0).
  rewrite (IHA1 H1), (IHA2 H2). auto.
- simpl. simpl in H0. destruct (eq_nat n0 n); auto.
  destruct (closed_univ _ _ H0).
  + apply IHA in H1. simpl. rewrite H1. auto.
  + simpl. destruct (closed (substitution A n t)) eqn:HA; auto.
    destruct (free_list (substitution A n t)).
    * apply IHA. admit.
    * admit.
Admitted.

Lemma term_sub_ind_fit_closed : forall (A E : formula) (n : nat) (s t : term),
  closed A = true -> closed_t t = true ->
  forall (S : subst_ind),
    subst_ind_fit A S = true ->
    closed (term_sub_ind_fit A E n s t S) = true.
Proof.
intros. rewrite term_sub_formula_sub. apply formula_sub_ind_fit_closed; auto.
intros. apply (subst_closed _ _ s); auto.
Qed.

Lemma subst_twice_t : forall (n : nat) (T s t : term),
  substitution_t T n t = substitution_t (substitution_t T n s) n t.
Proof.
intros. induction T; auto.
- simpl. rewrite IHT. auto.
- simpl. rewrite IHT1,IHT2. auto.
- simpl. rewrite IHT1,IHT2. auto.
Admitted.


Lemma subst_twice_a : forall (a : atomic_formula) (n : nat) (s t : term),
  substitution_a a n t = substitution_a (substitution_a a n s) n t.
Proof.
intros. Admitted.

Lemma subst_twice : forall (A : formula) (n : nat) (s t : term),
  substitution A n t = substitution (substitution A n s) n t.
Proof.
intros. Admitted.

















(* First, we must prove that term_sub_ptree simply changes the base formula
of an ptree the way we expect with formula_sub_ind *)
(* *)
Lemma term_sub_ptree_formula' :
  forall (P : ptree) (E : formula) (n : nat) (s t : term),
  valid P ->
  correct_a (equ s t) = true ->
  forall (S : subst_ind),
    subst_ind_fit (ptree_formula P) S = true ->
    ptree_formula
      (term_sub_ptree P E n s t S) =
    term_sub_ind
      (ptree_formula P) E n s t S.
Proof.
intros P E n s t.
induction P; try intros H Hst S Hs.

- simpl in Hs. simpl. rewrite Hs. simpl.
  rewrite term_sub_ptree_formula_true; auto.
  destruct H as [H1 H2]. apply (IHP H2); auto.

- simpl in Hs. simpl. rewrite Hs. simpl.
  rewrite term_sub_ptree_formula_true; auto.
  destruct H as [H1 H2]. apply (IHP H2); auto.

- simpl in Hs. simpl. rewrite Hs. simpl. rewrite term_sub_fit_true; auto.

- simpl. destruct S; auto. inversion Hs. rewrite H1. simpl.
  repeat rewrite term_sub_formula_sub. auto.

- simpl. destruct S; auto. destruct S1; auto.
  inversion Hs. rewrite H1. simpl. auto.
  repeat rewrite term_sub_formula_sub. auto.

- simpl. destruct S; auto. destruct S1; auto.
  inversion Hs. rewrite H1. simpl. auto.
  repeat rewrite term_sub_formula_sub. auto.

- simpl. destruct S; auto. destruct S1; auto. destruct S1_1; auto.
  inversion Hs. rewrite H1. simpl. auto.
  repeat rewrite term_sub_formula_sub. auto.

- simpl. destruct (subst_ind_fit f S) eqn:HS.
  + simpl. rewrite term_sub_fit_true; auto.
  + simpl. rewrite term_sub_fit_false; auto.

- simpl. destruct S; auto. inversion Hs. rewrite H1. simpl.
  repeat rewrite term_sub_formula_sub. auto.

- simpl. destruct S; auto. inversion Hs. rewrite H1. simpl.
  repeat rewrite term_sub_formula_sub. auto.

- simpl. destruct S; auto.
  + simpl. destruct (substitution E n s); auto. destruct f1; auto.
    destruct (eq_f f f1_1 && eq_f f0 f1_2); auto.
  + simpl. destruct (substitution E n s) eqn:HE; auto. destruct f1; auto.
    destruct (eq_f f f1_1 && eq_f f0 f1_2) eqn:Hf1; auto. simpl.
    rewrite (subst_twice E _ s). rewrite HE.
    destruct (and_bool_prop _ _ Hf1).
    rewrite (f_eq_decid _ _ H0). rewrite (f_eq_decid _ _ H1). auto.





- simpl. destruct S; auto.
  destruct S1; auto; inversion Hs; rewrite H1; simpl; auto.

- simpl. destruct S; auto.

- simpl. destruct S; auto.
  destruct S1; auto; inversion Hs; rewrite H1; simpl; auto.

- simpl. destruct S; auto.

- simpl. destruct S; auto.
  destruct S1; auto; inversion Hs; rewrite H1; simpl; auto.

- simpl. destruct S; auto.

- intros Hv S Hs. simpl. destruct S; auto.
  destruct S1; auto; inversion Hs; rewrite H1; simpl; auto.

- simpl. destruct (subst_ind_fit f S) eqn:HS.
  + simpl. rewrite sub_fit_true; auto.
  + simpl. rewrite sub_fit_false; auto.

- simpl. destruct (subst_ind_fit f0 S) eqn:HS.
  + simpl. rewrite sub_fit_true; auto.
  + simpl. rewrite sub_fit_false; auto.

- simpl. destruct S; auto. inversion Hs. rewrite H1. simpl. auto.
Qed.

*)
