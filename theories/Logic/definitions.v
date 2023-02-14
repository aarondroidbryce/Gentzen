Open Scope bool.

Lemma and_bool_symm : forall (b1 b2 : bool),
  b1 && b2 = true -> b2 && b1 = true.
Proof. intros. case_eq b1; case_eq b2; intros; rewrite H0,H1 in H; auto. Qed.

Lemma and_bool_prop : forall (b1 b2 : bool),
  b1 && b2 = true -> b1 = true /\ b2 = true.
Proof. intros. case_eq b1; case_eq b2; intros; rewrite H0,H1 in H; auto. Qed.

Lemma or_bool_symm : forall (b1 b2 : bool),
  b1 || b2 = true -> b2 || b1 = true.
Proof. intros. case_eq b1; case_eq b2; intros; rewrite H0,H1 in H; auto. Qed.

Lemma or_bool_prop : forall (b1 b2 : bool),
  b1 || b2 = true -> b1 = true \/ b2 = true.
Proof. intros. case_eq b1; case_eq b2; intros; rewrite H0,H1 in H; auto. Qed.