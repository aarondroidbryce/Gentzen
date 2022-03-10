Require Import Ensembles.
Require Import Relations.
Require Import AccP.

Set Implicit Arguments.
Require Import PartialFix.

Section example.
  Let U := (nat * nat)%type.

  Inductive Lt: U -> U -> Prop:=
  LT_1 : forall i j k l:nat, i < k -> Lt (i,j) (k,l).

  Inductive D : U -> Prop :=
  D_1 : forall i, D (i,0).



  Lemma Acc_Lt : forall u, D u -> Acc (restrict  _ D Lt) u.
  Admitted.

 Check PFix2.
 Check (PFix2 Acc_Lt (fun u:U => U)).



 Definition fonct : forall x : U,
        (forall y : U, D y -> Lt y x -> (fun _ : U => U) y) ->
        D x -> (fun _ : U => U) x.
  intro u;case u.
 intros a b.
 case b.
 2:intros.
 2:elimtype False.
 2:inversion H0.
 case a.
 intros; exact (1,1).
 intros n Hn DSn.
 generalize (Hn (n,0)).
 intro H.
 assert (D (n,0)).
 constructor.
 assert (Lt (n, 0) (S n, 0)).
 constructor.
 auto.
 case (H H0 H1).
 intros x _;exact (2*x,0).
Defined.


 Check (PFix2  Acc_Lt (fun u:U => U) fonct).
Definition my_fun := PFix2  Acc_Lt (fun u:U => U) fonct.


 
 
 
Check (PFix2_eq Acc_Lt (fun _ => U) fonct).

Lemma extens : (forall (x : U)
          (f g : forall y : U, restrict U D Lt y x -> (fun _ : U => U) y)
          (Dx : D x),
        (forall (y : U) (p : restrict U D Lt y x), f y p = g y p) ->
        fonct
          (fun (y : U) (H1 : D y) (H2 : Lt y x) => f y (conj H1 (conj H2 Dx)))
          Dx =
        fonct
          (fun (y : U) (H1 : D y) (H2 : Lt y x) => g y (conj H1 (conj H2 Dx)))
          Dx).
destruct x.
destruct n;simpl.
 case n0;simpl.
 auto.
auto.
case n0;simpl;auto.
intros.
rewrite H.
auto.
Qed.

Check (PFix2_eq Acc_Lt (fun _ => U) fonct extens).

(*


PFix2_eq Acc_Lt (fun _ : U => U) fonct extens
     : forall (x : U) (H : D x),
       PFix2 Acc_Lt (fun _ : U => U) fonct x H =
       fonct
         (fun (y : U) (H1 : D y) (H2 : Lt y x) =>
          PFix2 Acc_Lt (fun _ : U => U) fonct y (lt_D (conj H1 (conj H2 H))))
         H

*)

Lemma my_fun_rw 
     : forall (x : U) (H : D x),
       my_fun (*PFix2 Acc_Lt (fun _ : U => U) fonct*)  H =
       fonct
         (fun (y : U) (H1 : D y) (H2 : Lt y x) =>
          (*PFix2 Acc_Lt (fun _ : U => U) fonct y*) my_fun (lt_D (T:=U) (conj H1 (conj H2 H))))
         H.

intros;unfold my_fun. 
(*

1 subgoal
  
  x : U
  H : D x
  ============================
   PFix2 Acc_Lt (fun _ : U => U) fonct x H =
   fonct
     (fun (y : U) (H1 : D y) (H2 : Lt y x) =>
      PFix2 Acc_Lt (fun _ : U => U) fonct y (lt_D (conj H1 (conj H2 H)))) H



*)
Check PFix2_eq.
eapply (PFix2_eq Acc_Lt (fun _ : U => U)).
apply extens.
Qed.


End example.
