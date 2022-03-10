Require Import Ensembles.
Require Import Relations.
 Require Import AccP.
Set Implicit Arguments.
Section  partial_fix.

 
 Variable T : Type.
 Variable D : Ensemble T.
 Variable lt : T -> T -> Prop.
 Hypothesis  lt_D : forall x y, lt x y -> D x.
 Hypothesis gt_D : forall x y, lt x y -> D y.
 Hypothesis D_Acc : forall x, D x -> Acc lt x.

 Section Acc_iterP. 

 Variable P : T-> Type.

 Variable F : forall x:T, (forall y:T,  lt y x -> P y) -> D x -> P x.


 
Fixpoint Acc_iter_partial (x:T) (H:D x) (a:Acc lt x) {struct a} : P x :=
    F  (x:=x)
     (fun (y:T) (h: lt y  x) =>
          Acc_iter_partial (lt_D h) (Acc_inv a _ h))H .


End Acc_iterP.


Definition partial_fun_induction P F (x:T) Dx :=
  Acc_iter_partial P F Dx (D_Acc (x:=x) Dx).


Section FixPoint.

 Variable P : T -> Type.

 Variable F : forall x:T, (forall y:T, lt  y  x -> P y) -> D x -> P x.


 
Definition PFix (x:T)(H:D x) := Acc_iter_partial P F H (D_Acc  H).

 Hypothesis
    F_ext :
      forall (x:T) (f g:forall y:T,  lt y  x -> P y) (Dx: D x),
        (forall (y:T) (p:lt y  x), f y p = g y p) -> F f Dx = F g Dx.

Lemma PFix_F_eq :
   forall (x:T)(H:D x)(r:Acc lt x),
    F  (fun (y:T) (h: lt y x) => 
      Acc_iter_partial P F (lt_D  h) (Acc_inv  r y h))H  = 
      Acc_iter_partial P F H r.
  Proof.
   destruct r using Acc_inv_dep.
   auto.
 Qed.

  Lemma PFix_F_inv :  forall (x:T)(H:D x) (r s:Acc lt x),
       Acc_iter_partial P F H r  = Acc_iter_partial P F H s .
  Proof.
   intro x.
   intro H.
   generalize H.
   pattern x.
   apply partial_fun_induction.
   intros. 
   rewrite <- (PFix_F_eq  H2 r). 
   rewrite <- (PFix_F_eq  H2 s).
   apply F_ext.
   auto.
   auto.
  Qed.


 Lemma PFix_eq : forall (x:T )(H:D x),
             PFix  H = 
             F  (fun (y:T) (h: lt y  x) => PFix  (lt_D h)) H.
 Proof.
  intro x; unfold PFix in |- *.
  intro;rewrite <- (PFix_F_eq (x:=x)).
  apply F_ext; intros.
  apply PFix_F_inv.
Qed.

End FixPoint.

End partial_fix.

Section partialfix2.
 Variable T : Type.
 Variable D : Ensemble T.
 Variable lt : T -> T -> Prop.

 Hypothesis D_Acc : forall x, D x -> Acc (restrict _ D lt) x.
 
Section Acc_iterP.

 Variable P : T-> Type.

 Variable F : forall x:T, (forall y:T,  D y -> lt y x -> P y) -> D x -> P x.

Lemma lt_D : forall x y, restrict _ D lt x y -> D x.
firstorder.
Qed.


Let F': forall x : T, (forall y : T, restrict T D lt y x -> P y) -> D x -> P x.
 intro x.
 intro H.
 intros;
 apply F.
 2:auto.
 unfold restrict in H.
 firstorder. 
Defined.

Definition PFix2 := 
 (PFix  (T:=T) D (lt:=(restrict _ D lt)) lt_D D_Acc P F').
Check PFix2.

Check PFix_eq.

Check (PFix_eq (T:=T) D (lt:=(restrict _ D lt)) lt_D D_Acc P F').

Lemma PFix2_eq 
(* PFix_eq D lt_D D_Acc P F' *)
     : (forall (x : T) (f g : forall y : T, restrict T D lt y x -> P y)
          (Dx : D x),
        (forall (y : T) (p : restrict T D lt y x), f y p = g y p) ->
        F' f Dx = F' g Dx) ->
       forall (x : T) (H : D x),
       PFix2  H =
       F'
         (fun (y : T) (h : restrict T D lt y x) =>
          PFix2 (lt_D h)) H.
 intros;unfold PFix2;apply PFix_eq.
 unfold restrict.
 intros.
 apply H.
 intros.
 apply H1.
Qed.


End Acc_iterP.





End partialfix2.

Check PFix2_eq.
(*

     : forall (T : Type) (D : Ensemble T) (lt : T -> T -> Prop)
         (D_Acc : forall x : T, D x -> Acc (restrict T D lt) x)
         (P : T -> Type)
         (F : forall x : T,
              (forall y : T, D y -> lt y x -> P y) -> D x -> P x),
       (forall (x : T) (f g : forall y : T, restrict T D lt y x -> P y)
          (Dx : D x),
        (forall (y : T) (p : restrict T D lt y x), f y p = g y p) ->
        F x
          (fun (y : T) (H1 : D y) (H2 : lt y x) => f y (conj H1 (conj H2 Dx)))
          Dx =
        F x
          (fun (y : T) (H1 : D y) (H2 : lt y x) => g y (conj H1 (conj H2 Dx)))
          Dx) ->
       forall (x : T) (H : D x),
       PFix2 D_Acc P F x H =
       F x
         (fun (y : T) (H1 : D y) (H2 : lt y x) =>
          PFix2 D_Acc P F y (lt_D (conj H1 (conj H2 H)))) H



*)
Check PFix_eq.
(*


PFix_eq
     : forall (T : Type) (D : Ensemble T) (lt : T -> T -> Prop)
         (lt_D : forall x y : T, lt x y -> D x)
         (D_Acc : forall x : T, D x -> Acc lt x) (P : T -> Type)
         (F : forall x : T, (forall y : T, lt y x -> P y) -> D x -> P x),
       (forall (x : T) (f g : forall y : T, lt y x -> P y) (Dx : D x),
        (forall (y : T) (p : lt y x), f y p = g y p) -> F x f Dx = F x g Dx) ->
       forall (x : T) (H : D x),
       PFix D lt_D D_Acc P F x H =
       F x (fun (y : T) (h : lt y x) => PFix D lt_D D_Acc P F y (lt_D y x h))
         H

*)

