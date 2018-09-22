Require Import PredomCore.
Require Import PredomProd.

Section KnasterTarski.

Section CLattice.

(** printing <= $\sqsubseteq$ *)
(** printing sup $\bigwedge$ *)
(** printing inf $\bigvee$ *)
(** printing == $\equiv$ *)

(** * Complete Lattice
  A semi-lattice [(L, \/ )] is a partial order [L = (T, <= )] and a binary operation inf [\/ : L -> L -> L],
  such that [forall x y, x \/ y <= x], [forall x y, x \/ y == y \/ x] and [forall z x y, z <= x /\ z <= y -> z <= x \/ y].

  A complete lattice is a semi lattice where the inf operation has been generalized to all subsets of [L].
*)

Record CLattice := mk_semilattice
 {
   ltord :> ord;
   inf : forall S : ltord -> Prop, ltord;
   Pinf : forall P : ltord -> Prop, forall t, P t -> inf P <= t;
   PinfL : forall P : ltord -> Prop, forall t, (forall x, P x -> t <= x) -> t <= inf P
 }.

Variable L : CLattice.

(** A complete lattice has both infima and suprema. Suprema of a set S ([sup S]) is given by [inf { z | S <= z}] *)

Definition sup (S:L -> Prop) : L := inf L (fun D => forall s, S s -> s <= D).

Lemma Psup : forall (S:L -> Prop) t, S t -> t <= sup S.
intros S t St. unfold sup.
refine (PinfL _ _ _ _).
intros l Cl. apply Cl. apply St.
Qed.

Lemma PsupL : forall (S:L -> Prop) t, (forall x, S x -> x <= t) -> sup S <= t.
intros S t C. unfold sup. refine (Pinf _ _ _ _).
intros l Sl. apply C. apply Sl.
Qed.

End CLattice.

Section SubLattice.
Variable L : CLattice.

(** Let [P] represent a subset of [L]. *)
Variable P : ltord L -> Prop.

(** We can then define a an ordering on the subset [P] by inheriting the ordering from [L]. *)
Definition Subord : ord.
exists ({t | P t}) (fun (x y:{t | P t}) => match x with exist x _ =>
                                             match y with exist y _ => x <= y
                                             end
                                           end).
intros x. case x. clear x. intros x _. auto.
intros x y z ; case x ; case y ; case z ; clear x z y. intros x _ y _ z _.
apply Ole_trans.
Defined.

Definition ForgetSubord : Subord -> ltord L.
intros S. case S. clear S. intros x _. apply x.
Defined.

(** If [P] is closed under infima then it is a complete lattice *)
Variable PSinf: forall (S:ltord L -> Prop), (forall t, S t -> P t) -> P (inf L S).

Definition Embed (t:ltord L) (p:P t) : Subord.
intros t Pt. exists t. apply Pt.
Defined.

Definition Extend (S : Subord -> Prop) : ltord L -> Prop.
intros S l. apply (exists p:P l, S (Embed l p)).
Defined.

Lemma ExtendP: forall (S:Subord -> Prop) t, Extend S t -> P t.
intros S t Ex. unfold Extend in Ex. unfold Embed in Ex. destruct Ex as [E _].
apply E.
Defined.

Definition SubLattice : CLattice.
exists (Subord) (fun (S:Subord -> Prop) =>
               Embed (inf L (Extend S)) (PSinf (Extend S) (ExtendP S))).
intros S t. case t. simpl. clear t. intros l Pl Pe. refine (Pinf _ _ _ _ ).
 unfold Extend. unfold Embed. exists Pl. apply Pe.
intros S t. case t. simpl. clear t. intros x Px C. apply PinfL.
intros t et.
unfold Extend in et. unfold Embed in et.
destruct et as [Pt St]. specialize (C _ St). apply C.
Defined.

End SubLattice.

Variable L : CLattice.

Definition op_ord (O:ord) : ord.
intros O. exists (tord O) (fun x y => y <= x).
auto. intros x y z. intros A B. apply (Ole_trans B A).
Defined.

Definition op_lat : CLattice.
exists (op_ord L) (sup L).
intros P t Pt. simpl. apply (Psup L P _ Pt).
intros P t C. simpl. refine (PsupL L P _ _). apply C.
Defined.

Variable f : L -m> L.

Definition PreFixedPoint d := f d <= d.

Lemma PreFixedInfs: (forall S : L -> Prop,
        (forall t : L, S t -> PreFixedPoint t) -> PreFixedPoint (inf L S)).
intros S C.
unfold PreFixedPoint in *.
apply (PinfL L S). intros l Sl.
apply Ole_trans with (y:= f l).
assert (monotonic f) as M by auto. apply M.
apply Pinf. apply Sl.
apply (C _ Sl).
Qed.

Definition PreFixedLattice := SubLattice L (fun x => PreFixedPoint x) PreFixedInfs.

Definition PostFixedPoint d := d <= f d.

Lemma PostFixedSups: forall S : op_lat -> Prop,
        (forall t : op_lat, S t -> (fun x : op_lat => PostFixedPoint x) t) ->
        (fun x : op_lat => PostFixedPoint x) (inf op_lat S).
unfold PostFixedPoint.
intros S C. simpl in *. refine (PsupL L _ _ _).
intros l Sl. apply Ole_trans with (y:= f l). apply C. apply Sl.
assert (monotonic f) as M by auto. apply M. apply (Psup L _ _ Sl).
Qed.

Definition PostFixedLattice := SubLattice op_lat (fun x => PostFixedPoint x) PostFixedSups.

Definition lfp := match (inf PreFixedLattice (fun _ => True)) with exist x _ => x end.

Definition gfp := match (inf PostFixedLattice (fun _ => True)) with exist x _ => x end.

Lemma lfp_fixedpoint : f lfp == lfp.
unfold lfp.
assert (yy:= Pinf PreFixedLattice (fun _ => True)).
generalize yy ; clear yy.
case (inf PreFixedLattice (fun _ => True)).
intros x Px yy.
assert (zz:=fun X PX => (yy (exist (fun t => PreFixedPoint t) X PX))). clear yy.
assert (PreFixedPoint (f x)). unfold PreFixedPoint.
assert (monotonic f) as M by auto. apply M. apply Px.
split.
specialize (zz _ H). simpl in zz.
apply Px.
apply zz ; auto.
Qed.

Lemma gfp_fixedpoint : f gfp == gfp.
unfold gfp.
assert (yy:= Pinf PostFixedLattice (fun _ => True)).
generalize yy ; clear yy.
case (inf PostFixedLattice (fun _ => True)).
intros x Px yy.
assert (zz:=fun X PX => (yy (exist (fun t => PostFixedPoint t) X PX))). clear yy.
assert (PostFixedPoint (f x)). unfold PostFixedPoint.
assert (monotonic f) as M by auto. apply M. apply Px.
split.
specialize (zz _ H). simpl in zz. apply zz. auto.
apply Px.
Qed.

Lemma lfp_least: forall fp, f fp <= fp -> lfp <= fp.
unfold lfp.
intros fp ff. assert (PreFixedPoint fp). apply ff.
assert (yy:= Pinf PreFixedLattice (fun _ => True)).
generalize yy ; clear yy.
case (inf PreFixedLattice (fun _ => True)).
intros x Px yy.
assert (zz:=fun X PX => (yy (exist (fun t => PreFixedPoint t) X PX))). clear yy.
case (inf PreFixedLattice (fun _ : PreFixedLattice => True)).
specialize (zz _ H). simpl in zz. intros _ _. apply zz. auto.
Qed.

Lemma gfp_greatest: forall fp, fp <= f fp -> fp <= gfp.
unfold gfp.
intros fp ff. assert (PostFixedPoint fp). apply ff.
assert (yy:= Pinf PostFixedLattice (fun _ => True)).
generalize yy ; clear yy.
case (inf PostFixedLattice (fun _ => True)).
intros x Px yy.
assert (zz:=fun X PX => (yy (exist (fun t => PostFixedPoint t) X PX))). clear yy.
case (inf PostFixedLattice (fun _ : PostFixedLattice => True)).
specialize (zz _ H). simpl in zz. intros _ _. apply zz. auto.
Qed.

End KnasterTarski.

Definition ProdLattice (L1 L2 : CLattice) : CLattice.
intros L1 L2. exists (Oprod L1 L2) (fun (S:Oprod L1 L2 -> Prop) =>
               (inf L1 (fun l1 => exists l2, S (l1,l2)),inf L2 (fun l2 => exists l1, S (l1,l2)))).
intros P t. case t. clear t. intros t0 t1 Pt. simpl. split.
refine (Pinf _ _ _ _). exists t1. apply Pt.
refine (Pinf _ _ _ _). exists t0. apply Pt.
intros P t. case t. clear t. intros t0 t1 Pt. simpl. split.
refine (PinfL _ _ _ _). intros x Px. destruct Px as [y Pxy].
specialize (Pt _ Pxy).
inversion Pt. simpl in *. auto.

refine (PinfL _ _ _ _). intros x Px. destruct Px as [y Pyx].
specialize (Pt _ Pyx). inversion Pt. simpl in *. auto.
Defined.

Definition LFst L1 L2 : ProdLattice L1 L2 -m> L1.
intros L1 L2. exists (@fst L1 L2). unfold monotonic.
intros x y ; case x ; clear x ; intros x0 x1 ; case y ; clear y ; intros y0 y1.
simpl. intros [A _] ; auto.
Defined.

Definition LSnd L1 L2 : ProdLattice L1 L2 -m> L2.
intros L1 L2. exists (@snd L1 L2). unfold monotonic.
intros x y ; case x ; clear x ; intros x0 x1 ; case y ; clear y ; intros y0 y1.
simpl. intros [_ A] ; auto.
Defined.

Definition ArrowLattice (T:Type) (L:CLattice) : CLattice.
intros T L. exists (ford T L) (fun (S:T -o> L -> Prop) => fun t => inf L (fun st => exists s, S s /\ s t = st)).
intros P f Pf. simpl. intros t. refine (Pinf _ _ _ _). exists f. split. auto. auto.
intros P f C. simpl. intros t. refine (PinfL _ _ _ _).
intros l Tl. destruct Tl as [f0 [Pf0 f0t]]. specialize (C _ Pf0). rewrite <- f0t.
auto.
Defined.

Require Import Sets.

Definition Subsetord (T:SetKind) : ord.
intros T. exists (set T) (@subset T).
intros x t ; auto.
intros x y z C1 C2 t. specialize (C1 t). specialize (C2 t).
intros a. apply (C2 (C1 a)).
Defined.

Definition SubsetLattice (T:SetKind) : CLattice.
intros T. exists (Subsetord T) (@Intersect T).
intros P t Pt. simpl. intros x Px. apply (Px t Pt).
intros P t Pt. simpl in *. intros x Px f Pf. specialize (Pt f Pf).
apply Pt. apply Px.
Defined.

Definition Supsetord (T:SetKind) := op_ord (Subsetord T).

Definition SupsetLattice (T:SetKind) := op_lat (SubsetLattice T).


