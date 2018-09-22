(**********************************************************************************
 * KnasterTarski.v                                                                *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                       *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)

(* Complete Lattices *)

Require Export PredomCore.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** printing <= $\sqsubseteq$ *)
(** printing sup $\bigwedge$ *)
(** printing inf $\bigvee$ *)
(** printing == $\equiv$ *)

(** * Complete Lattice
  A semi-lattice [(L, \/ )] is a partial order [L = (T, <= )] and a binary operation inf [\/ : L -> L -> L],
  such that [forall x y, x \/ y <= x], [forall x y, x \/ y == y \/ x] and [forall z x y, z <= x /\ z <= y -> z <= x \/ y].

  A complete lattice is a semi lattice where the inf operation has been generalized to all subsets of [L].
*)

Open Scope C_scope.

Module CLattice.

Section Mixin.

Variable T:ordType.

Definition axiom (inf : (T -> Prop) -> T) := 
   forall P:T -> Prop, (forall t, (P t -> inf P <= t) /\ ((forall x, P x -> t <= x) -> t <= inf P)).

Record mixin_of : Type := Mixin
{ inf : (T -> Prop) -> T;
  _ : axiom inf
}.

End Mixin.

Section ClassDef.
Record class_of (T:Type) : Type :=
  Class { base : PreOrd.class_of T ; 
          ext : mixin_of (PreOrd.Pack base T) }.
Local Coercion base : class_of >-> PreOrd.class_of.
Local Coercion ext : class_of >-> mixin_of.

Structure type : Type := Pack { sort : Type; _ : class_of sort ; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
  let: Pack T c _ := cT return K _ (class cT) in k _ c.
Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT.

Definition pack := let k T c m := Pack (@Class T c m) T in PreOrd.unpack k.

Definition ordType cT := PreOrd.Pack (class cT) cT.
Definition setoidType cT := Setoid.Pack (class cT) cT.
End ClassDef.
Module Import Exports.
Coercion base : class_of >-> PreOrd.class_of.
Coercion ext : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion ordType : type >-> PreOrd.type.
Coercion setoidType : type >-> Setoid.type.
Notation clatType := type.
Notation ClatMixin := Mixin.
Notation ClatType := pack.

Canonical Structure ordType.
Canonical Structure setoidType.
End Exports.
End CLattice.
Export CLattice.Exports.

Definition inf (cT:clatType) : (cT -> Prop) -> cT := CLattice.inf (CLattice.class cT).
Implicit Arguments inf [cT].

Lemma Pinf (T:clatType) : forall P : T -> Prop, forall t, P t -> inf P <= t.
unfold inf. case:T => A. case => O. simpl. case. simpl.
move => I X a P t x. by apply (proj1 (X P t) x).
Qed.

Lemma PinfL (T:clatType) : forall P : T -> Prop, forall t, (forall x, P x -> t <= x) -> t <= inf P.
unfold inf. case:T => A. case => O. simpl. case. simpl.
move => I X T P t x. by apply (proj2 (X P t) x).
Qed.

Lemma inf_ext (T:clatType) (P P' : T -> Prop) : (forall x, P x <-> P' x)  -> inf P =-= inf P'.
move => C. split.
- apply: PinfL. move => x Px'. apply Pinf. by apply (proj2 (C x) Px').
- apply: PinfL. move => x Px'. apply Pinf. by apply (proj1 (C x) Px').
Qed.


Add Parametric Relation (O:clatType) : O (@tset_eq O : O -> O -> Prop)
       reflexivity proved by (@Oeq_refl O) symmetry proved by (@Oeq_sym O)
       transitivity proved by (@Oeq_trans O) as Oeq_ClatRelation.

Add Parametric Relation (O:clatType) : O (@Ole O)
       reflexivity proved by (@Ole_refl O) 
       transitivity proved by (@Ole_trans O) as Ole_ClatRelation.

Definition imageSet (T0 T1:clatType) (f:ordCatType T0 T1) : (T0 -> Prop) -> T1 -> Prop :=
  fun S x => exists y, S y /\ f y = x.

Definition limitpres (T0 T1:clatType) (f: ordCatType T0 T1) :=
   forall S, f (inf S) =-= inf (imageSet f S).

Module FLimit.

Section flimit.
Variable O1 O2 : clatType.

Record mixin_of (f:fmono O1 O2) := Mixin { cont :> limitpres f }.

Record class_of (f : O1 -> O2) := Class { base : FMon.mixin_of f; ext : mixin_of (FMon.Pack base f) }.
Local Coercion base : class_of >-> FMon.mixin_of.
Local Coercion ext : class_of >-> mixin_of.

Structure type : Type := Pack {sort : O1 -> O2; _ : class_of sort; _ : O1 -> O2}.
Local Coercion sort : type >-> Funclass.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
  let: Pack T c _ := cT return K _ (class cT) in k _ c.
Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT.
Definition pack := let k T c m := Pack (@Class T c m) T in FMon.unpack k.

Definition fmono f : fmono O1 O2 := FMon.Pack (class f) f.
End flimit.
Module Import Exports.
Coercion base : class_of >-> FMon.mixin_of.
Coercion ext : class_of >-> mixin_of.
Coercion sort : type >-> Funclass.
Coercion fmono : type >-> FMon.type.
Notation flimit := type.
Notation flimitMixin := Mixin.
Notation flimitType := pack.
Canonical Structure fmono.
End Exports.
End FLimit.
Export FLimit.Exports.

Lemma flimitpres (T0 T1:clatType) (f:flimit T0 T1) : limitpres f.
case:f => f. case ; case => m. case => l s. by apply l.
Qed.

Lemma flimitp_ord_axiom (D1 D2 :clatType) : PreOrd.axiom (fun (f g:flimit D1 D2) => (f:fmono D1 D2) <= g).
move => f ; split ; first by [].
move => g h ; by apply Ole_trans.
Qed.

Canonical Structure flimitp_ordMixin (D1 D2 :clatType) := OrdMixin (@flimitp_ord_axiom D1 D2).
Canonical Structure flimitp_ordType (D1 D2 :clatType) := Eval hnf in OrdType (flimitp_ordMixin D1 D2).

Lemma clatMorphSetoidAxiom (O0 O1:clatType) : @Setoid.axiom (flimit O0 O1) (fun x y => (x:fmono O0 O1) =-= y).
split ; first by move => x ; apply: tset_refl. split.
- by apply: Oeq_trans.
- by apply: Oeq_sym.
Qed.

Canonical Structure clatMorphSetoidMixin (T0 T1 : clatType) := SetoidMixin (@clatMorphSetoidAxiom T0 T1).
Canonical Structure clatMorphSetoidType (T0 T1 : clatType) := Eval hnf in SetoidType (clatMorphSetoidMixin T0 T1).

(* flimit <= *)
Definition flimit_less (A B: clatType): relation (flimit A B) := (@Ole _).

Definition flimit_less_preorder (A B: clatType): PreOrder (@flimit_less A B).
split ;first by move => x.
move => x y z. by apply Ole_trans.
Defined.

Existing Instance flimit_less_preorder.

Add Parametric Morphism (A B : clatType) :
  (@FLimit.sort A B) with signature (@flimit_less A B ++> @Ole A ++> @Ole B)
 as flimit_le_compat.
move => x y l x' y' l'. apply Ole_trans with (y:=x y') ; first by apply: fmonotonic.
by apply l.
Qed.

(* fcont == *)
Definition flimit_equal (A B: clatType): relation (flimit A B) := (@tset_eq _).

Definition flimit_equal_equivalence (A B: clatType): Equivalence (@flimit_equal A B).
split.
- move => x. by apply: Oeq_refl.
- move => x y. by apply: Oeq_sym.
- move => x y z. by apply: Oeq_trans.
Defined.

Existing Instance flimit_equal_equivalence.

Add Parametric Morphism (A B : clatType) :
  (@FLimit.sort A B) with signature (@flimit_equal A B ==> @tset_eq A ==> @tset_eq B)
 as flimit_eq_compat.
move => x y l x' y' l'. apply Oeq_trans with (y:=x y') ; first by apply: fmon_stable.
by apply (fmon_eq_elim l y').
Qed.

Lemma fcomplp (D0 D1 D2 : clatType) (f : flimit D1 D2) (g: flimit D0 D1) :
   limitpres (ocomp f g).
move => S. simpl.
have gg:=flimitpres g S. rewrite -> gg.
have ff:=flimitpres f (imageSet g S). rewrite -> ff. clear gg ff.
apply: inf_ext. move => x. unfold imageSet. split.
- case => t1. case. case => t0. case => iS gt0 ft1. exists t0. split ; first by []. rewrite <- ft1.
  by rewrite <- gt0.
- case => t0. case => iS fg0. exists (g t0). split ; last by []. exists t0. by split.
Qed.

Canonical Structure mk_flimitM (D0 D1:clatType) (f:fmono D0 D1) (c:limitpres (FMon.Pack (FMon.class f) f)) := flimitMixin c.
Definition mk_flimit (D0 D1:clatType) (f:fmono D0 D1) (c:limitpres (FMon.Pack (FMon.class f) f)) := Eval hnf in @flimitType D0 D1 f (mk_flimitM c).

Definition complp (D0 D1 D2 : clatType) (f : flimit D1 D2) (g: flimit D0 D1) := Eval hnf in mk_flimit (fcomplp f g).

Lemma oidlp (T:clatType) : limitpres (@oid T).
move => S. simpl. apply: inf_ext.
move => x. split.
- move => iS. exists x. by split. unfold imageSet. 
- case => y [iS P].  simpl in P. rewrite <- P. by apply iS.
Qed.

Definition lpid (T:clatType) := Eval hnf in mk_flimit (@oidlp T).

Lemma clatCatAxiom : @Category.axiom _ clatMorphSetoidType complp lpid.
split ; last split ; last split.
move => T T' f. by apply: fmon_eq_intro.
move => T T' f. by apply: fmon_eq_intro.
move => T0 T1 T2 T3 f g h. by apply: fmon_eq_intro.
move => T0 T1 T2 f f' g g' e e'.
apply: fmon_eq_intro => a. simpl. rewrite -> e. by rewrite -> e'.
Qed.

Canonical Structure clatCatMixin := CatMixin clatCatAxiom.
Canonical Structure clatCat := Eval hnf in CatType clatCatMixin.

Section KnasterTarski.

Section Lat.
Variable L : clatType.

Definition aboveSet : (L -> Prop) -> L -> Prop := (fun D e => forall s, D s -> s <= e).

Definition sup (S: L -> Prop) : L := inf (aboveSet S).

Lemma Psup : forall (S : L -> Prop) t, S t -> t <= sup S.
intros S t St. unfold sup.
refine (PinfL _).
intros l Cl. apply Cl. by apply St.
Qed.

Lemma PsupL : forall (S: L -> Prop) t, (forall x, S x -> x <= t) -> sup S <= t.
intros S t C. unfold sup. refine (Pinf _).
intros l Sl. apply C. apply Sl.
Qed.


(** A complete lattice has both infima and suprema. Suprema of a set S ([sup S]) is given by [inf { z | S <= z}] *)

End Lat.

Section SubLattice.
Variable L : clatType.

(** Let [P] represent a subset of [L]. *)
Variable P : L -> Prop.



(** We can then define a an ordering on the subset [P] by inheriting the ordering from [L]. *)

(** If [P] is closed under infima then it is a complete lattice *)
Variable PSinf: forall (S:L -> Prop), (forall t, S t -> P t) -> P (inf S).

Definition Embed (t:L) (p:P t) : sub_ordType P.
by exists t.
Defined.

Definition Extend (S : sub_ordType P -> Prop) : L -> Prop := (fun l => (exists p:P l, S (Embed p))).

Lemma ExtendP: forall S t, Extend S t -> P t.
intros S t Ex. unfold Extend in Ex. unfold Embed in Ex. destruct Ex as [E _].
apply E.
Defined.

Lemma sublatAxiom : CLattice.axiom (fun (S:sub_ordType P -> Prop) =>
               @Embed (inf (Extend S)) (@PSinf (Extend S) (@ExtendP S))).
intros S t. split.
- case t. simpl. clear t. intros l Pl Pe. refine (Pinf _ ).
  unfold Extend. unfold Embed. exists Pl. by apply Pe.
- case t. simpl. clear t. intros x Px C. apply: PinfL.
  intros t et. unfold Extend in et. unfold Embed in et.
  destruct et as [Pt St]. specialize (C _ St). by apply C.
Qed.

Canonical Structure sub_clatMixin := ClatMixin sublatAxiom.
Canonical Structure sub_clatType := Eval hnf in ClatType sub_clatMixin.

End SubLattice.

Variable L : clatType.

Lemma op_ordAxiom (O:ordType) : PreOrd.axiom (fun (x y:O) => y <= x).
move => x.
split ; first by apply Ole_refl.
move => y z ; by apply (fun X Y => Ole_trans Y X).
Qed.

Definition op_ordMixin O := OrdMixin (@op_ordAxiom O).
Definition op_ordType O := Eval hnf in OrdType (op_ordMixin O).

Lemma oplatAxiom : @CLattice.axiom (op_ordType L) (@sup L).
intros P t. split.
- move => Pt. simpl. by apply (Psup Pt).
- intros C. simpl. refine (PsupL _). by apply C.
Qed.

Definition op_latMixin := ClatMixin oplatAxiom.
Definition op_latType := Eval hnf in @ClatType (op_ordType L) op_latMixin.

Variable f : ordCatType L L.

Definition PreFixedPoint d := f d <= d.

Lemma PreFixedInfs: (forall S : L -> Prop,
        (forall t : L, S t -> PreFixedPoint t) -> PreFixedPoint (inf S)).
intros S C.
unfold PreFixedPoint in *.
apply (PinfL ). intros l Sl.
apply Ole_trans with (y:= f l).
assert (monotonic f) as M by auto. apply M.
apply Pinf. apply Sl.
apply (C _ Sl).
Qed.

Definition PreFixedLattice := @sub_clatType L (fun x => PreFixedPoint x) PreFixedInfs.

Definition PostFixedPoint d := d <= f d.

Lemma PostFixedSups: forall S : op_latType -> Prop,
        (forall t : op_latType, S t -> (fun x : op_latType => PostFixedPoint x) t) ->
        (fun x : op_latType => PostFixedPoint x) (@inf op_latType S).
unfold PostFixedPoint.
intros S C. simpl in *. refine (PsupL _).
intros l Sl. apply Ole_trans with (y:= f l). apply C. apply Sl.
assert (monotonic f) as M by auto. apply M. apply (Psup Sl).
Qed.

Definition PostFixedLattice := @sub_clatType op_latType (fun x => PostFixedPoint x) PostFixedSups.

Definition lfp := match (@inf PreFixedLattice (fun _ => True)) with exist x _ => x end.

Definition gfp := match (@inf PostFixedLattice (fun _ => True)) with exist x _ => x end.

Lemma lfp_fixedpoint : f lfp =-= lfp.
unfold lfp.
assert (yy:= @Pinf PreFixedLattice (fun _ => True)).
generalize yy ; clear yy.
case (@inf PreFixedLattice (fun _ => True)).
intros x Px yy.
assert (zz:=fun X PX => (yy (exist (fun t => PreFixedPoint t) X PX))). clear yy.
assert (PreFixedPoint (f x)). unfold PreFixedPoint.
assert (monotonic f) as M by auto. apply M. apply Px.
split ; first by apply Px.
simpl in zz. specialize (zz _ H I). by apply zz.
Qed.

Lemma gfp_fixedpoint : f gfp =-= gfp.
unfold gfp.
assert (yy:= @Pinf PostFixedLattice (fun _ => True)).
generalize yy ; clear yy.
case (@inf PostFixedLattice (fun _ => True)).
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
assert (yy:= @Pinf PreFixedLattice (fun _ => True)).
generalize yy ; clear yy.
case (@inf PreFixedLattice (fun _ => True)).
intros x Px yy.
assert (zz:=fun X PX => (yy (exist (fun t => PreFixedPoint t) X PX))). clear yy.
case (@inf PreFixedLattice (fun _ : PreFixedLattice => True)).
specialize (zz _ H). simpl in zz. intros _ _. by apply zz.
Qed.

Lemma gfp_greatest: forall fp, fp <= f fp -> fp <= gfp.
unfold gfp.
intros fp ff. assert (PostFixedPoint fp). apply ff.
assert (yy:= @Pinf PostFixedLattice (fun _ => True)).
generalize yy ; clear yy.
case (@inf PostFixedLattice (fun _ => True)).
intros x Px yy.
assert (zz:=fun X PX => (yy (exist (fun t => PostFixedPoint t) X PX))). clear yy.
case (@inf PostFixedLattice (fun _ : PostFixedLattice => True)).
specialize (zz _ H). simpl in zz. intros _ _. by apply zz.
Qed.

End KnasterTarski.

Section ClatProd.

Variable L1 L2 : clatType.

Lemma prodCLatAxiom : CLattice.axiom (fun (S:L1 * L2 -> Prop) =>
               (@inf L1 (fun l1 => exists l2, S (l1,l2)),@inf L2 (fun l2 => exists l1, S (l1,l2)))).
move => P t. split.
- case t. clear t. intros t0 t1 Pt. simpl. split.
  * refine (Pinf _). exists t1. by apply Pt.
  * refine (Pinf _). exists t0. by apply Pt.
- case t. clear t. intros t0 t1 Pt. simpl. split.
  * refine (PinfL _). intros x Px. destruct Px as [y Pxy]. specialize (Pt _ Pxy).
    inversion Pt. simpl in *. by auto.
  * refine (PinfL _). intros x Px. destruct Px as [y Pyx].
    specialize (Pt _ Pyx). inversion Pt. simpl in *. by auto.
Qed.

Canonical Structure prod_clatMixin := ClatMixin prodCLatAxiom.
Canonical Structure prod_clatType := Eval hnf in ClatType prod_clatMixin.

Lemma Fst_lp : limitpres (@Fst L1 L2).
move => S. unfold imageSet. simpl. apply: inf_ext.
move => x. split ; case.
- move => y iS. exists (x,y). by split.
- case => x' y. simpl. case => iS e. exists y. by rewrite <- e.
Qed.

Definition lfst := Eval hnf in mk_flimit Fst_lp.

Lemma Snd_lp : limitpres (@Snd L1 L2).
move => S. unfold imageSet. simpl. apply: inf_ext.
move => x. split ; case.
- move => y iS. exists (y,x). by split.
- case => x' y. simpl. case => iS e. exists x'. by rewrite <- e.
Qed.

Definition lsnd := Eval hnf in mk_flimit Snd_lp.

Variable L:clatType.
Variable (f:L =-> L1) (g:L =-> L2).

Lemma prod_fun_lp : limitpres (<|f:ordCatType _ _,g|>).
move => S. simpl. rewrite -> (pair_eq_compat (flimitpres f S) (flimitpres g S)).
case_eq (inf (imageSet (<| (f : ordCatType _ _), g |>) S)).
move => l0 l1 e. unfold imageSet in e. simpl in e. apply: pair_eq_compat.
- have aa:=f_equal (Fst _ _) e. simpl in aa. rewrite <- aa. apply: inf_ext. move => x. unfold imageSet.
  split ; case.
  + move => x1 [iS ee]. exists (g x1). exists x1. split ; first by []. by rewrite ee.
  + move => x3. case => x1 [iS ee]. exists x1. by split ; case: ee.
- have aa:=f_equal (Snd _ _) e. simpl in aa. rewrite <- aa. apply: inf_ext. move => x. unfold imageSet.
  split ; case.
  + move => x1 [iS ee]. exists (f x1). exists x1. split ; first by []. by rewrite ee.
  + move => x3. case => x1 [iS ee]. exists x1. by split ; case: ee.
Qed.

Definition lprod_fun : L =-> prod_clatType :=
  Eval hnf in mk_flimit prod_fun_lp.

End ClatProd.

Lemma clatProdCatAxiom : CatProduct.axiom lfst lsnd lprod_fun.
move => X Y Z f g. split ; first split.
- by apply: fmon_eq_intro.
- by apply: fmon_eq_intro.
- move => m A. apply: fmon_eq_intro => x.
  simpl. have A0:=fmon_eq_elim (proj1 A) x. have A1:=fmon_eq_elim (proj2 A) x. by rewrite <- (pair_eq_compat A0 A1).
Qed.

Canonical Structure prod_clatCatMixin := prodCatMixin clatProdCatAxiom.
Canonical Structure prod_clatCatType := Eval hnf in prodCatType prod_clatCatMixin.

Lemma arrow_latAxiom (T:Type) (L:clatType) : @CLattice.axiom (ford_ordType T L)
   (fun (S:ford_ordType T L -> Prop) => fun t => @inf L (fun st => exists s, S s /\ s t = st)).
intros  P f. split.
- move => Pf. simpl. intros t. refine (Pinf _ ). exists f. by split.
- simpl. intros C t. refine (PinfL _).
  intros l Tl. destruct Tl as [f0 [Pf0 f0t]]. specialize (C _ Pf0). by rewrite <- f0t.
Qed.

Canonical Structure arrow_clatMixin (T:Type) (L:clatType) := ClatMixin (@arrow_latAxiom T L).
Canonical Structure arrow_clatType (T:Type) (L:clatType) := Eval hnf in @ClatType (ford_ordType T L) (@arrow_clatMixin T L).

Require Export NSetoid.
Open Scope C_scope.

Lemma setOrdAxiom T : @PreOrd.axiom (T =-> Props) (fun A B => forall x, A x -> B x).
move => c. split ; first by [].
move => y z A B a Ca. apply B. by apply A.
Qed.

Canonical Structure set_ordMixin T := OrdMixin (@setOrdAxiom T).
Definition set_ordType T := Eval hnf in OrdType (set_ordMixin T).

Lemma intersect_respect T (S:(T =-> Props) -> Prop) : setoid_respect (fun t, forall A, S A -> A t).
move => x y e. simpl.
split => X A sa ; specialize (X A sa).
- by apply (proj1 (frespect A e)).
- by apply (proj2 (frespect A e)).
Qed.

Definition intersect T (S:(T =-> Props) -> Prop) : T =-> Props := Eval hnf in mk_fset (intersect_respect S).

Lemma set_clatAxiom T : @CLattice.axiom (set_ordType T) (fun S => intersect S).
move => P x. split.
- move => iP a A. by apply (A x).
- move => A a ix B Pb. by apply (A B Pb a ix).
Qed.

Canonical Structure set_clatMixin T := ClatMixin (@set_clatAxiom T).
Definition set_clatType T := Eval hnf in @ClatType (@set_ordType T) (@set_clatMixin T).

Definition set_ordSupType T := Eval hnf in op_ordType (set_ordType T).
Definition set_clatSubType T := Eval hnf in op_latType (@set_clatType T).




