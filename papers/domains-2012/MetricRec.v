(**********************************************************************************
 * MetricRec.v                                                                    *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                       *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)

(* Categories enriched over bounded complete ultrametric spaces and solving domain
   equations therein
*)

Require Export Categories MetricCore NSetoid.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** printing T0 %\ensuremath{T_0}% *)
(** printing T1 %\ensuremath{T_1}% *)
(** printing T2 %\ensuremath{T_2}% *)
(** printing T3 %\ensuremath{T_3}% *)
(** printing T4 %\ensuremath{T_4}% *)
(** printing T5 %\ensuremath{T_5}% *)
(** printing T6 %\ensuremath{T_6}% *)

Open Scope C_scope.

(*=BaseCat *)
Module BaseCat.

Record mixin_of (C:catType) := Mixin
 { terminal :> CatTerminal.mixin_of C;
   metric : forall (X Y : C),
      Metric.mixin_of (Setoid.Pack (Setoid.class (C X Y)) (C X Y));
   cmetric : forall (X Y : C),
      CMetric.mixin_of (Metric.Pack (Metric.Class (metric X Y)) (C X Y)) ;
   comp: forall (X Y Z : C), (CMetric.Pack (CMetric.Class (cmetric Y Z)) (C Y Z)) *
          (CMetric.Pack (CMetric.Class (cmetric X Y)) (C X Y)) =-> 
          (CMetric.Pack (CMetric.Class (cmetric X Z)) (C X Z));
   comp_comp : forall X Y Z m m', (comp X Y Z (m,m'):C _ _) =-= m << m' }.
(*=End *)

Section ClassDef.
Record class_of (T:Type) (M:T -> T -> setoidType) : Type := 
  Class { base : Category.class_of M;
          ext: mixin_of (Category.Pack base T) }.
Local Coercion base : class_of >-> Category.class_of.
Local Coercion ext : class_of >-> mixin_of.

Definition base2 (T:Type) (M:T -> T -> setoidType) (c:class_of M) := CatTerminal.Class c.
Local Coercion base2 : class_of >-> CatTerminal.class_of.

Structure cat : Type := Pack {object : Type; morph : object -> object -> setoidType ; _ : class_of morph; _ : Type}.
Local Coercion object : cat >-> Sortclass.
Local Coercion morph : cat >-> Funclass.
Definition class cT := let: Pack _ _ c _ := cT return class_of (@morph cT) in c.
Definition unpack (K:forall O (M:O -> O -> setoidType) (c:class_of M), Type)
            (k : forall O (M: O -> O -> setoidType) (c : class_of M), K _ _ c) (cT:cat) :=
  let: Pack _ M c _ := cT return @K _ _ (class cT) in k _ _ c.
Definition repack cT : _ -> Type -> cat := let k T M c p := p c in unpack k cT.
Definition pack := let k T M c m := Pack (@Class T M c m) T in Category.unpack k.

Definition terminalCat (cT:cat) : terminalCat := CatTerminal.Pack (class cT) cT.
Definition catType (cT:cat) : catType := Category.Pack (class cT) cT.
Definition metricType (cT:cat) (X Y:cT) : metricType := Metric.Pack (Metric.Class (metric (class cT) X Y)) (cT X Y).
Definition cmetricType (cT:cat) (X Y:cT) : cmetricType := CMetric.Pack (CMetric.Class (cmetric (class cT) X Y)) (cT X Y).
End ClassDef.
Module Import Exports.
Coercion terminalCat : cat >-> CatTerminal.cat.
Coercion base : class_of >-> Category.class_of.
Coercion ext : class_of >-> mixin_of.
Coercion object : cat >-> Sortclass.
Coercion morph : cat >-> Funclass.
Canonical Structure terminalCat.
Canonical Structure catType.
Canonical Structure metricType.
Canonical Structure cmetricType.

Notation cmetricMorph := cmetricType.
Notation cmetricECat := cat.
Notation CmetricECatMixin := Mixin.
Notation CmetricECatType := pack.
End Exports.
End BaseCat.
Export BaseCat.Exports.

Definition ccomp (cT:cmetricECat) (X Y Z : cT) : cmetricMorph Y Z * cmetricMorph X Y =-> cmetricMorph X Z :=
   BaseCat.comp (BaseCat.class cT) X Y Z.

Lemma ccomp_eq (cT:cmetricECat) (X Y Z : cT) (f : cT Y Z) (f' : cT X Y) : ccomp X Y Z (f,f') =-= f << f'.
apply (@BaseCat.comp_comp cT (BaseCat.class cT) X Y Z f f').
Qed.

Section Msolution.
Variable M:cmetricECat.

Open Scope C_scope.
Open Scope S_scope.

(*=BiFunctor *)
Record BiFunctor : Type := mk_functor
{ ob : M -> M -> M ;
  morph : forall (T0 T1 T2 T3 : M),
             (cmetricMorph T1 T0) * (cmetricMorph T2 T3) =->
             (cmetricMorph (ob T0 T2) (ob T1 T3)) ;
  morph_comp: forall T0 T1 T2 T3 T4 T5
             (f:cmetricMorph T4 T1) (g:cmetricMorph T3 T5) 
             (h:cmetricMorph T1 T0) (k:cmetricMorph T2 T3),
                (morph T1 T4 T3 T5 (f,g)) <<  morph T0 T1 T2 T3 (h, k) 
                 =-= morph _ _ _ _ (h << f, g << k) ;
  morph_id : forall T0 T1, morph T0 _ T1 _ (Id , Id) =-= Id}.

(*=End *)

(*=Tower *)
Definition retract (T0 T1 : M) (f: T0 =-> T1) (g: T1 =-> T0) := g << f =-= Id.

Record Tower : Type := mk_tower
{ tobjects : nat -> M;
  tmorphisms : forall i, tobjects (S i) =-> (tobjects i);
  tmorphismsI : forall i, (tobjects i) =-> (tobjects (S i));
  tretract : forall i, retract (tmorphismsI i) (tmorphisms i);
  tlimitD : forall n i, n <= i -> 
    (tmorphismsI i << tmorphisms i : cmetricMorph _ _) = n = Id}.

(*=End *)

(*=Cone *)
Record Cone (To:Tower) : Type := mk_basecone
{ tcone :>  M;
  mcone : forall i, tcone =-> (tobjects To i);
  mconeCom : forall i, tmorphisms To i << mcone (S i) =-= mcone i }.
(*=End *)
  
Record CoCone (To:Tower) : Type := mk_basecocone
{ tcocone :> M;
  mcocone : forall i, (tobjects To i) =-> tcocone;
  mcoconeCom : forall i, mcocone (S i) << tmorphismsI To i =-= mcocone i }.

(*=Limit *)
Record Limit (To:Tower) : Type := mk_baselimit
{ lcone :> Cone To;
  limitExists : forall (A:Cone To), (tcone A) =-> (tcone lcone);
  limitCom : forall (A:Cone To), forall n, mcone A n =-= mcone lcone n << limitExists A;
  limitUnique : forall (A:Cone To) (h: (tcone A) =-> (tcone lcone))
     (C:forall n, mcone A n =-= mcone lcone n << h), h =-= limitExists A }.
(*=End *)
Record CoLimit (To:Tower) : Type := mk_basecolimit
{ lcocone :> CoCone To;
  colimitExists : forall (A:CoCone To), (tcocone lcocone) =-> (tcocone A) ;
  colimitCom : forall (A:CoCone To), forall n, mcocone A n =-= colimitExists A << mcocone lcocone n;
  colimitUnique : forall (A:CoCone To) (h: (tcocone lcocone) =-> (tcocone A))
     (C:forall n, mcocone A n =-= h << mcocone lcocone n), h =-= colimitExists A }.

Variable L:forall T:Tower, Limit T.

Section RecursiveDomains.

Variable F : BiFunctor.

Add Parametric Morphism C X Y Z W : (fun (x: _ =-> _) (y: _ =-> _) => @morph C X Y Z W (pair x y))
  with signature (@tset_eq _) ==> (@tset_eq _) ==> (@tset_eq _)
  as morph_eq_compat.
move => x x' e y y' e'. apply: (frespect (morph C X Y Z W)). by split.
Qed.

Lemma BiFuncRtoR: forall (T0 T1:M) (f: T0 =-> T1) (g: T1 =-> T0), retract f g ->
          retract (morph F _ _ _ _ (g,f)) (morph F _ _ _ _ (f,g)).
move => A B f g X. unfold retract.
- rewrite -> morph_comp. rewrite -> (morph_eq_compat F X X).
  by rewrite morph_id.
Qed.

Section Tower.

Variable DTower : Tower.

Lemma lt_gt_dec n m : (n < m) + (m = n) + (m < n).
case: (ltngtP m n) => e.
by right.
left. by left.
left. by right.
Qed.

Definition Diter_coercion n m (Eq:n = m) : M (tobjects DTower n) (tobjects DTower m).
rewrite Eq.  by apply: Id.
Defined.

Lemma leqI m n : (m <= n)%N = false -> n <= m.
move => I. have t:=(leq_total m n). rewrite I in t. by apply t.
Qed.

Lemma lt_subK n m : m < n -> n = (n - m + m)%N.
move => l. apply sym_eq. apply subnK. have x:= (leqnSn m). by apply (leq_trans x l).
Qed.

Fixpoint Projection_nm m (n:nat) : (tobjects DTower (n+m)) =-> (tobjects DTower m) :=
match n as n0 return (tobjects DTower (n0+m)) =-> (tobjects DTower m) with
| O => Id
| S n => Projection_nm m n << tmorphisms DTower (n+m)%N
end.

Fixpoint Injection_nm m (n:nat) : (tobjects DTower m) =-> (tobjects DTower (n+m)) :=
match n as n0 return (tobjects DTower m) =-> (tobjects DTower (n0+m)) with
| O => Id
| S n => tmorphismsI DTower (n+m) << Injection_nm m n
end.

Definition t_nm n m : (tobjects DTower n) =-> (tobjects DTower m) :=
match (lt_gt_dec m n) return (tobjects DTower n) =-> (tobjects DTower m) with
| inl (inl ee) => (Projection_nm m (n - m)%N) << (Diter_coercion (lt_subK ee))
| inl (inr ee) => Diter_coercion ee : (tobjects DTower n) =-> (tobjects DTower m)
| inr ee => Diter_coercion (sym_eq (lt_subK ee)) << Injection_nm n (m - n)
end.

Lemma Diter_coercion_simpl: forall n (Eq:n = n), Diter_coercion Eq = Id.
intros n Eq. by rewrite (eq_irrelevance Eq (refl_equal _)).
Qed.

Lemma Proj_left_comp : forall k m, Projection_nm m (S k) =-= 
                      tmorphisms DTower m << Projection_nm (S m) k << Diter_coercion (sym_eq (addnS k m)).
elim.
- move => m. simpl.
  rewrite comp_idL. rewrite comp_idR.
  rewrite (Diter_coercion_simpl). by rewrite -> comp_idR.
- move => n IH m. simpl. simpl in IH. rewrite -> IH.
  have P:=(sym_eq (addnS n m)). rewrite (eq_irrelevance (sym_eq (addnS n m)) P).
  have Q:=(sym_eq (addnS n.+1 m)). rewrite (eq_irrelevance (sym_eq (addnS n.+1 m)) Q).
  move: P Q. unfold addn. simpl. fold addn. move => P. generalize P. rewrite P. clear P.
  move => P Q. do 2 rewrite Diter_coercion_simpl.
  do 2 rewrite comp_idR. clear P Q. by rewrite comp_assoc.
Qed.

Lemma Inject_right_comp: forall k m, Injection_nm m (S k) =-=
           Diter_coercion (addnS k m) << Injection_nm (S m) k << tmorphismsI DTower m.
elim.
- move => m. simpl. do 2 rewrite comp_idR. rewrite (Diter_coercion_simpl). by rewrite -> comp_idL.
- move => n IH m. simpl. simpl in IH. rewrite -> IH. clear IH.
  have P:= (addnS n.+1 m). have Q:=(addnS n m). rewrite -> (eq_irrelevance _ P).
  rewrite -> (eq_irrelevance _ Q). move: P Q. unfold addn. simpl. fold addn.
  move => P Q. generalize P Q. rewrite <- Q. clear P Q. move => P Q. do 2 rewrite Diter_coercion_simpl.
  do 2 rewrite comp_idL. by rewrite comp_assoc.
Qed.

Lemma Diter_coercion_comp: forall x y z (Eq1:x = y) (Eq2 : y = z), 
     Diter_coercion Eq2 << Diter_coercion Eq1 =-= Diter_coercion (trans_equal Eq1 Eq2).
intros x y z Eq1. generalize Eq1. rewrite Eq1. clear x Eq1.
intros Eq1 Eq2. generalize Eq2. rewrite <- Eq2. clear Eq2. intros Eq2.
repeat (rewrite Diter_coercion_simpl). by rewrite -> comp_idL.
Qed.

Lemma Diter_coercion_eq n m (e e': n = m) : Diter_coercion e =-= Diter_coercion e'.
by rewrite (eq_irrelevance e e').
Qed.

Lemma lt_gt_dec_lt n m : n < m -> exists e, lt_gt_dec n m = inl _ (inl _ e).
move => e. case_eq (lt_gt_dec n m) ; first case.
- move => i _. by exists i.
- move => f. rewrite f in e. by rewrite ltnn in e.
- move => f. have a:=leq_trans (leqnSn _) f. have Fx:=leq_ltn_trans a e. by rewrite ltnn in Fx.
Qed.

Lemma lt_gt_dec_gt n m : m < n -> exists e, lt_gt_dec n m = (inr _ e).
move => e. case_eq (lt_gt_dec n m) ; first case.
- move => i _. have a:=leq_trans (leqnSn _) i. have Fx:=leq_ltn_trans a e. by rewrite ltnn in Fx.
- move => f. rewrite f in e. by rewrite ltnn in e.
- move => i _. by exists i.
Qed.

Lemma lt_gt_dec_eq n m : forall e : m = n, lt_gt_dec n m = (inl _ (inr _ e)).
move => e. generalize e. rewrite e. clear e m. move => e. case_eq (lt_gt_dec n n) ; first case.
- move => i _. have f:=i. by rewrite ltnn in f.
- move => f _. by rewrite (eq_irrelevance e f).
- move => i _. have f:=i. by rewrite ltnn in f.
Qed.

Lemma t_nmProjection: forall n m, t_nm n m =-= tmorphisms DTower m << t_nm n (S m).
move => n m. unfold t_nm. case (lt_gt_dec m n) ; first case.
- case (lt_gt_dec m.+1 n) ; first case.
  + move => l l'. rewrite comp_assoc.
    have X:=Proj_left_comp (n - m.+1) m. have XX:= addnS (n - m.+1) m.
    have Y:=comp_eq_compat X (tset_refl (Diter_coercion XX)).
    repeat (rewrite <- comp_assoc in Y). rewrite -> Diter_coercion_comp in Y.
    rewrite Diter_coercion_simpl in Y. rewrite -> comp_idR in Y. rewrite <- Y.
    rewrite <- comp_assoc. rewrite Diter_coercion_comp.
    have P:=(trans_equal (lt_subK l) XX). have Q:=(lt_subK l').
    rewrite -> (eq_irrelevance _ P). rewrite -> (eq_irrelevance _ Q).
    generalize P. have e:= (ltn_subS l'). have ee:(n - m).-1 = (n - m.+1). by rewrite e.
    rewrite <- ee. clear ee e P. have e:0 < n - m. rewrite <- ltn_add_sub. by rewrite addn0.
    move => P.  have PP:n = ((n - m).-1.+1 + m)%N. rewrite (ltn_predK e). apply Q.
    rewrite (eq_irrelevance P PP). move: PP. rewrite (ltn_predK e). clear. move => PP.
    by rewrite (eq_irrelevance Q PP).
  + move => e. generalize e. rewrite e. clear n e. move => e i. have x:= subSnn m.
    have a:=(lt_subK (n:=m.+1) (m:=m) i). rewrite (eq_irrelevance (lt_subK (n:=m.+1) (m:=m) i) a).
    move: a. rewrite x. clear x. move => a. rewrite (eq_irrelevance e a). simpl. by rewrite comp_idL.
  + move => i j. have Fx:=leq_trans i j. by rewrite ltnn in Fx.
- move => e. generalize e. rewrite e. clear n e. move => e. destruct (lt_gt_dec_gt (leqnn (S m))) as [p A].
  rewrite A. clear A.
  have ee:=subSnn m. have x:=(sym_eq (lt_subK (n:=m.+1) (m:=m) p)).
  rewrite <- (eq_irrelevance x (sym_eq (lt_subK (n:=m.+1) (m:=m) p))). move: x. rewrite ee. simpl.
  move => x. do 2 rewrite (Diter_coercion_simpl). rewrite comp_idL. rewrite comp_idR.
  unfold addn. simpl. by rewrite -> (tretract DTower m).
- move => i. have l:=leq_trans i (leqnSn m). destruct (lt_gt_dec_gt l) as [p A]. rewrite A. clear A l.
  have x:=(sym_eq (lt_subK (n:=m.+1) (m:=n) p)). rewrite (eq_irrelevance (sym_eq (lt_subK (n:=m.+1) (m:=n) p)) x).
  move: x. rewrite leq_subS ; last by []. simpl. move => x. do 2 rewrite comp_assoc.
  refine (comp_eq_compat _ (tset_refl _)). have y:=(sym_eq (lt_subK (n:=m) (m:=n) i)).
  rewrite (eq_irrelevance (sym_eq (lt_subK (n:=m) (m:=n) i)) y). have a:=(trans_eq (sym_eq (addSn _ _)) x).
  rewrite (eq_irrelevance x a).
  apply tset_trans with (y:=(tmorphisms DTower m << Diter_coercion a) << tmorphismsI DTower (m - n + n)) ; last by [].
  move: a. generalize y. rewrite -> y. clear. move => y a. do 2 rewrite Diter_coercion_simpl.
  rewrite comp_idR. by rewrite (tretract DTower m).
Qed.

Lemma t_nn_ID: forall n, t_nm n n =-= Id.
intros n.
unfold t_nm. rewrite (lt_gt_dec_eq (refl_equal n)). by rewrite Diter_coercion_simpl.
Qed.

Lemma t_nmProjection2 n m : (m <= n) % nat -> t_nm (S n) m =-= (t_nm n m) << tmorphisms DTower n.
move => nm.
assert (exists x, n - m = x) as X by (exists (n - m) ; auto).
destruct X as [x X]. elim: x n m X nm.
- move => n m E EE. have e:=eqn_leq n m. rewrite EE in e. have l:(n <= m)%N. unfold leq. by rewrite E.
  rewrite l in e. have ee:=eqP e. rewrite ee. rewrite t_nn_ID. rewrite comp_idL.
  rewrite -> t_nmProjection. rewrite t_nn_ID. by rewrite comp_idR.
- move => nm IH. case ; first by []. move => n m e l. have ll:n.+1 - m > 0 by rewrite e. rewrite subn_gt0 in ll.
  rewrite leq_subS in e ; last by []. specialize (IH n m). have ee: n - m = nm by auto.
  rewrite -> (IH ee ll).
  clear IH. have l0:=leq_trans ll (leqnSn _). destruct (lt_gt_dec_lt l0) as [p A].
  unfold t_nm. rewrite A. clear A. case_eq (lt_gt_dec m n) ; first case.
  + move => p' _. have x:=(lt_subK (n:=n.+2) (m:=m) p). rewrite (eq_irrelevance (lt_subK (n:=n.+2) (m:=m) p) x).
    move: x. have x:n.+2 - m = (n-m).+2. rewrite leq_subS ; last by []. rewrite leq_subS ; by [].
    rewrite x. clear x. move => x. simpl. do 4 rewrite <- comp_assoc. refine (comp_eq_compat (tset_refl _) _).
    have x':=(lt_subK (n:=n) (m:=m) p'). rewrite (eq_irrelevance (lt_subK (n:=n) (m:=m) p') x').
    have x1:((n - m).+2 + m)%N = ((n - m) + m).+2 by [].
    have x2:=trans_eq x x1.
    apply tset_trans with (y:=tmorphisms DTower (n - m + m) << (tmorphisms DTower (S(n - m + m)) << Diter_coercion x2)) ; 
    first by simpl ; rewrite (eq_irrelevance x2 x).
    move: x2. generalize x' ; rewrite <- x'. clear x' x x1 p p'. move => x x'. do 2 rewrite (Diter_coercion_simpl).
    rewrite comp_idR. by rewrite -> comp_idL.
  + move => e'. generalize e'. move: p. rewrite e'. clear e' n l ll e l0 ee. move => p e _.
    rewrite (Diter_coercion_simpl). rewrite comp_idL.
    have x:=(lt_subK (n:=m.+2) (m:=m) p).
    have ee:(m.+2 - m) = (m - m).+2. rewrite leq_subS ; last by []. rewrite leq_subS ; by [].
    rewrite (eq_irrelevance (lt_subK (n:=m.+2) (m:=m) p) x). generalize x. rewrite ee. clear ee. rewrite subnn.
    move => xx. clear x e p. simpl. rewrite comp_idL.
    rewrite (Diter_coercion_simpl). by rewrite -> comp_idR.
  + move => f. have lx:=leq_trans f ll. by rewrite ltnn in lx.
Qed.

Lemma t_nmEmbedding: forall n i, t_nm n i =-= (t_nm (S n) i) << tmorphismsI DTower n.
intros n m. unfold t_nm. case (lt_gt_dec m n) ; first case.
- move => i. have l:=leq_trans i (leqnSn _). destruct (lt_gt_dec_lt l) as [p A]. rewrite A. clear A l.
  have x:=((lt_subK p)). rewrite (eq_irrelevance ((lt_subK p)) x).
  move: x. rewrite leq_subS ; last by []. simpl. move => x. do 2 rewrite <- comp_assoc.
  refine (comp_eq_compat (tset_refl _) _). have y:=((lt_subK i)).
  rewrite (eq_irrelevance ((lt_subK i)) y). have a:=(trans_eq x ((addSn _ _))).
  rewrite (eq_irrelevance x a).
  apply tset_trans with (y:=tmorphisms DTower (n - m + m) << (Diter_coercion a << tmorphismsI DTower n)) ; last by [].
  move: a. generalize y. rewrite <- y. clear. move => y a. do 2 rewrite Diter_coercion_simpl.
  rewrite comp_idL. by rewrite <- (tretract DTower n).
- move => e. generalize e. rewrite e. clear n e. move => e. destruct (lt_gt_dec_lt (leqnn (S m))) as [p A].
  rewrite A. clear A.
  have ee:=subSnn m. have x:=((lt_subK (n:=m.+1) (m:=m) p)).
  rewrite <- (eq_irrelevance x ((lt_subK (n:=m.+1) (m:=m) p))). move: x. rewrite ee. simpl.
  move => x. do 2 rewrite (Diter_coercion_simpl). rewrite comp_idR. rewrite comp_idL.
  by rewrite -> (tretract DTower m).
- case (lt_gt_dec m n.+1) ; first case.
  + move => i j. have Fx:=leq_trans i j. by rewrite ltnn in Fx.
  + move => e. generalize e. rewrite <- e. clear m e. move => e i. have x:= subSnn n.
    have a:=(lt_subK i). rewrite (eq_irrelevance (lt_subK i) a).
    move: a. rewrite x. clear x. move => a. rewrite (eq_irrelevance (sym_eq a) e).
    simpl. by rewrite comp_idR.
  + move => l l'. rewrite <- comp_assoc. have X:=Inject_right_comp (m - n.+1) n. have XX:= sym_eq (addnS (m - n.+1) n).
    have Y:=comp_eq_compat (tset_refl (Diter_coercion XX)) X. rewrite -> comp_assoc in Y.
    rewrite -> (comp_assoc (Injection_nm _ _)) in Y. rewrite -> Diter_coercion_comp in Y.
    rewrite Diter_coercion_simpl in Y. rewrite -> comp_idL in Y. rewrite <- Y.
    rewrite comp_assoc. rewrite Diter_coercion_comp.
    have ee:=(trans_equal XX (sym_eq (lt_subK l))). rewrite -> (eq_irrelevance _ ee).
    clear XX X Y. have e:m - n.+1 = (m - n).-1. by rewrite (ltn_subS l').
    move: ee. rewrite -> e. have ll:0 < (m - n). rewrite <- ltn_add_sub. by rewrite addn0.
    move => Q.
    have PP:((m - n).-1.+1 + n)%N = m. rewrite -> (ltn_predK ll). by rewrite (sym_eq (lt_subK l')).
    rewrite (eq_irrelevance Q PP). move: PP. have P:=(sym_eq (lt_subK l')). rewrite -> (eq_irrelevance _ P).
    move: P. clear Q. clear e. move => P Q. move: P. rewrite -{1 2 3 4} (ltn_predK ll).
    move => P. by rewrite (eq_irrelevance P Q).
Qed.

Lemma t_nmEmbedding2: forall n m, (n <= m) % nat -> t_nm n (S m) =-= tmorphismsI DTower m << t_nm n m.
move => n m nm.
assert (exists x, m - n = x) as X by (eexists ; apply refl_equal).
destruct X as [x X]. elim: x n m X nm.
- move => n m E EE. have e:=eqn_leq n m. rewrite EE in e. have l:(m <= n)%N. unfold leq. by rewrite E.
  rewrite l in e. have ee:=eqP e. rewrite ee. rewrite -> t_nn_ID. rewrite comp_idR.
  rewrite -> t_nmEmbedding. rewrite t_nn_ID. by rewrite comp_idL.
- move => nm IH. move => n. case ; first by []. move => m e l. have ll:m.+1 - n > 0 by rewrite e. rewrite subn_gt0 in ll.
  rewrite leq_subS in e ; last by []. specialize (IH n m). have ee:m - n = nm by auto.
  rewrite (IH ee ll). clear IH. have l0:=leq_trans ll (leqnSn _). destruct (lt_gt_dec_gt l0) as [p A].
  unfold t_nm. rewrite A. clear A. case_eq (lt_gt_dec m n) ; first case.
  + move => f. have lx:=leq_trans f ll. by rewrite ltnn in lx.
  + move => e'. generalize e'. move: p. rewrite e'. clear e' n l ll e l0 ee. move => p e _.
    rewrite (Diter_coercion_simpl). rewrite comp_idR. have x:=(lt_subK p).
    have ee:(m.+2 - m) = (m - m).+2. rewrite leq_subS ; last by []. rewrite leq_subS ; by [].
    rewrite (eq_irrelevance (lt_subK (n:=m.+2) (m:=m) p) x). generalize x. rewrite ee. clear ee. rewrite subnn.
    move => xx. clear x e p. simpl. rewrite (Diter_coercion_simpl). rewrite -> comp_idL. by rewrite comp_idR.
  + move => p' _. have x:=(lt_subK p). rewrite (eq_irrelevance (lt_subK p) x).
    move: x. have x:m.+2 - n = (m-n).+2. rewrite leq_subS ; last by []. rewrite leq_subS ; by [].
    rewrite x. clear x. move => x. simpl. do 4 rewrite -> comp_assoc. refine (comp_eq_compat _ (tset_refl _)).
    have x':=sym_eq(lt_subK p'). rewrite (eq_irrelevance (sym_eq (lt_subK _)) x').
    have x1:((m - n).+2 + n)%N = ((m - n) + n).+2 by [].
    have x2:=sym_eq (trans_eq x x1).
    apply tset_trans with (y:=(Diter_coercion x2 << tmorphismsI DTower (S (m - n + n))) << tmorphismsI DTower ((m - n + n))) ; 
    first by simpl ; rewrite (eq_irrelevance x2 (sym_eq x)).
    move: x2. generalize x' ; rewrite x'. clear x' x x1 p p'. move => x x'. do 2 rewrite (Diter_coercion_simpl).
    rewrite -> comp_idR. by rewrite comp_idL.
Qed.

Lemma t_nm_EP i n : (i <= n)%N -> retract (t_nm i n) (t_nm n i).
 have e:exists x, x == n - i by eexists.
case: e => x e. elim: x i n e.
- move => i n e l. have ee:i = n. apply anti_leq. rewrite l. simpl. unfold leq. by rewrite <- (eqP e).
  rewrite -> ee. unfold retract. rewrite -> t_nn_ID. by rewrite comp_idL.
- move => x IH i. case ; first by rewrite sub0n.
  move => n e l. have ll:(i <= n)%N. have aa:0 < n.+1 - i. by rewrite <- (eqP e). rewrite subn_gt0 in aa. by apply aa.
  clear l. specialize (IH i n). rewrite (leq_subS ll) in e. specialize (IH e ll). unfold retract.
  rewrite (t_nmProjection2 ll). rewrite -> (t_nmEmbedding2 ll). rewrite comp_assoc.
  rewrite <- (comp_assoc (tmorphismsI _ _)). rewrite (tretract DTower n). rewrite comp_idR. by apply (IH).
Qed.

Add Parametric Morphism A B C n : (@Category.comp M A B C)
  with signature (fun x y => @Mrel (cmetricMorph B C) n x y) ==> (fun x y => @Mrel (cmetricMorph A B) n x y) ==>
     (fun x y => @Mrel (cmetricMorph A C) n x y)
  as comp_neq_compat.
move => x y e x' y' e'.
rewrite <- (ccomp_eq x). rewrite <- (proj2 (Mrefl (ccomp _ _ _ (y,y')) _) (ccomp_eq y y') n).
apply: fnonexpansive. by split.
Qed.

Lemma chainPEp (C:CoCone DTower) (C':Cone DTower) : cchainp (fun n : nat => mcocone C n << mcone C' n:cmetricMorph (tcone C') (tcocone C)).
move => n i j l l'. have X:= tlimitD DTower.
have A: forall k, n <= k -> (mcocone C n << mcone C' n:cmetricMorph (tcone C') (tcocone C)) = n = (mcocone C k << mcone C' k).
- elim ; first by move => lx ; rewrite leqn0 in lx ; rewrite (eqP lx).
  move => x IH lx. case_eq (n <= x) => a.
  + specialize (IH a). refine (Mrel_trans IH _).
    have Cx:=comp_eq_compat (mcoconeCom C x) ((mconeCom C' x)).
    simpl in Cx. rewrite <- comp_assoc in Cx. rewrite -> (comp_assoc (mcone C' _)) in Cx.
    refine (Mrel_trans ((proj2 (@Mrefl (cmetricMorph (tcone C') (tcocone C)) _ _) (tset_sym Cx) n)) _). clear Cx. specialize (X _ _ a).
    apply comp_neq_compat ; first by [].
    apply Mrel_trans with (y:=Id << mcone C' x.+1) ; last by apply: (proj2 (Mrefl _ _)) ; apply: comp_idL.
    apply comp_neq_compat ; last by [].
    by apply X.
  + have b:= ltnP x n. rewrite a in b. have c:(x < n) by inversion b. clear b.
    have b:=@anti_leq n (x.+1). rewrite c in b. rewrite lx in b. specialize (b is_true_true).
    by rewrite b.
have B:=A _ l. specialize (A _ l'). by apply (Mrel_trans (Msym B) A).
Qed.

Definition chainPE (C:CoCone DTower) (C':Cone DTower) : cchain (cmetricMorph (tcone C') (tcocone C)) :=
  mk_cchain (@chainPEp C C').

Definition coneN (n:nat) : Cone DTower.
exists (tobjects DTower n) (t_nm n).
move => m. simpl. by rewrite  ->(t_nmProjection n m).
Defined.

Lemma coneCom_l (X:Cone DTower) n i : (i <= n)%nat -> mcone X i =-= t_nm n i << mcone X n.
move => l.
assert (exists x, n - i = x) as E by (eexists ; auto).
destruct E as [x E]. elim: x n i l E.
- move => n i l E. have A:=@anti_leq n i. rewrite l in A.  unfold leq in A. rewrite E in A.
  rewrite andbT in A. specialize (A (eqtype.eq_refl _)). rewrite A. clear l E A n.
  rewrite t_nn_ID. by rewrite comp_idL.
- move => x IH n i l E. rewrite -> (comp_eq_compat (t_nmProjection n i) (tset_refl _)).
  rewrite <- comp_assoc. specialize (IH n i.+1). have l0:i < n by rewrite <- subn_gt0 ; rewrite E.
  have ee:n - i.+1 = x. have Y:= subn_gt0 i n. rewrite E in Y. rewrite ltn_subS in E ; first by auto. by rewrite <- Y.
  specialize (IH l0 ee). rewrite <- IH.
  by rewrite -> (mconeCom X i).
Qed.

Lemma coconeCom_l (X:CoCone DTower) n i : (n <= i)%nat -> mcocone X n =-= mcocone X i << (t_nm n i).
move => l.
assert (exists x, i - n = x) as E by (eexists ; auto).
destruct E as [x E]. elim: x n i l E.
- move => n i l E. have A:=@anti_leq n i. rewrite l in A. unfold leq in A. rewrite E in A.
  specialize (A is_true_true). rewrite A. rewrite -> t_nn_ID. by rewrite comp_idR.
- move => x IH n i l E. rewrite -> t_nmEmbedding.
  rewrite -> comp_assoc. specialize (IH n.+1 i).
  have ll:n < i by rewrite <- subn_gt0 ; rewrite E.
  have ee:i - n.+1 = x by have Y:= subn_gt0 n i ; rewrite E in Y ;
    rewrite ltn_subS in E ; try rewrite <- Y ; by auto.
  rewrite <- (IH ll ee). by apply (tset_sym (mcoconeCom X n)).
Qed.

End Tower.

Fixpoint Diter (n:nat) :=
match n return M with
| O => One
| S n => ob F (Diter n) (Diter n)
end.

Variable tmorph_ne : One =-> (ob F One One).

Fixpoint Injection (n:nat) : (Diter n) =-> (Diter (S n)) :=
match n with
| O => tmorph_ne
| S n => morph F (Diter n) (Diter (S n)) (Diter n) (Diter (S n))
           (Projection n, Injection n)
end
with Projection (n:nat) : (Diter (S n)) =-> (Diter n) :=
match n with
| O => terminal_morph _ 
| S n => morph F (Diter (S n)) (Diter n) (Diter (S n)) (Diter n)
        (Injection n,Projection n)
end.

Lemma retract_IP: forall n, retract (Injection n) (Projection n).
elim ; first by apply: terminal_unique.
move => n IH. unfold retract. simpl. rewrite -> morph_comp.
unfold retract in IH. rewrite -> (morph_eq_compat F IH IH).
by rewrite -> morph_id.
Qed.

Lemma IP_nonexp i j n : i <= j -> (Injection i << Projection i:cmetricMorph _ _) = n = Id -> (Injection j << Projection j : cmetricMorph _ _) = n = Id.
move => l.
have M':exists m, m = j - i by eexists ; apply refl_equal. destruct M' as [m M'].
elim: m i j l M'.
- move => i j l e. have E:= (subn_eq0 j i). rewrite e in E. rewrite eqtype.eq_refl in E.
  have A:= anti_leq. specialize (A i j). rewrite l in A. rewrite <- E in A. specialize (A is_true_true).
  by rewrite A.
- move => m IH i. case ; first by [].
  move=> j l e. specialize (IH i j). have ll: 0 < j.+1 - i. by rewrite <- e.
  rewrite subn_gt0 in ll. specialize (IH ll). clear l. move => X. have I:= (IH _ X). clear IH X.
  simpl. refine (Mrel_trans (proj2 (Mrefl (_ : cmetricMorph _ _) _) (morph_comp F _ _ _ _) n) _).
  apply: (Mrel_trans _ (proj2 (Mrefl (_ : cmetricMorph _ _) _) (morph_id F _ _) n)).
  apply: fnonexpansive. split ; apply I ; rewrite leq_subS in e ; by auto.
Qed.

Variable morph_contractive : forall (T0 T1 T2 T3:M), contractive (morph F T0 T1 T2 T3).

Lemma IP_cauchy n i : n <= i -> (Injection i << Projection i:cmetricMorph (Diter i.+1) (Diter i.+1)) = n = Id.
- elim:n i ; first by [].
  move => n IH. case ; first by []. move => i l. specialize (IH i l).
  simpl. refine (Mrel_trans (proj2 (Mrefl (_ : cmetricMorph _ _) _) (morph_comp F _ _ _ _) (S n)) _).
  refine (Mrel_trans _ (proj2 (Mrefl (_ : cmetricMorph _ _) _) (morph_id F _ _) (S n))).
  apply morph_contractive. simpl. by split.
Qed.

Definition DTower := mk_tower retract_IP IP_cauchy.

(** printing DInf %\ensuremath{D_\infty}% *)
(*=DInf *)
Definition DInf : M := tcone (L DTower).
(*=End *)
Definition Embeddings n : (tobjects DTower n) =-> DInf := limitExists (L DTower) (coneN DTower n).

Definition Projections n : DInf =-> Diter n := mcone (L DTower) n.

Lemma coCom i : Embeddings i.+1 << Injection i =-= Embeddings i.
unfold Embeddings.
rewrite -> (limitUnique (h:=(Embeddings (S i) << Injection _ :  (tcone (coneN DTower i)) =-> DInf))) ; first by [].
move => m. simpl. unfold Embeddings. rewrite -> comp_assoc. have e:= (limitCom (L DTower) (coneN DTower i.+1) m).
simpl in e. rewrite <- e. by rewrite -> (t_nmEmbedding DTower).
Qed.

Definition DCoCone : CoCone DTower := @mk_basecocone _ DInf Embeddings coCom.

Lemma retract_EP n : Projections n << Embeddings n =-= Id.
unfold Projections. unfold Embeddings.
- rewrite <- (limitCom (L DTower) (coneN DTower n) n). simpl. by rewrite -> t_nn_ID.
Qed.

Lemma emp: forall i j, Projections i << Embeddings j =-= t_nm DTower j i.
intros i j. have A:= leq_total i j. case_eq (i <= j)%N ; move => X ; rewrite X in A.
- unfold Projections. rewrite -> (comp_eq_compat (coneCom_l (L DTower) X) (tset_refl _)).
  rewrite <- comp_assoc. rewrite -> (comp_eq_compat (tset_refl _) (retract_EP j)). by rewrite -> comp_idR.
- simpl in A. have e:= (coconeCom_l DCoCone A). simpl in e. rewrite -> e.
  rewrite -> comp_assoc. rewrite -> (retract_EP i). by rewrite comp_idL.
Qed.

Definition chainPEc (C:CoCone DTower) : cchain (cmetricMorph DInf (tcocone C)) := chainPE C (L DTower).

Lemma EP_id : umet_complete (chainPEc DCoCone) =-= Id.
have Z:forall n : nat, mcone (L DTower) n =-= mcone (L DTower) n << Id by move => n ; rewrite -> comp_idR.
rewrite <- (tset_sym (@limitUnique _ (L DTower) (L DTower) Id Z)).
apply: limitUnique. move => n.
have A:= (nonexp_continuous (exp_fun (ccomp _ _ _) (mcone (L DTower) n)) (chainPEc DCoCone)).
simpl in A. rewrite -> (ccomp_eq (mcone _ n) (umet_complete (chainPEc DCoCone))) in A.
apply: (tset_trans _ (tset_sym A)). clear A. simpl. rewrite -> (cut_complete_eq n). clear Z.
apply tset_trans with (y:=umet_complete (const_cchain (mcone (L DTower) n:cmetricMorph _ _))) ; first by rewrite -> umet_complete_const. refine (@umet_complete_ext (cmetricMorph _ _) _ _ _).
move => i. simpl. rewrite ccomp_eq. rewrite -> comp_assoc.
rewrite -> (emp n (n+i)). by rewrite -> (coneCom_l (L DTower) (leq_addr i n)).
Qed.

Lemma chainPE_simpl X n : chainPEc X n = mcocone X n << Projections n.
by [].
Qed.

Definition DCoLimit : CoLimit DTower.
exists DCoCone (fun C => umet_complete (chainPEc C)).
- move => C n. simpl. have ne:nonexpansive (fun x => x << Embeddings n:cmetricMorph _ _).
    move => t m e e' R. by apply comp_neq_compat. rewrite -> (cut_complete_eq n _).
  apply: (proj1 (Mrefl (_ : cmetricMorph _ _) _)). move => m.
  destruct (cumet_conv (cutn n (chainPEc C)) m) as [m' X]. specialize (X m' (leqnn _)).
  specialize (ne _ _ _ _ X). simpl in ne. refine (Mrel_trans _ ne).
  apply: (proj2 (Mrefl _ _)). rewrite <- comp_assoc. rewrite (emp _ _). 
  by apply (coconeCom_l C (leq_addr m' n)).
- move => C h X. rewrite <- (comp_idR h). rewrite <- EP_id.
  have ne:= nonexp_continuous (exp_fun (@ccomp M _ _ _) h) (chainPEc DCoCone).
  simpl in ne. rewrite -> (ccomp_eq h (umet_complete (chainPEc DCoCone))) in ne.
  rewrite -> ne. clear ne. refine (@umet_complete_ext (cmetricMorph _ _) _ _ _) => i. simpl.
  rewrite ccomp_eq. rewrite comp_assoc. by rewrite <- X.
Defined.

Definition ECoCone : CoCone DTower.
exists (ob F DInf DInf) (fun i => morph F _ _ _ _ (Projections i, Embeddings i) << Injection i).
move => i. simpl. rewrite -> morph_comp.
by rewrite -> (morph_eq_compat F (mconeCom (L DTower) i) (mcoconeCom DCoCone i)).
Defined.

Lemma Tcomp_nonexpL (T0 T1 T2:M) (f: T0 =-> T1) : nonexpansive (fun x: T1 =-> T2 => x << f:cmetricMorph _ _).
move => n e e' R. by apply: comp_neq_compat.
Qed.

Lemma Tcomp_nonexpR (T0 T1 T2:M) (f: T2 =-> T0) : nonexpansive (fun x: T1 =-> T2 => f << x:cmetricMorph _ _).
move => n e e' R. by apply: comp_neq_compat.
Qed.

Definition FCone : Cone DTower.
exists (ob F DInf DInf) (fun n => Projection n << morph F _ _ _ _ (Embeddings n, Projections n)).
move => i. refine (comp_eq_compat (tset_refl _) _). unfold Projections.
rewrite <- (morph_eq_compat F (coCom i) (mconeCom (L DTower) i)). simpl.
by rewrite -> morph_comp.
Defined.

Definition chainFPE (C:CoCone DTower) := chainPE C FCone.

Lemma subS_leq j i m : j.+1 - i == m.+1 -> i <= j.
move => X. have a:=subn_gt0 i (j.+1). have x:=ltn0Sn m.
rewrite <- (eqP X) in x. rewrite a in x. by [].
Qed.

Lemma morph_tnm n m : morph F _ _ _ _ (t_nm DTower m n, t_nm DTower n m) =-= t_nm DTower n.+1 m.+1.
have t:= (leq_total n m). case_eq (n <= m)%N ; move => l ; rewrite l in t.
clear t. have M':exists x, m - n == x by eexists ; by []. destruct M' as [x M'].
elim: x m n l M'.
- move => j i l e. rewrite subn_eq0 in e.
  have A:= @anti_leq i j. rewrite l in A. rewrite e in A. specialize (A is_true_true).
  rewrite A. rewrite -> (morph_eq_compat F (t_nn_ID DTower j) (t_nn_ID DTower j)).
  rewrite -> morph_id. by rewrite -> t_nn_ID.
- move => m IH. case.
  + move=> i l e. rewrite leqn0 in l. have ee:=eqP l. rewrite ee.
    rewrite -> (morph_eq_compat F (t_nn_ID DTower O) (t_nn_ID DTower O)).
    rewrite -> morph_id. by rewrite -> t_nn_ID.
  + move => j i e l. specialize (IH j i). have l':=l. have l0:=subS_leq l'. rewrite (leq_subS l0) in l.
    specialize (IH l0 l). clear l l' e.
    have e:= morph_eq_compat F (t_nmProjection2 DTower l0) (t_nmEmbedding2 DTower l0).
    rewrite <- morph_comp in e. rewrite -> e. rewrite -> IH. clear e.
    have a:= (tset_sym (t_nmEmbedding2 DTower _)).
    specialize (a i.+1 j.+1 l0). by apply a.
simpl in t. clear l.
have M':exists x, n - m == x by eexists ; by []. destruct M' as [x M'].
elim: x m n t M'.
- move => j i l e. rewrite subn_eq0 in e.
  have A:= @anti_leq i j. rewrite l in A. rewrite e in A. specialize (A is_true_true).
  rewrite A. rewrite -> (morph_eq_compat F (t_nn_ID DTower j) (t_nn_ID DTower j)).
  rewrite -> morph_id. by rewrite -> t_nn_ID.
- move => m IH i. case.
  + move=> l e. rewrite leqn0 in l. have ee:=eqP l. rewrite ee.
    rewrite -> (morph_eq_compat F (t_nn_ID DTower O) (t_nn_ID DTower O)).
    rewrite -> morph_id. by rewrite -> t_nn_ID.
  + move => j e l. specialize (IH i j). have l':=l. have l0:=subS_leq l'. rewrite (leq_subS l0) in l.
    specialize (IH l0 l). clear l l' e.
    have e:= morph_eq_compat F (t_nmEmbedding2 DTower l0) (t_nmProjection2 DTower l0).
    rewrite <-morph_comp in e. rewrite -> e. rewrite -> IH.
    clear e. have a:= (tset_sym (t_nmProjection2 DTower _)).
    specialize (a j.+1 i.+1 l0). by apply a.
Qed.

Lemma ECoLCom : forall (A : CoCone DTower) (n : nat),
   mcocone A n =-= umet_complete (chainFPE A) << mcocone ECoCone n.
move => C n. simpl.
  have ne:=Tcomp_nonexpL (morph F (Diter n) DInf (Diter n) DInf (Projections n, Embeddings n) << Injection n).
  rewrite -> (cut_complete_eq n _).
  apply: (proj1 (Mrefl (_:cmetricMorph _ _) _)). move => m.
  destruct (cumet_conv (cutn n (chainFPE C)) m) as [m' X]. specialize (X m' (leqnn _)).
  specialize (ne _ _ _ _ X). simpl in ne. refine (Mrel_trans _ ne). clear ne.
  apply: (proj2 (Mrefl _ _)).
  do 2 rewrite comp_assoc. rewrite <- (comp_assoc (morph F _ _ _ _ _)). rewrite -> morph_comp.
  rewrite -> (morph_eq_compat F (emp n (n+m')) (emp (n+m') n)). rewrite morph_tnm.
  rewrite <- (comp_assoc (t_nm DTower n.+1 (n+m').+1) (Projection (n + m')) (mcocone C (n + m'))).
  rewrite <- (t_nmProjection DTower). rewrite <- comp_assoc. rewrite <- (t_nmEmbedding DTower).
  apply: (coconeCom_l C _). by apply (leq_addr _ _).
Qed.

Lemma CoLimitUnique : forall (A : CoCone DTower) h,
   (forall n : nat, mcocone A n =-= h << mcocone ECoCone n) ->
   h =-= umet_complete (chainFPE A).
move => C h X. rewrite <- (comp_idR h).
  have a:= morph_eq_compat F EP_id EP_id. rewrite -> morph_id in a. rewrite <- a. clear a.
  have b:= pair_limit (chainPEc DCoCone) (chainPEc DCoCone).
  have c:= (nonexp_continuous (morph F _ _ _ _) _).
  specialize (c _ _ _ _ (cchain_pair (chainPEc DCoCone) (chainPEc DCoCone))).
  have a:=frespect ( (morph F DInf DInf DInf DInf)) b. rewrite -> a in c. clear a b.
  rewrite -> c. clear c. 
  have ne:= nonexp_continuous (exp_fun (@ccomp M _ _ _) h) ((liftc (morph F DCoCone DInf DInf DCoCone)
        (cchain_pair (chainPEc DCoCone) (chainPEc DCoCone)))). simpl in ne.
  rewrite -> (@ccomp_eq M _ _ _ h (umet_complete (liftc (morph F DCoCone DInf DInf DCoCone) _))) in ne.
  apply: (tset_trans ne). rewrite -> (cut_complete_eq 1 (chainFPE C)).
  refine (@umet_complete_ext (cmetricMorph _ _) _ _ _) => i. simpl.
  rewrite ccomp_eq. clear ne. rewrite -> morph_comp.
  rewrite <- (morph_comp F (mcone (L DTower) i) (Embeddings i) (Embeddings i) (mcone (L DTower) i)).
  rewrite comp_assoc. apply: comp_eq_compat.
  + specialize (X i.+1). simpl in X. unfold addn. simpl. rewrite -> X. apply: comp_eq_compat ; first by [].
    rewrite -> morph_comp. apply morph_eq_compat.
    * by rewrite -> (mconeCom (L DTower) i).
    * by rewrite -> (@mcoconeCom DTower DCoCone i).
  + apply morph_eq_compat.
    * by rewrite -> (@mcoconeCom DTower DCoCone i).
    * by rewrite -> (mconeCom (L DTower) i).
Qed.

Definition ECoLimit : CoLimit DTower.
exists ECoCone (fun C => umet_complete (chainFPE C)).
by apply ECoLCom.
by apply CoLimitUnique.
Defined.

(*=FoldUnfoldIso *)
Definition Fold : (ob F DInf DInf) =-> DInf := (*CLEAR*) colimitExists ECoLimit DCoCone. (*CLEARED*)
Definition Unfold : DInf =-> (ob F DInf DInf) := (*CLEAR*) colimitExists DCoLimit ECoCone. (*CLEARED*)

Lemma FU_id : Fold << Unfold =-= Id.
(*CLEAR*)
apply tset_trans with (y:=colimitExists DCoLimit DCoLimit).
- refine (@colimitUnique _ DCoLimit DCoLimit _ _). move => i. unfold Fold. unfold Unfold.
  simpl. rewrite <- (ccomp_eq (umet_complete (chainFPE DCoCone)) (umet_complete (chainPEc ECoCone))).
  have a:=frespect ( (ccomp _ _ _)) (pair_limit (chainFPE DCoCone) (chainPEc ECoCone)).
  rewrite -> (nonexp_continuous (ccomp _ _ _)(cchain_pair (chainFPE DCoCone) (chainPEc ECoCone)) ) in a.
  rewrite <- a. clear a.
  have ne:= nonexp_continuous (exp_fun (@ccomp M _ _ _ << <|pi2,pi1|>) (Embeddings i)) (liftc (ccomp DInf FCone DCoCone)
        (cchain_pair (chainFPE DCoCone) (chainPEc ECoCone))).
  simpl in ne.
  rewrite -> (@ccomp_eq M _ _ _ (umet_complete (liftc (ccomp DInf FCone DCoCone)
              (cchain_pair (chainFPE DCoCone) (chainPEc ECoCone)))) (Embeddings i)) in ne.
  rewrite -> ne. clear ne. rewrite -> (cut_complete_eq i _).
  apply (tset_trans (tset_sym (umet_complete_const (Embeddings i:cmetricMorph _ _)))).
  apply umet_complete_ext => j. simpl.
  rewrite ccomp_eq. simpl.
  apply: (tset_trans _ (tset_sym (comp_eq_compat (ccomp_eq _ _) (tset_refl _)))).
  do 3 rewrite comp_assoc. rewrite <- (comp_assoc _ _ (Embeddings (i + j) << Projection (i + j))).
  rewrite -> (morph_comp F (Embeddings (i + j)) (Projections (i + j)) (Projections (i + j)) (Embeddings (i + j))).
  rewrite -> (morph_eq_compat F (emp (i+j) (i+j)) (emp (i+j) (i+j))).
  rewrite -> (morph_eq_compat F (t_nn_ID DTower (i+j)) (t_nn_ID DTower (i+j))).
  rewrite morph_id. rewrite comp_idR. rewrite <- (comp_assoc (Injection (i+j))).
  rewrite retract_IP. rewrite comp_idR. rewrite <- comp_assoc. rewrite -> emp.
  apply: (coconeCom_l DCoCone). by apply leq_addr.
- apply tset_sym. apply: (@colimitUnique _ DCoLimit DCoLimit _ _). move => n. simpl. by rewrite -> comp_idL.
Qed.
(*CLEARED*)
Lemma UF_id : Unfold << Fold =-= Id.
(*CLEAR*)
apply tset_trans with (y:=colimitExists ECoLimit ECoLimit).
- apply (@colimitUnique _ ECoLimit ECoLimit). move => i. unfold Fold. unfold Unfold.
  simpl. rewrite <- (ccomp_eq (umet_complete (chainPEc ECoCone)) (umet_complete (chainFPE DCoCone))).
  have a:=frespect ( (ccomp _ _ _)) (pair_limit (chainPEc ECoCone) (chainFPE DCoCone)).
  rewrite -> (nonexp_continuous (ccomp _ _ _) (cchain_pair (chainPEc ECoCone) (chainFPE DCoCone)) ) in a.
  rewrite <- a. clear a.
  have ne:= nonexp_continuous (exp_fun (@ccomp M _ _ _ << <|pi2,pi1|>) (morph F _ _ _ _ (Projections i,Embeddings i) << Injection i)) (liftc (ccomp _ _ _ )
        (cchain_pair (chainPEc ECoCone) (chainFPE DCoCone))).
  simpl in ne.
  rewrite -> (@ccomp_eq M _ _ _ (umet_complete (liftc (ccomp _ _ _)
              (cchain_pair (chainPEc ECoCone) (chainFPE DCoCone)))) (morph F _ _ _ _ (Projections i,Embeddings i) << Injection i)) in ne.
  rewrite -> ne. clear ne. rewrite -> (cut_complete_eq i _).
  apply (tset_trans (tset_sym (umet_complete_const (morph F _ _ _ _ (Projections i, Embeddings i) << Injection i:cmetricMorph _ _)))).
  apply umet_complete_ext => j. simpl.
  rewrite ccomp_eq. simpl.
  apply: (tset_trans _ (tset_sym (comp_eq_compat (ccomp_eq _ _) (tset_refl _)))).
  do 3 rewrite comp_assoc. rewrite <- (comp_assoc (Embeddings (i+j))). rewrite -> (emp (i+j) (i+j)).
  rewrite t_nn_ID. rewrite comp_idR. rewrite <- (comp_assoc (morph F _ _ _ _ (Projections i, Embeddings i))).
  rewrite -> (morph_comp F (Embeddings (i+j)) (Projections (i+j)) (Projections (i)) (Embeddings (i))).
  rewrite -> (morph_eq_compat F (emp i (i+j)) (emp (i+j) i)). rewrite morph_tnm.
  rewrite <- (comp_assoc (Injection i)). rewrite <- (t_nmEmbedding DTower i (i+j).+1).
  rewrite <- (comp_assoc _ (Projection (i+j))). rewrite <- (t_nmProjection DTower).
  rewrite <- comp_assoc. rewrite <- (@t_nmEmbedding2 DTower _ _ (leq_addr j i)). rewrite -> t_nmEmbedding.
  rewrite comp_assoc. rewrite <- morph_tnm. rewrite -> (morph_comp F (Projections (i + j)) (Embeddings (i + j))
           (t_nm DTower (i + j) i) (t_nm DTower i (i + j))).
  by rewrite <- (morph_eq_compat F (coneCom_l (L DTower) (leq_addr j i)) (coconeCom_l DCoCone (leq_addr j i))).
- apply tset_sym. apply (@colimitUnique _ ECoLimit ECoLimit). move => n. by rewrite -> comp_idL.
Qed.
(*CLEARED*)
(*=End *)

End RecursiveDomains.

End Msolution.

