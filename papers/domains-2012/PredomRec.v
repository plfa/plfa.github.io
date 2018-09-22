(**********************************************************************************
 * PredomRec.v                                                                    *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                       *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)

Require Export Categories PredomCore NSetoid.

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

(*=Enriched *)
Module BaseCat.
  Record mixin_of (O:Type) (M:O -> O -> cppoType) := Mixin
  { catm :> Category.mixin_of M;
    terminal :> CatTerminal.mixin_of (Category.Pack catm O);
    comp : forall X Y Z : O, M Y Z * M X Y =-> M X Z;
    comp_comp : forall X Y Z m m', comp X Y Z (m,m') =-= Category.tcomp catm m m'
  }. (*CLEAR*)
  Notation class_of := mixin_of (only parsing).
(*CLEARED*)
  Section ClassDef.
  Definition base2 T (M:T -> T -> cppoType) (c:class_of M) := CatTerminal.Class c. (*CLEAR*)
  Local Coercion base2 : class_of >-> CatTerminal.class_of.

  Structure cat := Pack {object; morph : object -> object -> cppoType ; _ : class_of morph; _ : Type}.
  Local Coercion object : cat >-> Sortclass.
  Local Coercion morph : cat >-> Funclass.
  Definition class cT := let: Pack _ _ c _ := cT return class_of (@morph cT) in c.
  Definition unpack (K:forall O (M:O -> O -> cppoType) (c:class_of M), Type)
              (k : forall O (M: O -> O -> cppoType) (c : class_of M), K _ _ c) (cT:cat) :=
    let: Pack _ M c _ := cT return @K _ _ (class cT) in k _ _ c.
  Definition repack cT : _ -> Type -> cat := let k T M c p := p c in unpack k cT.
  Definition pack T M c := @Pack T M c T.
 (*CLEARED*)
  Definition terminalCat (cT:cat) : terminalCat := CatTerminal.Pack (class cT) cT.
  Definition catType (cT:cat) : catType := Category.Pack (class cT) cT. (*CLEAR*)
  Definition ordType (cT:cat) (X Y:cT) : ordType := PreOrd.Pack (CPPO.class (morph X Y)) (cT X Y).
  Definition cpoType (cT:cat) (X Y:cT) : cpoType := CPO.Pack (CPPO.class (morph X Y)) (cT X Y). 
(*CLEARED*)
  Definition cppoType (cT:cat) (X Y:cT) : cppoType := 
               CPPO.Pack (CPPO.class (morph X Y)) (cT X Y). (*CLEAR*)
  Definition pointedType (cT:cat) (X Y:cT) : pointedType := Pointed.Pack (CPPO.class (morph X Y)) (cT X Y).
  End ClassDef.
  Module Import Exports.
  Coercion terminalCat : cat >-> CatTerminal.cat.
Coercion base2 : class_of >-> CatTerminal.class_of.
Coercion object : cat >-> Sortclass.
  Coercion morph : cat >-> Funclass.
Canonical Structure BaseCat.terminalCat.
Canonical Structure BaseCat.catType.
Canonical Structure BaseCat.ordType.
Canonical Structure BaseCat.cpoType.
Canonical Structure BaseCat.pointedType.
Canonical Structure BaseCat.cppoType.
Notation cppoMorph := BaseCat.cppoType. (*CLEAR*)
Notation cppoECat := BaseCat.cat.
Notation CppoECatMixin := BaseCat.Mixin.
(*CLEARED*)
Notation CppoECatType := BaseCat.pack.
(*CLEARED*)
End Exports.
End BaseCat. (*CLEAR*)
Export BaseCat.Exports.
(*CLEARED*)
(*=End *)

Definition getmorph (C:cppoECat) (X Y : C) (f:CPPO.cpoType (@BaseCat.cppoType C X Y)) : C X Y := f.
Coercion getmorph : cppoECat >-> Funclass.

Definition ccomp (cT:cppoECat) (X Y Z : cT) : cppoMorph Y Z * cppoMorph X Y =-> cppoMorph X Z := BaseCat.comp (BaseCat.class cT) X Y Z.

Lemma ccomp_eq (cT:cppoECat) (X Y Z : cT) (f : cT Y Z) (f' : cT X Y) : ccomp X Y Z (f,f') =-= f << f'.
unfold Category.comp. unfold ccomp. simpl. case:cT X Y Z f f'. simpl.
move => O M. case. simpl.
move => C T comp ce T' X Y Z f g. by apply: ce.
Qed.

Add Parametric Morphism (M:cppoECat) (X Y Z:M) : (@Category.comp M X Y Z)
  with signature (@Ole (cppoMorph Y Z)) ++> (@Ole (cppoMorph X Y)) ++> (@Ole (cppoMorph X Z))
  as comp_le_compat.
move => f f' l g g' l'.
have e:= (ccomp_eq f g).  have e':=ccomp_eq f' g'. rewrite <- e. rewrite <- e'. apply: fmonotonic.
by split.
Qed.

Section Msolution.
Variable M:cppoECat.

Open Scope C_scope.
Open Scope S_scope.

(*=BiFunctor *)
Record BiFunctor : Type := mk_functor
{ ob : M -> M -> M ;
  morph : forall (T0 T1 T2 T3 : M), (cppoMorph T1 T0) * (cppoMorph T2 T3) =->
                                    (cppoMorph (ob T0 T2) (ob T1 T3)) ;
  morph_comp: forall T0 T1 T2 T3 T4 T5 (f:M T4 T1) (g:M T3 T5) (h:M T1 T0)
    (k:M T2 T3), getmorph (morph T1 T4 T3 T5 (f,g)) << (morph T0 T1 T2 T3 (h, k)) =-=
                                            morph _ _ _ _ (h << f, g << k) ;
  morph_id : forall T0 T1, morph T0 T0 T1 T1 (Id:M _ _, Id:M _ _) =-= (Id : M _ _)}.
(*=End *)

Definition eppair T0 T1 (f:M T0 T1) (g:M T1 T0) :=
      g << f =-= Id /\ f << g <= @Category.id M _.

(*=Tower *)
Record Tower : Type := mk_tower
{ tobjects : nat -> M;
  tmorphisms : forall i, (tobjects (S i)) =-> (tobjects i);
  tmorphismsI : forall i, (tobjects i) =-> (tobjects (S i));
  teppair : forall i, eppair (tmorphismsI i) (tmorphisms i)}.
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

(*=CoLimit *)
Record CoLimit (To:Tower) : Type := mk_basecolimit
{ lcocone :> CoCone To;
  colimitExists : forall (A:CoCone To), (tcocone lcocone) =-> (tcocone A) ;
  colimitCom : forall (A:CoCone To), forall n, mcocone A n =-= colimitExists A << mcocone lcocone n;
  colimitUnique : forall (A:CoCone To) (h: (tcocone lcocone) =-> (tcocone A))
     (C:forall n, mcocone A n =-= h << mcocone lcocone n), h =-= colimitExists A }.
(*=End *)

(*=Limit *)
Record Limit (To:Tower) : Type := mk_baselimit
{lcone :> Cone To;
 limitExists : forall (A:Cone To), (tcone A) =-> (tcone lcone);
 limitCom : forall (A:Cone To), forall n, mcone A n =-= mcone lcone n << limitExists A;
 limitUnique : forall (A:Cone To) (h: (tcone A) =-> (tcone lcone))
    (C:forall n, mcone A n =-= mcone lcone n << h), h =-= limitExists A }.

Variable L:forall T:Tower, Limit T.
(*=End *)

Section RecursiveDomains.

Variable F : BiFunctor.

Add Parametric Morphism C X Y Z W : (fun (x: Y =-> X) (y: Z =-> W) => @morph C X Y Z W (pair x y))
  with signature (@tset_eq _) ==> (@tset_eq _) ==> (@tset_eq _)
  as morph_eq_compat.
move => x x' e y y' e'. apply: fmon_stable. by split ; split ;case: e ; case: e'.
Qed.

Lemma BiFuncRtoR: forall (T0 T1:M) (f: T0 =-> T1) (g: T1 =-> T0), eppair f g ->
          eppair (morph F _ _ _ _ (g,f)) (morph F _ _ _ _ (f,g)).
move => A B f g. case => e r. split.
- rewrite -> (morph_comp F f g g f). rewrite -> (morph_eq_compat F e e).
  by rewrite morph_id.
- rewrite morph_comp. rewrite -> (pair_le_compat r r). by rewrite morph_id.
Qed.

Section Tower.

Variable DTower : Tower.

Lemma lt_gt_dec n m : (n < m) + (m = n) + (m < n).
case: (ltngtP m n) => e.
- by right.
- left. by left.
- left. by right.
Qed.

Lemma leqI m n : (m <= n)%N = false -> n <= m.
move => I. have t:=(leq_total m n). rewrite I in t. by apply t.
Qed.

Lemma lt_subK n m : m < n -> n = (n - m + m)%N.
move => l. apply sym_eq. apply subnK. have x:= (leqnSn m). by apply (leq_trans x l).
Qed.

(*=Projections *)
Definition Diter_coercion n m : n = m ->
             M (tobjects DTower n) (tobjects DTower m) :=
  fun e => eq_rect_r (fun n : nat => M (tobjects DTower n) _) Id e.

Fixpoint Projection_nm m (n:nat) : 
          (tobjects DTower (n+m)) =-> (tobjects DTower m) :=
match n with
| O => Id
| S n => Projection_nm m n << tmorphisms DTower (n+m)%N
end.

Fixpoint Injection_nm m (n:nat) : 
          (tobjects DTower m) =-> (tobjects DTower (n+m)) :=
match n with
| O => Id
| S n => tmorphismsI DTower (n+m) << Injection_nm m n
end.

Definition t_nm n m : (tobjects DTower n) =-> (tobjects DTower m) :=
match (lt_gt_dec m n) with
| inl (inl ee) =>
     (Projection_nm m (n - m)%N) << (Diter_coercion (lt_subK ee))
| inl (inr ee) => Diter_coercion ee
| inr ee => Diter_coercion (sym_eq (lt_subK ee)) << Injection_nm n (m - n)
end.
(*=End *)

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
- move => f. have a:=leq_trans (leqnSn _) f. have Ff:=leq_ltn_trans a e. by rewrite ltnn in Ff.
Qed.

Lemma lt_gt_dec_gt n m : m < n -> exists e, lt_gt_dec n m = (inr _ e).
move => e. case_eq (lt_gt_dec n m) ; first case.
- move => i _. have a:=leq_trans (leqnSn _) i. have Ff:=leq_ltn_trans a e. by rewrite ltnn in Ff.
- move => f. rewrite f in e. by rewrite ltnn in e.
- move => i _. by exists i.
Qed.

Lemma lt_gt_dec_eq n m : forall e : m = n, lt_gt_dec n m = (inl _ (inr _ e)).
move => e ; generalize e ; rewrite e. clear e m => e.
case_eq (lt_gt_dec n n) ; first case.
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
  + move => i j. have Ff:=leq_trans i j. by rewrite ltnn in Ff.
- move => e. generalize e. rewrite e. clear n e. move => e. destruct (lt_gt_dec_gt (leqnn (S m))) as [p A].
  rewrite A. clear A.
  have ee:=subSnn m. have x:=(sym_eq (lt_subK (n:=m.+1) (m:=m) p)).
  rewrite <- (eq_irrelevance x (sym_eq (lt_subK (n:=m.+1) (m:=m) p))). move: x. rewrite ee. simpl.
  move => x. do 2 rewrite (Diter_coercion_simpl). rewrite comp_idL. rewrite comp_idR.
  unfold addn. simpl. by rewrite -> (proj1 (teppair DTower m)).
- move => i. have l:=leq_trans i (leqnSn m). destruct (lt_gt_dec_gt l) as [p A]. rewrite A. clear A l.
  have x:=(sym_eq (lt_subK (n:=m.+1) (m:=n) p)). rewrite (eq_irrelevance (sym_eq (lt_subK (n:=m.+1) (m:=n) p)) x).
  move: x. rewrite leq_subS ; last by []. simpl. move => x. do 2 rewrite comp_assoc.
  refine (comp_eq_compat _ (tset_refl (Injection_nm n (m-n)))). have y:=(sym_eq (lt_subK (n:=m) (m:=n) i)).
  rewrite (eq_irrelevance (sym_eq (lt_subK (n:=m) (m:=n) i)) y). have a:=(trans_eq (sym_eq (addSn _ _)) x).
  rewrite (eq_irrelevance x a).
  apply tset_trans with (y:=(tmorphisms DTower m << Diter_coercion a) << tmorphismsI DTower (m - n + n)) ; last by [].
  move: a. generalize y. rewrite -> y. clear. move => y a. do 2 rewrite Diter_coercion_simpl.
  rewrite comp_idR. by rewrite (proj1 (teppair DTower m)).
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
    rewrite x. clear x. move => x. simpl. do 4 rewrite <- comp_assoc.
    refine (comp_eq_compat (tset_refl (Projection_nm m _)) _).
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
  refine (comp_eq_compat (tset_refl (Projection_nm _ _)) _). have y:=((lt_subK i)).
  rewrite (eq_irrelevance ((lt_subK i)) y). have a:=(trans_eq x ((addSn _ _))).
  rewrite (eq_irrelevance x a).
  apply tset_trans with (y:=tmorphisms DTower (n - m + m) << (Diter_coercion a << tmorphismsI DTower n)) ; last by [].
  move: a. generalize y. rewrite <- y. clear. move => y a. do 2 rewrite Diter_coercion_simpl.
  rewrite comp_idL. by rewrite <- (proj1 (teppair DTower n)).
- move => e. generalize e. rewrite e. clear n e. move => e. destruct (lt_gt_dec_lt (leqnn (S m))) as [p A].
  rewrite A. clear A.
  have ee:=subSnn m. have x:=((lt_subK (n:=m.+1) (m:=m) p)).
  rewrite <- (eq_irrelevance x ((lt_subK (n:=m.+1) (m:=m) p))). move: x. rewrite ee. simpl.
  move => x. do 2 rewrite (Diter_coercion_simpl). rewrite comp_idR. rewrite comp_idL.
  by rewrite -> (proj1 (teppair DTower m)).
- case (lt_gt_dec m n.+1) ; first case.
  + move => i j. have Ff:=leq_trans i j. by rewrite ltnn in Ff.
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
    rewrite x. clear x. move => x. simpl. do 4 rewrite -> comp_assoc. refine (comp_eq_compat _ (tset_refl (Injection_nm _ _))).
    have x':=sym_eq(lt_subK p'). rewrite (eq_irrelevance (sym_eq (lt_subK _)) x').
    have x1:((m - n).+2 + n)%N = ((m - n) + n).+2 by [].
    have x2:=sym_eq (trans_eq x x1).
    apply tset_trans with (y:=(Diter_coercion x2 << tmorphismsI DTower (S (m - n + n))) << tmorphismsI DTower ((m - n + n))) ; 
    first by simpl ; rewrite (eq_irrelevance x2 (sym_eq x)).
    move: x2. generalize x' ; rewrite x'. clear x' x x1 p p'. move => x x'. do 2 rewrite (Diter_coercion_simpl).
    rewrite -> comp_idR. by rewrite comp_idL.
Qed.

Lemma t_nm_EP i n : (i <= n)%N -> eppair (t_nm i n) (t_nm n i).
have e:exists x, x == n - i by eexists.
case: e => x e. elim: x i n e.
- move => i n e l. have ee:i = n. apply anti_leq. rewrite l. simpl. unfold leq. by rewrite <- (eqP e).
  rewrite -> ee. split.
  + rewrite t_nn_ID. by rewrite comp_idL.
  + apply Oeq_le. rewrite t_nn_ID. by rewrite comp_idL.
- move => x IH i. case ; first by rewrite sub0n.
  move => n e l. have ll:(i <= n)%N. have aa:0 < n.+1 - i. by rewrite <- (eqP e). rewrite subn_gt0 in aa. by apply aa.
  clear l. specialize (IH i n). rewrite (leq_subS ll) in e. specialize (IH e ll). split.
  + rewrite (t_nmProjection2 ll). rewrite -> (t_nmEmbedding2 ll). rewrite comp_assoc.
    rewrite <- (comp_assoc (tmorphismsI _ _)). rewrite (proj1 (teppair DTower n)). rewrite comp_idR. by apply (proj1 IH).
  + rewrite -> (t_nmEmbedding2 ll). rewrite (t_nmProjection2 ll).
    rewrite comp_assoc. rewrite <- (comp_assoc (t_nm n i)).
    rewrite -> (comp_le_compat (comp_le_compat (Ole_refl _) (proj2 IH)) (Ole_refl _)).
    rewrite comp_idR. by rewrite -> (proj2 (teppair DTower n)).
Qed.

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

Lemma chainPEm (C:CoCone DTower) (C':Cone DTower) : monotonic (fun n => (mcocone C n << mcone C' n) : cppoMorph _ _).
move => i j l.
have E:exists x, j - i = x by exists (j - i).
case: E l => x. elim: x i j.
- move => i j e l. have l':(j <= i)%N. unfold leq. by rewrite e.
  have ee: j <= i <= j. rewrite l'. by apply l.
  by rewrite (anti_leq ee).
- move => x IH i. case ; first by rewrite sub0n.
  move => j l _. specialize (IH i.+1 j.+1). rewrite subSS in IH. rewrite <- IH.
  + have EE:= comp_eq_compat (mcoconeCom C i) (mconeCom C' i).
    rewrite <- comp_assoc in EE. rewrite -> (comp_assoc (mcone C' _)) in EE.
    have ll:= (proj2 (teppair DTower i)).
    rewrite -> (proj2 EE).
    apply: comp_le_compat ; first by [].
    rewrite  -> (comp_le_compat ll (Ole_refl _)). by rewrite comp_idL.
  + clear IH. have ll:(i < j.+1)%N. rewrite <- subn_gt0. by rewrite l.
    rewrite (@leq_subS i j ll) in l. by auto.
  + have ll:(i < j.+1)%N. rewrite <- subn_gt0. by rewrite l. by apply ll.
Qed.

Definition chainPE (C:CoCone DTower) (C':Cone DTower) : natO =-> cppoMorph _ _ := mk_fmono (@chainPEm C C').

End Tower.

(*=Diter *)
Fixpoint Diter (n:nat) :=
    match n return M with | O => One | S n => ob F (Diter n) (Diter n) end.
Fixpoint Injection (n:nat) : (Diter n) =-> (Diter (S n)) :=
match n with
| O => PBot
| S n => morph F _ _ _ _ (Projection n, Injection n)
end with Projection (n:nat) : (Diter (S n)) =-> (Diter n) :=
match n with
| O => terminal_morph _ 
| S n => morph F _ _ _ _ (Injection n,Projection n)
end.
Variable comp_left_strict : forall (X Y Z:M) (f:M X Y),
   (PBot:Y =-> Z) << f =-= (PBot:X =-> Z).
Lemma eppair_IP: forall n, eppair (Injection n) (Projection n).
(*=End *)
elim.
- split ; first by apply:terminal_unique.
  simpl. rewrite -> (comp_left_strict _ (terminal_morph _)). by apply: leastP.
- move => n IH. split.
  + simpl. rewrite -> (morph_comp F (Injection n) (Projection n) (Projection n) (Injection n)).
    rewrite -> (morph_eq_compat F (proj1 IH) (proj1 IH)). by rewrite morph_id.
  + simpl. rewrite morph_comp.
    rewrite -> (pair_le_compat (proj2 IH) (proj2 IH)). by rewrite morph_id.
Qed.

(*=DTower *)
Definition DTower := mk_tower eppair_IP.
(*=End *)

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
unfold eppair.
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

Definition chainPEc (C:CoCone DTower) : natO =-> (cppoMorph DInf (tcocone C)) := chainPE C (L DTower).

Lemma lub_comp_left (X Y:M) (f:X =-> Y) Z (c:natO =-> cppoMorph Y Z) :
   (lub c:M _ _) << f =-= lub ( (exp_fun (ccomp _ _ _ << <|pi2,pi1|>) f:ordCatType _ _) << c).
rewrite <- (ccomp_eq (lub c) f). by rewrite <- (lub_comp_eq _ c).
Qed.

Lemma lub_comp_right (Y Z:M) (f:Y =-> Z) X (c:natO =-> cppoMorph X Y) :
   f << lub c =-= lub ( (exp_fun (ccomp _ _ _) f:ordCatType _ _) << c).
rewrite <- (ccomp_eq f (lub c)). by rewrite <- lub_comp_eq.
Qed.

Lemma lub_comp_both (X Y Z:M) (c:natO =-> cppoMorph X Y) (c':natO =-> cppoMorph Y Z) :
  (lub c':M _ _) << lub c =-= lub ((ccomp _ _ _ : ordCatType _ _) << <|c', c|>).
rewrite <- lub_comp_eq.
rewrite {3} /lub. simpl. unfold prod_lub. rewrite prod_fun_fst. rewrite prod_fun_snd.
by rewrite -> ccomp_eq.
Qed.

Lemma EP_id : (lub (chainPEc DCoCone) : M _ _) =-= Id.
rewrite <- (tset_sym (@limitUnique _ (L DTower) (L DTower) Id (fun n => tset_sym (comp_idR _)))).
apply: limitUnique. move => n. rewrite -> lub_comp_right.
rewrite -> (lub_lift_left _ n). apply: Ole_antisym. rewrite <- (le_lub _ O). simpl. rewrite addn0.
have e:= comp_eq_compat (retract_EP n) (tset_refl (mcone (L DTower) n)).
rewrite -> comp_idL in e. unfold Projections in e. rewrite <- comp_assoc in e.
rewrite ccomp_eq. by rewrite e.

apply: lub_le. move => i. simpl. rewrite ccomp_eq. rewrite -> comp_assoc.
rewrite -> (emp n (n+i)). by rewrite (coneCom_l _ (leq_addr i n)).
Qed.

Lemma chainPE_simpl X n : chainPEc X n = mcocone X n << Projections n.
by [].
Qed.

Definition DCoLimit : CoLimit DTower.
exists DCoCone (fun C => lub (chainPEc C)).
- move => C n. simpl. rewrite -> lub_comp_left. apply Ole_antisym.
  + apply: (Ole_trans _ (le_lub _ n)).
    simpl. rewrite -> ccomp_eq.
    have e:= comp_eq_compat (tset_refl (mcocone C n)) (emp n n). rewrite -> t_nn_ID in e.
    rewrite -> comp_idR in e. rewrite -> comp_assoc in e. by rewrite -> e.
  + rewrite -> (lub_lift_left _ n). apply: lub_le => k.
    simpl. rewrite -> ccomp_eq.
    have e:=comp_eq_compat (tset_refl (mcocone C (n+k))) (emp (n+k) n). rewrite -> comp_assoc in e.
    rewrite <- (coconeCom_l C (leq_addr k n)) in e. by rewrite e.
- move => C h X. rewrite <- (comp_idR h). rewrite <- (EP_id).
  apply tset_trans with (y:=exp_fun (ccomp _ _ _) h (lub (chainPEc DCoCone))) ; first by  apply: (tset_sym (ccomp_eq _ _)).
  rewrite -> (@lub_comp_eq _ _ ( (exp_fun (ccomp _ _ _) h)) (chainPEc DCoCone)).
  apply: lub_eq_compat. apply fmon_eq_intro => n. simpl. specialize (X n).
  rewrite ccomp_eq.
  rewrite comp_assoc. by rewrite <- X.
Defined.

Definition ECoCone : CoCone DTower.
exists (ob F DInf DInf) (fun i => (morph F _ _ _ _ (Projections i, Embeddings i):M _ _) << Injection i).
move => i. simpl. rewrite -> (morph_comp F (Projections i.+1) (Embeddings i.+1) (Projection i) (Injection i)).
by rewrite -> (morph_eq_compat F (mconeCom (L DTower) i) (mcoconeCom DCoCone i)).
Defined.

Definition FCone : Cone DTower.
exists (ob F DInf DInf) (fun n => Projection n << morph F _ _ _ _ (Embeddings n, Projections n)).
move => i. refine (comp_eq_compat (tset_refl _) _). unfold Projections.
rewrite <- (morph_eq_compat F (coCom i) (mconeCom (L DTower) i)). simpl.
apply: morph_comp.
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
    rewrite <-morph_comp in e. rewrite -> e. simpl. rewrite -> IH.
    clear e. have a:= (tset_sym (t_nmProjection2 DTower _)).
    specialize (a j.+1 i.+1 l0). by apply a.
Qed.

Lemma ECoLCom : forall (A : CoCone DTower) (n : nat),
   mcocone A n =-= (lub (chainFPE A):M _ _) << mcocone ECoCone n.
move => C n. simpl.
  rewrite -> lub_comp_left. apply Ole_antisym.
  * rewrite <- (le_lub _ n). simpl. rewrite -> ccomp_eq. do 2 rewrite comp_assoc.
    rewrite <- (comp_assoc (morph F _ _ _ _ _ : M _ _)).
    rewrite -> (morph_comp F (Embeddings n) (Projections n) (Projections n) (Embeddings n)).
    rewrite -> (morph_eq_compat F (tset_trans (emp n n) (t_nn_ID _ _))
                                                   (tset_trans (emp n n) (t_nn_ID _ _))).
    rewrite -> morph_id. rewrite comp_idR. rewrite <- comp_assoc. rewrite -> (proj1 (teppair DTower n)).
    by rewrite comp_idR.
  * rewrite -> (lub_lift_left _ n). apply: lub_le => k. simpl. apply Oeq_le.
    rewrite -> ccomp_eq. do 2 rewrite comp_assoc. rewrite <- (comp_assoc (morph F _ _ _ _ _:M _ _)).
    rewrite -> (morph_comp F (Embeddings (n+k)) (Projections (n+k)) (Projections n) (Embeddings n)).
    rewrite -> (morph_eq_compat F  (emp n (n+k)) (emp (n+k) n)).
    rewrite morph_tnm. rewrite <- comp_assoc. rewrite <- (t_nmEmbedding DTower n (n+k).+1).
    rewrite <- comp_assoc. rewrite <- (t_nmProjection DTower n (n+k)).
    by rewrite <- (coconeCom_l C (leq_addr k n)).
Qed.

Open Scope D_scope.
Open Scope C_scope.

Lemma pair_lub (D E:cpoType) (c:natO =-> D) (c':natO =-> E) : @tset_eq (CPO.setoidType _) (lub c,lub c') (lub (<|c,c'|>)).
rewrite {3} /lub. simpl. unfold prod_lub.
split ; split ; simpl ; apply lub_le_compat ; apply Oeq_le ; try (by rewrite prod_fun_fst) ; by rewrite prod_fun_snd.
Qed.

Lemma CoLimitUnique : forall (A : CoCone DTower) h,
   (forall n : nat, mcocone A n =-= h << mcocone ECoCone n) ->
   h =-= lub (chainFPE A).
move => C h X. rewrite <- (comp_idR h).
  have a:= morph_eq_compat F EP_id EP_id. rewrite -> morph_id in a.
  rewrite <- a. clear a.  
  have b:= (pair_lub (chainPEc DCoCone) (chainPEc DCoCone)).
  have S:= (fmon_stable (morph F _ _ _ _) b). rewrite -> (Oeq_trans S (lub_comp_eq _ _)).
  clear b S. rewrite -> lub_comp_right. rewrite -> (lub_lift_left (chainFPE C) 1).
  apply: lub_eq_compat. apply fmon_eq_intro => n. simpl.
  rewrite -> (ccomp_eq h (morph F _ _ _ _ (Embeddings n << mcone (L DTower) n,
                                            Embeddings n << mcone (L DTower) n))).
  specialize (X n.+1). simpl in X.
  rewrite -> X. rewrite (morph_comp F (Projections n.+1) (Embeddings n.+1) (Projection n) (Injection n)).
  rewrite -> (morph_comp F (Injection n) (Projection n) (Embeddings (1 + n)) (Projections (1 + n))).
  rewrite -> (morph_eq_compat F (mconeCom (L DTower) n) (mcoconeCom DCoCone n)).
  rewrite -> (morph_eq_compat F (mcoconeCom DCoCone n) (mconeCom (L DTower) n)).
  rewrite <- comp_assoc.
  by rewrite -> (morph_comp F (mcone (L DTower) n) (mcocone DCoCone n) (mcocone DCoCone n) (mcone (L DTower) n)).
Qed.

Definition ECoLimit : CoLimit DTower.
exists ECoCone (fun C => lub (chainFPE C)).
by apply ECoLCom.
by apply CoLimitUnique.
Defined.

(*=Iso *)
Definition Fold : (ob F DInf DInf) =-> DInf := (* ... *) (*CLEAR*) colimitExists ECoLimit DCoCone. (*CLEARED*)
Definition Unfold : DInf =-> (ob F DInf DInf) := (*CLEAR*) colimitExists DCoLimit ECoCone. (*CLEARED*)

Lemma FU_id : Fold << Unfold =-= Id. Proof.
apply tset_trans with (y:=colimitExists DCoLimit DCoLimit).
- refine (@colimitUnique _ DCoLimit DCoLimit _ _). move => i. unfold Fold. unfold Unfold.
  simpl. rewrite -> lub_comp_both. rewrite -> lub_comp_left. apply Ole_antisym.
  * apply: (Ole_trans _ (le_lub _ i)).
    simpl. apply Oeq_le. rewrite ccomp_eq. rewrite ccomp_eq.
    do 3 rewrite comp_assoc. rewrite <- (comp_assoc (morph F _ _ _ _ _ :M _ _)).
    rewrite -> (morph_comp F (Embeddings i) (Projections i) (Projections i) (Embeddings i)).
    rewrite -> (morph_eq_compat F (tset_trans (emp i i) (t_nn_ID _ _)) (tset_trans (emp i i) (t_nn_ID _ _))).
    rewrite -> morph_id. rewrite comp_idR. rewrite <- (comp_assoc (Injection i)).
    rewrite -> (proj1 (teppair DTower i)). rewrite comp_idR. rewrite <- comp_assoc.
    rewrite -> (emp i i). rewrite t_nn_ID. by rewrite comp_idR.
  * rewrite -> (lub_lift_left _ i). apply: lub_le => k. simpl.
    apply Oeq_le. rewrite -> ccomp_eq. rewrite ccomp_eq.
    do 3 rewrite comp_assoc. rewrite <- (comp_assoc (morph F _ _ _ _ _:M _ _)).
    rewrite -> (morph_comp F (Embeddings (i + k)) (Projections (i + k)) (Projections (i + k)) (Embeddings (i + k))).
    rewrite (morph_eq_compat F (tset_trans (emp _ _) (t_nn_ID _ _)) (tset_trans (emp _ _) (t_nn_ID _ _))).
    rewrite -> morph_id. rewrite comp_idR. rewrite <- (comp_assoc (Injection (i+k))).
    rewrite -> (proj1 (teppair DTower (i+k))). rewrite comp_idR. rewrite <- comp_assoc.
    rewrite -> (emp (i+k) (i)).
    by apply (tset_sym (@coconeCom_l DTower DCoCone _ _ (leq_addr k i))).
- apply tset_sym. apply: (@colimitUnique _ DCoLimit DCoLimit _ _). move => n. simpl. by rewrite -> comp_idL.
Qed.
Lemma UF_id : Unfold << Fold =-= Id.
Proof.
apply tset_trans with (y:=colimitExists ECoLimit ECoLimit).
- apply (@colimitUnique _ ECoLimit ECoLimit). move => i. unfold Fold. unfold Unfold.
  simpl. rewrite -> lub_comp_both. rewrite -> lub_comp_left. apply Ole_antisym.
  * apply: (Ole_trans _ (le_lub _ i)).
    apply Oeq_le. simpl. do 2 rewrite -> ccomp_eq. simpl.
    do 3 rewrite comp_assoc. rewrite <- (comp_assoc (Embeddings i)).
    rewrite (emp i i). rewrite t_nn_ID. rewrite comp_idR.
    rewrite <- (comp_assoc (morph F _ _ _ _ _:M _ _)).
    rewrite -> (morph_comp F (Embeddings i) (Projections i)(Projections i) (Embeddings i)).
    rewrite -> (morph_eq_compat F (tset_trans (emp i i) (t_nn_ID _ _)) (tset_trans (emp i i) (t_nn_ID _ _))).
    rewrite -> morph_id. rewrite comp_idR. rewrite <- (comp_assoc (Injection i)).
    rewrite -> (proj1 (teppair DTower i)). by rewrite comp_idR.
  * rewrite -> (lub_lift_left _ i). apply: lub_le => k. simpl.
    apply Oeq_le. do 2 rewrite ccomp_eq.
    do 3 rewrite comp_assoc. rewrite <- (comp_assoc (Embeddings (i+k))).
    rewrite (emp _ _). rewrite t_nn_ID. rewrite comp_idR.
    rewrite <- (comp_assoc (morph F _ _ _ _ _:M _ _)).
    rewrite -> (morph_comp F (Embeddings (i + k)) (Projections (i + k)) (Projections i) (Embeddings i)).
    rewrite -> (morph_eq_compat F (emp i (i+k)) (emp (i+k) i)).
    rewrite -> morph_tnm. rewrite <- comp_assoc. rewrite <- (t_nmEmbedding DTower i (i + k).+1).
    rewrite <- comp_assoc. rewrite <- (t_nmProjection DTower i (i+k)). rewrite <- comp_assoc.
    rewrite <- (t_nmEmbedding2 DTower (leq_addr k i)). rewrite t_nmEmbedding. rewrite comp_assoc.
    rewrite <- morph_tnm.
    rewrite -> (morph_comp F (Projections (i+k)) (Embeddings (i+k)) (t_nm DTower (i+k) i) (t_nm DTower i (i+k))).
    by rewrite <- (morph_eq_compat F (@coneCom_l DTower (L DTower) _ _ (leq_addr k i)) (@coconeCom_l DTower DCoCone _ _ (leq_addr k i))).
- apply tset_sym. apply (@colimitUnique _ ECoLimit ECoLimit). move => n. by rewrite -> comp_idL.
Qed.
(*=End *)

Add Parametric Morphism C X Y Z W : (@morph C X Y Z W)
  with signature (@Ole ((cppoMorph Y X) * (cppoMorph Z W))) ==> (@Ole _)
  as morph_le_compat.
case => x x'. case => y y' e.
by apply: fmonotonic.
Qed.

Lemma delta_mon : monotonic (fun e => Fold << morph F _ _ _ _ (e,e) << Unfold).
move => e e' X. simpl.
by apply: (comp_le_compat (comp_le_compat (Ole_refl _) (morph_le_compat F (pair_le_compat X X))) (Ole_refl _)).
Qed.

Definition deltat : ordCatType (cppoMorph DInf DInf) (cppoMorph DInf DInf) := Eval hnf in mk_fmono delta_mon.

Lemma comp_lub_eq (D0 D1 D2 :M) (f:D1 =-> D2) (c:natO =-> cppoMorph D0 D1) :
   f << lub c =-= lub ((exp_fun (ccomp D0 D1 D2) f : ordCatType _ _) << c).
have a:=@lub_comp_eq _ _ ( (exp_fun (ccomp _ _ _) f)).
specialize (a D0 c). simpl in a. rewrite <- a. by rewrite ccomp_eq.
Qed.

Lemma lub_comp (D0 D1 D2 : M) (f:D0 =-> D1) (c:natO =-> cppoMorph D1 D2) :
   (lub c : M _ _) << f =-= lub ((exp_fun (ccomp D0 D1 D2 << <|pi2,pi1|>) f : ordCatType _ _) << c).
have a:=@lub_comp_eq _ _ ( (exp_fun (ccomp _ _ _ << <|pi2,pi1|>) f)).
specialize (a D2 c). rewrite <- a. simpl. by rewrite ccomp_eq.
Qed.

Lemma delta_cont : continuous deltat.
move => c. simpl. have S:=fmon_stable (morph F _ _ _ _).
specialize (S _ _ _ _ _ _ (pair_lub c c)).
rewrite -> (@lub_comp_eq _ _ ( (morph F _ _ _ _)) (<|c:natO =-> cppoMorph _ _,c|>)) in S.
rewrite -> S. clear S. rewrite comp_lub_eq. rewrite lub_comp.
apply: lub_le_compat => n. simpl. rewrite -> ccomp_eq. by rewrite ccomp_eq.
Qed.

Definition delta : (cppoMorph DInf DInf) =-> (cppoMorph DInf DInf) := 
  Eval hnf in mk_fcont delta_cont.
(*=Delta *)
Lemma delta_simpl e : delta e = Fold << morph F _ _ _ _ (e,e) << Unfold. 
(*CLEAR*)
by [].
Qed. (*CLEARED*)
(*=End *)

Require Import PredomFix.

Definition retract (C:catType) (A B : C) (f: A =-> B) (g : B =-> A) := f << g =-= Id.

Lemma retract_eq (C:catType) (X Y Z : C) (f:X =-> Y) g h (k:Z =-> X) : retract g f -> h =-= f << k -> g << h =-= k.
move => R A.
have B:=comp_eq_compat (tset_refl g) A. rewrite -> comp_assoc in B. rewrite -> R in B.
by rewrite -> comp_idL in B.
Qed.

Lemma delta_iter_id k : iter delta k <= (@Category.id M _:cppoMorph _ _).
elim:k ; first by apply: leastP.
move => n IH. simpl.
rewrite -> (comp_le_compat (comp_le_compat (Ole_refl (Fold:cppoMorph _ _))
                (morph_le_compat F (pair_le_compat IH IH))) (Ole_refl (Unfold:cppoMorph _ _))).
rewrite -> morph_id. rewrite comp_idR. by rewrite FU_id.
Qed.

Lemma delta_id_id : delta (@Category.id M _:cppoMorph DInf DInf) =-= @Category.id M _.
rewrite delta_simpl. rewrite morph_id. rewrite comp_idR. by rewrite FU_id.
Qed.

(*=FIXDelta *)
Lemma id_min : (FIXP delta : M _ _) =-= Id.
(*=End *)
rewrite <- EP_id.
apply: (tset_trans (@limitUnique DTower (L DTower) (L DTower) _ _) _).
- move => n. simpl. unfold fixp. rewrite -> lub_comp_right. apply Ole_antisym.
  + rewrite <- (le_lub _ n). simpl. rewrite ccomp_eq.
    elim: n. simpl. apply Oeq_le. have a:= terminal_unique. specialize (a M). by apply: a.
    move => n IH. simpl. unfold Unfold. unfold Fold. simpl.
    rewrite <- (comp_le_compat (Ole_refl (Projections n.+1:cppoMorph _ _)) (comp_le_compat (comp_le_compat (le_lub (chainFPE DCoCone) n.+1) (Ole_refl (morph F _ _ _ _ (iter_ delta n, iter_ delta n)))) (le_lub (chainPEc ECoCone) n.+1))).
    simpl. repeat rewrite comp_assoc. rewrite -> (emp n.+1 n.+1). rewrite t_nn_ID. rewrite comp_idL.
    rewrite morph_comp. rewrite -> (morph_eq_compat F (mcoconeCom (DCoCone) n) (mconeCom (L DTower) n)).
    rewrite morph_comp. rewrite <- (comp_assoc (morph F _ _ _ _ (Projection n, Injection n):M _ _)).
    rewrite morph_comp. rewrite -> (morph_eq_compat F (mconeCom (L DTower) n) (mcoconeCom DCoCone n)).
    rewrite morph_comp.
    have a:= (Ole_trans _ (comp_le_compat (morph_le_compat F (pair_le_compat ((Oeq_le (tset_sym (comp_assoc _ (iter_ delta n:M _ _) _)))) (Ole_refl _))) (Ole_refl _))). apply: a.
    have aa:= (comp_le_compat (morph_le_compat F (pair_le_compat (comp_le_compat IH (Ole_refl _)) (comp_le_compat IH (Ole_refl _)))) (Ole_refl _)). rewrite <- aa. clear aa.
    rewrite (emp n n). rewrite t_nn_ID. rewrite morph_id. by rewrite comp_idL.
  + apply: lub_le => k. simpl.
    rewrite ccomp_eq. 
    rewrite -> (comp_le_compat (Ole_refl _) (delta_iter_id k)). by rewrite comp_idR.
- apply tset_sym. apply limitUnique. move => n.
  rewrite EP_id. by rewrite comp_idR.
Qed.

End RecursiveDomains.

End Msolution.




