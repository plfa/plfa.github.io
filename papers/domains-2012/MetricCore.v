(**********************************************************************************
 * MetricCore.v                                                                   *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                       *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)


(** * Specification and properties of bisected ultrametric spaces *)

Require Export ssreflect ssrnat ssrbool eqtype.
Require Export Categories NSetoid.

Require Export Coq.Setoids.Setoid.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Open Scope nat_scope.

Open Scope S_scope.
Open Scope C_scope.

(*=Metric *)
Module Metric. Section Axioms.
  Variable M:setoidType.
  Variable Mrel : forall n : nat, M -> M -> Prop.
  Definition Mrefl x y := ((forall n, Mrel n x y) <-> x =-= y).
  Definition Msym n x y := Mrel n x y -> Mrel n y x.
  Definition Mtrans n x y z := Mrel n x y -> Mrel n y z -> Mrel n x z.
  Definition Mmono x y n := Mrel (S n) x y -> Mrel n x y.
  Definition Mbound x y := Mrel O x y.
  Definition axiom := forall n x y z, @Mrefl x y /\ @Msym n x y /\ @Mtrans n x y z /\
                                      @Mmono x y n /\ @Mbound x y.
  End Axioms.
  Record mixin_of (M:setoidType) : Type := Mixin
    { Mrel : forall n : nat, M -> M -> Prop; _ : axiom Mrel }. (*CLEAR*)  

  Section ClassDef.
Record class_of (T:Type) : Type :=
  Class { base : Setoid.class_of T ; met : mixin_of (Setoid.Pack base T) }.
  Local Coercion base : class_of >-> Setoid.class_of.
  Local Coercion met : class_of >-> mixin_of.

Structure type : Type := Pack { sort : Type; _ : class_of sort ; _ : Type}.
  Local Coercion sort : type >-> Sortclass.

Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
  let: Pack T c _ := cT return K _ (class cT) in k _ c.
Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT.

Definition pack := let k T c m := Pack (@Class T c m) T in Setoid.unpack k. (*CLEARED*) 
  Definition setoidType cT := Setoid.Pack (class cT) cT.
  End ClassDef.
  Module Import Exports.
  Coercion base : class_of >-> Setoid.class_of.
  Coercion met : class_of >-> mixin_of.
  Coercion sort : type >-> Sortclass.
  Coercion setoidType : type >-> Setoid.type.
Notation metricType := Metric.type. (*CLEAR*)  
Notation MetricMixin := Metric.Mixin. 
Notation MetricType := Metric.pack.
Canonical Structure Metric.setoidType.
(*CLEARED*)
End Exports.
End Metric.
Export Metric.Exports.

Bind Scope M_scope with Metric.sort.
Delimit Scope M_scope with Metric.
Open Scope M_scope.

Definition Mrel (m:metricType) : nat -> m -> m -> Prop :=
  let: Metric.Mixin r _ := Metric.met (Metric.class m) in r.
Notation "x '=' n '=' y" := (@Mrel _ n x y) : M_scope.
(*=End *)

Implicit Arguments Mrel [m].

Lemma Mrefl (m:metricType) (x y:m) : (forall n, x = n = y) <-> x =-= y.
unfold Mrel. case (Metric.met (Metric.class m)). move => r P. apply (proj1 (P O x y y)).
Qed.

Lemma Msym (m:metricType) n (x y:m) : x = n = y -> Mrel n y x.
unfold Mrel. case (Metric.met (Metric.class m)). move => r P. apply (proj1 (proj2 (P n x y y))).
Qed.

Lemma Mmono (M:metricType) (x y:M) n : x = n.+1 = y -> Mrel n x y.
unfold Mrel. case (Metric.met (Metric.class M)). move => r P.
apply (proj1 (proj2 (proj2 (proj2 (P n x y y))))).
Qed.

Lemma Mrel_trans (M:metricType) n (x y z:M) : x = n = y -> y = n = z -> x = n = z.
unfold Mrel. case (Metric.met (Metric.class M)) => r P.
by apply (proj1 (proj2 (proj2 (P n x y z)))).
Qed.

Lemma Mrel_mono (M:metricType) (x y:M) n m : n <= m -> x = m = y -> x = n = y.
elim: m.
- case n ; first by [].
  move => nn. by rewrite ltn0.
- move => m IH. rewrite leq_eqVlt. move => L. destruct (orP L) as [E | LL] ; first by rewrite (eqP E).
  specialize (IH LL). move => X. apply IH. by apply (Mmono X).
Qed.

Lemma Mtai (M:metricType) (x y z:M) n m : x = n = y -> y = m = z -> x = minn n m = z.
move => E E'. case_eq (n <= m) => L.
- have En:=Mrel_mono L E'. rewrite (minnl L). apply (Mrel_trans E En).
- rewrite leqNgt in L. have L':=negbFE L. clear L. have L:=ltnW L'. clear L'.
  rewrite (minnr L). by apply (Mrel_trans (Mrel_mono L E) E').
Qed.

Lemma Mbound (m:metricType) (x y:m) : x = O = y.
unfold Mrel. case (Metric.met (Metric.class m)). move => r P.
apply (proj2 (proj2 (proj2 (proj2 (P O x y x))))).
Qed.

Hint Resolve Mbound.
Hint Immediate Msym Mmono.

Lemma Mrel_refl (M:metricType) n (x:M) : Mrel n x x.
by apply (proj2 (Mrefl x x)).
Qed.

Hint Resolve Mrel_refl.

Hint Immediate Mrel_trans.

Add Parametric Relation (M:metricType) n : M (@Mrel M n : M -> M -> Prop)
  reflexivity proved by (@Mrel_refl M n) symmetry proved by (@Msym M n)
  transitivity proved by (@Mrel_trans M n) as Mrel_metricType.

Add Parametric Morphism (M:metricType) n : (@Mrel M n)
 with signature (@tset_eq _ : M -> M -> Prop) ==> (@tset_eq _ : M -> M -> Prop) ==> iff
 as metric_eq_compat.
move => x x' e y y' e'.
have r := proj2 (Mrefl x x') e n.
have r':= proj2 (Mrefl y y') e' n.
rewrite -> r. by rewrite -> r'.
Qed.

(*=cchainp *)
Definition cchainp (M:metricType) (x:nat -> M) : Prop :=
   forall n i j, n <= i -> n <= j ->  (x i) = n = (x j).
Record cchain (M:metricType) : Type := mk_cchain
  { tchain :> nat -> M; cchain_cauchy : cchainp tchain }.
(*=End *)

Lemma cutnP (n:nat) M (c:cchain M) : cchainp (M:=M) (fun i : nat => c (n + i)%N).
move => m i j l l'. by apply (cchain_cauchy c (leq_trans l (leq_addl n i)) (leq_trans l' (leq_addl n j))).
Qed.

Definition cutn (n:nat) M (c:cchain M) : cchain M := mk_cchain (cutnP n c).

Lemma const_cchainP (M:metricType) (x:M) : cchainp (M:=M) (fun _ : nat => x).
by [].
Qed.

Definition const_cchain (M:metricType) (x:M) : cchain M := mk_cchain (const_cchainP x).

Lemma const_cchain_simpl (M:metricType) (x:M) i : const_cchain x i = x.
by [].
Qed.

(*=cmetric *)
Definition mconverge (M:metricType) (c:cchain M) (x:M) : Prop :=
  forall n, exists m, forall i, m <= i -> (c i) = n = x.
Module CMetric.
  Definition axiom M (comp:cchain M -> M) := forall c, mconverge c (comp c).
  Record mixin_of (M : metricType) : Type := Mixin
    { comp : cchain M -> M; _ : axiom comp }. (*CLEAR*)
Section ClassDef. 
Record class_of (T : Type) : Type := Class
{ base : Metric.class_of T;
  ext : mixin_of (Metric.Pack base T) }.
Local Coercion base : class_of >-> Metric.class_of.
Local Coercion ext : class_of >-> mixin_of.
(*CLEARED*) 
  Structure type : Type := Pack {sort : Type; _ : class_of sort; _ : Type}. (*CLEAR*)  
Local Coercion sort : type >-> Sortclass.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
  let: Pack T c _ := cT return K _ (class cT) in k _ c.
Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT.

Definition pack := let k T c m := Pack (@Class T c m) T in Metric.unpack k.

Definition setoidType cT := Setoid.Pack (class cT) cT. (*CLEARED*) 
Definition metricType cT := Metric.Pack (class cT) cT.
End ClassDef.
Module Import Exports.
Coercion sort : type >-> Sortclass.
Coercion metricType : type >-> Metric.type.
Coercion base : class_of >-> Metric.class_of.
Coercion ext : class_of >-> mixin_of.
Notation cmetricType := CMetric.type. (*CLEAR*) 
Notation CMetricMixin := CMetric.Mixin.
Notation CMetricType := CMetric.pack.
Canonical Structure CMetric.setoidType.
Canonical Structure CMetric.metricType.
(*CLEARED*) 
End Exports.
End CMetric.
Export CMetric.Exports.

Definition umet_complete (M:cmetricType) : cchain M -> M := 
  CMetric.comp (CMetric.class M).
(*=End *)

Lemma cumet_conv (M:cmetricType) (c:cchain M) : mconverge c (umet_complete c).
unfold umet_complete. move: c. unfold CMetric.metricType. case: (CMetric.class M). simpl.
move => b. case. simpl. move => comp P. apply P.
Qed.

Lemma umet_complete_extn (M:cmetricType) (c c':cchain M) n :
   (forall i, c i = n = c' i) -> umet_complete c = n = umet_complete c'.
move => C. destruct (cumet_conv c n) as [x X]. destruct (cumet_conv c' n) as [x' X'].
specialize (X (maxn x x')). specialize (X' (maxn x x')).
rewrite -> leq_maxr in X',X. rewrite -> leqnn in X',X. rewrite orbT in X'.
specialize (X' is_true_true). specialize (X is_true_true). specialize (C (maxn x x')).
by apply (Mrel_trans (Msym X) (Mrel_trans C X')).
Qed.

Lemma umet_complete_ext (M:cmetricType) (c c':cchain M) :
  (forall i, c i =-= c' i) -> (umet_complete c) =-= (umet_complete c').
move =>  C. apply: (proj1 (Mrefl _ _)). move => n. apply umet_complete_extn.
move => i. by apply (proj2 (Mrefl _ _) (C i)).
Qed.

Lemma umet_complete_const (M:cmetricType) (x:M) : umet_complete (const_cchain x) =-= x.
apply: (proj1 (Mrefl _ _)). move => n.
destruct (cumet_conv (const_cchain x) n) as [m X]. specialize (X m). rewrite leqnn in X.
specialize (X is_true_true). simpl in X. by apply (Msym X).
Qed.

Lemma cut_complete_eq n (M:cmetricType) (c:cchain M) : umet_complete c =-= umet_complete (cutn n c).
apply: (proj1 (Mrefl _ _)). move => m.
destruct (cumet_conv c m) as [x X]. destruct (cumet_conv (cutn n c) m) as [x' X'].
specialize (X (n+(maxn x x'))%N). specialize (X' (maxn x x')).
have A:x <= maxn x x' by rewrite -> leq_maxr ; by rewrite -> leqnn.
specialize (X (leq_add (leq0n n) A)).
rewrite -> leq_maxr in X'. rewrite -> leqnn in X'. rewrite orbT in X'.
specialize (X' is_true_true). simpl in X'.
by apply (Mrel_trans (Msym X) X').
Qed.

Add Parametric Relation (M:cmetricType) (n:nat) : M (fun x y => @Mrel M n x y)
       reflexivity proved by (@Mrel_refl M n) symmetry proved by (@Msym M n)
       transitivity proved by (@Mrel_trans M n) as Mrel_Relation.

(*=nonexpansive *)
Definition nonexpansive (M M':metricType) (f:M -> M') : Prop :=
  forall (n : nat) (e e' : M), e = n = e' -> f e = n = f e'.
Module FMet. Section fmet.
  Variable O1 O2 : metricType.
  Record mixin_of (f:O1 -> O2) := Mixin { nonexp :> nonexpansive f }.
  Notation class_of := mixin_of (only parsing). (*CLEAR*) 
  Lemma ner (M M':metricType) (f:M -> M') (ne:nonexpansive f) : setoid_respect f.
move => x x' e.
apply (proj1 (Mrefl _ _)) => n. apply ne. by apply (proj2 (Mrefl _ _)).
Qed.

  Section ClassDef.
  Definition base2 (f:O1 -> O2) (c:class_of f) : FSet.mixin_of f := fsetMixin (ner c). (*CLEARED*)
  Local Coercion base2 : class_of >-> FSet.mixin_of.
  Structure type : Type := Pack {sort : O1 -> O2; _ : class_of sort; _ : O1 -> O2}. (*CLEAR*)
  Local Coercion sort : type >-> Funclass.
  Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
  Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
    let: Pack T c _ := cT return K _ (class cT) in k _ c.
  Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT.
  Definition pack f (c:class_of f) := @Pack f c f.
  Definition fset f : fset O1 O2 := FSet.Pack (class f) f.
  End ClassDef.
 (*CLEARED*) End fmet.
Module Import Exports.
Coercion fset : type >-> FSet.type.
Coercion base2 : mixin_of >-> FSet.mixin_of.
Coercion sort : type >-> Funclass.
Notation fmet := FMet.type.
Notation fmetMixin := Mixin.
Notation fmetType := pack.
Canonical Structure fset.
End Exports.
End FMet.
Export FMet.Exports.
(*=End *)

Lemma fnonexpansive (M M':metricType) (f: fmet M M') : nonexpansive f.
case: f => f. case => a f'. simpl. by apply a.
Qed.

Definition mk_fmetM (M M':metricType) (f:M -> M') (ne:nonexpansive f) := fmetMixin ne.
Definition mk_fmet (M M':metricType) (f:M -> M') (ne:nonexpansive f) := Eval hnf in fmetType (mk_fmetM ne).

Lemma metric_morphSP (T T' : metricType) : Setoid.axiom (fun (f g:fmet T T') => forall x:T, f x =-= g x).
split ; last split.
- by move => f.
- move => f g h. simpl. move => X Y e. by apply (tset_trans (X e) (Y e)).
- move => f g. simpl. move => X e. by apply (tset_sym (X e)).
Qed.

Canonical Structure morph_metricSMixin (T T':metricType) := Setoid.Mixin (metric_morphSP T T').
Canonical Structure morph_metricSType T T' := Eval hnf in SetoidType (morph_metricSMixin T T').

Lemma Mrel_respect2 (M M':metricType) n : setoid_respect2 (fun f g : fmet M M' => forall x, (f x) = n = (g x) : Props).
simpl. split.
- move => h f g. unlock tset_eq. move => X. split => Y e.
  + specialize (Y e). specialize (X e). by apply (Mrel_trans (Msym (proj2 (Mrefl _ _) X n)) Y).
  + specialize (Y e). specialize (X e). by apply (Mrel_trans ((proj2 (Mrefl _ _) X n)) Y).
- move => h f g. unlock tset_eq. move => X. split => Y e.
  + specialize (Y e). specialize (X e). by apply (Mrel_trans Y (proj2 (Mrefl _ _) X n)).
  + specialize (Y e). specialize (X e). by apply (Mrel_trans Y (Msym (proj2 (Mrefl _ _) X n))).
Qed.

Lemma metric_morphP (M M':metricType) : Metric.axiom (fun n (f g : fmet M M') => forall x, f x = n = g x).
move => n f g h. simpl ; split ; last split ; last split ; last split.
- simpl. split.
  + move => C x. have C':=C _ x. clear C. by apply (proj1 (Mrefl _ _) C').
  + move => C n' x. apply (proj2 (Mrefl (f x) (g x))). unlock tset_eq in C. by apply C.
- move => C. simpl => x. simpl in C. by apply (Msym (C x)).
- move => X Y. simpl => x. by apply Mrel_trans with (y:= g x) ; [apply X | apply Y].
- move => C. simpl => x. specialize (C x). by apply (Mmono C).
- by [].
Qed.

Canonical Structure fmet_metricMixin (T T':metricType) := Metric.Mixin (@metric_morphP T T').
Canonical Structure fmet_metricType T T' := Eval hnf in MetricType (fmet_metricMixin T T').

(** printing -n> %\nonexpmorph% *)
(*Infix "-n>" := morph_metricType (at level 45, right associativity) : M_scope.*)

(*=contractive *)
Definition contractive M N (f:fmet M N) : Prop := 
  forall n x y, x = n = y -> f x = n.+1 = f y.
(*=End *)
    
Definition liftc M M' (f:fmet M M') (c:cchain M) : cchain M'.
exists (fun n => f (c n)).
move => n i j l l'. simpl. apply: fnonexpansive. by apply (cchain_cauchy c l l').
Defined.

Definition binaryLimit M N P (f:fmet M (fmet_metricType N P)) (c:cchain M) (c':cchain N) : cchain P.
exists (fun n => f (c n) (c' n)).
move => n i j l l'. simpl. have X:= (cchain_cauchy c l l'). have X':=cchain_cauchy c' l l'.
have a:=fnonexpansive f X. specialize (a (c' i)). simpl in a. apply (Mrel_trans a).
by apply (fnonexpansive (f (c j)) X').
Defined.

Lemma binaryLimit_simpl M N P (f:fmet M (fmet_metricType N P)) (c:cchain M) (c':cchain N) n : binaryLimit f c c' n = f (c n) (c' n).
by [].
Qed.

Lemma nonexp_continuous (M N:cmetricType) (f:fmet M N) (c:cchain M) : f (umet_complete c) =-= umet_complete (liftc f c).
apply (proj1 (Mrefl _ _)). move => n.
destruct (cumet_conv (liftc f c) n) as [m A].
simpl in A. destruct (cumet_conv c n) as [m' B]. specialize (A (maxn m m')).
specialize (B (maxn m m')). rewrite -> leq_maxr in A,B. rewrite -> leqnn in A, B. rewrite orbT in B.
specialize (A is_true_true). specialize (B is_true_true).
by refine (Mrel_trans (Msym (fnonexpansive f B)) A).
Qed.

Lemma Scomp_ne S S' S'' (f:fmet S' S'') (g:fmet S S') : nonexpansive (fun x => f ( g x)).
move => n x y e.
apply: (fnonexpansive f). by apply (fnonexpansive g e).
Qed.

Definition mcomp S S' S'' (f:fmet S' S'') (g:fmet S S') : (fmet S S'') := Eval hnf in mk_fmet (Scomp_ne f g).

(*
Lemma mcomp_simpl S S' S'' f g x : @mcomp S S' S'' f g x = f (g x).
by [].
Qed.*)

Lemma Sid_ne (A:metricType) : nonexpansive (@id A).
by [].
Qed.

Definition mid A : fmet A A := Eval hnf in mk_fmet (@Sid_ne A).

(*
Lemma mid_simpl A x : @mid A x = x.
by [].
Qed.*)

Lemma metricCatAxiom : Category.axiom (@mcomp) (@mid).
split ; first by move => M M' f. split ; first by move => M M' f.
split ; first by move => M0 M1 M2 M3 f g h.
move => M0 M1 M2. simpl. move => f f' g g' e e'.
move => x. apply tset_trans with (y:=f (g' x)). apply: (frespect f). by apply e'.
by apply e.
Qed.

Canonical Structure metricCatMixin := CatMixin metricCatAxiom.
Canonical Structure metricCatType := Eval hnf in CatType metricCatMixin.

Lemma cmetricCatAxiom : Category.axiom (fun X Y Z :cmetricType => @mcomp X Y Z) (fun X => @mid X).
split ; first by move => X Yf ; apply (proj1 metricCatAxiom).
split ; first by move => X Yf ; apply (proj1 (proj2 metricCatAxiom)).
split ; first by move => X Y Z W f g h ; apply (proj1 (proj2 (proj2 metricCatAxiom)) X Y Z W f g h).
move => X Y Z f f' e g g' e'. by apply: (proj2 (proj2 (proj2 metricCatAxiom)) X Y Z _ _ e _ _ e').
Qed.

Canonical Structure cmetricCatMixin := CatMixin cmetricCatAxiom.
Canonical Structure cmetricCatType := Eval hnf in CatType cmetricCatMixin.

Open Scope C_scope.

Section MetricProducts.
Variable A B : metricType.

Lemma prod_setoid_respect2 : forall n : nat,
      setoid_respect2 (S:=(Metric.setoidType A * B)) (S':=Metric.setoidType A * B) (S'':=Props)
        (fun a b : A * B => fst a = n = fst b /\ snd a = n = snd b).
move => n. split.
  - case => a b ; case => c d ; case => e f ; simpl. move => [X Y].
    have X':=Msym (proj2 (Mrefl _ _) X n). have Y':=Msym (proj2 (Mrefl _ _) Y n).
    clear X Y. split ; move => [X Y] ; first by split ; [apply (Mrel_trans X' X) | apply (Mrel_trans Y' Y)].
    split ; by [apply (Mrel_trans (Msym X') X) | apply (Mrel_trans (Msym Y') Y)].
  - case => a b ; case => c d ; case => e f ; simpl. move => [X Y].
    have X':=Msym (proj2 (Mrefl _ _) X n). have Y':=Msym (proj2 (Mrefl _ _) Y n).
    clear X Y. split ; move => [X Y] ; first by split ; [apply (Mrel_trans X (Msym X')) | apply (Mrel_trans Y (Msym Y'))].
    split ; by [apply (Mrel_trans X X') | apply (Mrel_trans Y Y')].
Qed.

Lemma prod_metric_axiom : Metric.axiom (fun (n : nat) (a b : A * B) => fst a = n = fst b /\ snd a = n = snd b).
- move => n ; case => a b ; case => c d ; case => e f. split ; last split ; last split ; last split ; simpl ; clear.
  split ; move => X ; first by split ; apply (proj1 (Mrefl _ _)) ; move => n ; destruct (X n) ; auto.
  move => n. by split ; [apply (proj2 (Mrefl _ _) (proj1 X)) | apply (proj2 (Mrefl _ _) (proj2 X))].
- move => [X Y]. simpl. split ; by apply Msym.
- move => [X Y] [Z W]. simpl. by split ; [apply (Mrel_trans X Z) | apply (Mrel_trans Y W)].
- by move => [X Y] ; split ; apply Mmono.
- by split.
Qed.

Canonical Structure prod_metricMixin := Metric.Mixin prod_metric_axiom.
Canonical Structure prod_metricType := Eval hnf in MetricType prod_metricMixin.

Lemma Sfst_ne : nonexpansive (@fst A B).
move => n. case => a b ; case => c d ; simpl. move => [X Y] ; by [].
Qed.

Lemma Ssnd_ne : nonexpansive (@snd A B).
move => n. case => a b ; case => c d ; simpl. move => [X Y] ; by [].
Qed.

Definition mfst : prod_metricType =-> A := Eval hnf in mk_fmet Sfst_ne.
Definition msnd : prod_metricType =-> B := Eval hnf in mk_fmet Ssnd_ne.

Variable C:metricType.
Variable (f:C =-> A) (g:C =-> B).

Lemma Sprod_fun_ne : nonexpansive (fun x => (f x, g x)).
move => n c c' e. simpl. by split ; [apply (fnonexpansive f e) | apply (fnonexpansive g e)].
Qed.

Definition mprod_fun : C =-> prod_metricType := Eval hnf in mk_fmet Sprod_fun_ne.

End MetricProducts.

Lemma metricProdCatAxiom : @CatProduct.axiom _ prod_metricType (@mfst) (@msnd) (@mprod_fun).
move => A B C f g. split ; first by split.
move => m [P Q] x. specialize (P x). specialize (Q x). apply tset_trans with (y:=(f x, g x)) ; last by [].
rewrite <- (pair_eq_compat P Q). simpl. by case: (m x).
Qed.

Canonical Structure metricProdMixin := prodCatMixin metricProdCatAxiom.
Canonical Structure metricProdCatType := Eval hnf in prodCatType metricProdMixin.

Section CompleteProducts.
Variable A B : cmetricType.

Lemma prod_cmetric_axiom  : CMetric.axiom (fun c => (umet_complete (liftc (@mfst A B) c), umet_complete (liftc (@msnd A B) c))).
move => c n.
destruct (cumet_conv (liftc (@mfst A B) c) n) as [m0 C].
destruct (cumet_conv (liftc (@msnd A B) c) n) as [m1 C'].
exists (maxn m0 m1). move => i L. specialize (C i). specialize (C' i).
rewrite leq_maxl in L. specialize (C (proj1 (andP L))). specialize (C' (proj2 (andP L))).
split ; simpl ; [by apply: Mrel_trans _ C | by apply: Mrel_trans _ C'].
Qed.

Canonical Structure prod_cmetricMixin := CMetric.Mixin prod_cmetric_axiom.
Canonical Structure prod_cmetricType := Eval hnf in CMetricType prod_cmetricMixin.

End CompleteProducts.

Lemma cmetricProdCatAxiom :@CatProduct.axiom _ prod_cmetricType (fun A B => @mfst A B) (fun A B => @msnd A B) 
           (fun A B C => @mprod_fun A B C).
move => A B C f g. split ; first split.
by apply (proj1 (proj1 (metricProdCatAxiom f g))).
by apply (proj2 (proj1 (metricProdCatAxiom f g))).
move => m. by apply (proj2 (metricProdCatAxiom f g) m).
Qed.

Canonical Structure cmetricProdMixin := prodCatMixin cmetricProdCatAxiom.
Canonical Structure cmetricProdCatType := Eval hnf in prodCatType cmetricProdMixin.

Lemma mpair_ne (A B : metricType) (x:A) : nonexpansive (fun (y:B) => (x,y)).
move => n y y' e. simpl. by split.
Qed.

Definition mpair (A B : metricType) (x:A) : B =-> A * B := Eval hnf in mk_fmet (mpair_ne x).

Lemma mcurry_ne (A B C:metricType) (f:A * B =-> C) : nonexpansive (fun x => f << mpair _ x).
move => n x x' e z. simpl. apply: fnonexpansive. by split.
Qed.

Definition mcurry (A B C:metricType) (f:A * B =-> C) : A =-> (fmet_metricType B C) := Eval hnf in mk_fmet (mcurry_ne f).

Section mexponential.

Lemma Snev_ne (A B:metricType) : nonexpansive (fun p: (B =-> A) * B => fst p (snd p)).
move => n. case => f x. case => f' x'. case. simpl.
move => X Y. apply Mrel_trans with (y:=f x') ; first by apply: fnonexpansive.
by apply X.
Qed.

Definition mev B A : (fmet_metricType B A) * B =-> A := Eval hnf in mk_fmet (@Snev_ne A B).

Lemma metricExpCatAxiom : @CatExp.axiom _ fmet_metricType (@mev) (@mcurry).
move => A B C f. split ; first by case.
move => h X x y. specialize (X (x,y)). by apply X.
Qed.

End mexponential.

Canonical Structure metricExpMixin := expCatMixin metricExpCatAxiom.
Canonical Structure metricExpCatType := Eval hnf in expCatType metricExpMixin.

Lemma lift_comp M N (Q:cmetricType) (f: N =-> Q) (g:M =-> N) (c:cchain M) :
    umet_complete (liftc f (liftc g c)) =-= umet_complete (liftc (f << g) c).
by apply umet_complete_ext.
Qed.

Lemma Mcomp_ne (A B C:metricType) : nonexpansive (fun (p:(B =-> C) * (A =-> B)) => fst p << snd p).
move => n. case => f g. case => f' g'. case => X Y x.
simpl. apply Mrel_trans with (y:= f (g' x)) ; first by apply: fnonexpansive; apply Y.
by apply X.
Qed.

Definition MComp (A B C:metricType) : ((B -=> C) * (A -=> B)) =-> (A -=> C) := Eval hnf in mk_fmet (@Mcomp_ne A B C).

Lemma MComp_simpl (A B C:metricType) (f:B =-> C) (g:A =-> B) : MComp _ _ _ (f,g) = f << g.
by [].
Qed.

Lemma sconst_ne (M M':metricType) (x:M') : nonexpansive (fun _ : M => x).
by [].
Qed.

Definition mconst (M M':metricType) (x:M') : M =-> M' := Eval hnf in mk_fmet (sconst_ne x).

Lemma mconst_contractive (A B:metricType) x : contractive (@mconst A B x).
move => n a b e. by apply Mrel_refl.
Qed.

Lemma One_setoid_respect2 : setoid_respect2 (fun (x:One:setoidType) (y:One:setoidType) => True).
by [].
Qed.

Lemma One_metric_axiom : Metric.axiom (fun (_ : nat) (x y : unit) => True).
move => n. by case ; case ; case.
Qed.

Canonical Structure unit_metricMixin := Metric.Mixin One_metric_axiom.
Canonical Structure unit_metricType := Eval hnf in MetricType unit_metricMixin.

Lemma metricTerminalAxiom : CatTerminal.axiom unit_metricType.
by [].
Qed.

Canonical Structure metricTerminalMixin := terminalCatMixin (fun M => @mconst M unit_metricType tt) metricTerminalAxiom.
Canonical Structure metricTerminalType := Eval hnf in terminalCatType metricTerminalMixin.

Lemma unit_cmetricMixinP : @CMetric.axiom One (fun _ => tt).
move => c. simpl. move => n. by exists 0.
Qed.

Canonical Structure unit_cmetricMixin := CMetric.Mixin unit_cmetricMixinP.
Canonical Structure unit_cmetricType := Eval hnf in CMetricType unit_cmetricMixin.

Lemma cmetricTerminalAxiom : CatTerminal.axiom unit_cmetricType.
by [].
Qed.

Canonical Structure cmetricTerminalMixin := terminalCatMixin (fun (M:cmetricType) => @mconst M unit_cmetricType tt) cmetricTerminalAxiom.
Canonical Structure cmetricTerminalType := Eval hnf in terminalCatType cmetricTerminalMixin.

(*=iter *)
Fixpoint iter n (M:metricType) (f:M -> M) :=
    match n with | O => id  | S n => fun x => f (iter n f x) end.
(*=End *)
  
Lemma iter_ne n (M:metricType) (f:M =-> M) : nonexpansive (iter n f).
elim: n ; first by [].
move => n IH.
simpl. move => m e e' E. simpl. specialize (IH m _ _ E). by apply (fnonexpansive f IH).
Qed.

Definition itern (n:nat) (M:metricType) (f:M =-> M) : M =-> M := Eval hnf in mk_fmet (iter_ne n f).

Lemma iter_plus (M:metricType) f (x:M) m m' : iter m' f (iter m f x) = iter (m'+m) f x.
elim: m' ; first by [].
move => n IH. simpl. by rewrite IH.
Qed.

Lemma bounded_contractive_n M (f:M =-> M) (C:contractive f) n m x y : n <= m -> (iter m f x) = n = (iter m f y).
elim: n m x y; first by [].
move => n IH. case ; first by [].
move => m x y L. specialize (IH m x y L). simpl. apply C. by apply IH.
Qed.

Module NonEmpty.

Record mixin_of (T:Type) : Type := Mixin { elem : T }.

Notation class_of := mixin_of.

Section ClassDef.
Structure type : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
  let: Pack T c _ := cT return K _ (class cT) in k _ c.
Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT.
Definition pack T c := @Pack T c T.
End ClassDef.
Module Import Exports.
Coercion sort : type >-> Sortclass.
Notation nonemptyType := type.
Notation NonEmptyMixin := Mixin.
Notation NonEmptyType := pack.
Canonical Structure nonempty (T:Type) (x:T) := NonEmpty.Mixin x.
End Exports.
End NonEmpty.
Export NonEmpty.Exports.

Definition nonempty_elem := NonEmpty.elem.

(*=cfixP *)
Lemma cfixP (M:cmetricType) (f:M =-> M) (C:contractive f) x :
                                 cchainp (fun n => iter n f x). (*CLEAR*) 
move => n i j l l'. simpl.
have A:=(bounded_contractive_n C (iter (i - n) f x) (iter (j - n) f x)) (leqnn n).
do 2 rewrite iter_plus in A. rewrite subnKC in A ; last by []. rewrite subnKC in A ; last by []. by apply A.
Qed.

(*CLEARED*)
Definition cfix (M:cmetricType) f C x : cchain M := mk_cchain (@cfixP M f C x).
Definition fixp (M:cmetricType) f C x : M := umet_complete (@cfix M f C x).
(*=End *)
Lemma nonexpansive_iter (M:metricType) (f:M =-> M) m n x y : x =n= y -> iter m f x =n= iter m f y.
elim: m x y ; first by [].
move => m IH x y E. simpl. by apply (fnonexpansive f (IH _ _ E)).
Qed.

(*=fixeq *)
Lemma fixp_eq (M:cmetricType) (f:M =-> M) (C:contractive f) (x:M) :
                           fixp C x =-= f (fixp C x). (*CLEAR*) 
refine (proj1 (@Mrefl M ((fixp C x)) (f (fixp C x))) _). move => n.
unfold fixp. destruct (cumet_conv (cfix C x) n) as [m0 X].
specialize (X(maxn n m0)). rewrite leq_maxr in X. rewrite leqnn in X. rewrite orbT in X.
specialize (X is_true_true). apply: (Mrel_trans (Msym X) _).
apply: (Mrel_trans _ (fnonexpansive f X)). have B:=bounded_contractive_n C x (iter 1 f x).
specialize (B n (maxn n m0)). rewrite iter_plus in B. clear X.
simpl. rewrite addnC in B. rewrite leq_maxr in B. rewrite leqnn in B. specialize (B is_true_true).
by apply (Mrel_trans B).
Qed.

Lemma fixp_iter (M:cmetricType) (f:M =-> M) (C:contractive f) x i : fixp C x =-= iter i f (fixp C x).
elim:i ; first by [].
move => n IH. simpl. rewrite <- (frespect f IH). by apply fixp_eq.
Qed.

(*CLEARED*) 
Lemma fixp_unique (M:cmetricType) f (C:contractive f) (x y:M) :
                         fixp C x =-= fixp C y. (*CLEAR*) 
apply: (proj1 (Mrefl _ _)). move => n.
unfold fixp.
destruct (cumet_conv (cfix C x) n) as [m0 X].
destruct (cumet_conv (cfix C y) n) as [m1 Y].
specialize (X(maxn n (maxn m0 m1))). specialize (Y(maxn n (maxn m0 m1))).
rewrite -> leq_maxr in X, Y. rewrite -> leq_maxr in X,Y. rewrite -> leqnn in X,Y. rewrite -> orbT in X, Y.
rewrite orbT in Y.
specialize (X is_true_true). specialize (Y is_true_true). apply: (Mrel_trans (Msym X) _).
apply: (Mrel_trans _ Y). clear X Y. apply: (bounded_contractive_n C x y).
rewrite leq_maxr. by rewrite leqnn.
Qed.

(*CLEARED*) 
Lemma fixp_ne (M:cmetricType) f f' (C:contractive f) (C':contractive f') 
  (x x':M) n : f = n = f' -> fixp C x = n= fixp C' x'.
(*=End *)      
simpl. move => E. refine (Mrel_trans _ (proj2 (Mrefl _ _) (fixp_unique C' x x') n)).
clear x'. unfold fixp.
destruct (cumet_conv (cfix C x) n) as [m X].
destruct (cumet_conv (cfix C' x) n) as [m' Y].
specialize (X (maxn m m')). specialize (Y (maxn m m')). rewrite -> leq_maxr in X,Y. rewrite -> leqnn in X,Y.
rewrite orbT in Y. specialize (X is_true_true). specialize (Y is_true_true).
apply (Mrel_trans (Msym X)). refine (Mrel_trans _ Y). clear X Y. simpl.
elim: (maxn m m') ; first by [].
move => i IH. simpl. apply Mrel_trans with (y:=f' (iter i f x)) ; first by apply E.
apply fnonexpansive. by apply IH.
Qed.

Lemma chain_appP (M M':metricType) (c:cchain (M -=> M')) (x:M) : cchainp (fun n : nat => c n x).
move => n i j l l'. simpl. by apply (cchain_cauchy c l l' x).
Qed.

Definition chain_app M M' (c:cchain (M -=> M')) (x:M) : cchain M' := mk_cchain (chain_appP c x).

Lemma fun_lub_ne (M M':cmetricType) (c:cchain (fmet_metricType M M')) : nonexpansive (fun x : M => umet_complete (chain_app c x)).
move => n e e' R. simpl.
destruct (cumet_conv (chain_app c e) n) as [m0 A].
destruct (cumet_conv (chain_app c e') n) as [m1 B].
specialize (A ((maxn m0 m1))). specialize (B ((maxn m0 m1))).
rewrite -> leq_maxr in A, B. rewrite -> leqnn in A,B. rewrite -> orbT in B.
specialize (A is_true_true). specialize (B is_true_true). apply: Mrel_trans (Msym A) _. apply: Mrel_trans _ B.
clear A. simpl. by apply (fnonexpansive (c (maxn m0 m1)) R).
Qed.

Definition fun_lub (M M':cmetricType) (c:cchain (fmet_metricType M M')) : M =-> M' := Eval hnf in mk_fmet (fun_lub_ne c).

Lemma fun_lub_simpl (M M':cmetricType) (c:cchain (fmet_metricType M M')) (x:M) : fun_lub c x = umet_complete (chain_app c x).
by [].
Qed.

Lemma cmetric_morphP M M' : CMetric.axiom (fun_lub (M:=M) (M':=M')).
move => c n. exists n => i l.
have A:=cchain_cauchy c l. move => x. destruct (cumet_conv (chain_app c x) n) as [m0 X]. rewrite fun_lub_simpl.
specialize (A (maxn n m0)). specialize (X (maxn n m0)). rewrite -> leq_maxr in X, A. rewrite -> leqnn in X,A.
rewrite orbT in X. specialize (A is_true_true). specialize (X is_true_true). specialize (A x). simpl in A. simpl in X.
by apply (Mrel_trans A X).
Qed.

Canonical Structure morph_cmetricMixin (T T':cmetricType) := CMetric.Mixin (@cmetric_morphP T T').
Canonical Structure morph_cmetricType T T' := Eval hnf in CMetricType (morph_cmetricMixin T T').

Lemma cmetricExpCatAxiom : @CatExp.axiom _ morph_cmetricType (fun X Y => @mev X Y) (fun X Y Z => @mcurry X Y Z).
move => A B C f. split ; first by case.
move => h X x y. specialize (X (x,y)). by apply X.
Qed.

Canonical Structure cmetricExpMixin := expCatMixin cmetricExpCatAxiom.
Canonical Structure cmetricExpCatType := Eval hnf in expCatType cmetricExpMixin.

Section IProducts.

Variable I : Type.
Variable P : I -> metricType.

Lemma prodI_metric_axiom : Metric.axiom (fun (n : nat) (a b : prodI_setoidType P) => forall i, @Mrel (P i) n (Sproj P i a) (Sproj P i b)).
move => n x y z ; split ; last split ; last split ; last split ; simpl ; clear.
  split ; move => X ; first by move => i ; apply (proj1 (Mrefl _ _)) ; move => n ; apply (X n i).
  move => n i. by apply (proj2 (Mrefl _ _) (X i)).
- move => X. simpl => i. by apply Msym.
- move => X Y. simpl => i. by apply (Mrel_trans (X i) (Y i)).
- move => X. by simpl => i ; apply Mmono ; auto.
- by [].
Qed.

Canonical Structure prodI_metricMixin := Metric.Mixin prodI_metric_axiom.
Canonical Structure prodI_metricType := Eval hnf in @MetricType (prodI_setoidType (fun x : I => P x)) prodI_metricMixin.

Lemma Sproj_ne i : nonexpansive (Sproj P i:setoidCat prodI_metricType (P i)).
by [].
Qed.

Definition mproj i : prodI_metricType =-> P i := Eval hnf in mk_fmet (Sproj_ne i).

Lemma mproj_simpl (i:I) (x:prodI_metricType) : mproj i x = x i.
by [].
Qed.

Variable C:metricType.
Variable f:forall i, C =-> P i.

Lemma SprodI_fun_ne : nonexpansive (SprodI_fun f : setoidCat C prodI_metricType).
move => n c c' e. simpl. by move => i ; apply (fnonexpansive  (f i) e).
Qed.

Definition mprodI_fun : C =-> prodI_metricType := Eval hnf in mk_fmet SprodI_fun_ne.

Lemma mprodI_fun_proj i : (mproj i) << (mprodI_fun) =-= f i.
by [].
Qed.

Lemma mprodI_fun_unique (h:C =-> prodI_metricType) :
   (forall i, mproj i << h =-= f i) -> h =-= mprodI_fun.
move => X x. apply (SprodI_fun_unique X).
Qed.

End IProducts.

Lemma metricProdICatAxiom I : @CatIProduct.axiom _ I (@prodI_metricType I) (@mproj I) (@mprodI_fun I).
move => P Z f. split ; first by move => x y.
move => m X x i. simpl. by apply (X i x).
Qed.

Canonical Structure metricProdIMixin := prodICatMixin metricProdICatAxiom.
Canonical Structure metricProdICatType := Eval hnf in prodICatType metricProdIMixin.

Section ICProducts.
Variable I : Type.
Variable P : I -> cmetricType.

Lemma prodI_cmetric_axiom : @CMetric.axiom (prodI_metricType P) (fun c => (fun n => umet_complete (liftc (mproj P n) c))).
move => c n. exists n => j L i. simpl.
destruct (cumet_conv (liftc (mproj P i) c) n) as [m X]. simpl in X.
specialize (X (maxn n m)). rewrite leq_maxr in X. rewrite leqnn in X. rewrite orbT in X.
specialize (X is_true_true). simpl in X. apply: (Mrel_trans _ X). clear X.
have C:=cchain_cauchy c. specialize (C n j (maxn n m) L). rewrite leq_maxr in C. rewrite leqnn in C.
specialize (C is_true_true). specialize (C i). simpl in C. by apply C.
Qed.

Canonical Structure prodI_cmetricMixin := CMetric.Mixin prodI_cmetric_axiom.
Canonical Structure prodI_cmetricType := Eval hnf in @CMetricType (prodI_metricType P) prodI_cmetricMixin.

End ICProducts.

Lemma cmetricProdICatAxiom I : @CatIProduct.axiom _ I (@prodI_cmetricType I)
    (fun P i => @mproj I P i) (fun P i => @mprodI_fun I P i).
move => P Z f. split ; first by apply (proj1 (@metricProdICatAxiom I P Z f)).
move => m X. apply (proj2 (@metricProdICatAxiom I P Z f) m X).
Qed.

Canonical Structure cmetricProdIMixin := prodICatMixin cmetricProdICatAxiom.
Canonical Structure cmetricProdICatType := Eval hnf in prodICatType cmetricProdIMixin.

Definition cchain_pair M N (c:cchain M) (c':cchain N) : cchain (M * N).
exists (fun n => (c n,c' n)).
move => n i j l l'. simpl. split ; by apply cchain_cauchy.
Defined.

Lemma pair_limit (M N:cmetricType) (c:cchain M) (c':cchain N) : umet_complete (cchain_pair c c':cchain (M * N)) =-= (umet_complete c,umet_complete c').
by split ; simpl ; apply: umet_complete_ext ; simpl ; auto.
Qed.

Definition ccomplete (M:cmetricType) (P:M -> Prop) : Prop := forall c : cchain M, (forall i, P (c i)) -> P (umet_complete c).

Lemma contractive_complete (A B:cmetricType) : ccomplete (fun f : (A =-> B) => contractive f).
simpl. move => c. simpl. move => X. move => n x y e.
destruct (cumet_conv c n.+1) as [m C]. specialize (C (m+n)%N). rewrite leq_addr in C.
specialize (C is_true_true). refine (Mrel_trans (Msym C _) _).
refine (Mrel_trans _ (C _)). clear C. specialize (X (m+n)%N). by apply X.
Qed.

Section OPT.
Variable M:metricType.

Lemma option_metric_axiom : Metric.axiom (fun n (x y : option M) => match n with O => True | S _ => match x,y with Some x, Some y => x = n = y | None, None => True | _,_ => False end end).
move => n x y z ; split ; last split ; last split ; last split ; simpl ; clear.
- split.
  + case: x ; case: y ; simpl ; 
    [idtac | by move => s X ; specialize (X 1) | by move => s X ; specialize (X 1) | by []].
    move => m m' X. unfold tset_eq. simpl. apply (proj1 (Mrefl _ _)) => n. specialize (X n). by case: n X.
  + case: x ; case: y ; [idtac | by [] | by [] | move => e ; by case].
    move => m m' e. case ; first by []. move => n. simpl. by apply (proj2 (Mrefl _ _)).
- case: x ; case: y ; [idtac | move => a X ; apply X | move => a X ; apply X | move => X ; apply X].
  move => m m' X. case:n X ; first by []. move => n X. simpl. by apply (Msym X).
- case: x ; case: y ; case: z ;
  [move => x y z | move => x y ; by case: n ; by try move => n A B
 | move => x y ; by case: n ; by try move => n A B
 | move => x ; by case: n ; by try move => n A B
 | move => x y ; by case: n ; by try move => n A B
 | move => x ; by case: n ; by try move => n A B
 | move => x ; by case: n ; by try move => n A B
 | by case: n ; last (move => n X Y) ].
  move => X Y. simpl. simpl in X. simpl in Y. case: n X Y ; first by [].
  move => n. by apply Mrel_trans.
- case: n ; first by []. move => n X. simpl. simpl in X. case: x X ; last by case: y. case: y ; last by [].
  move => x y E. by apply (Mmono E).
- by case: x ; case: y.
Qed.

Canonical Structure option_metricMixin := MetricMixin option_metric_axiom.
Canonical Structure option_metricType := Eval hnf in MetricType option_metricMixin.

Notation "'Option'" := option_metricType : M_scope.

End OPT.

Section option_cmetric.
Variable A:cmetricType.

Lemma option_cchainP (c:cchain (option_metricType A)) y (c1:c 1 = Some y) : cchainp (fun n => match c n with Some x => x | None => y end).
case.
move => i j _ _. by case (c i) ; case (c j).
move => n i j l l'. have a:exists yi, c i = Some yi.
have il:O < i. apply: (ssrnat.leq_trans _ l). by apply ltn0Sn.
have X:=cchain_cauchy c il (ltn0Sn O). rewrite c1 in X. case: (c i) X ; last by [].
move => s E. by exists s.
have b:exists yi, c j = Some yi.
have il:O < j. apply: (ssrnat.leq_trans _ l'). by apply ltn0Sn.
have X:=cchain_cauchy c il (ltn0Sn O). rewrite c1 in X. case: (c j) X ; last by [].
move => s E. by exists s.
case: a => yi a. case: b => yj b. rewrite -> a. rewrite -> b.
have X:=cchain_cauchy c l l'. rewrite a in X. rewrite b in X. by apply X.
Qed.

Definition option_cchain (c:cchain (option_metricType A)) y (c1:c 1 = Some y) := mk_cchain (option_cchainP c1).

Definition option_case T (x:option T) : (x = None) + {y | x = Some y} :=
match x as x0 return (x0 = None) + {y : T | x0 = Some y} with
| None => inl _ (refl_equal None)
| Some x => inr _ (exist _ x (refl_equal (Some x)))
end.

Definition option_lub (c: cchain (option_metricType A)) : option A :=
match (option_case (c 1)) with 
| inl e => None
| inr e' => match e' with exist y e => Some (umet_complete (option_cchain e)) end
end.

Lemma option_cmetricAxiom : CMetric.axiom option_lub.
move => c n. exists n. case: n ; first by [].
move => n i l. unfold option_lub. case_eq (option_case (c 1)).
- move => e _. have C:=cchain_cauchy c (ltn0Sn O).
  specialize (C i (leq_trans (ltn0Sn _) l)). rewrite e in C. by case: (c i) C.
- case. move => x e _. case: (cumet_conv (option_cchain e) n.+1).
  move => m C. specialize (C (i+m)%N). specialize (C (leq_addl _ _)).
  have ee:Some (option_cchain e (i + m)%N) = n.+1 = Some (umet_complete (option_cchain e)) by apply C.
  clear C. rewrite <- ee. clear ee.
  have C:=cchain_cauchy (option_cchain e) l. specialize (C (i+m)%N).
  specialize (C (ssrnat.leq_trans l (leq_addr m i))).
  have ee:Some (option_cchain e i) = n.+1 = Some (option_cchain e (i + m)%N) by apply C.
  rewrite <- ee. clear C ee. simpl. have ee:exists y, c i = Some y.
  have il:O < i. apply: (ssrnat.leq_trans _ l). by apply ltn0Sn.
  have X:=cchain_cauchy c il (ltn0Sn O). rewrite e in X. case: (c i) X ; last by [].
  move => s E. by exists s. case: ee => y ee.
  by case: (c i) ee.
Qed.

Definition option_cmetricMixin := CMetricMixin option_cmetricAxiom.
Canonical Structure option_cmetricType := Eval hnf in CMetricType option_cmetricMixin.

End option_cmetric.


Section Submetric.

Variable (M:metricType) (P:M -> Prop).

Lemma sub_metric_axiom : Metric.axiom (fun n (x y:@sub_setoidType M (fun e => P e)) =>  match x,y with exist x' _, exist y' _ => @Mrel M n x' y' end).
move => n x y z ; split ; last split ; last split ; last split ; clear.
- case: x. case: y. move => y Py x Px. split ; first by move => C ; apply (proj1 (Mrefl _ _) C).
  simpl. unfold tset_eq. simpl. by apply (proj2 (Mrefl _ _)).
- case: x. case: y. move => y Py x Px. simpl. move => C. by apply (Msym C).
- case: x. case: y. case: z. move => z Pz y Py x Px. move => C C'. simpl. by apply (Mrel_trans C C').
- case: x. case: y. move => y Py x Px. move => C. by apply (Mmono C).
- case: x. case: y. move => y Py x Px. simpl. apply: Mbound.
Qed.

Canonical Structure sub_metricMixin := Metric.Mixin sub_metric_axiom.
Canonical Structure sub_metricType := Eval hnf in MetricType sub_metricMixin.

Lemma Sforget_ne : nonexpansive (@Sforget (Metric.setoidType M) (fun x => P x)).
move => n. by case => x Px ; case.
Qed.

Definition mforget : sub_metricType =-> M := Eval hnf in mk_fmet Sforget_ne.

Lemma sInherit_ne (N : metricType) (f:N =-> M) (c:forall n, P (f n)) :
   nonexpansive (@sInheritFun (Metric.setoidType M) (fun x => P x) _ _ c).
move => n x x' e. simpl. by apply (fnonexpansive f e).
Qed.

Definition mInheritFun (N : metricType) (f:N =-> M)
   (c:forall n, P (f n)) : N =-> sub_metricType := Eval hnf in mk_fmet (sInherit_ne c).

Lemma mForget_mono (N:metricType) (f:N =-> sub_metricType) g : mforget << f =-= mforget << g -> f =-= g.
move => C. apply: Sforget_mono. apply C.
Qed.

End Submetric.

Section SubCMetric.

Variable (M:cmetricType) (P:M -> Prop) (C:@ccomplete M P).

Lemma subchainlubP (c:cchain (sub_metricType P)) : P (umet_complete (liftc (mforget P) c)).
apply (@C (liftc (mforget P) c)).
move => i. simpl. by case(c i).
Qed.

Lemma sub_cmetric_axiom : CMetric.axiom (fun (c:cchain (sub_metricType P)) => (exist (fun x => P x) (umet_complete (liftc (mforget P) c)) (subchainlubP c))).
move => c n ; simpl. destruct ((cumet_conv (liftc (mforget P) c)) n) as [m X].
exists m. move => i L. specialize (X i L). simpl in X. case_eq (c i) => x Px E.
rewrite E in X. by apply X.
Qed.

Canonical Structure sub_cmetricMixin := CMetric.Mixin sub_cmetric_axiom.
Canonical Structure sub_cmetricType := Eval hnf in CMetricType sub_cmetricMixin.

Definition MInheritFun (N : cmetricType) (f:N =-> M) : (forall n, P (f n)) -> N =-> sub_cmetricType :=
 fun c => mInheritFun c.

Definition Mforget : sub_cmetricType =-> M := mforget P.

Lemma Mforget_mono (N:cmetricType) (f:N =-> sub_cmetricType) g : Mforget << f =-= Mforget << g -> f =-= g.
apply: mForget_mono.
Qed.

End SubCMetric.

Lemma nonexp_cont2 (M N P:cmetricType) (f:M =-> N -=> P) (c:cchain M) (c':cchain N) :
    f (umet_complete c) (umet_complete c') =-= umet_complete (binaryLimit f c c').
have b:=frespect ((uncurry f)) (pair_limit c c').
have X:= nonexp_continuous (((uncurry f):(M * N =-> P))). simpl in X.
specialize (X (cchain_pair c c')). simpl in b.
have Y:=tset_trans (tset_sym b) X. clear b X. rewrite -> Y. clear Y.
by apply: umet_complete_ext.
Qed.


Section Discrete.

Variable T:Type.

Lemma mdiscrete_respect2 n : setoid_respect2 (fun x y : discrete_setoidType T => match n with O => True | S _ => x = y end).
split => x y y' e. case: n ; first by []. move => _. by split => e' ; rewrite <- e' ; rewrite e.
case: n ; first by []. move => _. by split => e' ; rewrite -> e' ; rewrite e.
Qed.

Lemma discrete_metric_axiom : Metric.axiom (fun n  (x y : discrete_setoidType T) => match n with O => True | S _ => x = y end).
move => n x y z ; split ; last split ; last split ; last split ; clear.
- split => C ; first by apply (C 1). case ; first by []. by move => n ; apply C.
- case: n ; first by []. move => n X. simpl. simpl in X. by rewrite X.
- case: n ; first by []. move => n X Y. by rewrite -> X.
- case: n ; first by []. move => n X. by apply X.
- by [].
Qed.

Definition discrete_metricMixin := MetricMixin discrete_metric_axiom.
Definition discrete_metricType := Eval hnf in @MetricType (discrete_setoidType T) discrete_metricMixin.

Lemma discrete_conv (c:cchain discrete_metricType) : mconverge c (c 1).
exists 1. case ; first by []. move => i _.
have A:=cchain_cauchy c. specialize (A 1 i.+1 1 (ltn0Sn _) (ltnSn _)).
case: n ; first by []. move => n. by apply A.
Qed.

Definition discrete_cmetricMixin := CMetricMixin discrete_conv.
Definition discrete_cmetricType := Eval hnf in @CMetricType discrete_metricType discrete_cmetricMixin.

End Discrete.

