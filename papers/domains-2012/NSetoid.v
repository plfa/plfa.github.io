(**********************************************************************************
 * NSetoid.v                                                                      *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                       *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)

Require Export Categories.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** printing >-> %\ensuremath{>}\ensuremath{-}\ensuremath{>}% *)
(** printing :> %\ensuremath{:>}% *)
(** printing Canonical %\coqdockw{Canonical}% *)

Open Scope S_scope.

Definition setoid_respect (T T':setoidType) (f: T -> T') :=
    forall x y, x =-= y -> (f x) =-= (f y).

Module FSet.

Section fset.
Variable O1 O2 : setoidType.

Record mixin_of (f:O1 -> O2) := Mixin { ext :> setoid_respect f}.

Notation class_of := mixin_of (only parsing).

Section ClassDef.
Structure type : Type := Pack {sort : O1 -> O2; _ : class_of sort; _ : O1 -> O2}.
Local Coercion sort : type >-> Funclass.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
  let: Pack T c _ := cT return K _ (class cT) in k _ c.
Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT.
Definition pack f (c:class_of f) := @Pack f c f.
End ClassDef.
End fset.
Module Import Exports.
Coercion sort : type >-> Funclass.
Notation fset := type.
Notation fsetMixin := Mixin.
Notation fsetType := pack.
End Exports.
End FSet.
Export FSet.Exports.

Lemma frespect (S S':setoidType) (f:fset S S') : setoid_respect f.
case:f => f. case. move => a s. by apply a.
Qed.

Hint Resolve frespect.

Lemma fset_setoidAxiom (T T' : setoidType) : Setoid.axiom (fun (f g:fset T T') => forall x:T, (f x) =-= (g x)).
split ; last split.
- by move => f.
- move => f g h. simpl. move => X Y e. by apply (tset_trans (X e) (Y e)).
- move => f g. simpl. move => X e. by apply (tset_sym (X e)).
Qed.

Canonical Structure fset_setoidMixin (T T':setoidType) := Setoid.Mixin (fset_setoidAxiom T T').
Canonical Structure fset_setoidType T T' := Eval hnf in SetoidType (fset_setoidMixin T T').

Definition setmorph_equal (A B: setoidType) : relation (fset A B) :=
(@tset_eq (@fset_setoidType A B)).

Definition setmorph_equal_equivalence (A B: setoidType): Equivalence
(@setmorph_equal A B).
split.
- move => x. by apply: tset_refl.
- move => x y. by apply: tset_sym.
- move => x y z. by apply: tset_trans.
Defined.

Existing Instance setmorph_equal_equivalence.

Add Parametric Morphism (A B : setoidType) :
  (@FSet.sort A B) with signature (@setmorph_equal A B ==> @tset_eq A ==>
  @tset_eq B)
   as setmorph_eq_compat.
   intros f g fg x y xy. apply tset_trans with (g x) ; first by auto.
   by apply frespect.
   Qed.

Definition mk_fsetM (O1 O2:setoidType) (f:O1 -> O2) (m:setoid_respect f) := fsetMixin m.
Definition mk_fset (O1 O2:setoidType) (f:O1 -> O2) (m:setoid_respect f) : fset O1 O2 := 
   Eval hnf in fsetType (mk_fsetM m).

Lemma ScompP S S' S'' (f:fset S' S'') (g:fset S S') : setoid_respect (T:=S) (T':=S'') (fun x : S => f (g x)).
move => x y e. have a:=frespect g e. by apply (frespect f a).
Qed.

Definition Scomp S S' S'' (f:fset S' S'') (g:fset S S') : fset S S'' :=
   Eval hnf in  mk_fset (ScompP f g).

Lemma SidP (S:setoidType) : setoid_respect (id : S -> S).
move => x y X. by apply X.
Qed.

Definition Sid S : (fset S S) := Eval hnf in mk_fset (@SidP S).

Lemma setoidCatAxiom : Category.axiom Scomp Sid.
split ; last split ; last split.
- by move => S S' x.
- by move => S S' x.
- by move => S0 S1 S2 S3 f g h x.
- move => S0 S1 S2 f f' g g' e e' x. apply tset_trans with (y:= f (g' x)).
  + apply: (frespect f). by apply e'.
  + by apply e.
Qed.

Canonical Structure setoidCatMixin := CatMixin setoidCatAxiom.
Canonical Structure setoidCat := Eval hnf in CatType setoidCatMixin.

Open Scope C_scope.

Lemma PropP : Setoid.axiom (fun f g : Prop => iff f g).
split ; last split.
- by move => x.
- move => x y z. simpl. move => [X Y] [Z W]. by split ; auto.
- move => x y. simpl. move => [X Y]. by split.
Qed.

Canonical Structure prop_setoidMixin := Setoid.Mixin PropP.
Canonical Structure prop_setoidType := Eval hnf in SetoidType prop_setoidMixin.

Notation Props := prop_setoidType.

Section SetoidProducts.
Variable A B:setoidType.

Lemma sum_setoidAxiom : Setoid.axiom (fun p0 p1 : A + B => match p0,p1 with inl a, inl b => a =-= b | inr a, inr b => a =-= b | _,_ => False end).
split ; last split.
- by case.
- case => a ; case => b ; case => c ; try done ; by apply tset_trans.
- case => a ; case => b ; try done ; by apply tset_sym.
Qed.

Canonical Structure sum_setoidMixin := Setoid.Mixin sum_setoidAxiom.
Canonical Structure sum_setoidType := Eval hnf in SetoidType sum_setoidMixin.

Lemma prod_setoidAxiom : Setoid.axiom (fun p0 p1 : A * B => tset_eq (fst p0) (fst p1) /\ tset_eq (snd p0) (snd p1)).
split ; last split.
- case => a b ; by split.
- case => a b ; case => c d ; case => e f ; simpl ; move => [X Y] [Z W]. 
  by split ; [apply (tset_trans X Z) | apply (tset_trans Y W)].
- by case => a b ; case => c d ; simpl ; move => [X Y] ; split ; auto.
Qed.

Canonical Structure prod_setoidMixin := Setoid.Mixin prod_setoidAxiom.
Canonical Structure prod_setoidType := Eval hnf in SetoidType prod_setoidMixin.

Lemma Sfst_respect : setoid_respect (T:=prod_setoidType) (T':=A) (@fst _ _).
case => a b ; case => c d ; simpl ; unlock tset_eq ; move => [X Y] ; by unlock tset_eq in X ; apply X.
Qed.

Lemma Ssnd_respect : setoid_respect (T:=prod_setoidType) (T':=B) (@snd _ _).
case => a b ; case => c d ; simpl ; unlock tset_eq ; move => [X Y] ; by unlock tset_eq in Y ; apply Y.
Qed.

Definition Sfst : prod_setoidType =-> A := Eval hnf in mk_fset Sfst_respect.

Definition Ssnd : prod_setoidType =-> B := Eval hnf in mk_fset Ssnd_respect.

Lemma prod_fun_respect C (f:C =-> A) (g:C =-> B) : setoid_respect (T:=C) (T':=prod_setoidType) (fun c : C => (f c, g c)).
move => c c' e. simpl. unlock tset_eq. by split ; [apply (frespect f e) | apply (frespect g e)].
Qed.

Definition Sprod_fun C (f:C =-> A) (g:C =-> B) : C =-> prod_setoidType := Eval hnf in mk_fset (prod_fun_respect f g).

Lemma Sin1_respect : @setoid_respect A (sum_setoidType) (@inl _ _).
move => a a' e. by apply e.
Qed.

Lemma Sin2_respect : @setoid_respect B (sum_setoidType) (@inr _ _).
move => a a' e. by apply e.
Qed.

Definition Sin1 : A =-> sum_setoidType := Eval hnf in mk_fset Sin1_respect.
Definition Sin2 : B =-> sum_setoidType := Eval hnf in mk_fset Sin2_respect.

Lemma Ssum_fun_respect C (f:A =-> C) (g:B =-> C) : @setoid_respect sum_setoidType C (fun x => match x with inl x => f x | inr x => g x end).
case => x ; case => y => e ; try done ; by apply frespect ; apply e.
Qed.

Definition Ssum_fun C (f:A =-> C) (g:B =-> C) : sum_setoidType =-> C := Eval hnf in mk_fset (Ssum_fun_respect f g).


(*

Lemma Sprod_fun_unique C (f:C -s> A) (g:C -s> B) (h:C -s> prod_setoidType) :
  Scomp Sfst h =-= f -> Scomp Ssnd h =-= g -> h =-= Sprod_fun f g.
move => C f g h. unlock tset_eq. move => X Y x. specialize (X x). specialize (Y x). unlock tset_eq. by split ; auto.
Qed.

Lemma Sprod_fun_fst C f g : Sfst << (@Sprod_fun C f g) =-= f.
move => C f g. unlock tset_eq. by simpl.
Qed.

Lemma Sprod_fun_snd C f g : Ssnd << (@Sprod_fun C f g) =-= g.
move => C f g. unlock tset_eq. by simpl.
Qed.*)

End SetoidProducts.

Lemma setoidProdCatAxiom : @CatProduct.axiom _ prod_setoidType Sfst Ssnd Sprod_fun.
move => S0 S1 S2 f g. split ; [by split | move => m].
move => [X Y] x. simpl. specialize (X x). by specialize (Y x).
Qed.

Canonical Structure setoidProdCatMixin := prodCatMixin setoidProdCatAxiom.
Canonical Structure setoidProdCat := Eval hnf in prodCatType (CatProduct.Class setoidProdCatMixin).

Lemma setoidSumCatAxiom : @CatSum.axiom _ sum_setoidType Sin1 Sin2 Ssum_fun.
move => S0 S1 S2 f g. split ; first by split.
move => h [X Y]. by case => x ; simpl ; [apply: X | apply: Y].
Qed.

Canonical Structure setoidSumCatMixin := sumCatMixin setoidSumCatAxiom.
Canonical Structure setoidSumCat := Eval hnf in sumCatType setoidSumCatMixin.

Section SetoidIProducts.

Variable I : Type.
Variable P : I -> setoidType.

Lemma prodI_setoidP : Setoid.axiom (fun (p0 p1:forall i, P i) => forall i:I, @tset_eq _ (p0 i) (p1 i)).
split ; last split.
- move => X ; simpl ; by [].
- move => X Y Z ; simpl ; move => R S i. by apply (tset_trans (R i) (S i)).
- move => X Y ; simpl ; move => R i. by apply (tset_sym (R i)).
Qed.

Canonical Structure prodI_setoidMixin := Setoid.Mixin prodI_setoidP.
Canonical Structure prodI_setoidType := Eval hnf in SetoidType prodI_setoidMixin.

Lemma Sproj_respect i : setoid_respect (T:=prodI_setoidType) (T':=P i)
     (fun X : prodI_setoidType => X i).
move => a b e. simpl. unlock tset_eq in e. by apply (e i).
Qed.

Definition Sproj i : prodI_setoidType =-> P i := Eval hnf in mk_fset (Sproj_respect i).

Lemma SprodI_fun_respect C (f:forall i, C =-> P i) : setoid_respect (T:=C) (T':=prodI_setoidType) (fun (c : C) (i : I) => f i c).
move => c c' e. simpl. unlock tset_eq. by move => i ; apply (frespect (f i) e).
Qed.

Definition SprodI_fun C (f:forall i, C =-> P i) : C =-> prodI_setoidType := Eval hnf in mk_fset (SprodI_fun_respect f).

Lemma SprodI_fun_proj C (f:forall i, C =-> P i) i : Scomp (Sproj i) (SprodI_fun f) =-= f i.
by unlock tset_eq ; simpl.
Qed.

Lemma SprodI_fun_unique C (f:forall i, C =-> P i) (h:C =-> prodI_setoidType) : (forall i, Scomp (Sproj i) h =-= f i) -> h =-= SprodI_fun f.
move => X. unlock tset_eq. move => x. unlock tset_eq. move => i. unlock tset_eq in X. apply (X i x).
Qed.

End SetoidIProducts.

Add Parametric Morphism A B : (@pair A B)
with signature (@tset_eq A) ==> (@tset_eq B) ==> (@tset_eq (A * B))
as pair_eq_compat.
by move => x y e x' y' e'.
Qed.

Lemma spair_respect (A B : setoidType) (x:A) : setoid_respect (fun y:B => (x,y)).
move => y y' e. by split.
Qed.

Definition spair (A B : setoidType) (x:A) : B =-> A * B := Eval hnf in mk_fset (spair_respect x).

Lemma scurry_respect (A B C : setoidType) (f:A * B =-> C) : setoid_respect (fun x => f << spair _ x).
move => x x' e y. simpl. by rewrite -> e.
Qed.

Definition scurry (A B C : setoidType) (f:A * B =-> C) : A =-> (fset_setoidType B C) := Eval hnf in mk_fset (scurry_respect f).

Definition setoid_respect2 (S S' S'' : setoidType) (f:S -> S' -> S'') := 
  (forall s', setoid_respect (fun x => f x s')) /\ forall s, setoid_respect (f s).

Lemma setoid2_morphP (S S' S'' : setoidType) (f:S -> S' -> S'') (C:setoid_respect2 f) :
   setoid_respect (T:=S) (T':=S' =-> S'')
     (fun x : S => FSet.Pack (FSet.Mixin (proj2 C x)) (f x)).
move => x y E. unfold tset_eq. simpl. move => s'. apply (proj1 C s' _ _ E).
Qed.

Definition setoid2_morph (S S' S'' : setoidType) (f:S -> S' -> S'') (C:setoid_respect2 f) :
    S =-> (fset_setoidType S' S'') := Eval hnf in mk_fset (setoid2_morphP C).

Definition Sprod_map (A B C D:setoidType) (f:A =-> C) (g:B =-> D) := <| f << pi1, g << pi2 |>.

Lemma ev_respect B A : setoid_respect (fun (p:(fset_setoidType B A) * B) => fst p (snd p)).
case => f b. case => f' b'. simpl.
case ; simpl. move => e e'. rewrite -> e. by rewrite -> e'.
Qed.

Definition Sev B A : (fset_setoidType B A) * B =-> A := Eval hnf in mk_fset (@ev_respect B A).

Implicit Arguments Sev [A B].

Lemma setoidExpAxiom : @CatExp.axiom _ fset_setoidType (@Sev) (@scurry).
move => X Y Z h. split ; first by case.
move => h' A x y. specialize (A (x,y)). by apply A.
Qed.

Canonical Structure setoidExpMixin := expCatMixin setoidExpAxiom.
Canonical Structure setoidExpCat := Eval hnf in expCatType setoidExpMixin.

Lemma const_respect (M M':setoidType) (x:M') : setoid_respect (fun _ : M => x).
by [].
Qed.

Definition sconst (M M':setoidType) (x:M') : M =-> M' := Eval hnf in mk_fset (const_respect x).

Lemma unit_setoidP : Setoid.axiom (fun _ _ : unit => True).
by [].
Qed.

Canonical Structure unit_setoidMixin := Setoid.Mixin unit_setoidP.
Canonical Structure unit_setoidType := Eval hnf in SetoidType unit_setoidMixin.

Lemma setoidTerminalAxiom : CatTerminal.axiom unit_setoidType.
move => C h h' x. case (h x). by case (h' x).
Qed.

Canonical Structure setoidTerminalMixin := terminalCatMixin (fun T => sconst T tt) setoidTerminalAxiom.
Canonical Structure setoidTerminalCat := Eval hnf in terminalCatType (CatTerminal.Class setoidTerminalMixin).

Lemma emp_setoid_axiom : Setoid.axiom (fun x y : Empty => True).
split ; last split ; by move => x.
Qed.

Canonical Structure emp_setoidMixin := SetoidMixin emp_setoid_axiom.
Canonical Structure emp_setoidType := Eval hnf in SetoidType emp_setoidMixin.

Lemma setoidInitialAxiom : CatInitial.axiom emp_setoidType.
move => C h h'. by case.
Qed.

Lemma SZero_initial_unique D (f g : emp_setoidType =-> D) : f =-= g.
by move => x.
Qed.

Lemma SZero_respect (D:setoidType) : setoid_respect (fun (x:Empty) => match x with end : D).
by [].
Qed.

Definition SZero_initial D : emp_setoidType =-> D := Eval hnf in mk_fset (SZero_respect D).

Canonical Structure setoidInitialMixin := initialCatMixin SZero_initial setoidInitialAxiom.
Canonical Structure setoidInitialCat := Eval hnf in initialCatType (CatInitial.Class setoidInitialMixin).

Section Subsetoid.
Variable (S:setoidType) (P:S -> Prop).

Lemma sub_setoidP : Setoid.axiom (fun (x y:{e : S | P e}) => match x,y with exist x' _, exist y' _ => x' =-= y' end).
split ; last split.
- by case => x Px.
- case => x Px. case => y Py. case => z Pz. by apply tset_trans.
- case => x Px. case => y Py. apply tset_sym.
Qed.

Canonical Structure sub_setoidMixin := Setoid.Mixin sub_setoidP.
Canonical Structure sub_setoidType := Eval hnf in SetoidType sub_setoidMixin.

Lemma forget_respect : setoid_respect (fun (x:sub_setoidType) => match x with exist x' _ => x' end).
by case => x Px ; case => y Py.
Qed.

Definition Sforget : sub_setoidType =-> S := Eval hnf in mk_fset forget_respect.

Lemma InheretFun_respect (N : setoidType) (f:N =-> S) (c:(forall n, P (f n))) : setoid_respect (fun n => exist (fun x => P x) (f n) (c n)).
move => n n' e. simpl. by apply (frespect f e).
Qed.

Definition sInheritFun (N : setoidType) (f:N =-> S) (c:forall n, P (f n)) : 
  N =-> sub_setoidType := Eval hnf in mk_fset (InheretFun_respect c).

Lemma Sforget_mono M (f:M =-> sub_setoidType) g : Sforget << f =-= Sforget << g -> f =-= g.
move => C x. specialize (C x). case_eq (f x). move => fx Pf. case_eq (g x). move => gx Pg.
move => e e'. have ee:(Sforget (f x) =-= Sforget (g x)) by []. rewrite e in ee. rewrite e' in ee. simpl in ee.
apply ee.
Qed.

End Subsetoid.

Section Option.

Variable S:setoidType.

Lemma option_setoid_axiom :
  Setoid.axiom (fun x y : option S => match x,y with None,None => True | Some x, Some y => x =-= y | _,_ => False end).
split ; last split.
- by case.
- case ; first (move => x ; case ; [move => y ; case ; by [move => z ; apply tset_trans | by []] | by []]).
  case ; first by []. by case.
- case ; [move => x ; case ; [move => y ; apply tset_sym | by []] | by case].
Qed.

Canonical Structure option_setoidMixin := SetoidMixin option_setoid_axiom.
Canonical Structure option_setoidType := Eval hnf in SetoidType option_setoidMixin.

End Option.

Arguments Scope fset_setoidType [S_scope S_scope].

Notation "'Option'" := option_setoidType : S_scope.

Lemma some_respect (S:setoidType) : setoid_respect (@Some S).
by [].
Qed.

Definition Ssome (S:setoidType) : S =-> Option S := Eval hnf in mk_fset (@some_respect S).

Lemma sbind_respect (S S':setoidType) (f:S =-> Option S') : setoid_respect (fun x => match x with None => None | Some x => f x end).
case ; last by case.
move => x. case ; last by []. move => y e. apply (frespect f). by apply e.
Qed.

Definition Soptionbind (S S':setoidType) (f:S =-> Option S') : Option S =-> Option S' :=
  Eval hnf in mk_fset (sbind_respect f).

Lemma discrete_setoidAxiom (T:Type) : Setoid.axiom (fun x y : T => x = y).
split ; first by [].
split ; first by apply: trans_equal.
by apply:sym_equal.
Qed.

Definition discrete_setoidMixin T := SetoidMixin (discrete_setoidAxiom T).
Definition discrete_setoidType T := Eval hnf in SetoidType (discrete_setoidMixin T).

Lemma setAxiom T : @Setoid.axiom (T -> Prop) (fun X Y => forall x, X x <-> Y x).
split ; last split.
- move => a. simpl. by [].
- move => a. simpl. move => y z A B x. rewrite <- B. by  rewrite <- A.
- move => a. simpl. move => b A x. by rewrite A.
Qed.

Canonical Structure setMixin T := SetoidMixin (setAxiom T).
Canonical Structure setType T := Eval hnf in  SetoidType (setMixin T).

Close Scope S_scope.
Close Scope C_scope.

