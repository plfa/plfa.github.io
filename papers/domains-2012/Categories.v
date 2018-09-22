(**********************************************************************************
 * Categories.v                                                                   *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                      *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)

Require Export ssreflect Coq.Setoids.Setoid.

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

Inductive Empty : Set := .

(*=Setoid *)
Module Setoid.
  Definition axiom (T:Type) (e:T -> T -> Prop) := equiv _ e.
  Record mixin_of T := Mixin
  { set_eq : T -> T -> Prop; set_equiv : axiom set_eq }.
  Notation class_of := mixin_of (only parsing).

  Section ClassDef.
  Structure type := Pack {sort; _:class_of sort; _:Type}.
  Local Coercion sort : type >-> Sortclass.
  Definition class cT := let: Pack _ c _ := cT return class_of cT in c. 
  Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
    let: Pack T c _ := cT return K _ (class cT) in k _ c. (*CLEAR*)
  Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT. (*CLEARED*)
  Definition pack T c := @Pack T c T.
  End ClassDef.

  Module Import Exports.
  Coercion sort : type >-> Sortclass.
  Notation setoidType := type.
  Notation SetoidMixin := Mixin.
  Notation SetoidType := pack.
  End Exports.

End Setoid.
Export Setoid.Exports.

Definition tset_eq := fun T => Setoid.set_eq (Setoid.class T). (*CLEAR*)

Bind Scope S_scope with Setoid.sort.
Delimit Scope S_scope with SET.
Open Scope S_scope.

(** printing =-= %\ensuremath{\equiv}% *)
(*CLEARED*)
Infix "=-=" := tset_eq (at level 70). (*CLEAR*)

Arguments Scope tset_eq [S_scope _ _].
(*CLEARED*)
Lemma tset_refl (T:setoidType) (x:T) : x =-= x. (*CLEAR*)
unlock tset_eq. apply (proj1 (Setoid.set_equiv (Setoid.class T)) x).
Qed.

Arguments Scope tset_refl [S_scope _].
Hint Resolve tset_refl.
(*CLEARED*)
Lemma tset_trans (T:setoidType) (x y z:T) : x =-= y -> y =-= z -> x =-= z. (*CLEAR*)
unlock tset_eq. apply (proj1 (proj2 (Setoid.set_equiv (Setoid.class T))) x y z).
Qed.

Arguments Scope tset_trans [S_scope _ _ _].

Hint Immediate tset_trans. (*CLEARED*)
Lemma tset_sym (T:setoidType) (x y:T) : x =-= y -> y =-= x. (*CLEAR*)
unlock tset_eq. apply (proj2 (proj2 (Setoid.set_equiv (Setoid.class T))) x y).
Qed.

Arguments Scope tset_sym [S_scope _ _].

Hint Immediate tset_sym. (*CLEARED*)
Add Parametric Relation (T:setoidType) : T (@tset_eq T)
 reflexivity proved by (@tset_refl T) symmetry proved by (@tset_sym T)
 transitivity proved by (@tset_trans T) as tset_eqrel.
(*=End *)

(*=Category *)
Module Category.
  Section Axioms.
    Variable Ob:Type.
    Variable Morph : Ob -> Ob -> setoidType.
    Variable tcomp : forall T0 T1 T2, Morph T1 T2 -> Morph T0 T1 -> Morph T0 T2.
    Variable tid : forall T0, Morph T0 T0.
    Definition tid_left := forall T0 T1 (f:Morph T0 T1), tcomp (tid T1) f =-= f.
    Definition tid_right := forall T0 T1 (f:Morph T0 T1), tcomp f (tid T0) =-= f.
    Definition tcomp_assoc := forall T0 T1 T2 T3 (f:Morph T2 T3) (g:Morph T1 T2)
              (h:Morph T0 T1), (tcomp f (tcomp g h)) =-= (tcomp (tcomp f g) h).
    Definition tcomp_respect := forall T0 T1 T2 (f f' : Morph T1 T2) 
          (g g' : Morph T0 T1), f =-= f' -> g =-= g' -> tcomp f g =-= tcomp f' g'.
  End Axioms.
  Definition axiom O M c i := 
    @tid_left O M c i /\ tid_right c i /\ tcomp_assoc c /\ tcomp_respect c.
  Record mixin_of T (Morph : T -> T -> setoidType) := Mixin
  { tcomp : forall T0 T1 T2, Morph T1 T2 -> Morph T0 T1 -> Morph T0 T2;
    tid : forall T0, Morph T0 T0;
    tcategory : axiom tcomp tid }.
  Notation class_of := mixin_of.
  Section ClassDef.
  Structure cat := Pack {object;
    morph : object -> object -> setoidType ; _:class_of morph; _:Type}.
  Local Coercion object : cat >-> Sortclass.
  Local Coercion morph : cat >-> Funclass.
  Definition class cT := let: Pack _ _ c _ := cT return class_of cT in c. 
  Definition unpack (K:forall O (M:O -> O -> setoidType) (c:class_of M), Type)
    (k : forall O (M: O -> O -> setoidType) (c:class_of M), K _ _ c) (cT:cat) :=
    let: Pack _ M c _ := cT return @K _ _ (class cT) in k _ _ c. (*CLEAR*)
  Definition repack cT : _ -> Type -> cat := 
                                  let k T M c p := p c in unpack k cT.
  (*CLEARED*)
  Definition pack T M c := @Pack T M c T.
  Definition comp (cT:cat) : forall (A B C:cT),
                morph B C -> morph A B -> morph A C := tcomp (class cT).
  Definition id (cT:cat) : forall (A:cT), morph A A := tid (class cT). (*CLEAR*)
  Implicit Arguments id [cT A].
  (*CLEARED*)
  End ClassDef.
  
  Module Import Exports.
  Coercion object : cat >-> Sortclass.
  Coercion morph : cat >-> Funclass.
  Notation catType := cat. (*CLEAR*)
  Notation CatMixin := Mixin.
  Notation CatType := pack.
  Implicit Arguments id [cT A].
  Notation morph := Category.morph.
  Notation object := Category.object.
  End Exports.
(*CLEARED*)  

End Category.
Export Category.Exports. (*CLEAR*)
Bind Scope C_scope with Category.object.
Delimit Scope C_scope with CAT.
Open Scope C_scope.
(*CLEARED*)
Infix "=->" := Category.morph (at level 55, right associativity) (*CLEAR*) : C_scope.

Arguments Scope Category.morph [_ C_scope C_scope].
(*CLEARED*)
Infix "<<" := Category.comp (at level 35) (*CLEAR*) : C_scope.

Arguments Scope Category.comp [_ C_scope C_scope C_scope S_scope S_scope].
(*CLEARED*)
Notation Id := Category.id. (*CLEAR*)
Lemma comp_respect (C:catType) (X Y Z : C) (f f' : Y =-> X) (g g' : Z =-> Y) 
        : f =-= f' -> g =-= g' -> f << g =-= f' << g'. 
Proof.
unfold Category.comp.
case: (Category.class C). move => c i. case => Il. case => ir. case => A R.
simpl. by apply R.
Qed.
(*CLEARED*)
Add Parametric Morphism (C:catType) X Y Z : (@Category.comp C X Y Z)
  with signature (@tset_eq (C Y Z)) ==> (@tset_eq (C X Y)) ==> (@tset_eq (C X Z))
  as comp_eq_compat. (*CLEAR*)
move => x y e f g e'.
by apply: comp_respect.
Qed.
(*CLEARED*)
Lemma comp_assoc (C:catType) (W X Y Z : C) (f:W =-> X) (g : X =-> Y) 
    (h : Y =-> Z) :  h << (g << f) =-= h << g << f. (*CLEAR*)
unfold Category.comp.
case: (Category.class C). by move => c i [AA [BB A]] ; apply A.
Qed.
(*CLEARED*)
Lemma comp_idR (C:catType) (X Y : C) (f : X =-> Y) : f << Id =-= f. (*CLEAR*)
unfold Category.comp, Category.id.
case: (Category.class C). by move => c i [AA [BB A]] ; apply BB.
Qed.

Lemma comp_idL (C:catType) (X Y : C) (f : X =-> Y) : Id << f =-= f. 
unfold Category.comp, Category.id.
case: (Category.class C). simpl. by move => c i [AA [BB A]] ; apply AA.
Qed.
(*CLEARED*)
(*=End *)

Definition iso (C:catType) X Y (f:C X Y) (f':C Y X) : Prop := f << f' =-= Id /\ f' << f =-= Id.

Module CatTerminal.

Definition axiom (C:catType) (T:C) := forall T' (m m' : T' =-> T), m =-= m'.

Record mixin_of (C:catType) : Type := Mixin
{ 
  tto : C;
  tto_exists : forall C', morph C' tto;
  tto_unique : axiom tto
}.

Section ClassDef.
Record class_of (T:Type) (M:T -> T -> setoidType) : Type :=
  Class { base : Category.class_of M ; terminal : mixin_of (CatType base) }.

Local Coercion base : class_of >-> Category.class_of.
Local Coercion terminal : class_of >-> mixin_of.

Structure cat : Type := Pack {object; morph : object -> object -> setoidType ; _ : class_of morph; _ : Type}.
Local Coercion object : cat >-> Sortclass.
Local Coercion morph : cat >-> Funclass.
Definition class cT := let: Pack _ _ c _ := cT return class_of cT in c.
Definition unpack (K:forall O (M:O -> O -> setoidType) (c:class_of M), Type)
            (k : forall O (M: O -> O -> setoidType) (c : class_of M), K _ _ c) (cT:cat) :=
  let: Pack _ M c _ := cT return @K _ _ (class cT) in k _ _ c.
Definition repack cT : _ -> Type -> cat := let k T M c p := p c in unpack k cT.
Definition pack := let k T M c m := Pack (@Class T M c m) T in Category.unpack k.
Definition catType cT := Category.pack (class cT).

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Category.class_of.
Coercion terminal : class_of >-> mixin_of.
Coercion catType : cat >-> Category.cat.

Canonical Structure catType.
Notation terminalCat := cat.
Notation terminalCatMixin := Mixin.
Notation terminalCatType := pack.
End Exports.

End CatTerminal.
Export CatTerminal.Exports.

Definition terminal (C:terminalCat) : C := CatTerminal.tto (CatTerminal.class C).
Implicit Arguments terminal [C].

Notation "'One'" := terminal : C_scope.

Definition terminal_morph (C:terminalCat) (X:C) : X =-> One := CatTerminal.tto_exists (CatTerminal.class C) X.

Lemma terminal_unique (C:terminalCat) (X : C) (m m' : X =-> One) : m =-= m'.
move: m m'. unfold terminal. case: (CatTerminal.class C). simpl. move => B [T mm A]. simpl.
move => m m'. by apply A.
Qed.

Module CatInitial.

Definition axiom (C:catType) (T:C) := forall T' (m m' : morph T T'), m =-= m'.

Record mixin_of (C:catType) : Type := Mixin
{ 
  init : C;
  init_exists : forall C', morph init C';
  init_unique : axiom init
}.

Section ClassDef.
Record class_of (T:Type) (M:T -> T -> setoidType) : Type :=
  Class { base : Category.class_of M ; initial : mixin_of (CatType base) }.
Local Coercion base : class_of >-> Category.class_of.
Local Coercion initial : class_of >-> mixin_of.

Structure cat : Type := Pack {object : Type; morph : object -> object -> setoidType ; _ : class_of morph; _ : Type}.
Local Coercion object : cat >-> Sortclass.
Local Coercion morph : cat >-> Funclass.
Definition class cT := let: Pack _ _ c _ := cT return class_of cT in c.
Definition unpack (K:forall O (M:O -> O -> setoidType) (c:class_of M), Type)
            (k : forall O (M: O -> O -> setoidType) (c : class_of M), K _ _ c) (cT:cat) :=
  let: Pack _ M c _ := cT return @K _ _ (class cT) in k _ _ c.
Definition repack cT : _ -> Type -> cat := let k T M c p := p c in unpack k cT.
Definition pack := let k T M c m := Pack (@Class T M c m) T in Category.unpack k.
Definition catType cT := Category.pack (class cT).
End ClassDef.
Module Import Exports.
Canonical Structure catType.
Coercion base : class_of >-> Category.class_of.
Coercion initial : class_of >-> mixin_of.
Coercion object : cat >-> Sortclass.
Coercion morph : cat >-> Funclass.

Notation initialCat := CatInitial.cat.
Notation initialCatMixin := CatInitial.Mixin.
Notation initialCatType := CatInitial.pack.

End Exports.

End CatInitial.

Export CatInitial.Exports.

Definition initial (C:initialCat) : C := CatInitial.init (CatInitial.class C).
Implicit Arguments initial [C].

Notation "'Zero'" := initial : C_scope.

Definition initial_morph (C:initialCat) X : Zero =-> X := CatInitial.init_exists (CatInitial.class C) X.

Lemma initial_unique (C:initialCat) X (m m': C Zero X): m =-= m'.
by apply (CatInitial.init_unique m m').
Qed.


(*=Products *)
Module CatProduct.
  Definition prod_diagram (C : catType) (A B P : C) (pi1 : C P A) (pi2 : C P B) 
                              (X : C) (f : C X A) (g : C X B) (h : C X P) :=
                          pi1 << h =-= f /\ pi2 << h =-= g.
  Definition axiom (C:catType) (prod : C -> C -> C) (pi1 : forall A B, C (prod A B) A)
     (pi2 : forall A B, C (prod A B) B) (h: forall A B Z, C Z A -> C Z B -> C Z (prod A B)) :=
    forall A B X f g,
        @prod_diagram C A B (prod A B) (pi1 _ _) (pi2 _ _) X f g (h A B X f g) /\
          forall m, prod_diagram (pi1 _ _) (pi2 _ _) f g m -> m =-= (h A B X f g).
  Record mixin_of (C:catType) := Mixin
  { prod : C -> C -> C;
    pi1 : forall A B, C (prod A B) A;
    pi2 : forall A B, C (prod A B) B;
    prod_ex : forall A B Z, C Z A -> C Z B -> C Z (prod A B); _ : axiom pi1 pi2 prod_ex}.

  Section ClassDef.

  Record class_of T (M:T -> T -> setoidType) : Type :=
    Class { base : Category.class_of M ; ext : mixin_of (Category.Pack base T)}.
  Local Coercion base : class_of >-> Category.class_of.
  Local Coercion ext : class_of >-> mixin_of.

  Structure cat := Pack {object; 
         morph : object -> object -> setoidType ; _ : class_of morph; _ : Type}.
  Local Coercion object : cat >-> Sortclass.
  Local Coercion morph : cat >-> Funclass.

  Definition class cT := let: Pack _ _ c _ := cT return class_of cT in c. (*CLEAR*)
  Definition unpack (K:forall O (M:O -> O -> setoidType) (c:class_of M), Type)
              (k : forall O (M: O -> O -> setoidType) (c : class_of M), K _ _ c) (cT:cat) :=
    let: Pack _ M c _ := cT return @K _ _ (class cT) in k _ _ c.
  Definition repack cT : _ -> Type -> cat := let k T M c p := p c in unpack k cT.
(*CLEARED*)
  Definition pack := let k T M c m := Pack (@Class T M c m) T in Category.unpack k.
  Definition catType (cT:cat) := Category.pack (class cT).
  End ClassDef.
  Module Import Exports.
  Coercion catType : cat >-> Category.cat.
  Coercion base : class_of >-> Category.class_of.
  Coercion ext : class_of >-> mixin_of.
  Coercion object : cat >-> Sortclass.
  Coercion morph : cat >-> Funclass.
  Notation prodCat := cat. (*CLEAR*)
  Notation prodCatMixin := Mixin.
  Notation prodCatType := pack.
Canonical Structure catType.
  End Exports.
End CatProduct.
Export CatProduct.Exports.

(*CLEARED*)
Definition prod (C:prodCat) (A B:C) : C :=
                   (CatProduct.prod (CatProduct.class C) A B).
Definition pi1 (C:prodCat) (A B:C) : morph (prod A B) A :=
                   (CatProduct.pi1 (CatProduct.class C) A B).
Definition pi2 (C:prodCat) (A B:C) : morph (prod A B) B :=
                   (CatProduct.pi2 (CatProduct.class C) A B).
Definition prod_fun (C:prodCat) (Z A B:C) (f:C Z A) (g:C Z B) :
  morph Z (prod A B) := (CatProduct.prod_ex (CatProduct.class C) f g).
Infix "*" := prod (*CLEAR*) : C_scope.
Implicit Arguments pi1 [C A B].
Implicit Arguments pi2 [C A B]. (*CLEARED*)
Notation "'<|' f , g '|>'" := (prod_fun f g) (at level 30) (*CLEAR*) : C_scope. (*CLEARED*)
Notation "f '><' g" := (prod_fun (f << pi1) (g << pi2)) (at level 30) (*CLEAR*) : C_scope.
(* Notation "'(|' f , g '|)'" := (prod_fun (f << pi1) (g << pi2)) (at level 30) : C_scope.*)

Arguments Scope prod_fun [_ C_scope C_scope C_scope S_scope S_scope].
(*CLEARED*)
Lemma prod_fun_fst (C:prodCat) (X Y Z:C) (f:Z =-> Y) (g:Z =-> X) :
                                                pi1 << <|f , g|> =-= f. (*CLEAR*)
move: C X Y Z f g.
unfold prod_fun. case. simpl. move => OO MM. case. simpl. move => B. case. simpl. move => P pia pib pie A XX X Y Z f g. 
by apply (proj1 (A Y X Z f g)).
Qed. 
(*CLEARED*)
Lemma prod_fun_snd (C:prodCat) (X Y Z:C) (f:Z =-> Y) (g:Z =-> X) :
                                                pi2 << <|f , g|> =-= g. (*CLEAR*)
move: C X Y Z f g.
unfold prod_fun. case. simpl. move => OO MM. case. simpl. move => B. case. simpl. move => P pia pib pie A XX X Y Z f g.
by apply (proj1 (A Y X Z f g)).
Qed.

Lemma prod_fun_unique (C:prodCat) (X Y Z : C) (f:Z =-> X) (g:Z =-> Y) (h:Z =-> X * Y) :
    pi1 <<  h =-= f -> pi2 << h =-= g -> h =-= prod_fun f g.
move: C X Y Z f g h.
unfold prod_fun. case. simpl. move => OO MM. case. simpl. move => B. case. simpl.
move => P pia pib pie A XX X Y Z f g h Q Q'.
apply: ((proj2 (A _ _ _ f g) _ _)). by split.
Qed.
(*CLEARED*)
Lemma prod_unique (C:prodCat) (X Y Z : C) (h h':Z =-> X * Y) : 
  pi1 << h =-= pi1 << h' -> pi2 << h =-= pi2 << h' -> h =-= h'. (*CLEAR*)
move => A B. apply (tset_trans (prod_fun_unique (tset_refl _) (tset_refl _))).
apply tset_sym. by apply prod_fun_unique ; apply tset_sym.
Qed.
(*CLEARED*)
Add Parametric Morphism (C:prodCat) X Y Z : (@prod_fun C X Y Z)
  with signature (@tset_eq (C X Y)) ==> (@tset_eq (C X Z)) ==>
                 (@tset_eq (C X (Y * Z))) as prod_fun_eq_compat. (*CLEAR*)
move => f f' e g g' e'.  apply: prod_unique.
+ by do 2 rewrite prod_fun_fst ; apply e.
+ by do 2 rewrite prod_fun_snd ; apply e'.
Qed.
(*CLEARED*)
Lemma prod_map_prod_fun (C:prodCat) (X Y Z W A : C) (f:X =-> Y) (g: Z =-> W) 
                (h:A =-> _) (k:A =-> _) :  f >< g << <|h,k|> =-= <|f << h, g << k|>.
apply prod_unique; rewrite comp_assoc.
- do 2 rewrite prod_fun_fst. rewrite <- comp_assoc. by rewrite prod_fun_fst.
- do 2 rewrite prod_fun_snd. rewrite <- comp_assoc. by rewrite prod_fun_snd.
Qed.
(*=End *)

Lemma prod_fun_compl (Z:prodCat) (D E F G : Z) (f : D =-> E) (g : D =-> F) (h : G =-> D) : 
        <| f, g|> << h =-= <| f << h , g << h |>.
apply prod_unique.
- rewrite comp_assoc. by do 2 rewrite prod_fun_fst.
- rewrite comp_assoc. by do 2 rewrite prod_fun_snd.
Qed.

Lemma prod_fun_compr (Z:prodCat) (D E F G H : Z) (f : H =-> D) (g : D =-> E) (h : H =-> F) (k : F =-> G) :
       <| g << f, k << h |> =-= g >< k << <| f, h |>.
apply prod_unique.
rewrite comp_assoc. do 2 rewrite prod_fun_fst. rewrite <- comp_assoc. by rewrite prod_fun_fst.
rewrite comp_assoc. do 2 rewrite prod_fun_snd. rewrite <- comp_assoc. by rewrite prod_fun_snd.
Qed.

Lemma prod_fun_prod_fun (C:prodCat) (X Y Z W W':C) (h:X =-> Y) (k:X =-> Z) (f:Y * Z =-> W) (g:Y * Z =-> W') :
     <| f, g |> << <| h, k|> =-= <| f << <| h, k|>, g << <| h, k|> |>.
apply: prod_unique ; rewrite comp_assoc.
- by do 2 rewrite prod_fun_fst.
- by do 2 rewrite prod_fun_snd.
Qed.

Definition prod_assoc (C:prodCat) (D E F:C) : (D * E * F) =-> (D * (E * F)) := <| pi1 << pi1, <| pi2 << pi1, pi2|>|>.

Definition prod_assocI (C:prodCat) (D E F:C) : (D * (E * F)) =-> (D * E * F) := <| <| pi1, pi1 << pi2|>, pi2 << pi2|>.

Lemma prodAAI_id (C:prodCat) (D E F:C) : prod_assoc D E F << prod_assocI D E F =-= Id.
unfold prod_assoc. unfold prod_assocI.
apply prod_unique ; rewrite comp_assoc ; [rewrite -> prod_fun_fst | rewrite -> prod_fun_snd] ; rewrite comp_idR.
- rewrite <- comp_assoc. by do 2 rewrite prod_fun_fst. 
- apply prod_unique ; rewrite comp_assoc ; [rewrite -> prod_fun_fst | by do 2 rewrite -> prod_fun_snd].
  rewrite <- comp_assoc. rewrite prod_fun_fst. by rewrite prod_fun_snd.
Qed.

Lemma prodAIA_id (C:prodCat) (D E F:C) : prod_assocI D E F << prod_assoc D E F =-= Id.
unfold prod_assoc. unfold prod_assocI.
apply prod_unique ; rewrite comp_assoc ; [rewrite -> prod_fun_fst | rewrite -> prod_fun_snd] ; rewrite comp_idR.
- apply prod_unique ; rewrite comp_assoc; [by do 2rewrite -> prod_fun_fst | rewrite -> prod_fun_snd].
  rewrite <- comp_assoc. rewrite prod_fun_snd. by rewrite prod_fun_fst.
- rewrite <- comp_assoc. by do 2 rewrite prod_fun_snd.
Qed.

Lemma prod_eta (C:prodCat) (X Y Z : C) (f: X =-> Y * Z) : <| pi1 << f, pi2 << f|> =-= f.
apply: prod_unique.
- by rewrite prod_fun_fst.
- by rewrite prod_fun_snd.
Qed.

Lemma prod_id (C:prodCat) (D E : C) : <| pi1, pi2 |> =-= @Id _ (D * E).
rewrite <- (comp_idR pi1). rewrite <- (comp_idR pi2).
by apply prod_eta.
Qed.

Module Sums.

Section P.
Variable C:catType.
Variable A B P : C.
Variable in1 : morph A P.
Variable in2 : morph B P.

Definition axiom X (f:morph A X) g h := h << in1 =-= f /\ h << in2 =-= g.

End P.

End Sums.

Module CatSum.

Definition axiom (C:catType) (sum : C -> C -> C) (in1 : forall A B, C A (sum A B))
   (in2 : forall A B, C B (sum A B)) (h: forall A B Z, C A Z -> C B Z -> C (sum A B) Z) :=
  forall A B X f g, @Sums.axiom C A B (sum A B) (in1 _ _) (in2 _ _) X f g (h A B X f g) /\
        forall m, Sums.axiom (in1 _ _) (in2 _ _) f g m -> m =-= (h A B X f g).

Record mixin_of (C:catType) : Type := Mixin
{ sum : C -> C -> C;
  in1 : forall A B, morph A (sum A B);
  in2 : forall A B, morph B (sum A B);
  sum_exists : forall A B Z, morph A Z -> morph B Z -> morph (sum A B) Z;
  _ : axiom in1 in2 sum_exists }.

Section ClassDef.
Record class_of (T:Type) (M:T -> T -> setoidType) : Type :=
  Class { base : Category.class_of M ; ext : mixin_of (Category.Pack base T) }.

  Local Coercion base : class_of >-> Category.class_of.
  Local Coercion ext : class_of >-> mixin_of.

Structure cat : Type := Pack {object; morph : object -> object -> setoidType ; _ : class_of morph; _ : Type}.

  Local Coercion object : cat >-> Sortclass.
  Local Coercion morph : cat >-> Funclass.

Definition class cT := let: Pack _ _ c _ := cT return class_of cT in c.
Definition unpack (K:forall O (M:O -> O -> setoidType) (c:class_of M), Type)
            (k : forall O (M: O -> O -> setoidType) (c : class_of M), K _ _ c) (cT:cat) :=
  let: Pack _ M c _ := cT return @K _ _ (class cT) in k _ _ c.
Definition repack cT : _ -> Type -> cat := let k T M c p := p c in unpack k cT.
Definition pack := let k T M c m := Pack (@Class T M c m) T in Category.unpack k.

Definition catType (cT:cat) := Category.pack (class cT).
  End ClassDef.
Module Import Exports.
  Coercion catType : cat >-> Category.cat.
  Coercion base : class_of >-> Category.class_of.
  Coercion ext : class_of >-> mixin_of.
  Coercion object : cat >-> Sortclass.
  Coercion morph : cat >-> Funclass.
Notation sumCat := CatSum.cat.
Notation sumCatMixin := Mixin.
Notation sumCatType := pack.
Canonical Structure catType.
End Exports.

End CatSum.
Export CatSum.Exports.


Definition sum (C:sumCat) (A B:C) : C := (CatSum.sum (CatSum.class C) A B).
Definition in1 (C:sumCat) (A B:C) : morph A (sum A B) := (CatSum.in1 (CatSum.class C) A B).
Definition in2 (C:sumCat) (A B:C) : morph B (sum A B) := (CatSum.in2 (CatSum.class C) A B).
Definition sum_fun (C:sumCat) (Z A B:C) (f:C A Z) (g:C B Z) : morph (sum A B) Z := 
  (CatSum.sum_exists (CatSum.class C) f g).

Infix "+" := sum : C_scope.

Implicit Arguments in1 [C A B].
Implicit Arguments in2 [C A B].

Notation "'[|' f , g '|]'" := (sum_fun f g) (at level 30) : C_scope.

Arguments Scope sum_fun [_ C_scope C_scope C_scope S_scope S_scope].

Lemma sum_fun_fst (C:sumCat) (X Y Z:C) (f:Y =-> Z) (g:X =-> Z) : [|f , g|] << in1 =-= f.
move: C X Y Z f g.
unfold sum_fun. case. simpl. move => OO MM. case. simpl. move => B. case. simpl. move => P pia pib pie A XX X Y Z f g.
by apply (proj1 (A Y X Z f g)).
Qed.

Lemma sum_fun_snd (C:sumCat) (X Y Z:C) (f:Y =-> Z) (g:X =-> Z) : [|f , g|] << in2 =-= g.
move: C X Y Z f g.
unfold sum_fun. case. simpl. move => OO MM. case. simpl. move => B. case. simpl. move => P pia pib pie A XX X Y Z f g.
by apply (proj1 (A Y X Z f g)).
Qed.

Lemma sum_fun_unique (C:sumCat) (X Y Z : C) (f:X =-> Z) (g:Y =-> Z) (h:X + Y =-> Z) :
    h << in1 =-= f -> h << in2 =-= g -> h =-= sum_fun f g.
move: C X Y Z f g h.
unfold sum_fun. case. simpl. move => OO MM. case. simpl. move => B. case. simpl.
move => P pia pib pie A XX X Y Z f g h Q Q'.
apply (proj2 (A _ _ _ f g)). by split.
Qed.

Lemma sum_unique (C:sumCat) (X Y Z : C) (h h':X + Y =-> Z) :
  h << in1 =-= h' << in1 -> h << in2 =-= h' << in2 -> h =-= h'.
move => A B. apply: (tset_trans (sum_fun_unique (tset_refl _) (tset_refl _))).
apply tset_sym. by apply sum_fun_unique ; apply tset_sym.
Qed.

Add Parametric Morphism (C:sumCat) (X Y Z:C) : (@sum_fun C _ _ _)
  with signature (@tset_eq (C X Y)) ==> (@tset_eq (C Z Y)) ==> (@tset_eq (C (X + Z) Y))
  as sum_fun_eq_compat.
move => f f' e g g' e'.  apply: sum_unique.
+ by do 2 rewrite sum_fun_fst ; apply e.
+ by do 2 rewrite sum_fun_snd ; apply e'.
Qed.

Lemma SUM_fun_comp : 
  forall (Z:sumCat) (C D E F:Z) (f:C=->E) (g:D=->E) (h:E=->F), h << [|f, g|] =-= [|h << f, h << g|].
move => Z C D E F f g h.
by apply: sum_fun_unique ; rewrite <- comp_assoc ; [rewrite -> sum_fun_fst | rewrite -> sum_fun_snd].
Qed.

Lemma sum_eta (C:sumCat) (X Y Z : C) (f: X + Y =-> Z) : [|f << in1, f << in2|] =-= f.
apply sum_unique.
- by rewrite sum_fun_fst.
- by rewrite sum_fun_snd.
Qed.

Lemma sum_id (C:sumCat) (X Y : C) : [| in1, in2|] =-= @Id _ (X + Y).
rewrite <- (comp_idL in1).
rewrite <- (comp_idL in2).
by apply sum_eta.
Qed.

Module Exponential.

Section P.
Variable C:prodCat.
Variable X Y Z E : C.
Variable ev : C (E * X) Y.
Variable exp : C (Z * X) Y -> C Z E.

Definition axiom (h:C Z E) h' := ev << h >< Id =-= h'.

End P.

End Exponential.

Module CatExp.

Definition axiom (C:prodCat) (E:C -> C -> C)
   (ev:forall X Y, C (E X Y * X) Y) (exp:forall X Y Z, C (X * Y) Z -> C X (E Y Z)) :=
  forall X Y Z h, @Exponential.axiom C _ _ _ (E _ _) (ev Y Z) (exp X Y Z h) h /\
        forall h', Exponential.axiom (ev _ _) h' h -> h' =-= (exp X Y Z h).

Record mixin_of (C:prodCat) : Type := Mixin
{ 
  exp : C -> C -> C;
  ev : forall X Y, C (exp X Y * X) Y;
  exp_fun : forall X Y Z, C (X * Y) Z -> C X (exp Y Z);
  _ : axiom ev exp_fun
}.

Section ClassDef.
Record class_of (T:Type) (M:T -> T -> setoidType) : Type :=
  Class { base : CatProduct.class_of M ; ext : mixin_of (CatProduct.Pack base T) }.
  Local Coercion base : class_of >-> CatProduct.class_of.
  Local Coercion ext : class_of >-> mixin_of.

Structure cat : Type := Pack {object; morph : object -> object -> setoidType ; _ : class_of morph; _ : Type}.
  Local Coercion object : cat >-> Sortclass.
  Local Coercion morph : cat >-> Funclass.

Definition class cT := let: Pack _ _ c _ := cT return class_of cT in c.
Definition unpack (K:forall O (M:O -> O -> setoidType) (c:class_of M), Type)
            (k : forall O (M: O -> O -> setoidType) (c : class_of M), K _ _ c) (cT:cat) :=
  let: Pack _ M c _ := cT return @K _ _ (class cT) in k _ _ c.
Definition repack cT : _ -> Type -> cat := let k T M c p := p c in unpack k cT.
Definition pack := let k T M c m := Pack (@Class T M c m) T in CatProduct.unpack k.

Definition catType (cT:cat) := Category.Pack (class cT) cT.
Definition catProdType (cT:cat) := CatProduct.Pack (class cT) cT.
End ClassDef.
Module Import Exports.
  Coercion catProdType : cat >-> CatProduct.cat.
  Coercion base : class_of >-> CatProduct.class_of.
  Coercion ext : class_of >-> mixin_of.
  Coercion object : cat >-> Sortclass.
  Coercion morph : cat >-> Funclass.
Notation expCat := CatExp.cat.
Notation expCatMixin := CatExp.Mixin.
Notation expCatType := CatExp.pack.
Canonical Structure CatExp.catType.
Canonical Structure CatExp.catProdType.
End Exports.
End CatExp.
Export CatExp.Exports.

Definition exp (C:expCat) (A B : C) : C := CatExp.exp (CatExp.class C) A B.
Definition ev (C:expCat) (A B : C) : C (exp A B * A) B := CatExp.ev (CatExp.class C) A B.
Definition exp_fun (C:expCat) (X Y Z : C) (h: C (X * Y) Z) : C X (exp Y Z) := CatExp.exp_fun (CatExp.class C) h.

Implicit Arguments ev [C A B].

Arguments Scope ev [_ C_scope C_scope].
Arguments Scope exp [_ C_scope C_scope].

Infix "-=>" := exp (at level 54, right associativity) : C_scope.

Lemma exp_com (C:expCat) (X Y Z : C) (h:X * Y =-> Z) : ev << exp_fun h >< Id =-= h.
move: C X Y Z h.
unfold exp_fun. unfold ev. simpl.
case. move => OO MM. case. simpl. move => B. case. move => eexp eev eexp_fun A T X Y Z h. simpl.
by apply (proj1 (A X Y Z h)).
Qed.

Lemma exp_unique (C:expCat) (X Y Z : C) (h:X =-> Y -=> Z) h' : ev << h >< Id =-= h' -> h =-= exp_fun h'.
move: C X Y Z h h'.
unfold exp_fun. unfold ev. simpl.
case. move => OO MM. case. simpl. move => B. case. move => eexp eev eexp_fun A T X Y Z h h'. simpl.
by apply (proj2 (A X Y Z h')).
Qed.

Add Parametric Morphism (C:expCat) (X Y Z:C) : (@exp_fun C X Y Z)
  with signature (@tset_eq (C (X * Y) Z)) ==> (@tset_eq (C X (Y -=> Z)))
  as exp_fun_eq_compat.
move => f f' e. apply: exp_unique.
by rewrite exp_com.
Qed.

Lemma exp_ev (Z:expCat) : forall (C D E:Z) (f:C =-> D -=> E) , exp_fun (ev << f >< Id ) =-= f.
symmetry.
by apply: exp_unique.
Qed.

Lemma exp_comp (Z:expCat) : forall (A B C D:Z) (f:A * B =-> C) (g:D =-> A), exp_fun f << g =-= exp_fun (f << g >< Id).
intros A B C D f g.
have H:=exp_com f. rewrite <- H.
rewrite <- comp_assoc. rewrite prod_map_prod_fun. rewrite exp_ev.
rewrite comp_idL. rewrite comp_assoc. by rewrite exp_ev.
Qed.

Definition uncurry (Z:expCat) (D0 D1 D2 : Z) (f:D0 =-> D1 -=> D2) : D0 * D1 =-> D2 :=
      ev << <|f << pi1, pi2|>.

Lemma UC_id (C:expCat) (X Y Z:C) (f:X * Y =-> Z) : uncurry (exp_fun f) =-= f.
unfold uncurry.
rewrite <- (comp_idL pi2). by rewrite -> exp_com.
Qed.

Lemma CU_id (C:expCat) (X Y Z:C) (f:X =-> Y -=> Z) : exp_fun (uncurry f) =-= f.
unfold uncurry. rewrite <- (comp_idL pi2).
by rewrite -> exp_ev.
Qed.

Module ProdSumCat.

Record mixin_of (C:prodCat) : Type := Mixin {
  sumM :> CatSum.mixin_of C;
  initialM :> CatInitial.mixin_of C;
  terminalM :> CatTerminal.mixin_of C
  }.

Section ClassDef.

Record class_of (T:Type) (M:T -> T -> setoidType) : Type :=
  Class { base : CatProduct.class_of M ; ext : mixin_of (CatProduct.Pack base T) }.

  Local Coercion base : class_of >-> CatProduct.class_of.
  Local Coercion ext : class_of >-> mixin_of.

  Definition base2 (T:Type) (M:T -> T -> setoidType) (c:class_of M) : CatSum.class_of M := CatSum.Class c.
  Definition base3 (T:Type) (M:T -> T -> setoidType) (c:class_of M) : CatInitial.class_of M := CatInitial.Class c.
  Definition base4 (T:Type) (M:T -> T -> setoidType) (c:class_of M) : CatTerminal.class_of M := CatTerminal.Class c.

  Local Coercion base2 : class_of >-> CatSum.class_of.
  Local Coercion base3 : class_of >-> CatInitial.class_of.
  Local Coercion base4 : class_of >-> CatTerminal.class_of.

Structure cat : Type := Pack {object; morph : object -> object -> setoidType ; _ : class_of morph; _ : Type}.
  Local Coercion object : cat >-> Sortclass.
  Local Coercion morph : cat >-> Funclass.

Definition class cT := let: Pack _ _ c _ := cT return class_of cT in c.
Definition unpack (K:forall O (M:O -> O -> setoidType) (c:class_of M), Type)
            (k : forall O (M: O -> O -> setoidType) (c : class_of M), K _ _ c) (cT:cat) :=
  let: Pack _ M c _ := cT return @K _ _ (class cT) in k _ _ c.
Definition repack cT : _ -> Type -> cat := let k T M c p := p c in unpack k cT.
Definition pack := let k T M c m := Pack (@Class T M c m) T in CatProduct.unpack k.

Definition catType (cT:cat) := Category.Pack (class cT) cT.
Definition catProdType (cT:cat) := CatProduct.Pack (class cT) cT.
Definition catTerminalType (cT:cat) := CatTerminal.Pack (class cT) cT.
Definition catSumType (cT:cat) := CatSum.Pack (class cT) cT.
Definition catInitialType (cT:cat) := CatInitial.Pack (class cT) cT.
End ClassDef.

Module Import Exports.
  Coercion catProdType : cat >-> CatProduct.cat.
  Coercion catSumType : cat >-> CatSum.cat.
  Coercion catInitialType : cat >-> CatInitial.cat.  
  Coercion catTerminalType : cat >-> CatTerminal.cat.
  Coercion base : class_of >-> CatProduct.class_of.
  Coercion base2 : class_of >-> CatSum.class_of.
  Coercion base3 : class_of >-> CatInitial.class_of.
  Coercion base4 : class_of >-> CatTerminal.class_of.
  Coercion ext : class_of >-> mixin_of.
  Coercion object : cat >-> Sortclass.
  Coercion morph : cat >-> Funclass.
Notation prodsumCat := cat.
Notation prodsumCatType := pack.
Canonical Structure catType.
Canonical Structure catProdType.
Canonical Structure catSumType.
Canonical Structure catInitialType.
Canonical Structure catTerminalType.
End Exports.

End ProdSumCat.
Export ProdSumCat.Exports.

Module Distributive.

Record mixin_of (C:prodsumCat) : Type := Mixin
 { distribS : forall (X Y Z:C), (X + Y) * Z =-> (X * Z) + (Y * Z);
   isoS : forall (X Y Z:C), iso (distribS X Y Z) ([| (in1 : C _ _) >< Id, (in2 : C _ _) >< Id|]);
   isoN : forall (X:C), iso (initial_morph (X*Zero)) pi2
}.

Section ClassDef.

Record class_of (T:Type) (M:T -> T -> setoidType) : Type :=
  Class { base : ProdSumCat.class_of M ; ext : mixin_of (ProdSumCat.Pack base T) }.
  Local Coercion base : class_of >-> ProdSumCat.class_of.
  Local Coercion ext : class_of >-> mixin_of.


Structure cat : Type := Pack {object : Type; morph : object -> object -> setoidType ; _ : class_of morph; _ : Type}.
  Local Coercion object : cat >-> Sortclass.
  Local Coercion morph : cat >-> Funclass.

Definition class cT := let: Pack _ _ c _ := cT return class_of cT in c.
Definition unpack (K:forall O (M:O -> O -> setoidType) (c:class_of M), Type)
            (k : forall O (M: O -> O -> setoidType) (c : class_of M), K _ _ c) (cT:cat) :=
  let: Pack _ M c _ := cT return @K _ _ (class cT) in k _ _ c.
Definition repack cT : _ -> Type -> cat := let k T M c p := p c in unpack k cT.
Definition pack := let k T M c m := Pack (@Class T M c m) T in ProdSumCat.unpack k.

Definition catType (cT:cat) := Category.Pack (class cT) cT.
Definition catProdType (cT:cat) := CatProduct.Pack (class cT) cT.
Definition catSumType (cT:cat) := CatSum.Pack (class cT) cT.
Definition catInitialType (cT:cat) := CatInitial.Pack (class cT) cT.
Definition catTerminalType (cT:cat) := CatTerminal.Pack (class cT) cT.
Definition catProdSumType (cT:cat) := ProdSumCat.Pack (class cT) cT.
End ClassDef.
Module Import Exports.
  Coercion catProdSumType : cat >-> ProdSumCat.cat.
  Coercion base : class_of >-> ProdSumCat.class_of.
  Coercion ext : class_of >-> mixin_of.
  Coercion object : cat >-> Sortclass.
  Coercion morph : cat >-> Funclass.
Canonical Structure catType.
Canonical Structure catProdType.
Canonical Structure catSumType.
Canonical Structure catInitialType.
Canonical Structure catTerminalType.
Notation distCat := Distributive.cat.
Notation distCatMixin := Distributive.Mixin.
Notation distCatType := Distributive.pack.
Canonical Structure catProdSumType.
End Exports.
End Distributive.
Export Distributive.Exports.

Module CatIProduct.
Section XX.
Variable C:catType.
Definition prod_diagram I (A:I -> C) (P : C) (pi : forall i, C P (A i)) 
                            (X : C) (f : forall i, C X (A i)) (h : C X P) :=
                        forall i, pi i << h =-= f i.
Definition axiom I (prod : (I -> C) -> C) (pi : forall A i, C (prod A) (A i))
    (h: forall A Z, (forall i, C Z (A i)) -> C Z (prod A)) :=
  forall A X f,
      @prod_diagram I A (prod A) (pi _) X f (h A _ f) /\
        forall m, prod_diagram (pi _) f m -> m =-= (h A X f).
Record mixin_of : Type := Mixin
{ prod : forall I, (I -> C) -> C;
  pi : forall I A i, C (prod A) (A i);
  prod_ex : forall I A Z, (forall i, C Z (A i)) -> C Z (@prod I A);
  _ : forall I, @axiom I _ (@pi I) (@prod_ex I)}.

End XX.

Section BiProd.
Variable C:catType.
Variable m:mixin_of C.

Lemma biAxiom : @CatProduct.axiom C (fun A B => prod m (fun x => match x with inl _ => A | inr _ => B end))
              (fun A B => pi m (fun x => match x with inl _ => A | inr _ => B end) (inl _ tt))
              (fun A B => pi m (fun x => match x with inl _ => A | inr _ => B end) (inr _ tt))
               (fun A B (Z:C) (f:Z =-> A) g => @prod_ex _ _ _ (fun x => match x with inl _ => A | inr _ => B end) Z
                (fun i => match i with inl _ => f | inr _ => g end)) .
case: m. move => P pi' ex ax.
move => A B X f g. simpl.
specialize (@ax (unit+unit)%type (fun x => match x with inl _ => A | inr _ => B end) X
                (fun i => match i with inl _ => f | inr _ => g end)).
simpl in ax. case: ax => ax0 ax1. split ; first split.
- by apply (ax0 (inl unit tt)).
- by apply (ax0 (inr unit tt)).
- move => m' ax. apply (ax1 m'). clear ax1. case ; case. by apply (proj1 ax). by apply (proj2 ax).
Qed.

Definition prodM := prodCatMixin biAxiom.
End BiProd.

Section ClassDef.

Record class_of (T:Type) (M:T -> T -> setoidType) : Type :=
  Class { base : Category.class_of M ; ext : mixin_of (Category.Pack base T)}.
  Local Coercion base : class_of >-> Category.class_of.
  Local Coercion ext : class_of >-> mixin_of.

Definition base2 (T:Type) (M:T -> T -> setoidType) (c:class_of M) := CatProduct.Class (prodM c).
  Local Coercion base2 : class_of >-> CatProduct.class_of.

Structure cat : Type := Pack {object;
       morph : object -> object -> setoidType ; _ : class_of morph; _ : Type}.
  Local Coercion object : cat >-> Sortclass.
  Local Coercion morph : cat >-> Funclass.

Definition class cT := let: Pack _ _ c _ := cT return class_of cT in c. (*CLEAR*)
Definition unpack (K:forall O (M:O -> O -> setoidType) (c:class_of M), Type)
            (k : forall O (M: O -> O -> setoidType) (c : class_of M), K _ _ c) (cT:cat) :=
  let: Pack _ M c _ := cT return @K _ _ (class cT) in k _ _ c.
Definition repack cT : _ -> Type -> cat := let k T M c p := p c in unpack k cT.
(*CLEARED*)
Definition pack := let k T M c m := Pack (@Class T M c m) T in Category.unpack k.
Definition catType (cT:cat) := Category.Pack (class cT) cT.
Definition prodCatType (cT:cat) := CatProduct.Pack (class cT) cT.
End ClassDef.
  Module Import Exports.
  Coercion catType : cat >-> Category.cat.
  Coercion base : class_of >-> Category.class_of.
  Coercion base2 : class_of >-> CatProduct.class_of.
  Coercion ext : class_of >-> mixin_of.
  Coercion object : cat >-> Sortclass.
  Coercion morph : cat >-> Funclass.
Notation prodICat := cat.
Notation prodICatMixin := Mixin.
Notation prodICatType := pack.
Canonical Structure catType.
Canonical Structure prodCatType.
  End Exports.

End CatIProduct.
Export CatIProduct.Exports.

Definition prodi (C:prodICat) I (A: I -> C) : C :=
                   (CatIProduct.prod (CatIProduct.class C) A).
Definition pi (C:prodICat) I (A: I -> C) i : C (prodi A) (A i) :=
                   (CatIProduct.pi (CatIProduct.class C) A i).
Definition prodi_fun (C:prodICat) (Z:C) I (A:I -> C) (f:forall i, C Z (A i)) :
  C Z (prodi A) := (CatIProduct.prod_ex (CatIProduct.class C) f).
Implicit Arguments pi [C I A].

Arguments Scope prodi_fun [_ _ C_scope C_scope S_scope S_scope].

Lemma prodi_fun_pi (C:prodICat) I (Z:C) (A:I -> C) (f:forall i:I,Z =-> A i) (i:I):
                                                pi i << prodi_fun f =-= f i.
move: C I Z A f i.
unfold prodi_fun. case. simpl. move => OO MM. case. simpl. move => B. case. simpl. move => P pia pie A XX X Y Z f i.
by apply (proj1 (A X Z Y f)).
Qed.

Lemma prodi_fun_unique (C:prodICat) I (Z : C) (X:I -> C) (f:forall i, Z =-> X i) (h:Z =-> prodi X) :
    (forall i, pi i <<  h =-= f i) -> h =-= prodi_fun f. 
move: C I Z X f h.
unfold prodi_fun. case. simpl. move => OO MM. case. simpl. move => B. case. simpl.
move => P pia pie A XX X Y Z f g h.
apply: ((proj2 (A _ _ _ f) _ _)). by apply: h.
Qed.

Lemma prodi_unique (C:prodICat) I (Z : C) (A:I -> C) (h h':Z =-> prodi A) : 
  (forall i, pi i << h =-= pi i << h') -> h =-= h'.
move => X. apply (tset_trans (prodi_fun_unique (fun i => tset_refl _))).
apply tset_sym. by apply prodi_fun_unique ; move => i ; apply tset_sym.
Qed.

Record functor (C C':catType) : Type := mk_functor
 { functor_ob :> C -> C';
   functor_morph :> forall (X Y : C), (C X Y) -> C' (functor_ob X) (functor_ob Y);
   functor_id : forall X, @functor_morph X X Id =-= Id;
   functor_comp : forall X Y Z (f:C Y Z) (g:C X Y), functor_morph (f << g) =-= functor_morph f << functor_morph g
 }.

Implicit Arguments functor_morph [C C' X Y].

(*
Module CatCountable.

Section ClassDef.
Record class_of (T:Type) (M:T -> T -> setoidType) : Type :=
  Class { base1 : Category.class_of M ; ext : Countable.mixin_of (Category.Pack base1 T)}.
  Local Coercion base1 : class_of >-> Category.class_of.
  Local Coercion ext : class_of >-> Countable.mixin_of.

  Definition base2 (T:Type) (M:T -> T -> setoidType) (c:class_of M) : Countable.class_of (Category.Pack (base1 c) T) := 
  Countable.Class (Choice.Class (Countable.EqMixin c) (Countable.ChoiceMixin c)) c.
  Local Coercion base2 : class_of >-> Countable.class_of.

Structure cat : Type := Pack {object :> Type; morph :> object -> object -> setoidType ; _ : class_of morph; _ : Type}.
Definition class cT := let: Pack _ _ c _ := cT return class_of cT in c.
Definition unpack (K:forall O (M:O -> O -> setoidType) (c:class_of M), Type)
            (k : forall O (M: O -> O -> setoidType) (c : class_of M), K _ _ c) (cT:cat) :=
  let: Pack _ M c _ := cT return @K _ _ (class cT) in k _ _ c.
Definition repack cT : _ -> Type -> cat := let k T M c p := p c in unpack k cT.
Definition pack := let k T M c m := Pack (@Class T M c m) T in Category.unpack k.

Definition catType cT := Category.Pack (class cT) cT.
Definition countType (cT:cat) := Countable.Pack (class cT) cT.
End ClassDef.
Module Import Exports.
  Coercion base1 : class_of >-> Category.class_of.
  Coercion ext : class_of >-> Countable.mixin_of.
  Coercion base2 : class_of >-> Countable.class_of.
  Coercion catType : cat >-> Category.cat.
  Coercion countType : cat >-> Countable.type.
Canonical Structure catType.
Canonical Structure countType.
Notation countCat := cat.
Notation CountCat := pack.
End Exports.
End CatCountable.
Export CatCountable.Exports.
*)

(*
Module CatLimit.

Section Cone.

Variable C C':catType.
Variable F:functor C C'.

Record Cone : Type := mk_cone
{ conet :> C';
  conem :> forall c:C, conet =-> (F c);
  conem_com : forall c0 c1 (m:C c0 c1), (functor_morph F m) << conem c0 =-= conem c1 }.

Record Limit : Type := mk_limit
{ 
  limitt :> Cone;
  limitm : forall (X:Cone), X =-> limitt;
  limitm_com : forall (X:Cone) (c:C), X c =-= limitt c << limitm X
}.

End Cone.

Record mixin_of (C:catType) : Type := Mixin {
  limits :> forall (C':countCat) (F:functor C' C), Limit F
}.

Record class_of (T:Type) (M:T -> T -> setoidType) : Type :=
  Class { base1 :> Category.class_of M ; ext :> mixin_of (Category.Pack base1 T) }.

Structure cat : Type := Pack {object :> Type; morph :> object -> object -> setoidType ; _ : class_of morph; _ : Type}.
Definition class cT := let: Pack _ _ c _ := cT return class_of cT in c.
Definition unpack (K:forall O (M:O -> O -> setoidType) (c:class_of M), Type)
            (k : forall O (M: O -> O -> setoidType) (c : class_of M), K _ _ c) (cT:cat) :=
  let: Pack _ M c _ := cT return @K _ _ (class cT) in k _ _ c.
Definition repack cT : _ -> Type -> cat := let k T M c p := p c in unpack k cT.
Definition pack := let k T M c m := Pack (@Class T M c m) T in Category.unpack k.

Coercion catType (cT:cat) := Category.Pack (class cT) cT.

Section Theory.

Variable cT:cat.
Variable C':countCat.
Variable F:functor C' cT.
Variable C:Cone F.

Definition limit_cone : Cone F := (limitt (class cT C' F)).
Definition limit : cT := conet limit_cone.
Definition limit_fun : cT (conet C) limit := limitm (class cT C' F) C.
Lemma limit_com c : conem C c =-= conem limit_cone c << limit_fun.
move => c. by apply limitm_com.
Qed.

End Theory.

End CatLimit.

Notation cone := CatLimit.Cone.
Notation limitCat := CatLimit.cat.
Notation LimitCatMixin := CatLimit.Mixin.
Notation LimitCat := CatLimit.pack.
Canonical Structure CatLimit.catType.

Notation limit := CatLimit.limit.

Module CatCoLimit.

Section CoCone.

Variable C C':catType.
Variable F:functor C C'.

Record CoCone : Type := mk_cocone
{ coconet :> C';
  coconem :> forall c:C, F c =-> coconet;
  coconem_com : forall c0 c1 (m:C c0 c1), coconem c1 << (functor_morph F m) =-= coconem c0 }.

Record CoLimit : Type := mk_colimit
{ 
  colimitt :> CoCone;
  colimitm : forall (X:CoCone), colimitt =-> X;
  colimitm_com : forall (X:CoCone) (c:C), coconem X c =-= colimitm X << colimitt c
}.

End CoCone.

Record mixin_of (C:catType) : Type := Mixin {
  colimits :> forall (C':countCat) (F:functor C' C), CoLimit F
}.

Record class_of (T:Type) (M:T -> T -> setoidType) : Type :=
  Class { base1 :> Category.class_of M ; ext :> mixin_of (Category.Pack base1 T) }.

Structure cat : Type := Pack {object :> Type; morph :> object -> object -> setoidType ; _ : class_of morph; _ : Type}.
Definition class cT := let: Pack _ _ c _ := cT return class_of cT in c.
Definition unpack (K:forall O (M:O -> O -> setoidType) (c:class_of M), Type)
            (k : forall O (M: O -> O -> setoidType) (c : class_of M), K _ _ c) (cT:cat) :=
  let: Pack _ M c _ := cT return @K _ _ (class cT) in k _ _ c.
Definition repack cT : _ -> Type -> cat := let k T M c p := p c in unpack k cT.
Definition pack := let k T M c m := Pack (@Class T M c m) T in Category.unpack k.

Coercion catType (cT:cat) := Category.Pack (class cT) cT.

Section Theory.

Variable cT:cat.
Variable C':countCat.
Variable F:functor C' cT.
Variable C:CoCone F.

Definition colimit_cone : CoCone F := (colimitt (class cT C' F)).
Definition colimit : cT := coconet colimit_cone.
Definition colimit_fun : cT colimit (coconet C) := colimitm (class cT C' F) C.
Lemma colimit_com c : @coconem _ _ F C c =-= @Category.comp cT _ _ _ colimit_fun (coconem colimit_cone c).
move => c. by apply colimitm_com.
Qed.

End Theory.

End CatCoLimit.

Notation cocone := CatCoLimit.CoCone.
Notation colimitCat := CatCoLimit.cat.
Notation CoLimitCatMixin := CatCoLimit.Mixin.
Notation CoLimitCat := CatCoLimit.pack.
Canonical Structure CatCoLimit.catType.

Notation colimit := CatCoLimit.colimit.
*)
Close Scope C_scope.
Close Scope S_scope.
