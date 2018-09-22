Require Export Setoids.Setoid.

Set Implicit Arguments.
Unset Strict Implicit.

Record SetKind :=
  {
    tSetKind :> Type;
    eq_rel : tSetKind -> tSetKind -> Prop;
    Peq_rel : equiv _ eq_rel
  }.

Record set (sk:SetKind) :=
  {
    car : tSetKind sk -> Prop;
    car_eq : forall x y, @eq_rel sk x y -> car x -> car y
  }.

Lemma set_trans : forall (T:SetKind) a b c, (@eq_rel T a b) -> (eq_rel b c) -> (eq_rel a c).
intros T a b c ab bc.
assert (xx:=Peq_rel T). unfold equiv in *. destruct xx as [_ [tt _]].
unfold transitive in tt. apply (tt _ _ _ ab bc).
Qed.

Hint Resolve set_trans.

Lemma set_refl : forall (T:SetKind) a, @eq_rel T a a.
intros T a. assert (xx:=Peq_rel T). unfold equiv in *. destruct xx as [tt [_ _]].
unfold reflexive in tt. apply (tt a).
Qed.

Hint Resolve set_refl.

Lemma set_sym : forall (T:SetKind) a b, (@eq_rel T a b) -> (eq_rel b a).
intros T a b. assert (xx:=Peq_rel T). unfold equiv in *. destruct xx as [_ [_ tt]].
unfold symmetric in tt. apply (tt a b).
Qed.

Hint Resolve set_sym.

Definition union T (S R:set T) : set T.
intros T S R. exists (fun x => car S x \/ car R x).
intros x y Rel xy. destruct xy as [Sx | Sy].
left. apply (car_eq Rel Sx). right. apply (car_eq Rel Sy).
Defined.

Definition Union T (S:set T -> Prop) : set T.
intros T S. exists (fun x => exists s, S s /\ car s x).
intros x y Rel xy. destruct xy as [s [Ss cx]].
exists s. split. auto. refine (car_eq Rel cx).
Defined.

Definition intersect T (S R:set T) : set T.
intros T S R. exists (fun x => car S x /\ car R x).
intros x y Rel [Sx Rx]. split.
apply (car_eq Rel Sx). apply (car_eq Rel Rx).
Defined.

Definition Intersect T (S: set T -> Prop) : set T.
intros T S. exists (fun x => forall s, S s -> car s x).
intros x y Rel C s Ss.
apply (car_eq Rel (C _ Ss)).
Defined.

Definition subset T (S R:set T) := forall x, car S x -> car R x.

Definition set_eq T (S R:set T) := subset S R /\ subset R S.

Definition setmorphism (T T':SetKind) (f: T -> set T') :=
    forall x y, @eq_rel T x y -> set_eq (f x) (f y).

Record fsetm (T T':SetKind) :=
  {
    fsett :> T -> set T';
    fsetmorphism : setmorphism fsett
  }.

Definition Sarrow (T:Type) (T':SetKind) : SetKind.
intros T T'. exists (T -> T') (fun f g => forall x, eq_rel (f x) (g x)).
assert (equiv _ (@eq_rel T')). apply Peq_rel.
unfold equiv in *. unfold reflexive in *. unfold transitive in *. unfold symmetric in *.
destruct H as [r [t s]]. split.
intros f x. auto. split. intros f g h a b x. specialize (a x). specialize (b x).
specialize (t _ _ _  a b). apply t.
intros f g a x. specialize (a x). specialize (s _ _ a). apply s.
Defined.

Definition Sprod (T T' : SetKind) : SetKind.
intros T T'. exists (T * T')%type (fun p0 p1 => @eq_rel T (fst p0) (fst p1) /\ @eq_rel T' (snd p0) (snd p1)).
assert (equiv _ (@eq_rel T)) as [sr [st ss]] by (apply Peq_rel).
assert (equiv _ (@eq_rel T')) as [s'r [s't s's]] by (apply Peq_rel).
unfold equiv. unfold reflexive in *. unfold transitive in *. unfold symmetric in *.
split. intros x. case x. clear x. intros ; auto. split.
intros x ; case x ; clear x. intros x0 x1 y ; case y ; clear y.
intros y0 y1 z ; case z ; clear z ; intro z0. simpl. intros z1 [E0 E1] [E2 E3].
specialize (st _ _ _ E0 E2). specialize (s't _ _ _ E1 E3).
split ; auto.
intros x ; case x ; clear x ; intros x0 x1 y ; case y ; clear y ; intros y0 y1.
simpl. intros [E0 E1]. specialize (ss _ _ E0). specialize (s's _ _ E1).
split ; auto.
Defined.

Definition SFst T T' : set (Sprod T T') -> set T.
intros T T' S. exists (fun t => exists t', car S (t,t')).
intros t0 t1. intros Rel ex. destruct ex as [t' c0]. exists t'.
simpl in *. assert (@eq_rel (Sprod T T') (t0,t') (t1,t')) as Rel'.
simpl. split. apply Rel. apply set_refl.
refine (car_eq Rel' c0).
Defined.

Definition SSnd T T' : set (Sprod T T') -> set T'.
intros T T' S. exists (fun t' => exists t, car S (t,t')).
intros t0 t1. intros Rel ex. destruct ex as [t' c0]. exists t'.
simpl in *. assert (@eq_rel (Sprod T T') (t',t0) (t',t1)) as Rel'.
simpl. split. apply set_refl. apply Rel.
refine (car_eq Rel' c0).
Defined.

Definition Ssum (T T':SetKind) : SetKind.
intros T T'. exists (T + T') % type 
   (fun x y => match x, y with | inl x, inl y => eq_rel x y 
                               | inr x, inr y => eq_rel x y | _,_ => False 
               end).
unfold equiv.  split. unfold reflexive. intros x ; case x ; auto.
split. unfold transitive.
intros x y z ; case x ; clear x ; intros x ; case y ; clear y ; intros y ;
 case z ; clear z ; intros z ; auto.
refine (@set_trans T x y z).
intros incon. inversion incon. intros incon. inversion incon.
refine (@set_trans T' x y z).

unfold symmetric.
intros x y ; case x ; clear x ; intro x ; case y ; clear y ; intros y ; auto.
Defined.

Definition SingleSet (T:SetKind) (v:T) : set T.
intros T x. exists (fun (y:T) => eq_rel x y).
intros x0 y0. intros veq xeq. assert (tt:= proj1 (proj2 (Peq_rel T))).
unfold transitive in tt. apply (tt _ _ _ xeq veq).
Defined.

Definition EmptySet (T:SetKind) : set T.
intros T. exists (fun (x:T) => False).
auto.
Defined.

Definition inv_Kind (T:SetKind) S (f:S -> T) : SetKind.
intros T S f. exists (S) (fun x y => eq_rel (f x) (f y)).
unfold equiv. split. unfold reflexive.
intros s. auto. split. unfold transitive. intros x y z xy yz.
apply (proj1 (proj2 (Peq_rel T)) (f x) (f y) (f z)) ; auto.
intros x y. apply (proj2 (proj2 (Peq_rel T)) (f x) (f y)).
Defined.

Definition inv_image (T:SetKind) S (f:S -> T) : set T -> set (inv_Kind f).
intros T S f t.
exists (fun x => car t (f x)).
simpl. intros x y xy cx.
refine (car_eq xy cx).
Defined.

Definition LeibnizKind (T:Type) : SetKind.
intros T. exists T (@eq T).
unfold equiv. split. unfold reflexive. auto. split.
unfold transitive. intros x y z xy yz. apply (trans_eq xy yz).
unfold symmetric. intros x y xy. apply (sym_eq xy).
Defined.

Definition LeibnizSet (T:Type) (car:T -> Prop) : set (LeibnizKind T).
intros T c. exists c.
intros x y eq. simpl in eq. rewrite eq. auto.
Defined.

Definition EqSetKind T eq_rel (Peq_rel:equiv T eq_rel) : SetKind.
intros T eq equiv. exists T eq. auto.
Defined.

Definition UNIV T : set T.
intros T. exists (fun x => True). auto.
Defined.

Definition set_respect (T T':SetKind) (f:T -> T') := forall x y, eq_rel x y -> eq_rel (f x) (f y). 

Definition Inv_image (T T':SetKind) (f:T -> T') (sf:set_respect f) : (set T') -> set T.
intros T T' f sf s. exists (fun x => car s (f x)).
intros x y eq c. refine (car_eq _ c). unfold set_respect in sf.
refine (sf _ _ eq).
Defined.

Lemma fst_set_respect : forall (T T':SetKind), @set_respect (Sprod T T') T (@fst T T').
intros T T'. unfold set_respect.
simpl. intros x y [R _]. apply R.
Qed.

Lemma snd_set_respect : forall (T T':SetKind), @set_respect (Sprod T T') T' (@snd T T').
intros T T' x y [_ R]. apply R.
Qed.

