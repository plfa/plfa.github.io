(**********************************************************************************
 * Finmap.v                                                                       *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                       *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)

(* Finite maps with comparison on the domain *)

(*
 Summary of things:

 Types:
   compType is is the type of computable linear orders.
   [compType of nat] is the linear order of natural numbers.

   FinDom (C:compType) (T:Type) : Type 
     is the type finite maps from C to T.
     If T is an equality type then findom_eqType C T is an equality type.

   fdEmpty : FinDom C T
     the every undefined finite map.

   dom_fdEmpty : dom fdEmpty = [::]

   findom_undef (f:FinDom C T) (c \notin dom f) : f c = None

   findom_indom f c : (c \in dom f) = isSome (f c)

   updMap (c:T) (t:T) (f:FinDom C T) : FinDom C T
     add the pair (c,t) to the finite map f. If c \in dom f then f c is
     changed to t.

   updMap_simpl : updMap c t f c = Seom t

   updMap_simpl2 : c != c' -> updMap c t f c' = f c'

   indomUpdMap c (f:FinDom C T) c' t : c \in dom (updMap c' t f) = c == c' || c \in dom f

   remMap c (f:FinDom C T) : FinDom C T
     removes c from the domain of f.

   remMap_simpl c (f:FinDom C T) : remMap c f c = None

   remMap_simpl2 c c' (f:FinDom C T) : c != c' -> remMap c f c' = f c'

   indomRemMap c f t : c \in remMap t f = a != t && a \in dom f

   updMapCom f c t c' t' : c != c' -> updMap c t (updMap c' t' f) = updMap c' t' (updMap c t f)

   remUpdMap (f:FinDom C T) c c' t : c != c' -> remMap c (updMap c' t f) = updMap c' t (remMap c f)

   create_findom (C:compType) (T1:Type) (l:seq T0) (f:T0 -> option T1) : uniq l -> sorted l -> FinDom C T1
     takes a sorted list to a finite map.

   dom_create_findom gives you the domain of a create_findom.

   findom_map (m:FinDom T T') (f:forall x, x \in dom m -> T'') : FinDom T T''
     maps f over the domain of m.
     
   dom_findom_map ...
   
   post_comp (g:T -> option T') (f:FinDom C T) : FinDom C T'
     post composition of f with g.

   post_comp_simpl g (f:FinDom C T) c : post_comp g f c = option_bind g (f c)

   dom_post_comp g (f:FinDom C T) : dom (post_copm g f) = filter (fun x => isSome (option_bind g (f x))) (dom f)

*)

Require Export ssreflect ssrnat ssrbool seq eqtype.
Require Import ssrfun.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module Comparison.

Definition axiomAS (T:Type) l := forall x y : T, reflect (x = y) (l x y && l y x).
Definition axiomCL T (l:T -> T -> bool) (comp:T -> T -> unit + bool) :=
    forall x y, ((comp x y == inl _ tt) = l x y && l y x) /\ (comp x y == inr _ true) = l x y && negb (l y x) /\ 
                 (comp x y == inr _ false) = l y x && negb (l x y).
Definition axiomT T l := forall x y z  : T, l x y && l y z ==> l x z.

Record mixin_of (T:Type) : Type := 
  Mixin { leq : T -> T -> bool;
          comp : T -> T -> unit + bool;
          _ : axiomAS leq;
          _ : axiomT leq;
          _ : axiomCL leq comp
  }.

Notation class_of := mixin_of (only parsing).
Section ClassDef.
Structure type : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.

Definition eqop (T:type) (x y : T) := comp (class T) x y == inl _ tt.

Lemma eqP T : Equality.axiom (@eqop T).
case:T. move => T. case => l c A0 A1 A2 T'. unfold eqop. simpl.
move => x y. simpl. specialize (A0 x y). have A:=proj1 (A2 x y). simpl in A. rewrite <- A in A0. by apply A0.
Qed.

Lemma leq_refl (T:type) (x:T) : leq (class T) x x.
case:T x. move => T. case. move => l c AS Tr CL X. simpl. move => x. case_eq (l x x) => L; first by [].
specialize (AS x x). rewrite L in AS. simpl in AS. by case AS.
Qed.

Lemma leq_trans (T:type) (x y z:T) : leq (class T) x y -> leq (class T) y z -> leq (class T) x z.
case:T x y z => T. case. move => l c AS Tr CL X. simpl. move => x y z A B.
specialize (Tr x y z). rewrite -> A, -> B in Tr. rewrite implyTb in Tr. by apply Tr.
Qed.

Fixpoint sorted (T:type) (s:seq T) : bool :=
match s with
| nil => true
| x::s' => match s' with | nil => true | y::_ => leq (class T) x y && sorted s' end
end.

Lemma leq_seq_trans T x t s : leq (class T) x t -> all (leq (class T) t) s -> all (leq (class T) x) s.
elim:s ; first by [].
move => e s IH X. specialize (IH X). simpl. move => Y. rewrite (IH (proj2 (andP Y))). rewrite andbT.
apply (@leq_trans _ x t e). by rewrite X. by rewrite (proj1 (andP Y)).
Qed.

Lemma ltn_trans T x y t : leq (class T) x y -> leq (class T) t x -> ~~ eqop t x -> ~~ eqop t y.
move: T (@eqP T) x y t. case => T. simpl. case => l c AS Tr CL X E. simpl. unfold eqop in E. simpl in E.
move => x y t L L'. unfold eqop. simpl. case_eq (c t y) ; last by case.
case. move => e. have e':c t y == inl bool tt by rewrite e.
have ee:=E _ _ e'. rewrite <- ee in L. specialize (AS t x). rewrite L in AS. rewrite L' in AS. simpl in AS.
specialize (E t x). simpl in E. case: E ; first by [].
have a:= elimT AS. specialize (a is_true_true). by rewrite a.
Qed.

Lemma ltn_seq_trans T x t s : leq (class T) x t -> negb (eqop x t) -> all (leq (class T) t) s -> 
  all (leq (class T) x) s && all (fun y => negb (eqop x y)) s.
elim:s ; first by [].
move => e s IH L N A. simpl in A. simpl. specialize (IH L N (proj2 (andP A))).
rewrite (leq_trans (y:=t) L) ; last by rewrite -> (proj1 (andP A)). simpl.
rewrite (leq_seq_trans L (proj2 (andP A))). simpl. rewrite (proj2 (andP IH)).
by rewrite (ltn_trans (proj1 (andP A)) L N).
Qed.

Lemma sorted_cons (T:type) (s:seq T) (x:T) : sorted (x::s) = all (leq (class T) x) s && sorted s.
elim:s x ; first by [].
move => t s IH x. simpl @all.
apply trans_eq with (y:=leq (class T) x t && sorted (t::s)) ; first by []. rewrite (IH t). clear IH.
case_eq (leq (class T) x t) ; last by []. move => xt. simpl.
case_eq (all (leq (class T) t) s) ; last by simpl ; rewrite andbF.
move => ts. simpl. by rewrite (leq_seq_trans xt ts).
Qed.

Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
  let: Pack T c _ := cT return K _ (class cT) in k _ c.
Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT.
Definition pack T c := @Pack T c T.

Definition eqType cT := Equality.Pack (Equality.Mixin (@eqP cT)) cT.

Lemma comp_ne cT x y b : comp (class cT) x y = inr unit b -> negb (@eqop cT x y).
unfold eqop. move => e. by rewrite e.
Qed.

End ClassDef.
Module Import Exports.
Coercion eqType : type >-> Equality.type.
Coercion sort : type >-> Sortclass.
Notation compType := type.
Notation CompType := pack.
Notation CompMixin := Mixin.

Canonical Structure eqType.
Notation "[ 'compType' 'of' T 'for' cT ]" :=
    (@repack cT (@Pack T) T)
  (at level 0, format "[ 'compType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'compType' 'of' T ]" :=
    (repack (fun c => @Pack T c) T)
  (at level 0, format "[ 'compType'  'of'  T ]") : form_scope.
End Exports.
End Comparison.
Export Comparison.Exports.


Definition comparison (T:compType) (x y:T) := Comparison.comp (Comparison.class T) x y.
Definition leq (T:compType) (x y:T) := Comparison.leq (Comparison.class T) x y.
Definition sorted (T:compType) (s:seq T) := Comparison.sorted s.

Lemma leq_trans (T:compType) (x y z:T) : leq x y -> leq y z -> leq x z.
move => E. by apply (Comparison.leq_trans E).
Qed.

Lemma leq_refl (T:compType) (x:T) : leq x x.
by apply (Comparison.leq_refl).
Qed.

Lemma leq_seq_trans (T:compType) (x:T) t s : leq x t -> all (leq t) s -> all (leq x) s.
move => L A. by apply (Comparison.leq_seq_trans L A).
Qed.

Lemma ltn_trans (T:compType) (x y t:T) : leq x y -> leq t x -> t != x -> t != y.
move => L L' N. by apply (Comparison.ltn_trans L L' N).
Qed.

Lemma ltn_seq_trans (T:compType) (x t:T) s : leq x t -> x != t -> all (leq t) s -> 
  all (leq x) s && all (fun y => x != y) s.
move => L N A. by apply (Comparison.ltn_seq_trans L N A).
Qed.

Lemma sorted_cons (T:compType) (s:seq T) (x:T) : sorted (x::s) = all (leq x) s && sorted s.
by apply Comparison.sorted_cons.
Qed.

Lemma comp_eq (T:compType) (x y:T) : (comparison x y == inl bool tt) = (x == y).
case_eq (comparison x y == inl bool tt) => E.
apply sym_eq. by apply E.
case_eq (x == y) => E' ; last by [].
case: T x y E E'. move => T. case => l c A0 A1 A2 T'. simpl.
move => x y. have a:= (A0 x y). have A:=proj1 (A2 x y). move => F. simpl in A. rewrite F in A.
move => e. rewrite (eqP e) in A. by rewrite (introT (A0 y y) (refl_equal _)) in A.
Qed.

Lemma comp_leq (T:compType) (x y:T) : (comparison x y == inr unit true) = (leq x y && (x != y)).
case_eq (x == y) => E. have e:=comp_eq x y. rewrite E in e.
rewrite (eqP e). simpl. by rewrite andbF.

simpl. rewrite andbT. have e:(comparison x y != inl bool tt) by rewrite comp_eq ; rewrite E. clear E.
move: T x y e.
case => T. case => l c A0 A1 A2 T'. unfold comparison. unfold leq. simpl.
move => x y. have a:= (proj1 (proj2 (A2 x y))). simpl in a. rewrite a. clear a.
case_eq (l x y) => E ; last by []. simpl. case_eq (l y x) => L ; last by [].
specialize (A2 x y). rewrite E in A2. rewrite L in A2. simpl in A2. by rewrite (proj1 A2).
Qed.

Lemma comp_geq (T:compType) (x y:T) : (comparison x y == inr unit false) = (leq y x && (x != y)).
case_eq (x == y) => E. have e:=comp_eq x y. rewrite E in e.
rewrite (eqP e). simpl. by rewrite andbF.

simpl. rewrite andbT. have e:(comparison x y != inl bool tt) by rewrite comp_eq ; rewrite E. clear E.
move: T x y e.
case => T. case => l c A0 A1 A2 T'. unfold comparison. unfold leq. simpl.
move => x y. have a:= (proj2 (proj2 (A2 x y))). simpl in a. rewrite a. clear a.
case_eq (l y x) => E ; last by []. simpl. case_eq (l x y) => L ; last by [].
specialize (A2 x y). rewrite E in A2. rewrite L in A2. simpl in A2. by rewrite (proj1 A2).
Qed.

Lemma comp_neq (T:compType) (x y:T) b : comparison x y = inr _ b -> x != y.
move => E. by apply (Comparison.comp_ne E).
Qed.

Lemma comp_leqT (T:compType) (x y:T) : comparison x y = inr unit true -> leq x y.
case:T x y => T. case => l c AS Tr CL X. simpl. move => x y. have A:= (CL x y). unfold comparison. simpl. unfold leq. simpl.
move => E. rewrite E in A. simpl in A. have a:=proj1 (proj2 A). by case: (l x y) a.
Qed.

Lemma comp_leqF (T:compType) (x y:T) : comparison x y = inr unit false -> leq y x.
case:T x y => T. case => l c AS Tr CL X. simpl. move => x y. have A:= (CL x y). unfold comparison. simpl. unfold leq. simpl.
move => E. rewrite E in A. simpl in A. have a:=proj2 (proj2 A). by case: (l y x) a.
Qed.

Lemma leq_anti (T:compType) (x y : T) : leq x y -> leq y x -> x = y.
unfold leq. case: T x y. move => T. case. move => le comp A B C T'. simpl.
move => x y l l'. specialize (A x y). rewrite l in A. rewrite l' in A. simpl in A.
by inversion A.
Qed.

Fixpoint compare_nat (m n : nat) : unit + bool :=
match m,n with
| O,O => inl _ tt
| S m, O => inr _ false
| O, S n => inr _ true
| S m, S n => compare_nat m n
end.

Lemma comp_natAS : Comparison.axiomAS ssrnat.leq.
move => x y. apply: (iffP idP) ; last by move => X ; rewrite X ; rewrite leqnn.
move => L. by apply (anti_leq L).
Qed.

Lemma nat_leqT : Comparison.axiomT ssrnat.leq.
move => x y z. case_eq (x <= y <= z) ; last by rewrite implyFb.
move => E. rewrite implyTb. by apply (ssrnat.leq_trans (proj1 (andP E)) (proj2 (andP E))).
Qed.

Lemma comp_natCL : Comparison.axiomCL ssrnat.leq compare_nat.
move => x y. simpl. elim: x y ; first by case.
move => x IH. case ; first by []. move => y. simpl. specialize (IH y).
rewrite (proj1 IH). rewrite (proj1 (proj2 IH)). by rewrite (proj2 (proj2 IH)).
Qed.

Canonical Structure nat_compMixin := CompMixin (comp:=compare_nat) comp_natAS nat_leqT comp_natCL.
Canonical Structure nat_compType := Eval hnf in CompType nat_compMixin.

Lemma map_map T T' T'' (f:T -> T') (g:T' -> T'') l : map g (map f l) = map (fun x => g (f x)) l.
elim:l ; first by [].
move => e l IH. simpl. by rewrite IH.
Qed.

Section FinDom.
Variable T:compType.

Section Def.
Variable T':Type.

(*=FinDom *)
Record FinDom : Type := mk_findom 
{ findom_t : seq (T * T');
  findom_P : sorted (map (@fst T T') findom_t) &&
                     uniq (map (@fst T T') findom_t) }.
(*=End *)
Fixpoint findom_fun (f:seq (T * T')) (x:T) : option T' :=
match f with
| nil => None
| (x0,y) :: r => if x == x0 then Some y else findom_fun r x
end.

Definition findom_f f := findom_fun (findom_t f).

Definition dom f := map (@fst _ _) (findom_t f).
Definition codom f := map (@snd _ _) (findom_t f).

End Def.

Coercion findom_f : FinDom >-> Funclass.

Variable T' : Type.

Fixpoint updpair (x:T * T') (l:seq (T * T')) : seq (T * T') :=
match l with
| nil => [:: x]
| y::yr => match comparison (fst x) (fst y) with inl _ => x::yr | inr true => x::y::yr | inr false => y::updpair x yr end
end.

Lemma all_leq_upd x (s:seq (T * T')) t : all (leq t) (map (@fst _ _) s) -> leq t x.1 ->
   all (leq t) (map (@fst _ _) (updpair x s)).
elim:s t ; first simpl. move => t. by rewrite andbT.
case => t0 t0' s IH t. simpl. move => A L.
case: (comparison x.1 t0) (comp_eq x.1 t0) (comp_leq x.1 t0) (comp_geq x.1 t0) ; case ; rewrite eq_refl.
- move => B _ _. rewrite (eqP (sym_eq B)) in L. simpl. rewrite (proj2 (andP A)).
  rewrite <- (eqP (sym_eq B)) in L. by rewrite L.
- move => _ B _. simpl. rewrite L. simpl. by apply A.
- move => _ _ B. simpl. rewrite (proj1 (andP A)). simpl. apply IH ; first by apply (proj2 (andP A)).
  by apply L.
Qed.

Lemma notin_updpair x s t : t != x.1 -> t \notin map (@fst _ _) s -> t \notin map (@fst _ _) (updpair x s).
elim: s t. simpl. move => t e _. rewrite in_cons. by case: (t == x.1) e.
case => t t' s IH t0 e. simpl. rewrite in_cons.
case: (comparison x.1 t) (comp_eq x.1 t) (comp_leq x.1 t) (comp_geq x.1 t) ; case ; rewrite eq_refl.
- move => E. rewrite (eqP (sym_eq E)) in e. simpl. rewrite in_cons.
  by rewrite (eqP (sym_eq E)).
- move => _ A _. simpl. do 2 rewrite in_cons.
  case: (t0 == t) ; first by []. simpl. by case: (t0 == x.1) e.
- move=> _ _ A. simpl. rewrite in_cons. case: (t0 == t) ; first by [].
  simpl. move => X. by apply IH.
Qed.


Lemma findom_fun_notin T0 t s : t \notin map (@fst _ T0) s -> findom_fun s t = None.
elim: s ; first by [].
case => e2 e3 s IH. simpl. rewrite in_cons. rewrite negb_or. move => P.
specialize (IH (proj2 (andP P))). rewrite IH. rewrite <- if_neg. by rewrite (proj1 (andP P)).
Qed.

Lemma findom_upd (a:T') l s : findom_fun (updpair (l, a) s) l = Some a.
elim: s. simpl. by rewrite eq_refl.
- case => e0 e1 s IH. simpl. case_eq (comparison l e0) ; case => E.
  + simpl. by rewrite eq_refl.
  + simpl. by rewrite eq_refl.
  + simpl. have b:=comp_geq l e0. rewrite E in b. rewrite eq_refl in b. have c:=sym_eq b.
    have N:=proj2 (andP c). rewrite <- if_neg. rewrite N. by apply IH.
Qed.

Lemma findom_upd2 (a:T') x l s : x != l -> findom_fun (updpair (l, a) s) x = findom_fun s x.
move => P. elim: s. simpl. rewrite <- if_neg. by rewrite P.
case => e0 e1 s IH. simpl. case_eq (comparison l e0) ; case => E.
- have e:=comp_eq l e0. rewrite E in e. rewrite eq_refl in e.  simpl. rewrite <- (eqP (sym_eq e)).
  rewrite <- if_neg. rewrite P. rewrite <- if_neg. by rewrite P.
- simpl. rewrite <- if_neg. by rewrite P.
- simpl. case_eq (x == e0) ; first by []. move => E'. by apply IH.
Qed.

Lemma all_diff_notin (t:T) s : all (fun y : T => t != y) s = (t \notin s).
elim: s ; first by [].
move => t0 s IH. simpl. rewrite in_cons. rewrite negb_or. case_eq (t != t0) ; last by []. move => e. by apply IH.
Qed.

Lemma updpairP (x:T * T') f : sorted (T:=T) (map (@fst _ T') (updpair x (findom_t f))) &&
   uniq (map (@fst _ _) (updpair x (findom_t f))).
case: f. elim ; first by [].
case => t t' s IH. simpl @map. rewrite sorted_cons.
case: (comparison x.1 t) (comp_eq x.1 t) (comp_leq x.1 t) (comp_geq x.1 t) ; case ; rewrite eq_refl.
- move => A. simpl @map. rewrite sorted_cons. simpl. by rewrite (eqP (sym_eq A)).
- move => _ A _. simpl @map. do 2 rewrite sorted_cons. simpl. move => B.
  rewrite (proj2 (andP B)).  rewrite (proj1 (andP B)). rewrite (proj1 (andP (sym_eq A))). simpl.
  have C:=(ltn_seq_trans (proj1 (andP (sym_eq A))) (proj2 (andP (sym_eq A))) (proj1 (andP (proj1 (andP B))))).
  rewrite (proj1 (andP C)). rewrite -> all_diff_notin in C. rewrite in_cons.
  case: (x.1 == t) (proj2 (andP (sym_eq A))) ; first by []. simpl.
  by rewrite (proj2 (andP C)).
- move => _ _ A. simpl @map. rewrite sorted_cons. simpl. move => B.
  have Y:sorted (map (@fst _ _) s) && uniq (map (@fst _ _) s).
    rewrite (proj2 (andP (proj1 (andP B)))). by rewrite (proj2 (andP (proj2 (andP B)))).
  specialize (IH Y). simpl in IH. rewrite (proj1 (andP IH)). rewrite (proj2 (andP IH)).
  do 2 rewrite andbT. rewrite (all_leq_upd (proj1 (andP (proj1 (andP B)))) (proj1 (andP (sym_eq A)))).
  simpl. apply notin_updpair ; last by apply (proj1 (andP (proj2 (andP B)))).
  rewrite eq_sym. by apply (proj2 (andP (sym_eq A))).
Qed.

Definition updMap (t:T) (t':T') (f:FinDom T') : FinDom T' := mk_findom (@updpairP (t,t') f).

Lemma updMap_simpl t t' f : updMap t t' f t = Some t'.
case: f => s f. unfold findom_f. simpl. clear f. elim:s ; first by simpl ; rewrite eq_refl.
move => e s IH. simpl. case_eq (comparison t e.1) ; case.
  + move => eq. rewrite eq. simpl. by rewrite -> eq_refl.
  + move => eq ; rewrite eq. simpl. by rewrite eq_refl.
  + move => eq ; rewrite eq. simpl. case: e eq. move => e0 e1. rewrite IH. simpl. move => X. have a:=comp_geq t e0. rewrite X in a.
    rewrite eq_refl in a. have b:= sym_eq a. have f:=(proj2 (andP b)). case_eq (t == e0) => E ; first by rewrite E in f.
    by [].
Qed.

Lemma updMap_simpl2 t t0 t' f : t0 != t -> updMap t t' f t0 = f t0.
case:f => s f. unfold findom_f. simpl. clear f. move => ne. elim: s.
- simpl. case_eq (t0 == t) =>e ; last by []. by rewrite e in ne.
- move => e s IH. simpl. case_eq (comparison t e.1) ; case.
  + move => E. rewrite E. simpl. rewrite <- if_neg. rewrite ne. have te:=comp_eq t e.1. rewrite E in te. rewrite eq_refl in te.
    have te':=sym_eq te. rewrite (eqP te') in ne. clear E te te'. case: e ne. simpl. move => e0 e1 e. rewrite <- if_neg.
    by rewrite e.
  + move => eq ; rewrite eq. simpl. rewrite <- if_neg. by rewrite ne.
  + move => eq ; rewrite eq. simpl. by rewrite IH.
Qed.

Lemma NoneP : sorted (T:=T) (map (@fst T T') [::]) && uniq (map (@fst T T') [::]).
by [].
Qed.

Definition fdEmpty : FinDom T' := mk_findom NoneP.

Lemma findom_ind (f:FinDom T') (P:FinDom T' -> Prop) : P fdEmpty ->
   (forall f n x, all (leq n) (dom f) -> n \notin dom f -> P f -> P (updMap n x f)) -> P f.
move => E C. case: f. elim.
- simpl. move => X. unfold fdEmpty in E. rewrite -> (eq_irrelevance NoneP X) in E. by apply E.
- case => a b s. move => IH X.
  have X':=X. simpl @map in X'. rewrite sorted_cons in X'. simpl in X'.
  have Y:sorted (map (@fst _ _) s) && uniq (map (@fst _ _) s).
    rewrite -> (proj2 (andP (proj2 (andP X')))). by rewrite -> (proj2 (andP (proj1 (andP X')))).
  specialize (IH Y). specialize (C (mk_findom Y) a b).
  have d:a \notin dom (mk_findom Y). unfold dom. simpl. simpl in X. by apply (proj1 (andP (proj2 (andP X)))).
  specialize (C (proj1 (andP (proj1 (andP X')))) d IH).
  have e:(updMap a b (mk_findom Y)) = (mk_findom X). simpl @map in X.
  unfold updMap. have A:= (updpairP (a, b) (mk_findom Y)).
  rewrite (eq_irrelevance (updpairP (a, b) (mk_findom Y)) A).
  simpl in A.
  have ee:(updpair (a, b) s) = (a,b)::s. clear Y C IH X d. case: s X' A ; first by [].
    case => a0 b0 s. simpl. move => A B. have L:= comp_leq a a0.
    rewrite (proj1 (andP (proj1 (andP (proj1 (andP A)))))) in L. simpl in L.
    have ee:=(proj1 (andP (proj2 (andP A)))). rewrite in_cons in ee. 
    have x:(a != a0). by case: (a == a0) ee. rewrite x in L. clear ee x. by rewrite (eqP L).
  move: A. rewrite ee. simpl @map. move => A. by rewrite (eq_irrelevance X A).
  rewrite <- e. by apply C.
Qed.

Lemma dom_fdEmpty : dom fdEmpty = [::].
by [].
Qed.

Lemma dom_empty_eq f : dom f = [::] -> f = fdEmpty.
unfold dom. case: f. simpl. case ; last by [].
simpl. move => X _. by rewrite (eq_irrelevance X NoneP).
Qed.

Fixpoint rempair (x:T) (l:seq (T * T')) : seq (T * T') :=
match l with
| nil => [::]
| y::yr => match comparison x (fst y) with inl _ => yr | inr true => y::yr | inr false => y::rempair x yr end
end.

Lemma remMapP t f : sorted (T:=T) (map (@fst _ _) (rempair t (findom_t f))) &&
   uniq (map (@fst _ _) (rempair t (findom_t f))).
case: f => s P. simpl. elim: s P ; first by [].
case. move => t0 t0' s IH P. simpl.
case_eq (comparison t t0) ; case.
- move => C. simpl @map in P. rewrite sorted_cons in P. rewrite (proj2 (andP (proj1 (andP P)))). simpl.
  simpl in P. by rewrite (proj2 (andP (proj2 (andP P)))).
- by [].
- move => C. simpl @map. simpl @map in P. rewrite sorted_cons in P. simpl in P.
  rewrite (proj2 (andP (proj1 (andP P)))) in IH. rewrite (proj2 (andP (proj2 (andP P)))) in IH.
  specialize (IH is_true_true). rewrite sorted_cons. rewrite (proj1 (andP IH)). simpl. rewrite (proj2 (andP IH)).
  do 2 rewrite andbT. clear IH.
  have a:=(proj1 (andP (proj1 (andP P)))). have b:=(proj1 (andP (proj2 (andP P)))). clear C P.
  elim: s a b ; first by []. case => e0 e1 s IH P Q. simpl. simpl in P. simpl in Q.
  case_eq (comparison t e0) ; case.
  + rewrite in_cons in Q. rewrite negb_or in Q. rewrite (proj2 (andP Q)). by rewrite (proj2 (andP P)).
  + simpl. rewrite Q. by rewrite P.
  + simpl. specialize (IH (proj2 (andP P))). rewrite in_cons in Q. rewrite negb_or in Q. specialize (IH (proj2 (andP Q))).
    rewrite in_cons. rewrite negb_or. rewrite (proj1 (andP IH)). rewrite (proj2 (andP IH)).
    rewrite (proj1 (andP Q)). by rewrite (proj1 (andP P)).
Qed.

Definition remMap (t:T) (f:FinDom T') : FinDom T' := mk_findom (@remMapP t f).

Lemma updpair_least n x s : all (leq n) (map (@fst _ _) s) -> n \notin (map (@fst _ _) s) ->
         (updpair (n, x) s) = (n,x)::s.
case:s ; first by [].
case => t t' s X Y. simpl. simpl in X. simpl in Y. rewrite in_cons in Y.
case: (comparison n t) (comp_eq n t) (comp_leq n t) (comp_geq n t) ; case ; rewrite eq_refl.
- move => A _ _. by rewrite (sym_eq A) in Y.
- by [].
- move => _ _ A. have e:=leq_anti (proj1 (andP X)) (proj1 (andP (sym_eq A))). rewrite e in A.
  rewrite eq_refl in A. by rewrite andbF in A.
Qed.

Lemma seq_ext_nil (g:seq T) : [::] =i g -> g = [::].
case: g ; first by [].
move => s r X. specialize (X s). rewrite in_nil in X. rewrite in_cons in X. by rewrite eq_refl in X.
Qed.

Lemma findom_ext (f g:FinDom T') : dom f =i dom g -> (forall x, x \in dom g -> f x = g x) -> g = f.
case: f g. unfold findom_f. unfold dom. simpl. move => f Pf. case. simpl. move => g Pg D C.
have e:f = g. elim: f g Pf Pg C D. simpl. move => g _ e X a. move: (seq_ext_nil a). clear. by case: g.
case => c e f IH. case. simpl. move => _ _ _ F. specialize (F c). rewrite in_nil in F.
  by rewrite in_cons in F ; simpl in F ; rewrite eq_refl in F.
case => c' e' g. simpl @map. do 2 rewrite sorted_cons.
move => A B C X.
have Y:= X c. have XX:=X. specialize (X c'). do 2 rewrite in_cons in X. do 2 rewrite in_cons in Y.
rewrite (eq_sym c' c) in X. rewrite eq_refl in X. rewrite eq_refl in Y. simpl in X. simpl in Y.
have F:c != c' -> False. simpl in A,B.
  have Z:c != c' -> c = c'.
  case: (c == c') X Y ; first by []. simpl. move => X Y _.
  have l:= allP (proj1 (andP (proj1 (andP A)))) _ X.
  have l':= allP (proj1 (andP (proj1 (andP B)))) _ (sym_eq Y).
  by apply (leq_anti l l'). move => F. specialize (Z F). rewrite Z in F. by rewrite eq_refl in F.
have e0:(c == c') ; case: (c == c') F ; first by []. move => Z. by case (Z is_true_true).
move => _. rewrite <- (eqP e0).
have C':=C c. rewrite in_cons in C'. rewrite e0 in C'. specialize (C' is_true_true).
simpl in C'. rewrite eq_refl in C'. rewrite e0 in C'. case: C' => C'. rewrite <- C'. f_equal.
apply IH. simpl in A. rewrite (proj2 (andP (proj2 (andP A)))). by rewrite (proj2 (andP (proj1 (andP A)))).
simpl in B. rewrite (proj2 (andP (proj2 (andP B)))). by rewrite (proj2 (andP (proj1 (andP B)))).
move => x ix.
specialize (C x). rewrite in_cons in C. rewrite ix in C. rewrite orbT in C. specialize (C is_true_true).
simpl in C. simpl in B. have F:x == c -> False. move => F. rewrite (eqP F) in ix. rewrite (eqP e0) in ix.
  rewrite ix in B. by rewrite andbF in B.
rewrite <- (eqP e0) in C. case: (x == c) F C ; last by [].
move => F. by case: (F is_true_true).
move => a. specialize (XX a). rewrite <- (eqP e0) in XX.
do 2 rewrite in_cons in XX. rewrite <- (eqP e0) in B. simpl in A. simpl in B.
case_eq (a == c) => aa. rewrite (eqP aa). move: (proj1 (andP (proj2 (andP A)))).
move: (proj1 (andP (proj2 (andP B)))). case: (c \in map (@fst _ _) f) ; first by [].
case: (c \in map (@fst _ _) g) ; by [].
rewrite aa in XX. simpl in XX. by apply XX.
move => F. case: (F is_true_true).

move: C D Pg Pf. rewrite e. clear f e. move => C D Pg Pf. by rewrite (eq_irrelevance Pg Pf).
Qed.

Lemma in_filter (Te:eqType) P l (x:Te) : x \in filter P l = (x \in l) && P x.
elim:l x ; first by [].
move => t s IH x. simpl. rewrite in_cons. have e:x == t -> P t = P x. move => E. by rewrite (eqP E).
case: (P t) e.
- rewrite in_cons. case: (x == t) ; last move => F. simpl. move => X. by apply (X is_true_true).
  simpl. by apply IH.
- case: (x == t) ; simpl. move => X. specialize (X is_true_true). specialize (IH x). rewrite <- X in IH.
  rewrite andbF in IH. rewrite IH. by rewrite <- X.
  move => A. by apply IH.
Qed.

Lemma indomEmpty i : (i \in dom fdEmpty) = false.
by [].
Qed.

Lemma indomUpdMap i f x y : i \in dom (updMap x y f) = (i == x) || (i \in dom f).
move: x y. apply (findom_ind f).
- move => x y. rewrite indomEmpty. rewrite orbF. unfold updMap. unfold fdEmpty. unfold dom. simpl. rewrite in_cons.
  rewrite in_nil. by rewrite orbF.
- clear f. move => f n x A I IH x' y'. unfold dom. simpl. rewrite (updpair_least _ A).
  simpl. rewrite in_cons. case: (comparison x' n) (comp_eq x' n) (comp_leq x' n) (comp_geq x' n) ; case ; rewrite eq_refl.
  + move => B _ _. simpl. rewrite in_cons. rewrite (eqP (sym_eq B)). clear x' B y'.
    by case: (i == n).
  + move => _ B _. simpl. rewrite in_cons. by rewrite in_cons.
  + move => _ _ B. simpl. rewrite in_cons.  specialize (IH x' y'). unfold dom in IH. simpl in IH. rewrite IH.
    case: (i == n) ; simpl. by rewrite orbT.
  + by [].
by apply I.
Qed.
  
Lemma updMapCom f x y x' y' : x != x' -> updMap x y (updMap x' y' f) = updMap x' y' (updMap x y f).
move => e. apply findom_ext.
- move => a. do 4 rewrite indomUpdMap.
  case: (a == x') ; simpl ; first by rewrite orbT. by [].
- move => n I. do 2 rewrite indomUpdMap in I.
  case_eq (n == x') => F.
  + rewrite (eqP F). rewrite updMap_simpl. rewrite eq_sym in e.
    rewrite (updMap_simpl2 y _ e). by rewrite updMap_simpl.
  + have ee:n != x' by case: (n == x') F. clear F.
    rewrite (updMap_simpl2 y' _ ee). case_eq (x == n).
    * move => e0. rewrite (eqP e0). by do 2 rewrite updMap_simpl. 
    * move => e0. have e1:x != n by case: (x == n) e0.
      clear e0. rewrite eq_sym in e1. do 2 rewrite (updMap_simpl2 y _ e1).
      by rewrite (updMap_simpl2 y' _ ee).
Qed.

Lemma indomRemMap a f t : (a \in dom (remMap t f)) = (a != t) && (a \in dom f).
move: t ; apply (findom_ind f) ; clear f.
- move => t. rewrite indomEmpty. by rewrite andbF.
- move => f n x A I IH t.
  rewrite indomUpdMap. unfold dom. simpl. rewrite (updpair_least _ A) ; last by apply I.
  simpl. case: (comparison t n) (comp_eq t n) (comp_leq t n) (comp_geq t n) ; case ; rewrite eq_refl.
  + move => B _ _. rewrite (eqP (sym_eq B)). clear t B.
    case_eq (a == n) ; last by []. simpl. move => e. rewrite <- (eqP e) in I. unfold dom in I.
    by case: (a \in map (@fst _ _) (findom_t f)) I.
  + move => _ B _. simpl. rewrite in_cons.
    case_eq (a == n) => e. simpl. rewrite eq_sym. rewrite (eqP e). by rewrite (proj2 (andP (sym_eq B))).
    simpl. case_eq (a == t) ; last by [].
    move => e'. rewrite (eqP e'). rewrite -> (eqP e') in IH, e. clear e' a.
    rewrite e in B. simpl in B. rewrite andbT in B. have aa:=ltn_seq_trans (sym_eq B) _ A.
    rewrite e in aa. simpl in aa. specialize (aa is_true_true).
    have bb:=proj2 (andP aa). rewrite all_diff_notin in bb. simpl. unfold dom in bb.
    by case: (t \in map (@fst _ _) (findom_t f)) bb.
  + move => _ _ B. simpl. rewrite in_cons. rewrite IH. case_eq (a == n) ; simpl ; last by [].
    move => e. rewrite (eqP e). rewrite eq_sym. by rewrite (proj2 (andP (sym_eq B))).
Qed.

Lemma remMap_simpl t (f:FinDom T') : remMap t f t = None.
case: f => s P. unfold findom_f. simpl.
elim: s P ; first by [].
case => e0 e1 s IH. simpl @map. rewrite sorted_cons. move => P. simpl.
case_eq (comparison t e0) ;case.
- have Q:=proj1 (andP (proj2 (andP P))). clear IH P. move => C. have a:=comp_eq t e0. rewrite C in a. rewrite eq_refl in a.
  have b:=sym_eq a. rewrite <- (eqP b) in Q. clear a b C. by rewrite (findom_fun_notin Q).
- simpl. move => C. have a:=comp_leq t e0. rewrite C in a. rewrite eq_refl in a. have b:=sym_eq a.
  rewrite <- if_neg. rewrite (proj2 (andP b)).
  have c:=ltn_seq_trans (proj1 (andP b)) (proj2 (andP b)) (proj1 (andP (proj1 (andP P)))).
  rewrite ((all_diff_notin _ _)) in c. by rewrite (findom_fun_notin (proj2 (andP c))).
- move => C. simpl in P.  rewrite (proj2 (andP (proj1 (andP P)))) in IH. rewrite (proj2 (andP (proj2 (andP P)))) in IH.
  simpl. rewrite IH ; last by []. rewrite <- if_neg. have a:=comp_geq t e0. rewrite C in a. rewrite eq_refl in a.
  have b:=sym_eq a. by rewrite (proj2 (andP b)).
Qed.

Lemma remMap_simpl2 t t' (f:FinDom T') : t' != t -> remMap t f t' = f t'.
case:f => s P. unfold findom_f. simpl. move => E.
elim: s P ; first by [].
case => e0 e1 s IH. simpl @map. rewrite sorted_cons. move => P. simpl.
case_eq (comparison t e0) ;case.
- have Q:=proj1 (andP (proj2 (andP P))). clear IH P. move => C. have a:=comp_eq t e0. rewrite C in a. rewrite eq_refl in a.
  have b:=sym_eq a. rewrite <- (eqP b) in Q. rewrite <- (eqP b). rewrite <- if_neg. by rewrite E.
- by [].
- move => C. simpl in P. simpl. rewrite (proj2 (andP (proj1 (andP P)))) in IH. rewrite (proj2 (andP (proj2 (andP P)))) in IH.
  simpl. by rewrite IH.
Qed.

Lemma remUpdMap f n t x : t != n -> remMap t (updMap n x f) = updMap n x (remMap t f).
move => e. apply findom_ext.
- move => a. rewrite indomUpdMap. do 2 rewrite indomRemMap. rewrite indomUpdMap.
  case_eq (a == n) => ee ; last by []. simpl. rewrite <- (eqP ee) in e. rewrite eq_sym. by rewrite e.
- move => a X. rewrite indomRemMap in X. rewrite indomUpdMap in X.
  case_eq (a == n) => ee. rewrite (eqP ee). rewrite updMap_simpl. rewrite (eqP ee) in X.
  rewrite (remMap_simpl2 _ (proj1 (andP X))). by rewrite updMap_simpl.
  have en:a != n by case: (a == n) ee. clear ee.
  rewrite (updMap_simpl2 _ _ en). do 2 rewrite (remMap_simpl2 _ (proj1 (andP X))).
  by rewrite (updMap_simpl2 _ _ en).
Qed.

Section Eq.
Variable Teq : eqType.
Definition findom_eq (f f':FinDom Teq) : bool := findom_t f == findom_t f'.

Lemma findom_eqP : Equality.axiom findom_eq.
move => f f'. apply: (iffP idP) ; last by move => e ; rewrite e ; apply eq_refl.
unfold findom_eq. case: f. move => l s. case: f'. simpl. move => l' s'.
move => X. move: s. rewrite (eqP X). clear. move => s. by rewrite (eq_irrelevance s s').
Qed.

Definition findom_leq (f f':FinDom Teq) : bool := all (fun x => f x == f' x) (dom f).

Lemma findom_leq_refl (f:FinDom Teq) : findom_leq f f.
case: f. unfold findom_leq. unfold dom. unfold findom_f. simpl. move => s P.
by apply (introT (@allP T _ (map (@fst _ _) s))).
Qed.

End Eq.

Lemma map_pmap X Y (f:X -> Y) Z (g:Z -> option X) s : map f (pmap g s) = pmap (fun x => option_map f (g x)) s.
elim: s ; first by [].
move => t s IH. simpl. case_eq (g t). move => gt e. simpl. by rewrite IH. simpl. by rewrite IH.
Qed.

Lemma all_map_filter X Y (f:X -> Y) p g l : all p (map f l) -> all p (map f (filter g l)).
elim: l ; first by []. move => t s IH P.
simpl. simpl in P. specialize (IH (proj2 (andP P))). case_eq (g t) ; last by [].
move => e. simpl. rewrite IH. by rewrite (proj1 (andP P)).
Qed.

Lemma sorted_map_filter X (f:X -> T) g l : sorted (map f l) -> sorted (T:=T) (map f (filter g l)).
elim: l ; first by []. move => t s IH. simpl @map. rewrite sorted_cons. move => P.
specialize (IH (proj2 (andP P))). 
case (g t) ; last by []. simpl @map ; rewrite sorted_cons. rewrite IH. by rewrite (all_map_filter _ (proj1 (andP P))).
Qed.

Lemma notin_map_filter X (Y:eqType) (f:X -> Y) p s x :x \notin map f s -> (x \notin map f (filter p s)).
elim: s ; first by [].
move => t s IH. simpl. rewrite in_cons. rewrite negb_or. move => P. specialize (IH (proj2 (andP P))).
case (p t) ; last by []. simpl. rewrite in_cons ; rewrite negb_or. rewrite IH. by rewrite (proj1 (andP P)).
Qed.

Lemma uniq_map_filter X (Y:eqType) (f:X -> Y) p l : uniq (map f l) -> uniq (map f (filter p l)).
elim: l ; first by []. move => t s IH. simpl. move => P. specialize (IH (proj2 (andP P))).
case (p t) ; last by []. simpl. rewrite IH. by rewrite (notin_map_filter _ (proj1 (andP P))).
Qed.

Lemma post_compP T0 (g : T' -> option T0) (f:FinDom T') : sorted (T:=T)
     (map (@fst _ _) (pmap (fun p : T * T' => option_map (fun r => (p.1,r)) (g p.2)) (findom_t f))) &&
   uniq (map (@fst _ _) (pmap (fun p : T * T' => option_map (fun r => (p.1,r)) (g p.2)) (findom_t f))).
case: f. simpl. move => l. rewrite map_pmap.
have e:pmap (fun x => option_map (@fst _ _) (option_map [eta pair x.1] (g x.2))) l = (map (@fst _ T') (filter (fun p => g p.2) l)). elim: l ; first by []. case => e0 e1 s IH. simpl. case (g e1) ; simpl ; by rewrite IH.
rewrite e. clear e. move => P. rewrite (sorted_map_filter _ (proj1 (andP P))). simpl.
by rewrite (uniq_map_filter _ (proj2 (andP P))).
Qed.

Definition post_comp T0 (g : T' -> option T0) (f:FinDom T') : FinDom T0 := mk_findom (post_compP g f).

Definition option_bind Y Z (g:Y -> option Z) (y:option Y) : option Z :=
match y with | None => None | Some fx => g fx end.

Lemma in_pmap (A B : eqType) (f:A -> option B) x s y : Some x = f y -> y \in s -> x \in pmap f s.
elim: s y. simpl. move => y. by do 2 rewrite in_nil.
move => a s IH y. simpl. rewrite in_cons.
move => E. specialize (IH _ E). case_eq (y == a) => e. rewrite (eqP e) in E. rewrite <- E. simpl. rewrite in_cons.
by rewrite eq_refl.
simpl. move => X. specialize (IH X). case: (f a) ; simpl ; last by [].
move => aa. rewrite in_cons. rewrite IH. by rewrite orbT.
Qed.

Lemma notin_pmap (A B : eqType) (f:A -> option B) x s : (forall y, Some x = f y -> y \notin s) -> x \notin pmap f s.
elim: s. simpl. by [].
move => t s IH C. simpl.  case_eq (f t) => e ; simpl.
have C':=C.
specialize (C t). move => ee. rewrite ee in C. rewrite in_cons. case_eq (x == e) => aa.
rewrite (eqP aa) in C. specialize (C (refl_equal _)). rewrite in_cons in C. rewrite eq_refl in C. by [].
simpl. apply IH. move => y X. specialize (C' _ X). rewrite in_cons in C'. by case: (y == t) C'.
apply IH. move => y E. specialize (C y E). rewrite in_cons in C. by case: (y == t) C.
Qed.

Lemma post_comp_simpl T0 (g : T' -> option T0) (f:FinDom T') t : post_comp g f t = option_bind g (f t).
apply (findom_ind f) ; clear f ; first by [].
move => f n x A I X. unfold post_comp. unfold findom_f. simpl. rewrite (updpair_least _ A I). simpl.
case_eq (t == n) => e. rewrite (eqP e). rewrite (eqP e) in X. clear e t. simpl. case: (g x). simpl. by rewrite eq_refl. 
simpl. rewrite findom_fun_notin ; first by [].  rewrite map_pmap.
have ll:forall s, n \notin (map (@fst _ _) s) -> n \notin pmap (fun x0 : T * T' => option_map (@fst _ _) (option_map [eta pair x0.1] (g x0.2))) s.
elim ; first by [].
case => t0 t1 s IH. simpl. rewrite in_cons. case (g t1). simpl. rewrite in_cons. by case: (n == t0).
simpl. move => aa. apply IH. by case: (n == t0) aa.
rewrite ll ; first by []. clear ll. by apply I.
case_eq (f t) => ft. move => ee. unfold findom_f in ee. rewrite ee. simpl.
case: (g x). simpl. rewrite e.  move => _. unfold findom_f in X. rewrite ee in X. simpl in X.
by rewrite <- X.
simpl. unfold findom_f in X. rewrite ee in X. simpl in X. by rewrite <- X.
unfold findom_f in ft. rewrite ft. simpl. case: (g x) ; simpl. rewrite e.
move => _. unfold findom_f in X. rewrite ft in X. simpl in X. by apply X.
unfold findom_f in X. rewrite ft in X. by apply X.
Qed.

Lemma dom_post_comp T0 (g : T' -> option T0) (f:FinDom T') : dom (post_comp g f) =
  filter (fun x => isSome (option_bind g (f x))) (dom f).
case: f. unfold findom_f. unfold dom. simpl. move => s Ps. have U:=proj2 (andP Ps). clear Ps.
elim: s U ; first by [].
case => c e f. simpl. move => IH. rewrite eq_refl. simpl. case_eq (g e).
- move => ge E. simpl. move => X.
  rewrite IH ; last by rewrite (proj2 (andP X)). f_equal. apply: eq_in_filter => x I.
  case_eq (x == c) => E' ; last by []. by rewrite (eqP E') in I ; rewrite I in X.
- move => E. simpl. move => X.
  rewrite IH ; last by rewrite (proj2 (andP X)). apply: eq_in_filter => x I.
  case_eq (x == c) => E' ; last by []. by rewrite (eqP E') in I ; rewrite I in X.
Qed.

Lemma findom_undef (f:FinDom T') x (P:x \notin dom f) : f x = None.
case:f x P => s P x C. unfold dom in C. simpl in C. by apply findom_fun_notin.
Qed.

Lemma findom_indom (f:FinDom T') t : (t \in dom f) = isSome (f t).
case: f. unfold dom. unfold findom_f. simpl. move => s P.
elim: s P ; first by [].
case => t0 t0' s IH P. simpl. rewrite in_cons. case_eq (t == t0) => E ; first by [].
- simpl. apply IH. simpl @map in P. rewrite sorted_cons in P. simpl in P.
  rewrite (proj2 (andP (proj1 (andP P)))). by rewrite (proj2 (andP (proj2 (andP P)))).
Qed.

Lemma filter_some T0 (s:seq T0) : filter some s = s.
elim: s ; first by [].
move => t s IH. simpl. by rewrite IH.
Qed.

Lemma dom_post_compS T0 (g : T' -> T0) (f:FinDom T') : dom (post_comp (fun x => Some (g x)) f) = dom f.
rewrite dom_post_comp. apply trans_eq with (y:=filter [eta some] (dom f)) ; last by rewrite filter_some.
apply: eq_in_filter => x I. rewrite findom_indom in I. by case: (f x) I.
Qed.

End FinDom.

Canonical Structure findom_eqMixin T T' := EqMixin (@findom_eqP T T').
Canonical Structure findom_eqType T T' := Eval hnf in EqType _ (findom_eqMixin T T').

Lemma leq_upd T (T':eqType) (f:FinDom T T') l a : l \notin (dom f) -> findom_leq f (updMap l a f).
apply (findom_ind f) ; first by [].
clear f. move => f n x A I C. rewrite indomUpdMap. case_eq (l == n) ; first by [].
move => e. simpl. move => I'. specialize (C I'). rewrite updMapCom ; last by rewrite e.
unfold findom_leq. apply (introT (@allP T _ _)). move => b. rewrite indomUpdMap.
case_eq (b == n) => ee ; simpl.
- move => _. rewrite (eqP ee). by do 2 rewrite updMap_simpl.
- move => d. have N:(b != n) by case: (b == n) ee. do 2 rewrite (updMap_simpl2 _ _ N).
  have NN:(l != n) by case: (l == n) e. have F:(b == l) -> False. move => ex. rewrite (eqP ex) in d. by rewrite d in I'.
  have FF:(b != l). case: (b == l) F ; last by []. move => X. by case: (X is_true_true).
  by rewrite (updMap_simpl2 _ _ FF).
Qed.

Lemma create_findomP (T:compType) (T':Type) (l:seq T) (f:T -> option T') : (uniq l) -> (sorted l) ->
   sorted (map (@fst _ _) (pmap (fun x : T => option_map [eta pair x] (f x)) l)) &&
   uniq (map (@fst _ _) (pmap (fun x : T => option_map [eta pair x] (f x)) l)).
move => U S.
have A:= (@pmap_uniq T _ _ id _ l U). rewrite map_pmap. rewrite -> A ; last by move => x ; simpl ; case (f x).
rewrite andbT. clear A. clear U.
elim: l S ; first by [].
move => t s IH S. rewrite sorted_cons in S. specialize (IH (proj2 (andP S))).
simpl. case (f t) ; last by apply IH.
move => t'. simpl @oapp. rewrite sorted_cons. rewrite IH. rewrite andbT. clear IH t'.
elim: s S ;first by []. move => x s IH A. rewrite sorted_cons in A. simpl in A.
rewrite (proj2 (andP (proj1 (andP A)))) in IH. rewrite (proj2 (andP (proj2 (andP A)))) in IH. specialize (IH is_true_true).
simpl. case (f x) ; last by apply IH. move => y. simpl. rewrite (proj1 (andP (proj1 (andP A)))). simpl.
by apply IH.
Qed.

Definition create_findom (T:compType) (T':Type) (l:seq T) (f:T -> option T') (U:uniq l) (S:sorted l) : FinDom T T' :=
    mk_findom (create_findomP f U S).

Lemma create_findom_simpl (T:compType) (T':Type) (l:seq T) (f:T -> option T') (U:uniq l) (S:sorted l) :
  findom_t (create_findom f U S) = (pmap (fun x => option_map (fun y => (x,y)) (f x)) l).
by [].
Qed.

Definition create_findomF (T:compType) (X T':Type) (l:FinDom T X) (f:T -> option T') : FinDom T T'.
case:l f => l Pl f. by apply (create_findom f (proj2 (andP Pl)) (proj1 (andP Pl))).
Defined.

Lemma dom_create_findom (T:compType) T' (f:T -> option T') x U S :
   dom (@create_findom _ _ x f U S) = filter [eta f] x.
unfold dom.
rewrite create_findom_simpl.
rewrite pmap_filter. apply eq_filter => a. by case (f a).
move => a. simpl. by case (f a).
Qed.

Lemma dom_create_findomF (T:compType) T' T'' (f:T -> option T') (x:FinDom T T'') :
   dom (create_findomF x f) = filter [eta f] (dom x).
case: x. simpl. move => x P. by rewrite dom_create_findom.
Qed.

Lemma create_findomF_simpl (T:compType) T' T'' (f:T -> option T') (x:FinDom T T'') i :
   create_findomF x f i = if i \in dom x then f i else None.
unfold findom_f. case: x => x P. simpl. unfold dom. simpl.
elim: x P ; first by [].
case => j x s IH. simpl @map. rewrite sorted_cons. simpl. move => P.
rewrite (proj2 (andP (proj1 (andP P)))) in IH. rewrite (proj2 (andP (proj2 (andP P)))) in IH. specialize (IH is_true_true).
case_eq (f j).
- move => t fj. simpl. rewrite in_cons. case_eq (i == j) => IJ ; first by rewrite <- (eqP IJ) in fj ; rewrite fj.
  simpl. by apply IH.
- move => fj. simpl. rewrite in_cons. rewrite IH. case_eq (i == j) => E ; last by [].
  simpl. rewrite <- (eqP E) in fj. rewrite fj. simpl. case_eq (i \in map (@fst _ _) s) => X ; by rewrite X.
Qed.


Section FinMap.

Variable T:compType.

Lemma Pemp T' (x:T) (P:x \in map (@fst _ T') nil) : False.
by [].
Qed.

Fixpoint indom_app_fi T' (s:seq (T * T')) x (P:x \in map (@fst _ _) s) :=
match s as s0 return x \in map (@fst _ _) s0 -> T' with 
| nil => fun F => match Pemp F with end
| (a,b)::r => fun P => (match (x == a) as b return b || (x \in map (@fst _ _) r) -> T'
                        with true => fun _ => b
                           | false => fun P => @indom_app_fi _ r x P end) P
end P.

Definition indom_app T' (f:FinDom T T') x (P:x \in dom f) : T' := @indom_app_fi T' (findom_t f) x P.

Lemma indom_app_eq T' (f:FinDom T T') x (P:x \in dom f) : Some (indom_app P) = f x.
case: f x P . move => s P x I. elim: s P I ; first by [].
case => a b s IH. simpl @map. simpl @uniq. unfold dom. simpl @map. move => P. unfold in_mem. simpl.
move => I. have X:= proj1 (andP P). rewrite sorted_cons in X.
have Y:sorted (map (@fst _ _) s) && uniq (map (@fst _ _) s). rewrite (proj2 (andP X)). simpl.
  by rewrite (proj2 (andP (proj2 (andP P)))).
specialize (IH Y). unfold dom in IH. simpl in IH.
case_eq (x == a) => A.
- move: I. unfold findom_f. simpl. move: A. clear. move => A. unfold indom_app. simpl. by rewrite A.
- unfold findom_f. unfold indom_app. move: I. simpl. rewrite A. simpl. move => I. specialize (IH I).
  unfold indom_app in IH. simpl in IH. by rewrite IH.
Qed.

Lemma mem_cons x y (s:seq T) : x \in s -> x \in (y::s).
move => I. rewrite in_cons. rewrite I. by rewrite orbT.
Qed.

Fixpoint indom_app_map T' P' (f:forall x, P' x -> T') (s:seq T) (I:forall x, x \in s -> P' x) : seq (T * T') :=
match s as s0 return (forall x, x \in s0 -> P' x) -> seq (T * T') with 
| nil => fun _ => nil
| cons x rs => fun P => (x,f x (P x (mem_head x rs))) :: (@indom_app_map _ P' f rs (fun y X => P _ (mem_cons x X)))
end I.

Lemma list_fst_map T' P' (f:forall x, P' x -> T') (s:seq T) (I:forall x, x \in s -> P' x) :
  map (@fst _ _) (indom_app_map f I) = s.
elim: s I ; first by [].
move=> t s IH I. simpl. specialize (IH (fun (y : T) (X : y \in s) => I y (mem_cons t X))).
f_equal. by apply IH.
Qed.

Definition findom_map T' T'' (m:FinDom T T') (f:forall x, x \in dom m -> T'') : FinDom T T''.
exists (@indom_app_map T'' (fun x => x \in dom m) f (dom m) (fun x X => X)).
case: m f => s P f. rewrite list_fst_map. unfold dom. by apply P.
Defined.

Lemma dom_findom_map T' T'' (m:FinDom T T') (f:forall x, x \in dom m -> T'') : dom m = dom (findom_map f).
have A:=list_fst_map f (fun x => id). by rewrite <- A.
Qed.

Lemma findom_fun_map T' P (f:forall x, P x -> T') (s:seq T) (I:forall x, x \in s -> P x) x (I':x \in s) :
   findom_fun (@indom_app_map _ P f s I) x = Some (f x (I _ I')).
elim:s I x I' ; first by [].
move => t s IH I x I'. simpl. case_eq (x == t) => E. move: I'. rewrite (eqP E). move => I'.
 by rewrite (eq_irrelevance (mem_head t s) I').
specialize (IH (fun (y : T) (X : y \in s) => I y (mem_cons t X))). specialize (IH x).
have I0:= I'. rewrite in_cons in I0. rewrite E in I0. simpl in I0. specialize (IH I0). rewrite IH.
by rewrite (eq_irrelevance (mem_cons t I0) I').
Qed.

Lemma findom_map_app T' T'' (m:FinDom T T') x (I:x \in dom m) (f:forall x, x \in dom m -> T'') :
   findom_map f x = Some (f x I).
case: m x I f. move => s P. unfold findom_f. simpl. unfold dom. simpl.
move => x I f. apply (findom_fun_map f (fun x => id) I).
Qed.

End FinMap.

