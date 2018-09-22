(*==========================================================================
  Definition of products and associated lemmas
  ==========================================================================*)
Require Import PredomCore.
Set Implicit Arguments.
Unset Strict Implicit.

(*==========================================================================
  Order-theoretic definitions
  ==========================================================================*)
Definition Oprod : ord -> ord -> ord.
intros O1 O2; exists (O1 * O2)%type (fun x y => fst x <= fst y /\ snd x <= snd y); intuition.
apply Ole_trans with a0; trivial.
apply Ole_trans with b0; trivial.
Defined.

Definition Fst (O1 O2 : ord) : Oprod O1 O2 -m> O1.
intros O1 O2; exists (fst (A:=O1) (B:=O2)); red; simpl; intuition.
Defined.

Implicit Arguments Fst [O1 O2].

Definition Snd (O1 O2 : ord) : Oprod O1 O2 -m> O2.
intros O1 O2; exists (snd (A:=O1) (B:=O2)); red; simpl; intuition.
Defined.

Implicit Arguments Snd [O1 O2].

(*
Definition Pairr (O1 O2 : ord) : O1 -> O2 -m> Oprod O1 O2.
intros O1 O2 x.
exists (fun (y:O2) => (x,y)).
red; auto.
Defined.

Definition Pair (O1 O2 : ord) : O1 -m> O2 -m> Oprod O1 O2.
intros O1 O2; exists (Pairr (O1:=O1) O2); red; auto.
Defined.
*)

Lemma Fst_simpl : forall (O1 O2 : ord) (p:Oprod O1 O2), Fst p = fst p.
trivial.
Save.

Lemma Snd_simpl : forall (O1 O2 : ord) (p:Oprod O1 O2), Snd p = snd p.
trivial.
Save.

(*
Lemma Pair_simpl : forall (O1 O2 : ord) (x:O1)(y:O2), Pair O1 O2 x y = (x,y).
trivial.
Save.
*)

Lemma Oprod_unique: forall O1 O2 O3 (f g:O1 -m> Oprod O2 O3),
      Fst @ f == Fst @ g -> Snd @ f == Snd @ g -> f == g.
intros O1 O2 O3 f g ff ss.
apply fmon_eq_intro. intros x.
split ; auto using (fmon_eq_elim ff x), (fmon_eq_elim ss x).
Qed.

(*
Definition prod0 (D1 D2:cpo) : Oprod D1 D2 := (0: D1,0: D2).
*)

Definition prod_lub (D1 D2:cpo) (f : natO -m> Oprod D1 D2) := (lub (Fst @f), lub (Snd @f)).

Definition Dprod : cpo -> cpo -> cpo.
intros D1 D2; exists (Oprod D1 D2) 
                     (* (prod0 D1 D2) *)
                     (prod_lub (D1:=D1) (D2:=D2)); unfold prod_lub; intuition.
apply Ole_trans with (fst (fmonot c n), snd (fmonot c n)); simpl; intuition.
apply (le_lub (Fst @ c) (n)).
apply (le_lub (Snd @ c) (n)).
apply Ole_trans with (fst x, snd x); simpl; intuition.
apply lub_le; simpl; intros.
case (H n); auto.
apply lub_le; simpl; intros.
case (H n); auto.
Defined.

(** printing DOne %\DOne% *)
Definition DOne : cpo := Discrete unit.

Lemma DOne_final: forall D (f g : D -C-> DOne), f == g.
intros. refine (fcont_eq_intro _). intros d. case (f d) ; case (g d) ; auto.
Qed.

Instance DOne_pointed : Pointed DOne.
exists tt.
intros d. case d. auto.
Defined.



(*==========================================================================
  Domain-theoretic definitions
  ==========================================================================*)

(** printing *c* %\ensuremath{\times}% *)
Infix "*c*" := Dprod (at level 28, left associativity).

Lemma Dprod_eq_intro : forall (D1 D2:cpo) (p1 p2 :  D1 *c* D2),
             fst p1 == fst p2 -> snd p1 == snd p2 -> p1 == p2.
split; simpl; auto.  
Save.
Hint Resolve Dprod_eq_intro.

Lemma Dprod_eq_pair : forall (D1 D2 : cpo) (x1 y1 : D1) (x2 y2 : D2),
             x1==y1 -> x2==y2 -> ((x1,x2):Dprod D1 D2) == (y1,y2).
auto.  
Save.
Hint Resolve Dprod_eq_pair.

Lemma Dprod_eq_elim_fst : forall (D1 D2 : cpo) (p1 p2 : Dprod D1 D2),
             p1==p2 -> fst p1 == fst p2.
split; case H; simpl; intuition.  
Save.
Hint Immediate Dprod_eq_elim_fst.

Lemma Dprod_eq_elim_snd : forall (D1 D2:cpo) (p1 p2: Dprod D1 D2),
             p1==p2 -> snd p1 == snd p2.
split; case H; simpl; intuition.  
Save.
Hint Immediate Dprod_eq_elim_snd.

Lemma Dprod_le_elim_snd: forall (D1 D2:cpo) (p1 p2 : Dprod D1 D2),
        p1 <= p2 -> snd p1 <= snd p2.
simpl. intros D1 D2 p1 p2. intros x. destruct x. auto.
Qed.

Hint Immediate Dprod_le_elim_snd.

Lemma Dprod_le_elim_fst: forall (D1 D2:cpo) (p1 p2:Dprod D1 D2),
       p1 <= p2 -> fst p1 <= fst p2.
simpl. intros D1 D2 p1 p2 x. destruct x. auto.
Qed.

Hint Immediate Dprod_le_elim_fst.

(** printing FST %\FST% *)

Definition FST (D1 D2 : cpo) : D1 *c* D2 -c> D1.
intros; exists (@Fst D1 D2); red; intros; auto.
Defined.

Implicit Arguments FST [D1 D2].

Add Parametric Morphism (D E : cpo) : (@FST D E)
with signature (@Ole (Dprod D E)) ++> (@Ole D)
as PROD_FST_le_compat.
auto.
Qed.

Add Parametric Morphism (D E : cpo) : (@FST D E)
with signature (@Oeq (Dprod D E)) ==> (@Oeq D)
as PROD_FST_eq_compat.
intros ; split ; auto.
Qed.

(** printing SND %\SND% *)
Definition SND (D1 D2 : cpo) : D1 *c* D2 -c> D2.
intros; exists (@Snd D1 D2); red; intros; auto.
Defined.

Implicit Arguments SND [D1 D2].

Add Parametric Morphism (D E : cpo) : (@SND D E)
with signature (@Ole (Dprod D E)) ++> (@Ole E)
as PROD_SND_le_compat.
intros ; auto.
Qed.

Add Parametric Morphism (D E : cpo) : (@SND D E)
with signature (@Oeq (Dprod D E)) ==> (@Oeq E)
as PROD_SND_eq_compat.
intros ; split ; auto.
Qed.

Definition Pairr (O1 O2 : ord) : O1 -> O2 -m> Oprod O1 O2.
intros O1 O2 x.
exists (fun (y:O2) => (x,y)).
red; auto.
Defined.

Definition Pair (O1 O2 : ord) : O1 -m> O2 -m> Oprod O1 O2.
intros O1 O2; exists (Pairr (O1:=O1) O2); red; auto.
Defined.

Lemma Pair_continuous2 : forall (D1 D2 : cpo), continuous2 (D3:=Dprod D1 D2) (Pair D1 D2).
red; intros; auto.
Save.

Definition PAIR (D1 D2:cpo) : D1 -c> D2 -C-> Dprod D1 D2 
                := continuous2_cont (Pair_continuous2 (D1:=D1) (D2:=D2)).

Implicit Arguments PAIR [D1 D2].

Add Parametric Morphism (D0 D1:cpo) : (@pair D0 D1)
with signature (@Ole D0) ++> (@Ole D1) ++> (@Ole (Dprod D0 D1))
as pair_le_compat.
auto.
Qed.

Add Parametric Morphism (D0 D1:cpo) : (@pair D0 D1)
with signature (@Oeq D0) ==> (@Oeq D1) ==> (@Oeq (Dprod D0 D1))
as pair_eq_compat.
auto.
Qed.

Lemma Dprod_unique: forall D E F (f g : F -C-> D *c* E), 
   FST << f == FST << g ->
   SND << f == SND << g -> 
   f == g.
Proof.
intros D E F f g ff ss.
refine (Oprod_unique ff ss).
Qed.

Lemma FST_simpl : forall (D1 D2 :cpo) (p:Dprod D1 D2), FST p = Fst p.
trivial.
Save.

Lemma SND_simpl : forall (D1 D2 :cpo) (p:Dprod D1 D2), SND p = Snd p.
trivial.
Save.

Definition Prod_fun (O1 O2 O3:ord)(f:O1-m>O2)(g:O1-m>O3) : O1 -m> Oprod O2 O3.
intros O1 O2 O3 f g. exists (fun p => (f p, g p)). auto.
Defined.

Lemma Prod_fun_simpl (O1 O2 O3:ord)(f:O1-m>O2)(g:O1-m>O3) x : Prod_fun f g x = (f x,g x).
auto.
Qed.


Definition PROD_fun (D1 D2 D3:cpo)(f:D1-c>D2)(g:D1-c>D3) : D1 -c> D2 *c* D3.
intros D1 D2 D3 f g. exists (Prod_fun (fcontit f) (fcontit g)).
unfold continuous.
intros c.
simpl. split.
apply Ole_trans with (y:= f (lub c)) ; auto.
rewrite (fcont_continuous f) ; auto.
apply Ole_trans with (y:= g (lub c)) ; auto.
rewrite (fcont_continuous g) ; auto.
Defined.


Lemma FST_PAIR_simpl : forall (D1 D2 :cpo) (p1:D1) (p2:D2), 
            FST (PAIR p1 p2) = p1.
trivial.
Save.

Lemma SND_PAIR_simpl : forall (D1 D2 :cpo) (p1:D1) (p2:D2), 
            SND (PAIR p1 p2) = p2.
trivial.
Save.

Lemma PAIR_simpl : forall (D1 D2 :cpo) (p1:D1) (p2:D2), PAIR p1 p2 = Pair D1 D2 p1 p2.
trivial.
Save.

(** printing <| %\ensuremath{\langle}% *)
(** printing |> %\ensuremath{\rangle}% *)
Notation "'<|' f , g '|>'" := (PROD_fun f g) (at level 30).

Lemma PROD_fun_simpl (D E F : cpo) (f : D -C-> E) (g : D -C-> F) d :
           <| f, g |> d = (f d , g d).
auto.
Qed.

Lemma FST_PROD_fun: forall D0 D1 D2 (f:D0 -C-> D1) (g:D0 -C-> D2), FST << PROD_fun f g == f.
intros. apply fcont_eq_intro ; auto.
Qed.

Lemma SND_PROD_fun: forall D0 D1 D2 (f:D0 -C-> D1) (g:D0 -C-> D2), SND << PROD_fun f g == g.
intros. apply fcont_eq_intro ; auto.
Qed.

Add Parametric Morphism (D0 D1 D2:cpo) : (@PROD_fun D0 D1 D2)
with signature (@Ole (D0 -c> D1)) ++> (@Ole (D0 -c> D2)) ++> (@Ole (D0 -c> @Dprod D1 D2))
as PROD_fun_le_compat.
intros f g feq s r seq.
simpl.
intros x.
assert (fd:=fcont_le_elim feq x). assert (fe := fcont_le_elim seq x).
auto.
Qed.

Add Parametric Morphism (D0 D1 D2:cpo) : (@PROD_fun D0 D1 D2)
with signature (@Oeq (D0 -c> D1)) ==> (@Oeq (D0 -c> D2)) ==> (@Oeq (D0 -c> @Dprod D1 D2))
as PROD_fun_eq_compat.
intros f g feq s r geq.
destruct feq as [fle1 fle2].
destruct geq as [gle1 gle2].
split ; auto.
Qed.

Definition PROD_map (D1 D2 D3 D4:cpo)(f:D1-c>D3)(g:D2-c>D4) : 
      D1 *c* D2 -c> D3 *c* D4 := PROD_fun (f << FST) (g << SND).

Implicit Arguments PROD_map [D1 D2 D3 D4].

(** printing *f* %\crossf% *)
Infix "*f*" := PROD_map (at level 28).

Lemma PROD_fun_compl (D E F G : cpo) (f : D -C-> E) (g : D -C-> F) (h : G -C-> D) : 
        <| f, g|> << h == <| f << h , g << h |>.
intros D E F G f g h.
simpl. apply (@Dprod_unique E F G).
rewrite FST_PROD_fun. rewrite <-fcont_comp_assoc. rewrite FST_PROD_fun. auto.
rewrite SND_PROD_fun. rewrite <- fcont_comp_assoc. rewrite SND_PROD_fun. auto.
Qed.

Lemma PROD_fun_compr (D E F G H : cpo) (f : H -c> D) (g : D -c> E) (h : H -c> F) (k : F -c> G) :
       <| g << f, k << h |> == g *f* k << <| f, h |>.
intros D E F G H f g h k. apply (@Dprod_unique E G H).
rewrite FST_PROD_fun. rewrite <-fcont_comp_assoc. unfold PROD_map.
rewrite FST_PROD_fun. rewrite fcont_comp_assoc. rewrite FST_PROD_fun. auto.
rewrite SND_PROD_fun. rewrite <-fcont_comp_assoc. unfold PROD_map.
rewrite SND_PROD_fun. rewrite fcont_comp_assoc. rewrite SND_PROD_fun. auto.
Qed.

Add Parametric Morphism (D E F G:cpo) : (@PROD_map D E F G)
with signature (@Ole (D -c> F)) ++> (@Ole (E -c> G)) ++> (@Ole (@Dprod D E -c> @Dprod F G))
as PROD_map_le_compat.
intros f g feq s r seq.
simpl.
intros x. case x. clear x. intros d e.
assert (fd:=fcont_le_elim feq d). assert (fe := fcont_le_elim seq e).
auto.
Qed.

Add Parametric Morphism (D E F G:cpo) : (@PROD_map D E F G)
with signature (@Oeq (D -c> F)) ==> (@Oeq (E -c> G)) ==> (@Oeq (@Dprod D E -c> @Dprod F G))
as PROD_map_eq_compat.
intros f g feq s r geq.
destruct feq as [fle1 fle2].
destruct geq as [gle1 gle2].
split ; auto.
Qed.

Lemma PROD_map_simpl :  forall (D1 D2 D3 D4 : cpo) (f : D1 -c> D3) (g : D2 -c> D4) (p : D1 *c* D2), 
      (f *f* g) p = pair (f (fst p)) (g (snd p)).
trivial.
Save.

Definition PROD_Map1 (D E F G:cpo) : (D -C-> F) -> (E -C-> G) -M-> Dprod D E -C-> Dprod F G.
intros. exists (@PROD_map D E F G X). unfold monotonic.
intros f0 f1 leq. intros x. simpl ; auto.
Defined.

Definition PROD_Map (D E F G:cpo) : (D -C-> F) -M-> (E -C-> G) -M-> Dprod D E -C-> Dprod F G.
intros. exists (@PROD_Map1 D E F G). unfold monotonic.
intros f0 f1 leq. intros x. simpl ; auto.
Defined.

Lemma PROD_Map_continuous2 : forall D E F G, continuous2 (PROD_Map D E F G).
intros. unfold continuous2. intros c1 c2.
intros p. auto.
Save.

Definition PROD_MAP (D E F G:cpo) : (D -C-> F) -C-> (E -C-> G) -C-> Dprod D E -C-> Dprod F G :=
  (continuous2_cont (@PROD_Map_continuous2 D E F G)).

Definition SWAP D E := <| @SND D E, FST |>.
Implicit Arguments SWAP [D E].

Instance prod_pointed A B { pa : Pointed A} {pb : Pointed B} : Pointed (A *c* B).
intros.
destruct pa as [pa Pa0].
destruct pb as [pb Pb0].
exists (pa,pb).
intro.
auto.
Defined.

Lemma PROD_map_compl D0 D1 D2 D3 D4 (f:D0 -c> D1) (g:D1 -c> D2) (h:D3 -c> D4) : (g << f) *f* h == (g *f* ID) << (f *f* h).
intros ; refine (Dprod_unique _ _). unfold PROD_map. rewrite FST_PROD_fun.
rewrite <- fcont_comp_assoc. rewrite FST_PROD_fun. repeat (rewrite fcont_comp_assoc). rewrite FST_PROD_fun.
auto. unfold PROD_map. rewrite SND_PROD_fun.
rewrite <- fcont_comp_assoc. rewrite SND_PROD_fun. repeat (rewrite fcont_comp_assoc). rewrite SND_PROD_fun.
rewrite fcont_comp_unitL.
auto.
Qed.

Lemma PROD_map_compr D0 D1 D2 D3 D4 (f:D0 -c> D1) (g:D1 -c> D2) (h:D3 -c> D4) : h *f* (g << f) == (ID *f* g) << (h *f* f).
intros ; refine (Dprod_unique _ _). unfold PROD_map. rewrite FST_PROD_fun.
rewrite <- fcont_comp_assoc. rewrite FST_PROD_fun. repeat (rewrite fcont_comp_assoc). rewrite FST_PROD_fun.
rewrite fcont_comp_unitL. auto.
unfold PROD_map. rewrite SND_PROD_fun.
rewrite <- fcont_comp_assoc. rewrite SND_PROD_fun. repeat (rewrite fcont_comp_assoc). rewrite SND_PROD_fun.
auto.
Qed.

Definition curry (D1 D2 D3 : cpo) (f:Dprod D1 D2 -c> D3) : D1 -c> (D2-C->D3) :=
fcont_COMP D1 (D2-C->Dprod D1 D2) (D2-C->D3) 
                          (fcont_COMP D2 (Dprod D1 D2) D3 f) (PAIR).

Definition EV D0 D1 := ((AP D0 D1) @2_ FST) SND.

Implicit Arguments EV [D0 D1].

Lemma EV_simpl D0 D1 (f : D0 -c> D1) a : EV (f,a) = f a.
auto.
Qed.

Add Parametric Morphism D0 D1 : (@EV D0 D1)
with signature (@Ole (Dprod (D0 -C-> D1) D0)) ++> (@Ole D1)
as EV_le_compat.
auto.
Qed.

Add Parametric Morphism D E : (@EV D E)
with signature (@Oeq (Dprod (D -C-> E) D)) ==> (@Oeq E)
as EV_eq_compat.
split ; auto.
Qed.

Definition CURRY (D0 D1 D2:cpo) : (Dprod D0 D1 -C-> D2) -c> (D0 -C-> D1 -C-> D2) :=
   curry (curry (EV << <| FST << FST, <| SND << FST, SND |> |>)).

Implicit Arguments CURRY [D0 D1 D2].

Lemma CURRY_simpl : forall (D1 D2 D3 : cpo) (f:Dprod D1 D2 -C-> D3), 
       CURRY f == curry f.
intros. unfold CURRY.
simpl. apply fcont_eq_intro. intros x. simpl. apply fcont_eq_intro. intros y. auto.
Save.

Lemma curry_com: forall D E F (f : D *c* E -C-> F),
        f == EV << (PROD_map (curry f) ID).
intros. simpl. apply fcont_eq_intro. intros d. case d. clear d.
intros d e. auto.
Qed.

Lemma curry_unique: forall D E F (f:D -c> E -C-> F) g,
         g == EV << (PROD_map f ID) -> f == curry g.
intros. apply fcont_eq_intro. intros a. simpl. apply fcont_eq_intro. intros b.
assert (xx:=fcont_eq_elim H (a,b)). auto.
Qed.

Add Parametric Morphism (D0 D1 D2 : cpo) : (@curry D0 D1 D2)
with signature (@Ole (Dprod D0 D1 -c> D2)) ++> (@Ole (D0 -c> (D1 -C-> D2)))
as curry_le_compat.
intros f g lf.
simpl. intros x0 x1. auto.
Qed.

Hint Resolve curry_le_compat_Morphism.

Add Parametric Morphism (D0 D1 D2 : cpo) : (@curry D0 D1 D2)
with signature (@Oeq (Dprod D0 D1 -c> D2)) ==> (@Oeq (D0 -c> (D1 -C-> D2)))
as curry_eq_compat.
intros f1 f2 Eqf.
destruct Eqf as [fle1 fle2].
split.
apply (curry_le_compat fle1).
apply (curry_le_compat fle2).
Qed.

Hint Resolve curry_eq_compat_Morphism.

Lemma curry_simpl: forall D E F (f:(Dprod E F) -C-> D) x y, curry f x y = f (x,y).
intros D E F f x y.
unfold curry.
repeat (try (rewrite fcont_COMP_simpl) ; try (rewrite fcont_comp_simpl) ; try (rewrite PAIR_simpl)).
simpl. auto.
Qed.

Lemma Dext (D0 D1 D2:cpo) (f g : D0 -c> D1 -C-> D2) : EV << (f *f* ID) == EV << (g *f* ID) -> f == g.
intros D0 D1 D2 f g C.
rewrite (curry_unique (Oeq_refl (EV << (f *f* ID)))).
rewrite (curry_unique (Oeq_refl (EV << (g *f* ID)))).
apply (curry_eq_compat C).
Qed.

Definition uncurry D0 D1 D2 :=
      curry (EV << <| EV << <| @FST (D0 -C-> D1 -C-> D2) _, FST << SND |>,
                      SND << SND |>).

Implicit Arguments uncurry [D0 D1 D2].

Lemma uncurry_simpl: forall D E F (f:D -c> E -C-> F) p1 p2, uncurry f (p1,p2) = f p1 p2.
intros ; auto.
Qed.

Lemma PROD_fun_comp (D0 D1 D2 D3:cpo) (f:D0 -c> D1) (g:D0 -c> D2) (h:D3 -c> D0) : <| f,g |> << h == <| f << h, g << h |>.
intros.
refine (Dprod_unique _ _); rewrite <- fcont_comp_assoc.
rewrite FST_PROD_fun ; rewrite FST_PROD_fun  ; auto.
rewrite SND_PROD_fun ; rewrite SND_PROD_fun  ; auto.
Qed.

Lemma curry_uncurry (D0 D1 D2:cpo) : @CURRY D0 D1 D2 << uncurry == ID.
intros D0 D1 D2.

assert (forall D0 D1 D2 D3 D4 (f:D0 -c> D1) (g:D1 -C-> D2) (h:D3 -c> D4), (g << f) *f* h == (g *f* ID) << (f *f* h)).
intros. refine (Dprod_unique _ _) ; unfold PROD_map. rewrite FST_PROD_fun.
rewrite <- fcont_comp_assoc. rewrite FST_PROD_fun. repeat (rewrite fcont_comp_assoc). rewrite FST_PROD_fun. auto.
rewrite SND_PROD_fun.
rewrite <- fcont_comp_assoc. rewrite SND_PROD_fun. repeat (rewrite fcont_comp_assoc). rewrite SND_PROD_fun.
rewrite fcont_comp_unitL. auto.

apply Dext. rewrite H.
rewrite <- fcont_comp_assoc.
unfold CURRY. rewrite <- curry_com.
apply Dext.
rewrite H.
rewrite <- fcont_comp_assoc.
rewrite <- curry_com.
unfold uncurry.
rewrite fcont_comp_assoc.
assert ((<| FST << FST, <| SND << FST, SND |> |> <<
    (curry (D1:=D0 -C-> D1 -C-> D2) (D2:=D0 *c* D1) (D3:=D2)
       (EV << <| EV << <| FST, FST << SND |>, SND << SND |>) *f* 
     @ID D0) *f* @ID D1) == 
  (curry (EV << <| EV << <| FST, FST << SND |>, SND << SND |>) *f* (ID *f* ID)) <<
    <| FST << FST, <| SND << FST, SND |> |>).
refine (Dprod_unique _ _) ; unfold PROD_map.
rewrite <- fcont_comp_assoc. rewrite FST_PROD_fun. rewrite fcont_comp_assoc.
rewrite FST_PROD_fun. rewrite <- fcont_comp_assoc. rewrite FST_PROD_fun.
rewrite <- fcont_comp_assoc. rewrite FST_PROD_fun. repeat (rewrite fcont_comp_assoc). rewrite FST_PROD_fun. auto.
rewrite <- fcont_comp_assoc. rewrite SND_PROD_fun.
rewrite <- fcont_comp_assoc. rewrite SND_PROD_fun.
refine (Dprod_unique _ _). rewrite <- fcont_comp_assoc. rewrite FST_PROD_fun.
rewrite fcont_comp_assoc. rewrite FST_PROD_fun. rewrite <- fcont_comp_assoc. rewrite SND_PROD_fun.
repeat (rewrite <- fcont_comp_assoc). rewrite FST_PROD_fun.
repeat (rewrite fcont_comp_unitL).
repeat (rewrite fcont_comp_assoc). rewrite SND_PROD_fun. rewrite FST_PROD_fun. auto.
rewrite <- fcont_comp_assoc. repeat (rewrite SND_PROD_fun).
repeat (rewrite <- fcont_comp_assoc). rewrite SND_PROD_fun. rewrite fcont_comp_assoc.
rewrite SND_PROD_fun. rewrite fcont_comp_assoc.
rewrite SND_PROD_fun. auto.
rewrite H0. clear H0. rewrite <- fcont_comp_assoc.
assert (@ID D0 *f* @ID D1 == ID) as Ide. refine (Dprod_unique _ _) ; unfold PROD_map.
rewrite FST_PROD_fun. rewrite fcont_comp_unitR. rewrite fcont_comp_unitL. auto.
rewrite SND_PROD_fun. rewrite fcont_comp_unitR. rewrite fcont_comp_unitL. auto.
rewrite (PROD_map_eq_compat (Oeq_refl _) Ide). rewrite <- curry_com.
repeat (rewrite fcont_comp_assoc).
refine (fcont_comp_eq_compat (Oeq_refl _) _).
refine (Dprod_unique _ _) ; unfold PROD_map.
rewrite <- fcont_comp_assoc. repeat (rewrite FST_PROD_fun).
repeat (rewrite fcont_comp_assoc).
refine (fcont_comp_eq_compat (Oeq_refl _) _).
refine (Dprod_unique _ _). repeat (rewrite <- fcont_comp_assoc). repeat (rewrite FST_PROD_fun).
rewrite fcont_comp_unitL. auto. repeat (rewrite <- fcont_comp_assoc). repeat (rewrite SND_PROD_fun).
rewrite fcont_comp_unitL. rewrite fcont_comp_assoc. rewrite SND_PROD_fun. rewrite FST_PROD_fun. auto.
repeat (rewrite <- fcont_comp_assoc). repeat (rewrite SND_PROD_fun).
rewrite fcont_comp_assoc. repeat (rewrite SND_PROD_fun). rewrite fcont_comp_unitL. auto.
Qed.

(*
Lemma uncurry_curry (D0 D1 D2:cpo) : uncurry << @CURRY D0 D1 D2 == ID.
intros.
apply Dext. unfold uncurry.
assert (forall D0 D1 D2 D3 D4 (f:D0 -c> D1) (g:D1 -C-> D2) (h:D3 -c> D4), (g << f) *f* h == (g *f* ID) << (f *f* h)).
intros. refine (Dprod_unique _ _) ; unfold PROD_map. rewrite FST_PROD_fun.
rewrite <- fcont_comp_assoc. rewrite FST_PROD_fun. repeat (rewrite fcont_comp_assoc). rewrite FST_PROD_fun. auto.
rewrite SND_PROD_fun.
rewrite <- fcont_comp_assoc. rewrite SND_PROD_fun. repeat (rewrite fcont_comp_assoc). rewrite SND_PROD_fun.
rewrite fcont_comp_unitL. auto.

rewrite H. rewrite <- fcont_comp_assoc. rewrite <- curry_com. unfold CURRY.

*)

Add Parametric Morphism (D0 D1 D2:cpo) : (@uncurry D0 D1 D2)
with signature (@Oeq (D0 -c> (D1 -C-> D2))) ==> (@Oeq ((Dprod D0 D1) -c> D2))
as uncurry_eq_compat.
intros. apply fcont_eq_intro ; auto.
Qed.
Hint Resolve uncurry_eq_compat_Morphism.

Add Parametric Morphism (D0 D1 D2:cpo) : (@uncurry D0 D1 D2)
with signature (@Ole (D0 -c> (D1 -C-> D2))) ++> (@Ole ((Dprod D0 D1) -c> D2))
as uncurry_le_compat.
intros. apply fcont_le_intro ; auto.
Qed.
Hint Resolve uncurry_le_compat_Morphism.

Lemma Uncurry_simpl : forall (D1 D2 D3 : cpo) (f:D1 -c> (D2-C->D3)) (p:Dprod D1 D2), 
       uncurry f p = f (fst p) (snd p).
trivial.
Save.

Lemma FST_SWAP : forall D E F (f:D -c> F), f << FST << SWAP == f << SND (D1:=E).
intros; apply fcont_eq_intro; auto. 
Qed.

Lemma SND_SWAP : forall D E F (f:E -c> F), f << SND << SWAP == f << FST (D2:=D).
intros; apply fcont_eq_intro. auto. 
Qed.

Lemma SND_PAIR : forall D E F (f:E -c> F) x, f << SND << PAIR (D1:=D) x == f. 
intros; apply fcont_eq_intro. auto. 
Qed.

Lemma FST_PAIR : forall D E F (f:D -c> F) (x:D),  f << FST << PAIR x == @K E _ (f x). 
intros; apply fcont_eq_intro. auto. 
Qed.

Lemma FST_PROD_fun_aux : forall C D E F (f:C -c> D) (g:C -c> E) (k:D -c> F), k << FST << PROD_fun f g == k << f.
intros; apply fcont_eq_intro. auto.  
Qed.

Lemma SND_PROD_fun_aux : forall C D E F (f:C -c> D) (g:C -c> E) (k:E -c> F), k << SND << PROD_fun f g == k << g.
intros; apply fcont_eq_intro. auto.
Qed.

Lemma PROD_map_ID_ID :
  forall C D, PROD_map (D1 := C) (D2 := D) ID ID == ID.
intros C D. 
apply fcont_eq_intro. auto. 
Qed.

Lemma PROD_map_PROD_map : forall A B C D E F (f:A -c> B) (g : C -c> D) (h :B -c> E) (i :D -c> F), 
  PROD_map h i << PROD_map f g == PROD_map (h << f) (i << g). 
intros. apply fcont_eq_intro.  auto. 
Qed.

Lemma Curry_EV : forall C D E (f:C -c> D -C-> E) , curry (EV << PROD_map f ID) == f.
intros C D E f.
symmetry.
apply curry_unique. trivial.
Qed.

Lemma EV_Curry : forall C D E (f:Dprod C D -c> E) , EV << PROD_map (curry f) ID == f.
intros C D E f.
rewrite <- curry_com.  trivial.
Qed. 

Lemma Curry_comp : forall A B C D (f:Dprod A B -c> C) (g:D -c> A), curry f << g == curry (f << PROD_map g ID).
intros A B C D f g.
assert (H := curry_com f). rewrite H. 
rewrite fcont_comp_assoc.
rewrite PROD_map_PROD_map. 
rewrite Curry_EV.  rewrite fcont_comp_unitL.
rewrite Curry_EV. trivial.
Qed.





(** ** Indexed product of cpo's *)

Definition Oprodi (I:Type)(O:I->ord) : ord.
intros; exists (forall i:I, O i) (fun p1 p2 => forall i:I, p1 i <= p2 i); intros; auto.
apply Ole_trans with (y i); trivial.
Defined.

Lemma Oprodi_eq_intro : forall (I:Type)(O:I->ord) (p q : Oprodi O), (forall i, p i == q i) -> p==q.
intros; apply Ole_antisym; intro i; auto.
Save.

Lemma Oprodi_eq_elim : forall (I:Type)(O:I->ord) (p q : Oprodi O), p==q -> forall i, p i == q i.
intros; apply Ole_antisym; case H; auto.
Save.

Definition Proj (I:Type)(O:I->ord) (i:I) : Oprodi O -m> O i.
intros.
exists (fun (x:Oprodi O) => x i); red; intuition.
Defined.

Lemma Proj_simpl : forall  (I:Type)(O:I->ord) (i:I) (x:Oprodi O),
            Proj O i x = x i.
trivial.
Save.

Definition Dprodi (I:Type)(D:I->cpo) : cpo.
intros; exists (Oprodi D) (fun (f : natO -m> Oprodi D) (i:I) => lub (Proj D i @ f));
intros; simpl; intros; auto.
apply (le_lub (Proj (fun x : I => D x) i @ c) (n)).
apply lub_le; simpl; intros.
apply (H n i).
Defined.

Lemma Dprodi_lub_simpl : forall (I:Type)(Di:I->cpo)(h:natO-m>Dprodi Di)(i:I),
            lub h i = lub (c:=Di i) (Proj Di i @ h).
trivial.
Save.

Lemma Dprodi_eq_intro : forall I O (p1 p2:@Dprodi I O),
     (forall i, Proj O i p1 == Proj O i p2) -> p1 == p2.
intros I O p1 p2 C.
split ; intro i ; specialize (C i) ; simpl in C; auto.
Qed.

Lemma Dprodi_eq_elim : forall I O i (p1 p2: @Dprodi I O),
     p1 == p2 -> Proj O i p1 == Proj O i p2.
intros. simpl. simpl in H. destruct H as [X Y].
split ; auto.
Qed.

Hint Resolve Dprodi_eq_intro.
Hint Immediate Dprodi_eq_elim.

Lemma Dprodi_le_intro : forall I O (p1 p2:@Dprodi I O),
     (forall i, Proj O i p1 <= Proj O i p2) -> p1 <= p2.
intros I O p1 p2 C.
intro i ; specialize (C i) ; simpl in C; auto.
Qed.

Lemma Dprodi_le_elim : forall I O i (p1 p2: @Dprodi I O),
     p1 <= p2 -> Proj O i p1 <= Proj O i p2.
auto.
Qed.

Hint Resolve Dprodi_le_intro.
Hint Immediate Dprodi_le_elim.

Lemma Proj_cont : forall (I:Type)(Di:I->cpo) (i:I), 
                    continuous (D1:=Dprodi Di) (D2:=Di i) (Proj Di i).
red; intros; simpl; trivial.
Save.

Definition PROJ (I:Type)(Di:I->cpo) (i:I) : Dprodi Di -c> Di i := 
      mk_fconti (Proj_cont (Di:=Di) i).

Lemma PROJ_simpl : forall (I:Type)(Di:I->cpo) (i:I)(d:Dprodi Di),
               PROJ Di i d = d i.
trivial.
Save.

Lemma Dprodi_unique: forall I O D (f g : D -C-> @Dprodi I O),
    (forall i, PROJ O i << f == PROJ O i << g) -> f == g.
intros. simpl.
apply fcont_eq_intro. intros x. simpl.
refine (Dprodi_eq_intro _).
intros i. specialize (H i). assert (h:=fcont_eq_elim H x).
auto.
Qed.

Definition Prodi_fun I O D (f:forall i:I, D -m> O i) : D -m> Oprodi O.
intros. exists (fun d => fun i => f i d).
unfold monotonic. intros d0 d1 deq. simpl. intros i.
assert (monotonic (f i)) as M by auto.
apply M. auto.
Defined.

Definition PRODI_fun I O D (f:forall i:I, D -c> O i) : D -c> Dprodi O.
intros. exists (@Prodi_fun I _ D (fun i => fcontit (f i))).
unfold continuous. intros c. simpl.
intros i. assert (continuous (fcontit (f i))) as C by auto.
unfold continuous in C. rewrite C.
refine (lub_le_compat _). auto.
Defined.

Lemma PROJ_com_point: forall D I O (f:forall i, D -C-> O i) (i:I) d,
                 PROJ O i (PRODI_fun f d) = f i d.
auto.
Qed.

Lemma PROJ_com: forall D I O (f:forall i, D -C-> O i) (i:I),
                 PROJ O i << PRODI_fun f == f i.
auto using fcont_eq_intro.
Qed.

Definition PRODI_map I O1 O2 (f:forall i:I, O1 i -c> O2 i) :=
 PRODI_fun (fun i => f i << PROJ O1 i).

Lemma Dprodi_continuous : forall (D:cpo)(I:Type)(Di:I->cpo)
    (f:D -m> Dprodi Di), (forall i, continuous (Proj Di i @ f)) -> 
    continuous f.
red; intros; intro i.
apply Ole_trans with (lub (c:=Di i) ((Proj Di i @ f) @ c)); auto.
exact (H i c).
Save.

Definition Dprodi_lift : forall (I J:Type)(Di:I->cpo)(f:J->I),
             Dprodi Di -m> Dprodi (fun j => Di (f j)).
intros.
exists (fun (p:Dprodi Di) j => p (f j)); red; auto.
Defined.

Lemma Dprodi_lift_simpl : forall (I J:Type)(Di:I->cpo)(f:J->I)(p:Dprodi Di),
             Dprodi_lift Di f p = fun j => p (f j).
trivial.
Save.

Lemma Dprodi_lift_cont : forall (I J:Type)(Di:I->cpo)(f:J->I),
             continuous (Dprodi_lift Di f).
intros; apply Dprodi_continuous; red; simpl; intros; auto.
Save.

Definition DLIFTi (I J:Type)(Di:I->cpo)(f:J->I) : Dprodi Di -c> Dprodi (fun j => Di (f j)) 
             := mk_fconti (Dprodi_lift_cont (Di:=Di) f).

Definition Dmapi : forall (I:Type)(Di Dj:I->cpo)(f:forall i, Di i -m> Dj i), 
            Dprodi Di -m> Dprodi Dj.
intros; exists (fun p i => f i (p i)); red; auto.
Defined.

Lemma Dmapi_simpl : forall (I:Type)(Di Dj:I->cpo)(f:forall i, Di i -m> Dj i) (p:Dprodi Di) (i:I),
Dmapi f p i = f i (p i).
trivial.
Save.


(* Stuff
(** *** Particular cases with one or two elements *)

Section Product2.

Definition I2 := bool.
Variable DI2 : bool -> cpo.

Definition DP1 := DI2 true.
Definition DP2 := DI2 false.

Definition PI1 : Dprodi DI2 -c> DP1 := PROJ DI2 true.
Definition pi1 (d:Dprodi DI2) := PI1 d.

Definition PI2 : Dprodi DI2 -c> DP2 := PROJ DI2 false.
Definition pi2 (d:Dprodi DI2) := PI2 d.

Definition pair2 (d1:DP1) (d2:DP2) : Dprodi DI2 := bool_rect DI2 d1 d2.

Lemma pair2_le_compat : forall (d1 d'1:DP1) (d2 d'2:DP2), d1 <= d'1 -> d2 <= d'2 
            -> pair2 d1 d2 <= pair2 d'1 d'2.
intros; intro b; case b; simpl; auto.
Save.

Definition Pair2 : DP1 -m> DP2 -m> Dprodi DI2 := le_compat2_mon pair2_le_compat.

Definition PAIR2 : DP1 -c> DP2 -C-> Dprodi DI2.
apply continuous2_cont with (f:=Pair2).
red; intros; intro b.
case b; simpl; apply lub_le_compat; auto.
Defined.

Lemma PAIR2_simpl : forall (d1:DP1) (d2:DP2), PAIR2 d1 d2 = Pair2 d1 d2.
trivial.
Save.

Lemma Pair2_simpl : forall (d1:DP1) (d2:DP2), Pair2 d1 d2 = pair2 d1 d2.
trivial.
Save.

Lemma pi1_simpl : forall  (d1: DP1) (d2:DP2), pi1 (pair2 d1 d2) = d1.
trivial.
Save.

Lemma pi2_simpl : forall  (d1: DP1) (d2:DP2), pi2 (pair2 d1 d2) = d2.
trivial.
Save.

Definition DI2_map (f1 : DP1 -c> DP1) (f2:DP2 -c> DP2) 
               : Dprodi DI2 -c> Dprodi DI2 :=
                 DMAPi (bool_rect (fun b:bool => DI2 b -c>DI2 b) f1 f2).

Lemma Dl2_map_eq : forall (f1 : DP1 -c> DP1) (f2:DP2 -c> DP2) (d:Dprodi DI2),
               DI2_map f1 f2 d == pair2 (f1 (pi1 d)) (f2 (pi2 d)).
intros; simpl; apply Oprodi_eq_intro; intro b; case b; trivial.
Save.
End Product2.
Hint Resolve Dl2_map_eq.

Section Product1.
Definition I1 := unit.
Variable D : cpo.

Definition DI1 (_:unit) := D.
Definition PI : Dprodi DI1 -c> D := PROJ DI1 tt.
Definition pi (d:Dprodi DI1) := PI d.

Definition pair1 (d:D) : Dprodi DI1 := unit_rect DI1 d.

Definition pair1_simpl : forall (d:D) (x:unit), pair1 d x = d.
destruct x; trivial.
Defined.

Definition Pair1 : D -m> Dprodi DI1.
exists pair1; red; intros; intro d.
repeat (rewrite pair1_simpl);trivial.
Defined.


Lemma Pair1_simpl : forall (d:D), Pair1 d = pair1 d.
trivial.
Save.

Definition PAIR1 : D -c> Dprodi DI1.
exists Pair1; red; intros; repeat (rewrite Pair1_simpl).
intro d; rewrite pair1_simpl.
rewrite (Dprodi_lub_simpl (Di:=DI1)).
apply lub_le_compat; intros.
intro x; simpl; rewrite pair1_simpl; auto.
Defined.

Lemma pi_simpl : forall  (d:D), pi (pair1 d) = d.
trivial.
Save.

Definition DI1_map (f : D -c> D) 
               : Dprodi DI1 -c> Dprodi DI1 :=
                 DMAPi (fun t:unit => f).

Lemma DI1_map_eq : forall (f : D -c> D) (d:Dprodi DI1),
               DI1_map f d == pair1 (f (pi d)).
intros; simpl; apply Oprodi_eq_intro; intro b; case b; trivial.
Save.
End Product1.

Hint Resolve DI1_map_eq.
End of Stuff *)
