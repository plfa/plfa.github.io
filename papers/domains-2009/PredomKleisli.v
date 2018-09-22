Require Import utility.
Require Import PredomCore.
Require Import PredomProd.
Require Import PredomLift.
Set Implicit Arguments.
Unset Strict Implicit.

Definition kleislit (D0 D1 : cpo) (f: D0 -> D1 _BOT) :=
 cofix kl (l:DL_ord D0) := match l with Eps l => Eps (kl l) | Val d => f d end.

Lemma kleisli_inv : forall (D0 D1:cpo) (f: D0 -> D1 _BOT) (l : D0 _BOT), kleislit f l =
 match l with Eps l' => Eps (kleislit f l')
            | Val d => f d
 end.
intros.
transitivity  (match kleislit f l with Eps x => Eps x | Val d => Val d end).
apply (DL_inv (D:=D1)).
case l.
auto.
intro d.
simpl.
symmetry.
apply DL_inv.
Qed.

(* Monad stuff *)
Lemma left_unit : forall (D0 D1 : cpo) (d:D0) (f : D0 -c> DL D1), kleislit f (Val d) == f d.
intros; auto. rewrite kleisli_inv.
trivial.
Qed.

Lemma kleisli_Eps: forall D E (x : DL D) (f:D -> DL E), kleislit f (Eps x) = Eps (kleislit f x).
intros.
rewrite kleisli_inv. auto.
Qed.

Lemma kleisli_Val: forall (D:cpo) E (d:D) (f:D -> DL E), kleislit f (Val d) = f d.
Proof.
  intros.
  rewrite kleisli_inv.
  auto.
Qed.

(* Revising kleislival to work with nats first cos that'll make the induction work better... *)
Lemma kleislipredValVal : forall (D E : cpo) k (e: tcpo E) (M: DL_ord D) (f : D -> DL E), pred_nth (kleislit f M) k = Val e -> exists d, M == Val d /\ f d == Val e.
induction k.

intros.
 simpl in H.
 rewrite kleisli_inv in H.
 dcase M; intros.
 rewrite H0 in H.
  discriminate.
 rewrite H0 in H.
  exists t.
  split.
  trivial.
  rewrite H; auto.

intros.
 rewrite kleisli_inv in H.
 dcase M; intros.
 rewrite H0 in H.
 simpl pred_nth in H.
 assert (Hfoo := IHk _ _ _ H).
 destruct Hfoo as (d0,(H1,H2)).
 exists d0.
 split.
 rewrite <- H1.
 apply Oeq_sym.
 apply eq_Eps.
 assumption.

 rewrite H0 in H.
 exists t.
 split.
 auto.
 rewrite <- H.
 (* this is bloody obvious, why has auto foresaken me? *)
 Lemma predn_DLeq : forall D n (x:DL_ord D), x == pred_nth x n.
 induction n; intros.
  simpl; auto.
  rewrite pred_nth_Sn.
  set (GRR := pred_nth x n).
  rewrite (IHn x).
  subst GRR.
  apply predeq.
 Qed.

 apply (@predn_DLeq E (S k) (f t)).
Qed.

Lemma kleisli_Valeq: forall (D E:cpo) v (d:D) (f : D -m> E _BOT), v == Val d ->
   kleislit f v == (f d:DL_ord (E)).
Proof.
intros D E v d M veq.
destruct veq as [v1 v2].
destruct (DLle_Val_exists_pred v2) as [n [dd [pd ld]]].
assert (dd == d) as DD. apply Ole_antisym.
assert (xx:=DLle_pred_nth_left). specialize (xx _ n _ _ v1). rewrite pd in xx.
apply vleinj. apply xx. apply ld. clear ld.

assert (M d == M dd). assert (stable M) by auto. unfold stable in H.
apply H. auto. rewrite H. clear d DD H v1 v2.

  generalize dependent v.
  induction n.
  intros v P. simpl in P. rewrite P in *.
  rewrite kleisli_Val. auto.

  intros v P. destruct v.
    rewrite kleisli_Eps.
    simpl in P.
    apply Oeq_trans with (kleislit M v). apply (Oeq_sym (@eq_Eps E (kleislit M v))).
    rewrite (IHn _ P) ; auto.

  inversion P as [Eq]. rewrite Eq in *. simpl in P.
  assert (pred_nth (Val dd) n = Val dd). destruct n ; auto.
  apply (IHn _ H).
Qed.

Hint Resolve DLle_leVal.

Lemma kleisliValVal : forall (D E : cpo) (M: D _BOT) (f : D -c> E _BOT) e,
                kleislit f M == Val e -> exists d, M == Val d /\ f d == Val e.
intros D E M N e [kv1 kv2].
destruct (DLvalval kv2) as [n [d [pd ld]]].
destruct (kleislipredValVal pd) as [md [vm ndm]].
exists md. split. apply vm. refine (Oeq_trans ndm _).
rewrite (kleisli_Valeq (fcontit N) vm) in kv1. rewrite ndm in kv1.
split. apply kv1.
auto.
Qed.

Definition kleislim (D E:cpo) : (D-c> DL E) -> (DL_ord D) -m> DL E.
intros.
exists (kleislit X).
unfold monotonic.
intros x y L. simpl. apply DLless_cond.
intros e C. destruct (kleisliValVal C) as [dd [P Q]].
rewrite (kleisli_Valeq (fcontit X) P).
rewrite P in L.
destruct (DLle_Val_exists_eq L) as [y0 [yv Py]].
rewrite (kleisli_Valeq (fcontit X) yv).
assert (monotonic (fcontit X)) as M by auto.
apply M. auto.
Defined.

Lemma eta_val: forall D f, @eta D f = Val f.
auto.
Qed.

Definition kleisli (D0 D1: cpo) : (D0 -c> DL D1) -> (DL D0) -c> DL D1.
intros D0 D1 f.
exists (kleislim f).
unfold continuous.
intros h.
simpl.
apply DLless_cond.
intros xx C.
destruct (kleisliValVal C) as [x' [P Q]].
rewrite (kleisli_Valeq (fcontit f) P).
apply Ole_trans with (y:=lub (kleislim f <m< h)) ; auto.
clear C Q xx.
destruct (lubval P) as [k [hk [hkv Pk]]].
destruct (DLvalgetchain hkv) as [c Pc].
apply Ole_trans with (y:=((lub (fcontit f <m< c)))).
assert (continuous (fcontit f)) as cf by auto.
rewrite <- (lub_comp_eq c cf).
assert (monotonic f) as M by auto. apply M.
apply vleinj. rewrite <- P.
rewrite <- eta_val.
assert (continuous (fcontit (@eta D0))) as ce by auto.
rewrite (lub_comp_eq c ce).
apply Ole_trans with (y:= lub h) ; auto.
rewrite (lub_lift_left _ k). refine (lub_le_compat _).
apply fmon_le_intro. intros n. destruct (Pc n) ; auto.
rewrite (lub_lift_left (kleislim f <m< h) k).
refine (lub_le_compat _). apply fmon_le_intro.
intros n. repeat (rewrite fmon_comp_simpl).
apply Ole_trans with (y:=kleislit f (h (k+n))) ; auto.
specialize (Pc n). rewrite (kleisli_Valeq (fcontit f) Pc).
auto.
Defined.

Lemma kleisli_simpl (D0 D1: cpo) (f:D0 -c> D1 _BOT) v : kleisli f v = kleislit f v.
auto.
Qed.

Definition Kleisli (D0 D1 : cpo) : (D0 -C-> DL D1) -m> (DL D0) -C-> DL D1.
intros. exists (@kleisli D0 D1).
unfold monotonic.
intros f g fgL x.
simpl. apply DLless_cond.
intros e C. destruct (kleisliValVal C) as [d [P Q]].
rewrite (kleisli_Valeq (fcontit f) P).
rewrite (kleisli_Valeq (fcontit g) P). apply fgL.
Defined.

Lemma Kleisli_simpl (D0 D1 : cpo) (f:D0 -c> D1 _BOT)  : Kleisli _ _ f = kleisli f.
auto.
Qed.

Definition KLEISLI (D0 D1: cpo) : (D0 -C-> DL D1) -c> DL D0 -C-> DL D1.
intros D0 D1. exists (Kleisli D0 D1).
unfold continuous.
intros c. intros d0. simpl.
apply DLless_cond.
intros e C.
destruct (kleisliValVal C) as [d [V hd]].
rewrite (@kleisli_Valeq _ _ _ _ (fcontit (fcont_lub c)) V).
apply Ole_trans with (y:=lub (c <__> d)) ; auto.
apply Ole_trans with (y:=lub (Kleisli D0 D1 <m< c <__> d0)) ; auto.
refine (lub_le_compat _). apply fmon_le_intro. intros n.
repeat (rewrite fcont_app_simpl). rewrite fmon_comp_simpl.
rewrite Kleisli_simpl.
rewrite kleisli_simpl.
rewrite (kleisli_Valeq (fcontit (c n)) V). auto.
Defined.

Add Parametric Morphism (D0 D1:cpo) f : (@kleisli D0 D1 f)
with signature (@Ole (D0 _BOT)) ++> (@Ole (D1 _BOT))
as kleisli_le_compat.
auto.
Qed.

Add Parametric Morphism (D0 D1:cpo) f : (@kleisli D0 D1 f)
with signature (@Oeq (D0 _BOT)) ==> (@Oeq (D1 _BOT))
as kleisli_eq_compat.
intros ; split ; auto.
Qed.

Add Parametric Morphism (D0 D1:cpo) : (KLEISLI D0 D1)
with signature (@Ole (D0 -c> D1 _BOT)) ++> (@Ole (D0 _BOT -C-> D1 _BOT))
as KLEISLI_le_compat.
auto.
Qed.

Add Parametric Morphism (D0 D1:cpo) : (KLEISLI D0 D1)
with signature (@Oeq (D0 -c> D1 _BOT)) ==> (@Oeq (D0 _BOT -C-> D1 _BOT))
as KLEISLI_eq_compat.
intros ; split ; auto.
Qed.

Implicit Arguments KLEISLI [D0 D1].

Lemma KLEISLI_simpl (D0 D1: cpo) (f:D0 -c> D1 _BOT) : KLEISLI f = kleisli f.
auto.
Qed.

Lemma kleislit_comp: forall D E F (f:DL E -c> DL F) (g:D -c> DL E) d,
   (forall x xx, f x == Val xx -> exists y, x == Val y) ->
         kleislit (f << g) d == f (kleislit g d).
intros D E F f g d S. split. simpl.
apply DLless_cond.

intros ff kv.
destruct (kleisliValVal kv) as [dd [dv fdd]].
rewrite (kleisli_Valeq (fcontit (f << g)) dv). rewrite fdd.
assert (f (g dd) == f (kleisli g d)).
assert (stable f) as sf. auto.
unfold stable in sf. apply sf.
rewrite (kleisli_Valeq (fcontit g) dv). auto.
rewrite <- H. auto.

simpl. apply DLless_cond.
intros xx fx.
specialize (S _ _ fx).
destruct S as [e ke].
destruct (kleisliValVal ke) as [dd [de ge]].
rewrite (kleisli_Valeq (fcontit (f << g)) de).
assert (monotonic f) as M by auto.
apply Ole_trans with (y:= (f << g) dd) ; auto.
rewrite fcont_comp_simpl.
apply M. rewrite <- ge in ke.
auto.
Qed.

Lemma kleisli_comp: forall D0 D1 D2 (f:D0 -c> DL D1) (g:D1 -c> DL D2),
       kleisli g << kleisli f == kleisli (kleisli g << f).
intros.
refine (fcont_eq_intro _).
intros d. rewrite fcont_comp_simpl.
repeat (rewrite KLEISLI_simpl).
repeat (rewrite kleisli_simpl).
rewrite kleislit_comp. auto.
intros e ff. rewrite kleisli_simpl.
intros kl. destruct (kleisliValVal kl) as [dd [edd gd]].
exists dd. auto.
Qed.

Lemma kleisli_leq: forall (D E F:cpo) a b (f:D -C-> DL E) (g: F -C-> DL E),
      (forall aa, a == Val aa -> exists bb, b == Val bb /\ f aa <= g bb) ->
   @kleisli D E f a <= @kleisli F E g b.
Proof.
intros D E F a b f g V. simpl. apply DLless_cond.
intros xx [_ kl].
destruct (DLle_Val_exists_pred kl) as [n [dd [pd ld]]].
destruct (kleislipredValVal pd) as [aa [va fa]].
rewrite (kleisli_Valeq (fcontit f) va). specialize (V _ va).
destruct V as [bb [vb fg]]. rewrite (kleisli_Valeq (fcontit g) vb). apply fg.
Qed.

Lemma kleisli_eq: forall (D E F:cpo) a b (f:D -C-> DL E) (g: F -C-> DL E),
      (forall aa, a == Val aa -> exists bb, b == Val bb /\ f aa == g bb) ->
      (forall bb, b == Val bb -> exists aa, a == Val aa /\ f aa == g bb) ->
   @kleisli D E f a == @kleisli F E g b.
Proof.
intros D E F a b f g V1 V2.
apply Ole_antisym.
apply kleisli_leq.
intros aa va. destruct (V1 _ va) as [bb [vb fa]].
exists bb. auto.
apply kleisli_leq. intros bb vb.
destruct (V2 _ vb) as [aa [f1 f2]].
exists aa. auto.
Qed.

Lemma kleisli_eta_com: forall D E f, @kleisli D E f << eta == f.
intros D E f. refine (fcont_eq_intro _).
intros d. rewrite fcont_comp_simpl.
rewrite eta_val. rewrite kleisli_simpl. rewrite kleisli_Val. auto.
Qed.

Lemma kleisli_point_unit: forall (D:cpo) (d:D _BOT), kleisli eta d == d.
intros D d.
split. simpl. apply DLless_cond.

intros dd kl. destruct (kleisliValVal kl) as [d1 [P1 P2]].
assert (eta d1 == Val dd) as P3 by auto. clear P2.
rewrite eta_val in P3. rewrite P3 in P1.
rewrite (kleisli_Valeq (fcontit eta) P1). auto.

simpl. apply DLless_cond.
intros dd kl.
rewrite (kleisli_Valeq (fcontit eta) kl). auto.
Qed.

Lemma kleisli_unit: forall D, kleisli (@eta D) == ID.
intros D. refine (fcont_eq_intro _).
intros d. rewrite ID_simpl. simpl.
assert (xx := kleisli_point_unit). simpl. simpl in xx. apply xx.
Qed.

Lemma kleisli_comp2: forall D E F (f:D -C-> E) (g:E -C-> DL F),
         kleisli (g << f) == kleisli g << kleisli (eta << f).
intros D E F f g.
refine (fcont_eq_intro _).
intros d. repeat (rewrite kleisli_cc_simpl).
rewrite fcont_comp_simpl. repeat (rewrite kleisli_cc_simpl).
refine (kleisli_eq _ _).
intros dd dv. exists (f dd). rewrite fcont_comp_simpl. split ; auto.
rewrite (kleisli_Valeq (fcontit (eta << f)) dv). auto.
intros ee kl.
destruct (kleisliValVal  kl) as [dd P]. exists dd.
split. destruct P ; auto.
rewrite fcont_comp_simpl in *. destruct P as [_ P].
simpl in P.
assert (stable g) as sg by auto. apply sg.
apply (vinj P).
Qed.

Definition mu D := kleisli (@ID (D _BOT)).

Lemma mu_natural D E (f:D -c> E) :
   kleisli (eta << f) << mu _ == mu _ << kleisli (eta << (kleisli (eta << f))).
intros D E f.
unfold mu. rewrite <- kleisli_comp2. rewrite kleisli_comp.
rewrite fcont_comp_unitR. rewrite fcont_comp_unitL.
auto.
Qed.

Lemma mumu D : mu _ << kleisli (eta << mu _) == mu D << mu _.
intros D. unfold mu. rewrite <- kleisli_comp2. rewrite kleisli_comp.
repeat (rewrite fcont_comp_unitL). rewrite fcont_comp_unitR. auto.
Qed.

Lemma mukl D : mu D << kleisli (eta << eta) == ID.
intros D. unfold mu.
rewrite <- kleisli_comp2. rewrite fcont_comp_unitL. rewrite kleisli_unit. auto.
Qed.


(* Now that I've got bottomless cpos, I need ones with bottom for fixpoints.
   Could work with things that are lifted, but that's a bit literal.
   Could work with algebras for the lift monad, but that's probably going to be heavy in Coq
   So I'll just add a new class of things with bottom, like Christine's original cpos but with 
   a new layer of stuff. Hope I can do enough implicit stuff not to make this too disgusting.
*)
(*
Record pcpo : Type := mk_pcpo 
  {tpcpo:>cpo; D0 : tpcpo; Dbot : forall x:tpcpo, D0 <= x}.

Check DL.

Check DL_bot.

Definition Lift (D:cpo) : pcpo.
intro D; exists (DL D) (DL_bot D).
intro.
red. simpl.
apply (DL_bot_least).
Defined.
*)

Record alg : Type := mk_alg
  { acpo :> cpo; strength : DL acpo -c> acpo;
    st_eta : strength << eta == ID;
    st_kl : strength << kleisli (eta << strength) == strength << kleisli ID }.

Definition Aprod : alg -> alg -> alg.
intros A1 A2. exists (Dprod (acpo A1) (acpo A2))
     (<| strength A1 << (kleisli (eta << FST)),
               strength A2 << (kleisli (eta << SND)) |>).
rewrite PROD_fun_compl.
apply (@Dprod_unique A1 A2 (Dprod A1 A2)). rewrite FST_PROD_fun.
rewrite fcont_comp_unitR. rewrite fcont_comp_assoc.
rewrite kleisli_eta_com. rewrite <- fcont_comp_assoc. rewrite st_eta. rewrite fcont_comp_unitL. auto.
rewrite SND_PROD_fun.
rewrite fcont_comp_unitR. rewrite fcont_comp_assoc.
rewrite kleisli_eta_com. rewrite <- fcont_comp_assoc. rewrite st_eta. rewrite fcont_comp_unitL. auto.

refine (@Dprod_unique (acpo A1) (acpo A2) _ _ _ _ _). rewrite <- fcont_comp_assoc.
rewrite FST_PROD_fun. rewrite <- fcont_comp_assoc. rewrite FST_PROD_fun.
rewrite fcont_comp_assoc. rewrite fcont_comp_assoc.
rewrite kleisli_comp. rewrite <- fcont_comp_assoc. rewrite kleisli_eta_com.
rewrite fcont_comp_assoc. rewrite FST_PROD_fun. rewrite kleisli_comp.
rewrite fcont_comp_unitR.
rewrite <- fcont_comp_assoc. rewrite kleisli_comp2. rewrite <- fcont_comp_assoc.
rewrite st_kl. rewrite fcont_comp_assoc. rewrite <- kleisli_comp2. rewrite fcont_comp_unitL.
auto.

rewrite <- fcont_comp_assoc.
rewrite SND_PROD_fun. rewrite <- fcont_comp_assoc. rewrite SND_PROD_fun.
rewrite fcont_comp_assoc. rewrite fcont_comp_assoc.
rewrite kleisli_comp. rewrite <- fcont_comp_assoc. rewrite kleisli_eta_com.
rewrite fcont_comp_assoc. rewrite SND_PROD_fun. rewrite kleisli_comp.
rewrite fcont_comp_unitR.
rewrite <- fcont_comp_assoc. rewrite kleisli_comp2. rewrite <- fcont_comp_assoc.
rewrite st_kl. rewrite fcont_comp_assoc. rewrite <- kleisli_comp2. rewrite fcont_comp_unitL.
auto.
Defined.

Definition AF : cpo -> alg.
intros D. exists (DL D) (kleisli ID).
rewrite kleisli_eta_com. auto.
rewrite <- kleisli_comp2. rewrite fcont_comp_unitL.
rewrite kleisli_comp. rewrite fcont_comp_unitR. auto.
Defined.

Definition Application := fun D0 D1 => curry (uncurry (@KLEISLI (D0 -C-> D1 _BOT) D1) <<
                                       <| curry (uncurry KLEISLI << SWAP) << SND, FST |>).

Definition Operator2 := fun A B C (F:Dprod A B -C-> DL C) =>
  (Application _ _) << (kleisli (eta << (curry F))).

Definition Smash := fun A B => @Operator2 _ _ (Dprod A B) eta.

Definition LStrength := fun A B => uncurry (Smash A _) << eta *f* (@ID (DL B)).
Definition RStrength := fun A B => uncurry (Smash _ B) << (@ID (DL A)) *f* eta.

Definition KLEISLIR := fun A B C (f:Dprod A B -c> DL C) => kleisli f << LStrength A B.
Definition KLEISLIL := fun A B C (f:Dprod A B -c> DL C) => kleisli f << RStrength A B.

Lemma Operator2Val: forall (D E F:cpo) (h:Dprod D E -C-> DL F) d e f,
     Operator2 h d e == Val f -> exists d', exists e', d == Val d' /\ e == Val e' /\ h (d',e') == Val f.
intros D E F h d e f.
unfold Operator2. unfold Application.
repeat (try (rewrite fcont_comp_simpl) ; try (rewrite curry_simpl) ; try (rewrite kliesli_cc_simpl) ;
        try (rewrite PROD_fun_simpl) ; simpl ; try (rewrite FST_simpl) ; try (rewrite SND_simpl) ;
        try (rewrite fcont_comp2_simpl) ; try (rewrite kleisli_c_simpl) ;
        try (rewrite ID_simpl)).
rewrite uncurry_simpl. rewrite KLEISLI_simpl. rewrite kleisli_simpl.
intros c.
destruct (kleisliValVal c) as [f' [cc1 cc2]]. clear c. rewrite curry_simpl in cc2.
rewrite fcont_comp_simpl in cc2. unfold SWAP in cc2. rewrite PROD_fun_simpl in cc2.
rewrite uncurry_simpl in cc2. rewrite SND_simpl, FST_simpl in cc2. simpl in cc2. rewrite KLEISLI_simpl in cc2.
destruct (kleisliValVal cc2) as [e' [eeq feeq]]. clear cc2.
destruct (kleisliValVal cc1) as [d' [deq deeq]]. clear cc1.
rewrite fcont_comp_simpl in *.
exists d'. exists e'. split. auto. split. auto.
rewrite eta_val in *. assert (xx:=fcont_eq_elim (vinj deeq) e'). clear deeq deq eeq. rewrite <- feeq.
rewrite curry_simpl in xx. auto.
Qed.

Lemma Operator2_simpl: forall (E F D:cpo) (f:Dprod E F -C-> DL D) v1 v2,
          Operator2 f (Val v1) (Val v2) == f (v1,v2).
intros E F D f.
intros v1 v2.
unfold Operator2. unfold Application. repeat (rewrite fcont_comp_simpl).
rewrite kleisli_simpl. rewrite kleisli_Val. rewrite curry_simpl.
rewrite fcont_comp_simpl. rewrite PROD_fun_simpl. rewrite uncurry_simpl.
rewrite FST_simpl. simpl. rewrite KLEISLI_simpl.
rewrite kleisli_simpl. repeat (rewrite fcont_comp_simpl). rewrite eta_val. rewrite kleisli_Val.
rewrite SND_simpl. simpl. rewrite curry_simpl. rewrite fcont_comp_simpl.
unfold SWAP. rewrite PROD_fun_simpl. rewrite SND_simpl, FST_simpl. simpl.
rewrite uncurry_simpl. rewrite KLEISLI_simpl. rewrite kleisli_simpl. rewrite kleisli_Val.
auto.
Qed.

Lemma strength_proj D E: kleisli (eta << SND) << LStrength _ _ == @SND E (DL D).
intros D E.
unfold LStrength. unfold Smash. refine (fcont_eq_intro _).
intros p. case p. clear p. simpl. intros u d.
rewrite SND_simpl. simpl. repeat (rewrite fcont_comp_simpl).
rewrite PROD_map_simpl. simpl. rewrite ID_simpl. simpl.
rewrite uncurry_simpl. split.
refine (DLless_cond _). intros dd C.
destruct (kleisliValVal C) as [x [P Pd]].
rewrite fcont_comp_simpl in *. rewrite eta_val in Pd. assert (Pdd:=vinj Pd). clear Pd.
destruct x as [uu x]. rewrite SND_simpl in *. simpl in Pdd.
destruct (Operator2Val P) as [u1 [d1 [_ Pu]]]. clear P C. rewrite eta_val in Pu.
assert (P := vinj (proj2 Pu)). repeat (rewrite eta_val).
assert (Pd := proj1 Pu).
apply Ole_trans with (y:=kleisli (eta << SND) (Operator2 (eta) (Val (D:=E) u) (Val d1))) ; auto.
refine (app_le_compat (Ole_refl _) _). refine (app_le_compat (Ole_refl _) _) ; auto.
rewrite (app_eq_compat (Oeq_refl (kleisli (eta << SND))) (Operator2_simpl (@eta (Dprod E D)) _ _)).
repeat (rewrite eta_val). rewrite kleisli_simpl, kleisli_Val. auto.

refine (DLless_cond _). intros dd V.
rewrite <- (app_eq_compat (Oeq_refl (KLEISLI (eta << SND)))
    (app_eq_compat (Oeq_refl (Operator2 (@eta (Dprod E D)) (@eta E u))) (Oeq_sym V))).
rewrite eta_val. rewrite (app_eq_compat (Oeq_refl (KLEISLI (@eta D << @SND E D)))
                      (Operator2_simpl (@eta (Dprod E D)) _ _)).
rewrite KLEISLI_simpl. rewrite eta_val. rewrite kleisli_simpl, kleisli_Val. auto.
Qed.

Definition assoc D E F := (PROD_fun (FST << FST) (PROD_fun (@SND D E << FST) (@SND _ F))).
Lemma assoc_simpl D E F d e f : assoc D E F (d,e,f) = (d,(e,f)).
auto.
Qed.

Lemma strength_assoc D E F :
  LStrength _ _ << <| FST , LStrength _ _ << SND |> << assoc D E (DL F) ==
  kleisli (eta << assoc _ _ _) << LStrength _ _.
intros D E F. refine (fcont_eq_intro _).
intros p. case p ; clear p. intros p df. case p ; clear p ; intros d e.
repeat (rewrite fcont_comp_simpl). unfold LStrength. repeat (rewrite fcont_comp_simpl).
rewrite assoc_simpl. rewrite PROD_fun_simpl. repeat (rewrite fcont_comp_simpl).
rewrite FST_simpl. simpl. unfold PROD_map.
repeat (rewrite PROD_fun_simpl). repeat (rewrite fcont_comp_simpl). rewrite FST_simpl, SND_simpl, ID_simpl. simpl.
rewrite ID_simpl, SND_simpl. simpl. repeat (rewrite uncurry_simpl).
repeat (rewrite FST_simpl, SND_simpl). rewrite ID_simpl. simpl.
unfold Smash. split.
refine (DLless_cond _). intros p C.
destruct (Operator2Val C) as [dd [ee [ed [Ov Pd]]]].
rewrite eta_val in Pd. assert (PPd := vinj Pd). clear Pd. rewrite eta_val in ed.
assert (Ed := vinj ed). clear ed. rewrite <- Ed in PPd. clear dd Ed.
destruct ee as [ee ff].
destruct (Operator2Val Ov) as [e1 [f1 [Eeq [deq Pe]]]].
rewrite eta_val in *. clear Ov. assert (EEq := vinj Eeq). clear Eeq.
assert (PPe := vinj Pe). clear Pe C.
rewrite (app_eq_compat (Oeq_refl (Operator2 (@eta (Dprod D (Dprod E F))) (Val (D:=D) d)))
     (app_eq_compat (Oeq_refl (Operator2 (@eta (Dprod E F)) (@eta E e))) deq)).
rewrite eta_val.
rewrite (app_eq_compat  (Oeq_refl (Operator2 (@eta (Dprod D (Dprod E F))) (Val (D:=D) d)))(Operator2_simpl _ _ _)).
repeat (rewrite eta_val). rewrite Operator2_simpl.
rewrite (app_eq_compat (Oeq_refl (kleisli (@eta (Dprod D (Dprod E F)) << assoc D E F))) (app_eq_compat (Oeq_refl _) deq)).
rewrite (app_eq_compat (Oeq_refl (kleisli (@eta (Dprod D (Dprod E F)) << assoc D E F)))
         (Operator2_simpl (@eta (Dprod (Dprod D E) F)) _ _)). rewrite kleisli_simpl.
repeat (rewrite eta_val). rewrite kleisli_Val. rewrite fcont_comp_simpl. rewrite assoc_simpl.
auto.

refine (DLless_cond _).
intros p C. rewrite kleisli_simpl in C. destruct (kleisliValVal C) as [pp [OV CC]]. clear C.
destruct (Operator2Val OV) as [p1 [f [fv [def Px]]]].
rewrite eta_val in Px. assert (ppeq := vinj Px). clear Px.
rewrite eta_val in fv. assert (deq := vinj fv). clear fv. clear OV.
rewrite (app_eq_compat (Oeq_refl (kleisli (@eta (Dprod D (Dprod E F)) << assoc D E F))) 
           (app_eq_compat (Oeq_refl (Operator2 (@eta (Dprod (Dprod D E) F)) (@eta (Dprod D E) (d, e)))) def)).
rewrite (app_eq_compat (Oeq_refl (Operator2 (@eta (Dprod D (Dprod E F))) (@eta D d)))
           (app_eq_compat (Oeq_refl (Operator2 (@eta (Dprod E F)) (@eta E e))) def)).
repeat (rewrite eta_val).
rewrite (app_eq_compat (Oeq_refl (kleisli (@eta (Dprod D (Dprod E F)) << assoc D E F))) (Operator2_simpl (@eta (Dprod (Dprod D E) F)) _ _)).
repeat (rewrite eta_val).
rewrite kleisli_simpl, kleisli_Val. rewrite fcont_comp_simpl. 
rewrite (app_eq_compat (Oeq_refl (Operator2 (@eta (Dprod D (Dprod E F))) (Val (D:=D) d))) (Operator2_simpl (@eta (Dprod E F)) _ _)).
repeat (rewrite eta_val). rewrite Operator2_simpl.
auto.
Qed.

Lemma strength_eta D E : LStrength _ _ << PROD_fun (@FST D E) (eta << SND) == eta.
intros D E.
refine (fcont_eq_intro _).
intros p. case p ; clear p.
intros d e. repeat (rewrite fcont_comp_simpl). rewrite PROD_fun_simpl.
rewrite fcont_comp_simpl.
rewrite SND_simpl, FST_simpl. simpl.
unfold LStrength. repeat (rewrite fcont_comp_simpl). unfold PROD_map. rewrite PROD_fun_simpl.
repeat (rewrite fcont_comp_simpl). rewrite SND_simpl, FST_simpl. simpl. rewrite ID_simpl. simpl.
rewrite uncurry_simpl. unfold Smash. repeat (rewrite eta_val). rewrite Operator2_simpl. auto.
Qed.

Lemma strength_tt D E : LStrength _ _ << PROD_fun (@FST D (DL (DL E))) (mu _ << SND) ==
     mu _ << kleisli (eta << LStrength _ _) << LStrength _ _.
intros D E. unfold mu.
rewrite <- kleisli_comp2. rewrite fcont_comp_unitL.
unfold LStrength. rewrite fcont_comp_assoc. rewrite <- PROD_fun_compr. unfold Smash.
refine (fcont_eq_intro _).
intros p ; case p ; clear p ; intros d e.
repeat (rewrite fcont_comp_simpl).
rewrite PROD_fun_simpl. repeat (rewrite fcont_comp_simpl). rewrite uncurry_simpl.
repeat (rewrite ID_simpl). simpl. rewrite FST_simpl, SND_simpl. simpl.
rewrite PROD_map_simpl. simpl. rewrite ID_simpl. rewrite uncurry_simpl. simpl.
repeat (rewrite eta_val).
split. refine (DLless_cond _). intros p. case p ; clear p ; intros dd ee.
intros C. destruct (Operator2Val C) as [d1 [e1 [V1 [k Pe]]]].
assert (dee := vinj V1). clear V1. assert (ddeq := vinj Pe). clear Pe.
rewrite <- dee in ddeq. clear d1 dee. clear C. rewrite kleisli_simpl in k.
destruct (kleisliValVal k) as [e2 [Pe Pee]]. rewrite ID_simpl in Pee. simpl in Pee.
rewrite (app_eq_compat (Oeq_refl (Operator2 (@eta (Dprod D E)) (Val d)))
   (app_eq_compat (Oeq_refl (kleisli ID)) Pe)).
rewrite kleisli_simpl. rewrite kleisli_Val. rewrite ID_simpl.
rewrite (app_eq_compat (Oeq_refl (Operator2 (@eta (Dprod D E)) (Val d))) Pee). rewrite Operator2_simpl.
rewrite (app_eq_compat (Oeq_refl (kleisli (uncurry (Operator2 (@eta (Dprod D E))) << PROD_map (eta) (ID)))) 
  (app_eq_compat (Oeq_refl (Operator2 (@eta (Dprod D (DL E))) (Val d))) Pe)).
rewrite Operator2_simpl.
repeat (rewrite eta_val). rewrite kleisli_simpl. rewrite kleisli_Val.
rewrite fcont_comp_simpl, PROD_map_simpl. rewrite uncurry_simpl. rewrite ID_simpl.
rewrite (app_eq_compat (Oeq_refl (Operator2 eta (eta (d)))) Pee).
rewrite eta_val, Operator2_simpl. auto.

refine (DLless_cond _). intros p ; case p ; clear p ; intros dd ee.
intros C. rewrite kleisli_simpl in C. destruct (kleisliValVal C) as [de [Ov Px]].
destruct de as [d1 e1]. rewrite fcont_comp_simpl in Px. rewrite PROD_map_simpl, uncurry_simpl in Px.
simpl in Ov,Px. rewrite ID_simpl in *. simpl in Px.
destruct (Operator2Val Ov) as [d2 [e2 [deq [eeq Pv]]]].
assert (ddeq := vinj deq). clear deq. clear Ov C.
rewrite eta_val in Pv. assert (peq := vinj Pv). clear Pv.
rewrite <- ddeq in peq. clear d2 ddeq.
rewrite (app_eq_compat (Oeq_refl (Operator2 eta (Val d)))
   (app_eq_compat (Oeq_refl (kleisli ID)) eeq)).
rewrite kleisli_simpl. rewrite kleisli_simpl, kleisli_Val. rewrite ID_simpl.
destruct (Operator2Val Px) as [d3 [e3 [Pe [Pd Q]]]].
assert (stable (@SND D (DL E))) as sf by auto. specialize (sf _ _ peq). repeat (rewrite SND_simpl in sf). simpl in sf.
rewrite <- sf in *. clear sf e1 Px peq.
rewrite (app_eq_compat (Oeq_refl (Operator2 eta (Val d))) Pd). rewrite Operator2_simpl.
rewrite <- kleisli_simpl.
rewrite (app_eq_compat (Oeq_refl (kleisli (uncurry (Operator2 eta) << eta *f* ID))) (app_eq_compat (Oeq_refl (Operator2 eta (Val d))) eeq)).
rewrite Operator2_simpl. rewrite eta_val. rewrite kleisli_simpl.
rewrite kleisli_Val. rewrite fcont_comp_simpl.
rewrite PROD_map_simpl. rewrite uncurry_simpl. rewrite ID_simpl. rewrite eta_val.
rewrite (app_eq_compat (Oeq_refl (Operator2 eta (Val d))) Pd).
rewrite Operator2_simpl. auto.
Qed.

Lemma KLEISLIL_eq (A A' B B' C:cpo) : forall (f:Dprod A B -C-> DL C) (f':Dprod A' B' -C-> DL C)
            a b a' b',
    (forall aa aa', a == Val aa -> a' == Val aa' -> f (aa,b) == f' (aa',b')) ->
    (forall aa, a == Val aa -> exists aa', a' == Val aa') ->
    (forall aa', a' == Val aa' -> exists aa, a == Val aa) ->
  @KLEISLIL A B C f (a,b) == @KLEISLIL A' B' C f' (a',b').
Proof.
intros A A' B B' C f f' a b a' b' V1 V2 V3.
unfold KLEISLIL.
unfold RStrength. repeat (rewrite fcont_comp_simpl).
repeat (rewrite PROD_map_simpl). simpl. repeat (rewrite ID_simpl). simpl.
repeat (rewrite uncurry_simpl). unfold Smash.
refine (kleisli_eq _ _).
intros aa sa.
destruct (Operator2Val sa) as [a1 [b1 [Pa1 [Pb1 pv]]]].
destruct (V2 _ Pa1) as [aa' Paa].
exists (aa', b'). specialize (V1 a1 aa' Pa1 Paa). rewrite <- V1.
rewrite eta_val in *.
split.
refine (Oeq_trans (app_eq_compat (app_eq_compat (Oeq_refl (Operator2 eta)) Paa) (Oeq_refl _)) _).
rewrite Operator2_simpl. auto.
auto.
refine (app_eq_compat (Oeq_refl _) _).
refine (Oeq_trans (Oeq_sym (vinj pv)) _).
refine (pair_eq_compat (Oeq_refl _) _).
apply (Oeq_sym (vinj Pb1)).

intros bb ob. destruct (Operator2Val ob) as [aa' [bb' [av P]]].
specialize (V3 _ av). destruct V3 as [aa va].
specialize (V1 _ _ va av).
exists (aa,b).
split. rewrite eta_val.
refine (Oeq_trans (app_eq_compat (app_eq_compat (Oeq_refl (Operator2 eta)) va) (Oeq_refl (Val b))) _).
rewrite Operator2_simpl. rewrite eta_val. auto.
refine (Oeq_trans V1 _).
refine (app_eq_compat (Oeq_refl _) _).
destruct P as [P1 P2]. rewrite eta_val in P2. refine (Oeq_trans _ (vinj P2)).
rewrite eta_val in P1.
refine (pair_eq_compat (Oeq_refl _) (vinj P1)).
Qed.

Lemma KLEISLIR_eq (A A' B B' C:cpo) : forall (f:Dprod A B -C-> DL C) (f':Dprod A' B' -C-> DL C)
            a b a' b',
    (forall aa aa', b == Val aa -> b' == Val aa' -> f (a,aa) == f' (a',aa')) ->
    (forall aa, b == Val aa -> exists aa', b' == Val aa') ->
    (forall aa', b' == Val aa' -> exists aa, b == Val aa) ->
  @KLEISLIR A B C f (a,b) == @KLEISLIR A' B' C f' (a',b').
Proof.
intros A A' B B' C f f' a b a' b' V1 V2 V3.
unfold KLEISLIR.
unfold LStrength. repeat (rewrite fcont_comp_simpl).
repeat (rewrite PROD_map_simpl). repeat (rewrite ID_simpl).
repeat (rewrite uncurry_simpl). unfold Smash.
refine (kleisli_eq _ _).
intros aa sa.
destruct (Operator2Val sa) as [a1 [b1 [Pa1 [Pb1 pv]]]].
destruct (V2 _ Pb1) as [aa' Paa].
exists (a',aa'). specialize (V1 _ aa' Pb1 Paa). rewrite <- V1.
rewrite eta_val in *.
split.
refine (Oeq_trans (app_eq_compat (Oeq_refl (Operator2 eta (Val a'))) (Paa )) _).
rewrite Operator2_simpl. auto.
refine (app_eq_compat (Oeq_refl _) _).
refine (Oeq_trans (Oeq_sym (vinj pv)) _).
refine (pair_eq_compat _ (Oeq_refl _)).
apply (Oeq_sym (vinj Pa1)).

intros bb ob. destruct (Operator2Val ob) as [aa' [bb' [av [bv P]]]].
specialize (V3 _ bv). destruct V3 as [aa va].
specialize (V1 _ _ va bv).
exists (a,aa).
split. rewrite eta_val.
refine (Oeq_trans (app_eq_compat (Oeq_refl (Operator2 eta (Val a))) va) _).
rewrite Operator2_simpl. rewrite eta_val. auto.
refine (Oeq_trans V1 _).
refine (app_eq_compat (Oeq_refl _) _).
rewrite eta_val in P. refine (Oeq_trans _ (vinj P)).
rewrite eta_val in av.
refine (pair_eq_compat (vinj av) (Oeq_refl _)).
Qed.

Add Parametric Morphism (D E F:cpo) : (@KLEISLIL D E F)
with signature (@Oeq (Dprod D E -c> DL F)) ==> (@Oeq (Dprod (DL D) E -c> DL F))
as KLEISLIL_eq_compat.
intros f0 f1 feq.
apply fcont_eq_intro. intros de. simpl.
unfold KLEISLIL. repeat (rewrite fcont_comp_simpl).
repeat (rewrite kleisli_cc_simpl).
refine (app_eq_compat _ (Oeq_refl _)). rewrite feq. auto.
Qed.

Add Parametric Morphism (D E F:cpo) : (@KLEISLIR D E F)
with signature (@Oeq (Dprod D E -c> DL F)) ==> (@Oeq (Dprod D (DL E) -c> DL F))
as KLEISLIR_eq_compat.
intros f0 f1 feq.
apply fcont_eq_intro. intros de. simpl.
unfold KLEISLIR. repeat (rewrite fcont_comp_simpl).
repeat (rewrite kleisli_cc_simpl). refine (app_eq_compat _ (Oeq_refl _)).
rewrite feq ; auto.
Qed.

Lemma KLEISLIL_comp: forall D E F G (f:Dprod D E -C-> DL F) g h,
        KLEISLIL f << PROD_fun g h == KLEISLIL (f << PROD_map ID h) << PROD_fun g (@ID G).
intros.
apply fcont_eq_intro.
intros gg. repeat (rewrite fcont_comp_simpl).
repeat (rewrite PROD_fun_simpl). rewrite ID_simpl.
simpl. refine (KLEISLIL_eq _ _ _).
intros d0 d1 vd0 vd1. rewrite fcont_comp_simpl. rewrite PROD_map_simpl. simpl. repeat (rewrite ID_simpl). simpl.
rewrite vd0 in vd1. assert (vv:=vinj vd1). assert (stable f) as sf by auto. unfold stable in sf.
apply (sf (d0,h gg) (d1,h gg)). auto.
intros d0 vd0. exists d0. auto. intros aa vv. eexists ; apply vv.
Qed.

Lemma KLEISLIR_comp: forall D E F G (f:Dprod D E -C-> DL F) g h,
        KLEISLIR f << PROD_fun h g == KLEISLIR (f << PROD_map h ID) << PROD_fun (@ID G) g.
intros.
apply fcont_eq_intro.
intros gg. rewrite fcont_comp_simpl. rewrite fcont_comp_simpl.
refine (KLEISLIR_eq _ _ _).
intros d0 d1 vd0 vd1. rewrite fcont_comp_simpl. rewrite PROD_map_simpl. simpl.
rewrite vd0 in vd1. assert (vv:=vinj vd1). assert (stable f) as sf by auto. unfold stable in sf.
apply (sf (h gg,d0) (h gg,d1)). auto.
intros d0 vd0. exists d0. auto. intros aa vv. eexists ; apply vv.
Qed.

Lemma KLEISLIL_unit: forall D E F G (f:Dprod D E -C-> DL F) (g:G -C-> D) h,
    KLEISLIL f << <| eta << g, h |> == f << <| g,  h |>.
intros.
unfold KLEISLIL. unfold RStrength.
repeat (rewrite fcont_comp_assoc).
refine (fcont_eq_intro _). intros gg. unfold PROD_map. repeat (rewrite fcont_comp_simpl). repeat (rewrite PROD_fun_simpl).
rewrite uncurry_simpl. unfold Smash. repeat (rewrite fcont_comp_simpl).
rewrite eta_val. rewrite FST_simpl, ID_simpl. simpl. rewrite SND_simpl, eta_val. simpl.
refine (Oeq_trans (app_eq_compat (Oeq_refl _) (Operator2_simpl _ _ _)) _).
rewrite eta_val. rewrite kleisli_simpl. rewrite kleisli_Val. auto.
Qed.

Lemma KLEISLIR_unit: forall D E F G (f:Dprod E D -C-> DL F) (g:G -C-> D) h,
    KLEISLIR f << PROD_fun h (eta << g) == f << PROD_fun h g.
intros.
unfold KLEISLIR. unfold LStrength.
repeat (rewrite fcont_comp_assoc).
refine (fcont_eq_intro _). intros gg. repeat (rewrite fcont_comp_simpl). repeat (rewrite PROD_map_simpl).
rewrite uncurry_simpl. unfold Smash. rewrite ID_simpl. rewrite eta_val. simpl.
refine (Oeq_trans (app_eq_compat (Oeq_refl _) (Operator2_simpl _ _ _)) _).
rewrite eta_val. rewrite kleisli_simpl. rewrite kleisli_Val. auto.
Qed.

Lemma KLEISLIR_ValVal: forall D E F (f:Dprod D E -C-> DL F) e d r, KLEISLIR f (d,e) == Val r ->
             exists ee, e == Val ee /\ f (d,ee) == Val r.
intros D E F f e d r. unfold KLEISLIR. unfold LStrength.
repeat (rewrite fcont_comp_simpl). rewrite kleisli_simpl.
intros klv. destruct (kleisliValVal klv) as [dd [Pdd PP]].
rewrite PROD_map_simpl in Pdd. rewrite eta_val in Pdd.
simpl in Pdd. rewrite ID_simpl in Pdd. simpl in Pdd.
rewrite uncurry_simpl in Pdd.  unfold Smash in Pdd.
destruct (Operator2Val Pdd) as [d1 [e1 [Pd1 [Pe1 XX]]]]. exists e1.
split. auto. rewrite eta_val in XX. assert (YY:=vinj XX).
assert (stable f) as sf by auto. rewrite <- (vinj Pd1) in YY.
specialize (sf _ _ YY).
refine (Oeq_trans sf PP).
Qed.

Lemma KLEISLIL_ValVal: forall D E F (f:Dprod D E -C-> DL F) e d r, KLEISLIL f (d,e) == Val r ->
             exists dd, d == Val dd /\ f (dd,e) == Val r.
intros D E F f e d r. unfold KLEISLIL. unfold RStrength.
repeat (rewrite fcont_comp_simpl). rewrite kleisli_simpl.
intros klv. destruct (kleisliValVal klv) as [dd [Pdd PP]].
rewrite PROD_map_simpl in Pdd. rewrite eta_val in Pdd.
simpl in Pdd. rewrite ID_simpl in Pdd. simpl in Pdd.
rewrite uncurry_simpl in Pdd.  unfold Smash in Pdd.
destruct (Operator2Val Pdd) as [d1 [e1 [Pd1 [Pe1 XX]]]]. exists d1.
split. auto. rewrite eta_val in XX. assert (YY:=vinj XX).
assert (stable f) as sf by auto. rewrite <- (vinj Pe1) in YY.
specialize (sf _ _ YY).
refine (Oeq_trans sf PP).
Qed.

(*
Definition fcont_alg : cpo -> alg -> alg.
intros D A. exists (D -C-> A) (curry (strength A << (KLEISLIL (eta _ << (EV D A))))).
apply fcont_eq_intro. intros f.
rewrite fcont_comp_simpl. rewrite ID_simpl. simpl.
apply fcont_eq_intro. intros d. rewrite curry_simpl. rewrite fcont_comp_simpl.
assert (kl:=fcont_eq_elim (@KLEISLIL_unit _ _ _ _ (eta A << EV D A) (K _ f) (ID _)) d).
repeat (rewrite fcont_comp_simpl in kl).
assert ((PROD_fun (A:=DL (D -C-> A)) (B:=D) (C:=D)
            (eta (D -C-> A) << K D (D2:=D -C-> A) f) 
            (ID D) d) == (eta (D -C-> A) f, d)) as F by auto.
assert (X:=app_eq_compat (Oeq_refl (KLEISLIL (eta A << EV D A))) F).
rewrite X in kl. clear F X.
rewrite (app_eq_compat (Oeq_refl (strength A)) kl). clear kl.
assert (X:=fcont_eq_elim (st_eta A) (EV D A
           (PROD_fun (A:=D -C-> A) (B:=D) (C:=D) (K D (D2:=D -C-> A) f)
              (ID D) d))). auto.

rewrite curry_compr.
refine (Oeq_sym _).
apply curry_unique.
rewrite fcont_comp_assoc.




apply fcont_eq_intro.
intros f''. repeat (rewrite fcont_comp_simpl).
refine (fcont_eq_intro _). intros d.
repeat (rewrite curry_simpl).
repeat (rewrite fcont_comp_simpl).
assert (X:=st_kl A).

*)

Record fstricti (D1 D2 : cpo) (PD1:Pointed D1) (PD2:Pointed D2) : Type
  := mk_fstricti {fstrictit : D1 -c> D2; fstrict : strict fstrictit}.

Definition fstricti_fun (D1 D2 : cpo) (PD1:Pointed D1) (PD2:Pointed D2) (f:fstricti PD1 PD2) : D1 -> D2 := fun x =>
fstrictit f x.
Coercion fstricti_fun : fstricti >-> Funclass.

Definition fstrict_ord (D1 D2:cpo) (PD1:Pointed D1) (PD2:Pointed D2) : ord.
intros D1 D2 PD1 PD2.
exists (fstricti PD1 PD2) (fun (f g:fstricti PD1 PD2) => fstrictit f <= fstrictit g).
intros; auto.
intros; auto.
apply Ole_trans with (fstrictit y); auto.
Defined.

Infix "-s>" := fstrict_ord (at level 30, right associativity) : O_scope.

(* Now Christine has a whole bunch of auxiliary lemmas for continuous
   maps, which I copy here, assuming they'll turn out to be useful
*)

Lemma fstrict_le_intro : forall (D1 D2:cpo) (PD1:Pointed D1) (PD2:Pointed D2) (f g : PD1 -s> PD2), (forall x, f x <=
 g x) -> f <= g.
trivial.
Save.

Lemma fstrict_le_elim : forall (D1 D2:cpo) (PD1:Pointed D1) (PD2:Pointed D2) (f g : PD1 -s> PD2), f <= g -> forall x
, f x <= g x.
trivial.
Save.

Lemma fstrict_eq_intro : forall (D1 D2:cpo) (PD1:Pointed D1) (PD2:Pointed D2) (f g : PD1 -s> PD2), (forall x, f x ==
 g x) -> f == g.
intros; apply Ole_antisym; apply fstrict_le_intro; auto.
Save.

Lemma fstrict_eq_elim : forall (D1 D2:cpo) (PD1:Pointed D1) (PD2:Pointed D2) (f g : PD1 -s> PD2), f == g -> forall x
, f x == g x.
intros; apply Ole_antisym; apply fstrict_le_elim; auto.
Save.

Lemma fstrict_monotonic : forall (D1 D2:cpo) (PD1:Pointed D1) (PD2:Pointed D2) (f : PD1 -s> PD2) (x y : D1),
            x <= y -> f x <= f y.
intros; apply (fmonotonic (fcontit (fstrictit f)) H).
Save.
Hint Resolve fstrict_monotonic.

Lemma fstrict_stable : forall (D1 D2:cpo) (PD1:Pointed D1) (PD2:Pointed D2) (f : PD1 -s> PD2) (x y : D1),
            x == y -> f x == f y.
intros; apply (fmon_stable (fcontit (fstrictit f)) H).
Save.
Hint Resolve fstrict_monotonic.

Lemma strict_lub  : forall (D1 D2 : cpo) (PD1:Pointed D1) (PD2:Pointed D2)  (f:natO -m> (D1 -c> D2)),
                                        (forall n, strict (f n)) ->
                                         strict  (lub (c:=D1-C->D2) f).
intros. unfold strict.
rewrite fcont_lub_simpl.
split ; auto.
apply lub_le.
intro n.
rewrite fcont_app_simpl.
unfold strict in H.
rewrite (H n).
auto.
Defined.

Definition Fstrictit (D1 D2 : cpo) (PD1:Pointed D1) (PD2:Pointed D2) : (PD1 -s> PD2)-m> (D1-c> D2).
intros D1 D2 PD1 PD2; exists (fstrictit (D1:=D1) (D2:=D2) (PD1:=PD1) (PD2:=PD2)).
auto.
Defined.

Definition fstrict_lub (D1 D2 : cpo) (PD1:Pointed D1) (PD2:Pointed D2) : (natO -m> PD1 -s> PD2) -> (PD1 -s> PD2).
intros D1 D2 PD1 PD2 f.
exists (lub (c:= D1 -C->D2) (Fstrictit PD1 PD2 @ f)).
apply strict_lub.
intros; simpl.
apply (fstrict (f n)).
Defined.

Definition fstrict_cpo (D1 D2:cpo) (PD1:Pointed D1) (PD2:Pointed D2) : cpo.
intros D1 D2 PD1 PD2; exists (fstrict_ord PD1 PD2)
                     (fstrict_lub (D1:=D1) (D2:=D2) (PD1:=PD1) (PD2:=PD2));
simpl;intros; auto.
apply (le_lub (((Fcontit D1 D2 @ (Fstrictit PD1 PD2 @ c)) <_> x))
                  (n)).
Defined.

Infix "-S->" := fstrict_cpo (at level 30, right associativity) : O_scope.

Definition fstrict_comp : forall (D1 D2 D3:cpo) {PD1:Pointed D1} {PD2:Pointed D2} {PD3:Pointed D3}, 
    (PD2 -s> PD3) -> (PD1-s> PD2) -> PD1 -s> PD3.
intros D1 D2 D3 PD1 DP2 PD3 f g.
exists ((fstrictit f) << (fstrictit g)).
red.
rewrite fcont_comp_simpl.
apply Oeq_trans with (fstrictit f (PBot)).
apply fcont_stable.
apply (fstrict g).
apply (fstrict f).
Defined.

Lemma strictVal: forall D E (f:DL D -c> DL E), (forall d e, f d == Val e -> exists dd, d == Val dd) -> strict f.
intros. unfold strict.
split ; auto.

simpl. apply DLless_cond.
intros xx Fx. specialize (H _ _ Fx). destruct H as [d incon].
simpl in incon.
assert (yy := eqValpred incon).
destruct yy as [n [dd [pp _]]].
assert False as F. induction n.
simpl in pp. rewrite DL_bot_eq in pp. inversion pp.
rewrite DL_bot_eq in pp. simpl in pp. auto. inversion F.
Qed.

Lemma kleisli_bot: forall D E (f:D -c> DL E), kleisli f (@PBot (DL D) _) == PBot.
intros.
refine (strictVal (f:=kleisli f) _).
intros d e. rewrite kleisli_simpl.
intros kl. destruct (kleisliValVal kl) as [dd [P _]]. exists dd. auto.
Qed.

