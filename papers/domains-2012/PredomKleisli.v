(**********************************************************************************
 * PredomKleisli.v                                                                *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                       *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)

Require Import PredomCore.
Require Import PredomLift.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition kleislit D E (f: D -> Stream E) :=
(*=kl *)
 cofix kl (l:Stream D) := match l with Eps l => Eps (kl l) | Val d => f d end.
(*=End *)

Lemma kleisli_inv : forall D0 D1 (f: D0 -> Stream D1) (l : Stream D0), kleislit f l =
 match l with Eps l' => Eps (kleislit f l')
            | Val d => f d
 end.
move=> D0 D1 f l.
transitivity  (match kleislit f l with Eps x => Eps x | Val d => Val d end).
apply (DL_inv (D:=D1)).
case l ; auto.
move => d.
simpl.
symmetry.
apply DL_inv.
Qed.

(* Monad stuff *)
Lemma left_unit : forall D0 (D1:ordType) (d:D0) (f : D0 -> Stream D1), kleislit f (Val d) =-= f d.
intros; auto. rewrite kleisli_inv ; auto.
Qed.

Lemma kleisli_Eps: forall D E (x : Stream D) (f:D -> Stream E), kleislit f (Eps x) = Eps (kleislit f x).
intros ; rewrite kleisli_inv. auto.
Qed.

Lemma kleisli_Val: forall D E (d:D) (f:D -> Stream E), kleislit f (Val d) = f d.
Proof.
  intros.
  rewrite kleisli_inv.
  auto.
Qed.

(* Revising kleislival to work with nats first cos that'll make the induction work better... *)
Lemma kleislipredValVal : forall D (E:ordType) k (e:E) (M:lift_ordType D) (f : D -> lift_ordType E),
   pred_nth (kleislit f M) k = Val e -> exists d, M =-= Val d /\ f d =-= Val e.
move => D E. elim.
- move => e M f P.
  simpl in P. rewrite kleisli_inv in P.
  case: M P => t Eq ; first by [].
  exists t. by rewrite Eq.
- move => n IH e M f P.
  rewrite kleisli_inv in P.
  case: M P => t Eq.
  + specialize (IH e t f Eq). case: IH => d [A B]. exists d. split ; last by [].
    by apply (Oeq_trans (predeq (Eps t))).
  + exists t. split ; first by [].
    apply Oeq_sym. apply (@Val_exists_pred_eq _ (f t)). by exists (S n).
Qed.

Lemma kleisli_Valeq: forall (D E:ordType) v (d:D) (f : D =-> lift_ordType E), v =-= Val d ->
   kleislit f v =-= (f d:lift_ordType E).
move => D E v d M. case => [v1 v2].
case: (DLle_Val_exists_pred v2) => n [dd [pd ld]].
have DD:dd =-= d.
- apply Ole_antisym. have xx:=DLle_pred_nth_left n v1. rewrite pd in xx.
  apply vleinj. apply xx. by apply ld.
have X:stable M by []. specialize (X _ _ DD).
rewrite <- X. clear ld DD X d v1 v2.
elim: n v pd.
- move => v. simpl. move => e. rewrite e. by rewrite kleisli_Val.
- move => n IH. case.
  + simpl. move => x e. rewrite -> kleisli_Eps. specialize (IH _ e). rewrite <- IH.
    by apply: (Oeq_trans (predeq _)).
  + move => x. simpl. case => e. rewrite e. by rewrite kleisli_Val.
Qed.

Hint Resolve DLle_leVal.

Lemma kleisli_ValVal : forall D E (M: lift_ordType D) (f : D =-> lift_ordType E) e,
                kleislit f M =-= Val e -> exists d, M =-= Val d /\ f d =-= Val e.
move => D E M N e [kv1 kv2].
case: (DLvalval kv2) => n [d [pd ld]].
case: (kleislipredValVal pd) => md [vm ndm].
exists md. split ; first by [].
refine (Oeq_trans ndm _). move: kv1. rewrite (kleisli_Valeq N vm). rewrite -> ndm.
move => kv1.
split ; first by [].
by apply: DLle_leVal.
Qed.

Lemma kleislit_mono D E (X:D =-> lift_ordType E) : monotonic (kleislit X).
move => x y L. simpl. apply: DLless_cond => e C.
case: (kleisli_ValVal C) => dd [P Q].
rewrite (kleisli_Valeq X P).
rewrite -> P in L.
destruct (DLle_Val_exists_eq L) as [y0 [yv Py]].
rewrite (kleisli_Valeq X yv). by apply fmonotonic.
Qed.

Definition kleislim D E (X:D =-> lift_ordType E) : lift_ordType D =-> lift_ordType E :=
mk_fmono (kleislit_mono X).

Lemma eta_val: forall D f, @eta D f = Val f.
auto.
Qed.

Lemma eta_injp D E (f g :D =-> E) : eta << f =-= eta << g -> f =-= g.
move => C. apply: fmon_eq_intro.
move=> d. assert (X:=fmon_eq_elim C d).
apply: vinj. apply X.
Qed.

Lemma eta_leinjp D E (f g :D =-> E) : eta << f <= eta << g -> f <= g.
move => C d.
assert (X:= C d). apply vleinj. apply X.
Qed.

Lemma kleisli_cont (D0 D1: cpoType) (f:D0 =-> D1 _BOT) : continuous (kleislim f).
unfold continuous.
intros h.
simpl.
apply: DLless_cond.
intros xx C.
destruct (kleisli_ValVal C) as [x' [P Q]].
rewrite (kleisli_Valeq f P).
apply Ole_trans with (y:=@lub (D1 _BOT) (kleislim f << h)) ; auto.
clear C Q xx.
destruct (lubval P) as [k [hk [hkv Pk]]].
destruct (DLvalgetchain hkv) as [c Pc].
apply Ole_trans with (y:=((lub ((f:ordCatType _ _) << c)))).
- assert (continuous f) as cf by auto. rewrite <- cf. apply fmonotonic.
  apply vleinj. rewrite <- P. apply Ole_trans with (y:=eta (lub c)) ; last by [].
  rewrite -> (@lub_comp_eq _ _ eta c).
  rewrite -> (lub_lift_left _ k). refine (lub_le_compat _).
  intros n. by destruct (Pc n) ; auto.
- rewrite -> (@lub_lift_left (D1 _BOT) (kleislim f << h) k).
  refine (lub_le_compat _).
  intros n.
  apply Ole_trans with (y:=kleislit f (h (k+n)%N)) ; last by auto.
  specialize (Pc n). by rewrite -> (kleisli_Valeq f Pc).
Qed.

Definition kleisliX (D0 D1: cpoType) (f:D0 =-> D1 _BOT) : (D0 _BOT) =-> D1 _BOT :=
   Eval hnf in mk_fcont (kleisli_cont f).

Definition kleisli (D0 D1: cpoType) (f:D0 =-> D1 _BOT) : (D0 _BOT) =-> D1 _BOT := locked (kleisliX f).

Lemma kleisliValVal : forall D E (M: D _BOT) (f : D =-> E _BOT) e,
                kleisli f M =-= Val e -> exists d, M =-= Val d /\ f d =-= Val e.
intros D E M N e kv. unlock kleisli in kv.
apply (kleisli_ValVal kv).
Qed.

Lemma kleisli_simpl (D0 D1: cpoType) (f:D0 =-> D1 _BOT) v : kleisli f v = kleislit f v.
by unlock kleisli.
Qed.

Lemma kleisliVal D E d (f:D =-> E _BOT) : kleisli f (Val d) =-= f d.
apply (@Oeq_trans _ _ (kleislit f (Val d))) ; first by unlock kleisli.
by rewrite kleisli_Val.
Qed.

Lemma kleisli_mono (D0 D1 : cpoType) : monotonic (@kleisli D0 D1).
unfold monotonic. move => f g fgL x.
simpl. apply: DLless_cond => e C.
case: (kleisliValVal C) => d [P Q]. unlock kleisli. simpl.
rewrite (kleisli_Valeq f P).
rewrite (kleisli_Valeq g P).
by apply fgL.
Qed.

Definition Kleisli (D0 D1 : cpoType) : ordCatType (D0 -=> D1 _BOT) (D0 _BOT -=> D1 _BOT) :=
Eval hnf in mk_fmono (@kleisli_mono D0 D1).

Lemma Kleisli_simpl (D0 D1 : cpoType) (f:D0 =-> D1 _BOT)  : Kleisli _ _ f = kleisli f.
by [].
Qed.

Lemma Kleisli_cont (D0 D1: cpoType) : continuous (@Kleisli D0 D1).
move => c d0. simpl.
apply: DLless_cond.
intros e C.
destruct (@kleisliValVal D0 D1 d0 ((lub c)) e C) as [d [V hd]]. simpl. unlock kleisli. simpl.
rewrite (@kleisli_Valeq _ _ _ _ ((fcont_lub c)) V). simpl.
refine (lub_le_compat _). move => n. simpl. rewrite -> V. by rewrite kleisliVal.
Qed.

Definition KLEISLI (D0 D1: cpoType) : (D0 -=> D1 _BOT) =-> D0 _BOT -=> D1 _BOT :=
   Eval hnf in mk_fcont (@Kleisli_cont D0 D1).

Add Parametric Morphism (D0 D1:cpoType) : (@kleisli D0 D1)
with signature (@Ole (D0 -=> D1 _BOT)) ++> (@Ole (D0 _BOT -=> D1 _BOT))
as kleisli_le_compat.
move => f f' m. apply: (Ole_trans (y:=KLEISLI _ _ f)) ; first by [].
have X:monotonic (KLEISLI D0 D1) by apply: fmonotonic.
specialize (X _ _ m). by rewrite -> X.
Qed.

Add Parametric Morphism (D0 D1:cpoType) : (@kleisli D0 D1)
with signature (@tset_eq _) ==> (@tset_eq _)
as kleisli_eq_compat.
move => f f' e. split ; [apply (kleisli_le_compat (proj1 e)) | apply (kleisli_le_compat (proj2 e))].
Qed.

Implicit Arguments KLEISLI [D0 D1].

Lemma KLEISLI_simpl (D0 D1: cpoType) (f:D0 =-> D1 _BOT) : KLEISLI f = kleisli f.
auto.
Qed.

Definition total D E (f:D -> lift_ordType E) := forall d, exists e, f d =-= eta_m e.

Definition DLgetelem D (x :lift_ordType  D) (P:exists x', x =-= Val x') : D.
assert (hasVal x). unfold hasVal. destruct P as [x' E].
destruct (eqValpred E) as [n [d [X Eq]]].
exists n. exists d. apply X.
apply (extract (exist (@hasVal D) x H)).
Defined.

Lemma total_mono D (E : ordType) (f:D =-> lift_ordType E) (Tot:total f) : monotonic (fun d => @DLgetelem E (f d) (Tot _)).
move => x y L. apply: extractmono. simpl. assert (monotonic f) as m by auto.
by apply m.
Qed.

Definition totalLmX D (E : ordType) (f:D =-> lift_ordType E) (Tot:total f) : D =-> E :=
  Eval hnf in mk_fmono (total_mono Tot).

Definition totalLm D (E : ordType) (f:D =-> lift_ordType E) (Tot:total f) : D =-> E :=
  locked (totalLmX Tot).

Lemma total_cont (D E : cpoType) (f:D =-> E _BOT) (Tot:total f) : continuous (totalLmX Tot).
unfold continuous. intros c. simpl. apply vleinj.
unfold DLgetelem. rewrite <- extractworks. simpl projj.
rewrite (fcontinuous f). rewrite -> (@lub_comp_eq _ _ eta (totalLmX Tot << c)).
refine (lub_le_compat _) => n. simpl.
apply (Oeq_le). simpl. unfold DLgetelem. simpl. by apply: (Oeq_trans _ (extractworks _)).
Qed.

Definition totalLX (D E :cpoType) (f:D =-> E _BOT) (Tot:total f) : D =-> E :=
  Eval hnf in mk_fcont (total_cont Tot).

Definition totalL (D E :cpoType) (f:D =-> E _BOT) (Tot:total f) : D =-> E := locked (totalLX Tot).

Lemma DLgetelem_eta D (x : lift_ordType D) (P:exists x', x =-= Val x') : Val (DLgetelem P) =-= x.
unfold DLgetelem.
rewrite <- extractworks. simpl. auto.
Qed.

Lemma totalLm_eta D (E :ordType) (f:D =-> lift_ordType E) (Tot:total f) : eta_m << totalLm Tot =-= f.
apply: fmon_eq_intro => n. simpl. unlock totalLm. simpl. by apply DLgetelem_eta.
Qed.

Lemma totalL_eta D (E :cpoType) (f:D =-> E _BOT) (Tot:total f) : eta << totalL Tot =-= f.
assert (x:= totalLm_eta Tot).
apply: fmon_eq_intro.
intros d.
assert (xx := fmon_eq_elim x d).
rewrite <- xx. unlock totalL. by unlock totalLm.
Qed.

Lemma eta_m_total D (f : D =-> lift_ordType D) : f =-= eta_m -> total f.
move => P.
unfold total. intros d.
exists d.
apply (fmon_eq_elim P d).
Qed.

Lemma eta_total D (f : D =-> D _BOT) : f =-= eta -> total f.
move => P.
unfold total. intros d.
exists d.
apply (fmon_eq_elim P d).
Qed.

Lemma totalLm_etap D E (f : D =-> lift_ordType E) (Tot : total f) d : eta_m (totalLm Tot d) =-= f d.
apply (fmon_eq_elim (totalLm_eta Tot) d).
Qed.

Lemma totalL_etap D E (f : D =-> E _BOT) (Tot : total f) d : eta (totalL Tot d) =-= f d.
apply (fmon_eq_elim (totalL_eta Tot) d).
Qed.

Lemma valtotalm D (E :ordType) (f:D =-> lift_ordType E) (Tot:total f) x : Val (totalLm Tot x) =-= f x.
assert (X := fmon_eq_elim (totalLm_eta Tot) x). by apply X.
Qed.

Lemma valtotal D (E :cpoType) (f:D =-> E _BOT) (Tot:total f) x : Val (totalL Tot x) =-= f x.
assert (X := fmon_eq_elim (totalL_eta Tot) x). by apply X.
Qed.

Lemma kleislit_comp: forall D E F (f : E _BOT =-> F _BOT) (g:D =-> E _BOT) d,
   (forall x xx, f x =-= Val xx -> exists y, x =-= Val y) ->
         kleislit (f << g) d =-= f (kleislit g d).
intros D E F f g d S. split. simpl.
apply: DLless_cond.

intros ff kv.
destruct (kleisli_ValVal (f:= (f << g)) kv) as [dd [dv fdd]].
rewrite (kleisli_Valeq ( (f << g)) dv). rewrite -> fdd.
assert (f (g dd) =-= f (kleisli g d)). apply: fmon_stable. rewrite -> dv. by rewrite kleisliVal.
unlock kleisli in H. simpl in H. rewrite <- H. by auto.

simpl. apply: DLless_cond.
intros xx fx.
specialize (S _ _ fx).
destruct S as [e ke].
destruct (kleisli_ValVal ke) as [dd [de ge]].
rewrite (kleisli_Valeq ( (f << g)) de). apply: fmonotonic. rewrite <- ge in ke.
by auto.
Qed.

Lemma kleisli_comp: forall D0 D1 D2 (f:D0 =-> D1 _BOT) (g:D1 =-> D2 _BOT),
       kleisli g << kleisli f =-= kleisli (kleisli g << f).
intros.
refine (fmon_eq_intro _) => d. simpl. unlock {2} kleisli. simpl.
rewrite <- (@kleislit_comp _ _ _ (kleisli g) f d) ; first by unlock kleisli.
intros e ff.
intros kl. destruct (kleisliValVal kl) as [dd [edd gd]].
exists dd. by auto.
Qed.

Lemma kleisli_leq: forall (D E F:cpoType) a b (f:D =-> E _BOT) (g: F =-> E _BOT),
      (forall aa, a =-= Val aa -> exists bb, b =-= Val bb /\ f aa <= g bb) ->
   @kleisli D E f a <= @kleisli F E g b.
Proof.
intros D E F a b f g V. simpl. apply: DLless_cond.
intros xx [_ kl].
destruct (DLle_Val_exists_pred kl) as [n [dd [pd ld]]]. unlock kleisli in pd.
destruct (kleislipredValVal pd) as [aa [va fa]]. rewrite -> va. rewrite kleisliVal.
specialize (V _ va).
destruct V as [bb [vb fg]]. rewrite -> vb. rewrite kleisliVal. by apply fg.
Qed.

Lemma kleisli_eq: forall (D E F:cpoType) a b (f:D =-> E _BOT) (g: F =-> E _BOT),
      (forall aa, a =-= Val aa -> exists bb, b =-= Val bb /\ f aa =-= g bb) ->
      (forall bb, b =-= Val bb -> exists aa, a =-= Val aa /\ f aa =-= g bb) ->
   @kleisli D E f a =-= @kleisli F E g b.
Proof.
intros D E F a b f g V1 V2.
apply: Ole_antisym.
apply kleisli_leq.
intros aa va. destruct (V1 _ va) as [bb [vb fa]].
exists bb. by auto.
apply kleisli_leq. intros bb vb.
destruct (V2 _ vb) as [aa [f1 f2]].
exists aa. by auto.
Qed.

Lemma kleislim_eta_com: forall D E f, @kleislim D E f << eta_m =-= f.
intros D E f. refine (fmon_eq_intro _) => d.
simpl. by rewrite kleisli_Val.
Qed.

Lemma kleisli_eta_com: forall D E f, @kleisli D E f << eta =-= f.
intros D E f.
refine (fmon_eq_intro _) => d. simpl. by apply (kleisliVal d f).
Qed.

Lemma kleisli_point_unit: forall D (d:lift_ordType D), kleislit (eta_m) d =-= d.
intros D d.
split. simpl. apply: DLless_cond.

intros dd kl.
assert (kleislit eta_m d =-= Val dd) as kkl by auto.
destruct (kleisli_ValVal kkl) as [d1 [P1 P2]].
simpl in P2. rewrite -> P2 in P1.
rewrite (kleisli_Valeq (eta_m) P1) ; auto.

simpl. apply: DLless_cond.
intros dd kl.
rewrite (kleisli_Valeq eta_m kl). auto.
Qed.

Lemma kleislim_unit: forall D, kleislim (@eta_m D) =-= Id.
intros D. refine (fmon_eq_intro _) => d. simpl.
by rewrite kleisli_point_unit.
Qed.

Lemma kleisli_unit: forall D, kleisli (@eta D) =-= Id.
intros D. refine (fmon_eq_intro _) => d. unlock kleisli. simpl. by rewrite kleisli_point_unit.
Qed.

Lemma kleisli_comp2: forall D E F (f:D =-> E) (g:E =-> F _BOT),
         kleisli (g << f) =-= kleisli g << kleisli (eta << f).
intros D E F f g.
refine (fmon_eq_intro _) => d.
refine (kleisli_eq _ _).
intros dd dv. exists (f dd). split ; last by  auto.
rewrite -> dv. by rewrite -> (kleisliVal dd (eta << f)).

intros ee kl.
destruct (kleisliValVal  kl) as [dd P]. exists dd.
split. destruct P ; auto. case: P => _ P.
simpl in P. apply: (fmon_stable g). by apply (vinj P).
Qed.

Definition mu D := @kleisli (D _BOT) D Id.

Lemma mu_natural D E (f:D =-> E) :
   kleisli (eta << f) << mu _ =-= mu _ << kleisli (eta << (kleisli (eta << f))).
unfold mu. rewrite <- kleisli_comp2. rewrite -> kleisli_comp.
rewrite -> comp_idR. by rewrite comp_idL.
Qed.

Lemma mumu D : mu _ << kleisli (eta << mu _) =-= mu D << mu _.
unfold mu.
rewrite <- kleisli_comp2. rewrite kleisli_comp. rewrite comp_idL. by rewrite comp_idR.
Qed.

Lemma mukl D : mu D << kleisli (eta << eta) =-= Id.
unfold mu.
rewrite <- kleisli_comp2. rewrite comp_idL. by rewrite kleisli_unit.
Qed.

Definition SWAP (C:prodCat) (X Y : C) : (X * Y) =-> (Y * X) := <| pi2, pi1 |>.
Implicit Arguments SWAP [C X Y].

Definition Application := fun (D0 D1:cpoType) => exp_fun ((uncurry (@KLEISLI (D0 -=> D1 _BOT) D1)) <<
                                       <| exp_fun ((uncurry KLEISLI) << SWAP) << pi2, pi1 |>).

Definition Operator2 := fun A B C (F: A * B =-> C _BOT) =>
  locked ((Application _ _) << (kleisli (eta << (exp_fun F)))).

Definition Smash := fun A B => @Operator2 _ _ (A * B) eta.

Definition LStrength := fun A B => (uncurry  (Smash A B)) << eta >< Id.
Definition RStrength := fun A B => (uncurry (Smash A B)) << Id >< eta.

Definition KLEISLIR := fun A B C (f: A * B =-> C _BOT) => locked (kleisli f << LStrength A B).
Definition KLEISLIL := fun A B C (f: A * B =-> C _BOT) => locked (kleisli f << RStrength A B).

Lemma Operator2Val: forall (D E F:cpoType) (h:D * E =-> F _BOT) d e f,
     Operator2 h d e =-= Val f -> exists d', exists e', d =-= Val d' /\ e =-= Val e' /\ h (d',e') =-= Val f.
intros D E F h d e f. unlock Operator2.
move => X.
destruct (kleisliValVal X) as [f' [cc1 cc2]]. clear X.
destruct (kleisliValVal cc2) as [e' [eeq feeq]]. clear cc2.
destruct (kleisliValVal cc1) as [d' [deq deeq]]. clear cc1. simpl in eeq, feeq.
exists d'. exists e'. split ; first by []. split ; first by []. rewrite <- feeq.
by apply (fmon_eq_elim (vinj deeq) e').
Qed.

Lemma Operator2_simpl: forall (E F D:cpoType) (f:E * F =-> D _BOT) v1 v2,
          Operator2 f (Val v1) (Val v2) =-= f (v1,v2).
move => E F D f v1 v2. unlock Operator2. simpl. rewrite kleisliVal. simpl.
rewrite kleisliVal. simpl. rewrite kleisliVal. by simpl.
Qed.

Lemma strength_proj D E: kleisli (eta << pi2) << LStrength E D =-= pi2.
apply: fmon_eq_intro. case => e d. unfold LStrength. unfold Smash. unlock Operator2.
simpl.
repeat (rewrite kleisliVal ; simpl). unfold id.
apply Oeq_trans with (y:=(kleisli (eta << pi2) << kleisli (eta << PAIR D e)) d) ; first by [].
rewrite kleisli_comp. rewrite comp_assoc. rewrite kleisli_eta_com.
have ee:pi2 << PAIR D e =-= Id by apply: fmon_eq_intro. rewrite <- comp_assoc. rewrite ee.
rewrite comp_idR. by rewrite kleisli_unit.
Qed.

Hint Resolve tset_refl.

Lemma const_post_comp (X Y Z : cpoType) (f:Y =-> Z) e : f << const X e =-= const X (f e).
by apply: fmon_eq_intro.
Qed.

Lemma strength_assoc D E F :
  LStrength _ _ << <| pi1 , LStrength _ _ << pi2 |> << prod_assoc D E (F _BOT) =-=
  kleisli (eta << prod_assoc _ _ _) << LStrength _ _.
unfold LStrength. unfold Smash. do 3 rewrite  <- comp_assoc.
rewrite (comp_assoc (prod_assoc _ _ _)). rewrite prod_map_prod_fun. do 2 rewrite comp_idL.
refine (fmon_eq_intro _). case => p df. case: p => d e. simpl. unlock Operator2. simpl.
repeat rewrite kleisli_Val. unfold id. rewrite (kleisliVal d). simpl.
repeat (rewrite kleisliVal ; simpl).
apply (@Oeq_trans _ _ ((kleisli (eta << PAIR _ d) << (kleisli (eta << PAIR _ e))) df)) ; first by [].
apply Oeq_trans with (y:=(kleisli (eta << prod_assoc _ _ _) << kleisli (eta << PAIR _ (d,e))) df) ; last by [].
rewrite -> kleisli_comp. rewrite comp_assoc. rewrite kleisli_eta_com.
rewrite -> kleisli_comp. rewrite comp_assoc. rewrite kleisli_eta_com.
apply: (fmon_eq_elim _ df). apply: kleisli_eq_compat.
do 2 rewrite <- comp_assoc. refine (comp_eq_compat (tset_refl eta) _). by apply: fmon_eq_intro.
Qed.

Lemma strength_eta D E : LStrength D E << <| pi1, eta << pi2 |> =-= eta.
apply: fmon_eq_intro. case => d e. unfold LStrength. unfold Smash. simpl.
by rewrite Operator2_simpl.
Qed.

Lemma KLEISLIL_eq (A A' B B' C:cpoType) : forall (f:A * B =-> C _BOT) (f': A' * B' =-> C _BOT)
            a b a' b',
    (forall aa aa', a =-= Val aa -> a' =-= Val aa' -> f (aa,b) =-= f' (aa',b')) ->
    (forall aa, a =-= Val aa -> exists aa', a' =-= Val aa') ->
    (forall aa', a' =-= Val aa' -> exists aa, a =-= Val aa) ->
  @KLEISLIL A B C f (a,b) =-= @KLEISLIL A' B' C f' (a',b').
Proof.
intros f f' a b a' b' V1 V2 V3. unlock KLEISLIL. simpl. unfold Smash, id.
refine (kleisli_eq _ _).
intros aa sa.
destruct (Operator2Val sa) as [a1 [b1 [Pa1 [Pb1 pv]]]].
destruct (V2 _ Pa1) as [aa' Paa].
exists (aa', b'). specialize (V1 a1 aa' Pa1 Paa). rewrite <- V1.
split. rewrite -> Paa.
by rewrite Operator2_simpl. have X:=Oeq_sym (vinj pv). rewrite -> X. by rewrite (vinj Pb1).

intros bb ob. destruct (Operator2Val ob) as [aa' [bb' [av P]]].
specialize (V3 _ av). destruct V3 as [aa va].
specialize (V1 _ _ va av).
exists (aa,b).
split. rewrite -> va.
rewrite Operator2_simpl. rewrite eta_val. by auto.
refine (Oeq_trans V1 _). case: P => P1 P2. rewrite <- (vinj P2). by rewrite (vinj P1).
Qed.

Lemma KLEISLIR_eq (A A' B B' C:cpoType) : forall (f:A * B =-> C _BOT) (f': A' * B' =-> C _BOT)
            a b a' b',
    (forall aa aa', b =-= Val aa -> b' =-= Val aa' -> f (a,aa) =-= f' (a',aa')) ->
    (forall aa, b =-= Val aa -> exists aa', b' =-= Val aa') ->
    (forall aa', b' =-= Val aa' -> exists aa, b =-= Val aa) ->
  @KLEISLIR A B C f (a,b) =-= @KLEISLIR A' B' C f' (a',b').
Proof.
intros f f' a b a' b' V1 V2 V3. unlock KLEISLIR.
unfold LStrength. unfold Smash. simpl. unfold id.
refine (kleisli_eq _ _).
intros aa sa.
destruct (Operator2Val sa) as [a1 [b1 [Pa1 [Pb1 pv]]]].
destruct (V2 _ Pb1) as [aa' Paa].
exists (a',aa'). specialize (V1 _ aa' Pb1 Paa). rewrite <- V1.
split. rewrite -> Paa.
by rewrite Operator2_simpl. rewrite <- (vinj pv). by rewrite -> (vinj Pa1).

intros bb ob. destruct (Operator2Val ob) as [aa' [bb' [av [bv P]]]].
specialize (V3 _ bv). destruct V3 as [aa va].
specialize (V1 _ _ va bv).
exists (a,aa).
split. rewrite -> va.
rewrite Operator2_simpl. by auto.
refine (Oeq_trans V1 _). rewrite <- (vinj P). by rewrite (vinj av).
Qed.

Add Parametric Morphism (D E F:cpoType) : (@KLEISLIL D E F)
with signature (@tset_eq (D * E =-> F _BOT)) ==> (@tset_eq (D _BOT * E =-> F _BOT))
as KLEISLIL_eq_compat.
intros f0 f1 feq.
apply: fmon_eq_intro. intros de. unlock KLEISLIL. simpl. by rewrite -> feq.
Qed.

Add Parametric Morphism (D E F:cpoType) : (@KLEISLIR D E F)
with signature (@tset_eq (D * E =-> F _BOT)) ==> (@tset_eq (D * (E _BOT) =-> F _BOT))
as KLEISLIR_eq_compat.
intros f0 f1 feq.
apply: fmon_eq_intro. intros de. unlock KLEISLIR. simpl. by rewrite -> feq.
Qed.

Lemma KLEISLIL_comp D E F G (f:D * E =-> F _BOT) (g:G =-> D _BOT) h :
        KLEISLIL f << <| g, h|> =-= KLEISLIL (f << Id >< h ) << <|g, Id|>.
apply: fmon_eq_intro. simpl. move => gg. unfold id. refine (KLEISLIL_eq _ _ _).
intros d0 d1 vd0 vd1. rewrite -> vd0 in vd1. by rewrite (vinj vd1).
intros d0 vd0. by exists d0. intros aa vv. by eexists ; apply vv.
Qed.

Lemma KLEISLIL_comp2 D E F G H (f:D * E =-> F _BOT) (g:G =-> D) (h:H =-> E) :
        KLEISLIL f << kleisli (eta << g) >< h =-= KLEISLIL (f << g >< h).
apply: fmon_eq_intro. case => gg hh. simpl. apply: KLEISLIL_eq.
- intros d0 d1 vd0 vd1. simpl. rewrite -> vd1 in vd0. rewrite -> kleisliVal in vd0.
  by rewrite -> (vinj vd0).
intros d0 vd0.
destruct (kleisliValVal vd0) as [g0 [ggl P]]. by exists g0.
intros d0 vd0.
exists (g d0). simpl. simpl in vd0. rewrite -> vd0. by rewrite kleisliVal.
Qed.

Lemma KLEISLIR_comp: forall D E F G (f:D * E =-> F _BOT) (g:G =-> E _BOT) h,
        KLEISLIR f << <|h, g|> =-= KLEISLIR (f << h >< Id) << <|Id, g|>.
move => D E F G f g h.
apply: fmon_eq_intro.
intros gg.
refine (KLEISLIR_eq _ _ _).
intros d0 d1 vd0 vd1. simpl. unfold id. rewrite -> vd0 in vd1. by rewrite (vinj vd1).
intros d0 vd0. by exists d0. intros aa vv. by eexists ; apply vv.
Qed.

Lemma KLEISLIL_unit: forall D E F G (f: D * E =-> F _BOT) (g:G =-> D) h,
    KLEISLIL f << <| eta << g, h |> =-= f << <| g,  h |>.
intros.
refine (fmon_eq_intro _). intros gg. unlock KLEISLIL. simpl.  unfold id. unfold Smash. rewrite Operator2_simpl.
simpl. by rewrite kleisliVal.
Qed.

Lemma KLEISLIR_unit: forall D E F G (f:E * D =-> F _BOT) (g:G =-> D) h,
    KLEISLIR f << <| h, eta << g|> =-= f << <| h, g|>.
intros.
refine (fmon_eq_intro _). intros gg. unlock KLEISLIR. simpl. unfold Smash. rewrite Operator2_simpl.
by rewrite kleisliVal.
Qed.

Lemma KLEISLIR_ValVal: forall D E F (f:D * E =-> F _BOT) e d r, KLEISLIR f (d,e) =-= Val r ->
             exists ee, e =-= Val ee /\ f (d,ee) =-= Val r.
intros D E F f e d r. unlock KLEISLIR. simpl. unfold Smash. unfold id.
intros klv. destruct (kleisliValVal klv) as [dd [Pdd PP]].
destruct (Operator2Val Pdd) as [d1 [e1 [Pd1 [Pe1 XX]]]]. exists e1.
split. by auto. rewrite <- (vinj Pd1) in XX. by rewrite -> (vinj XX).
Qed.

Lemma KLEISLIL_ValVal: forall D E F (f: D * E =-> F _BOT) e d r, KLEISLIL f (d,e) =-= Val r ->
             exists dd, d =-= Val dd /\ f (dd,e) =-= Val r.
intros D E F f e d r. simpl. unlock KLEISLIL. simpl. unfold Smash. unfold id.
intros klv. destruct (kleisliValVal klv) as [dd [Pdd PP]].
destruct (Operator2Val Pdd) as [d1 [e1 [Pd1 [Pe1 XX]]]]. exists d1. split ; first by [].
rewrite <- (vinj Pe1) in XX. by rewrite (vinj XX).
Qed.

Lemma Operator2_Valeq D E F (f:D * E =-> F _BOT) d dl e el :
   dl =-= Val d -> el =-= Val e -> Operator2 f dl el =-= f (d,e).
move => X Y. rewrite -> X. rewrite -> Y. by rewrite Operator2_simpl.
Qed.

Lemma KLEISLIL_Valeq D E F (g:D * E =-> F _BOT) dl d e : dl =-= Val d -> KLEISLIL g (dl,e) =-= g (d,e).
move => X. unlock KLEISLIL. simpl. unfold Smash. unfold id. rewrite -> X. rewrite Operator2_simpl.
by rewrite kleisliVal.
Qed.

Lemma KLEISLIL_simpl D E F (g:D * E =-> F _BOT) d e : KLEISLIL g (Val d,e) =-= g (d,e).
intros. refine (KLEISLIL_Valeq g _ (Oeq_refl _)).
Qed.

Lemma KLEISLIL_comp3 D E F G (g : F =-> G _BOT) (f:D * E =-> F) : KLEISLIL (g << f) =-= kleisli g << KLEISLIL (eta << f).
apply:fmon_eq_intro => x. case: x => dl e. simpl.
split ;  apply: DLless_cond.
- intros gg kl. destruct (KLEISLIL_ValVal kl) as [d [Pdl P]]. rewrite -> (pair_eq_compat Pdl (tset_refl e)).
  do 2 rewrite KLEISLIL_simpl. simpl. by rewrite kleisliVal.
- move => gg k. destruct (kleisliValVal k) as [ff [Pk P]].
  destruct (KLEISLIL_ValVal Pk) as [d [dlv Pd]]. rewrite -> (pair_eq_compat dlv (tset_refl e)).
  do 2 rewrite KLEISLIL_simpl. simpl. by rewrite kleisliVal.
Qed.

Lemma KLEISLIL_comp4 D E F G H (f:E * G =-> H _BOT) (g:D =-> E _BOT) (h:F =-> G) :
     KLEISLIL (KLEISLIL f << g >< h) =-= KLEISLIL f << kleisli g >< h.
intros. apply: fmon_eq_intro => x. case: x => dl df.
split ; simpl ; apply: DLless_cond ; unfold id, Smash.
intros hh kh. destruct (KLEISLIL_ValVal kh) as [d0 [dlv Pd]].
destruct (KLEISLIL_ValVal Pd) as [e0 [elv Pe]]. unlock KLEISLIL.
simpl. rewrite -> dlv. rewrite Operator2_simpl. by do 2 rewrite kleisliVal.

intros hh hv. destruct (KLEISLIL_ValVal hv) as [e0 [elv Pe]].
destruct (kleisliValVal elv) as [d0 [dlv Pd]]. unlock KLEISLIL. simpl. rewrite -> dlv. rewrite Operator2_simpl.
do 2 rewrite kleisliVal. simpl. rewrite -> Pd. by rewrite Operator2_simpl.
Qed.

Definition liftCppoType (D:cpoType) := Eval hnf in CppoType (Pointed.class (@liftOrdPointedType D)).

Lemma strictVal: forall D E (f: D _BOT =-> E _BOT), (forall d e, f d =-= Val e -> exists dd, d =-= Val dd) -> strict f.
intros. unfold strict. split ; last by apply: leastP.
simpl. apply: DLless_cond.
intros xxx Fx. specialize (H _ _ Fx). destruct H as [d incon].
simpl in incon.
assert (yy := eqValpred incon).
destruct yy as [n [dd [pp _]]]. have F:False ; last by [].
move: pp. clear. elim: n ; unfold Pointed.least ; simpl.
- by rewrite DL_bot_eq.
- move => n IH X. apply IH. by apply X.
Qed.

Lemma kleisli_bot: forall D E (f:D =-> E _BOT), kleisli f PBot =-= PBot.
intros.
refine (strictVal (f:=kleisli f) _).
intros d e.
intros kl. destruct (kleisliValVal kl) as [dd [P _]]. by exists dd.
Qed.

