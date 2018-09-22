Require Import PredomAll.
Require Import unisem.
Require Import KnasterTarski.
Require Import Sets.

Set Implicit Arguments.
Unset Strict Implicit.

Lemma Oeq_equiv : forall (O:ord), equiv O (@Oeq O).
intros O.
unfold equiv. split. unfold reflexive. auto.
split. unfold transitive. intros x y z xy yz. refine (Oeq_trans xy yz).
unfold symmetric. intros x y xy. refine (Oeq_sym xy).
Qed.

Definition RelKind := Sprod (EqSetKind (Oeq_equiv VInf)) (LeibnizKind Value).

Definition strictV (f:DInf -C-> DInf) := forall d e, Unroll (f (Roll d)) == Val e -> exists d', d == Val d'.

Lemma strictV_eq : forall f g, f == g -> strictV f -> strictV g.
intros f g fg. unfold strictV. intros C d e rr.
specialize (C d e). assert (stable Unroll) as su by auto.
specialize (su _ _ (fcont_eq_elim fg (Roll d))).
apply (C (Oeq_trans su rr)).
Qed.

Lemma strictV_adm: admissible strictV.
unfold admissible. intros f C.
unfold strictV in *.
intros d e R.
assert (continuous (fcontit Unroll)) as cu by auto.
rewrite fcont_lub_simpl in R.
rewrite (lub_comp_eq (f <__> Roll d) cu) in R. clear cu.
destruct (lubval R) as [k [dd [kV dde]]].
specialize (C k d).
rewrite fmon_comp_simpl in kV. rewrite fcont_app_simpl in kV.
specialize (C _ kV). apply C.
Qed.

Definition RelV : set RelKind -> set RelKind -> set RelKind.
intros R S.
exists (fun (p:VInf * Value) => match p with (d,v) =>  match v with 
| NUM m => d == inl _ m
| VAR m => False
| LAMBDA e => exists f, d == inr _ f  /\ strictV f /\
      forall (d1:VInf) (v1:Value), VTyping 0 v1 -> car R (d1,v1) ->
           forall dv, Unroll (f (Roll (Val d1))) == Val dv ->
      exists v2, exists ev : substExp [v1] e =>> v2, car S (dv,v2)
end end).
intros x y ; case x ; clear x ; intros x0 x1 ; case y ; clear y ; intros y0 y1.
simpl. case x1 ; simpl. intros n _ F. inversion F.
case y1. intros n m [_ incon]. inversion incon.
intros n0 n1 [xy num]. inversion num. rewrite H0 in *. clear n1 H0 num. rewrite xy. auto.
intros e n [_ incon]. inversion incon.

case y1 ; clear y1. intros n e [_ incon]. inversion incon.
intros n e [_ incon]. inversion incon.
clear x1. intros e0 e1 [xy L].
inversion L. rewrite H0 in *. clear H0 L e1.
intros C. destruct C as [f [xx [SV P]]].
rewrite xy in xx. exists f. split ; auto.
Defined.

Definition imageD (f:VInf -c> DL VInf) (R S:set RelKind) := 
 (forall x, car R x -> let (d,v) := x in forall dd, (f d) == Val dd -> car S (dd,v)).

Definition RAdm (R : set RelKind) := forall (S : set RelKind)
               (c : natO -m> (VInf -C-> VInf _BOT)), (forall n, imageD (c n) S R) ->
                  imageD (lub c) S R.

Lemma RAdm_inf : forall S : SubsetLattice RelKind -> Prop,
        (forall t : SubsetLattice RelKind, S t -> RAdm t) -> RAdm (inf (SubsetLattice RelKind) S).
intros S C. unfold RAdm in *.
intros R c A. unfold imageD. intros de. case de ; clear de. intros d e Rd dd ldd.
simpl. intros Si SSi.
specialize (C _ SSi R c).
assert ((forall n : natO, imageD (c n) R Si)) as xx.
intros nn. specialize (A nn). simpl in A. unfold imageD in A. unfold imageD.
intros x ; case x ; clear x. intros d1 v1 R1. specialize (A _ R1). simpl in A.
intros dd1 ddv1. specialize (A _ ddv1 _ SSi). apply A.
specialize (C xx). unfold imageD in C.
specialize (C _ Rd _ ldd). apply C.
Qed.

Definition RelAdm := SubLattice (SubsetLattice RelKind) RAdm RAdm_inf.

Definition RelAdmop := op_lat RelAdm.

Lemma ev_determ: forall e v1, e =>> v1 -> forall v2, e =>> v2 -> v1 = v2.
intros v v1 ev. induction ev ; try (intros ; inversion H ; auto ; fail).
intros v3 ev. inversion ev. subst. rewrite <- (IHev1 _ H1) in *. apply (IHev2 _ H3).
Qed.

Lemma sum_right_simpl: forall D E (c:natO -m> Dsum D E) T k e, c k == inr _ e -> sum_right (c:=c) T k == e.
intros D E c T k e. case T. simpl. clear T. intros x c0. clear c0. case_eq (c k). intros t incon1 incon2.
simpl in *. rewrite incon1 in incon2. inversion incon2. inversion H.
intros t ckt ck. simpl. simpl in ckt. rewrite ckt. rewrite ckt in ck. auto.
Qed.

Definition Kab (D1 D2:cpo) : D2 -m> (D1 -C-> D2).
intros D1 D2. exists (fun x => @K D1 D2 x).
unfold monotonic. intros x y. auto.
Defined.

Definition RelVA : RelAdmop -> RelAdm -> RelAdm.
intros R S. case R. clear R. intros R AR. case S. clear S. intros S AS.
exists (RelV R S). unfold RAdm.
simpl. intros A c C.
unfold imageD. intros e ; case e ; clear e. intros d v Ad dd lubdd.
assert (xx:=fcont_lub_simpl c d). simpl in xx. rewrite xx in lubdd. clear xx.
assert (xx:=lubval). specialize (xx _ (c <__> d) dd). specialize (xx lubdd).
destruct xx as [k [dd' [ck Pdd]]].
destruct (DLvalgetchain ck) as [c' Pc'].

generalize Ad. clear Ad.
case v ; clear v. simpl. intros n cA. unfold imageD in C. specialize (C k _ cA). simpl in C.
specialize (Pc' 0). rewrite fcont_app_simpl in Pc'. assert (k+0 = k) as Ar by omega. rewrite Ar in *. clear Ar.
specialize (C _ Pc'). apply C.

intros n cA. simpl. specialize (C k). unfold imageD in C.
rewrite fcont_app_simpl in ck. specialize (C _ cA). simpl in C. specialize (C _ ck).
assert (lub (c <__> d) == Val (lub c')) as lc.
assert (continuous (fcontit (eta (D:=VInf)))) as cv by auto.
rewrite <- eta_val. rewrite (lub_comp_eq c' cv).
refine (Oeq_trans (lub_lift_left (c <__> d) k) _).
refine (lub_eq_compat _). refine (fmon_eq_intro _).
intros m. simpl. apply (Pc' m). simpl in lc. rewrite lc in lubdd.
assert (ll := vinj lubdd). clear lubdd.
rewrite <- ll in *. clear ll. rewrite C in Pdd.
assert (c' 0 == inl (fconti DInf DInf) n).
specialize (Pc' 0). rewrite fcont_app_simpl in Pc'.  assert (k+0 = k) as Ar by omega. rewrite Ar in *. clear Ar.
rewrite ck in Pc'. assert (xx := vinj Pc'). rewrite <- xx. rewrite C. auto.
assert (forall x, @INL (Discrete nat) (DInf -C-> DInf) n <= x -> exists d, x == inl (fconti DInf DInf) d).
intros x. simpl. case x. intros t nt. simpl. exists t ; auto.
intros t FF. inversion FF. specialize (H0 _ Pdd).
destruct H0 as [nn sn].
rewrite sn in Pdd. simpl in Pdd. rewrite <- Pdd in *. apply sn.

simpl.
intros ee Cc. assert (C0 := C k). unfold imageD in C0. specialize (C0 _ Cc). simpl in C0.
rewrite fcont_app_simpl in ck. specialize (C0 _ ck).

destruct (C0) as [f [cf _]].
case (SuminjProof c' 0). intros incon. case incon. clear incon.
intros ff incon.
rewrite cf in *. specialize (Pc' 0). rewrite fcont_app_simpl in Pc'. assert (k+0 = k) as Ar by omega.
rewrite Ar in *. clear Ar. rewrite ck in Pc'. assert (M:=vinj Pc').
simpl in incon. simpl in M. rewrite incon in M. rewrite cf in M. assert (MM:=proj1 M). inversion MM.

intros T. exists (lub (sum_right T)).
assert (dd ==
   inr nat
     (lub (c:=DInf -C-> DInf)
        (sum_right (D1:=Discrete nat) (D2:=DInf -C-> DInf) (c:=c') T))) as ldd.

assert (continuous (fcontit (@INR (Discrete nat) (DInf -C-> DInf)))). auto.
simpl in H. assert (forall x, Inr (Discrete_ord nat) (DInf -c> DInf) x = inr (Discrete nat) x).
intros x. auto. rewrite <- H0. clear H0. rewrite (lub_comp_eq (sum_right T) H).

assert (lub (c <__> d) == Val (lub c')) as lc.
assert (continuous (fcontit (@eta VInf))) as cv by auto.
rewrite <- eta_val. rewrite (lub_comp_eq c' cv).
refine (Oeq_trans (lub_lift_left (c <__> d) k) _).
refine (lub_eq_compat _). refine (fmon_eq_intro _).
intros m. simpl. apply (Pc' m). simpl in lc. rewrite lc in lubdd.
assert (ll := vinj lubdd). clear lubdd.
rewrite <- ll. assert (xx:=@lub_eq_compat _ c'). simpl in xx. simpl. apply xx.
refine (fmon_eq_intro _). intros m. simpl.
assert (exists dd, c' m == inr (Discrete nat) dd). assert (c' 0 <= c' m) as cm.
assert (monotonic c') as cm' by auto. apply cm'. auto. simpl. omega. case T. intros x c'0.
simpl in c'0.
generalize cm. clear cm. case (c' m). intros t incon. simpl in incon. rewrite c'0 in incon. inversion incon.
intros t cm. exists t. auto. destruct H0 as [c'm cm]. 
assert (yy := sum_right_simpl T cm). rewrite cm.  simpl. assert (stable (@INR (Discrete nat) (DInf -C-> DInf))).
auto. simpl in H0. refine (H0 _ _ _). clear H0.
rewrite yy. auto.

split. apply ldd. split.
apply (strictV_adm).
intros n.
specialize (C (k+n)). unfold imageD in C. specialize (C _ Cc). simpl in C.
clear ldd. specialize (Pc' n). rewrite fcont_app_simpl in Pc'.
specialize (C _ Pc'). destruct C as [ff [cr [sf _]]].
refine (strictV_eq (Oeq_sym (sum_right_simpl T cr)) _). apply sf.

intros d1 v1 tv1 Sd1 dv rdv.
assert (continuous (fcontit Unroll)) as Cont by auto.
rewrite fcont_lub_simpl in rdv.
rewrite (lub_comp_eq (sum_right T <__> Roll (@Val VInf d1)) Cont) in rdv.
destruct (lubval rdv) as [kk [dkk [ckk dkkl]]].
destruct (DLvalgetchain ckk) as [c1' cP].
rewrite fmon_comp_simpl in ckk. repeat (rewrite fcont_app_simpl in ckk).

assert (D := C (k+kk)). unfold imageD in D. specialize (D _ Cc). simpl in D.
assert (xx:= Pc' kk). rewrite fcont_app_simpl in xx. specialize (D _ xx).
destruct D as [ff [c0 [Sf P]]].
specialize (P _ _ tv1 Sd1).
assert (cp0:= cP 0).

assert (bla:=sum_right_simpl T c0). rewrite fmon_comp_simpl in cp0.
rewrite fcont_app_simpl in cp0. assert (kk+0 = kk) as KK by omega. rewrite KK in *. clear KK.
assert (stable (fcontit Unroll)) as su by auto.
specialize (su _ _ (fcont_eq_elim bla (Roll (@Val VInf d1)))). rewrite su in cp0.
specialize (P _ cp0). destruct P as [v2 [ev2 S2]].
exists v2. exists ev2. clear bla su cp0 xx S2 Sf c0 ff.

unfold RAdm in AS.
specialize (AS (Inv_image (@snd_set_respect (EqSetKind (Oeq_equiv VInf)) (LeibnizKind Value))
                         (@SingleSet (LeibnizKind Value) v2))).

specialize (AS (Kab VInf _ @ (eta_m _ @ c1'))).
assert ((forall n : natO,
        imageD ((Kab VInf (DL VInf) @ (eta_m VInf @ c1')) n)
            (Inv_image (@snd_set_respect (EqSetKind (Oeq_equiv VInf)) (LeibnizKind Value))
                      (@SingleSet (LeibnizKind Value) v2)) S)) as BLA.
intros n. unfold imageD. simpl. intros x ; case x; clear x. simpl.
intros d0 v0 veq. rewrite <- veq. clear v0 veq. intros d00.
rewrite K_simpl. intros vv. assert (vvv := vinj vv).
assert (@eq_rel RelKind (c1' n,v2) (d00,v2)). simpl. split ; auto.
refine (car_eq H _). clear H vvv vv d00. clear d0.
specialize (C (k+kk+n)).
unfold imageD in C. specialize (C _ Cc). simpl in C.
specialize (cP n).
assert (c (k + kk + n) d == Val (c' (kk + n))).
specialize (Pc' (kk+n)). rewrite fcont_app_simpl in Pc'. rewrite <- Pc'.
assert (k+kk+n = k + (kk+n)) as Ar by omega. rewrite Ar. auto.
specialize (C _ H).
destruct C as [fn [c'n [_ Pn']]].
specialize (Pn' _ _ tv1 Sd1).
rewrite fmon_comp_simpl in cP.
rewrite fcont_app_simpl in cP. clear H.
assert (xx:=sum_right_simpl T c'n).
assert (stable (fcontit Unroll)) as su by auto.
specialize (su _ _ (fcont_eq_elim xx (Roll (@Val VInf d1)))). rewrite su in cP.
clear su xx. specialize (Pn' _ cP).
destruct Pn' as [v3 [ev3 S3]].
rewrite (ev_determ ev3 ev2) in *. clear ev3 v3.
apply S3. specialize (AS BLA).
unfold imageD in AS.
specialize (AS (d,v2)). simpl in AS.
refine (AS _ _ _). auto.
assert (xx := fcont_lub_simpl (Kab VInf (DL VInf) @ (eta_m VInf @ c1')) d).
simpl in xx. rewrite xx. clear xx.
rewrite <- rdv.
assert (aa:=@lub_eq_compat (DL VInf)).
simpl in aa.
refine (Oeq_trans _ (Oeq_sym (lub_lift_left _ kk))).
refine (aa _ _ _). refine (fmon_eq_intro _). intros n.
specialize (cP n). auto using cP.
Defined.

Definition RelVm : ProdLattice RelAdmop RelAdm -m> ProdLattice RelAdmop RelAdm.
exists (fun (p:ProdLattice RelAdmop RelAdm) => 
         (RelVA (LSnd _ _ p) (LFst _ _ p), RelVA (LFst _ _ p) (LSnd _ _ p))).
unfold monotonic. intros x. case x. clear x. intros x0 y0 y. case y. clear y. intros x1 y1.
simpl. case x1. clear x1. intros x1 rx1. case x0. clear x0. intros x0 rx0.
case y0 ; clear y0 ; intros y0 ry0. case y1 ; clear y1 ; intros y1 ry1.
intros [sx sy]. split. simpl.
intros dv. case dv. clear dv. intros d v. simpl. case v. auto. auto.
clear v. intros e C. destruct C as [f [df [sf P]]]. exists f. split ; split ; auto.
intros d1 v1 tv1 y01. specialize (P d1 v1 tv1).
specialize (sy (d1,v1) y01). intros dv rdv. specialize (P sy dv rdv).
destruct P as [v2 [ev2 P]]. exists v2. exists ev2.
apply (sx (dv,v2) P).

simpl.
intros dv. case dv. clear dv. intros d v. simpl.
case v ; auto. clear v. intros v C. destruct C as [f [df [sf C]]].
exists f. split ; split ; auto. intros d1 v1 tv1 c1. specialize (C d1 v1 tv1).
specialize (sx (d1,v1) c1). intros dv dvr. specialize (C sx dv dvr).
destruct C as [v2 [ev2 C]]. exists v2. exists ev2. apply (sy (dv,v2) C).
Defined.

Definition Delta := LSnd _ _ (lfp _ RelVm).
Definition Deltam := LFst _ _ (lfp _ RelVm).

Lemma RelV_fixedD: Delta == (RelVA Deltam Delta).
unfold Delta, Deltam. assert (xx:=lfp_fixedpoint _ RelVm).
generalize xx. clear xx.
case ((lfp (ProdLattice RelAdmop RelAdm) RelVm)).
intros d0 d1. simpl. intros X. inversion X ; inversion H ; inversion H0; auto.
Qed.

Lemma RelV_fixedDm : Deltam == (RelVA Delta Deltam).
unfold Deltam,Delta. assert (xx := lfp_fixedpoint _ RelVm).
generalize xx ;clear xx.
case (lfp (ProdLattice _ _ ) RelVm).
intros d0 d1. simpl. intros X ; inversion X ; inversion H ; inversion H0 ; auto.
Qed.

Lemma RelV_least: forall R S, R <= RelVA S R -> (RelVA R S) <= S ->
                          R <= Deltam /\ Delta <= S.
intros R S.
assert (xx:=lfp_least _ RelVm).
intros Rsub Ssub. simpl in Rsub, Ssub.
assert (RelVm (R,S) <= (R,S)). simpl. split. apply Rsub. apply Ssub.
specialize (xx _ H).
assert (lfp _ RelVm == (Deltam,Delta)) as L.
unfold Deltam, Delta. split ; auto.
rewrite L in xx.
destruct xx ; split ; auto.
Qed.

Lemma BiLift_morph_simpl (F : BiFunctor) (A B C D : cpo) p q :
       BiLift_morph F A B C D p q =
       kleisli (D0:=ob F A C) (D1:=ob F B D) (eta << morph F A B C D p) q.
auto.
Qed.

Lemma RelV_F_action: forall (f:VInf -c> DL VInf) (R S:set RelKind), imageD f R S ->
       imageD ((morph (BiLift (BiSum (BiConst (Discrete nat)) BiArrow)) _ _ _ _ 
                 (Roll << kleisli f << Unroll, Roll << kleisli f << Unroll)) << eta) (RelV S R) (RelV R S).

unfold imageD. simpl. intros f R S C x. case x ; clear x ; intros d v.
intros Bla dd. simpl.
intros L. rewrite fcont_comp_simpl in L.
rewrite (@BiLift_morph_simpl (BiSum (BiConst (Discrete nat)) BiArrow) DInf DInf DInf DInf) in L.
rewrite eta_val in L.
rewrite kleisli_simpl in L. rewrite kleisli_Val in L. rewrite fcont_comp_simpl in L.
rewrite eta_val in L. assert (M:= vinj L). clear L.
generalize Bla. clear Bla.
assert (stable (morph (BiSum (BiConst (Discrete nat)) BiArrow) DInf DInf DInf DInf
     ((Roll << kleisli f) << Unroll, (Roll << kleisli f) << Unroll))) as su. auto.
case v ; auto.

intros n dxn.
specialize (su _ _ dxn). rewrite su in M. rewrite M. auto.

intros e EC.
destruct EC as [ff [dxf [sff EC]]].
specialize (su _ _ dxf). rewrite su in M. clear su.
simpl in M.
rewrite fcont_comp2_simpl in M.
rewrite SUM_map_simpl in M. unfold SUM_map in M.
rewrite SUM_fun_simpl in M. simpl in M.
exists (((Roll << kleisli f) << Unroll) << (ff << ((Roll << kleisli f) << Unroll))). split ; auto. split.
unfold strictV. intros d0 e0. repeat (rewrite fcont_comp_simpl). rewrite UR_eq.
intros B. rewrite kleisli_simpl in B. destruct (kleisliValVal B) as [x [Px fx]].
unfold strictV in sff. specialize (sff _ _ Px).
destruct sff as [d1 sff]. rewrite kleisli_simpl in sff.
destruct (kleisliValVal sff) as [xx [Pxx fxx]]. rewrite UR_eq in Pxx. exists xx. apply Pxx.

intros d1 v1 tv1 car1 dv dvr.
repeat (rewrite fcont_comp_simpl in dvr). rewrite UR_eq in dvr.
rewrite kleisli_simpl in dvr.
destruct (kleisliValVal dvr) as [dx [fx P]]. clear dvr. clear dd M.
assert (stable Unroll) as su by auto. assert (stable ff) as sf by auto.
assert (stable Roll) as sr. unfold stable. apply fcont_stable.
assert ((kleisli f (Unroll (Roll (Val (D:=VInf) d1)))) == f d1).
rewrite UR_eq.
rewrite kleisli_simpl, kleisli_Val. auto.
assert (srr := su _ _ (sf _ _ (sr _ _ H))).
rewrite srr in fx. clear H srr.

unfold strictV in sff. specialize (sff _ _ fx).
destruct sff as [fd1 Pfd1].
assert (CC := C _ car1). simpl in CC. specialize (CC _ Pfd1).
specialize (EC _ _ tv1 CC).
assert (srr := su _ _ (sf _ _ (sr _ _ Pfd1))).
specialize (EC _ (Oeq_trans (Oeq_sym srr) fx)).
destruct EC as [v2 [ev2 EC]]. exists v2. exists ev2.
specialize (C (dx,v2) EC). simpl in C. apply (C _ P).
Qed.

Definition cc:=fcont_COMP _ _ _ Unroll << curry (uncurry (fcont_COMP _ _ _) << SWAP) (Roll << eta).

Lemma cc_simpl: forall f, cc f == (((Unroll << f) << Roll) << eta).
intros f. unfold cc. repeat (rewrite fcont_comp_simpl). rewrite fcont_COMP_simpl.
repeat (rewrite fcont_comp_assoc). refine (fcont_comp_eq_compat (Oeq_refl _) _).
refine (fcont_eq_intro _). intros v. rewrite curry_simpl.
rewrite fcont_comp_simpl. auto.
Qed.

Lemma imageD_eq: forall f g X Y, f == g -> imageD f X Y -> imageD g X Y.
intros f g X Y fg. unfold imageD. intros C. intros x ; case x ; clear x.
intros d v. simpl. specialize (C (d,v)). intros Xd. specialize (C Xd).
simpl in C. intros dd gd. assert (ff := fcont_eq_elim fg d). rewrite <- ff in gd.
specialize (C _ gd). apply C.
Qed.

Definition delta : ((DInf -C-> DInf) -c> (DInf -C-> DInf)) := delta FS.

Lemma delta_simpl : forall e, delta e == Roll << (morph  (BiLift (BiSum (BiConst (Discrete nat)) BiArrow)) _ _ _ _ (e,e)) << Unroll.
intros e. unfold delta. unfold DInf. unfold Unroll, Roll. apply lc.delta_simpl.
Qed.

Lemma Delta_l: Delta == Deltam.
split. apply (proj1 (RelV_least (proj1 RelV_fixedD) (proj1 (RelV_fixedDm)))).
case_eq Delta. intros D AD Deq. case_eq Deltam. intros Dm ADm Dmeq. simpl.
intros dv. case dv. clear dv. intros d v. unfold RAdm in AD.
intros Dmdv. assert (imageD (Unroll << (ID) << Roll << eta) Dm D).
assert (AA:=AD Dm).
assert (admissible (fun (X:DInf -C-> DInf) => imageD (((Unroll << X) << Roll) << eta) Dm D /\
                          X <= ID)) as Ad.
unfold admissible. intros c C1.
split. assert (C := fun n => proj1 (C1 n)). clear C1.
assert (continuous (fcontit cc)) as ccc. auto.
assert (C1:=cc_simpl (lub c)). assert (X:=lub_comp_eq c ccc). assert (X2:=Oeq_trans (Oeq_sym X) C1).
clear X C1. clear ccc.
specialize (AA (fcontit cc @ c)). refine (imageD_eq X2 _).
apply AD. clear AA. intros n. specialize (C n). 
simpl. apply C.
refine (lub_le _). intros n. specialize (C1 n). apply (proj2 C1).
assert ((((Unroll << ID) << Roll) << eta) == 
       (((Unroll << (@FIXP _ (@fun_pointed _ _ (DInf_pointed _)) delta)) << Roll) << eta))
      as BLA.
refine (fcont_comp_eq_compat _ (Oeq_refl _)).
refine (fcont_comp_eq_compat _ (Oeq_refl _)).
refine (fcont_comp_eq_compat (Oeq_refl _) _).
apply id_min.
refine (imageD_eq (Oeq_sym BLA) _). clear BLA.
rewrite FIXP_simpl. rewrite Fixp_simpl.
refine (proj1 (fixp_ind Ad _ _)). unfold imageD. split.
intros x ; case x ; clear x.
intros dd vv. intros ddC d0. repeat (rewrite fcont_comp_simpl).
simpl.
rewrite K_simpl. assert (Unroll (@PBot _ (DInf_pointed _)) == PBot). split ; auto.
assert (xx:=Roll_monic). unfold monic in xx. apply xx. rewrite RU_eq. auto.
simpl in H. rewrite H. intros incon.
destruct incon as [_ incon].
inversion incon. assert False as F. induction n. simpl in H1. rewrite DL_bot_eq in H1. inversion H1.
rewrite DL_bot_eq in H1. simpl in H1. apply (IHn H1).
inversion F. refine (Pleast _).

intros f imaf. split.
Focus 2.
assert (fcontit delta f == delta f). auto. rewrite H. clear H.
refine (Ole_trans (proj1 (delta_simpl f)) _).
destruct imaf as [_ imaf]. assert (monotonic (morph (BiLift (BiSum (BiConst (Discrete nat)) BiArrow)) DInf DInf DInf DInf)) as M by auto.
specialize (M (f,f) (ID,ID)). rewrite morph_id in M.
assert (((f,f) : Dprod (DInf -C-> DInf) (DInf -C-> DInf)) <= (ID, ID)) as fm by auto.
specialize (M fm). clear fm.
assert (xx:=DIso_ru FS). fold Roll in xx. fold Unroll in xx. fold DInf in xx.
assert (Roll << ID << Unroll <= ID). rewrite fcont_comp_unitR. apply (proj1 xx).
refine (Ole_trans _ H). refine (fcont_comp_le_compat _ (Ole_refl Unroll)).
refine (fcont_comp_le_compat (Ole_refl Roll) _). apply M.
Unfocus.
assert ((Unroll << Roll) == ID) as UR_eq by (apply fcont_eq_intro ; intros; rewrite fcont_comp_simpl ; apply UR_eq).

destruct imaf as [imaf fless].
assert (xx := RelV_F_action imaf).
assert ((morph (BiLift (BiSum (BiConst (Discrete nat)) BiArrow)) DInf DInf
            DInf DInf
            ((Roll <<
              kleisli (((Unroll << f) << Roll) << eta)) <<
             Unroll,
            (Roll <<
             kleisli (((Unroll << f) << Roll) << eta)) <<
            Unroll) <<
          eta) == 
     (((Unroll <<
        fcontit delta f) <<
       Roll) << eta)).
simpl morph.
rewrite (@lc.BiLift_morph_simpl (BiSum (BiConst (Discrete nat)) BiArrow)).
rewrite (@kleisli_eta_com (ob (BiSum (BiConst (Discrete nat)) BiArrow) DInf DInf)
            (ob (BiSum (BiConst (Discrete nat)) BiArrow) DInf DInf)).
assert (fcontit delta f = delta f) by auto. rewrite H. clear H.
assert ((morph  (BiLift (BiSum (BiConst (Discrete nat)) BiArrow)) _ _ _ _ (f,f)) << eta == 
                ((Unroll << delta f) << Roll) << eta).
refine (fcont_comp_eq_compat _ (Oeq_refl _)).
rewrite (delta_simpl f).
repeat (rewrite fcont_comp_assoc).
rewrite UR_eq.
rewrite fcont_comp_unitR.
repeat (rewrite <- fcont_comp_assoc). rewrite UR_eq.
rewrite fcont_comp_unitL. apply Oeq_refl.
refine (Oeq_trans _ H).

simpl morph. rewrite (lc.BiLift_morph_simpl (BiSum (BiConst (Discrete nat)) BiArrow)).
rewrite (@kleisli_eta_com (ob (BiSum (BiConst (Discrete nat)) BiArrow) DInf DInf) 
           (ob (BiSum (BiConst (Discrete nat)) BiArrow) DInf DInf)).
refine (fcont_comp_eq_compat (Oeq_refl _) _).

refine (app_eq_compat (@Oeq_refl (Dprod (DInf -C-> DInf) (DInf -C-> DInf) -C-> _) 
 ((SUM_MAP (Discrete nat) (DInf -C-> DInf) (Discrete nat) (DInf -C-> DInf) @2_
    K (Dprod (DInf -C-> DInf) (DInf -C-> DInf))
      (D2:=Discrete nat -C-> Discrete nat) (ID))
     (curry (D1:=Dprod (DInf -C-> DInf) (DInf -C-> DInf))
        (D2:=DInf -C-> DInf) (D3:=DInf -C-> DInf)
        ((fcont_COMP DInf DInf DInf @2_
          @SND (DInf -C-> DInf) (DInf -C-> DInf) <<
          @FST (Dprod (DInf -C-> DInf) (DInf -C-> DInf)) (DInf -C-> DInf))
           ((fcont_COMP DInf DInf DInf @2_
             @SND (Dprod (DInf -C-> DInf) (DInf -C-> DInf)) (DInf -C-> DInf))
              (@FST (DInf -C-> DInf) (DInf -C-> DInf) <<
               @FST (Dprod (DInf -C-> DInf) (DInf -C-> DInf)) (DInf -C-> DInf))))))) _).

assert ((Roll << kleisli (((Unroll << f) << Roll) << eta)) << Unroll == f) as ef.
assert (forall D (f : _ -c> D) g, f << Roll == g << Roll -> f == g).
intros DD ff gg C. assert (CC:= fcont_comp_eq_compat C (Oeq_refl Unroll)). repeat (rewrite fcont_comp_assoc in CC).
assert (Roll << Unroll == ID) as RU_eq by (apply fcont_eq_intro ; intros; rewrite fcont_comp_simpl ; apply RU_eq).
rewrite RU_eq in CC. repeat (rewrite fcont_comp_unitR in CC). apply CC.
apply H0. rewrite fcont_comp_assoc. rewrite UR_eq. rewrite fcont_comp_unitR.
assert (forall D (f : D -c> _) g, Unroll << f == Unroll << g -> f == g).
intros DD ff gg C. assert (CC:= fcont_comp_eq_compat (Oeq_refl Roll) C). repeat (rewrite <- fcont_comp_assoc in CC).
assert (Roll << Unroll == ID) as RU_eq by (apply fcont_eq_intro ; intros; rewrite fcont_comp_simpl ; apply RU_eq).
rewrite RU_eq in CC. repeat (rewrite fcont_comp_unitR in CC). apply CC.
apply H1. rewrite <- fcont_comp_assoc. rewrite UR_eq. rewrite fcont_comp_unitL.
split.
refine (fcont_le_intro _).
intros dd.
refine (DLless_cond _). intros d1. intros C.
destruct (kleisliValVal C) as [x1 [ddv Px]]. rewrite fcont_comp_simpl in Px. rewrite eta_val in Px.
rewrite C. rewrite (app_eq_compat (Oeq_refl (Unroll << (f << Roll))) ddv). rewrite Px. auto.
refine (fcont_le_intro _). intros x.
refine (DLless_cond _). intros x0 C.
assert (yy := proj2 C). rewrite fcont_comp_simpl in yy.
rewrite (app_le_compat (Ole_refl Unroll) (app_le_compat (fcont_comp_le_compat fless (Ole_refl Roll)) (Ole_refl x))) in yy.
rewrite fcont_comp_simpl in yy. rewrite ID_simpl in yy.
assert (Unroll (Roll x) == x) as xa. apply (fcont_eq_elim UR_eq x). rewrite xa in yy.
clear xa. destruct (DLle_Val_exists_eq yy) as [x1 [Px1 PP]].
rewrite kleisli_simpl.
rewrite (kleisli_Valeq (fcontit (((Unroll << f) << Roll) << eta)) Px1).
rewrite (app_eq_compat (Oeq_refl (Unroll << (f << Roll))) Px1). auto.
rewrite (pair_eq_compat2 ef ef). auto.

assert (HH:=imageD_eq H xx).
clear H xx.
assert (X1:=RelV_fixedD).
assert (X2:=RelV_fixedDm).
rewrite Deq in X1, X2. rewrite Dmeq in X1, X2.
assert (D == RelV Dm D) by auto.
assert (Dm == RelV D Dm) by auto.
clear X1 X2.

Lemma imageD_eqS : forall (X Y Z W:set RelKind) f, @Ole (Subsetord RelKind) Z X ->
        @Ole (Subsetord RelKind) Y W -> imageD f X Y -> imageD f Z W.
intros. unfold imageD in *.  intros x ; case x ; clear x. intros d v Zd.
specialize (H1 (d,v)). assert (car X (d,v)) as xx. simpl in H. unfold subset in H.
specialize (H _ Zd). apply H. specialize (H1 xx).
simpl in H1. intros dd fd. specialize (H1 _ fd).
simpl in H0. unfold subset in H0. apply H0. apply H1.
Qed.

refine (imageD_eqS _ _ HH). auto. auto.
unfold imageD in H. specialize (H _ Dmdv). simpl in H.
specialize (H d).  apply H. repeat (rewrite fcont_comp_simpl). rewrite ID_simpl.
simpl.
rewrite UR_eq. rewrite eta_val. auto.
Qed.

Definition LR : set RelKind := match Delta with exist D _ => D end.

Lemma LR_fix: @Oeq (Subsetord RelKind) LR (RelV LR LR) /\ RAdm LR.
unfold LR.
assert (Dfix:=RelV_fixedD). assert (monotonic RelVm). auto.
assert (M:= H (Delta,Delta) (Deltam,Delta)).
specialize (H (Deltam,Delta) (Delta,Delta)).
assert (xx:=Delta_l). split.
assert (((Deltam, Delta) : (ProdLattice RelAdmop RelAdm)) <= (Delta, Delta)).  destruct xx as [X0 X1].
split. auto. auto. specialize (H H0).
assert (((Delta, Delta) : (ProdLattice RelAdmop RelAdm)) <= (Deltam, Delta)). destruct xx as [X0 X1].
split ; auto.
specialize (M H1). clear H0 H1.
generalize H M Dfix xx. clear Dfix xx H M.
case Delta. intros D Rd.
case Deltam. intros Dm RDm.
intros H M Dfix yy.
assert (D == RelV Dm D) by auto.
assert (Dm == D) by auto. clear yy Dfix.
destruct H0 as [S0 S1].
destruct H1 as [S2 S3].
generalize H M. simpl. clear H M.
intros [R0 R1] [R2 R3]. auto. split. refine (Ole_trans S0 _). auto.
refine (Ole_trans _ S1). auto.

case Delta. simpl. auto.
Qed.

Definition ELR := fun ld e, forall d, ld == Val d -> exists v, exists ev:e =>> v, car (RelV LR LR) (d,v).

Lemma ll : forall T sl n i (v:T), length sl = n -> nth_error sl i = Some v -> i < n.
intros T sl. induction sl. intros n i v _ incon.
destruct i ; inversion incon.
intros n. case n. intros i v incon. simpl in incon. inversion incon.
clear n. intros n. simpl. intros i. case i. clear i.
intros ; omega.
clear i. intros i v. simpl. specialize (IHsl n i v).
intros X Y. specialize (IHsl (eq_add_S _ _ X) Y). omega.
Qed.

Lemma car_set_eq : forall T (X Y:set T), @Ole (Subsetord T) X Y -> forall d, car X d -> car Y d.
intros T X Y xyeq d cd.
simpl in *. apply xyeq. apply cd.
Qed.

Lemma RelV_simpl: forall R S d v, car (RelV R S) (d,v) =
 match v with 
| NUM m => d == inl _ m
| VAR m => False
| LAMBDA e => exists f, d == inr _ f  /\ strictV f /\
      forall (d1:VInf) (v1:Value), VTyping 0 v1 -> car R (d1,v1) ->
           forall dv, Unroll (f (Roll (Val d1))) == Val dv ->
      exists v2, exists ev : substExp [v1] e =>> v2, car S (dv,v2)
end. intros R S d v. simpl. case v ; auto.
Qed.

Fixpoint take T (n:nat) (l:list T) :=
match n with
| O => nil
| S n => match l with | nil => nil | (x::xr) => x :: (take n xr) end
end.

Fixpoint drop T (n:nat) (l:list T) :=
match n with
| O => l
| S n => match l with | nil => nil | (x::xr) => drop n xr end
end.

Lemma nth_drop: forall T (ss:list T) n k, nth_error ss (n+k) = nth_error (drop n ss) k.
intros T ss. induction ss. intros n k. case n. simpl. auto.
simpl. case k. simpl. auto.  simpl. auto.
intros n ; case n. simpl. intros k. auto.
clear n. intros n. simpl. auto.
Qed.

Lemma nth_take : forall T (ss:list T) n k, k < n -> nth_error ss k = nth_error (take n ss) k.
intros T ss. induction ss. intros n k. case n ; case k ; simpl ; auto.
intros n. case n. clear n. simpl. intros k incon. inversion incon.
clear n. intros n k. case k. simpl. auto. simpl. clear k.
intros k Sk. apply IHss. omega.
Qed.

Lemma nth_take2 : forall T (ss:list T) n k, k >= n -> nth_error (take n ss) k = error.
intros T ss. induction ss. intros n k. case n ; simpl ; case k ; simpl ; auto.
intros n k. case n ; clear n. simpl. intros _. destruct k ; simpl ; auto.
intros n. simpl. case k. simpl. intros incon. assert False as F by omega. inversion F.
clear k. intros k. simpl. intros X. apply IHss. omega.
Qed.

Lemma take_map: forall T T' (l:list T) n (f : T -> T'), map f (take n l) = take n (map f l).
intros T T' l n f. generalize n. clear n. induction l.
intros n. case n ; simpl ; auto.
intros n ; case n ; simpl. auto. clear n.
intros n. f_equal.  apply IHl.
Qed.

Lemma drop_map : forall T T' (l:list T) n (f: T -> T'), map f (drop n l) = drop n (map f l).
intros T T' l n f. generalize n. clear n. induction l.
intros n ; case n ; simpl ; auto.
intros n ; case n ; clear n ; simpl ; auto.
Qed.

Lemma list_ext : forall T (l1 l2:list T), (forall n, nth_error l1 n = nth_error l2 n) -> l1 = l2.
intros T l1. induction l1. intros l2 ; case l2 ; simpl ; auto.
clear l2. intros t l2. intros C. specialize (C 0). simpl in C. inversion C.
intros l2 ; case l2 ; clear l2. intros C. specialize (C 0). simpl in C. inversion C.
intros t l2. intros C. assert (C0 := C 0). simpl in C0. inversion C0. f_equal.
apply IHl1. intros n. specialize (C (S n)). simpl in C. apply C.
Qed.

Lemma shiftE_commute: forall e k m k' m', (k <= k') %nat ->
     shiftE (k'+m) m' (shiftE k m e) = shiftE k m (shiftE k' m' e).
apply (@Exp_type2 (fun v => forall k m k' m', (k <= k') %nat ->
     shiftV (k'+m) m' (shiftV k m v) = shiftV k m (shiftV k' m' v))
                  (fun e => forall k m k' m', (k <= k') %nat ->
     shiftE (k'+m) m' (shiftE k m e) = shiftE k m (shiftE k' m' e))).
simpl. intros n k m k' m'. intros kk.
case_eq (bleq_nat k n).
intros kn. case_eq (bleq_nat k' n). intros k'n. simpl.
assert (kkn := true_bleq_nat _ _ (sym_eq kn)).
assert (kk'n := true_bleq_nat _ _ (sym_eq k'n)).
assert ((k' + m) <= (n + m)) % nat as A by omega.
rewrite <- (bleq_nat_true _ _ A).
assert (k <= (n+m')) % nat as B by omega.
rewrite <- (bleq_nat_true _ _ B). auto. f_equal. omega.
intros k'n. simpl.
assert (kk'n := false_bleq_nat _ _ (sym_eq k'n)).
assert ((k' + m) > (n + m)) % nat as A by omega.
rewrite <- (bleq_nat_false _ _ A). rewrite kn. auto.
intros kn. assert (kkn := false_bleq_nat _ _ (sym_eq kn)).
assert (k' > n) as A by omega. rewrite <- (bleq_nat_false _ _ A).
simpl. rewrite <- (bleq_nat_false _ _ kkn).
assert (k' + m > n) as B by omega. rewrite <- (bleq_nat_false _ _ B).
auto.

simpl. auto.
simpl. intros e IH k m k' m' kk.
f_equal. specialize (IH (S k) m (S k') m'). simpl in IH. apply IH. omega.
simpl. intros v IH k m k' m' kk. f_equal.
apply IH. auto.

intros v1 IH1 v2 IH2 k m k' m' kk. simpl. f_equal. eapply IH1 ; auto.
eapply IH2 ; auto.

intros e1 IH1 e2 IH2 k m k' m' kk. simpl. f_equal. eapply IH1 ; auto.
specialize (IH2 (S k) m (S k') m'). simpl in IH2.
eapply IH2 ; auto. omega.

intros v IHv e1 IHe1 e2 IH2 k m k' m' kk. simpl.
f_equal. eapply IHv ; auto. eapply IHe1 ; auto. eapply IH2 ; auto.

intros n v IHv vv IHvv k m k' m' kk. simpl. f_equal.
eapply IHv ; auto. eapply IHvv ; auto.
Qed.

Lemma shiftV_commute : forall v k m k' m', (k <= k') %nat ->
     shiftV (k'+m) m' (shiftV k m v) = shiftV k m (shiftV k' m' v).
intros v. induction v. simpl.

intros k m k' m'. intros kk.
case_eq (bleq_nat k n).
intros kn. case_eq (bleq_nat k' n). intros k'n. simpl.
assert (kkn := true_bleq_nat _ _ (sym_eq kn)).
assert (kk'n := true_bleq_nat _ _ (sym_eq k'n)).
assert ((k' + m) <= (n + m)) % nat as A by omega.
rewrite <- (bleq_nat_true _ _ A).
assert (k <= (n+m')) % nat as B by omega.
rewrite <- (bleq_nat_true _ _ B). auto. f_equal. omega.
intros k'n. simpl.
assert (kk'n := false_bleq_nat _ _ (sym_eq k'n)).
assert ((k' + m) > (n + m)) % nat as A by omega.
rewrite <- (bleq_nat_false _ _ A). rewrite kn. auto.
intros kn. assert (kkn := false_bleq_nat _ _ (sym_eq kn)).
assert (k' > n) as A by omega. rewrite <- (bleq_nat_false _ _ A).
simpl. rewrite <- (bleq_nat_false _ _ kkn).
assert (k' + m > n) as B by omega. rewrite <- (bleq_nat_false _ _ B).
auto.

simpl. auto.

simpl. intros k m k' m' kk.
f_equal. assert (S k <= S k') % nat as B by omega.
assert (IH := shiftE_commute e m m' B). apply IH.
Qed.

Lemma subst_shiftE:
 forall n e k ss ss', map (shiftV k n) (take k ss) = take k ss' ->
     map (shiftV k n) (drop k ss) = drop (k+n) ss' ->
   substExp ss' (shiftE k n e) = shiftE k n (substExp ss e).
intros n.
refine (@Exp_type2 (fun v => forall k ss ss', map (shiftV k n) (take k ss) = take k ss' ->
     map (shiftV k n) (drop k ss) = drop (k+n) ss' ->
   substVal ss' (shiftV k n v) = shiftV k n (substVal ss v))
          (fun e => forall k ss ss', map (shiftV k n) (take k ss) = take k ss' ->
     map (shiftV k n) (drop k ss) = drop (k+n) ss' ->
   substExp ss' (shiftE k n e) = shiftE k n (substExp ss e)) _ _ _ _ _ _ _ _).
intros m k ss ss'. simpl.
case_eq (bleq_nat k m).
intros km. simpl. intros _ mm.
assert (xx:=nth_drop ss' (k+n) (m - k)).
assert ((k + n + (m - k)) = (m+n)) as A.
assert (aa:=true_bleq_nat _ _ (sym_eq km)). omega. rewrite A in xx. rewrite xx.
rewrite <- mm. rewrite nth_error_map.
assert (yy:=nth_drop ss k (m - k)). rewrite <- yy.
assert (k+ (m - k) = m) as MM. omega. rewrite MM.
case_eq (nth_error ss m).  auto. simpl. rewrite km. auto.

simpl. intros km. intros mm _.
assert (xx:=nth_take ss' ). assert (kmm := false_bleq_nat _ _ (sym_eq km)).
specialize (xx _ _ kmm). rewrite xx. rewrite <- mm. rewrite nth_error_map.
clear xx. assert (xx := nth_take ss kmm). rewrite <- xx.
case_eq (nth_error ss m). auto. simpl. rewrite km. auto.

intros m k ss ss'. simpl. auto.
intros e IH k ss ss'. simpl.
intros m1 m2. f_equal.
specialize (IH (S k)). apply IH. simpl. f_equal. generalize m1. clear.
intros mm.
refine (list_ext _). intros m. rewrite nth_error_map.
assert (xx:= @nth_take _ (map (shiftV 0 1) ss) k m).
case_eq (bleq_nat k m).
intros km.
assert (yy:=nth_take2 (map (shiftV 0 1) ss)).
assert (A := true_bleq_nat _ _ (sym_eq km)).
specialize (yy _ _ A). rewrite yy. simpl.
rewrite nth_take2. auto. auto.
intros km. assert (A := false_bleq_nat _ _ (sym_eq km)).
specialize (xx A). rewrite <- xx. clear xx.
assert (xx := nth_take (map (shiftV 0 1) ss') A).
rewrite <- xx. clear xx.
rewrite nth_error_map.
rewrite nth_error_map. rewrite (nth_take ss' A).
rewrite <- mm. rewrite nth_error_map. rewrite <- (nth_take ss A).
case (nth_error ss m) ; simpl ; auto.
intros v. f_equal. assert (S k = k + 1) as B by omega. rewrite B.
rewrite shiftV_commute. auto. omega.

generalize m2. clear. intros mm.
refine (list_ext _).
intros m. rewrite nth_error_map.
rewrite <- nth_drop. simpl. rewrite nth_error_map.
rewrite <- nth_drop. rewrite nth_error_map.
assert (xx:= nth_drop ss'). specialize (xx (k+n) m). rewrite xx. rewrite <- mm.
rewrite nth_error_map. rewrite <- nth_drop. case (nth_error ss (k + m)).
intros v. assert (S k = k + 1) as B by omega. rewrite B. f_equal.
rewrite shiftV_commute. auto. omega. simpl. auto.

intros v IH k ss ss' m1 m2. simpl. f_equal.
apply IH. auto. auto.

intros v IHv vv IHvv k ss ss'. simpl. intros m1 m2.
f_equal. eapply IHv ; auto. eapply IHvv ; auto.

intros e IHe ee IHee k ss ss' m1 m2. simpl. f_equal.
eapply IHe ; auto. eapply IHee. simpl. f_equal.

refine (list_ext _). intros m. rewrite nth_error_map.
assert (xx:= @nth_take _ (map (shiftV 0 1) ss) k m).
case_eq (bleq_nat k m).
intros km.
assert (yy:=nth_take2 (map (shiftV 0 1) ss)).
assert (A := true_bleq_nat _ _ (sym_eq km)).
specialize (yy _ _ A). rewrite yy. simpl.
rewrite nth_take2. auto. auto.
intros km. assert (A := false_bleq_nat _ _ (sym_eq km)).
specialize (xx A). rewrite <- xx. clear xx.
assert (xx := nth_take (map (shiftV 0 1) ss') A).
rewrite <- xx. clear xx.
rewrite nth_error_map.
rewrite nth_error_map. rewrite (nth_take ss' A).
rewrite <- m1. rewrite nth_error_map. rewrite <- (nth_take ss A).
case (nth_error ss m) ; simpl ; auto.
intros v. f_equal. assert (S k = k + 1) as B by omega. rewrite B.
rewrite shiftV_commute. auto. omega.

refine (list_ext _).
intros m. rewrite nth_error_map.
rewrite <- nth_drop. simpl. rewrite nth_error_map.
rewrite <- nth_drop. rewrite nth_error_map.
assert (xx:= nth_drop ss'). specialize (xx (k+n) m). rewrite xx. rewrite <- m2.
rewrite nth_error_map. rewrite <- nth_drop. case (nth_error ss (k + m)).
intros v. assert (S k = k + 1) as B by omega. rewrite B. f_equal.
rewrite shiftV_commute. auto. omega. simpl. auto.

intros v IHv e1 IH1 e2 IH2 k ss ss'. simpl. intros m1 m2.
f_equal. eapply IHv ; auto. eapply IH1 ; auto. eapply IH2 ; auto.
intros op v IHv vv IHvv k ss ss' m1 m2. simpl.
f_equal. eapply IHv ; auto. eapply IHvv ; auto.
Qed.

Lemma subst_shiftV:
 forall n v k ss ss', map (shiftV k n) (take k ss) = take k ss' ->
     map (shiftV k n) (drop k ss) = drop (k+n) ss' ->
   substVal ss' (shiftV k n v) = shiftV k n (substVal ss v).
intros n. intros v. induction v.
intros k ss ss'. simpl.
case_eq (bleq_nat k n0).
intros km. simpl. intros _ mm.
assert (xx:=nth_drop ss' (k+n) (n0 - k)).
assert ((k + n + (n0 - k)) = (n0+n)) as A.
assert (aa:=true_bleq_nat _ _ (sym_eq km)). omega. rewrite A in xx. rewrite xx.
rewrite <- mm. rewrite nth_error_map.
assert (yy:=nth_drop ss k (n0 - k)). rewrite <- yy.
assert (k+ (n0 - k) = n0) as MM. omega. rewrite MM.
case_eq (nth_error ss n0).  auto. simpl. rewrite km. auto.

simpl. intros km. intros mm _.
assert (xx:=nth_take ss' ). assert (kmm := false_bleq_nat _ _ (sym_eq km)).
specialize (xx _ _ kmm). rewrite xx. rewrite <- mm. rewrite nth_error_map.
clear xx. assert (xx := nth_take ss kmm). rewrite <- xx.
case_eq (nth_error ss n0). auto. simpl. rewrite km. auto.

intros m k ss ss'. simpl. auto.

intros k ss ss'. simpl.
intros m1 m2. f_equal.
assert (IH := @subst_shiftE n e (S k)).
apply IH. simpl. f_equal. generalize m1. clear.
intros mm.
refine (list_ext _). intros m. rewrite nth_error_map.
assert (xx:= @nth_take _ (map (shiftV 0 1) ss) k m).
case_eq (bleq_nat k m).
intros km.
assert (yy:=nth_take2 (map (shiftV 0 1) ss)).
assert (A := true_bleq_nat _ _ (sym_eq km)).
specialize (yy _ _ A). rewrite yy. simpl.
rewrite nth_take2. auto. auto.
intros km. assert (A := false_bleq_nat _ _ (sym_eq km)).
specialize (xx A). rewrite <- xx. clear xx.
assert (xx := nth_take (map (shiftV 0 1) ss') A).
rewrite <- xx. clear xx.
rewrite nth_error_map.
rewrite nth_error_map. rewrite (nth_take ss' A).
rewrite <- mm. rewrite nth_error_map. rewrite <- (nth_take ss A).
case (nth_error ss m) ; simpl ; auto.
intros v. f_equal. assert (S k = k + 1) as B by omega. rewrite B.
rewrite shiftV_commute. auto. omega.

generalize m2. clear. intros mm.
refine (list_ext _).
intros m. rewrite nth_error_map.
rewrite <- nth_drop. simpl. rewrite nth_error_map.
rewrite <- nth_drop. rewrite nth_error_map.
assert (xx:= nth_drop ss'). specialize (xx (k+n) m). rewrite xx. rewrite <- mm.
rewrite nth_error_map. rewrite <- nth_drop. case (nth_error ss (k + m)).
intros v. assert (S k = k + 1) as B by omega. rewrite B. f_equal.
rewrite shiftV_commute. auto. omega. simpl. auto.
Qed.

Lemma subst_substV:
     forall v n, VTyping n v -> forall sl, length sl >= n ->
     forall ss, substVal ss (substVal sl v) = substVal (map (substVal ss) sl) v.
refine (@Value_type2
 (fun v => forall n, VTyping n v -> forall sl, length sl >= n ->
     forall ss, substVal ss (substVal sl v) = substVal (map (substVal ss) sl) v)
 (fun e => forall n, ETyping n e -> forall sl, length sl >= n ->
     forall ss, substExp ss (substExp sl e) = substExp (map (substVal ss) sl) e)
 _ _ _ _ _ _ _ _).
intros n m. simpl. intros tv. inversion tv. clear tv m0 H.
intros sl l ss.
case_eq (nth_error sl n).
intros v nth. rewrite nth_error_map. rewrite nth. auto.
intros incon. assert False as F. clear ss. assert (n < length sl) as ll by omega.
clear l H0 m. generalize n incon ll. clear n incon ll. induction sl.
simpl. intros n _ incon. inversion incon.
simpl. intros n. case n ; clear n. simpl. intros incon. inversion incon.
intros n. simpl. intros nth sn. specialize (IHsl _ nth (lt_S_n _ _ sn)).
apply IHsl. inversion F.

intros m n tv sl l ss. simpl. auto.

intros e IH n tv sl l ss. simpl.
f_equal.
inversion tv. clear tv H e0.
specialize (IH _ H0 (VAR 0 :: map (shiftV 0 1) sl)).
assert (length (VAR 0 :: map (shiftV 0 1) sl) >= S n) as ll.
simpl. rewrite map_length. omega. specialize (IH ll (VAR 0 :: map (shiftV 0 1) ss)).
rewrite IH. f_equal.
simpl. f_equal.
rewrite map_map. rewrite map_map.
refine (map_ext _ _ _ _).
intros a. assert (ssV:=subst_shiftV).
specialize (ssV 1 a 0 ss). eapply ssV. simpl. auto.
simpl. auto.

intros v IHv n tv sl l ss.
simpl. f_equal. inversion tv. eapply IHv. apply H0. auto.

intros v IHv vv IHvv n ta sl l ss. inversion ta.
simpl. f_equal. eapply IHv. apply H1. auto. eapply IHvv. apply H2. auto.

intros e IHe ee IHee n tl sl l ss.
simpl. inversion tl. 
f_equal.
eapply IHe. apply H1. auto.
specialize (IHee _ H2 (VAR 0 :: map (shiftV 0 1) sl)).
assert (length (VAR 0 :: map (shiftV 0 1) sl) >= S n) as ll.
simpl. rewrite map_length. omega. specialize (IHee ll (VAR 0 :: map (shiftV 0 1) ss)).
rewrite IHee. f_equal.
simpl. f_equal.
rewrite map_map. rewrite map_map.
refine (map_ext _ _ _ _).
intros a. assert (ssV:=subst_shiftV).
specialize (ssV 1 a 0 ss). eapply ssV. simpl. auto.
simpl. auto.

intros v IHv e0 IH0 e1 IH1 n ti sl l ss.
inversion ti. simpl. f_equal. eapply IHv. apply H2. auto.
eapply IH0. apply H3. auto. eapply IH1. apply H4. auto.

intros op v IHv vv IHvv n to sl l ss.
inversion to. simpl. f_equal. eapply IHv. apply H1. auto.
eapply IHvv. apply H3. auto.
Qed.

Lemma subst_substE:
     forall e n, ETyping n e -> forall sl, length sl >= n ->
     forall ss, substExp ss (substExp sl e) = substExp (map (substVal ss) sl) e.
intros e. induction e.

intros n tv sl l ss. simpl.
f_equal. inversion tv. refine (subst_substV H0 _ _ ). auto.

intros n ta sl l ss. inversion ta.
simpl. f_equal. refine (subst_substV H1 _ _) ; auto.
refine (subst_substV H2 _ _ ) ; auto.

intros n tl sl l ss.
simpl. inversion tl. 
f_equal.
eapply IHe1. apply H1. auto.
specialize (IHe2 _ H2 (VAR 0 :: map (shiftV 0 1) sl)).
assert (length (VAR 0 :: map (shiftV 0 1) sl) >= S n) as ll.
simpl. rewrite map_length. omega. specialize (IHe2 ll (VAR 0 :: map (shiftV 0 1) ss)).
rewrite IHe2. f_equal.
simpl. f_equal.
rewrite map_map. rewrite map_map.
refine (map_ext _ _ _ _).
intros a. assert (ssV:=subst_shiftV).
specialize (ssV 1 a 0 ss). eapply ssV. simpl. auto.
simpl. auto.

intros n ti sl l ss.
inversion ti. simpl. f_equal. refine (subst_substV H2 _ _) ; auto.
eapply IHe1. apply  H3. auto. eapply IHe2. apply H4. auto.

intros m to sl l ss.
inversion to. simpl. f_equal. refine (subst_substV H1 _ _) ; auto.
refine (subst_substV H3 _ _) ; auto.
Qed.

Lemma shift_nilV: forall v n, VTyping n v -> forall x, x >= n -> forall m, shiftV x m v = v.
apply (@Value_type2 (fun v => forall n, VTyping n v -> forall x, x >= n -> forall m, shiftV x m v = v)
                    (fun e => forall n, ETyping n e -> forall x, x >= n -> forall m, shiftE x m e = e)).
intros m n tv. inversion tv. simpl. intros x xn mm. assert (x > m) as A by omega.
rewrite <- (bleq_nat_false _ _ A). auto.

intros m n x xn. simpl. auto.
intros e IH n tv x xn m. inversion tv. simpl. f_equal. eapply IH. apply H0. omega.
intros v IH n tv x xn m. inversion tv. simpl. f_equal. eapply IH. apply H0. auto.

intros v IHv vv IHvv n ta x xn m. inversion ta. simpl. f_equal. eapply IHv. apply H1. auto.
eapply IHvv. apply H2. auto.

intros e IHe ee IHee n tl x xn m. inversion tl. simpl. f_equal.
eapply IHe. apply H1. auto. eapply IHee. apply H2. omega.

intros v IHv e0 IH0 e1 IH1. intros n ti x xn m. inversion ti. simpl. f_equal.
eapply IHv. apply H2. auto. eapply IH0. apply H3. auto. eapply IH1. apply H4. auto.

intros op v IHv vv IHvv n to x xn m. inversion to.
simpl. f_equal. eapply IHv. apply H1. auto. eapply IHvv. apply H3. auto.
Qed.

Lemma shift_nilE: forall e n, ETyping n e -> forall x, x >= n -> forall m, shiftE x m e = e.
apply (@Exp_type2 (fun v => forall n, VTyping n v -> forall x, x >= n -> forall m, shiftV x m v = v)
                    (fun e => forall n, ETyping n e -> forall x, x >= n -> forall m, shiftE x m e = e)).
intros m n tv. inversion tv. simpl. intros x xn mm. assert (x > m) as A by omega.
rewrite <- (bleq_nat_false _ _ A). auto.

intros m n x xn. simpl. auto.
intros e IH n tv x xn m. inversion tv. simpl. f_equal. eapply IH. apply H0. omega.
intros v IH n tv x xn m. inversion tv. simpl. f_equal. eapply IH. apply H0. auto.

intros v IHv vv IHvv n ta x xn m. inversion ta. simpl. f_equal. eapply IHv. apply H1. auto.
eapply IHvv. apply H2. auto.

intros e IHe ee IHee n tl x xn m. inversion tl. simpl. f_equal.
eapply IHe. apply H1. auto. eapply IHee. apply H2. omega.

intros v IHv e0 IH0 e1 IH1. intros n ti x xn m. inversion ti. simpl. f_equal.
eapply IHv. apply H2. auto. eapply IH0. apply H3. auto. eapply IH1. apply H4. auto.

intros op v IHv vv IHvv n to x xn m. inversion to.
simpl. f_equal. eapply IHv. apply H1. auto. eapply IHvv. apply H3. auto.
Qed.

Lemma subst_nil:
 (forall v n, VTyping n v -> forall sl,
                             (forall i, i < n -> nth_error sl i = value (VAR i)) ->
                               substVal sl v = v) /\
 forall e n, ETyping n e -> forall sl,
                             (forall i, i < n -> nth_error sl i = value (VAR i)) ->
                               substExp sl e = e.
apply ExpValue_ind.

intros m n tv sl. simpl. inversion tv. intros V. specialize (V _ H0). rewrite V. simpl. auto.

intros m n tv sl C. simpl. auto.

intros e IHe n te sl C. inversion te. simpl. f_equal. specialize (IHe _ H0).
eapply IHe. intros i. case i. simpl. auto. clear i. intros i si. simpl.
specialize (C _ (lt_S_n _ _ si)). rewrite nth_error_map.
rewrite C. simpl. assert (S i = i + 1) as AA by omega. rewrite AA. auto.

intros v IHv n tv sl C. simpl. f_equal. eapply IHv. inversion tv. apply H0. apply C.

intros v IHv vv IHvv n ta sl C. inversion ta. simpl. f_equal. eapply IHv. apply H1. apply C.
eapply IHvv. apply H2. auto.

intros e IHe ee IHee n tl sl C. inversion tl. simpl. f_equal. eapply IHe. apply H1. auto.
eapply IHee. apply H2. intros i. case i. simpl. auto. clear i ; intros i Si. simpl. rewrite nth_error_map.
specialize (C i (lt_S_n _ _ Si)). rewrite C. simpl. assert (i + 1 = S i) as AA by omega. rewrite AA.
auto.

intros v IHv e IHe ee IHee n ti sl C. inversion ti. simpl. f_equal.
eapply IHv. apply H2. apply C. eapply IHe. apply H3. apply C. eapply IHee. apply H4. apply C.

intros op v IHv vv IHvv n to sl C. simpl. inversion to. f_equal. eapply IHv. apply H1. auto.
eapply IHvv. apply H3. auto.
Qed.

Lemma PBot_val_incon: forall D x, DL_bot D == Val (D:=D) x -> False.
intros D x incon. assert (xx := proj2 incon). clear incon.
simpl in xx. inversion xx. subst. clear H1 xx. induction n.
simpl in H0. rewrite DL_bot_eq in H0. inversion H0.
rewrite DL_bot_eq in H0. simpl in H0. apply (IHn H0).
Qed.

Lemma Adequacy : 
(forall n v (tv: VTyping n v) sl d (l:length sl = n),
       (forall i v, nth_error sl i = Some v -> VTyping 0 v) ->
       (forall i v (nth: nth_error sl i = Some v), car LR (projenv (ll l nth) d, v)) ->
           car (RelV LR LR) (SemVal tv d, substVal sl v)) /\
forall n e (te: ETyping n e) sl d (l:length sl = n),
       (forall i v, nth_error sl i = Some v -> VTyping 0 v) ->
       (forall i v (nth: nth_error sl i = Some v), car LR (projenv (ll l nth) d, v)) ->
           ELR (SemExp te d) (substExp sl e).
refine (Typing_ind _ _ _ _ _ _ _ _).
intros n m l sl d le ST C.
specialize (C m).
case_eq (nth_error sl m). intros v nth.
specialize (C v nth).
refine (car_set_eq (proj1 (proj1 LR_fix)) _).

simpl. intros X Y. simpl in C. specialize (C _ Y). simpl in C. rewrite nth. clear Y.
refine (car_eq _ C). simpl. split ; auto.
refine (fcont_eq_elim (@projenv_irr n m _ _) d).

intros incon. assert False as F.
rewrite <- le in l.
destruct (nth_error_lengthI _ l) as [e incon2]. rewrite incon in incon2. inversion incon2.
inversion F.

intros n m sl d l C. simpl SemVal. simpl substVal. rewrite RelV_simpl.
intros _. auto.

intros n e et IH sl d l ST C. simpl substVal.
rewrite RelV_simpl. simpl SemVal.
exists ((Dlift << curry (Roll << SemExp et)) d). split.
repeat (rewrite fcont_comp_simpl). auto. split.
unfold strictV.
intros d0 e0.
unfold Dlift. repeat (rewrite fcont_comp_simpl). rewrite curry_simpl.
repeat (rewrite fcont_comp_simpl). rewrite UR_eq.
rewrite PROD_map_simpl. simpl. rewrite EV_simpl.
rewrite fcont_comp_simpl. rewrite fcont_COMP_simpl.
intros kk. rewrite KLEISLI_simpl in kk.
destruct (kleisliValVal kk) as [d1 [Pd1 XX]].
rewrite UR_eq in Pd1. repeat (rewrite fcont_comp_simpl in XX).
rewrite curry_simpl in XX.
repeat (rewrite fcont_comp_simpl in XX). rewrite UR_eq in XX.
exists d1. apply Pd1.

intros d1 v1 tv1 c1 dv.
unfold Dlift. repeat (rewrite fcont_comp_simpl). rewrite curry_simpl.
repeat (rewrite fcont_comp_simpl). rewrite UR_eq.
rewrite PROD_map_simpl. rewrite EV_simpl.
rewrite fcont_comp_simpl. rewrite fcont_COMP_simpl.
intros kk. simpl in kk. rewrite KLEISLI_simpl in kk.
destruct (kleisliValVal kk) as [d2 [Pd2 X2]].
rewrite UR_eq in Pd2. assert (deq := vinj Pd2).
repeat (rewrite fcont_comp_simpl in X2).
rewrite curry_simpl in X2.
rewrite fcont_comp_simpl in X2. rewrite UR_eq in X2.
assert (stable (SemExp et)) as se by auto.
specialize (se (d,d2) (d,d1)). rewrite X2 in se. clear Pd2 X2.
assert (SemExp et (d,d1) == Val dv) as Pdv.
refine (Oeq_sym (se _)).
rewrite deq. auto.
assert (substExp [v1] (substExp (VAR 0 :: map (shiftV 0 1) sl) e) =
        substExp (v1 :: sl) e).
rewrite (subst_substE (n:=S n) (e:=e)). simpl. f_equal.
f_equal. refine (list_ext _). intros m.
rewrite nth_error_map. rewrite nth_error_map. case_eq (nth_error sl m).
intros v nth. f_equal. specialize (ST m v nth).
rewrite (shift_nilV ST). assert (xx:=proj1 subst_nil v 0 ST). rewrite xx. auto.
intros i incon. inversion incon. auto.
simpl. auto. apply et. simpl. rewrite map_length. omega.

rewrite H.
specialize (IH (v1::sl) (d,d1) (eq_S _ _ l)).
assert ((forall (i : nat) (v : Value),
        nth_error (v1 :: sl) i = Some v -> VTyping 0 v)) as nth.
intros i ; case i ; clear i. simpl. intros v iv. inversion iv. rewrite <- H1. apply tv1.
intros i v. simpl. apply ST. specialize (IH nth).
assert ((forall (i : nat) (v : Value) (nth : nth_error (v1 :: sl) i = Some v),
        car LR
          (projenv (m:=i) (n:=S n)
             (ll (sl:=v1 :: sl) (i:=i) (eq_S (length sl) n l) nth) 
             (d, d1), v))) as LRp.
intros i. case i. intros v nthn. simpl in nthn. inversion nthn. simpl projenv.
refine (car_eq _ c1). simpl. split ; auto.
clear i. intros i v. simpl nth_error. intros nthn. simpl projenv.
specialize (C i v nthn). refine (car_eq _ C).
simpl. split ; auto.
rewrite fcont_comp_simpl. rewrite FST_simpl. simpl.
refine (fcont_eq_elim (projenv_irr _ _) _). specialize (IH LRp).
unfold ELR in IH. specialize (IH _ Pdv).
destruct IH as [v [ev R]]. exists v.
exists ev.
refine (car_set_eq _ R). apply (proj2 (proj1 LR_fix)).

(* TVAL *)
intros n v tv IH sl d l C0 C1. unfold ELR.
intros dd dv. simpl in dv. rewrite fcont_comp_simpl in dv. rewrite eta_val in dv.
assert (xx := vinj dv). clear dv.
specialize (IH sl d l C0 C1).
simpl substExp.
exists (substVal sl v). exists (e_Value _).
refine (car_eq _ IH).
simpl. split ; auto.

(* APP *)
intros n v1 v2 tv1 IH1 tv2 IH2 sl d l C0 C1.
unfold ELR. intros env sem. simpl in sem.
rewrite fcont_comp_simpl in sem. rewrite PROD_fun_simpl in sem. unfold Dapp in sem.
rewrite fcont_comp_simpl in sem. rewrite PROD_map_simpl in sem. simpl in sem.
rewrite EV_simpl in sem. rewrite SUM_fun_simpl in sem. simpl in sem.
generalize sem. clear sem. case_eq (SemVal tv1 d). intros sv _. rewrite K_simpl.
intros incon. assert(F:=PBot_val_incon incon). inversion F.
intros f sv. repeat (rewrite fcont_comp_simpl).
specialize (IH1 sl d l C0 C1).
specialize (IH2 sl d l C0 C1).
rewrite sv in IH1.
generalize IH1. case_eq (substVal sl v1). intros nn _ F. simpl in F. inversion F.
intros nn _ incon. simpl in incon. assert (iincon := proj1 incon). inversion iincon.
intros e ve EE. clear IH1.
destruct EE as [ff [fe [sf P]]].
assert (f == ff) as ffeq. destruct fe ; split ; auto.
specialize (P (SemVal tv2 d) (substVal sl v2)).
assert (VTyping 0 (substVal sl v2)) as sT.
refine (subst_typingV tv2 _ C0). auto.
specialize (P sT).
assert (car LR (SemVal tv2 d, substVal sl v2)) as LR2. refine (car_set_eq _ IH2). apply (proj2 (proj1 LR_fix)).
specialize (P LR2). intros uf. rewrite eta_val in uf.
assert (stable Unroll) as su by auto.
specialize (su _ _ (fcont_eq_elim ffeq (Roll (Val (D:=VInf) (SemVal tv2 d))))).
rewrite su in uf. specialize (P _ uf). clear uf su.
destruct P as [v3 [ev3 LR3]].
exists v3. 
assert (substExp sl (APP v1 v2) =>> v3) as ev. simpl. rewrite ve. refine (e_App ev3). exists ev.
assert (car (RelV LR LR) (SemVal tv2 d, substVal sl v2)) as ccc. refine (car_set_eq _ LR2).
apply (proj1 LR_fix).
refine (car_set_eq _ LR3). apply (proj1 LR_fix).

(* TLET *)
intros n e1 e2 te1 IH1 te2 IH2 sl d l C0 C1.
unfold ELR. intros env sem. simpl in sem.
rewrite fcont_comp_simpl in sem. rewrite PROD_fun_simpl in sem.
rewrite EV_simpl in sem.
rewrite curry_simpl in sem.
specialize (IH1 sl d l C0 C1).


destruct (KLEISLIR_ValVal sem) as [d1 [deV Pf]].
unfold ELR in IH1. specialize (IH1 _ deV). clear sem.
destruct IH1 as [v1 [ev1 c1]].
specialize (IH2 (v1 :: sl) (d,d1) (eq_S _ _ l)).
assert ((forall (i : nat) (v : Value),
         nth_error (v1 :: sl) i = Some v -> VTyping 0 v)) as C2.
intros i ; case i ; clear i. intros v. simpl. intros ev. inversion ev. rewrite <- H0.
clear v ev H0.

refine (eval_preserve_type ev1 _). refine (subst_typingE te1 _ C0). auto.
intros i v. simpl. apply (C0). specialize (IH2 C2).
assert ((forall (i : nat) (v : Value) (nth : nth_error (v1 :: sl) i = Some v),
         car LR
           (projenv (m:=i) (n:=S n)
              (ll (sl:=v1 :: sl) (i:=i) (eq_S (length sl) n l) nth) 
              (d, d1), v))) as C3. intros i. case i ; clear i.
intros v nth. simpl projenv. simpl in nth. inversion nth. rewrite <- H0. clear nth H0.
assert (car LR (d1,v1)) as lr1. refine (car_set_eq _ c1). apply (proj1 LR_fix).
refine (car_eq _ lr1). simpl. rewrite SND_simpl. simpl. auto.
intros i v nth. simpl in nth. specialize (C1 i v nth).
refine (car_eq _ C1). simpl. split ; auto.
rewrite fcont_comp_simpl. rewrite FST_simpl.  simpl. refine (fcont_eq_elim (projenv_irr _ _) _).
specialize (IH2 C3). unfold ELR in IH2.
specialize (IH2 _ Pf). destruct IH2 as [vv [evv cvv]].
exists vv.
assert (substExp sl (LET e1 e2) =>> vv) as ev2.
simpl. refine (e_Let ev1 _). rewrite (@subst_substE e2 (S n)).
simpl. rewrite map_map. assert (map (fun x : Value => substVal [v1] (shiftV 0 1 x)) sl = sl) as slE.
refine (list_ext _). intros i. rewrite nth_error_map. case_eq (nth_error sl i) ; auto.
intros v nthi. f_equal. specialize (C0 i v nthi).
rewrite (shift_nilV C0). rewrite (proj1 subst_nil _ 0 C0). auto.
intros ii incon. inversion incon. auto. rewrite slE. apply evv.
apply te2. simpl. rewrite map_length. omega.
exists ev2. apply cvv.

(* IFZ *)
intros n v e1 e2 tv IHv te1 IH1 te2 IH2 sl env l C0 C1. specialize (IHv sl env l C0 C1).
specialize (IH1 sl env l C0 C1). specialize (IH2 sl env l C0 C1).
intros d sem. simpl in sem. repeat (rewrite fcont_comp_simpl in sem).
rewrite PROD_fun_simpl in sem.
rewrite ID_simpl in sem. simpl in sem. rewrite fcont_comp_simpl in sem.
rewrite SUM_fun_simpl in sem. simpl in sem. generalize sem. clear sem.

fold VInf. case_eq (SemVal tv env). intros nn semtv.
rewrite EV_simpl. rewrite semtv in *. rewrite RelV_simpl in IHv.
case_eq (substVal sl v). intros n0 eq. rewrite eq in IHv. inversion IHv.
intros n0 eq.
assert (nn = n0) as nneq. rewrite eq in *. destruct IHv ; auto.
rewrite nneq in *. clear nn nneq IHv.
destruct n0.
intros KL. simpl in KL.
unfold ELR in IH1. specialize (IH1 _ KL). destruct IH1 as [vrr [evr cvr]].
exists vrr. assert (substExp sl (IFZ v e1 e2) =>> vrr) as eev.
simpl. rewrite eq. refine (e_Ifz1 _ _). apply evr.
exists eev. apply cvr.

intros KL. simpl in KL. unfold ELR in IH2. specialize (IH2 _ KL). destruct IH2 as [vrr [evr cvr]].
exists vrr. assert (substExp sl (IFZ v e1 e2) =>> vrr) as eev.
simpl. rewrite eq. refine (e_Ifz2 _ _ evr).
exists eev. apply cvr.

intros e incon. rewrite incon in *. simpl in IHv. clear incon. destruct IHv as [f [incon _]].
destruct incon as [incon _] ; inversion incon.

rewrite EV_simpl.
intros ff semtv KL. rewrite K_simpl in KL.
assert (F:= PBot_val_incon KL). inversion F.

(* OP *)
intros n op v1 v2 tv1 IH1 tv2 IH2 sl d l C0 C1.
unfold ELR. intros env sem. simpl in sem.
repeat (rewrite fcont_comp_simpl in sem).
rewrite PROD_fun_simpl in sem. rewrite uncurry_simpl in sem.
destruct (Operator2Val sem) as [nn [mm [Sn [Sm P]]]].
specialize (IH1 sl d l C0 C1).
specialize (IH2 sl d l C0 C1).
fold VInf in *.
rewrite fcont_comp_simpl in *.
destruct (SemVal tv1 d). simpl in Sn. unfold VInf in Sn. rewrite SUM_fun_simpl in Sn. simpl in Sn.
assert (teq := vinj Sn). clear Sn. assert (t = nn) as tteq by (destruct teq as [ee _] ; inversion ee ; auto).
rewrite tteq in *. clear t tteq teq.
destruct (SemVal tv2 d). simpl in Sm. unfold VInf in Sm. rewrite SUM_fun_simpl in Sm. simpl in Sm.
assert (teq := vinj Sm). clear Sm. assert (t = mm) as tteq by (destruct teq as [ee _] ; inversion ee ; auto).
rewrite tteq in *. clear teq t tteq.
repeat (rewrite fcont_comp_simpl in P). rewrite eta_val in P. assert (pp := vinj P). clear P.
rewrite RelV_simpl in IH1.
case_eq (substVal sl v1). intros m1 sm. rewrite sm in *. inversion IH1.
intros m1 sv. rewrite sv in *.
rewrite RelV_simpl in IH2.
case_eq (substVal sl v2). intros m2 sm. rewrite sm in *. inversion IH2.
intros m2 sv2. rewrite sv2 in *.
exists (NUM (op m1 m2)).
assert (substExp sl (OP op v1 v2) =>> NUM (op m1 m2)) as ev.
simpl. rewrite sv. rewrite sv2. refine (e_Op _ _ _).
exists ev.
clear sem.
assert (nn = m1) as meq. inversion IH1. auto. rewrite meq in *. clear IH1 meq nn.
assert (mm = m2) as meq. inversion IH2. auto. rewrite meq in *. clear IH2 meq mm.

rewrite RelV_simpl. rewrite <- pp. auto.

intros e incon. rewrite incon in *. destruct IH2 as [f [incon1 _]].
inversion incon1. inversion H.
intros f sem2. rewrite sem2 in *. destruct IH1 as [ff [incon _]]. inversion incon. inversion H.
unfold VInf in *. rewrite SUM_fun_simpl in Sm. simpl in Sm.
assert (F:=PBot_val_incon Sm). inversion F.
unfold VInf in *. rewrite SUM_fun_simpl in Sn. simpl in Sn.
assert (F:=PBot_val_incon Sn). inversion F.
Qed.

Lemma Adequate: forall e (te:ETyping 0 e) d env, SemExp te env == Val d ->
   exists v, exists ev:e =>> v, True.
intros e te d env sem.
assert (xx:=proj2 Adequacy _ _ te nil env).
 simpl length in xx. specialize (xx (refl_equal 0)).
unfold ELR in xx. assert (forall (i : nat) (v : Value), nth_error nil i = Some v -> VTyping 0 v) as e1.
intros i v. destruct i ; simpl ; auto. intros incon. inversion incon. intros incon. inversion incon.
specialize (xx e1).
assert (forall (i : nat) (v : Value) (nth : nth_error nil i = Some v),
        car LR (projenv (ll (sl:=nil) (refl_equal 0) nth) env, v)) as e2.
intros i ; case i. intros v incon ; simpl in incon ; inversion incon.
intros n v incon ; simpl in incon ; inversion incon.
specialize (xx e2). specialize (xx _ sem). destruct xx as [v [ev _]].
exists v. assert (yy:=proj2 subst_nil _ _ te nil). rewrite yy in ev. exists ev. auto.
intros i incon. inversion incon.
Qed.

