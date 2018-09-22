(**********************************************************************************
 * uniiade.v                                                                      *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                       *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)

(* Adequacy of semantics for unityped lambda calculus *)

Require Import unii.
Require Export uniisem uniiop Fin. 
Require Import PredomAll.
Require Import KnasterTarski.
Require Import NSetoid.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope C_scope.

Definition RelKind : setoidType := CPO.setoidType VInf * discrete_setoidType (Value O).

Lemma RelV_respect (R S:RelKind =-> Props) : setoid_respect 
  (fun (p:RelKind) => match p with (d,v) =>  match v with 
| INT m => d =-= inl m
| VAR _ => False
| LAMBDA e => 
    exists f, d =-= inr f  /\
    forall (d1:VInf) (v1:Value O), R (d1,v1) -> 
      forall dv, kleisli (eta << Unroll) (f (Roll d1)) =-= Val dv ->
        exists v2, subExp ([v1]) e =>> v2 /\ S (dv,v2)
end end).
case => d1 v1. case => d2 v2. case => e0 e1. simpl in e0,e1. case: e1 => e1.
rewrite e1 ; clear e1 v1. case: v2 ; first by [].
- move => n. split => e ; by rewrite <- e ; auto.
- move => e. by split ; case => f [e1 P] ; exists f ; rewrite <- e1 ; split ; auto.
Qed.

Definition RelV (R S:RelKind =-> Props) : (RelKind =-> Props) :=
  Eval hnf in mk_fset (RelV_respect R S).

Definition imageD (f:VInf =-> VInf _BOT) (R S:RelKind =-> Props) := 
 (forall x, R x -> let (d,v) := x in forall dd, (f d) =-= Val dd -> S (dd,v)).

Definition RAdm (R : RelKind =-> Props) := forall (S : RelKind =-> Props)
               (c : natO =-> (VInf -=> VInf _BOT)), (forall n, imageD (c n) S R) ->
                  imageD (lub c) S R.

Lemma RAdm_inf : forall S : set_clatType RelKind -> Prop,
        (forall t : set_clatType RelKind, S t -> RAdm t) -> RAdm (@inf (set_clatType RelKind) S).
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

Definition RelAdm := @sub_clatType (set_clatType RelKind) RAdm RAdm_inf.

Definition RelAdmop := op_latType RelAdm.

Lemma ev_determ: forall e v1, e =>> v1 -> forall v2, e =>> v2 -> v1 = v2.
intros v v1 ev. induction ev ; try (intros ; inversion H ; auto ; fail).
intros v3 ev. inversion ev. subst. rewrite <- (IHev1 _ H1) in *. apply (IHev2 _ H3).
Qed.

Lemma sum_right_simpl: forall (D E:cpoType) (c:natO =-> (D + E)) T k e, c k =-= inr e -> sum_right (D1:=D) (c:=c) T k =-= e.
intros D E c T k e. case T. simpl. clear T. intros x c0. clear c0. case: (c k).  move => s. by case.
move => s A. by apply A.
Qed.

Lemma single_set_respect (T:setoidType) (v:T) : setoid_respect (fun y => y =-= v).
move => y y' e.
by split => e' ; rewrite <- e' ; rewrite e.
Qed.

Definition single_set (T:setoidType) (v:T) : T =-> Props := Eval hnf in mk_fset (single_set_respect v).

Lemma Kab_mono (D1 D2:cpoType) : monotonic (fun x:D2 => @const D1 D2 x:D1 -=> D2).
by move => x y l.
Qed.

Definition Kab (D1 D2:cpoType) : ordCatType D2 (D1 -=> D2) := Eval hnf in mk_fmono (@Kab_mono D1 D2).

Lemma inv_image_respect (T T':setoidType) (f: T =-> T') (Y:T' =-> Props) : setoid_respect (fun x => Y (f x)).
move => x y e. simpl. by rewrite -> e.
Qed.

Definition inv_image (T T':setoidType) (f: T =-> T') (Y:T' =-> Props) : (T =-> Props) :=
  Eval hnf in mk_fset (inv_image_respect f Y).

Lemma RelVA_adm (R : set_clatType RelKind)
  (AR : RAdm R) (S : set_clatType RelKind) (AS : RAdm S) : RAdm (RelV R S).
unfold RAdm.
simpl. move => A c C.
unfold imageD. intros e ; case e ; clear e. intros d v Ad dd lubdd.
simpl in lubdd.
assert (xx:=lubval lubdd). destruct xx as [k [dd' [ck Pdd]]].
destruct (DLvalgetchain ck) as [c' Pc'].

generalize Ad. clear Ad.
case v ; clear v. simpl. intros n. Require Import Program. by dependent destruction n.

intros n cA. simpl. specialize (C k). unfold imageD in C.
specialize (C _ cA _ ck).
assert (lub (fcont_app c d) =-= Val (lub c')) as lc.
rewrite <- eta_val. rewrite -> (lub_comp_eq _ c').
rewrite -> (lub_lift_left _ k).
refine (lub_eq_compat _). refine (fmon_eq_intro _) => m.
simpl. apply (Pc' m). simpl in lc. rewrite -> lc in lubdd.
assert (ll := vinj lubdd). clear lubdd.
rewrite <- ll in *. clear ll. simpl in C. rewrite -> C in Pdd.
assert (c' 0%N =-= @INL (discrete_cpoType nat) (DInf -=> DInf _BOT) n).
specialize (Pc' O). rewrite addn0 in Pc'.
rewrite -> ck in Pc'. assert (xx := vinj Pc'). rewrite <- xx. rewrite -> C. by auto.
assert (forall x, @INL (discrete_cpoType nat) (DInf -=> DInf _BOT) n <= x -> exists d, x =-= inl d).
intros x. simpl. case x. intros t nt. simpl. exists t ; auto.
intros t FF. inversion FF. specialize (H0 _ Pdd).
destruct H0 as [nn sn].
rewrite -> sn in Pdd. simpl in Pdd. rewrite <- Pdd in *. by apply sn.

simpl.
intros ee Cc. assert (C0 := C k). unfold imageD in C0. specialize (C0 _ Cc). simpl in C0.
specialize (C0 _ ck).

destruct (C0) as [f [cf _]].
case (SuminjProof c' 0). intros incon. case incon. clear incon.
intros ff incon. specialize (Pc' O). rewrite -> addn0 in Pc'. rewrite incon in Pc'. simpl in Pc'.
rewrite -> ck in Pc'. have Pcc:=vinj Pc'. rewrite -> cf in Pcc. by case: Pcc.

intros T. exists (lub (sum_right T)).
assert (dd =-=
   inr (* nat *)
     (@lub (DInf -=> DInf _BOT)
        (sum_right (D1:=discrete_cpoType nat) (D2:=DInf -=> DInf _BOT) (c:=c') T))) as ldd.
have CI:(continuous ( (@INR (discrete_cpoType nat) (DInf -=> DInf _BOT)))) by auto.
assert (forall x, Inr (discrete_ordType nat) (DInf -=> DInf _BOT) x = inr x).
intros x. by auto. rewrite <- H. clear H. rewrite -> (lub_comp_eq (INR (discrete_cpoType nat) _) (sum_right T)).

assert (lub (fcont_app c d) =-= Val (lub c')) as lc.
rewrite <- eta_val. rewrite -> (lub_comp_eq _ c').
refine (Oeq_trans (lub_lift_left (fcont_app c d) k) _).
refine (lub_eq_compat _). refine (fmon_eq_intro _).
intros m. simpl. apply (Pc' m). simpl in lc. rewrite -> lc in lubdd.
assert (ll := vinj lubdd). clear lubdd.
rewrite <- ll. assert (xx:=@lub_eq_compat _ c'). simpl in xx. simpl. apply xx.
refine (fmon_eq_intro _). intros m. simpl.
assert (exists dd, c' m =-= inr (* (discrete_cpoType nat) *) dd). assert (c' O <= c' m) as cm.
assert (monotonic c') as cm' by auto. by apply cm'. simpl. case T. intros x c'0.
simpl in c'0.
generalize cm. clear cm. case (c' m). intros t incon. simpl in incon. rewrite c'0 in incon. inversion incon.
intros t cm. exists t. auto. destruct H as [c'm cm].
assert (yy := sum_right_simpl T cm). rewrite -> cm.  simpl.
assert (stable (@INR (discrete_cpoType nat) (DInf -=> DInf _BOT))) by auto.
simpl in H. refine (H _ _ _). clear H.
rewrite <- yy. by auto.

split. apply ldd.

intros d1 v1 Sd1 dv rdv.
rewrite fcont_lub_simpl in rdv.
rewrite -> (lub_comp_eq _ (fcont_app (sum_right T) (Roll d1))) in rdv.
destruct (lubval rdv) as [kk [dkk [ckk dkkl]]].
destruct (DLvalgetchain ckk) as [c1' cP]. simpl in ckk.

assert (D := C (k+kk)%N). unfold imageD in D. specialize (D _ Cc). simpl in D.
assert (xx:= Pc' kk). specialize (D _ xx).
case: D => ff. case => c0 P.
specialize (P _ v1 Sd1).
assert (cp0:= cP O).

assert (bla:=sum_right_simpl T c0). simpl in cp0. rewrite addn0 in cp0.
assert (stable ((kleisli (eta << Unroll)))) as su by apply: fmon_stable.
specialize (su _ _ (fmon_eq_elim bla (Roll (d1)))). rewrite -> su in cp0.
specialize (P _ cp0). destruct P as [v2 [ev2 S2]].
exists v2. split. by apply ev2. clear bla su cp0 xx S2 c0 ff.

unfold RAdm in AS.

specialize (AS (inv_image (@Ssnd _ _) (single_set (v2:discrete_setoidType (Value O))))).
specialize (AS (Kab _ (VInf _BOT) << (eta_m << c1'))).
have AA:(forall n : natO,
        imageD ((Kab VInf (VInf _BOT) << (eta_m << c1')) n)
          (inv_image
             (Ssnd (CPO.setoidType VInf) (discrete_setoidType (Value 0)))
             (single_set (v2:discrete_setoidType (Value 0)))) S).
intros n. unfold imageD. simpl. intros x ; case x; clear x. simpl.
intros d0 v0 veq. unfold tset_eq in veq. simpl in veq. rewrite  veq. clear v0 veq. intros d00.
move => vv. have vvv:=vinj vv. clear vv.
specialize (C (k+kk+n)%N).
unfold imageD in C. specialize (C _ Cc). simpl in C.
specialize (cP n).
assert (c (k + kk + n)%N d =-= Val (c' (kk + n))%N).
specialize (Pc' (kk+n)%N). rewrite <- Pc'.
by rewrite addnA.
specialize (C _ H).
destruct C as [fn [c'n Pn']].
specialize (Pn' _ _ Sd1). simpl in cP. clear H.
assert (xx:=sum_right_simpl T c'n).
assert (stable ( (kleisli (eta << Unroll)))) as su by apply:fmon_stable.
specialize (su _ _ (fmon_eq_elim xx (Roll d1))). rewrite -> su in cP.
clear su xx. specialize (Pn' _ cP).
destruct Pn' as [v3 [ev3 S3]]. have e0:=ev_determ ev3 ev2. rewrite -> e0 in S3. clear ev3 v3 e0.
have e0:S (d00, v2) =-= S (c1' n,v2). apply frespect. split ; last by []. simpl. by rewrite -> vvv.
apply (proj2 e0). by apply S3. specialize (AS AA).
unfold imageD in AS.
specialize (AS (d,v2)). simpl in AS.
refine (AS _ _ _) ; first by [].
assert (xx := fcont_lub_simpl (Kab VInf (VInf _BOT) << (eta_m << c1')) d).
simpl in xx. rewrite xx. clear xx.
rewrite <- rdv.
assert (aa:=@lub_eq_compat (VInf _BOT)).
simpl in aa.
refine (Oeq_trans _ (Oeq_sym (lub_lift_left _ kk))).
refine (aa _ _ _). refine (fmon_eq_intro _). intros n.
specialize (cP n). auto using cP.
Qed.

Definition RelVA : RelAdmop -> RelAdm -> RelAdm.
intros R S. case R. clear R. intros R AR. case S. clear S. intros S AS.
exists (RelV R S). by apply RelVA_adm.
Defined.

Definition RelVAop : RelAdm -> RelAdmop -> RelAdmop := fun X Y => RelVA X Y.

Lemma RelVm_mon : monotonic (fun (p:prod_clatType RelAdmop RelAdm) => 
         (RelVAop (lsnd _ _ p) (lfst _ _ p), RelVA (lfst _ _ p) (lsnd _ _ p))).
unfold monotonic. intros x. case x. clear x. intros x0 y0 y. case y. clear y. intros x1 y1.
simpl. case x1. clear x1. intros x1 rx1. case x0. clear x0. intros x0 rx0.
case y0 ; clear y0 ; intros y0 ry0. case y1 ; clear y1 ; intros y1 ry1.
intros [sx sy]. split. simpl.
intros dv. case dv. clear dv. intros d v. simpl. case v ; [by auto | by auto | idtac].
clear v. intros e C. destruct C as [f [df P]]. exists f. split ; first by auto.
intros d1 v1 y01. specialize (P d1 v1).
specialize (sy (d1,v1) y01). intros dv rdv. specialize (P sy dv rdv).
destruct P as [v2 [ev2 P]]. exists v2. split; [by apply ev2 | by apply (sx (dv,v2) P)].

simpl.
intros dv. case dv. clear dv. intros d v. simpl.
case v ; auto. clear v. intros v C. destruct C as [f [df C]].
exists f. split ; first by auto. intros d1 v1 c1. specialize (C d1 v1).
specialize (sx (d1,v1) c1). intros dv dvr. specialize (C sx dv dvr).
destruct C as [v2 [ev2 C]]. exists v2. split; [by apply ev2 | by apply (sy (dv,v2) C)].
Qed.

Definition RelVm : ordCatType (prod_clatType RelAdmop RelAdm) (prod_clatType RelAdmop RelAdm) :=
  Eval hnf in mk_fmono RelVm_mon.

Definition Delta := lsnd _ _ (lfp RelVm).
Definition Deltam := lfst _ _ (lfp RelVm).

Lemma RelV_fixedD: Delta =-= (RelVA Deltam Delta).
unfold Delta, Deltam. assert (xx:=lfp_fixedpoint RelVm).
generalize xx. clear xx.
case ((@lfp (prod_clatType RelAdmop RelAdm) RelVm)).
intros d0 d1. simpl. intros X. case: X. simpl. case => A B. case => X Y. by split.
Qed.

Lemma RelV_fixedDm : Deltam =-= (RelVA Delta Deltam).
unfold Deltam,Delta. assert (xx := lfp_fixedpoint RelVm).
generalize xx ;clear xx.
case (lfp RelVm).
intros d0 d1. simpl. case. simpl. case => A B. case => X Y. by split.
Qed.

Lemma RelV_least: forall R S, R <= RelVA S R -> (RelVA R S) <= S ->
                          R <= Deltam /\ Delta <= S.
intros R S.
assert (xx:=@lfp_least _ RelVm).
intros Rsub Ssub. simpl in Rsub, Ssub.
assert (RelVm (R,S) <= (R,S)). simpl. split. by apply Rsub. by apply Ssub.
specialize (xx _ H).
assert (lfp RelVm =-= (Deltam,Delta)) as L.
unfold Deltam, Delta. by split.
rewrite -> L in xx.
by destruct xx ; split ; auto.
Qed.

Require Import uniirec.
Lemma RelV_F_action: forall (f:VInf =-> VInf _BOT) (R S:RelKind =-> Props), imageD f R S ->
  imageD (eta << [|in1,
      (in2 <<
       ((exp_fun (CCOMP _ _ _:cpoCatType _ _) (kleisli (kleisli (eta << Roll) << f << Unroll)) : cpoCatType _ _) <<
        ((exp_fun
           ((CCOMP DInf _ (DInf _BOT)) <<
            SWAP) ((kleisli (eta << Roll) << f << Unroll)) : cpoCatType _ _) << KLEISLI)))|]) (RelV S R) (RelV R S).
move => f R S X.
case => d. case ; first by [].
- move => n. simpl. move => e dd. move => A. have A':=vinj A. clear A. rewrite -> e in A'. clear d e.
  rewrite -> SUM_fun_simplx in A'. by apply (Oeq_sym A').
- move => e. simpl. case => f' [e' P] dd ee.
  exists (kleisli ((kleisli (eta << Roll) << f) << Unroll) <<
      (kleisli f' << ((kleisli (eta << Roll) << f) << Unroll))).
  have ee':=vinj ee. clear ee. rewrite -> e' in ee'. rewrite -> SUM_fun_simplx in ee'.
  simpl in ee'. rewrite <- ee'. split ; first by [].
  clear dd d e' ee'. move => d1 v1 R1 dv. simpl.
  rewrite -> (fmon_eq_elim UR_id d1). simpl. move => A.
  destruct (kleisliValVal A) as [d2 [B Q]]. have e1 := vinj Q. clear Q A.
  destruct (kleisliValVal B) as [d3 [C Q]]. clear B. destruct (kleisliValVal C) as [d4 [C0 Q0]].
  clear C. destruct (kleisliValVal C0) as [d5 [C1 Q1]]. clear C0. have X':= (X (d1,v1) R1 _ C1).
  specialize (P _ v1 X'). have Q2:=vinj Q1. clear Q1. rewrite <- Q2 in Q0. clear Q2 d4.
  destruct (kleisliValVal Q) as [d4 [P' Q']]. clear Q. have e2:=vinj Q'. clear Q'.
  have ee:kleisli (eta << Unroll) (f' (Roll d5)) =-= Val (Unroll d3). rewrite -> Q0. by rewrite kleisliVal.
  specialize (P _ ee). case: P => v2 Ev. exists v2. case: Ev => Ev P. split. apply Ev.
  specialize (X _ P _ P'). rewrite <- e2 in e1. clear e2 d2. have e2:=fmon_eq_elim UR_id d4.
  rewrite -> e2 in e1. simpl in e1. clear e2. have ea:= (frespect S).
  have eb:S (dv, v2) =-= S (d4, v2). apply frespect. split ; last by []. by rewrite -> e1.
  by apply (proj2 eb).
Qed.

Lemma imageD_eq: forall f g X Y, f =-= g -> imageD f X Y -> imageD g X Y.
intros f g X Y fg. unfold imageD. intros C. intros x ; case x ; clear x.
intros d v. simpl. specialize (C (d,v)). intros Xd. specialize (C Xd).
simpl in C. intros dd gd. assert (ff := fmon_eq_elim fg d). rewrite <- ff in gd.
specialize (C _ gd). apply C.
Qed.

Lemma imageD_eqS : forall (X Y Z W:RelKind =-> Props) f,  @Ole (set_ordType _) Z X ->
        @Ole (set_ordType RelKind) Y W -> imageD f X Y -> imageD f Z W.
move => X Y Z W f l x y. case => e v Ze.
specialize (l (e,v) Ze). specialize (y (e,v)). simpl in y. move => fe E.
specialize (y l _ E). by apply x.
Qed.

Lemma Delta_l: Delta =-= Deltam.
split. apply (proj1 (RelV_least (proj1 RelV_fixedD) (proj1 (RelV_fixedDm)))).
case_eq Delta. intros D AD Deq. case_eq Deltam. intros Dm ADm Dmeq. simpl.
intros dv. case dv. clear dv. intros d v. unfold RAdm in AD.
intros Dmdv. assert (imageD (eta << Unroll << Id << Roll) Dm D).
assert (AA:=AD Dm).
assert (admissible (fun (X:DInf -=> DInf _BOT) => imageD (((kleisli (eta << Unroll) << X) << Roll)) Dm D /\
                          X <= eta)) as Ad.
unfold admissible. intros c C1.
split. assert (C := fun n => proj1 (C1 n)). clear C1.
have a:= comp_eq_compat (comp_lub_eq (kleisli (eta << Unroll)) c) (tset_refl Roll).
rewrite -> lub_comp in a.
apply: (imageD_eq (Oeq_sym a)). clear a.
apply AD. simpl. move => n. by apply C.
apply lub_le => n. by apply (proj2 (C1 n)).
have ee:(((eta << Unroll) << Id) << Roll) =-= kleisli (eta << Unroll) << (FIXP delta) << Roll.
rewrite <- id_min. rewrite kleisli_eta_com. by rewrite comp_idR.
refine (imageD_eq (Oeq_sym ee) _). clear ee.
rewrite FIXP_simpl.

refine (proj1 (fixp_ind Ad _ _)). unfold imageD. split.
intros x ; case x ; clear x. simpl.
intros dd vv. intros ddC d0. repeat (rewrite fcont_comp_simpl).
move => F. rewrite -> kleisli_bot in F. by case: (@PBot_incon _ _ (proj2 F)).
by apply: leastP.

intros f imaf. split ; last by rewrite -> (fmonotonic ( delta) (proj2 imaf)) ; rewrite -> delta_eta.

destruct imaf as [imaf fless].
have aa:=comp_eq_compat (comp_eq_compat (tset_refl (kleisli (eta << Unroll))) (delta_simpl f)) (tset_refl Roll).
repeat rewrite -> comp_assoc in aa. rewrite -> kleisli_eta_com in aa.
do 3 rewrite <- (comp_assoc Roll) in aa. rewrite -> UR_id in aa. simpl. rewrite -> comp_idR in aa.
apply (imageD_eq (Oeq_sym aa)).

assert (X1:=RelV_fixedD).
assert (X2:=RelV_fixedDm).
rewrite Deq in X1, X2. rewrite Dmeq in X1, X2.
assert (D =-= RelV Dm D) by auto.
assert (Dm =-= RelV D Dm) by auto.
clear X1 X2.

apply (imageD_eqS (proj1 H0) (proj2 H)).
have e0:((kleisli (eta << Roll) <<
                   ((kleisli (eta << Unroll) << f) << Roll)) << Unroll) =-= f.
repeat rewrite comp_assoc. rewrite <- comp_assoc. rewrite RU_id. rewrite comp_idR.
rewrite <- kleisli_comp2. rewrite <- comp_assoc. rewrite RU_id. rewrite comp_idR.
 rewrite kleisli_unit. by rewrite comp_idL.
apply: (imageD_eq _ (RelV_F_action imaf)). rewrite -> e0. repeat rewrite <- comp_assoc.
rewrite UR_id. by rewrite comp_idR.

unfold imageD in H. specialize (H _ Dmdv). simpl in H.
specialize (H d). apply H. unfold id. apply: (fmon_stable eta).
by rewrite -> (fmon_eq_elim UR_id d).
Qed.

Definition LR : RelKind =-> Props := match Delta with exist D _ => D end.

Lemma LR_fix: LR =-= (RelV LR LR) /\ RAdm LR.
unfold LR.
assert (Dfix:=RelV_fixedD). assert (monotonic RelVm) by auto.
assert (M:= H (Delta,Delta) (Deltam,Delta)).
specialize (H (Deltam,Delta) (Delta,Delta)).
assert (xx:=Delta_l). split.
assert (((Deltam, Delta) : (prod_clatType RelAdmop RelAdm)) <= (Delta, Delta)).  destruct xx as [X0 X1].
split. auto. auto. specialize (H H0).
assert (((Delta, Delta) : (prod_clatType RelAdmop RelAdm)) <= (Deltam, Delta)). destruct xx as [X0 X1].
split ; auto.
specialize (M H1). clear H0 H1.
generalize H M Dfix xx. clear Dfix xx H M.
case Delta. intros D Rd.
case Deltam. intros Dm RDm.
intros H M Dfix yy.
assert (D =-= RelV Dm D) by auto.
assert (Dm =-= D) by auto. clear yy Dfix.
case: H. case: M. simpl. unfold Ole. simpl. rewrite {1 3} / Ole. simpl.
move => R0 R1 R2 R3. split => A.
- apply R3. by apply (proj1 H0).
- apply (proj2 H0). by apply R1.
case Delta. simpl. by auto.
Qed.

Definition ELR := fun ld e, forall d, ld =-= Val d -> exists v, exists ev:e =>> v, (RelV LR LR) (d,v).

Lemma RelV_simpl: forall R S d v, (RelV R S) (d,v) =
 match v with 
| INT m => d =-= inl(* _ *) m
| VAR _ => False
| LAMBDA e => exists f, d =-= inr (* _*) f  /\
      forall (d1:VInf) (v1:Value O), R (d1,v1) ->
           forall dv, kleisli (eta << Unroll) (f (Roll d1)) =-= Val dv ->
      exists v2, subExp (cons v1 (@idSub _)) e =>> v2 /\ S (dv,v2)
end. intros R S d v. simpl. case v ; auto.
Qed.

Fixpoint LRsubst E : SemEnv E -> unii.Sub E 0 -> Prop :=
  match E with
  | O   => fun d m => True
  | S n' => fun d m => LR (snd d, hd m) /\ LRsubst (fst d) (tl m)
  end. 

Add Parametric Morphism (O0 O1:cpoType) : (@pair O0 O1)
 with signature (@tset_eq _ : O0 -> O0 -> Prop) ==> (@tset_eq _ : O1 -> O1 -> Prop) ==> (@tset_eq (O0 * O1))
 as pair_eq_compat.
move => x y e x' y' e'. split. by rewrite -> e ; rewrite -> e'.
by rewrite <- e ; rewrite <- e'.
Qed.

(*=Fundamental *)
Theorem FundamentalTheorem n : 
(forall (v:Value n) sl d, LRsubst d sl -> (RelV LR LR) (SemVal v d, subVal sl v)) /\
forall (e:Exp n) sl d, LRsubst d sl -> ELR (SemExp e d) (subExp sl e).
(*=End *)
rewrite (lock LR).
move: n ; apply ExpValue_ind.
(* VAR *)
- intros n v sl d C. 
  dependent induction v.
  + destruct C as [Ch Ct]. fold LRsubst in Ct. rewrite -lock.
    have X:= ((proj1 LR_fix) _). by apply (proj1 (X _)).
  + destruct C as [Ch Ct]. fold LRsubst in Ct. rewrite -lock. rewrite (consEta sl). rewrite -lock in IHv. by apply (IHv _ _ Ct).
(* INT *) 
- by [].
(* LAMBDA *)
- move => n e IH s d C. simpl SemVal. SimplMap.  
  exists ((exp_fun ((kleisli (eta << Roll) << SemExp e) << Id >< Unroll)) d).
  split ; first by [].
  + intros d1 v1 c1 dv. simpl.
    move => X.
    have Y:=Oeq_trans (fmon_eq_elim (kleisli_comp2 _ _) _) X. clear X.
    case: (kleisliValVal Y) => v [se P]. rewrite <- comp_assoc in P. rewrite -> UR_id in P.
    rewrite -> P in se. clear P v Y.
    specialize (IH (cons v1 s) (d,d1)).
    have: (LRsubst ((d,d1):SemEnv (n.+1)) (cons v1 s)). split.
    * rewrite -lock in c1. by apply c1.
    * simpl. rewrite tlCons. by apply C.
  move => H. specialize (IH H).
  unfold ELR in IH. specialize (IH dv).
  have S: (SemExp e (d, d1) =-= Val dv). rewrite <- se.
  by rewrite -> (pair_eq_compat (tset_refl _) (fmon_eq_elim UR_id d1)).
  rewrite -> (pair_eq_compat (tset_refl _) (fmon_eq_elim UR_id d1)) in se. specialize (IH se).
  case: IH => v [ev evH]. exists v. split. rewrite <- (proj2 (applyComposeSub _)). rewrite composeSingleSub. by apply ev. rewrite -lock. by apply (proj2 (proj1 LR_fix _)).

(* VAL *)
- move => n v IH s d l d' H.
  specialize (IH s d l). exists (subVal s v). exists (e_Val (subVal s v)). rewrite -lock in IH.
  simpl in H. have e:=vinj H. clear H.
  refine (proj1 (frespect (RelV LR LR) _) IH). by apply NSetoid.pair_eq_compat.
(* APP *)
- move => n v0 IH0 v1 IH1 s d l d' e. SimplMap.
  simpl in e. specialize (IH0 s d l). specialize (IH1 s d l).
  simpl in IH0. case: (subVal s v0) IH0 ; first by [].
  + move=> m ee. rewrite -> ee in e. rewrite -> SUM_fun_simplx in e. simpl in e. rewrite -> kleisli_bot in e.
    by case: (PBot_incon (proj2 e)).
  + move => e'. case => f [e0 P]. rewrite -> e0 in e. rewrite -> SUM_fun_simplx in e.
    rewrite -lock in IH1. have IH:= proj2 (proj1 LR_fix _) IH1. clear IH1.
    rewrite -lock in P.
    specialize (P _ _ IH _ e). case: P => v. case => ev lr.
    exists v. exists (e_App ev). by apply (proj1 (proj1 LR_fix _)).
(* LET *)
- move => n e0 IH0 e1 IH1 s d l. simpl SemExp. SimplMap.
  specialize (IH0 s d l). simpl. 
  move => d' X.
  case: (KLEISLIR_ValVal X). clear X.
  move => d0 [D0 D1]. specialize (IH0 d0 D0). case: IH0 => v0 [ev0 r0].
  specialize (IH1 (cons v0 s) (d,d0)). have rr:=proj2 (proj1 LR_fix _) r0. clear r0.
  unfold LRsubst in IH1. fold LRsubst in IH1. rewrite hdCons tlCons in IH1. 
  specialize (IH1 (conj rr l)). unfold ELR in IH1. specialize (IH1 d' D1). destruct IH1 as [v [ev H]].
  exists v. 
  split ; last by apply H.
  refine (e_Let ev0 _). rewrite <- (proj2 (applyComposeSub _)). rewrite composeSingleSub. by apply ev.
(* IFZ *)
- move => n v0 IH0 e1 IH1 e2 IH2 s d l d' X.
  specialize (IH0 s d l). simpl in IH0. SimplMap.
  simpl in X.
  case: (subVal s v0) IH0 ; first by [].
  + move => ii ee. simpl SemExp in X. simpl in X. rewrite -> ee in X. rewrite -> SUM_fun_simplx in X. unfold id in X. 
    specialize (IH1 s d l d'). specialize (IH2 s d l d').
    case: ii X ee.
    * move => Y ee. simpl in Y. rewrite -> SUM_fun_simplx in Y. simpl in Y.
      specialize (IH1 Y). case: IH1 => v [ev rv]. exists v. split. apply (e_Ifz1 _ ev). by apply rv. 
    * move => ii Y ee. simpl in Y. rewrite -> SUM_fun_simplx in Y. simpl in Y.
      specialize (IH2 Y). case: IH2 => v [ev rv]. exists v. split. simpl. apply (e_Ifz2 _ _). apply ev. by apply rv. 
  + move => e. case => f [F _]. rewrite -> F in X. rewrite -> SUM_fun_simplx in X.
    simpl in X. by case: (PBot_incon (proj2 X)).
(* OP *)
- move => n op v0 IH0 v1 IH1 s d l d' X. simpl in X.
  specialize (IH0 s d l). specialize (IH1 s d l). simpl in IH0. simpl in IH1. SimplMap.
  case: (kleisliValVal X) => dd [Y Z]. clear X.
  case: (subVal s v0) IH0 IH1 ; first by [].
  + move => i0 ee. case: (subVal s v1) ; first by [].
    * move => i1 ee'. rewrite -> ee in Y. rewrite -> ee' in Y. clear ee ee'.
      do 2 rewrite -> SUM_fun_simplx in Y. simpl in Y. unfold Smash in Y.
      rewrite -> Operator2_simpl in Y. have e:=vinj Y. clear Y.
      rewrite <- e in Z. clear e dd. exists (@INT 0 (op i0 i1)). exists (e_Op op i0 i1).
      simpl in Z. simpl. by rewrite <- (vinj Z).
    * move => e1. case => f [F _]. rewrite -> F in Y. rewrite -> ee in Y.
      do 2 rewrite -> SUM_fun_simplx in Y. simpl in Y. unfold Smash in Y.
      rewrite -> Operator2_strictR in Y. by case: (PBot_incon (proj2 Y)).
  + move => e1. case => f [F _]. rewrite -> F in Y. do 2 rewrite -> SUM_fun_simplx in Y. simpl in Y.
    unfold Smash in Y. rewrite -> Operator2_strictL in Y.
    by case: (PBot_incon (proj2 Y)).
Qed.

(*=Adequate *)
Corollary Adequacy (e:Exp O) d : SemExp e tt =-= Val d -> exists v, e =>> v.
(*=End *)
move => S.
assert (xx:=proj2 (FundamentalTheorem _) e (@idSub _) tt).
simpl in xx. unfold ELR in xx. specialize (xx I _ S). destruct xx as [v P]. exists v. 
have ee:subExp (@idSub _) e = e by apply (proj2 (Map.applyId _ _)). rewrite ee in P. by apply P.
Qed.

