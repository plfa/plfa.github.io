(**********************************************************************************
 * typedadequacy.v                                                                *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                       *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)


(* Require Import utility.*)
Require Import PredomAll.
Require Import typedlambda.
Require Import typedopsem.
Require Import typeddensem.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(*==========================================================================
  Logical relation between semantics and terms, used to prove adequacy 
  See Winskel Chapter 11, Section 11.4.
  ==========================================================================*)

(** printing senv %\ensuremath{\rho}% *)
(** printing d1 %\ensuremath{d_1}% *)

(* Lift a value-relation to a computation-relation *)
(*=liftRel *)
Definition liftRel t (R : SemTy t -> CValue t -> Prop) :=
  fun d e => forall d', d =-= Val d' -> exists v, e =>> v /\ R d' v. (*CLEAR*)
(* = End *)

(* Logical relation between semantics and closed value terms *)
Unset Implicit Arguments.

(* = relValEnvExp *)
(*CLEARED*)
Fixpoint relVal t : SemTy t -> CValue t -> Prop :=
 match t with
  | Int        => fun d v => v = TINT d
  | Bool       => fun d v => v = TBOOL d
  | t1 --> t2  => fun d v => exists e, v = TFIX e /\ 
    forall d1 v1, relVal t1 d1 v1 -> liftRel (relVal t2) (d d1) (subExp [ v1, v ] e)
  | t1 ** t2   => fun d v => exists v1, exists v2, 
                v = TPAIR v1 v2 /\ relVal t1 (fst d) v1 /\ relVal t2 (snd d) v2
 end. (*CLEAR*)

Fixpoint relEnv E : SemEnv E -> Sub E nil -> Prop :=
  match E with
  | nil => fun _ _ => True
  | t :: E => fun d s => relVal t (snd d) (hdMap s) /\ relEnv E (fst d) (tlMap s)
  end.
(*CLEARED*)
Definition relExp ty :=  liftRel (relVal ty).
(*=End *)
(* Computation relation, already inlined into relVal *)

Set Implicit Arguments.
Unset Strict Implicit.

Lemma relVal_lower_lift : 
  forall ty,
  (forall d d' (v:CValue ty), d <= d' -> relVal ty d' v -> relVal ty d v) ->
  (forall d d' (e:CExp   ty), d <= d' -> relExp ty d' e -> relExp ty d e).
rewrite /relExp /liftRel. move => t IH d d' e l R d0 eq.
rewrite -> eq in l. clear d eq. case: (DLle_Val_exists_eq l) => d'v [e0 l1].
specialize (R _ e0). case: R => v [ev rv]. exists v. split ; first by [].
by apply (IH _ _ _ l1).
Qed.

(* Lemma 11.12 (ii) from Winskel *)
(*=relValLower *)
Lemma relVal_lower: forall t d d' v, d <= d' -> relVal t d' v -> relVal t d v. 
(*CLEAR*)

elim.

(* Int *)
simpl. move => d d' v. by case => e ; rewrite e.

(* Bool *)
simpl. move => d d' v. by case: d ; case: d'.

(* Arrow *)
move => t IH t' IH' d d' v l /=. case => b. case => e ; rewrite e. clear v e.
move => C. exists b. split ; first by []. move => d1 v1 r1.  specialize (C d1 v1 r1).
apply (relVal_lower_lift IH' (l d1)). by apply C.

(* Pair *)
move => t IH t' IH' p1 p2 v L. case => v0 ; case => v1 [e l]. rewrite e. clear v e.
simpl. exists v0. exists v1. split ; first by [].
specialize (IH _ _ v0 (proj1 L)). specialize (IH' _ _ v1 (proj2 L)). split ; [apply IH | apply IH'] ; apply l.
Qed.

Add Parametric Morphism ty (v:CValue ty) : (fun d => relVal ty d v)
with signature (@tset_eq (SemTy ty)) ==> iff as relVal_eq_compat.
intros x y xyeq.
destruct xyeq as [xy1 xy2].
split; apply relVal_lower; trivial.
Qed.

Add Parametric Morphism t (v:CExp t) : (fun d => relExp t d v)
with signature (@tset_eq ((SemTy t)_BOT)) ==> iff as relExp_eq_compat.
intros x y xyeq.
destruct xyeq as [xy1 xy2].
split; apply (relVal_lower_lift (relVal_lower (t:=t))); trivial.
Qed.

(* ==========================================================================
  Admissibility
   ========================================================================== *)

Lemma rel_admissible_lift : forall ty,
  (forall v, admissible (fun d => relVal ty d v)) ->
  (forall e, admissible (fun d => relExp ty d e)).
rewrite /admissible /relExp /liftRel. move => t IH e c C d eq.
case: (lubval eq) => k [dv [ck dvd]].
case: (C _ _ ck) => v [ev rv].
exists v. split ; first by [].
destruct (DLvalgetchain ck) as [c' P].
specialize (IH v c').
have El: ((@lub (SemTy t) c') =-= d). apply: vinj. rewrite <- eq.
  apply tset_trans with (y:=eta (lub c')) ; first by [].
  rewrite -> (lub_comp_eq). rewrite (lub_lift_left c k). apply: lub_eq_compat.
  apply fmon_eq_intro => n. simpl. by rewrite <- P.

refine (relVal_lower (proj2 El) _).
apply IH => n.
specialize (P n). specialize (C _ _ P). case: C => v' [ev' rv'].
rewrite (Determinacy ev ev'). by apply rv'.
Qed.

(* Lemma 11.12 (iii) from Winskel *)

(*CLEARED*)Lemma rel_admissible: forall t v, admissible (fun d => relVal t d v).
(*=End *)
elim.

(* Int *)
intros v c C. simpl. apply (C 0).

(* Bool *)
intros v c C. simpl. specialize (C 0). simpl in C. have e:lub c = c 0.
 unfold lub. simpl. unfold sum_lub. simpl. case: (SuminjProof c 0).
  + simpl. case. case. move => e. by rewrite {2} e.
  + simpl. case. case. move => e. by rewrite {2} e.
by rewrite e.

(* Arrow *)
rewrite /admissible => t IH t' IH' v c C.
simpl.
assert (rv := C 0). simpl in rv. destruct rv as [b [tbeq C0]].
exists b.
split; first by [].
intros d1 v1 R1.
refine (rel_admissible_lift _ _).
intros vv cc CC. apply IH'. apply CC.

intros n. unfold relExp. unfold liftRel.
intros d' CC.
assert (Cn := C n). simpl in Cn.
destruct Cn as [bb [tteq Cn]]. rewrite tteq in tbeq C C0 Cn. rewrite tteq. clear v tteq.
assert (b = bb) as bbeq  by apply (TFIX_injective (sym_equal tbeq)).
rewrite <- bbeq in C0, C, Cn. rewrite <- bbeq. clear tbeq bb bbeq.
specialize (Cn _ _ R1).
unfold liftRel in Cn. specialize (Cn _ CC). by apply Cn.

(* Pair *)
unfold admissible.
move => t IH t' IH' v c C. simpl. unfold prod_lub.
generalize C.
destruct (ClosedPair v) as [v1 [v2 veq]]. subst.
intros _. 
exists v1. exists v2. 
split;first by [].
specialize (IH v1). specialize (IH' v2).
split.
- apply: IH. move => n. specialize (C n). case: C => v3 [v4 [veq [C1 C2]]].
  destruct (TPAIR_injective veq) as [E1 E2]. subst. by apply C1.
- apply: IH'. move => n. specialize (C n). case: C => v3 [v4 [veq [C1 C2]]].
  destruct (TPAIR_injective veq) as [E1 E2]. subst. by apply C2.
Qed.

Lemma SemEnvCons : forall t E (env : SemEnv (t :: E)), exists d, exists ds, env =(ds, d).
intros. dependent inversion env. exists s0. by exists s.
Qed.

Lemma Discrete_injective : forall t (v1 v2:discrete_cpoType t), v1 =-= v2 -> v1 = v2.
intros t v1 v2 eq.
destruct eq. destruct H.  destruct H0.  trivial.
Qed.

Lemma relEnv_ext env senv s s' : (forall x y, s x y = s' x y) -> relEnv env senv s -> relEnv env senv s'.
elim:env senv s s' ; first by [].
move => a E IH env s s' C r.
simpl. simpl in r. destruct r as [rl rr].
split. unfold hdMap. rewrite <- (C a (ZVAR E a)). by apply rl.
unfold tlMap.
refine (IH _ _ _ _ rr). intros x y. by specialize (C x (SVAR a y)).
Qed.

(*=FT *)
Theorem FundamentalTheorem E:
 (forall t v senv s, relEnv E senv s -> relVal t (SemVal v senv) (subVal s v)) /\
 (forall t e senv s, relEnv E senv s -> liftRel (relVal t) (SemExp e senv) (subExp s e)).
(*=End *)
Proof.
move: E ; apply ExpVal_ind.

(* TINT *)
by simpl; auto. 

(* TBOOL *)
simpl. move=> E. by case.

(* TVAR *)
intros E t v env s Renv.
induction v.
destruct (SemEnvCons env) as [d [ds eq]]. subst. simpl. fold SemEnv in *.
simpl in Renv. destruct Renv as [R1 _]. by trivial. 
destruct (SemEnvCons env) as [d [ds eq]]. subst. simpl. fold SemEnv in *.
simpl in Renv. destruct Renv as [_ R2].
specialize (IHv ds (tlMap s) R2). by auto.

(* TFIX *)
intros E t1 t2 e IH env s R.
simpl SemVal.
rewrite substTFIX.
apply (@fixp_ind _ ((exp_fun (exp_fun (SemExp e)) env)) _ (@rel_admissible (t1 --> t2) _)).
simpl. exists (subExp  (liftSub t1 (liftSub (t1 --> t2) s)) e) ; split ; auto.
intros d1 v1 rv1. unfold liftRel. intros dd.
intros CC. by destruct (PBot_incon_eq (Oeq_sym CC)).

intros f rf.
exists (subExp (liftSub t1 (liftSub (t1 --> t2) s)) e). split ; first by [].
intros d1 v1 rv1. unfold liftRel. intros dd fd.
assert (SemExp e (env,f,d1) =-= Val dd) as se by auto. clear fd.
rewrite <- (proj2 (substComposeSub _)).
rewrite <- substTFIX.
assert (relEnv ((t1 :: t1 --> t2 :: E)) (env,f,d1) (consMap v1 (consMap (subVal (env':=nil) s (TFIX e)) s))).
simpl relEnv. split.
unfold hdMap. simpl. by apply rv1. split.
unfold tlMap. unfold hdMap. simpl. rewrite substTFIX. exists (subExp 
          (liftSub t1 (liftSub (t1 --> t2) s)) e). split ; first by [].
intros d2 v2 rv2.
simpl in rf. destruct rf as [bb [bbeq Pb]].
assert (bb = (subExp (liftSub t1 (liftSub (t1 --> t2) s)) e)) as beq.
apply (TFIX_injective (sym_equal bbeq)).
rewrite beq in bbeq, Pb. clear bb beq bbeq. specialize (Pb d2 v2 rv2). by apply Pb.

simpl. unfold tlMap. simpl.
refine (relEnv_ext _ R). by intros x y ; auto.

specialize (IH _ _ H). unfold liftRel in IH. specialize (IH _ se).
rewrite composeCons. rewrite composeCons. 
rewrite composeSubIdLeft. by apply IH.

(* TP *)
intros E t1 t2 v1 IH1 v2 IH2 env s R.
simpl. specialize (IH1 env s R). specialize (IH2 env s R).
exists (subVal s v1). exists (subVal s v2). by split; auto.

(* TFST *)
intros E t1 t2 v IH env s R.
simpl. specialize (IH env s R).
unfold liftRel. intros d1 eq.
rewrite substTFST.
destruct (ClosedPair (subVal s v)) as [v1 [v2 veq]].
rewrite veq in IH. rewrite veq. clear veq.
exists v1. split. apply: e_Fst. simpl relVal in IH. 
destruct IH as [v3 [v4 [veq [gl1 gl2]]]]. destruct (TPAIR_injective veq) as [v1eq v2eq]. subst. clear veq.
assert (H := vinj eq). 
by apply (relVal_lower (proj2 H) gl1).

(* TSND *)
intros E t1 t2 v IH env s R.
simpl. fold SemTy. specialize (IH env s R).
unfold liftRel. intros d2 eq.
rewrite substTSND.
destruct (ClosedPair (subVal s v)) as [v1 [v2 veq]].
rewrite veq in IH. rewrite veq. clear veq.
exists v2. split. apply e_Snd. simpl relVal in IH. 
destruct IH as [v3 [v4 [veq [gl1 gl2]]]]. destruct (TPAIR_injective veq) as [v1eq v2eq]. subst. clear veq.
assert (H := vinj eq). 
by apply (relVal_lower (proj2 H) gl2).

(* TOP *)
intros E op v1 IH1 v2 IH2 env s R.
simpl. specialize (IH1 env s R). specialize (IH2 env s R).
unfold liftRel. intros d eq.
rewrite substTOP.
destruct (ClosedInt (subVal s v1)) as [i1 eq1].
destruct (ClosedInt (subVal s v2)) as [i2 eq2].
rewrite -> eq1 in IH1. rewrite eq1. rewrite eq2 in IH2. rewrite eq2. clear eq1 eq2.
exists (TINT (op i1 i2)).
split. apply e_Op. simpl in IH1, IH2. case: IH1 => IH1. rewrite -> IH1.
case: IH2 => e ; rewrite -> e. case: (vinj eq). simpl => ee. by rewrite <- ee.

(* TGT *)
intros E v1 IH1 v2 IH2 env s R.
simpl. specialize (IH1 env s R). specialize (IH2 env s R).
unfold liftRel. intros d eq. have H:=vinj eq.
rewrite substTGT.
destruct (ClosedInt (subVal s v1)) as [i1 eq1].
destruct (ClosedInt (subVal s v2)) as [i2 eq2].
rewrite -> eq1 in IH1. rewrite eq1. rewrite eq2 in IH2. rewrite eq2. clear eq1 eq2.
exists (TBOOL (i2 <= i1)%N).
split. apply e_Gt. simpl in IH1,IH2. case: IH1 => e ; rewrite e. clear e. case: IH2 => e ; rewrite e. clear e.
f_equal.
have HH:(if (SemVal v2 env <= SemVal v1 env)%N then INL _ _ tt else INR _ _ tt) =-= d by apply H. clear H.
case: (SemVal v2 env <= SemVal v1 env)%N HH ; simpl ; clear eq ; case: d ; simpl ; case ; by case.

(* VAL *)
intros E t v IH env s R. 
simpl. specialize (IH env s R). 
unfold liftRel. intros d eq. have H:=vinj eq. clear eq.
exists (subVal s v). 
split. apply e_Val.
apply (relVal_lower (proj2 H) IH).

(* TLET *)
intros E t1 t2 e1 IH1 e2 IH2 env s R.
unfold liftRel. intros d2 d2eq.
specialize (IH1 env s R). unfold liftRel in *. 
simpl in d2eq.

rewrite substTLET.
destruct (KLEISLIR_ValVal d2eq) as [d1 [d1eq d2veq]]. clear d2eq.
specialize (IH1 _ d1eq).
destruct IH1 as [v1 [ev1 R1]].
specialize (IH2 (env,d1) (consMap v1 s)).
assert (RR : relEnv (t1::E) (env,d1) (consMap v1 s)).
simpl relEnv. split ; first by [].
by rewrite tlConsMap.
specialize (IH2 RR d2 d2veq).
destruct IH2 as [v2 [ev2 R2]].
exists v2. split.
refine (e_Let ev1 _).
rewrite <- (proj2 (substComposeSub _)). rewrite composeCons. rewrite composeSubIdLeft. apply ev2. by assumption.

(* TAPP *)
intros E t1 t2 v1 IH1 v2 IH2 env s R.
specialize (IH1 env s R). specialize (IH2 env s R).
unfold liftRel. intros d eq. rewrite substTAPP.
destruct (ClosedFunction (subVal s v1)) as [e1 eq1].
unfold relVal in IH1. fold relVal in IH1. destruct IH1 as [e1' [eq' R']].
rewrite eq' in eq1.
assert (H := TFIX_injective eq1).
subst.  clear eq1.
specialize (R' (SemVal v2 env) (subVal s v2) IH2).
clear IH2.
unfold liftRel in R'. specialize (R' d eq). 
destruct R' as [v [ev Rv]]. 
exists v. rewrite eq' in ev. 
assert (H := e_App ev). 
split. simpl. rewrite eq'. apply H. 
by apply Rv.

(* TIF *)
intros E t v IH e1 IH1 e2 IH2 env s R.
specialize (IH env s R). specialize (IH1 env s R). specialize (IH2 env s R). 
unfold liftRel in *. intros d eq. 
rewrite substTIF.
destruct (ClosedBool (subVal s v)) as [b beq].
rewrite beq in IH. 
unfold relVal in IH.
inversion IH.  clear IH. 
simpl subExp. rewrite beq.
rewrite H0 in beq. rewrite H0. clear b H0. simpl in eq.
case: (SemVal v env) eq beq ; case => eq beq.
- specialize (IH1 _ eq). case: IH1 => v0 [S0 R0]. exists v0. split ; last by [].
  by apply (e_IfTrue _ S0).
- specialize (IH2 _ eq). case: IH2 => v0 [S0 R0]. exists v0. split ; last by [].
  by apply (e_IfFalse _ S0).
Qed.

(*=Adequacy *)
Corollary Adequacy: forall t (e : CExp t) d, SemExp e tt =-= Val d -> exists v, e =>> v.
(*=End *)
Proof.
intros t e d val.
destruct (FundamentalTheorem nil) as [_ FT].
specialize (FT t e tt (idSub nil)). 
have X: (relEnv nil tt (idSub nil)) by [].
specialize (FT X). unfold liftRel in FT. specialize (FT d val). 
destruct FT as [v [ev _]]. exists v. by rewrite (proj2 (applyIdSub _)) in ev.
Qed.

