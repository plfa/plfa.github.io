Require Import utility.
Require Import PredomAll.
Require Import typedlambda.
Require Import typedopsem.
Require Import typeddensem.

Set Implicit Arguments.

(*==========================================================================
  Logical relation between semantics and terms, used to prove adequacy 
  See Winskel Chapter 11, Section 11.4.
  ==========================================================================*)

(** printing senv %\ensuremath{\rho}% *)
(** printing d1 %\ensuremath{d_1}% *)

(* Lift a value-relation to a computation-relation *)
Definition liftRel ty (R : SemTy ty -> CValue ty -> Prop) :=
  fun (d:DL _) e => forall d', d == Val d' -> exists v, e =>> v /\ R d' v.

(* Logical relation between semantics and closed value terms *)
Unset Implicit Arguments.

Fixpoint relVal ty : SemTy ty -> CValue ty -> Prop :=
match ty with
| Int           => fun d v => v = TINT d
| Bool          => fun d v => v = TBOOL d
| ty1 --> ty2   => fun d v => exists e, v = TFIX e /\ forall d1 v1, relVal ty1 d1 v1 -> liftRel (relVal ty2) (d d1) (substExp [ v1, v ] e)
| ty1 ** ty2    => fun d v => exists v1, exists v2, v = TPAIR v1 v2 /\ relVal ty1 (FST d) v1 /\ relVal ty2 (SND d) v2
end.

(* Logical relation between semantic environments and value environments *)
Fixpoint relEnv env : SemEnv env -> Subst env nil -> Prop :=
  match env with
  | nil => fun _ _ => True
  | ty :: env => fun d s => relVal ty (SND d) (hdMap s) /\ relEnv env (FST d) (tlMap s)
  end.

(* Computation relation, already inlined into relVal *)
Definition relExp ty :=  liftRel (relVal ty).

Set Implicit Arguments.
Unset Strict Implicit.



Lemma relVal_lower_lift : 
  forall ty,
  (forall d d' (v:CValue ty), d <= d' -> relVal ty d' v -> relVal ty d v) ->
  (forall d d' (e:CExp   ty), d <= d' -> relExp ty d' e -> relExp ty d e).
intros t IH d d' e l R.
unfold relExp, liftRel in *.
intros d'0 eq.
rewrite eq in l.
assert (S := DLle_Val_exists_eq l).
destruct S as [d'1 [d'eq l']].
clear eq l. specialize (R d'1 d'eq). 
destruct R as [v [ev grl]].
exists v. split; auto. specialize (IH d'0 d'1 v l'). auto.
Qed.

(* Lemma 11.12 (ii) from Winskel *)
Lemma relVal_lower: forall ty d d' v, d <= d' -> relVal ty d' v -> relVal ty d v.
induction ty.

(* Int *)
simpl. intros. subst. auto. 

(* Bool *)
simpl. intros. subst. auto.

(* Arrow *)
intros d d' v l. simpl relVal. intros [b [veq C]]. subst. exists b.
split; auto. 
intros d1 v1 gl1.
assert (S := fcont_le_elim l d1).
specialize (C d1 v1 gl1). unfold liftRel in *.  
assert (A := relVal_lower_lift IHty2 S (e := (substExp (env':= nil) [v1,TFIX b] b))). unfold relExp, liftRel in A. auto. 

(* Pair *)
simpl. intros p1 p2 v [leq1 leq2] [v1 [v2 [veq [gl1 gl2]]]].
subst.
exists v1. exists v2. split; auto.
specialize (IHty1 _ _ v1 leq1 gl1).
specialize (IHty2 _ _ v2 leq2 gl2). split ; auto.
Qed.

Add Parametric Morphism ty (v:CValue ty) : (fun d => relVal ty d v)
with signature (@Oeq (SemTy ty)) ==> iff as relVal_eq_compat.
intros x y xyeq.
destruct xyeq as [xy1 xy2].
split; apply relVal_lower; trivial.
Qed.

Add Parametric Morphism ty (v:CExp ty) : (fun d => relExp ty d v)
with signature (@Oeq (DL (SemTy ty))) ==> iff as relExp_eq_compat.
intros x y xyeq.
destruct xyeq as [xy1 xy2].
split; apply (relVal_lower_lift (relVal_lower (ty:=ty))); trivial.
Qed.

(*==========================================================================
  Admissibility
  ==========================================================================*)

Lemma rel_admissible_lift : forall ty,
  (forall v, admissible (fun d => relVal ty d v)) ->
  (forall e, admissible (fun d => relExp ty d e)).
intros t IH e.
unfold admissible in *.
intros c C.
unfold relExp, liftRel in *.
intros d eq.
destruct (lubval eq) as [k [dv [ck dvd]]].
destruct (C _ _ ck) as [v [ev rv]].
exists v. split ; auto.
destruct (DLvalgetchain ck) as [c' P].
specialize (IH v c').
assert ((lub (c:=SemTy t) c') == d) as deq. apply vinj.
rewrite <- eq. rewrite <- eta_val. apply (Oeq_trans (y:=lub (fcontit eta @ c'))).
apply lub_comp_eq ; auto.
apply Oeq_sym.
refine (Oeq_trans (lub_lift_left _ k) _).
apply lub_eq_compat. apply fmon_eq_intro. intros x. simpl. apply P.

refine (relVal_lower (proj2 deq) _).
apply IH. intros n.
specialize (P n). specialize (C _ _ P).
destruct C as [vv [evv rvv]].
rewrite (Determinacy ev evv). apply rvv.
Qed.

Require Import Program.Equality.

(* Lemma 11.12 (iii) from Winskel *)
Lemma rel_admissible: forall ty v, admissible (fun d => relVal ty d v).
induction ty.

(* Int *)
intros v c C. simpl. apply (C 0). 

(* Bool *)
intros v c C. simpl. apply (C 0).

(* Arrow *)
unfold admissible in *.
intros v c C.
simpl relVal.
assert (rv := C 0). simpl in rv. destruct rv as [b [tbeq C0]].
exists b.
split; auto.
intros d1 v1 R1.
refine (rel_admissible_lift _ _). unfold admissible.
intros vv cc CC. apply IHty2. apply CC.

intros n. unfold relExp. unfold liftRel.
intros d' CC.
assert (Cn := C n). simpl in Cn.
destruct Cn as [bb [tteq Cn]].
assert (b = bb) as bbeq. rewrite tteq in *.
clear C0 d1 v1 R1 CC tteq v Cn C.
generalize bb tbeq. clear bb tbeq.
intros bb. intros eq.
apply (TFIX_injective (sym_equal eq)).
rewrite <- bbeq in *. clear bb bbeq.
clear tteq.
specialize (Cn _ _ R1).
unfold liftRel in Cn. specialize (Cn _ CC). apply Cn.

(* Pair *)
unfold admissible.
intros v c C. simpl. unfold prod_lub.
generalize C.
destruct (ClosedPair v) as [v1 [v2 veq]]. subst.
intros _. 
exists v1. exists v2. 
split;auto.
specialize (IHty1 v1). specialize (IHty2 v2).
split. rewrite FST_simpl. rewrite Fst_simpl. simpl fst. apply IHty1. intros n. specialize (C n). simpl. simpl in C. 
destruct C as [v3 [v4 [veq [C1 C2]]]]. clear C2.
destruct (TPAIR_injective veq) as [E1 E2]. subst.
trivial.

rewrite SND_simpl. rewrite Snd_simpl. simpl snd. apply IHty2. intros n. specialize (C n). simpl. simpl in C. 
destruct C as [v3 [v4 [veq [C1 C2]]]]. clear C1.
destruct (TPAIR_injective veq) as [E1 E2]. subst.
trivial.

Qed.

Lemma PBot_val_incon: forall D x, DL_bot D == Val (D:=D) x -> False.
intros D x incon. assert (xx := proj2 incon). clear incon.
simpl in xx. inversion xx. subst. clear H1 xx. induction n.
simpl in H0. rewrite DL_bot_eq in H0. inversion H0.
rewrite DL_bot_eq in H0. simpl in H0. apply (IHn H0).
Qed.

Lemma choose_t_simpl: forall (D:cpo) e1 e2, choose D e1 e2 true = e1.
intros D e1 e2. unfold choose. auto.
Qed.

Lemma choose_f_simpl: forall (D:cpo) e1 e2, choose D e1 e2 false = e2.
intros D e1 e2. unfold choose. auto.
Qed.

Lemma chooseVal: forall (D:cpo) b (e1 e2:DL D) v , choose _ e1 e2 b == Val v ->
            (b = true /\ e1 == Val v) \/ (b = false /\ e2 == Val v).
intros D b e1 e2 v.
assert (choose _ e1 e2 b = fcontit (choosec e1 e2) b). auto.
rewrite H. simpl. clear H.
destruct b. intros e1val. left. split ; auto.
intros ; right ; split ; auto.
Qed.

Lemma SemEnvCons : forall t E (env : SemEnv (t :: E)), exists d, exists ds, env = PAIR ds d.
intros. dependent inversion env. exists t1. exists t0. auto. 
Qed.

Lemma Discrete_injective : forall t (v1 v2:Discrete t), v1 == v2 -> v1 = v2.
intros t v1 v2 eq.
destruct eq. destruct H.  destruct H0.  trivial.
Qed.

Lemma relEnv_ext env senv s s' : (forall x y, s x y = s' x y) -> relEnv env senv s -> relEnv env senv s'.
intros E env s s' C r. induction E. auto.
simpl. simpl in r. destruct r as [rl rr].
split. rewrite SND_simpl. rewrite SND_simpl in rl. unfold hdMap. unfold hdMap in rl.
simpl. simpl in rl. rewrite <- (C a (ZVAR E a)). apply rl.
rewrite FST_simpl. unfold tlMap. simpl. rewrite FST_simpl in rr. unfold tlMap in rr. simpl in rr.
refine (IHE _ _ _ _ rr). intros x y. specialize (C x (SVAR a y)). auto.
Qed.

Theorem FundamentalTheorem:
     (forall env ty v senv s, relEnv env senv s -> relVal ty (SemVal v senv) (substVal s v))
     /\ 
     (forall env ty e senv s, relEnv env senv s -> liftRel (relVal ty) (SemExp e senv) (substExp s e)).
Proof.
apply ExpVal_ind.

(* TINT *)
simpl; auto. 

(* TBOOL *)
simpl; auto. 

(* TVAR *)
intros E t v env s Renv.
induction v.
destruct (SemEnvCons env) as [d [ds eq]]. subst. simpl. fold SemEnv in *.
simpl in Renv. destruct Renv as [R1 _]. trivial. 
destruct (SemEnvCons env) as [d [ds eq]]. subst. simpl. fold SemEnv in *.
simpl in Renv. destruct Renv as [_ R2].  rewrite fcont_comp_simpl.
specialize (IHv ds (tlMap s) R2).  auto.

(* TFIX *)
intros E t1 t2 e IH env s R.
simpl SemVal.
rewrite fcont_comp_simpl.
rewrite substTFIX.
rewrite FIXP_simpl. rewrite Fixp_simpl.
apply (@fixp_ind _ _ (fcontit (curry (curry (SemExp e)) env))).
refine (@rel_admissible (t1 --> t2) _).
simpl. exists (substExp  (liftSubst t1 (liftSubst (t1 --> t2) s)) e) ; split ; auto.
intros d1 v1 rv1. unfold liftRel. intros dd. rewrite K_simpl.
intros CC. assert False as F by (apply (PBot_val_incon CC)). inversion F.

intros f rf.
exists (substExp (liftSubst t1 (liftSubst (t1 --> t2) s)) e). split ; auto.
intros d1 v1 rv1. unfold liftRel. intros dd fd.
assert (SemExp e (env,f,d1) == Val dd) as se by auto. clear fd.
rewrite <- (proj2 substComposeSubst). 
rewrite <- substTFIX.
assert (relEnv ((t1 :: t1 --> t2 :: E)) (env,f,d1) (consMap v1 (consMap (substVal (env':=nil) s (TFIX e)) s))).
simpl relEnv. rewrite SND_simpl. simpl. split.
unfold hdMap. simpl. apply rv1. split.
unfold tlMap. unfold hdMap. simpl. rewrite substTFIX. exists (substExp 
          (liftSubst t1 (liftSubst (t1 --> t2) s)) e). split ; auto.
intros d2 v2 rv2. rewrite FST_simpl. rewrite SND_simpl. simpl.
simpl in rf. destruct rf as [bb [bbeq Pb]].
assert (bb = (substExp (liftSubst t1 (liftSubst (t1 --> t2) s)) e)) as beq.
apply (TFIX_injective (sym_equal bbeq)).
rewrite beq in *. clear bb beq bbeq. specialize (Pb d2 v2 rv2). apply Pb.

rewrite FST_simpl. rewrite FST_simpl. simpl. unfold tlMap. simpl.
refine (relEnv_ext _ R). intros x y ; auto.

specialize (IH _ _ H). unfold liftRel in IH. specialize (IH _ se).
rewrite composeCons. rewrite composeCons. 
rewrite composeSubstIdLeft. apply IH.

(* TP *)
intros E t1 t2 v1 IH1 v2 IH2 env s R.
simpl. specialize (IH1 env s R). specialize (IH2 env s R).
exists (substVal s v1). exists (substVal s v2). split; auto. 

(* TFST *)
intros E t1 t2 v IH env s R.
simpl. specialize (IH env s R).
unfold liftRel. intros d1 eq.
rewrite substTFST.
destruct (ClosedPair (substVal s v)) as [v1 [v2 veq]].
rewrite veq in *. clear veq.
exists v1. split. apply e_Fst. simpl relVal in IH. 
destruct IH as [v3 [v4 [veq [gl1 gl2]]]]. destruct (TPAIR_injective veq) as [v1eq v2eq]. subst. clear veq.
rewrite fcont_comp_simpl in eq.
rewrite fcont_comp_simpl in eq.
rewrite eta_val in eq.
assert (H := vinj eq). 
apply (relVal_lower (proj2 H) gl1).

(* TSND *)
intros E t1 t2 v IH env s R.
simpl. fold SemTy. specialize (IH env s R).
unfold liftRel. intros d2 eq. rewrite fcont_comp_simpl in eq. rewrite fcont_comp_simpl in eq.
rewrite substTSND.
destruct (ClosedPair (substVal s v)) as [v1 [v2 veq]].
rewrite veq in *. clear veq.
exists v2. split. apply e_Snd. simpl relVal in IH. 
destruct IH as [v3 [v4 [veq [gl1 gl2]]]]. destruct (TPAIR_injective veq) as [v1eq v2eq]. subst. clear veq.
rewrite eta_val in eq.
assert (H := vinj eq). 
apply (relVal_lower (proj2 H) gl2).

(* TOP *)
intros E op v1 IH1 v2 IH2 env s R.
simpl. specialize (IH1 env s R). specialize (IH2 env s R).
unfold liftRel. intros d eq. rewrite fcont_comp_simpl in eq. rewrite fcont_comp_simpl in eq. rewrite eta_val in eq. assert (H := vinj eq). clear eq. 
rewrite substTOP.
destruct (ClosedInt (substVal s v1)) as [i1 eq1].
destruct (ClosedInt (substVal s v2)) as [i2 eq2].
rewrite eq1 in *. rewrite eq2 in *. clear eq1 eq2.
exists (TINT (op i1 i2)).
split. apply e_Op. rewrite PROD_fun_simpl in H. rewrite uncurry_simpl in H.
unfold relVal in *. inversion IH1. inversion IH2. clear IH1 IH2 H1 H2.
assert ((op (SemVal v1 env) (SemVal v2 env) : Discrete nat) == d) by auto. clear H.
unfold SemTy in d.
assert (H := Discrete_injective H0). rewrite <- H. trivial.

(* TGT *)
intros E v1 IH1 v2 IH2 env s R.
simpl. specialize (IH1 env s R). specialize (IH2 env s R).
unfold liftRel. intros d eq. rewrite fcont_comp_simpl in eq. rewrite fcont_comp_simpl in eq. rewrite eta_val in eq. assert (H := vinj eq). clear eq. 
rewrite substTGT.
destruct (ClosedInt (substVal s v1)) as [i1 eq1].
destruct (ClosedInt (substVal s v2)) as [i2 eq2].
rewrite eq1 in *. rewrite eq2 in *. clear eq1 eq2.
exists (TBOOL (ble_nat i2 i1)).
split. apply e_Gt.
rewrite PROD_fun_simpl in H. rewrite uncurry_simpl in H.
unfold relVal in *. inversion IH1. inversion IH2. clear IH1 IH2 H1 H2.
assert ((ble_nat (SemVal v2 env) (SemVal v1 env) : Discrete bool) == d) by auto. clear H.
unfold SemTy in d.
assert (H := Discrete_injective H0). rewrite <- H. trivial.


(* VAL *)
intros E t v IH env s R. 
simpl. specialize (IH env s R). 
unfold liftRel. intros d eq. rewrite fcont_comp_simpl in eq. rewrite eta_val in eq. assert (H := vinj eq). clear eq.
exists (substVal s v). 
split. apply e_Val.
apply (relVal_lower (proj2 H) IH).

(* TLET *)
intros E t1 t2 e1 IH1 e2 IH2 env s R.
unfold liftRel. intros d2 d2eq.
specialize (IH1 env s R). unfold liftRel in *. 
simpl in d2eq.

rewrite substTLET. rewrite fcont_comp_simpl in d2eq. rewrite PROD_fun_simpl in d2eq.
rewrite ID_simpl in d2eq. simpl in d2eq.
destruct (KLEISLIR_ValVal d2eq) as [d1 [d1eq d2veq]]. clear d2eq.
specialize (IH1 _ d1eq).
destruct IH1 as [v1 [ev1 R1]].
specialize (IH2 (env,d1) (consMap v1 s)).
assert (RR : relEnv (t1::E) (env,d1) (consMap v1 s)).
simpl relEnv. split.
rewrite SND_simpl. assumption.
rewrite tlConsMap.
rewrite FST_simpl. assumption.
specialize (IH2 RR d2 d2veq).
destruct IH2 as [v2 [ev2 R2]].
exists v2. split.
refine (e_Let ev1 _).
rewrite <- (proj2 substComposeSubst). rewrite composeCons. rewrite composeSubstIdLeft. apply ev2. assumption.

(* TAPP *)
intros E t1 t2 v1 IH1 v2 IH2 env s R.
specialize (IH1 env s R). specialize (IH2 env s R).
unfold liftRel. intros d eq. simpl SemExp in eq. fold SemTy in eq. rewrite fcont_comp_simpl in eq. 
rewrite substTAPP.
destruct (ClosedFunction (substVal s v1)) as [e1 eq1].
unfold relVal in IH1. fold relVal in IH1. destruct IH1 as [e1' [eq' R']].
rewrite eq' in eq1.
assert (H := TFIX_injective eq1).
subst.  clear eq1.
specialize (R' (SemVal v2 env) (substVal s v2) IH2).
clear IH2.
unfold liftRel in R'. specialize (R' d eq). 
destruct R' as [v [ev Rv]]. 
exists v. rewrite eq' in ev. 
assert (H := e_App ev). 
split. simpl. rewrite eq'. apply H. 
apply Rv.

(* TIF *)
intros E t v IH e1 IH1 e2 IH2 env s R.
specialize (IH env s R). specialize (IH1 env s R). specialize (IH2 env s R). 
unfold liftRel in *. intros d eq. simpl SemExp in eq. 
rewrite substTIF.
destruct (ClosedBool (substVal s v)) as [b beq].
rewrite beq in IH. 
unfold relVal in IH.
inversion IH.  clear IH. 
simpl substExp. rewrite beq.
rewrite fcont_comp3_simpl in eq. 
case  (chooseVal eq).
(* chooseVal eq = true *) 
intros [H1 H2].
destruct b.
(* b=true *)
specialize (IH1 d H2). 
destruct IH1 as [v' [ev Rv]].
exists v'.
split.
apply (e_IfTrue (substExp s e2) ev).  
apply Rv.
(* b=false *)
rewrite H1 in H0. inversion H0. 
(* chooseVal eq = false *)
intros [H1 H2].
destruct b.
(* b=true *)
rewrite H1 in H0. inversion H0. 
(* b=false *)
specialize (IH2 d H2). 
destruct IH2 as [v' [ev Rv]].
exists v'.
split.
apply (e_IfFalse (substExp s e1) ev).  
apply Rv.
Qed.

Corollary Adequacy: forall ty (e : CExp ty) d, SemExp e tt == Val d -> exists v, e =>> v.
Proof.
intros t e d val.
destruct FundamentalTheorem as [_ FT]. 
specialize (FT nil t e tt (idSubst nil)). 
assert (relEnv nil (tt:DOne) (idSubst nil)). unfold relEnv. auto. specialize (FT H). 
unfold liftRel in FT. specialize (FT d val). 
destruct FT as [v [ev _]]. exists v. rewrite (proj2 applyIdSubst) in ev. trivial.
Qed.

