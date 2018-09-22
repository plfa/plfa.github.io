Require Import utility.
Require Import PredomAll.
Require Import typedlambda.
Require Import typeddensem.

Set Implicit Arguments.
Unset Strict Implicit.

(* Need this for nice pretty-printing *)
Unset Printing Implicit Defensive.

(*==========================================================================
  Semantics of substitution and renaming
  ==========================================================================*)

(* Apply semantic function pointwise to a renaming or substitution *)
Fixpoint SemSubst env env' : Subst env' env -> SemEnv env -c> SemEnv env' := 
  match env' with
  | nil => fun s => K _ (tt : DOne) 
  | _ :: _ => fun s => <| SemSubst (tlMap s) , SemVal (hdMap s) |>
  end.

Fixpoint SemRenaming env env' : Renaming env' env -> SemEnv env -c> SemEnv env' := 
  match env' with
| nil => fun s => K _ (tt : DOne)
| _ :: _ => fun s => <| SemRenaming (tlMap s) , SemVar (hdMap s) |>
  end.

Lemma SemLiftRenaming : 
  forall env env' (r : Renaming env env') ty, SemRenaming (tlMap (liftRenaming ty r)) == SemRenaming r << FST. 
Proof.
induction env. intros. simpl.
apply (DOne_final (K (Dprod (SemEnv env') (SemTy ty)) (tt:DOne)) _).  

intros. 
simpl. destruct (consMapInv r) as [r' [var eq]]. 
subst. simpl. rewrite hdConsMap. rewrite tlConsMap.
specialize (IHenv env' r' ty).
rewrite PROD_fun_comp.
refine (PROD_fun_eq_compat _ _).  
rewrite IHenv. auto. auto. 
Qed.

Lemma SemLift2Renaming : 
  forall env env' (r : Renaming env env') ty ty', SemRenaming (tlMap (tlMap (liftRenaming ty' (liftRenaming ty r)))) == SemRenaming r << FST << FST. 
Proof.
induction env. intros. simpl.
apply (DOne_final (K (Dprod (Dprod (SemEnv env') (SemTy ty)) (SemTy ty')) (tt:DOne)) _). 

intros. 
simpl. destruct (consMapInv r) as [r' [var eq]]. 
subst. simpl. rewrite hdConsMap. rewrite tlConsMap.
specialize (IHenv env' r' ty).
rewrite PROD_fun_comp. rewrite PROD_fun_comp. 
refine (PROD_fun_eq_compat _ _).  
rewrite IHenv. auto. auto. 
Qed.

(*==========================================================================
  Semantic function commutes with renaming
  ==========================================================================*)

Lemma SemCommutesWithRenaming:
   (forall env ty (v : Value env ty) env' (r : Renaming env env'),
   SemVal v << SemRenaming r == SemVal (renameVal r v))
/\ (forall env ty (exp : Exp env ty) env' (r : Renaming env env'),
   SemExp exp << SemRenaming r == SemExp (renameExp r exp)).
Proof.
apply ExpVal_ind.

(* TINT *)
intros. simpl. rewrite <- K_com; trivial.  

(* TBOOL *)
intros. simpl. rewrite <- K_com; trivial.

(* TVAR *)
intros env ty var env' r.
simpl. 
induction var. 
simpl. rewrite SND_PROD_fun.
destruct (consMapInv r) as [r' [v eq]]. subst.
simpl. rewrite hdConsMap. trivial.
destruct (consMapInv r) as [r' [v eq]]. subst.
simpl. 
specialize (IHvar r').
rewrite <- IHvar. rewrite fcont_comp_assoc. 
rewrite tlConsMap. rewrite FST_PROD_fun. trivial.

(* TFIX *)
intros E t t1 body IH E' s. 
specialize (IH _ (liftRenaming _ (liftRenaming _ s))).
rewrite renameTFIX.
simpl SemVal. 
rewrite fcont_comp_assoc.
rewrite Curry_comp. rewrite Curry_comp. rewrite <- IH.
clear IH. simpl. unfold PROD_map. rewrite fcont_comp_unitL. rewrite fcont_comp_unitL.
rewrite PROD_fun_comp. rewrite SemLift2Renaming. trivial.

(* TPAIR *)
intros E t1 t2 v1 IH1 v2 IH2 E' s.
rewrite renameTPAIR. simpl SemVal. rewrite <- IH1. rewrite <- IH2. rewrite <- PROD_fun_comp. trivial. 

(* TFST *)
intros E t1 t2 v IH E' s. rewrite renameTFST. simpl. 
rewrite <- IH. repeat (rewrite fcont_comp_assoc). trivial. 

(* TSND *)
intros E t1 t2 v IH E' s. rewrite renameTSND. simpl. 
rewrite <- IH. repeat (rewrite fcont_comp_assoc). trivial.

(* TOP *)
intros E n v1 IH1 v2 IH2 E' s. rewrite renameTOP. simpl.
repeat (rewrite fcont_comp_assoc). rewrite <- IH1. rewrite <- IH2.
rewrite PROD_fun_comp. trivial.

(* TGT *)
intros E v1 IH1 v2 IH2 E' s. rewrite renameTGT. simpl. 
repeat (rewrite fcont_comp_assoc). rewrite <- IH1. rewrite <- IH2.
rewrite PROD_fun_comp. trivial.

(* TVAL *)
intros E t v IH E' s. rewrite renameTVAL. simpl. 
rewrite <- IH. rewrite fcont_comp_assoc. trivial.

(* TLET *)
intros E t1 t2 e2 IH2 e1 IH1 E' s. rewrite renameTLET. simpl. 
rewrite fcont_comp_assoc.
specialize (IH2 _ s).
specialize (IH1 _ (liftRenaming _ s)).
rewrite PROD_fun_comp.
rewrite KLEISLIR_comp.
rewrite <- IH2. clear IH2. rewrite <- IH1. clear IH1. simpl. 
unfold PROD_map. rewrite fcont_comp_unitL. rewrite fcont_comp_unitL.
rewrite SemLiftRenaming. trivial. 

(* TAPP *)
intros E t1 t2 v1 IH1 v2 IH2 E' s. rewrite renameTAPP. simpl. 
rewrite fcont_comp_assoc. rewrite <- IH1. rewrite <- IH2.
rewrite PROD_fun_comp. trivial.

(* TIF *)
intros E t ec IHc te1 IH1 te2 IH2 E' s. rewrite renameTIF. simpl. 
rewrite fcont_comp3_comp. rewrite <- IHc. rewrite <- IH1. rewrite <- IH2. trivial.
Qed.

Set Printing Implicit Defensive.

Lemma SemShiftRenaming : 
  forall env env' (r : Renaming env env') ty, SemRenaming (shiftRenaming ty r) == SemRenaming r << FST.
Proof.
induction env. intros. simpl.
apply (DOne_final (K (Dprod (SemEnv env') (SemTy ty)) (tt:DOne)) _).

intros. 
simpl. destruct (consMapInv r) as [r' [var eq]]. 
subst. simpl. rewrite hdConsMap. rewrite tlConsMap.
specialize (IHenv env' r' ty).
rewrite PROD_fun_comp.
refine (PROD_fun_eq_compat IHenv _); auto.
Qed.

Lemma SemIdRenaming : forall env, SemRenaming (idRenaming env) == ID.
Proof.
induction env.
simpl. 
apply (DOne_final (K DOne _) _).

rewrite idRenamingDef. simpl SemRenaming. rewrite tlConsMap. rewrite SemShiftRenaming.  
rewrite IHenv. rewrite fcont_comp_unitL.
apply fcont_eq_intro. intros. destruct x.  auto. 
Qed.


Lemma SemShiftSubst : 
  forall env env' (s : Subst env env') ty, SemSubst (shiftSubst ty s) == SemSubst s << FST.
Proof.
induction env. intros. simpl.
apply (DOne_final (K (Dprod (SemEnv env') (SemTy ty)) (tt:DOne)) _). 

intros. 
simpl. destruct (consMapInv s) as [s' [var eq]]. 
subst. simpl. rewrite hdConsMap. rewrite tlConsMap.
specialize (IHenv env' s' ty).
rewrite PROD_fun_comp.
refine (PROD_fun_eq_compat _ _).  
rewrite IHenv. auto. unfold shiftSubst.
rewrite shiftConsMap. rewrite hdConsMap.
simpl. rewrite <- (proj1 SemCommutesWithRenaming).
refine (fcont_comp_eq_compat _ _). trivial.
(* Seems a bit round-about *)
assert ((fun t0 => SVAR ty) = tlMap (liftRenaming ty (idRenaming env'))).
rewrite LiftRenamingDef. rewrite tlConsMap. apply MapExtensional.   auto.
rewrite H.
rewrite SemLiftRenaming. rewrite SemIdRenaming. rewrite fcont_comp_unitL. auto. 
Qed.


Lemma SemLiftSubst : 
  forall env env' (s : Subst env env') ty, SemSubst (tlMap (liftSubst ty s)) == SemSubst s << FST. 
Proof.
intros.
rewrite LiftSubstDef. rewrite tlConsMap. apply SemShiftSubst. 
Qed.

Lemma SemLift2Subst : 
  forall env env' (s : Subst env env') ty ty', SemSubst (tlMap (tlMap (liftSubst ty' (liftSubst ty s)))) == SemSubst s << FST << FST. 
Proof.
intros.
rewrite LiftSubstDef. rewrite tlConsMap. rewrite LiftSubstDef. unfold shiftSubst. rewrite shiftConsMap. rewrite tlConsMap.
rewrite SemShiftSubst. rewrite SemShiftSubst. auto. 
Qed.

(*==========================================================================
  Semantic function commutes with substitution
  ==========================================================================*)


Lemma SemCommutesWithSubst:
   (forall env ty (v : Value env ty) env' (s : Subst env env'),
   SemVal v << SemSubst s == SemVal (substVal s v))
/\ (forall env ty (e : Exp env ty) env' (s : Subst env env'),
   SemExp e << SemSubst s == SemExp (substExp s e)).
Proof.
apply ExpVal_ind.

(* TINT *)
intros. simpl. rewrite <- K_com; trivial.  

(* TBOOL *)
intros. simpl. rewrite <- K_com; trivial.

(* TVAR *)
intros env ty var env' s.
simpl. 
unfold substVal. simpl travVal.
induction var. simpl.   rewrite SND_PROD_fun.
destruct (consMapInv s) as [s' [v eq]]. subst.
simpl. rewrite hdConsMap. trivial.
destruct (consMapInv s) as [s' [v eq]]. subst.
simpl. 
specialize (IHvar s').
rewrite <- IHvar. rewrite fcont_comp_assoc. 
rewrite tlConsMap. rewrite FST_PROD_fun. trivial.

(* TFIX *)
intros E t t1 body IH E' s. rewrite substTFIX. simpl. 
rewrite fcont_comp_assoc.
rewrite Curry_comp. rewrite Curry_comp. rewrite <- IH.
clear IH. simpl. unfold PROD_map. rewrite fcont_comp_unitL. rewrite fcont_comp_unitL.
rewrite SemLift2Subst. rewrite fcont_comp_assoc. rewrite PROD_fun_comp. rewrite fcont_comp_assoc. trivial.

(* TPAIR *)
intros E t1 t2 v1 IH1 v2 IH2 E' s. rewrite substTPAIR. simpl. 
rewrite <- IH1. rewrite <- IH2. rewrite PROD_fun_comp. trivial. 

(* TFST *)
intros E t1 t2 v IH E' s. rewrite substTFST. simpl. 
rewrite <- IH. repeat (rewrite fcont_comp_assoc). trivial. 

(* TSND *)
intros E t1 t2 v IH E' s. rewrite substTSND. simpl.
rewrite <- IH. repeat (rewrite fcont_comp_assoc). trivial.

(* TOP *)
intros E n v1 IH1 v2 IH2 E' s. rewrite substTOP. simpl. 
repeat (rewrite fcont_comp_assoc). rewrite <- IH1. rewrite <- IH2.
rewrite PROD_fun_comp. trivial.

(* TGT *)
intros E v1 IH1 v2 IH2 E' s. rewrite substTGT. simpl. 
repeat (rewrite fcont_comp_assoc). rewrite <- IH1. rewrite <- IH2.
rewrite PROD_fun_comp. trivial.

(* TVAL *)
intros E t v IH E' s. rewrite substTVAL. simpl. 
rewrite <- IH. rewrite fcont_comp_assoc. trivial.

(* TLET *)
intros E t1 t2 e2 IH2 e1 IH1 E' s. rewrite substTLET. simpl. 
rewrite fcont_comp_assoc.
specialize (IH2 _ s).
specialize (IH1 _ (liftSubst _ s)).
rewrite PROD_fun_comp.
rewrite KLEISLIR_comp.
rewrite <- IH2. clear IH2. rewrite <- IH1. clear IH1. simpl.
unfold PROD_map. rewrite fcont_comp_unitL. rewrite fcont_comp_unitL. rewrite SemLiftSubst.  trivial.

(* TAPP *)
intros E t1 t2 v1 IH1 v2 IH2 E' s. rewrite substTAPP. simpl. 
rewrite fcont_comp_assoc. rewrite <- IH1. rewrite <- IH2.
rewrite PROD_fun_comp. trivial.

(* TIF *)
intros E t ec IHc te1 IH1 te2 IH2 E' s. rewrite substTIF. simpl. 
rewrite fcont_comp3_comp.
rewrite <- IHc. rewrite <- IH1. rewrite <- IH2. trivial.
Qed.