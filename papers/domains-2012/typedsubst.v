(**********************************************************************************
 * typedsubst.v                                                                   *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                       *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)

Require Import PredomAll.
Require Import typedlambda.
Require Import typeddensem.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* Need this for nice pretty-printing *)
Unset Printing Implicit Defensive.

(*==========================================================================
  Semantics of substitution and renaming
  ==========================================================================*)

Section SEMMAP.

  Variable P : Env -> Ty -> Type.
  Variable ops : MapOps P.
  Variable Sem : forall E t, P E t -> SemEnv E =-> SemTy t.
  Variable SemVl : forall E t (v : P E t), Sem v =-= SemVal (vl ops v). 
  Variable SemVr : forall E t, Sem (vr ops (ZVAR E t)) =-= pi2.
  Variable SemWk : forall E t (v:P E t) t', Sem (wk ops t' v) =-= Sem v << pi1. 

  (* Apply semantic function pointwise to a renaming or substitution *)
  (*=SemSub *)
  Fixpoint SemMap E E' : Map P E' E -> SemEnv E =-> SemEnv E' := 
  match E' with
  | nil    => fun m => terminal_morph (SemEnv E)
  | _ :: _ => fun m => <| SemMap (tlMap m) , Sem (hdMap m) |>
  end.
  (*=End *)

  Lemma SemShift : forall E E' (m : Map P E E') t, SemMap (shiftMap ops t m) =-= SemMap m << pi1.
  Proof. elim. 
  - move => E' m t. by apply: terminal_unique.
  - move => t s IH E' m ty.
    simpl. destruct (consMapInv m) as [r' [var eq]]. 
    subst. simpl. rewrite hdConsMap. rewrite tlConsMap.
  rewrite -> (IH E' r' ty). rewrite prod_fun_compl. unfold shiftMap, hdMap. by rewrite SemWk. 
  Qed.

  Lemma SemLift : forall E E' (m : Map P E E') t, SemMap (lift ops t m) =-= SemMap m >< Id. 
  Proof. move => E E' m t. simpl. unfold tlMap, hdMap. simpl lift. rewrite SemVr. rewrite SemShift.
  apply: prod_unique. rewrite prod_fun_fst. by rewrite prod_fun_fst. 
  rewrite prod_fun_snd. rewrite prod_fun_snd. by rewrite comp_idL. 
  Qed.

(*
  Lemma SemId : forall E E' (m : Map P E E'), SemMap (fun t (v:Var E t) => vr ops v) =-= Id.
  Proof. elim.
  - intros. simpl. by apply: terminal_unique.
  - intros. simpl. apply:prod_unique. simpl. rewrite <- H.  simpl in H. rewrite H.  simpl. rewrite H. rewrite tlConsMap hdConsMap. rewrite SemShift. rewrite IH. rewrite comp_idL. rewrite SemVr.
    apply: prod_unique. rewrite prod_fun_fst. by rewrite comp_idR. rewrite prod_fun_snd. by rewrite comp_idR. 
  Qed. 
*)
  Lemma SemCommutesWithMap E:
   (forall t (v : Value E t) E' (r : Map _ E E'), SemVal v << SemMap r =-= SemVal (mapVal ops r v))
/\ (forall t (exp : Exp E t) E' (r : Map _ E E'), SemExp exp << SemMap r =-= SemExp (mapExp ops r exp)).
  Proof. move: E ; apply ExpVal_ind.

  (* TINT *) by []. 
  (* TBOOL *) intros. simpl. by rewrite <- const_com. 

  (* TVAR *) 
  intros E ty var E' r.
  simpl. 
  induction var. 
  simpl. rewrite prod_fun_snd.
  destruct (consMapInv r) as [r' [v eq]]. subst.
  simpl. rewrite hdConsMap. unfold mapVal. unfold travVal. by rewrite SemVl. 
  destruct (consMapInv r) as [r' [v eq]]. subst.
  simpl. 
  specialize (IHvar r').
  rewrite <- IHvar. rewrite <- comp_assoc.
  rewrite tlConsMap. by rewrite prod_fun_fst.

  (* TFIX *)
  intros E t t1 body IH E' s. 
  specialize (IH _ (lift ops _ (lift ops _ s))).
  rewrite mapTFIX.
  simpl SemVal. rewrite <- comp_assoc.
  do 2 rewrite exp_comp. rewrite <- IH. rewrite SemLift. by rewrite SemLift. 

  (* TPAIR *)
  intros E t1 t2 v1 IH1 v2 IH2 E' s. rewrite mapTPAIR. simpl. rewrite <- IH1. rewrite <- IH2. by rewrite <- prod_fun_compl.

  (* TFST *)
  intros E t1 t2 v IH E' s. rewrite mapTFST. simpl. rewrite <- IH. by repeat (rewrite comp_assoc).

  (* TSND *)
  intros E t1 t2 v IH E' s. rewrite mapTSND. simpl. rewrite <- IH. by repeat (rewrite comp_assoc).

  (* TOP *)
  intros E n v1 IH1 v2 IH2 E' s. rewrite mapTOP. simpl.
  repeat (rewrite <- comp_assoc). rewrite <- IH1. rewrite <- IH2. by rewrite prod_fun_compl. 

  (* TGT *)
  intros E v1 IH1 v2 IH2 E' s. rewrite mapTGT. simpl. 
  repeat (rewrite <- comp_assoc). rewrite <- IH1. rewrite <- IH2. by rewrite prod_fun_compl.

  (* TVAL *)
  intros E t v IH E' s. rewrite mapTVAL. simpl.
  rewrite <- IH. by rewrite <- comp_assoc.

  (* TLET *)
  intros E t1 t2 e2 IH2 e1 IH1 E' s. rewrite mapTLET. simpl. 
  rewrite <- comp_assoc.
  specialize (IH2 _ s).
  specialize (IH1 _ (lift ops _ s)). 
  rewrite prod_fun_compl. rewrite KLEISLIR_comp.
  rewrite <- IH2. rewrite <- IH1. rewrite SemLift. 
  by do 2 rewrite comp_idL. 

  (* TAPP *)
  intros E t1 t2 v1 IH1 v2 IH2 E' s. rewrite mapTAPP. simpl. 
  rewrite <- comp_assoc. rewrite <- IH1. rewrite <- IH2. by rewrite prod_fun_compl.

  (* TIF *)
  intros E t ec IHc te1 IH1 te2 IH2 E' s. rewrite mapTIF. simpl.
  rewrite choose_comp. rewrite -> IH1. rewrite -> IH2. by rewrite -> IHc.
Qed.

End SEMMAP. 

Definition SemRen := SemMap SemVar. 
Definition SemSub := SemMap SemVal. 

Lemma SemCommutesWithRen E:
   (forall t (v : Value E t) E' (r : Ren E E'), SemVal v << SemRen r =-= SemVal (renameVal r v))
/\ (forall t (e : Exp E t)   E' (r : Ren E E'), SemExp e << SemRen r =-= SemExp (renameExp r e)).
Proof. by apply SemCommutesWithMap. Qed.

Lemma SemShiftRen : forall E E' (r : Ren E E') t, SemRen (shiftRen t r) =-= SemRen r << pi1.
Proof. by apply SemShift. Qed.

Lemma SemIdRen : forall E, SemRen (idRen E) =-= Id.
elim.
- simpl. by apply: terminal_unique.
- move => t E IH. simpl. rewrite idRenDef. rewrite tlConsMap.
  rewrite SemShiftRen. rewrite IH. rewrite comp_idL.
  by apply: prod_unique ; [rewrite prod_fun_fst | rewrite prod_fun_snd] ; rewrite comp_idR.
Qed.

(*=Substitution *)
Lemma SemCommutesWithSub E:
   (forall t (v : Value E t) E' (s : Sub E E'), SemVal v << SemSub s =-= SemVal (subVal s v))
/\ (forall t (e : Exp E t)   E' (s : Sub E E'), SemExp e << SemSub s =-= SemExp (subExp s e)).
(*=End *)
move: E. apply SemCommutesWithMap. 
+ by []. + by []. + intros. simpl.
rewrite <- (proj1 (SemCommutesWithRen E)). assert (SSR := SemShiftRen). unfold shiftRen in SSR. unfold shiftMap in SSR. simpl in SSR. 
specialize (SSR E E (fun t v => v) t'). simpl in SSR. 
assert ((fun ty' (var : Var E ty') => SVAR t' var) = (fun t0 => SVAR t')).  apply MapExtensional. auto. rewrite H in SSR. rewrite SSR.
rewrite SemIdRen. by rewrite comp_idL. 
Qed.
