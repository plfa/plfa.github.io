(**********************************************************************************
 * uniisound.v                                                                    *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                       *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)

(* soundness of semantics of unityped lambda calculus *)

Require Import PredomAll.
Require Import ssrnat. 
Require Import uniisem uniiop Fin.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section SEMMAP.

  Variable P : Env -> Type.
  Variable ops : Map.Ops P.
  Variable Sem : forall E, P E -> SemEnv E =-> VInf.
  Variable SemVl : forall E (v : P E), Sem v =-= SemVal (Map.vl ops v). 
  Variable SemVr : forall E, Sem (Map.vr ops (FinZ E)) =-= pi2.
  Variable SemWk : forall E (v : P E), Sem (Map.wk ops v) =-= Sem v << pi1. 

  Fixpoint SemMap E E' : Map.Map P E' E -> SemEnv E =-> SemEnv E' :=
  match E' with
  | O   => fun m => terminal_morph (SemEnv E)
  | S _ => fun m => <| SemMap (tl m), Sem (hd m) |>
  end. 

  Lemma SemShift : forall E E' (m : Map.Map P E E'), SemMap (Map.shift ops m) =-= SemMap m << pi1.
  Proof. elim.
  - move => E' m. by apply: terminal_unique.
  - move => E IH E' m.
    rewrite -> (consEta m) at 1. rewrite Map.shiftCons. simpl. rewrite -> (IH E' (tl m)). rewrite prod_fun_compl. unfold Map.shift, hd. by rewrite SemWk. 
  Qed.

  Lemma SemLift : forall E E' (m : Map.Map P E E'), SemMap (Map.lift ops m) =-= SemMap m >< Id.
  Proof. move => E E' m. simpl. unfold tl, hd. simpl Map.lift. rewrite SemVr. rewrite SemShift.
  apply: prod_unique. rewrite prod_fun_fst. by rewrite prod_fun_fst. 
  rewrite prod_fun_snd. rewrite prod_fun_snd. by rewrite comp_idL. 
  Qed.

  Lemma SemId : forall E, SemMap (@Map.id P ops E) =-= Id.
  Proof. elim.
  - simpl. by apply: terminal_unique.
  - move => env IH. rewrite Map.idAsCons. simpl. rewrite tlCons hdCons. rewrite SemShift. rewrite IH. rewrite comp_idL. rewrite SemVr.
    apply: prod_unique. rewrite prod_fun_fst. by rewrite comp_idR. rewrite prod_fun_snd. by rewrite comp_idR. 
  Qed. 

  Lemma SemCommutesWithMap E :
     (forall (v : Value E) E' (r : Map.Map _ E E'), SemVal v << SemMap r =-= SemVal (Map.mapVal ops r v))
  /\ (forall (e : Exp E) E'   (r : Map.Map _ E E'), SemExp e << SemMap r =-= SemExp (Map.mapExp ops r e)).
  Proof. move: E ; apply ExpValue_ind.
  (* VAR *)
  - move => n v n' s. SimplMap. simpl. 
    induction v.
    + rewrite (consEta s). simpl. rewrite prod_fun_snd hdCons. by rewrite SemVl.
    + rewrite (consEta s). simpl. rewrite <- IHv. rewrite <- comp_assoc. by rewrite prod_fun_fst tlCons. 
  (* INT *)
  - move => n body n' s. SimplMap. simpl. rewrite <- comp_assoc. by rewrite <- const_com.
  (* LAMBDA *)
  - move => n body IH n' s. SimplMap. simpl SemVal. 
    rewrite <- (IH _ (Map.lift _ s)). rewrite SemLift. do 4 rewrite <- comp_assoc. apply: comp_eq_compat ; first by [].
    apply: exp_unique. rewrite <- (comp_assoc pi1 (SemMap s)). rewrite <- prod_map_prod_fun.
    rewrite (comp_assoc _ _ ev). rewrite exp_com. do 2 rewrite <- comp_assoc. rewrite prod_map_prod_fun. rewrite comp_idL. 
    rewrite prod_fun_compl. rewrite <- comp_assoc. rewrite prod_fun_fst. rewrite prod_fun_snd. by do 2 rewrite comp_idL. 
  (* VAL *)
  - move => n v IH n' s. SimplMap. simpl. rewrite <- comp_assoc. by rewrite IH. 
  (* APP *)
  - move => n v IH v' IH' n' s. SimplMap. simpl. rewrite <- IH. rewrite <- IH'.
    rewrite <- comp_assoc. rewrite prod_fun_compl. by repeat (rewrite <- comp_assoc).
  (* LET *)
  - move => n e IH e' IH' n' s. SimplMap. simpl.
    rewrite <- comp_assoc. rewrite prod_fun_compl. rewrite IH. rewrite exp_comp. rewrite <- IH'. rewrite SemLift.
    rewrite <- (comp_idL (SemExp (Map.mapExp ops s e))). rewrite <- (comp_idR (exp_fun _)).
    rewrite <- (prod_map_prod_fun (exp_fun (KLEISLIR (SemExp e') << SemMap s >< Id))).
    rewrite comp_assoc. rewrite exp_com. rewrite <- comp_assoc. rewrite prod_map_prod_fun.
    rewrite comp_idR. rewrite comp_idL.
    rewrite <- (comp_idR (exp_fun _)). rewrite <- (comp_idL (SemExp (Map.mapExp ops s e))). rewrite <- prod_map_prod_fun.
    rewrite comp_assoc. rewrite exp_com. rewrite KLEISLIR_comp. by do 2 rewrite comp_idL.
  (* IFZ *)
  - move => n v IH e0 IH0 e1 IH1 n' s.
    SimplMap. simpl. repeat rewrite <- comp_assoc. repeat rewrite prod_fun_compl.
    repeat rewrite comp_idL. do 2 rewrite prod_fun_snd. rewrite <- comp_assoc. rewrite prod_fun_fst.
    rewrite IH. clear IH. rewrite <- comp_assoc. rewrite prod_fun_fst.
    apply: fmon_eq_intro => x. simpl. case: ((SemVal (Map.mapVal _ s v)) x) ; simpl.
    + case.
      * simpl. do 2 rewrite SUM_fun_simplx. simpl. do 2 rewrite SUM_fun_simplx. apply: (fmon_eq_elim (IH0 _ s) x). 
      * simpl => nn. do 2 rewrite SUM_fun_simplx. simpl. do 2 rewrite SUM_fun_simplx. apply (fmon_eq_elim (IH1 _ s) x). 
    + simpl. move => m. do 2 rewrite SUM_fun_simplx. by split ; apply: leastP.
  (* OP *)
  - move => n op v0 IH0 v1 IH1 v s. 
    SimplMap. simpl.
    by (repeat rewrite <- comp_assoc; repeat rewrite prod_fun_compl; repeat rewrite <- comp_assoc; rewrite IH1; rewrite IH0). 
  Qed.

End SEMMAP.

Definition SemRen := SemMap SemVar. 
Definition SemSub := SemMap SemVal. 

Lemma SemCommutesWithRen E:
   (forall (v : Value E) E' (r : Ren E E'), SemVal v << SemRen r =-= SemVal (renVal r v))
/\ (forall (e : Exp E)   E' (r : Ren E E'), SemExp e << SemRen r =-= SemExp (renExp r e)).
Proof. by apply SemCommutesWithMap. Qed.

Lemma SemShiftRen : forall E E' (r : Ren E E'), SemRen (shiftRen r) =-= SemRen r << pi1.
Proof. by apply SemShift. Qed.

Lemma SemIdRen : forall E, SemRen (@idRen E) =-= Id. 
Proof. by apply SemId. Qed.  


(*=Substitution *)
Lemma SemCommutesWithSub E:
   (forall (v : Value E) E' (s : Sub E E'), SemVal v << SemSub s =-= SemVal (subVal s v))
/\ (forall (e : Exp E)   E' (s : Sub E E'), SemExp e << SemSub s =-= SemExp (subExp s e)).
(*=End *)
Proof. move: E ; apply SemCommutesWithMap.
+ by []. + by []. + intros. simpl. rewrite <- (proj1 (SemCommutesWithRen E)). rewrite SemShiftRen. rewrite SemIdRen. by rewrite comp_idL.  
Qed. 

(*=Soundness *)
Lemma Soundness e v : (e =>> v) -> SemExp e =-= eta << SemVal v.
(*=End *)
Proof. move => D. elim: e v / D.
- by [].
- move => e v v' D IH. simpl.
  repeat rewrite <- comp_assoc. rewrite <- (comp_idR ([|_,_|] << _)). rewrite <- (comp_idL (Roll << _)).
  rewrite <- prod_map_prod_fun.
  rewrite (comp_assoc _ _ ev). rewrite (comp_assoc _ in2). rewrite sum_fun_snd.
  rewrite (comp_idL (exp_fun _)). rewrite exp_com. repeat rewrite <- comp_assoc.
   rewrite comp_assoc. rewrite <- kleisli_comp2. rewrite <- comp_assoc.
  rewrite UR_id. rewrite comp_idR. rewrite kleisli_unit. rewrite comp_idL.
  rewrite prod_map_prod_fun. rewrite comp_idR. rewrite comp_assoc. rewrite UR_id.
  rewrite comp_idL. 
  rewrite <- (proj2 (SemCommutesWithSub _) e _ ([v] %sub)) in IH.
  rewrite <- IH. simpl. rewrite (terminal_unique Id _). by []. 
- move => e0 v0 e1 v1 D0 IH0 D1 IH1.
  simpl. rewrite IH0. clear IH0 D0.
  rewrite <- (comp_idL (eta << _)). rewrite <- (comp_idR (exp_fun _)). rewrite <- prod_map_prod_fun.
  rewrite comp_assoc. rewrite exp_com. rewrite KLEISLIR_unit. 
  rewrite <- (proj2 (SemCommutesWithSub 1%N) e1 _ ([ v0]%sub)) in IH1. simpl in IH1.
  rewrite <- IH1. rewrite (terminal_unique Id (terminal_morph One)).  by []. 
- move => e0 e1 v0 _ IH. simpl. repeat rewrite <- comp_assoc. rewrite prod_map_prod_fun.
  rewrite comp_assoc. rewrite sum_fun_fst. rewrite <- IH. clear IH.
  rewrite <- comp_assoc.
  have X:(zeroCase << @const One (discrete_cpoType nat) 0%N) =-= in1 by apply: fmon_eq_intro ; case.
  rewrite X. clear X. rewrite sum_fun_fst. rewrite <- (comp_idR (exp_fun _)). rewrite <- prod_map_prod_fun.
  rewrite comp_assoc. rewrite exp_com. rewrite <- comp_assoc. rewrite prod_fun_snd. by rewrite comp_idR.
- move => e0 e1 v0 n _ IH. simpl. repeat rewrite <- comp_assoc. rewrite prod_map_prod_fun.
  rewrite comp_assoc. rewrite sum_fun_fst. rewrite <- IH. clear IH.
  rewrite <- comp_assoc.
  have X:(zeroCase << @const One (discrete_cpoType nat) n.+1%N) =-= in2 << @const One (discrete_cpoType nat) n by apply: fmon_eq_intro ; case.
  rewrite X. clear X. rewrite comp_assoc. rewrite sum_fun_snd.
  rewrite <- prod_map_prod_fun. rewrite comp_assoc. rewrite exp_com. rewrite <- comp_assoc. rewrite prod_fun_snd.
  by rewrite comp_idR.
- move => op n n'. simpl. repeat rewrite comp_assoc. rewrite sum_fun_fst. simpl.
  rewrite <- (prod_map_prod_fun eta).  do 2 rewrite <- comp_assoc.
  rewrite (comp_assoc _ _ ev). rewrite - {1} (comp_idL pi2).
  rewrite (comp_assoc _ (eta >< eta)).
  have e:((ev << Smash (discrete_cpoType nat) (discrete_cpoType nat) >< Id) <<
     eta >< eta) =-= eta by apply: fmon_eq_intro => a; simpl ; unfold Smash ; simpl ; rewrite Operator2_simpl ; case: a.
  rewrite -> e. clear e. rewrite comp_assoc. rewrite kleisli_eta_com. 
  rewrite <- comp_assoc. by apply:fmon_eq_intro.
Qed.

