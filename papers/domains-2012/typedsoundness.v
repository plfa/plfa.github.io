(**********************************************************************************
 * typedsoundness.v                                                               *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                       *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)

Require Import PredomAll.
Require Import typeddensem.
Require Import typedopsem.
Require Import typedsubst.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(*=Soundness *)
Theorem Soundness: forall t (e : CExp t) v, e =>> v -> SemExp e =-= eta  << SemVal v.
(*=End *)
Proof.
intros t e v Ev.
induction Ev.

(* e_Val *)
simpl. trivial.

(* e_Op *)
simpl. rewrite <- comp_assoc. by apply: fmon_eq_intro.

(* e_Gt *)
simpl. by apply: fmon_eq_intro.

(* e_Fst *)
simpl. rewrite <- comp_assoc. by rewrite prod_fun_fst.

(* e_Snd *)
simpl. rewrite <- comp_assoc. by rewrite prod_fun_snd.

(* e_App *)
rewrite <- IHEv. clear IHEv. clear Ev.

rewrite <- (proj2 (SemCommutesWithSub _) _ e nil (consMap v1 (consMap (TFIX e) (idSub _)))). 
simpl. rewrite hdConsMap. rewrite -> (terminal_unique _ Id). simpl.
have a:= (@prod_fun_eq_compat cpoProdCatType _ _ _ _ _ (FIXP_com (exp_fun (exp_fun (SemExp e)))) _).
specialize (a _ (SemVal v1) (SemVal v1) (tset_refl _)). rewrite a. clear a.
rewrite - [FIXP << exp_fun _] comp_idL.
rewrite - {1} [exp_fun _] comp_idR.
rewrite - prod_map_prod_fun. rewrite comp_assoc. rewrite exp_com.
rewrite - {1} [SemVal _] comp_idL. rewrite - prod_map_prod_fun. rewrite comp_assoc. by rewrite exp_com.

(* e_Let *)
simpl. rewrite <- IHEv2. clear IHEv2.
rewrite <- (proj2 (SemCommutesWithSub _) _ _ _).
simpl. rewrite <- (KLEISLIR_unit (SemExp e2) (SemVal v1) _).
rewrite <- IHEv1. clear IHEv1.
by rewrite <- (terminal_unique Id _).

(* e_Iftrue *)
simpl. rewrite IHEv. by apply: fmon_eq_intro.

(* e_Iffalse *)
simpl. rewrite IHEv. by apply: fmon_eq_intro.
Qed.
