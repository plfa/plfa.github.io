Require Import utility.
Require Import PredomAll.
Require Import typeddensem.
Require Import typedopsem.
Require Import typedsubst.

Set Implicit Arguments.
Unset Strict Implicit.

Theorem Soundness: forall ty (e : CExp ty) v, e =>> v -> SemExp e == eta << SemVal v.
Proof.
intros t e v Ev.
induction Ev. 

(* e_Val *)
simpl. trivial.

(* e_Op *)
simpl. rewrite fcont_comp_assoc. apply fcont_eq_intro; auto.

(* e_Gt *)
simpl. apply fcont_eq_intro; auto. 

(* e_Fst *)
simpl. apply fcont_eq_intro; auto.

(* e_Snd *)
simpl. apply fcont_eq_intro; auto.  

(* e_App *)
rewrite <- IHEv. clear IHEv. clear Ev.

rewrite <- (proj2 SemCommutesWithSubst _ _ e nil (consMap v1 (consMap (TFIX e) (idSubst _)))). 
simpl.
assert (H := DOne_final (D := DOne) ID (K DOne (tt:DOne))). rewrite <- H.
rewrite hdConsMap. 
rewrite FIXP_com at 1. refine (fcont_eq_intro _) ; auto.

(* e_Let *)
simpl. rewrite <- IHEv2. clear IHEv2.
rewrite <- (proj2 SemCommutesWithSubst _ _ e2 _ (consMap v1 (idSubst _))).
simpl. rewrite <- (KLEISLIR_unit (SemExp e2) (SemVal v1) (K DOne (tt:DOne))).
rewrite <- IHEv1. clear IHEv1.
rewrite (DOne_final (D := DOne) ID (K DOne (tt:DOne))).
trivial.

(* e_Iftrue *)
simpl. apply fcont_eq_intro; auto. 

(* e_Iffalse *)
simpl. apply fcont_eq_intro; auto.
Qed.
