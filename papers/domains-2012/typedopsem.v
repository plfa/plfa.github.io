(**********************************************************************************
 * typedopsem.v                                                                   *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                       *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)

Require Import Coq.Program.Equality.
Require Import typedlambda.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(*==========================================================================
  Evaluation relation
  ==========================================================================*)

(** printing =>> %\ensuremath{\Downarrow}% *)
(** printing n1 %\ensuremath{n_1}% *)
(** printing n2 %\ensuremath{n_2}% *)
(** printing v1 %\ensuremath{v_1}% *)
(** printing v2 %\ensuremath{v_2}% *)
(** printing e1 %\ensuremath{e_1}% *)
(** printing e2 %\ensuremath{e_2}% *)

Open Scope Sub_scope.
Notation "x '<v=' y" := (x <= y)%N (at level 55).
Reserved Notation "e =>> v" (at level 70, no associativity). 
(*=Ev *)
Inductive Ev: forall t, CExp t -> CValue t -> Prop :=
| e_Val: forall t (v : CValue t), TVAL v =>> v
| e_Op: forall op n1 n2, TOP op (TINT n1) (TINT n2) =>> TINT (op n1 n2)
| e_Gt : forall n1 n2, TGT (TINT n1) (TINT n2) =>> TBOOL (n2 <v=  n1)
| e_Fst : forall t1 t2 (v1 : CValue t1) (v2 : CValue t2), TFST (TPAIR v1 v2) =>> v1
| e_Snd : forall t1 t2 (v1 : CValue t1) (v2 : CValue t2), TSND (TPAIR v1 v2) =>> v2
| e_App : forall t1 t2 e (v1 : CValue t1) (v2 : CValue t2), 
            subExp [ v1, TFIX e ] e =>> v2 -> TAPP (TFIX e) v1 =>> v2
| e_Let : forall t1 t2 e1 e2 (v1 : CValue t1) (v2 : CValue t2), 
            e1 =>> v1 -> subExp [ v1 ] e2 =>> v2 -> TLET e1 e2 =>> v2
| e_IfTrue : forall t (e1 e2 : CExp t) v, e1 =>> v -> TIF (TBOOL true) e1 e2 =>> v
| e_IfFalse : forall t (e1 e2 : CExp t) v, e2 =>> v -> TIF (TBOOL false) e1 e2 =>> v
where "e '=>>' v" := (Ev e v).
(*=End *)
(*==========================================================================
  Determinacy of evaluation
  ==========================================================================*)

Lemma Determinacy: forall ty, forall (e : CExp ty) v1, e =>> v1 -> forall v2, e =>> v2 -> v1 = v2.
Proof.
intros ty e v1 Ev1. 
induction Ev1.

(* e_Val *)
intros v2 Ev2. dependent destruction Ev2; trivial. 
(* e_Op *)
intros v2 Ev2. dependent destruction Ev2; trivial.
(* e_Gt *)
intros v2 Ev2. dependent destruction Ev2; trivial.
(* e_Fst *)
intros v3 Ev3. dependent destruction Ev3; trivial.
(* e_Snd *)
intros v3 Ev3. dependent destruction Ev3; trivial.
(* e_App *)
intros v3 Ev3. dependent destruction Ev3; auto.  
(* e_Let *)
intros v3 Ev3. dependent destruction Ev3. rewrite (IHEv1_1 _ Ev3_1) in IHEv1_2. auto. 
(* e_IfTrue *)
intros v3 Ev3. dependent destruction Ev3; auto. 
(* e_IfFalse *)
intros v3 Ev3. dependent destruction Ev3; auto.
Qed.

Unset Implicit Arguments.
