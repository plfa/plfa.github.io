(* typedopsem.v
   Standard operational semantics 
*)
Require Import utility.
Require Import Coq.Program.Equality.
Require Import EqdepFacts. 
Require Import typedlambda.

Set Implicit Arguments.
Unset Strict Implicit.

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
Reserved Notation "e =>> v" (at level 70, no associativity). 

Open Scope Subst_scope.
Inductive Ev: forall ty, CExp ty -> CValue ty -> Prop :=
| e_Val: forall ty (v : CValue ty), TVAL v =>> v
| e_Op: forall op n1 n2, TOP op (TINT n1) (TINT n2) =>> TINT (op n1 n2)
| e_Gt      : forall n1 n2, TGT (TINT n1) (TINT n2) =>> TBOOL (ble_nat n2 n1)
| e_Fst     : forall ty1 ty2 (v1 : CValue ty1) (v2 : CValue ty2), TFST (TPAIR v1 v2) =>> v1
| e_Snd     : forall ty1 ty2 (v1 : CValue ty1) (v2 : CValue ty2), TSND (TPAIR v1 v2) =>> v2
| e_App     : forall ty1 ty2 e (v1 : CValue ty1) (v2 : CValue ty2), substExp [ v1, TFIX e ] e =>> v2 -> TAPP (TFIX e) v1 =>> v2
| e_Let     : forall ty1 ty2 e1 e2 (v1 : CValue ty1) (v2 : CValue ty2), e1 =>> v1 -> substExp [ v1 ] e2 =>> v2 -> TLET e1 e2 =>> v2
| e_IfTrue  : forall ty (e1 e2 : CExp ty) v, e1 =>> v -> TIF (TBOOL true) e1 e2 =>> v
| e_IfFalse : forall ty (e1 e2 : CExp ty) v, e2 =>> v -> TIF (TBOOL false) e1 e2 =>> v
where "e '=>>' v" := (Ev e v).

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
intros v3 Ev3. dependent destruction Ev3. rewrite (IHEv1_1 _ Ev3_1) in *. auto. 
(* e_IfTrue *)
intros v3 Ev3. dependent destruction Ev3; auto. 
(* e_IfFalse *)
intros v3 Ev3. dependent destruction Ev3; auto.
Qed.

Unset Implicit Arguments.
