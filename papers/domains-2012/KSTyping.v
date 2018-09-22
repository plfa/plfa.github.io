(**********************************************************************************
 * KSTyping.v                                                                   *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                       *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)

(* Typing relation for kitchen sink language *)

Require Export ssreflect ssrnat. Require Import KSTy. Require Import KSTm.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Require Import Fin.

Definition StoreType E := nat -> Ty.Ty E.

Definition TEnv E n := FMap n (Ty.Ty E).
Definition shiftTy E : Ty.Ty E -> Ty.Ty E.+1 := Ty.renTy (fun v => FinS v). 
Definition subOneTy E (t' : Ty.Ty E) t := Ty.subTy (cons t' (@Ty.idSub _)) t. 
Definition unfoldTy E (t : Ty.Ty E.+1) := subOneTy (Ty.Mu t) t.

Require Import Program.

Definition emptyTEnv : TEnv O O.
move => var. dependent destruction var.
Defined.

Import Tm.
Inductive VTy E (se:StoreType E) : forall n, TEnv E n -> Tm.Value n -> Ty.Ty E -> Type :=
  | TvVAR: forall n (env : TEnv E n) v, VTy se env (VAR v) (env v)
  | TvLOC: forall n (env : TEnv E n) l, VTy se env (LOC l) (Ty.Ref (se l))
  | TvINT: forall n (env : TEnv E n) i , VTy se env (INT i) Ty.Int
  | TvUNIT: forall n (env : TEnv E n), VTy se env UNIT Ty.Unit
  | TvLAM: forall n (env : TEnv E n) t1 t2 e, ETy se (cons t1 env) e t2 -> VTy se env (LAM e) (t1 --> t2)
  | TvTLAM: forall n (env : TEnv E n) t e, ETy (E:=E.+1) (fun l => shiftTy (se l)) (fun v => shiftTy (env v)) e t -> VTy se env (TLAM e) (Ty.All t)
  | TvPAIR: forall n (env : TEnv E n) t1 t2 e1 e2, VTy se env e1 t1 -> VTy se env e2 t2 -> VTy se env (PAIR e1 e2) (t1 ** t2)
  | TvINL: forall n (env:TEnv E n) v t1 t2, VTy se env v t1 -> VTy se env (INL v) (Ty.Sum t1 t2)
  | TvINR: forall n (env:TEnv E n) v t1 t2, VTy se env v t2 -> VTy se env (INR v) (Ty.Sum t1 t2)
  | TvFOLD: forall n (env:TEnv E n) v t, VTy se env v (unfoldTy t) -> VTy se env (FOLD v) (Ty.Mu t)

with ETy E (se:StoreType E) : forall n, TEnv E n -> Tm.Exp n -> Ty.Ty E -> Type :=
  | TeVAL: forall n (env:TEnv E n) v t, VTy se env v t -> ETy se env (VAL v) t
  | TeLET: forall n (env:TEnv E n) e1 e2 t1 t2, ETy se env e1 t1 -> ETy se (cons t1 env) e2 t2 -> ETy se env (LET e1 e2) t2
  | TvFST: forall n (env:TEnv E n) v t1 t2, VTy se env v (t1**t2) -> ETy se env (FST v) t1
  | TvSND: forall n (env:TEnv E n) v t1 t2, VTy se env v (t1**t2) -> ETy se env (SND v) t2
  | TvOP: forall n (env:TEnv E n) op v, VTy se env v (Ty.Int**Ty.Int) -> ETy se env (OP op v) Ty.Int
  | TvUNFOLD: forall n (env:TEnv E n) t v, VTy se env v (Ty.Mu t) -> ETy se env (UNFOLD v) (unfoldTy t)
  | TvREF: forall n (env:TEnv E n) v t, VTy se env v t -> ETy se env (REF v) (Ty.Ref t)
  | TvBANG: forall n (env:TEnv E n) v t, VTy se env v (Ty.Ref t) -> ETy se env (BANG v) t
  | TvASSIGN: forall n (env:TEnv E n) v1 v2 t, VTy se env v1 (Ty.Ref t) -> VTy se env v2 t -> ETy se env (ASSIGN v1 v2) Ty.Unit
  | TeAPP: forall n (env:TEnv E n) t1 t2 v1 v2, VTy se env v1 (t1 --> t2) -> VTy se env v2 t1 -> ETy se env (APP v1 v2) t2
  | TeTAPP: forall n (env:TEnv E n) t v t', VTy se env v (Ty.All t) -> ETy se env (TAPP v) (subOneTy t' t)
  | TeCASE: forall n (env:TEnv E n) t1 t2 v e1 e2 t, VTy se env v (Ty.Sum t1 t2) -> ETy se (cons t1 env) e1 t -> ETy se (cons t2 env) e2 t -> ETy se env (CASE v e1 e2) t
.

Hint Resolve TvINT TeAPP TeCASE TeLET TeVAL TvVAR TvTLAM TLAM TvOP TvINL TvINR TvPAIR TvSND TvFST TvASSIGN TvBANG TvREF.

Scheme VTy_rec2 := Induction for VTy Sort Set
  with ETy_rec2 := Induction for ETy Sort Set.

Scheme VTy_rect2 := Induction for VTy Sort Type
  with ETy_rect2 := Induction for ETy Sort Type.

Scheme VTy_ind2 := Induction for VTy Sort Prop
  with ETy_ind2 := Induction for ETy Sort Prop.

Combined Scheme Typing_ind from VTy_ind2, ETy_ind2.

