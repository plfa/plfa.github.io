(**********************************************************************************
 * KSTy.v                                                                         *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                       *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)

(* Kitchen sink language, well-scoped by construction *)

Require Export ssreflect ssrnat.
Require Import Program.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Require Import Fin.

Ltac Rewrites E := 
  (intros; simpl; try rewrite E; 
   repeat (match goal with | [H : context[eq _ _] |- _] => rewrite H end); 
   auto).

Module Tm.

Definition Env := nat.
Definition Var := Fin.

(*=ValueExp *)
Inductive Value E :=
| VAR: Var E -> Value E
| LOC: nat -> Value E
| INT: nat -> Value E
| TLAM: Exp E -> Value E
| LAM: Exp E.+1 -> Value E
| UNIT : Value E
| PAIR: Value E -> Value E -> Value E
| INL : Value E -> Value E
| INR : Value E -> Value E
| FOLD : Value E -> Value E
with Exp E :=
| VAL: Value E -> Exp E
| FST: Value E -> Exp E
| SND: Value E -> Exp E
| OP: (nat -> nat -> nat) -> Value E -> Exp E
| UNFOLD: Value E -> Exp E
| REF: Value E -> Exp E
| BANG: Value E -> Exp E
| ASSIGN: Value E -> Value E -> Exp E
| LET: Exp E -> Exp E.+1 -> Exp E
| APP: Value E -> Value E -> Exp E
| TAPP: Value E -> Exp E
| CASE: Value E -> Exp E.+1 -> Exp E.+1 -> Exp E.
(*=End *)


Implicit Arguments INT [E].
Implicit Arguments LOC [E].
Implicit Arguments UNIT [E].

Scheme Value_ind2 := Induction for Value Sort Prop
  with Exp_ind2   := Induction for Exp Sort Prop.
Combined Scheme ExpValue_ind from Value_ind2, Exp_ind2.

(*==========================================================================
  Variable-domain maps. 
  By instantiating P with Var we get renamings.
  By instantiating P with Value we get substitutions.
  ==========================================================================*)
Module Map. 

Section MAP.

  Variable P : Env -> Type.
  Definition Map E E' := FMap E (P E').

  (*==========================================================================
    Package of operations used with a Map
      vr maps a Var into Var or Value (so is either the identity or TVAR)
      vl maps a Var or Value to a Value (so is either TVAR or the identity)
      wk weakens a Var or Value (so is either SVAR or renaming through SVAR on a value)
    ==========================================================================*)
  Record Ops :=
  {
    vr : forall E, Var E -> P E;   
    vl : forall E, P E -> Value E;
    wk : forall E, P E -> P E.+1;
    wkvr : forall E (var : Var E), wk (vr var) = vr (FinS var);
    vlvr : forall E (var : Var E), vl (vr var) = VAR var
  }.
  Variable ops : Ops.

  Definition lift E E' (m : Map E E') : Map E.+1 E'.+1 :=
  (fun var => match var in Fin E return Map E.-1 E' -> P E'.+1 with
  | FinZ _   => fun _ => vr ops (FinZ _)
  | FinS _ x => fun m => wk ops (m x)
  end m).

  Definition shift E E' (m : Map E E') : Map E E'.+1 := fun var => wk ops (m var).
  Definition id E : Map E E := fun (var : Var E) => vr ops var.

  Lemma shiftCons : forall E E' (m : Map E E') (x : P E'), shift (cons x m) = cons (wk ops x) (shift m). 
  Proof. move => E E' m x. apply Extensionality. intros var. by dependent destruction var. Qed.

  Lemma liftAsCons : forall E E' (m : Map E' E), lift m = cons (vr ops (FinZ _)) (shift m).
  Proof. move => E E' m. apply Extensionality. intros var. by dependent destruction var. Qed.

  Fixpoint mapVal E E' (m : Map E E') (v : Value E) : Value E' :=
  match v with
    | VAR v => vl ops (m v)
    | INT i => INT i
    | LAM e => LAM (mapExp (lift m) e)
    | TLAM e => TLAM (mapExp m e)
    | LOC l => LOC l
    | UNIT => UNIT
    | PAIR v1 v2 => PAIR (mapVal m v1) (mapVal m v2)
    | INL v => INL (mapVal m v)
    | INR v => INR (mapVal m v)
    | FOLD v => FOLD (mapVal m v)
  end
  with mapExp E E' (m : Map E E') (e : Exp E) : Exp E' :=
  match e with
    | VAL v => VAL (mapVal m v)
    | APP v0 v1 => APP (mapVal m v0) (mapVal m v1)
    | LET e0 e1 => LET (mapExp m e0) (mapExp (lift m) e1)
    | FST v => FST (mapVal m v)
    | SND v => SND (mapVal m v)
    | UNFOLD v => UNFOLD (mapVal m v)
    | OP op v => OP op (mapVal m v) 
    | REF v => REF (mapVal m v)
    | ASSIGN v1 v2 => ASSIGN (mapVal m v1) (mapVal m v2)
    | BANG v => BANG (mapVal m v)
    | TAPP v => TAPP (mapVal m v)
    | CASE v e1 e2 => CASE (mapVal m v) (mapExp (lift m) e1) (mapExp (lift m) e2)
  end.

  Variable E E' : Env.
  Variable m : Map E E'.
  Lemma mapVAR : forall (var : Var _), mapVal m (VAR var) = vl ops (m var). by []. Qed. 
  Lemma mapINT : forall n, mapVal m (INT n) = INT n. by []. Qed.
  Lemma mapLOC : forall n, mapVal m (LOC n) = LOC n. by []. Qed.
  Lemma mapLAM : forall (e : Exp _), mapVal m (LAM e) = LAM (mapExp (lift m) e). by []. Qed.
  Lemma mapOP : forall op v, mapExp m (OP op v) = OP op (mapVal m v). by []. Qed.
  Lemma mapVAL : forall (v : Value _), mapExp m (VAL v) = VAL (mapVal m v). by []. Qed.
  Lemma mapLET : forall (e1 : Exp _) (e2 : Exp _), mapExp m (LET e1 e2) = LET (mapExp m e1) (mapExp (lift m) e2). by []. Qed.
  Lemma mapAPP : forall (v1 : Value _) v2, mapExp m (APP v1 v2) = APP (mapVal m v1) (mapVal m v2). by []. Qed.
  Lemma mapPAIR : forall v1 v2, mapVal m (PAIR v1 v2) = PAIR (mapVal m v1) (mapVal m v2). by []. Qed.
  Lemma mapINL : forall v, mapVal m (INL v) = INL (mapVal m v). by []. Qed.
  Lemma mapINR : forall v, mapVal m (INR v) = INR (mapVal m v). by []. Qed. 
  Lemma mapFOLD : forall v, mapVal m (FOLD v) = FOLD (mapVal m v). by []. Qed.
  Lemma mapTLAM : forall e, mapVal m (TLAM e) = TLAM (mapExp m e). by []. Qed.
  Lemma mapUNIT : mapVal m UNIT = UNIT. by []. Qed.
  Lemma mapFST : forall v, mapExp m (FST v) = FST (mapVal m v). by []. Qed.
  Lemma mapSND : forall v, mapExp m (SND v) = SND (mapVal m v). by []. Qed.
  Lemma mapBANG : forall v, mapExp m (BANG v) = BANG (mapVal m v). by [].  Qed.
  Lemma mapREF : forall v, mapExp m (REF v) = REF (mapVal m v). by []. Qed.
  Lemma mapASSIGN : forall v1 v2, mapExp m (ASSIGN v1 v2) = ASSIGN (mapVal m v1) (mapVal m v2). by []. Qed.
  Lemma mapTAPP : forall v, mapExp m (TAPP v) = TAPP (mapVal m v). by []. Qed.
  Lemma mapUNFOLD : forall v, mapExp m (UNFOLD v) = UNFOLD (mapVal m v). by []. Qed.
  Lemma mapCASE : forall v e1 e2, mapExp m (CASE v e1 e2) = CASE (mapVal m v) (mapExp (lift m) e1) (mapExp (lift m) e2). by []. Qed.    

  Lemma liftId : lift (@id E) = @id E.+1.
  Proof. apply Extensionality. intros var. dependent destruction var; [by [] | by apply wkvr].  
  Qed.

  Lemma idAsCons : @id E.+1 = cons (vr ops (FinZ _)) (shift (@id E)).
  Proof. apply Extensionality. intros var. dependent destruction var; first by []. unfold id, shift. simpl. by rewrite wkvr. Qed.

End MAP. 

Hint Rewrite mapVAR mapINT mapLAM mapOP mapVAL mapLET mapAPP mapPAIR mapINL mapINR mapFOLD mapTLAM mapUNIT mapFST mapSND mapBANG mapREF mapASSIGN mapTAPP mapUNFOLD mapCASE : mapHints.
Implicit Arguments id [P].

Lemma applyId P (ops:Ops P) E : 
     (forall (v : Value E), mapVal ops (id ops E) v = v)
  /\ (forall (e : Exp E), mapExp ops (id ops E) e = e).
Proof. move: E ; apply ExpValue_ind; intros; autorewrite with mapHints; Rewrites liftId. by apply vlvr. 
Qed.

End Map. 

(*==========================================================================
  Variable renamings: Map Var
  ==========================================================================*)

Definition Ren   := Map.Map Var. 
Definition RenOps : Map.Ops Var. refine (@Map.Build_Ops _ (fun _ v => v) VAR FinS _ _). by []. by [].  Defined. 

Definition renVal := Map.mapVal RenOps.
Definition renExp := Map.mapExp RenOps.
Definition liftRen := Map.lift RenOps.
Definition shiftRen := Map.shift RenOps.
Definition idRen := Map.id RenOps.

(*==========================================================================
  Composition of renaming
  ==========================================================================*)

Definition composeRen P E E' E'' (m : Map.Map P E' E'') (r : Ren E E') : Map.Map P E E'' := fun var => m (r var). 

Lemma liftComposeRen : forall E E' E'' P ops (m:Map.Map P E' E'') (r:Ren E E'), Map.lift ops (composeRen m r) = composeRen (Map.lift ops m) (liftRen r).
Proof. move => E E' E'' P ops m r. apply Extensionality. intros var. by dependent destruction var. Qed.

Lemma applyComposeRen E : 
 (forall (v : Value E) E' E'' P ops (m:Map.Map P E' E'') (s : Ren E E'),
  Map.mapVal ops (composeRen m s) v = Map.mapVal ops m (renVal s v))
  /\ (forall (e : Exp   E) E' E'' P ops (m:Map.Map P E' E'') (s : Ren E E'),
    Map.mapExp ops (composeRen m s) e = Map.mapExp ops m (renExp s e)).
Proof.
move: E ; apply ExpValue_ind; intros; autorewrite with mapHints; Rewrites liftComposeRen. Qed.

(*==========================================================================
  Substitution
  ==========================================================================*)

Definition Sub := Map.Map Value.
Definition SubOps : Map.Ops Value. refine (@Map.Build_Ops _ VAR (fun _ v => v) (fun E => renVal (fun v => FinS v)) _ _). by []. by []. Defined.

Definition subVal := Map.mapVal SubOps.
Definition subExp := Map.mapExp SubOps.
Definition shiftSub := Map.shift SubOps.
Definition liftSub := Map.lift SubOps.
Definition idSub := Map.id SubOps.

Ltac UnfoldRenSub := (unfold subVal; unfold subExp; unfold renVal; unfold renExp; unfold liftSub; unfold liftRen).
Ltac FoldRenSub := (fold subVal; fold subExp; fold renVal; fold renExp; fold liftSub; fold liftRen).
Ltac SimplMap := (UnfoldRenSub; autorewrite with mapHints; FoldRenSub).

(*==========================================================================
  Composition of substitution followed by renaming
  ==========================================================================*)
Definition composeRenSub E E' E'' (r : Ren E' E'') (s : Sub E E') : Sub E E'' := fun var => renVal r (s var). 

Lemma liftComposeRenSub : forall E E' E'' (r:Ren E' E'') (s:Sub E E'), liftSub (composeRenSub r s) = composeRenSub (liftRen r) (liftSub s).
intros. apply Extensionality. intros var. dependent destruction var; first by [].
unfold composeRenSub, liftSub. simpl. unfold renVal at 1 3. by do 2 rewrite <- (proj1 (applyComposeRen _)). 
Qed.

Lemma applyComposeRenSub E :
   (forall (v:Value E) E' E'' (r:Ren E' E'') (s : Sub E E'),
    subVal (composeRenSub r s) v = renVal r (subVal s v))
/\ (forall (e:Exp   E) E' E'' (r:Ren E' E'') (s : Sub E E'),
    subExp (composeRenSub r s) e = renExp r (subExp s e)).
Proof. move: E ; apply ExpValue_ind; intros; SimplMap; Rewrites liftComposeRenSub. Qed. 

(*==========================================================================
  Composition of substitutions
  ==========================================================================*)

Definition composeSub E E' E'' (s' : Sub E' E'') (s : Sub E E') : Sub E E'' := fun var => subVal s' (s var). 

Lemma liftComposeSub : forall E E' E'' (s' : Sub E' E'') (s : Sub E E'), liftSub (composeSub s' s) = composeSub (liftSub s') (liftSub s).
intros. apply Extensionality. intros var. dependent destruction var; first by []. 
unfold composeSub. simpl. rewrite <- (proj1 (applyComposeRenSub _)). unfold composeRenSub, subVal. by rewrite <- (proj1 (applyComposeRen _)). 
Qed.

Lemma applyComposeSub E : 
   (forall (v : Value E) E' E'' (s' : Sub E' E'') (s : Sub E E'),
    subVal (composeSub s' s) v = subVal s' (subVal s v))
/\ (forall (e : Exp   E) E' E'' (s' : Sub E' E'') (s : Sub E E'),
    subExp (composeSub s' s) e = subExp s' (subExp s e)).
Proof. move: E ; apply ExpValue_ind; intros; SimplMap; Rewrites liftComposeSub. Qed.

Lemma composeCons : forall E E' E'' (s':Sub E' E'') (s:Sub E E') (v:Value _), 
  composeSub (cons v s') (liftSub s) = cons v (composeSub s' s).
intros. apply Extensionality. intros var. dependent destruction var; first by [].
unfold composeSub. unfold subVal. simpl. rewrite <- (proj1 (applyComposeRen _)). unfold composeRen.
simpl. replace ((fun (var0:Fin E') => s' var0)) with s' by (by apply Extensionality). by [].
Qed.

Lemma composeSubIdLeft : forall E E' (s : Sub E E'), composeSub (@idSub _) s = s.
Proof. intros. apply Extensionality.  intros var. by apply (proj1 (Map.applyId _ _)). Qed.

Lemma composeSubIdRight : forall E E' (s:Sub E E'), composeSub s (@idSub _) = s.
Proof. intros. by apply Extensionality. Qed.

Notation "[ x , .. , y ]" := (cons x .. (cons y (@Map.id _ SubOps _)) ..) : Sub_scope. 
Arguments Scope composeSub [_ _ _ Sub_scope Sub_scope]. 
Arguments Scope subExp [_ _ Sub_scope]. 
Arguments Scope subVal [_ _ Sub_scope].
Delimit Scope Sub_scope with sub.

Lemma composeSingleSub : forall E E' (s:Sub E E') (v:Value _), composeSub [v] (liftSub s) = cons v s.
Proof. intros. rewrite composeCons. by rewrite composeSubIdLeft. Qed.

End Tm.
