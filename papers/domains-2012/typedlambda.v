(**********************************************************************************
 * typedlambda.v                                                                  *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                       *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)


(*==========================================================================
  Call-by-value simply-typed lambda-calculus with recursion, pairs, and arithmetic
  ==========================================================================*)

Require Import Program.Equality.
Require Export ssreflect ssrnat seq eqtype.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Set Printing Implicit Defensive.

(*==========================================================================
  Types and contexts
  ==========================================================================*)

(*=Ty *)
Inductive Ty := Int | Bool | Arrow (ty1 t2 : Ty) | Prod (ty1 t2 : Ty).
Infix " --> " := Arrow (at level 55, right associativity).
Infix " ** " := Prod (at level 55).
Definition Env := seq Ty.
(*=End *)
(* begin hide *)
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..) : list_scope. 
(* end hide *)

(*==========================================================================
  Typed terms in context
  ==========================================================================*)
(*=VarValueExp *)
Inductive Var : Env -> Ty -> Type := 
| ZVAR : forall E t, Var (t :: E) t
| SVAR : forall E t t', Var E t -> Var (t' :: E) t.
Inductive Value E : Ty -> Type :=
| TINT : nat -> Value E Int
| TBOOL : bool -> Value E Bool
| TVAR :> forall t, Var E t -> Value E t
| TFIX : forall t1 t2, Exp (t1 :: t1 --> t2 :: E) t2 -> Value E (t1 --> t2)  
| TPAIR : forall t1 t2, Value E t1 -> Value E t2 -> Value E (t1 ** t2)
with Exp E : Ty -> Type :=
| TFST : forall t1 t2, Value E (t1 ** t2) -> Exp E t1
| TSND : forall t1 t2, Value E (t1 ** t2) -> Exp E t2
| TOP : (nat -> nat -> nat) -> Value E Int -> Value E Int -> Exp E Int
| TGT : Value E Int -> Value E Int -> Exp E Bool
| TVAL : forall t, Value E t -> Exp E t
| TLET : forall t1 t2, Exp E t1 -> Exp (t1 :: E) t2 -> Exp E t2 
| TAPP : forall t1 t2, Value E (t1 --> t2) -> Value E t1 -> Exp E t2
| TIF : forall t, Value E Bool -> Exp E t -> Exp E t -> Exp E t.
Definition CExp t := Exp nil t.
Definition CValue t := Value nil t.
(*=End *)
Implicit Arguments TBOOL [E].
Implicit Arguments TINT [E].

(* begin hide *)
Scheme Val_rec2 := Induction for Value Sort Set
  with Exp_rec2 := Induction for Exp Sort Set.

Scheme Val_type2 := Induction for Value Sort Type
  with Exp_type2 := Induction for Exp Sort Type.

Scheme Val_ind2 := Induction for Value Sort Prop
  with Exp_ind2 := Induction for Exp Sort Prop.

Combined Scheme ExpVal_ind from Val_ind2, Exp_ind2.
(* end hide *)

(*==========================================================================
  Variable-domain maps. 
  By instantiating P with Var we get renamings.
  By instantiating P with Val we get substitutions.
  ==========================================================================*)

Definition Map (P:Env -> Ty -> Type) E E' := forall t, Var E t -> P E' t.

(* Head, tail and cons *)
Definition tlMap P E E' t (m:Map P (t::E) E') : Map P E E' := fun t' v => m t' (SVAR t v).
Definition hdMap P E E' t (m:Map P (t::E) E') : P E' t := m t (ZVAR _ _).
Implicit Arguments tlMap [P E E' t].
Implicit Arguments hdMap [P E E' t].


Definition cast P (E E' : Env) (t : Ty) (x:P E t) (p:E=E') : P E' t.
intros.
subst. exact x.
Defined.

Program Definition consMap P E E' t (v:P E' t) (m:Map P E E') : Map P (t::E) E' :=
    fun t' (var:Var (t::E) t') => 
    match var with
    | ZVAR _ _ => v
    | SVAR _ _ _ var => m _ var
    end.

Implicit Arguments consMap [P E E' t].

Axiom MapExtensional : forall P E E' (r1 r2 : Map P E E'), (forall t var, r1 t var = r2 t var) -> r1 = r2.

Lemma hdConsMap : forall P env env' ty (v : P env' ty) (s : Map P env env'), hdMap (consMap v s) = v. Proof. auto. Qed.
Lemma tlConsMap : forall P env env' ty (v : P env' ty) (s : Map P env env'), tlMap (consMap v s) = s. Proof. intros. apply MapExtensional. auto. Qed.

Lemma consMapInv : forall P env env' ty (m:Map P (ty :: env) env'), exists m', exists v, m = consMap v m'.  
intros. exists (tlMap m). exists (hdMap m).
apply MapExtensional. dependent destruction var; auto. 
Qed.

(*==========================================================================
  Package of operations used with a Map
    vr maps a Var into Var or Value (so is either the identity or TVAR)
    vl maps a Var or Value to a Value (so is either TVAR or the identity)
    wk weakens a Var or Value (so is either SVAR or renaming through SVAR on a value)
  ==========================================================================*)
Record MapOps (P : Env -> Ty -> Type) :=
{
  vr : forall E ty, Var E ty -> P E ty;   
  vl : forall E ty, P E ty -> Value E ty;
  wk : forall E ty ty', P E ty -> P (ty' :: E) ty
}.

Section MapOps.

  Variable P : Env -> Ty -> Type.
  Variable ops : MapOps P.

  Program Definition lift env env' ty (m : Map P env env') : Map P (ty :: env) (ty :: env') :=
  fun ty' => fun var => match var with
  | ZVAR _ _ => vr ops (ZVAR _ _)
  | SVAR _ _ _ x => wk ops _ (m _ x)
  end.
  Implicit Arguments lift [env env'].

  Definition shiftMap env env' ty (m : Map P env env') : Map P env (ty :: env') := fun ty' => fun var => wk ops _ (m ty' var).
  Implicit Arguments shiftMap [env env'].

  Lemma shiftConsMap : forall env env' ty (m : Map P env env') (x : P env' ty) ty', shiftMap ty' (consMap x m) = consMap (wk ops _ x) (shiftMap ty' m). 
  Proof.
  intros env env' ty m x ty'. apply MapExtensional.
  intros ty0 var0. dependent destruction var0; auto.
  Qed.

  Fixpoint travVal env env' ty (v : Value env ty) : Map P env env' -> Value env' ty :=
  match v with
    | TINT i => fun m => TINT i
    | TBOOL b => fun m => TBOOL b
    | TVAR _ v => fun m => vl ops (m _ v)
    | TFIX _ _ e => fun m => TFIX (travExp e (lift _ (lift _ m)))
    | TPAIR _ _ e1 e2 => fun m => TPAIR (travVal e1 m) (travVal e2 m)
  end
  with travExp env env' ty (e : Exp env ty) : Map P env env' -> Exp env' ty :=
   match e with
    | TOP op e1 e2 => fun m => TOP op (travVal e1 m) (travVal e2 m)
    | TGT e1 e2 => fun m => TGT (travVal e1 m) (travVal e2 m)
    | TFST _ _ e => fun m => TFST (travVal e m)
    | TSND _ _ e => fun m => TSND (travVal e m)
    | TVAL _ v => fun m => TVAL (travVal v  m)
    | TIF _ v e1 e2 => fun m => TIF (travVal v m) (travExp e1 m) (travExp e2 m)
    | TAPP _ _ e1 e2 => fun m => TAPP (travVal e1 m) (travVal e2 m)
    | TLET _ _ e1 e2 => fun m => TLET (travExp e1 m) (travExp e2 (lift _ m))
  end.

  Definition mapVal env env' ty m v := @travVal env env' ty v m.
  Definition mapExp env env' ty m e := @travExp env env' ty e m.

  Variable env env' : Env.
  Variable m : Map P env env'.
  Variable t1 t2 : Ty.

  Lemma mapTVAR : forall (var : Var _ t1), mapVal m (TVAR var) = vl ops (m var). auto. Qed. 
  Lemma mapTINT : forall n, mapVal m (TINT n) = TINT n. auto. Qed.
  Lemma mapTBOOL : forall n, mapVal m (TBOOL n) = TBOOL n. auto. Qed.
  Lemma mapTPAIR : forall (v1 : Value _ t1) (v2 : Value _ t2), mapVal m (TPAIR v1 v2) = TPAIR (mapVal m v1) (mapVal m v2). auto. Qed.
  Lemma mapTFST : forall (v : Value _ (t1 ** t2)), mapExp m (TFST v) = TFST (mapVal m v). auto. Qed.
  Lemma mapTSND : forall (v : Value _ (t1 ** t2)), mapExp m (TSND v) = TSND (mapVal m v). auto. Qed.
  Lemma mapTFIX : forall (e : Exp (t1 :: t1-->t2 :: _) t2), mapVal m (TFIX e) = TFIX (mapExp (lift _ (lift _ m)) e). auto. Qed.
  Lemma mapTOP : forall op v1 v2, mapExp m (TOP op v1 v2) = TOP op (mapVal m v1) (mapVal m v2). auto. Qed.
  Lemma mapTGT : forall v1 v2, mapExp m (TGT v1 v2) = TGT (mapVal m v1) (mapVal m v2). auto. Qed.
  Lemma mapTVAL : forall (v : Value _ t1), mapExp m (TVAL v) = TVAL (mapVal m v). auto. Qed.
  Lemma mapTLET : forall (e1 : Exp _ t1) (e2 : Exp _ t2), mapExp m (TLET e1 e2) = TLET (mapExp m e1) (mapExp (lift _ m) e2). auto. Qed.
  Lemma mapTIF : forall v (e1 e2 : Exp _ t1), mapExp m (TIF v e1 e2) = TIF (mapVal m v) (mapExp m e1) (mapExp m e2). auto. Qed.
  Lemma mapTAPP : forall (v1 : Value _ (t1 --> t2)) v2, mapExp m (TAPP v1 v2) = TAPP (mapVal m v1) (mapVal m v2). auto. Qed.

End MapOps.

Hint Rewrite mapTVAR mapTINT mapTBOOL mapTPAIR mapTFST mapTSND mapTFIX mapTOP mapTGT mapTVAL mapTLET mapTIF mapTAPP : mapHints.

Implicit Arguments lift [P env env'].
Implicit Arguments shiftMap [P env env'].

(*==========================================================================
  Variable renamings: Map Var
  ==========================================================================*)

Definition Ren := Map Var. 
Definition RenMapOps := (Build_MapOps (fun _ _ v => v) TVAR SVAR).

Definition renameVal := mapVal RenMapOps.
Definition renameExp := mapExp RenMapOps.
Definition liftRen := lift RenMapOps. 
Implicit Arguments liftRen [env env'].
Definition shiftRen := shiftMap RenMapOps.
Implicit Arguments shiftRen [env env'].

Section RenDefs.

  Variable env env' : Env.
  Variable r : Ren env env'.
  Variable t1 t2 : Ty.

  Lemma renameTVAR : forall (var : Var env t1), renameVal r (TVAR var) = TVAR (r var). auto. Qed.
  Lemma renameTINT : forall n, renameVal r (TINT n) = TINT n. auto. Qed.
  Lemma renameTBOOL : forall n, renameVal r (TBOOL n) = TBOOL n. auto. Qed.
  Lemma renameTPAIR : forall (v1 : Value _ t1) (v2 : Value _ t2), renameVal r (TPAIR v1 v2) = TPAIR (renameVal r v1) (renameVal r v2). auto. Qed.
  Lemma renameTFST : forall (v : Value _ (t1 ** t2)), renameExp r (TFST v) = TFST (renameVal r v). auto. Qed.
  Lemma renameTSND : forall (v : Value _ (t1 ** t2)), renameExp r (TSND v) = TSND (renameVal r v). auto. Qed.
  Lemma renameTFIX : forall (e : Exp (t1 :: t1-->t2 :: _) t2), renameVal r (TFIX e) = TFIX (renameExp (liftRen _ (liftRen _ r)) e). auto. Qed.
  Lemma renameTOP : forall op v1 v2, renameExp r (TOP op v1 v2) = TOP op (renameVal r v1) (renameVal r v2). auto. Qed.
  Lemma renameTGT : forall v1 v2, renameExp r (TGT v1 v2) = TGT (renameVal r v1) (renameVal r v2). auto. Qed.
  Lemma renameTVAL : forall (v : Value env t1), renameExp r (TVAL v) = TVAL (renameVal r v). auto. Qed.
  Lemma renameTLET : forall (e1 : Exp _ t1) (e2 : Exp _ t2), renameExp r (TLET e1 e2) = TLET (renameExp r e1) (renameExp (liftRen _ r) e2). auto. Qed.
  Lemma renameTIF : forall v (e1 e2 : Exp _ t1), renameExp r (TIF v e1 e2) = TIF (renameVal r v) (renameExp r e1) (renameExp r e2). auto. Qed.
  Lemma renameTAPP : forall (v1 : Value _ (t1-->t2)) v2, renameExp r (TAPP v1 v2) = TAPP (renameVal r v1) (renameVal r v2). auto. Qed.

End RenDefs.

Hint Rewrite renameTVAR renameTINT renameTBOOL renameTPAIR renameTFST renameTSND renameTFIX renameTOP renameTGT renameTVAL renameTLET renameTIF renameTAPP : renameHints.

Lemma LiftRenDef : forall env env' (r : Ren env' env) ty, liftRen _ r = consMap (ZVAR _ ty) (shiftRen _ r).
intros. apply MapExtensional. auto.  Qed.

(*==========================================================================
  Identity renaming
  ==========================================================================*)

Definition idRen env : Ren env env := fun ty (var : Var env ty) => var.
Implicit Arguments idRen [].

Lemma liftIdRen : forall E t, liftRen _ (idRen E) = idRen (t::E).
intros. apply MapExtensional.  
dependent destruction var; auto. 
Qed.

Lemma applyIdRen env : 
   (forall ty (v : Value env ty), renameVal (idRen env) v = v)
/\ (forall ty (e : Exp env ty), renameExp (idRen env) e = e).
move: env. apply ExpVal_ind; 
(intros; try (autorewrite with renameHints using try rewrite liftIdRen; try rewrite liftIdRen; try rewrite H; try rewrite H0; try rewrite H1); auto).
Qed.

Lemma idRenDef : forall ty env, idRen (ty :: env) = consMap (ZVAR _ _) (shiftRen ty (idRen env)).
intros. apply MapExtensional. intros. dependent destruction var; auto. Qed.


(*==========================================================================
  Composition of renaming
  ==========================================================================*)

Definition composeRen P env env' env'' (m : Map P env' env'') (r : Ren env env') : Map P env env'' := fun t var => m _ (r _ var). 

Lemma liftComposeRen P ops E env' env'' t (m:Map P env' env'') (r:Ren E env') : lift ops t (composeRen m r) = composeRen (lift ops t m) (liftRen t r).
apply MapExtensional. intros t0 var.
dependent destruction var; auto. 
Qed.

Lemma applyComposeRen env : 
   (forall ty (v : Value env ty) P ops env' env'' (m:Map P env' env'') (s : Ren env env'),
    mapVal ops (composeRen m s) v = mapVal ops m (renameVal s v))
/\ (forall ty (e : Exp   env ty) P ops env' env'' (m:Map P env' env'') (s : Ren env env'),
    mapExp ops (composeRen m s) e = mapExp ops m (renameExp s e)).
move: env.
apply ExpVal_ind; intros; 
autorewrite with mapHints renameHints; try rewrite liftComposeRen; try rewrite liftComposeRen; try rewrite <- H;
try rewrite <- H0; try rewrite <- H1; auto.  
Qed.

Lemma composeRenAssoc : 
  forall P env env' env'' env''' (m : Map P env'' env''') r' (r : Ren env env'), 
  composeRen m (composeRen r' r) = composeRen (composeRen m r') r.
by []. Qed.

Lemma composeRenIdLeft : forall env env' (r : Ren env env'), composeRen (idRen _) r = r.
Proof. intros. apply MapExtensional. auto. Qed.

Lemma composeRenIdRight : forall P env env' (m:Map P env env'), composeRen m (idRen _) = m.
Proof. intros. apply MapExtensional. auto. Qed.

(*==========================================================================
  Substitution
  ==========================================================================*)

Definition Sub := Map Value.
Definition SubMapOps := Build_MapOps TVAR (fun _ _ v => v) (fun env ty ty' => renameVal (fun _ => SVAR ty')). 

(* Convert a renaming into a substitution *)
Definition renamingToSub env env' (r : Ren env env') : Sub env env' := fun ty => fun v => TVAR (r ty v).

Definition subVal := mapVal SubMapOps.
Definition subExp := mapExp SubMapOps.

Definition shiftSub := shiftMap SubMapOps.
Implicit Arguments shiftSub [env env'].

Definition liftSub := lift SubMapOps.
Implicit Arguments liftSub [env env']. 

Section SubDefs.

  Variable env env' : Env.
  Variable s : Sub env env'.
  Variable t1 t2 : Ty.

  Lemma substTVAR : forall (var : Var env t1), subVal s (TVAR var) = s var. auto. Qed.
  Lemma substTINT : forall n, subVal s (TINT n) = TINT n. auto. Qed.
  Lemma substTBOOL : forall n, subVal s (TBOOL n) = TBOOL n. auto. Qed.
  Lemma substTPAIR : forall (v1 : Value _ t1) (v2:Value _ t2), subVal s (TPAIR v1 v2) = TPAIR (subVal s v1) (subVal s v2). auto. Qed.
  Lemma substTFST : forall (v : Value _ (t1 ** t2)), subExp s (TFST v) = TFST (subVal s v). auto. Qed.
  Lemma substTSND : forall (v : Value _ (t1 ** t2)), subExp s (TSND v) = TSND (subVal s v). auto. Qed.
  Lemma substTFIX : forall (e : Exp (t1 :: t1-->t2 :: _) t2), subVal s (TFIX e) = TFIX (subExp (liftSub _ (liftSub _ s)) e). auto. Qed.
  Lemma substTOP : forall op v1 v2, subExp s (TOP op v1 v2) = TOP op (subVal s v1) (subVal s v2). auto. Qed.
  Lemma substTGT : forall v1 v2, subExp s (TGT v1 v2) = TGT (subVal s v1) (subVal s v2). auto. Qed.
  Lemma substTVAL : forall (v : Value _ t1), subExp s (TVAL v) = TVAL (subVal s v). auto. Qed.
  Lemma substTLET : forall (e1 : Exp _ t1) (e2 : Exp _ t2), subExp s (TLET e1 e2) = TLET (subExp s e1) (subExp (liftSub _ s) e2). auto. Qed.
  Lemma substTIF : forall v (e1 e2 : Exp _ t1), subExp s (TIF v e1 e2) = TIF (subVal s v) (subExp s e1) (subExp s e2). auto. Qed.
  Lemma substTAPP : forall (v1:Value _ (t1 --> t2)) v2, subExp s (TAPP v1 v2) = TAPP (subVal s v1) (subVal s v2). auto. Qed.

End SubDefs.

Hint Rewrite substTVAR substTPAIR substTINT substTBOOL substTFST substTSND substTFIX substTOP substTGT substTVAL substTLET substTIF substTAPP : substHints.


(*==========================================================================
  Identity substitution
  ==========================================================================*)

Definition idSub env : Sub env env := fun ty (x:Var env ty) => TVAR x.
Implicit Arguments idSub [].

Lemma liftIdSub : forall env ty, liftSub ty (idSub env) = idSub (ty :: env).
intros env ty. apply MapExtensional. unfold liftSub. intros.
dependent destruction var; auto. 
Qed.

Lemma applyIdSub env : 
   (forall ty (v : Value env ty), subVal (idSub env) v = v)
/\ (forall ty (e : Exp env ty), subExp (idSub env) e = e).
Proof.
move: env ; apply ExpVal_ind; intros; autorewrite with substHints; try rewrite liftIdSub; try rewrite liftIdSub; try rewrite H; try rewrite H0; try rewrite H1; auto.
Qed.

Notation "[ x , .. , y ]" := (consMap x .. (consMap y (idSub _)) ..) : Sub_scope. 
Delimit Scope Sub_scope with subst.
Arguments Scope subExp [_ _ Sub_scope]. 
Arguments Scope subVal [_ _ Sub_scope]. 

Lemma LiftSubDef : forall env env' ty (s : Sub env' env), liftSub ty s = consMap (TVAR (ZVAR _ _)) (shiftSub ty s).
intros. apply MapExtensional. intros. dependent destruction var; auto. Qed.

(*==========================================================================
  Composition of substitution followed by renaming
  ==========================================================================*)

Definition composeRenSub env env' env'' (r : Ren env' env'') (s : Sub env env') : Sub env env'' := fun t var => renameVal r (s _ var). 

Lemma liftComposeRenSub : forall E env' env'' t (r:Ren env' env'') (s:Sub E env'), liftSub t (composeRenSub r s) = composeRenSub (liftRen t r) (liftSub t s).
intros. apply MapExtensional. intros t0 var. dependent induction var; auto. 
simpl. unfold composeRenSub. unfold liftSub. simpl. unfold renameVal at 1.
rewrite <- (proj1 (applyComposeRen _)). unfold renameVal. rewrite <- (proj1 (applyComposeRen _)). 
auto. 
Qed.

Lemma applyComposeRenSub E :
   (forall t (v:Value E t) env' env'' (r:Ren env' env'') (s : Sub E env'),
    subVal (composeRenSub r s) v = renameVal r (subVal s v))
/\ (forall t (e:Exp   E t) env' env'' (r:Ren env' env'') (s : Sub E env'),
    subExp (composeRenSub r s) e = renameExp r (subExp s e)).
Proof.
move: E ; apply ExpVal_ind;
(intros; try (autorewrite with substHints renameHints using try rewrite liftComposeRenSub; try rewrite liftComposeRenSub; try rewrite H; try rewrite H0; try rewrite H1); auto).
Qed.

(*==========================================================================
  Composition of substitutions
  ==========================================================================*)

Definition composeSub env env' env'' (s' : Sub env' env'') (s : Sub env env') : Sub env env'' := fun ty var => subVal s' (s _ var). 

Arguments Scope composeSub [_ _ _ Sub_scope Sub_scope]. 

Lemma liftComposeSub : forall env env' env'' ty (s' : Sub env' env'') (s : Sub env env'), liftSub ty (composeSub s' s) = composeSub (liftSub ty s') (liftSub ty s).
intros. apply MapExtensional. intros t0 var. dependent destruction var. auto.
unfold composeSub. simpl. 
rewrite <- (proj1 (applyComposeRenSub _)). unfold composeRenSub. unfold subVal. 
rewrite <- (proj1 (applyComposeRen _)). auto.
Qed.

Lemma substComposeSub env : 
   (forall ty (v : Value env ty) env' env'' (s' : Sub env' env'') (s : Sub env env'),
    subVal (composeSub s' s) v = subVal s' (subVal s v))
/\ (forall ty (e : Exp   env ty) env' env'' (s' : Sub env' env'') (s : Sub env env'),
    subExp (composeSub s' s) e = subExp s' (subExp s e)).
Proof.
move: env ; apply ExpVal_ind;
(intros; try (autorewrite with substHints using try rewrite liftComposeSub; try rewrite liftComposeSub; try rewrite H; try rewrite H0; try rewrite H1); auto).
Qed.

Lemma composeCons : forall env env' env'' ty (s':Sub env' env'') (s:Sub env env') (v:Value _ ty), 
  composeSub (consMap v s') (liftSub ty s) = consMap v (composeSub s' s).
intros. apply MapExtensional. intros t0 var.  dependent destruction var. auto. 
unfold composeSub. simpl. unfold subVal. rewrite <- (proj1 (applyComposeRen _)). unfold composeRen. simpl.
assert ((fun (t0:Ty) (var0:Var env' t0) => s' t0 var0) = s') by (apply MapExtensional; auto). 
rewrite H. auto. 
Qed.

Lemma composeSubIdLeft : forall env env' (s : Sub env env'), composeSub (idSub _) s = s.
Proof. intros. apply MapExtensional. intros. unfold composeSub. apply (proj1 (applyIdSub _)). Qed.

Lemma composeSubIdRight : forall env env' (s:Sub env env'), composeSub s (idSub _) = s.
Proof. intros. apply MapExtensional. auto.  
Qed.

(*==========================================================================
  Constructors are injective 
  ==========================================================================*)

Lemma TPAIR_injective : 
  forall env t1 t2 (v1 : Value env t1) (v2 : Value env t2) v3 v4, 
  TPAIR v1 v2 = TPAIR v3 v4 -> 
  v1 = v3 /\ v2 = v4.
intros. dependent destruction H. auto. 
Qed.

Lemma TFST_injective : 
  forall env t1 t2 (v1 : Value env (t1 ** t2)) v2, 
  TFST v1 = TFST v2 -> 
  v1 = v2.
intros. dependent destruction H. auto. 
Qed.

Lemma TSND_injective : 
  forall env t1 t2 (v1 : Value env (t1 ** t2)) v2, 
  TSND v1 = TSND v2 -> 
  v1 = v2.
intros. dependent destruction H. auto. 
Qed.

Lemma TVAL_injective : 
  forall env ty (v1 : Value env ty) v2, 
  TVAL v1 = TVAL v2 -> 
  v1 = v2.
intros. dependent destruction H. auto. 
Qed.

Lemma TFIX_injective : 
  forall env t1 t2 (e1 : Exp (t1 :: _ :: env) t2) e2,
  TFIX e1 = TFIX e2 -> 
  e1 = e2.
intros. dependent destruction H. auto. 
Qed.

(*==========================================================================
  Closed forms
  ==========================================================================*)
Lemma ClosedFunction : forall t1 t2 (v : CValue (t1 --> t2)), exists b, v = TFIX b.
unfold CValue.
intros t1 t2 v.
dependent destruction v.
(* TVAR case: impossible *)
dependent destruction v.
(* TFIX case *)
exists e. trivial.
Qed.

Lemma ClosedPair : forall t1 t2 (v : CValue (t1 ** t2)), exists v1, exists v2, v = TPAIR v1 v2.
unfold CValue.
intros t1 t2 v.
dependent destruction v.
(* TVAR case: impossible *)
dependent destruction v.
(* TPAIR case *)
exists v1. exists v2. trivial.
Qed.

Lemma ClosedInt : forall (v : CValue Int), exists i, v = TINT i. 
unfold CValue.
intros v. dependent destruction v.
exists n. trivial.
dependent destruction v.
Qed.

Lemma ClosedBool : forall (v : CValue Bool), exists b, v = TBOOL b. 
unfold CValue.
intros v. dependent destruction v.
exists b. trivial.
dependent destruction v.
Qed.

Unset Implicit Arguments.
