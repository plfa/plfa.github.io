(*==========================================================================
  Call-by-value simply-typed lambda-calculus with recursion, pairs, and arithmetic
  ==========================================================================*)

Require Import utility.
Require Import List.
Require Import Program.Equality.
Set Implicit Arguments.
Unset Strict Implicit.
Set Printing Implicit Defensive.

(*====== coqdoc printing directives ========================================*)
(** printing --> %\ensuremath{\mathrel{\texttt{->}}}% *)
(** printing ** %\ensuremath{\mathrel{\texttt{*}}}% *)
(** printing Int %{\textsf{Int}}% *)
(** printing Bool %{\textsf{Bool}}% *)
(** printing Arrow %{\textsf{Arrow}}% *)
(** printing Prod %{\textsf{Prod}}% *)
(** printing Ty %{\textsf{Ty}}% *)
(** printing Env %{\textsf{Env}}% *)

(** printing env %{\ensuremath{\Gamma}}% *)
(** printing env' %{\ensuremath{\Gamma'}}% *)
(** printing ty %{\ensuremath{\tau}}% *)
(** printing ty1 %\ensuremath{\tau_1}% *)
(** printing ty2 %\ensuremath{\tau_2}% *)
(** printing ty' %\ensuremath{\tau'}% *)

(*==========================================================================
  Types and contexts
  ==========================================================================*)

Inductive Ty := Int | Bool | Arrow (ty1 ty2 : Ty) | Prod (ty1 ty2 : Ty).

Infix " --> " := Arrow. (* (at level 55). *)
Infix " ** " := Prod (at level 55).

Definition Env := list Ty.

(* begin hide *)
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..) : list_scope. 
(* end hide *)

(*==========================================================================
  Typed terms in context
  ==========================================================================*)

Inductive Var : Env -> Ty -> Type := 
| ZVAR : forall env ty, Var (ty :: env) ty
| SVAR : forall env ty ty', Var env ty -> Var (ty' :: env) ty.

Inductive Value : Env -> Ty -> Type :=
| TINT : forall env, nat -> Value env Int
| TBOOL : forall env, bool -> Value env Bool
| TVAR :> forall env ty, Var env ty -> Value env ty
| TFIX : forall env ty1 ty2, Exp (ty1 :: ty1 --> ty2 :: env) ty2 -> Value env (ty1 --> ty2)  
| TPAIR : forall env ty1 ty2, Value env ty1 -> Value env ty2 -> Value env (ty1 ** ty2)
with Exp : Env -> Ty -> Type :=
| TFST : forall env ty1 ty2, Value env (ty1 ** ty2) -> Exp env ty1
| TSND : forall env ty1 ty2, Value env (ty1 ** ty2) -> Exp env ty2
| TOP : forall env, (nat -> nat -> nat) -> Value env Int -> Value env Int -> Exp env Int
| TGT : forall env, Value env Int -> Value env Int -> Exp env Bool
| TVAL : forall env ty, Value env ty -> Exp env ty
| TLET : forall env ty1 ty2, Exp env ty1 -> Exp (ty1 :: env) ty2 -> Exp env ty2 
| TAPP : forall env ty1 ty2, Value env (ty1 --> ty2) -> Value env ty1 -> Exp env ty2
| TIF : forall env ty, Value env Bool -> Exp env ty -> Exp env ty -> Exp env ty.

Implicit Arguments TBOOL [env].
Implicit Arguments TINT [env].

(* begin hide *)
Scheme Val_rec2 := Induction for Value Sort Set
  with Exp_rec2 := Induction for Exp Sort Set.

Scheme Val_type2 := Induction for Value Sort Type
  with Exp_type2 := Induction for Exp Sort Type.

Scheme Val_ind2 := Induction for Value Sort Prop
  with Exp_ind2 := Induction for Exp Sort Prop.

Combined Scheme ExpVal_ind from Val_ind2, Exp_ind2.
(* end hide *)

(* Closed expressions and values *)
Definition CExp ty := Exp nil ty.
Definition CValue ty := Value nil ty.

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
  vr : forall env ty, Var env ty -> P env ty;   
  vl : forall env ty, P env ty -> Value env ty;
  wk : forall env ty ty', P env ty -> P (ty' :: env) ty
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
    | TINT _ i => fun m => TINT i
    | TBOOL _ b => fun m => TBOOL b
    | TVAR _ _ v => fun m => vl ops (m _ v)
    | TFIX _ _ _ e => fun m => TFIX (travExp e (lift _ (lift _ m)))
    | TPAIR _ _ _ e1 e2 => fun m => TPAIR (travVal e1 m) (travVal e2 m)
  end
  with travExp env env' ty (e : Exp env ty) : Map P env env' -> Exp env' ty :=
   match e with
    | TOP _ op e1 e2 => fun m => TOP op (travVal e1 m) (travVal e2 m)
    | TGT _ e1 e2 => fun m => TGT (travVal e1 m) (travVal e2 m)
    | TFST _ _ _ e => fun m => TFST (travVal e m)
    | TSND _ _ _ e => fun m => TSND (travVal e m)
    | TVAL _ _ v => fun m => TVAL (travVal v  m)
    | TIF _ _ v e1 e2 => fun m => TIF (travVal v m) (travExp e1 m) (travExp e2 m)
    | TAPP _ _ _ e1 e2 => fun m => TAPP (travVal e1 m) (travVal e2 m)
    | TLET _ _ _ e1 e2 => fun m => TLET (travExp e1 m) (travExp e2 (lift _ m))
  end.

  Definition mapVal env env' ty m v := @travVal env env' ty v m.
  Definition mapExp env env' ty m e := @travExp env env' ty e m.

  Variable env env' : Env.
  Variable m : Map P env env'.
  Variable ty1 ty2 : Ty.

  Lemma mapTVAR : forall (var : Var _ ty1), mapVal m (TVAR var) = vl ops (m var). auto. Qed. 
  Lemma mapTINT : forall n, mapVal m (TINT n) = TINT n. auto. Qed.
  Lemma mapTBOOL : forall n, mapVal m (TBOOL n) = TBOOL n. auto. Qed.
  Lemma mapTPAIR : forall (v1 : Value _ ty1) (v2 : Value _ ty2), mapVal m (TPAIR v1 v2) = TPAIR (mapVal m v1) (mapVal m v2). auto. Qed.
  Lemma mapTFST : forall (v : Value _ (ty1 ** ty2)), mapExp m (TFST v) = TFST (mapVal m v). auto. Qed.
  Lemma mapTSND : forall (v : Value _ (ty1 ** ty2)), mapExp m (TSND v) = TSND (mapVal m v). auto. Qed.
  Lemma mapTFIX : forall (e : Exp (ty1 :: ty1-->ty2 :: _) ty2), mapVal m (TFIX e) = TFIX (mapExp (lift _ (lift _ m)) e). auto. Qed.
  Lemma mapTOP : forall op v1 v2, mapExp m (TOP op v1 v2) = TOP op (mapVal m v1) (mapVal m v2). auto. Qed.
  Lemma mapTGT : forall v1 v2, mapExp m (TGT v1 v2) = TGT (mapVal m v1) (mapVal m v2). auto. Qed.
  Lemma mapTVAL : forall (v : Value _ ty1), mapExp m (TVAL v) = TVAL (mapVal m v). auto. Qed.
  Lemma mapTLET : forall (e1 : Exp _ ty1) (e2 : Exp _ ty2), mapExp m (TLET e1 e2) = TLET (mapExp m e1) (mapExp (lift _ m) e2). auto. Qed.
  Lemma mapTIF : forall v (e1 e2 : Exp _ ty1), mapExp m (TIF v e1 e2) = TIF (mapVal m v) (mapExp m e1) (mapExp m e2). auto. Qed.
  Lemma mapTAPP : forall (v1 : Value _ (ty1 --> ty2)) v2, mapExp m (TAPP v1 v2) = TAPP (mapVal m v1) (mapVal m v2). auto. Qed.

End MapOps.

Hint Rewrite mapTVAR mapTINT mapTBOOL mapTPAIR mapTFST mapTSND mapTFIX mapTOP mapTGT mapTVAL mapTLET mapTIF mapTAPP : mapHints.

Implicit Arguments lift [P env env'].
Implicit Arguments shiftMap [P env env'].

(*==========================================================================
  Variable renamings: Map Var
  ==========================================================================*)

Definition Renaming := Map Var. 
Definition RenamingMapOps := (Build_MapOps (fun _ _ v => v) TVAR SVAR).

Definition renameVal := mapVal RenamingMapOps.
Definition renameExp := mapExp RenamingMapOps.
Definition liftRenaming := lift RenamingMapOps. 
Implicit Arguments liftRenaming [env env'].
Definition shiftRenaming := shiftMap RenamingMapOps.
Implicit Arguments shiftRenaming [env env'].

Section RenamingDefs.

  Variable env env' : Env.
  Variable r : Renaming env env'.
  Variable ty1 ty2 : Ty.

  Lemma renameTVAR : forall (var : Var env ty1), renameVal r (TVAR var) = TVAR (r var). auto. Qed.
  Lemma renameTINT : forall n, renameVal r (TINT n) = TINT n. auto. Qed.
  Lemma renameTBOOL : forall n, renameVal r (TBOOL n) = TBOOL n. auto. Qed.
  Lemma renameTPAIR : forall (v1 : Value _ ty1) (v2 : Value _ ty2), renameVal r (TPAIR v1 v2) = TPAIR (renameVal r v1) (renameVal r v2). auto. Qed.
  Lemma renameTFST : forall (v : Value _ (ty1 ** ty2)), renameExp r (TFST v) = TFST (renameVal r v). auto. Qed.
  Lemma renameTSND : forall (v : Value _ (ty1 ** ty2)), renameExp r (TSND v) = TSND (renameVal r v). auto. Qed.
  Lemma renameTFIX : forall (e : Exp (ty1 :: ty1-->ty2 :: _) ty2), renameVal r (TFIX e) = TFIX (renameExp (liftRenaming _ (liftRenaming _ r)) e). auto. Qed.
  Lemma renameTOP : forall op v1 v2, renameExp r (TOP op v1 v2) = TOP op (renameVal r v1) (renameVal r v2). auto. Qed.
  Lemma renameTGT : forall v1 v2, renameExp r (TGT v1 v2) = TGT (renameVal r v1) (renameVal r v2). auto. Qed.
  Lemma renameTVAL : forall (v : Value env ty1), renameExp r (TVAL v) = TVAL (renameVal r v). auto. Qed.
  Lemma renameTLET : forall (e1 : Exp _ ty1) (e2 : Exp _ ty2), renameExp r (TLET e1 e2) = TLET (renameExp r e1) (renameExp (liftRenaming _ r) e2). auto. Qed.
  Lemma renameTIF : forall v (e1 e2 : Exp _ ty1), renameExp r (TIF v e1 e2) = TIF (renameVal r v) (renameExp r e1) (renameExp r e2). auto. Qed.
  Lemma renameTAPP : forall (v1 : Value _ (ty1-->ty2)) v2, renameExp r (TAPP v1 v2) = TAPP (renameVal r v1) (renameVal r v2). auto. Qed.

End RenamingDefs.

Hint Rewrite renameTVAR renameTINT renameTBOOL renameTPAIR renameTFST renameTSND renameTFIX renameTOP renameTGT renameTVAL renameTLET renameTIF renameTAPP : renameHints.

Lemma LiftRenamingDef : forall env env' (r : Renaming env' env) ty, liftRenaming _ r = consMap (ZVAR _ ty) (shiftRenaming _ r).
intros. apply MapExtensional. auto.  Qed.

(*==========================================================================
  Identity renaming
  ==========================================================================*)

Definition idRenaming env : Renaming env env := fun ty (var : Var env ty) => var.
Implicit Arguments idRenaming [].

Lemma liftIdRenaming : forall E t, liftRenaming _ (idRenaming E) = idRenaming (t::E).
intros. apply MapExtensional.  
dependent destruction var; auto. 
Qed.

Lemma applyIdRenaming : 
   (forall env ty (v : Value env ty), renameVal (idRenaming env) v = v)
/\ (forall env ty (e : Exp env ty), renameExp (idRenaming env) e = e).
Proof.
apply ExpVal_ind; 
(intros; try (autorewrite with renameHints using try rewrite liftIdRenaming; try rewrite liftIdRenaming; try rewrite H; try rewrite H0; try rewrite H1); auto).
Qed.

Lemma idRenamingDef : forall ty env, idRenaming (ty :: env) = consMap (ZVAR _ _) (shiftRenaming ty (idRenaming env)).
intros. apply MapExtensional. intros. dependent destruction var; auto. Qed.


(*==========================================================================
  Composition of renaming
  ==========================================================================*)

Definition composeRenaming P env env' env'' (m : Map P env' env'') (r : Renaming env env') : Map P env env'' := fun t var => m _ (r _ var). 

Lemma liftComposeRenaming : forall P ops E env' env'' t (m:Map P env' env'') (r:Renaming E env'), lift ops t (composeRenaming m r) = composeRenaming (lift ops t m) (liftRenaming t r).
intros. apply MapExtensional. intros t0 var.
dependent destruction var; auto. 
Qed.

Lemma applyComposeRenaming : 
   (forall env ty (v : Value env ty) P ops env' env'' (m:Map P env' env'') (s : Renaming env env'),
    mapVal ops (composeRenaming m s) v = mapVal ops m (renameVal s v))
/\ (forall env ty (e : Exp   env ty) P ops env' env'' (m:Map P env' env'') (s : Renaming env env'),
    mapExp ops (composeRenaming m s) e = mapExp ops m (renameExp s e)).
Proof.
apply ExpVal_ind; intros; 
autorewrite with mapHints renameHints; try rewrite liftComposeRenaming; try rewrite liftComposeRenaming; try rewrite <- H;
try rewrite <- H0; try rewrite <- H1; auto.  
Qed.

Lemma composeRenamingAssoc : 
  forall P env env' env'' env''' (m : Map P env'' env''') r' (r : Renaming env env'), 
  composeRenaming m (composeRenaming r' r) = composeRenaming (composeRenaming m r') r.
Proof. auto. Qed.

Lemma composeRenamingIdLeft : forall env env' (r : Renaming env env'), composeRenaming (idRenaming _) r = r.
Proof. intros. apply MapExtensional. auto. Qed.

Lemma composeRenamingIdRight : forall P env env' (m:Map P env env'), composeRenaming m (idRenaming _) = m.
Proof. intros. apply MapExtensional. auto. Qed.

(*==========================================================================
  Substitution
  ==========================================================================*)

Definition Subst := Map Value.
Definition SubstMapOps := Build_MapOps TVAR (fun _ _ v => v) (fun env ty ty' => renameVal (fun _ => SVAR ty')). 

(* Convert a renaming into a substitution *)
Definition renamingToSubst env env' (r : Renaming env env') : Subst env env' := fun ty => fun v => TVAR (r ty v).

Definition substVal := mapVal SubstMapOps.
Definition substExp := mapExp SubstMapOps.

Definition shiftSubst := shiftMap SubstMapOps.
Implicit Arguments shiftSubst [env env'].

Definition liftSubst := lift SubstMapOps.
Implicit Arguments liftSubst [env env']. 

Section SubstDefs.

  Variable env env' : Env.
  Variable s : Subst env env'.
  Variable ty1 ty2 : Ty.

  Lemma substTVAR : forall (var : Var env ty1), substVal s (TVAR var) = s var. auto. Qed.
  Lemma substTINT : forall n, substVal s (TINT n) = TINT n. auto. Qed.
  Lemma substTBOOL : forall n, substVal s (TBOOL n) = TBOOL n. auto. Qed.
  Lemma substTPAIR : forall (v1 : Value _ ty1) (v2:Value _ ty2), substVal s (TPAIR v1 v2) = TPAIR (substVal s v1) (substVal s v2). auto. Qed.
  Lemma substTFST : forall (v : Value _ (ty1 ** ty2)), substExp s (TFST v) = TFST (substVal s v). auto. Qed.
  Lemma substTSND : forall (v : Value _ (ty1 ** ty2)), substExp s (TSND v) = TSND (substVal s v). auto. Qed.
  Lemma substTFIX : forall (e : Exp (ty1 :: ty1-->ty2 :: _) ty2), substVal s (TFIX e) = TFIX (substExp (liftSubst _ (liftSubst _ s)) e). auto. Qed.
  Lemma substTOP : forall op v1 v2, substExp s (TOP op v1 v2) = TOP op (substVal s v1) (substVal s v2). auto. Qed.
  Lemma substTGT : forall v1 v2, substExp s (TGT v1 v2) = TGT (substVal s v1) (substVal s v2). auto. Qed.
  Lemma substTVAL : forall (v : Value _ ty1), substExp s (TVAL v) = TVAL (substVal s v). auto. Qed.
  Lemma substTLET : forall (e1 : Exp _ ty1) (e2 : Exp _ ty2), substExp s (TLET e1 e2) = TLET (substExp s e1) (substExp (liftSubst _ s) e2). auto. Qed.
  Lemma substTIF : forall v (e1 e2 : Exp _ ty1), substExp s (TIF v e1 e2) = TIF (substVal s v) (substExp s e1) (substExp s e2). auto. Qed.
  Lemma substTAPP : forall (v1:Value _ (ty1 --> ty2)) v2, substExp s (TAPP v1 v2) = TAPP (substVal s v1) (substVal s v2). auto. Qed.

End SubstDefs.

Hint Rewrite substTVAR substTPAIR substTINT substTBOOL substTFST substTSND substTFIX substTOP substTGT substTVAL substTLET substTIF substTAPP : substHints.


(*==========================================================================
  Identity substitution
  ==========================================================================*)

Definition idSubst env : Subst env env := fun ty (x:Var env ty) => TVAR x.
Implicit Arguments idSubst [].

Lemma liftIdSubst : forall env ty, liftSubst ty (idSubst env) = idSubst (ty :: env).
intros env ty. apply MapExtensional. unfold liftSubst. intros.
dependent destruction var; auto. 
Qed.

Lemma applyIdSubst : 
   (forall env ty (v : Value env ty), substVal (idSubst env) v = v)
/\ (forall env ty (e : Exp env ty), substExp (idSubst env) e = e).
Proof.
apply ExpVal_ind; intros; autorewrite with substHints; try rewrite liftIdSubst; try rewrite liftIdSubst; try rewrite H; try rewrite H0; try rewrite H1; auto.
Qed.

Notation "[ x , .. , y ]" := (consMap x .. (consMap y (idSubst _)) ..) : Subst_scope. 
Delimit Scope Subst_scope with subst.
Arguments Scope substExp [_ _ Subst_scope]. 
Arguments Scope substVal [_ _ Subst_scope]. 

Lemma LiftSubstDef : forall env env' ty (s : Subst env' env), liftSubst ty s = consMap (TVAR (ZVAR _ _)) (shiftSubst ty s).
intros. apply MapExtensional. intros. dependent destruction var; auto. Qed.

(*==========================================================================
  Composition of substitution followed by renaming
  ==========================================================================*)

Definition composeRenamingSubst env env' env'' (r : Renaming env' env'') (s : Subst env env') : Subst env env'' := fun t var => renameVal r (s _ var). 

Lemma liftComposeRenamingSubst : forall E env' env'' t (r:Renaming env' env'') (s:Subst E env'), liftSubst t (composeRenamingSubst r s) = composeRenamingSubst (liftRenaming t r) (liftSubst t s).
intros. apply MapExtensional. intros t0 var. dependent induction var; auto. 
simpl. unfold composeRenamingSubst. unfold liftSubst. simpl. unfold renameVal at 1. rewrite <- (proj1 applyComposeRenaming). unfold renameVal. rewrite <- (proj1 applyComposeRenaming). 
auto. 
Qed.

Lemma applyComposeRenamingSubst :
   (forall E t (v:Value E t) env' env'' (r:Renaming env' env'') (s : Subst E env'),
    substVal (composeRenamingSubst r s) v = renameVal r (substVal s v))
/\ (forall E t (e:Exp   E t) env' env'' (r:Renaming env' env'') (s : Subst E env'),
    substExp (composeRenamingSubst r s) e = renameExp r (substExp s e)).
Proof.
apply ExpVal_ind;
(intros; try (autorewrite with substHints renameHints using try rewrite liftComposeRenamingSubst; try rewrite liftComposeRenamingSubst; try rewrite H; try rewrite H0; try rewrite H1); auto).
Qed.

(*==========================================================================
  Composition of substitutions
  ==========================================================================*)

Definition composeSubst env env' env'' (s' : Subst env' env'') (s : Subst env env') : Subst env env'' := fun ty var => substVal s' (s _ var). 

Arguments Scope composeSubst [_ _ _ Subst_scope Subst_scope]. 

Lemma liftComposeSubst : forall env env' env'' ty (s' : Subst env' env'') (s : Subst env env'), liftSubst ty (composeSubst s' s) = composeSubst (liftSubst ty s') (liftSubst ty s).
intros. apply MapExtensional. intros t0 var. dependent destruction var. auto.
unfold composeSubst. simpl. 
rewrite <- (proj1 applyComposeRenamingSubst). unfold composeRenamingSubst. unfold substVal. 
rewrite <- (proj1 applyComposeRenaming). auto.
Qed.

Lemma substComposeSubst : 
   (forall env ty (v : Value env ty) env' env'' (s' : Subst env' env'') (s : Subst env env'),
    substVal (composeSubst s' s) v = substVal s' (substVal s v))
/\ (forall env ty (e : Exp   env ty) env' env'' (s' : Subst env' env'') (s : Subst env env'),
    substExp (composeSubst s' s) e = substExp s' (substExp s e)).
Proof.
apply ExpVal_ind;
(intros; try (autorewrite with substHints using try rewrite liftComposeSubst; try rewrite liftComposeSubst; try rewrite H; try rewrite H0; try rewrite H1); auto).
Qed.

Lemma composeCons : forall env env' env'' ty (s':Subst env' env'') (s:Subst env env') (v:Value _ ty), 
  composeSubst (consMap v s') (liftSubst ty s) = consMap v (composeSubst s' s).
intros. apply MapExtensional. intros t0 var.  dependent destruction var. auto. 
unfold composeSubst. simpl. unfold substVal. rewrite <- (proj1 applyComposeRenaming). unfold composeRenaming. simpl.
assert ((fun (t0:Ty) (var0:Var env' t0) => s' t0 var0) = s') by (apply MapExtensional; auto). 
rewrite H. auto. 
Qed.

Lemma composeSubstIdLeft : forall env env' (s : Subst env env'), composeSubst (idSubst _) s = s.
Proof. intros. apply MapExtensional. intros. unfold composeSubst. apply (proj1 applyIdSubst). Qed.

Lemma composeSubstIdRight : forall env env' (s:Subst env env'), composeSubst s (idSubst _) = s.
Proof. intros. apply MapExtensional. auto.  
Qed.

(*==========================================================================
  Constructors are injective 
  ==========================================================================*)

Lemma TPAIR_injective : 
  forall env ty1 ty2 (v1 : Value env ty1) (v2 : Value env ty2) v3 v4, 
  TPAIR v1 v2 = TPAIR v3 v4 -> 
  v1 = v3 /\ v2 = v4.
intros. dependent destruction H. auto. 
Qed.

Lemma TFST_injective : 
  forall env ty1 ty2 (v1 : Value env (ty1 ** ty2)) v2, 
  TFST v1 = TFST v2 -> 
  v1 = v2.
intros. dependent destruction H. auto. 
Qed.

Lemma TSND_injective : 
  forall env ty1 ty2 (v1 : Value env (ty1 ** ty2)) v2, 
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
  forall env ty1 ty2 (e1 : Exp (ty1 :: _ :: env) ty2) e2,
  TFIX e1 = TFIX e2 -> 
  e1 = e2.
intros. dependent destruction H. auto. 
Qed.

(*==========================================================================
  Closed forms
  ==========================================================================*)
Lemma ClosedFunction : forall ty1 ty2 (v : CValue (ty1 --> ty2)), exists b, v = TFIX b.
unfold CValue.
intros ty1 ty2 v.
dependent destruction v.
(* TVAR case: impossible *)
dependent destruction v.
(* TFIX case *)
exists e. trivial.
Qed.

Lemma ClosedPair : forall ty1 ty2 (v : CValue (ty1 ** ty2)), exists v1, exists v2, v = TPAIR v1 v2.
unfold CValue.
intros ty1 ty2 v.
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
