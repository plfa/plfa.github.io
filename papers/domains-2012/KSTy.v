(**********************************************************************************
 * KSTy.v                                                                         *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                       *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)

(* Kitchen sink types *)

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

Module Ty.

  Definition Env := nat.

(*=Ty *)  
  Inductive Ty E :=
  | TVar: Fin E -> Ty E
  | Int: Ty E 
  | Unit: Ty E
  | Product: Ty E -> Ty E -> Ty E
  | Sum: Ty E -> Ty E -> Ty E
  | Mu: Ty E.+1 -> Ty E 
  | All: Ty E.+1 -> Ty E
  | Arrow: Ty E -> Ty E -> Ty E
  | Ref: Ty E -> Ty E.
(*=End *)  
  Implicit Arguments Unit [E].
  Implicit Arguments Int [E].

  Scheme Ty_ind2 := Induction for Ty Sort Prop.

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
      vr : forall E, Fin E -> P E;   
      vl : forall E, P E -> Ty E;
      wk : forall E, P E -> P E.+1;
      wkvr : forall E (var : Fin E), wk (vr var) = vr (FinS var);
      vlvr : forall E (var : Fin E), vl (vr var) = TVar var
    }.
    Variable ops : Ops.

    
    Definition lift E E' (m : Map E E') : Map E.+1 E'.+1 :=
    (fun var => match var in Fin E return Map E.-1 E' -> P E'.+1 with
    | FinZ _   => fun _ => vr ops (FinZ _)
    | FinS _ x => fun m => wk ops (m x)
    end m).

    Definition shift E E' (m : Map E E') : Map E E'.+1 := fun var => wk ops (m var).
    Definition id E : Map E E := fun (var : Fin E) => vr ops var.

    Lemma shiftCons : forall E E' (m : Map E E') (x : P E'), shift (cons x m) = cons (wk ops x) (shift m). 
    Proof. move => E E' m x. apply Extensionality. by dependent destruction i. Qed.

    Lemma liftAsCons : forall E E' (m : Map E' E), lift m = cons (vr ops (FinZ _)) (shift m).
    Proof. move => E E' m. apply Extensionality. by dependent destruction i. Qed.

    Fixpoint mapTy E E' (m : Map E E') (t : Ty E) : Ty E' :=
    match t with
    | TVar v => vl ops (m v)
    | Int => Int
    | Unit => Unit
    | Product t1 t2 => Product (mapTy m t1) (mapTy m t2)
    | Sum t1 t2 => Sum (mapTy m t1) (mapTy m t2)
    | Mu t => Mu (mapTy (lift m) t)
    | All t => All (mapTy (lift m) t)
    | Arrow t1 t2 => Arrow (mapTy m t1) (mapTy m t2)
    | Ref t => Ref (mapTy m t)
    end.
 
    Variable E E' : Env.
    Variable m : Map E E'.
    Lemma mapTVar : forall (var : Fin _), mapTy m (TVar var) = vl ops (m var). by []. Qed. 
    Lemma mapInt : mapTy m Int = Int. by []. Qed.
    Lemma mapUnit : mapTy m Unit = Unit. by []. Qed.
    Lemma mapMu : forall t, mapTy m (Mu t) = Mu (mapTy (lift m) t). by []. Qed.
    Lemma mapAll : forall t, mapTy m (All t) = All (mapTy (lift m) t). by []. Qed.
    Lemma mapProduct : forall t1 t2, mapTy m (Product t1 t2) = Product (mapTy m t1) (mapTy m t2). by []. Qed.
    Lemma mapSum : forall t1 t2, mapTy m (Sum t1 t2) = Sum (mapTy m t1) (mapTy m t2). by []. Qed.
    Lemma mapArrow : forall t1 t2, mapTy m (Arrow t1 t2) = Arrow (mapTy m t1) (mapTy m t2). by []. Qed.
    Lemma mapRef : forall t, mapTy m (Ref t) = Ref (mapTy m t). by []. Qed.
  
    Lemma liftId : lift (@id E) = @id E.+1.
    Proof. apply Extensionality. dependent destruction i; [by [] | by apply wkvr].  
    Qed.

    Lemma idAsCons : @id E.+1 = cons (vr ops (FinZ _)) (shift (@id E)).
    Proof. apply Extensionality. dependent destruction i; first by []. unfold id, shift. simpl. by rewrite wkvr. Qed.

  End MAP. 

  Hint Rewrite mapTVar mapInt mapUnit mapMu mapAll mapProduct mapSum mapArrow mapRef : mapHints.
  Implicit Arguments id [P].

  Lemma applyId P (ops:Ops P) E : (forall (t : Ty E), mapTy ops (id ops E) t = t).
  Proof. induction t; intros; autorewrite with mapHints; Rewrites liftId. by apply vlvr. Qed.

  End Map. 

(*==========================================================================
  Variable renamings: Map Var
  ==========================================================================*)

Definition Ren   := Map.Map Fin. 
Definition RenOps : Map.Ops Fin. refine (@Map.Build_Ops _ (fun _ v => v) TVar FinS _ _). by []. by [].  Defined. 

Definition renTy := Map.mapTy RenOps.
Definition liftRen := Map.lift RenOps.
Definition shiftRen := Map.shift RenOps.
Definition idRen := Map.id RenOps.

(*==========================================================================
  Composition of renaming
  ==========================================================================*)

Definition composeRen P E E' E'' (m : Map.Map P E' E'') (r : Ren E E') : Map.Map P E E'' := fun var => m (r var). 

Lemma liftComposeRen : forall E E' E'' P ops (m:Map.Map P E' E'') (r:Ren E E'), Map.lift ops (composeRen m r) = composeRen (Map.lift ops m) (liftRen r).
Proof. move => E E' E'' P ops m r. apply Extensionality. by dependent destruction i. Qed.

Lemma applyComposeRen E : 
 (forall (t : Ty E) E' E'' P ops (m:Map.Map P E' E'') (s : Ren E E'),
  Map.mapTy ops (composeRen m s) t = Map.mapTy ops m (renTy s t)).
Proof. induction t; intros; autorewrite with mapHints; Rewrites liftComposeRen. Qed.

(*==========================================================================
  Substitution
  ==========================================================================*)

Definition Sub := Map.Map Ty.
Definition SubOps : Map.Ops Ty. refine (@Map.Build_Ops _ TVar (fun _ v => v) (fun E => renTy (fun v => FinS v)) _ _). by []. by []. Defined.

Definition subTy := Map.mapTy SubOps.
Definition shiftSub := Map.shift SubOps.
Definition liftSub := Map.lift SubOps.
Definition idSub := Map.id SubOps.

Ltac UnfoldRenSub := (unfold subTy; unfold renTy; unfold liftSub; unfold liftRen).
Ltac FoldRenSub := (fold subTy; fold renTy; fold liftSub; fold liftRen).
Ltac SimplMap := (UnfoldRenSub; autorewrite with mapHints; FoldRenSub).

(*==========================================================================
  Composition of substitution followed by renaming
  ==========================================================================*)
Definition composeRenSub E E' E'' (r : Ren E' E'') (s : Sub E E') : Sub E E'' := fun var => renTy r (s var). 

Lemma liftComposeRenSub : forall E E' E'' (r:Ren E' E'') (s:Sub E E'), liftSub (composeRenSub r s) = composeRenSub (liftRen r) (liftSub s).
intros. apply Extensionality. dependent destruction i; first by [].
unfold composeRenSub, liftSub. simpl. unfold renTy at 1 3. by do 2 rewrite <- applyComposeRen. 
Qed.

Lemma applyComposeRenSub E :
   (forall (t:Ty E) E' E'' (r:Ren E' E'') (s : Sub E E'),
    subTy (composeRenSub r s) t = renTy r (subTy s t)).
Proof. induction t; intros; SimplMap; Rewrites liftComposeRenSub. Qed. 

(*==========================================================================
  Composition of substitutions
  ==========================================================================*)

Definition composeSub E E' E'' (s' : Sub E' E'') (s : Sub E E') : Sub E E'' := fun var => subTy s' (s var). 

Lemma liftComposeSub : forall E E' E'' (s' : Sub E' E'') (s : Sub E E'), liftSub (composeSub s' s) = composeSub (liftSub s') (liftSub s).
intros. apply Extensionality. dependent destruction i; first by []. 
unfold composeSub. simpl. rewrite <- applyComposeRenSub. unfold composeRenSub, subTy. by rewrite <- applyComposeRen. 
Qed.

Lemma applyComposeSub E : 
   (forall (t : Ty E) E' E'' (s' : Sub E' E'') (s : Sub E E'),
    subTy (composeSub s' s) t = subTy s' (subTy s t)).
Proof. induction t; intros; SimplMap; Rewrites liftComposeSub. Qed.

Lemma composeCons : forall E E' E'' (s':Sub E' E'') (s:Sub E E') (v:Ty _), 
  composeSub (cons v s') (liftSub s) = cons v (composeSub s' s).
intros. apply Extensionality. dependent destruction i; first by [].
unfold composeSub. unfold subTy. simpl. rewrite <- applyComposeRen. unfold composeRen.
simpl. replace ((fun (var0:Fin E') => s' var0)) with s' by (by apply Extensionality). by [].
Qed.

Lemma composeSubIdLeft : forall E E' (s : Sub E E'), composeSub (@idSub _) s = s.
Proof. intros. apply Extensionality.  intros var. by apply Map.applyId. Qed.

Lemma composeSubIdRight : forall E E' (s:Sub E E'), composeSub s (@idSub _) = s.
Proof. intros. by apply Extensionality. Qed.

Notation "[ x , .. , y ]" := (cons x .. (cons y (@Map.id _ SubOps _)) ..) : Sub_scope. 
Arguments Scope composeSub [_ _ _ Sub_scope Sub_scope]. 
Arguments Scope subTy [_ _ Sub_scope]. 
Delimit Scope Sub_scope with sub.

Lemma composeSingleSub : forall E E' (s:Sub E E') (t:Ty _), composeSub [t] (liftSub s) = cons t s.
Proof. intros. rewrite composeCons. by rewrite composeSubIdLeft. Qed.

End Ty.

Notation "a --> b" := (Ty.Arrow a b) (at level 55, right associativity).
Notation "a ** b" := (Ty.Product a b) (at level 55).



