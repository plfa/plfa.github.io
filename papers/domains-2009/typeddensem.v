(* typeddensem.v
   denotational semantics
   This is the second attempt, this time using predomains with lifing
*)

Require Import utility.
Require Export typedlambda.
Require Import PredomAll.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope O_scope.

(*==========================================================================
  Meaning of types and contexts
  ==========================================================================*)

Delimit Scope Ty_scope with Ty.

Open Scope Ty_scope.

Fixpoint SemTy ty :=
match ty with
 | Int => Discrete nat
 | Bool => Discrete bool
 | ty1 --> ty2 => SemTy ty1 -C-> (SemTy ty2) _BOT
 | ty1 ** ty2 => SemTy ty1 *c* SemTy ty2
end.

(* We define the semantics of an environment "from the right";
   this avoids need for SWAP in the semantics *)
Fixpoint SemEnv env :=
match env with
 | nil => DOne
 | ty :: env => SemEnv env *c* SemTy ty
end.

(* Lookup in an environment *)
Fixpoint SemVar env ty (var : Var env ty) : SemEnv env -c> SemTy ty :=
  match var with
  | ZVAR _ _ => SND
  | SVAR _ _ _ v => SemVar v << FST
  end.

(* A coercion to allow embedding values of type X into its lifted 
   discrete domain. DL_discrete is funny because we need to put in the  
   stuff the existing coercions are already adding or else the matching 
   will fail. The Id type operator is there because coercions are by 
   name. *)   

Definition Id (x : Type) := x.
Definition DL_discrete X := tord (tcpo (DL (Discrete X))).

Definition discrete_lift : forall X : Set, Id X -> DL_discrete X := 
  fun X x => eta (x : Discrete X).

Implicit Arguments discrete_lift [X].

Coercion discrete_lift : Id >-> DL_discrete.

(* The need to use the defined operator names -- especially Id --
   makes it seem like a marginal benefit. But maybe it's worth
   it as an example of how coercions work.

Definition top : DL_discrete unit := (tt : Id unit).
Definition top': DL (Discrete unit) := discrete_lift tt.

*) 
Definition indiscrete (X:Type) (x:X) : Discrete X := x.

Definition SimpleOpm (A:Type) (B:cpo) (op : A -> ((tord B) : Type)) : Discrete A -m> B.
intros.
  exists op.
  unfold monotonic.
  intros.
  simpl in *.
  rewrite H. auto.
Defined.

Definition SimpleOp (A:Set) (B:cpo) (op : A -> B) : Discrete A -c> B.
intros.
exists (SimpleOpm op).
unfold continuous.
intros c.
assert (c 0 = lub c). auto.
rewrite <- H. simpl.
assert (op (c 0) <= (SimpleOpm op @ c) 0). auto.
eapply Ole_trans. apply H0.
apply le_lub.
Defined.

Definition SimpleOp2mm (A B C : Type) (op : A -> B -> C) : Discrete A -> Discrete B -m>  Discrete C.
intros.
exists (op X).
unfold monotonic.
intros.
simpl in *.
rewrite H. auto.
Defined.

Definition SimpleOp2c A B C (op:A -> B -> C) :
    Discrete A -> Discrete B -c> Discrete C.
intros.
exists (SimpleOp2mm op X).
simpl in *.
unfold continuous.
intros.
simpl. auto.
Defined.

Definition SimpleOp2m (A B C:Type) (op : A -> B -> C) :
    Discrete A -m> Discrete B -C-> Discrete C.
intros.
exists (SimpleOp2c op).
unfold monotonic.
intros.
simpl in *.
rewrite H. auto.
Defined.

Definition SimpleOp2 A B C (op:A -> B -> C) :
    Discrete A -c> Discrete B -C-> Discrete C.
intros.
exists (SimpleOp2m op).
unfold continuous ; intros ; simpl ; auto.
Defined.

Definition choosemm : forall (D : cpo), D -> D -> Discrete bool -m> D.
intros D X Y.
exists (fun (b:bool) => if b then X else Y).
unfold monotonic ; intros ; simpl in *; rewrite H ; auto.
Defined.

Definition choosec : forall (D : cpo), D -> D -> Discrete bool -c> D.
intros D X Y.
exists (choosemm X Y).
unfold continuous.
intros c ; simpl in *.
assert ((if c 0 then X else Y) = ((choosemm X Y @ c) 0)).
simpl ; auto. rewrite H. apply le_lub.
Defined.

Definition choosem :  forall (D : cpo), D -> D -m> Discrete bool -C-> D.
intros.
exists (@choosec D X).
unfold monotonic.
intros.
simpl. intro.
destruct x0 ; auto.
Defined.

Definition choosecc :  forall (D : cpo), D -> D -c> Discrete bool -C-> D.
intros.
exists (@choosem D X).
unfold continuous.
intros c.
simpl.
intro.
destruct x.
eapply Ole_trans.
assert (X <= ((Fcontit (Discrete bool) D @ (choosem X @ c) <_> true) 0)).
simpl ; auto. apply H.
apply le_lub.
refine (lub_le_compat _).
refine (fmon_le_intro _).
intros n.
auto.
Defined.

Definition choosecm : forall (D:cpo), D -m> D -C-> Discrete bool -C-> D.
intros.
exists (@choosecc D).
unfold monotonic.
intros.
simpl.
intros.
destruct x1. auto. auto.
Defined.

Definition choose : forall (D:cpo), D -c> D -C-> Discrete bool -C-> D.
intros.
exists (@choosecm D).
unfold continuous.
intros c.
simpl. intros.
destruct x0.
refine (lub_le_compat (fmon_le_intro _)).
intros n. auto.

eapply Ole_trans.
assert (x <= ((Fcontit (Discrete bool) D @ ((Fcontit D (Discrete bool -C-> D) @ (choosecm D @ c)) <_> x)) <_> false) 0).
simpl ; auto. apply H.
apply le_lub.
Defined.

Canonical Structure Discrete.

(*==========================================================================
  Meaning of values and expressions
  ==========================================================================*)

Fixpoint SemExp env ty (e : Exp env ty) : SemEnv env -c> (SemTy ty) _BOT :=
match e with
| TOP _ op v1 v2 => eta << uncurry (SimpleOp2 op) << <| SemVal v1 , SemVal v2 |>
| TGT _ v1 v2 => eta << uncurry (SimpleOp2 ble_nat) << <| SemVal v2 , SemVal v1 |>
| TAPP _ _ _ v1 v2 => EV << <| SemVal v1 , SemVal v2 |>
| TVAL _ _ v => eta << SemVal v
| TLET _ _ _ e1 e2 => KLEISLIR (SemExp e2) << <| ID , SemExp e1 |>
| TIF _ _ v e1 e2 => (choose _ @3_ (SemExp e1)) (SemExp e2) (SemVal v)
| TFST _ _ _ v => eta << FST << SemVal v
| TSND _ _ _ v => eta << SND << SemVal v
end

with SemVal env ty (v : Value env ty) : SemEnv env -c> SemTy ty :=
match v with
| TINT _ n => K _ (n : Discrete nat) 
| TBOOL _ b => K _ (b : Discrete bool)
| TVAR _ _ i => SemVar i
| TFIX _ _ _ e => FIXP << curry (curry (SemExp e))
| TPAIR _ _ _ v1 v2 => <| SemVal v1 , SemVal v2 |>
end.


Lemma choosec_t_simpl: forall (D:cpo) (a b:D), choosec a b true = a.
intros D a b.
auto.
Qed.

Lemma choosec_f_simpl: forall (D:cpo) (a b:D), choosec a b false = b.
intros D a b.
auto.
Qed.

Lemma choose_t_simpl: forall D a b, choose D a b true = a.
auto.
Qed.
Lemma choose_f_simpl: forall D a b, choose D a b false = b.
auto.
Qed.

Add Parametric Morphism E t (e:Exp E t) : (SemExp e)
with signature (@Oeq (SemEnv E)) ==> (@Oeq (DL (SemTy t)))
as SemExp_eq_compat.
intros e0 e1 eeq.
destruct eeq. split ; auto.
Qed.

Add Parametric Morphism E t (e:Value E t) : (SemVal e)
with signature (@Oeq (SemEnv E)) ==> (@Oeq (SemTy t))
as SemVal_eq_compat.
intros e0 e1 eeq.
destruct eeq. split ; auto.
Qed.

