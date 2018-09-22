(**********************************************************************************
 * typeddensem.v                                                                  *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                       *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)

Require Export typedlambda.
Require Import PredomAll.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Open Scope C_scope.
Open Scope D_scope.
Open Scope S_scope.

(*==========================================================================
  Meaning of types and contexts
  ==========================================================================*)

Delimit Scope Ty_scope with Ty.

Open Scope Ty_scope.

(*=SemTy *)
Fixpoint SemTy t : cpoType :=
  match t with
  | Int => nat_cpoType
  | Bool => (One:cpoType) + One
  | t1 --> t2 => SemTy t1 -=> (SemTy t2)_BOT
  | t1 ** t2 => SemTy t1 * SemTy t2
  end.
Fixpoint SemEnv E : cpoType :=
  match E with
  | nil => One
  | t :: E => SemEnv E * SemTy t
  end.
(*=End *)

(* Lookup in an environment *)
(*=SemVarExpVal *)
Fixpoint SemVar E t (var : Var E t) : SemEnv E =-> SemTy t :=
  match var with
  | ZVAR _ _ => pi2
  | SVAR _ _ _ v => SemVar v << pi1
  end. (*CLEAR*)

Lemma SimpleB_mon (A B :Type) (C:ordType) (op : A -> B -> C:Type) : monotonic (fun p:discrete_ordType A * discrete_ordType B => op (fst p) (snd p)).
case => x0 y0. case => x1 y1. case ; simpl. move => L L'.
have e:x0 = x1 by []. have e':y0 = y1 by []. rewrite e. by rewrite e'.
Qed.

Definition SimpleBOpm (A B :Type) (C:ordType) (op : A -> B -> C:Type) : discrete_ordType A * discrete_ordType B =-> C :=
  mk_fmono (SimpleB_mon op).

Lemma SimpleB_cont (A B:Type) (C:cpoType) (op : A -> B -> C:Type) :
   @continuous (discrete_cpoType A * discrete_cpoType B) C (SimpleBOpm op).
move => c. simpl. apply: (Ole_trans _ (le_lub _ 0)). simpl.
by [].
Qed.

Definition SimpleBOp (A B:Type) (C:cpoType) (op : A -> B -> C:Type) : discrete_cpoType A * discrete_cpoType B =-> C :=
  Eval hnf in mk_fcont (SimpleB_cont op).

Lemma choose_cont (Y Z: cpoType) (a:Z =-> Y) (b : Z =-> Y) (c:Z =-> (One:cpoType) + One) :
  forall x,
  (fun y => match c y with inl y' => a x | inr y' => b x end) x =-=
  (ev << <| SUM_Fun << <| exp_fun ((uncurry  (const One a)) << SWAP),
                                  exp_fun ((uncurry (const One b)) << SWAP) |>, c|>) x.
move => x. simpl. rewrite SUM_fun_simplx. by case_eq (c x) ; case => e.
Qed.

Definition choose (Y Z: cpoType) (a:Z =-> Y) (b : Z =-> Y) (c:Z =-> (One:cpoType) + One) :=
  Eval hnf in gen_cont (choose_cont a b c).

Lemma choose_comp (Y Z W : cpoType)  (a:Z =-> Y) (b : Z =-> Y) (c:Z =-> (One:cpoType) + One) 
   (h : W =-> Z) : choose a b c << h =-= choose (a << h) (b << h) (c << h).
by apply: fmon_eq_intro => x.
Qed.

Add Parametric Morphism (A B:cpoType) : (@choose A B)
  with signature (@tset_eq _) ==> (@tset_eq _) ==> (@tset_eq _) ==> (@tset_eq _)
    as choose_eq_compat.
move => f f' e g g' e' x x' ex.
apply: fmon_eq_intro => y. simpl. move: (fmon_eq_elim ex y). clear ex. unfold FCont.fmono. simpl.
case: (x y) ; case: (x' y) ; case ; case ; (try by case) ; move => _. by rewrite e. by rewrite e'.
Qed.

(*  SemExpVal *) 
(*CLEARED*)
Fixpoint SemExp E t (e : Exp E t) : SemEnv E =-> (SemTy t) _BOT :=
match e with
| TOP op v1 v2    => eta  << SimpleBOp op << <|  SemVal v1 , SemVal v2 |>
| TGT v1 v2       => eta  << SimpleBOp (fun x y => if leq x y then inl _ tt else inr _ tt)
                        << <| SemVal v2 , SemVal v1 |>
| TAPP _ _ v1 v2  => ev  << <| SemVal v1 , SemVal v2 |>
| TVAL _ v        => eta  << SemVal v
| TLET _ _ e1 e2  => KLEISLIR (SemExp e2) << <| Id , SemExp e1 |>
| TIF _ v e1 e2   => choose (SemExp e1) (SemExp e2) (SemVal v)
| TFST _ _ v      => eta  << pi1  << SemVal v
| TSND _ _ v      => eta  << pi2  << SemVal v
end with SemVal E t (v : Value E t) : SemEnv E =-> SemTy t :=
match v with
| TINT n          => const _ n
| TBOOL b         => const _ (if b then inl _ tt else inr _ tt)
| TVAR _ i        => SemVar i
| TFIX t1 t2 e    => (FIXP : cpoCatType _ _) << exp_fun (exp_fun (SemExp e))
| TPAIR _ _ v1 v2 => <|  SemVal v1 , SemVal v2 |>
end.
(*=End *)
