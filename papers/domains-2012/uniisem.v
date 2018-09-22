(**********************************************************************************
 * uniisem.v                                                                      *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                       *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)

(* semantics of unityped lambda calculus in recursive domain *)

Require Import PredomAll. 
Require Import Fin unii uniirec.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Export RD.

(*=SemEnv *)
Fixpoint SemEnv E : cpoType := match E with O => One | S E => SemEnv E * VInf end.
Fixpoint SemVar E (v : Fin E) : SemEnv E =-> VInf :=
  match v with 
  | FinZ _   => pi2
  | FinS _ v => SemVar v << pi1
  end.
(*=End *)

Canonical Structure nat_cpoType := Eval hnf in discrete_cpoType nat.
Canonical Structure bool_cpoType := Eval hnf in discrete_cpoType bool.

Lemma zeroCase_mon : monotonic (fun (n:nat_cpoType) => match n with | O => @in1 _ (One:cpoType) _ tt | S m => @in2 _ _ (discrete_cpoType nat) m end).
move => x y. case. move => e ; rewrite e. clear x e. by case: y.
Qed.

Definition zeroCasem : ordCatType (discrete_cpoType nat) ((One:cpoType) + nat_cpoType) :=
  Eval hnf in mk_fmono zeroCase_mon.

Lemma zeroCase_cont : continuous zeroCasem.
move => c. simpl. have e:lub c = c 0. by []. rewrite e. simpl.
by apply: (Ole_trans _ (le_lub _ O)).
Qed.

(*=zeroCase *)
Definition zeroCase : nat_cpoType =-> (One:cpoType) + nat_cpoType := 
  Eval hnf in mk_fcont zeroCase_cont.
(*=End *)

Lemma zeroCase_simplS: forall n, zeroCase (S n) = @in2 _ _ (discrete_cpoType nat) n.
intros n ; auto.
Qed.

Lemma zeroCase_simplO: zeroCase O = @in1 _ (One:cpoType) _ tt.
auto.
Qed.

Lemma SimpleB_mon (A B :Type) (C:ordType) (op : A -> B -> C:Type) : monotonic (fun p:discrete_ordType A * discrete_ordType B => op (fst p) (snd p)).
case => x0 y0. case => x1 y1. case ; simpl. move => L L'.
have e:x0 = x1 by []. have e':y0 = y1 by []. rewrite e. by rewrite e'.
Qed.

Definition SimpleBOpm (A B :Type) (C:ordType) (op : A -> B -> C:Type) : discrete_ordType A * discrete_ordType B =-> C :=
  Eval hnf in mk_fmono (SimpleB_mon op).

Lemma SimpleB_cont (A B:Type) (C:cpoType) (op : A -> B -> C:Type) :
   @continuous (discrete_cpoType A * discrete_cpoType B) C (SimpleBOpm op).
move => c. simpl. apply: (Ole_trans _ (le_lub _ 0)). simpl.
by [].
Qed.

Definition SimpleBOp (A B:Type) (C:cpoType) (op : A -> B -> C:Type) : discrete_cpoType A * discrete_cpoType B =-> C :=
  Eval hnf in mk_fcont (SimpleB_cont op).

(*=SemValExp *)
Fixpoint SemVal E (v:Value E) : SemEnv E =-> VInf :=
match v return SemEnv E =-> VInf with
| INT i => in1 << const _ i
| VAR m => SemVar m
| LAMBDA e => in2 << exp_fun (kleisli (eta << RD.Roll) << SemExp e << Id >< RD.Unroll)
end with SemExp E (e:Exp E) : SemEnv E =-> RD.VInf _BOT :=
match e with
| VAL v => eta  << SemVal v
| APP v1 v2 => kleisli (eta << RD.Unroll) << ev << 
    <| [| @const _ (exp_cppoType _ _) PBot , Id|] << SemVal v1, RD.Roll << SemVal v2 |>
| LET e1 e2 => ev << <| exp_fun (KLEISLIR (SemExp e2)), SemExp e1 |>
| OP op v0 v1 => kleisli (eta << in1 << SimpleBOp op) << uncurry (Smash _ _) <<
                  <| [| eta, const _ PBot|] << SemVal v0, [| eta, const _ PBot|] << SemVal v1|>
| IFZ v e1 e2 => ev <<
  [| [| exp_fun (SemExp e1 << pi2), exp_fun (SemExp e2 << pi2)|] << zeroCase , 
     @const _ (exp_cppoType _ _) PBot |]  ><  Id  <<  <|SemVal v, Id|>
end.
(*=End *)

Lemma Operator2_strictL A B C (f:A * B =-> C _BOT) d : Operator2 f PBot d =-= PBot.
apply: Ole_antisym ; last by apply: leastP.
unlock Operator2. simpl. by do 2 rewrite kleisli_bot.
Qed.

Lemma Operator2_strictR A B C (f:A * B =-> C _BOT) d : Operator2 f d PBot =-= PBot.
apply: Ole_antisym ; last by apply: leastP.
unlock Operator2. simpl.
apply: (Ole_trans (proj2 (fmon_eq_elim (kleisli_comp2 _ _) d))).
apply: DLless_cond. move => c X.
case: (kleisliValVal X) => a [e P]. rewrite -> e. clear d e X.
simpl in P. rewrite -> kleisli_bot in P.
by case: (PBot_incon (proj2 P)).
Qed.

Add Parametric Morphism E (e:Exp E) : (SemExp e)
with signature (@tset_eq _ : SemEnv E -> SemEnv E -> Prop) ==> (@tset_eq _ : VInf _BOT -> VInf _BOT -> Prop)
as SemExp_eq_compat.
intros e0 e1 eeq. by apply (fmon_stable (SemExp e)).
Qed.

Add Parametric Morphism E (v:Value E) : (SemVal v)
with signature (@tset_eq _ : SemEnv E -> SemEnv E -> Prop) ==> (@tset_eq _ : VInf -> VInf -> Prop)
as SemVal_eq_compat.
intros e0 e1 eeq. by apply (fmon_stable (SemVal v)). 
Qed.


