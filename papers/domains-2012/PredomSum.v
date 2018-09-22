(**********************************************************************************
 * PredomSum.v                                                                    *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                       *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)


(*==========================================================================
  Definition of co-products and associated lemmas
  ==========================================================================*)
Require Import PredomCore.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(*==========================================================================
  Order-theoretic definitions
  ==========================================================================*)

Section OrdSum.

Variable O1 O2 : ordType.

Lemma sum_ordAxiom : PreOrd.axiom (fun (x y:O1+O2) => match x, y with | inl x, inl y => x <= y | inr x, inr y => x <= y | _,_ =>  False end).
case => x0. split ; first by []. by case => x1 ; case => x2 ; try apply Ole_trans.
split ; first by []. by case => x1 ; case => x2 ; try apply Ole_trans.
Qed.

Canonical Structure sum_ordMixin := OrdMixin sum_ordAxiom.
Canonical Structure sum_ordType := Eval hnf in OrdType sum_ordMixin.

Lemma inl_mono : monotonic (@inl O1 O2).
by move => x y l.
Qed.

Definition Inl : O1 =-> sum_ordType := Eval hnf in mk_fmono inl_mono.

Lemma inr_mono : monotonic (@inr O1 O2).
by move => x y l.
Qed.

Definition Inr : O2 =-> sum_ordType := Eval hnf in mk_fmono inr_mono.

Lemma sum_fun_mono (O3:ordType) (f:O1 =-> O3) (g:O2 =-> O3) : monotonic (fun x => match x with inl x => f x | inr y => g y end).
by case => x ; case => y ; try done ; move => X ; apply fmonotonic.
Qed.

Definition Osum_fun (O3:ordType) (f:O1 =-> O3) (g:O2 =-> O3) := Eval hnf in mk_fmono (sum_fun_mono f g).

End OrdSum.

Lemma sumOrdAxiom : @CatSum.axiom _ (sum_ordType) (@Inl) (@Inr) (@Osum_fun).
move => O0 O1 O2 f g. split ; first by split ; apply: fmon_eq_intro.
move => m [A B]. apply: fmon_eq_intro. case => x.
- by apply (fmon_eq_elim A x).
- by apply (fmon_eq_elim B x).
Qed.

Canonical Structure sum_ordCatMixin := sumCatMixin sumOrdAxiom.
Canonical Structure sum_ordCatType := Eval hnf in sumCatType sum_ordCatMixin.

Add Parametric Morphism (D E F:ordType) : (@Osum_fun D E F)
with signature (@Ole _ : (D =-> F) -> (D =-> F) -> Prop) ++> (@Ole _ : (E =-> F) -> (E =-> F) -> Prop) ++>
   (@Ole (sum_ordType _ _ -=> _) : ((D + E) =-> F) -> (_ =-> _) -> Prop)
as Osum_fun_le_compat.
intros f f' lf g g' lg.
simpl. intros x ; case x ; clear x ; auto.
Qed.

Add Parametric Morphism (D E F:ordType) : (@Osum_fun D E F)
with signature (@tset_eq _ : (D =-> F) -> (D =-> F) -> Prop ) ==>
      (@tset_eq _ : (E =-> F) -> (E =-> F) -> Prop) ==> (@tset_eq ((sum_ordType D E) -=> F))
as Osum_fun_eq_compat.
intros f f' lf g g' lg.
simpl. apply fmon_eq_intro.
destruct lg. destruct lf.
intros x ; split ; case x ; clear x ; auto.
Qed.

Section CPOSum.

Variable D1 D2 : cpoType.

Lemma sum_left_mono (c:natO =-> sum_ordType D1 D2) (ex:{d| c O = inl D2 d}) :
   monotonic (fun x => match c x with | inl y => y | inr _ => projT1 ex end).
case:ex => x X. simpl.
move => z z' l. simpl.
have H:= fmonotonic c (leq0n z). have HH:=fmonotonic c (leq0n z').
rewrite -> X in H,HH.
have A:=fmonotonic c l. case: (c z) H A ; last by [].
move => x0 _. by case: (c z') HH.
Qed.

Definition sum_left (c:natO =-> sum_ordType D1 D2) (ex:{d| c O = inl D2 d}) : natO =-> D1 :=
   Eval hnf in mk_fmono (sum_left_mono ex).

Lemma sum_right_mono (c:natO =-> sum_ordType D1 D2) (ex:{d| c O = inr D1 d}) :
   monotonic (fun x => match c x with | inr y => y | inl _ => projT1 ex end).
case:ex => x X. simpl.
move => z z' l. simpl.
have H:= fmonotonic c (leq0n z). have HH:=fmonotonic c (leq0n z').
rewrite -> X in H,HH.
have A:=fmonotonic c l. case: (c z) H A ; first by [].
move => x0 _. by case: (c z') HH.
Qed.

Definition sum_right (c:natO =-> sum_ordType D1 D2) (ex:{d| c O = inr D1 d}) : natO =-> D2 :=
   Eval hnf in mk_fmono (sum_right_mono ex).

Definition SuminjProof (c:natO =-> sum_ordType D1 D2) (n:nat) :
      {d | c n = inl D2 d} + {d | c n = inr D1 d}.
case: (c n) => cn.
- left. by exists cn.
- right. by exists cn.
Defined.

Definition sum_lub (c: natO =-> sum_ordType D1 D2) : sum_ordType D1 D2 :=
match (SuminjProof c 0) with
| inl X => (inl D2 (lub (sum_left X)))
| inr X => (inr D1 (lub (sum_right X)))
end.

(*==========================================================================
  Domain-theoretic definitions
  ==========================================================================*)

Lemma Dsum_ub (c : natO =-> sum_ordType D1 D2) (n : nat) : c n <= sum_lub c.
have L:=fmonotonic c (leq0n n).
unfold sum_lub. case: (SuminjProof c 0) ; case => c0 e ; rewrite e in L.
-  move: L. case_eq (c n) ; last by []. move => cn e' L. apply: (Ole_trans _ (le_lub _ n)).
  simpl. by rewrite e'.
-  move: L. case_eq (c n) ; first by []. move => cn e' L. apply: (Ole_trans _ (le_lub _ n)).
  simpl. by rewrite e'.
Qed.

Lemma Dsum_lub (c : natO =-> sum_ordType D1 D2) (x : sum_ordType D1 D2) :
   (forall n : natO, c n <= x) -> sum_lub c <= x.
case x ; clear x ; intros x cn. unfold sum_lub.
case (SuminjProof c 0).
- intros s. assert (lub (sum_left s) <= x).
  apply (lub_le). intros n. specialize (cn n). destruct s as [d c0].
  simpl. case_eq (c n).
  + intros dn dnl. rewrite dnl in cn. by auto.
  + intros dn cnr. rewrite cnr in cn. by inversion cn.
  by auto.
- intros s. destruct s. simpl. specialize (cn 0). rewrite e in cn. by inversion cn.
- unfold sum_lub. case (SuminjProof c 0) ; first case.
  + move => y e. simpl. specialize (cn 0). rewrite e in cn. by inversion cn.
  + intros s. assert (lub (sum_right s) <= x).
    * apply lub_le. intros n. specialize (cn n). destruct s as [d c0].
      simpl. case_eq (c n).
      - intros dl cnl. rewrite cnl in cn. by inversion cn.
      - intros dl dll. rewrite dll in cn. by auto.
    by auto.
Qed.

Lemma sum_cpoAxiom : CPO.axiom sum_lub.
move => c s n.
split ; first by apply Dsum_ub.
by apply Dsum_lub.
Qed.

Canonical Structure sum_cpoMixin := CpoMixin sum_cpoAxiom.
Canonical Structure sum_cpoType := Eval hnf in CpoType sum_cpoMixin.

(*
(** Printing +c+ %\ensuremath{+}% *)
Infix "+c+" := Dsum (at level 28, left associativity).*)

Variable D3:cpoType.

Lemma SUM_fun_cont (f:D1 =-> D3) (g:D2 =-> D3) : @continuous sum_cpoType _ (Osum_fun f g).
intros c. simpl.
case_eq (lub c).
- move => ll sl. unfold lub in sl. simpl in sl. unfold sum_lub in sl. destruct (SuminjProof c 0) ; last by [].
  case: sl => e. rewrite <- e. clear ll e. rewrite -> (fcontinuous f (sum_left s)).
  apply lub_le_compat => n. simpl. case: s => d s. simpl. move: (fmonotonic c (leq0n n)).
  case: (c 0) s ; last by []. move => s e. rewrite -> e ; clear s e. by case: (c n).
- move => ll sl. unfold lub in sl. simpl in sl. unfold sum_lub in sl. destruct (SuminjProof c 0) ; first by [].
  case: sl => e. rewrite <- e. clear ll e. rewrite -> (fcontinuous g (sum_right s)).
  apply lub_le_compat => n. simpl. case: s => d s. simpl. move: (fmonotonic c (leq0n n)).
  case: (c 0) s ; first by []. move => s e. rewrite -> e ; clear s e. by case: (c n).
Qed.

Definition SUM_funX (f:D1 =-> D3) (g:D2 =-> D3) : sum_cpoType =-> D3 := Eval hnf in mk_fcont (SUM_fun_cont f g).
Definition SUM_fun f g := locked (SUM_funX f g).

Lemma SUM_fun_simpl f g x : SUM_fun f g x =-= match x with inl x => f x | inr x => g x end.
unlock SUM_fun. simpl. by case: x.
Qed.

(** printing [| %\ensuremath{[} *)
(** printing |] %\ensuremath{]} *)
(* Notation "'[|' f , g '|]'" := (SUM_fun f g) (at level 30).*)

Lemma Inl_cont : continuous (Inl D1 D2).
move => c. simpl. by apply: lub_le_compat => n.
Qed.

Definition INL : D1 =-> sum_cpoType := Eval hnf in mk_fcont Inl_cont.

Lemma Inr_cont : continuous (Inr D1 D2).
move => c. simpl. by apply: lub_le_compat => n.
Qed.

Definition INR : D2 =-> sum_cpoType := Eval hnf in mk_fcont Inr_cont.

End CPOSum.

Lemma sumCpoAxiom : @CatSum.axiom _ sum_cpoType (@INL) (@INR) (@SUM_fun).
move => D0 D1 D2 f g. split. unlock SUM_fun. apply: (proj1 (@sumOrdAxiom D0 D1 D2 f g)).
move => m. unlock SUM_fun. apply: (proj2 (@sumOrdAxiom D0 D1 D2 f g)).
Qed.

Canonical Structure cpoSumCatMixin := sumCatMixin sumCpoAxiom.
Canonical Structure cpoSumCatType := Eval hnf in sumCatType cpoSumCatMixin.

Lemma SUM_fun_simplx (X Y Z : cpoType) (f:X =-> Z) (g : Y =-> Z) x : [|f,g|] x =-= match x with inl x => f x | inr x => g x end.
case:x => x ; unfold sum_fun ; simpl ; by rewrite SUM_fun_simpl.
Qed.

Definition getmorph (D E : cpoType) (f:D -=> E) : D =-> E := ev << <| const _ f, Id |>.

Lemma SUM_Fun_mon (D E F:cpoType) : monotonic (fun (P:(D -=> F) * (E -=> F)) => [|getmorph (fst P), getmorph (snd P)|]).
case => f g. case => f' g'. case ; simpl => l l' x.
unfold sum_fun. simpl. do 2 rewrite SUM_fun_simpl.
by case x ; [apply l | apply l'].
Qed.

Definition SUM_Funm (D E F:cpoType) : fmono_ordType ((D -=> F) * (E -=> F)) (D + E -=> F) :=
  Eval hnf in mk_fmono (@SUM_Fun_mon D E F).

Lemma SUM_Fon_cont (D E F:cpoType) : continuous (@SUM_Funm D E F).
move => c. simpl. unfold getmorph. unfold sum_fun. simpl.
by case => x ; simpl ; rewrite SUM_fun_simpl ; apply: lub_le_compat => n ; simpl ; rewrite SUM_fun_simpl.
Qed.

Definition SUM_Fun (D E F:cpoType) : ((D -=> F) * (E -=> F)) =-> (D + E -=> F) := Eval hnf in  mk_fcont (@SUM_Fon_cont D E F).
Implicit Arguments SUM_Fun [D E F].

Lemma SUM_Fun_simpl (D E F:cpoType) (f:D =-> F) (g:E =-> F) : SUM_Fun (f,g) =-= SUM_fun f g.
apply: fmon_eq_intro => x. simpl. unfold sum_fun. simpl. by do 2 rewrite SUM_fun_simpl.
Qed.


