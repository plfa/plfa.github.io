(**********************************************************************************
 * KSSem.v                                                                         *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                       *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)

(* semantics of types for the kitchen sink language *)

Require Import MetricRec mpremet.
Require Import Fin KSTy KSTm KSTyping KSOp.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope C_scope.
Open Scope M_scope.

Definition CValue := Tm.Value O.
Definition CExp := Tm.Exp O.

(*=MetBF *)
Definition BF : BiFunctor pcmECatType := findomBF
 ((BiComp (halveBF idBF) (constBF (upred_pcmType CValue)) BiArrow))
                                                         [compType of nat]. (*CLEAR*)
Lemma BF_ob A B : ob BF A B = findom_pcmType [compType of nat] (halve_pcmType A -=> upred_pcmType CValue).
by [].
Qed.

Lemma morph_contractive A B C D : contractive (MetricRec.morph BF A B C D).
unfold BF. apply findom_BF_contractive.
apply comp_BF_contractive ; last by apply constBF_contractive. by apply halve_morph_contractive.
Qed.

Module Type RecMet.

Variable W : pcmType.
Variable Unfold : W =-> findom_pcmType [compType of nat] (halve_pcmType W -=> upred_pcmType CValue).
Variable Fold : findom_pcmType [compType of nat] (halve_pcmType W -=> upred_pcmType CValue) =-> W.

Variable FU_id : Fold << Unfold =-= Id.
Variable UF_id : Unfold << Fold =-= Id.

End RecMet.

Module Solution : RecMet.

(*CLEARED*) 
Definition W : pcmType := @DInf BF morph_contractive.
Definition Unfold := @Unfold BF morph_contractive :
  W =-> findom_pcmType [compType of nat] (halve_pcmType W -=> upred_pcmType CValue).
Definition Fold  := @Fold BF morph_contractive :
  findom_pcmType [compType of nat] (halve_pcmType W -=> upred_pcmType CValue) =-> W.
(*=End *)

Lemma FU_id : Fold << Unfold =-= Id.
apply (@FU_iso BF morph_contractive).
Qed.

Lemma UF_id : Unfold << Fold =-= Id.
apply (@UF_iso BF morph_contractive).
Qed.

End Solution.
Export Solution.

Open Scope O_scope.

Lemma Fold_monic x y : Fold x <= Fold y -> x <= y.
move => X. have M:=fmonotonic Unfold X. have e:= (UF_id x). have e':=UF_id y.
apply (pcm_respect e e' M).
Qed.

Lemma Unfold_monic x y : Unfold x <= Unfold y -> x <= y.
move => X. have M:=fmonotonic Fold X. have e:= (FU_id x). have e':=FU_id y.
apply (pcm_respect e e' M).
Qed.

Lemma Unfold_antinonexp n (w w':W) : Unfold w = n = Unfold w' -> w = n = w'.
move => X. have Y:=fnonexpansive Fold X. clear X.
apply (Mrel_trans (Msym (proj2 (Mrefl _ _) (FU_id w) n))).
refine (Mrel_trans _ (proj2 (Mrefl _ _) (FU_id w') n)). by apply Y.
Qed.

Lemma Fold_antinonexp n w w' : Fold w = n = Fold w' -> w = n = w'.
move => X. have Y:=fnonexpansive Unfold X. clear X.
apply (Mrel_trans (Msym (proj2 (Mrefl _ _) (UF_id w) n))).
refine (Mrel_trans _ (proj2 (Mrefl _ _) (UF_id w') n)). by apply Y.
Qed.

Lemma less_nil j (P:j < 0) : False.
move: P ; by rewrite ltn0.
Qed.

(*=TV *)
Definition TV := halve_pcmType W -=> upred_pcmType CValue.
Fixpoint TVal (n:nat) : cmetricType :=
match n with | O => One | S n => TVal n * TV end.

Fixpoint pick n (j : Fin n) : cmetricCatType (TVal n) TV :=
  match j with 
  | FinZ _   => pi2
  | FinS _ v => pick v << pi1
  end.
(*=End *)
  
Lemma upred_prod_down (X : upred_metricType CValue * upred_metricType CValue) :
   downclosed (fun kt => let v := snd kt in
                             match v with 
                             | Tm.PAIR v0 v1 => (fst X) (fst kt, v0) /\ (snd X) (fst kt, v1)
                             | _ => False 
                             end).
move => k k'. case => v L; try by []. simpl. 
move => P [A B]. 
split ; first by apply (upred_downclosed (ltnW P) A). by apply (upred_downclosed (ltnW P) B).
Qed.

Open Scope C_scope.
Open Scope M_scope.

Definition upred_prod (p : (upred_cmetricType CValue) * (upred_cmetricType CValue) %CAT)
  : upred_cmetricType CValue := Eval hnf in mk_upred (@upred_prod_down p).

Lemma upred_product_ne : nonexpansive upred_prod.
move => n.
case => x0 x1. case => y0 y1. case => e0 e1.
move => k v L. case v ; try by [].
move => v0 v1.
specialize (e0 k). 
specialize (e1 k). simpl in e0,e1. simpl. rewrite e0. by rewrite e1. by []. 
Qed.

Definition upred_productN : metricCatType (upred_pcmType CValue * upred_pcmType CValue) (upred_pcmType CValue) := Eval hnf in mk_fmet upred_product_ne.

Lemma upred_product_mono : monotonic upred_productN.
case => x0 x1. case => y0 y1. case => e0 e1. case => k. case; try by [].
move => v0 v1. specialize (e0 (k,v0)). 
specialize (e1 (k,v1)). move => [A B]. split ; by [apply e0 | apply e1].
Qed.

Definition upred_product : upred_pcmType CValue * upred_pcmType CValue =-> upred_pcmType CValue :=
  Eval hnf in mk_fpcm upred_product_mono.

Add Parametric Morphism : @upred_product
with signature (@tset_eq ((upred_pcmType CValue * upred_pcmType CValue)%CAT)) ==> (@tset_eq (upred_pcmType CValue))
as upred_product_eq_compat.
case => x y. case => x' y'. case => e0 e1. case => k v. simpl. case: v; try done.
move => v0 v1. simpl in e1,e0. specialize (e0 (k,v0)). 
specialize (e1 (k,v1)). rewrite e0. by rewrite e1.
Qed.

Lemma upred_sumP (X:upred_cmetricType CValue * upred_cmetricType CValue) :
  downclosed (fun kt => let v := snd kt:CValue in 
                             match v with
                               | Tm.INL p0 => (fst X) (fst kt, p0)
                               | Tm.INR p0 => (snd X) (fst kt, p0)
                               | _ => False end).
move => k k'. case => v L; simpl; try by []; move => A; apply (upred_downclosed (ltnW L) A).
Qed.

Definition upred_sumt (p:upred_cmetricType CValue * upred_cmetricType CValue) : upred_cmetricType CValue :=
  Eval hnf in mk_upred (@upred_sumP p).

Lemma upred_sum_ne : nonexpansive upred_sumt.
move => n.
case => x0 x1. case => y0 y1. case => e0 e1.
move => k. case => v; simpl; try by [].
- move => L; by rewrite (e0 k v L). 
- move => L. by rewrite (e1 k v L).
Qed.

Definition upred_sumN : metricCatType (upred_pcmType CValue * upred_pcmType CValue) (upred_pcmType CValue) := Eval hnf in mk_fmet upred_sum_ne.

Lemma upred_sum_mono : monotonic upred_sumN.
case => x0 x1. case => y0 y1. case => e0 e1. move => [k v]. destruct v; simpl; try by []. 
- move => H. by apply (e0 (k,v)).
- move => H. by apply (e1 (k,v)).
Qed.

Definition upred_sum : (upred_pcmType CValue * upred_pcmType CValue =-> upred_pcmType CValue) := 
  Eval hnf in mk_fpcm upred_sum_mono.

Add Parametric Morphism : @upred_sum
with signature (@tset_eq ((upred_pcmType CValue * upred_pcmType CValue)%CAT)) ==> (@tset_eq (upred_pcmType CValue))
as upred_sum_eq_compat.
case => x y. case => x' y'. case => e0 e1. move => [k v]. destruct v; simpl; try by []. 
Qed.

(*=upred_mu_down *)
Lemma upred_mu_down n 
   (R: TVal n.+1 =-> halve_pcmType W -=> upred_pcmType CValue) (s:TVal n)
   (P:(halve_pcmType W =-> upred_pcmType CValue) * halve_pcmType W) :
downclosed (fun kt => let: v' := snd kt in
  match fst kt, v' with
 | O,Tm.FOLD v => True
 | S k,Tm.FOLD v => (R ((s,(fst P))) (snd P)) (k,v)
 | _,_ => False
  end).
(*=End *)
case ; first by []. move => m k v. destruct v; simpl; try done. 
move => L. destruct k; first by []. 
refine (upred_downclosed _). by apply (ssrnat.ltn_trans (ltnSn k) L).
Qed.

(*=upred_mut *)
Definition upred_mut n R s w : upred_pcmType CValue := 
  Eval hnf in mk_upred (@upred_mu_down n R s w).
(*=End *)

Definition ne_mono (M:cmetricType) (P Q:pcmType) (f:M * P -> Q) :=
   (nonexpansive f) /\ forall m, monotonic (fun x => f (m,x)).

Lemma ne_mono_ne2 (M:cmetricType) (P Q:pcmType) (f:M * P -> Q) (X:ne_mono f) (m:M) : nonexpansive (fun x : P => f (m, x)).
move => n x x' e. simpl. by apply (proj1 X).
Qed.

Definition ne_monoN M P Q f (X:@ne_mono M P Q f) (m:M) : P =-> Q := Eval hnf in mk_fpcmX (ne_mono_ne2 X m) ((proj2 X) m).

Lemma mk_nemon_ne M P Q f (X:@ne_mono M P Q f) : nonexpansive (ne_monoN X).
move => n m m' e x. simpl. by apply ((proj1 X)).
Qed.

Definition mk_nemon M P Q f (X:@ne_mono M P Q f) : M =-> (P -=> Q) := Eval hnf in mk_fmet (mk_nemon_ne X).

(*upred_muS *)
Lemma upred_mu_ne n R s : ne_mono (@upred_mut n R s). 
(*=End *)
Proof.
split.
- move => m. case => f w. case => f' w'. case. case:m ; first by [].
  move => m e e' k. simpl. case => v; try done.
  simpl. have d:(R (s, f)) = m.+1 = (R (s, f')) by apply fnonexpansive.
  specialize (d w). have dd:=fnonexpansive ( (R (s, f'))) e'.
  case: k ; first by []. move => k L. apply ((Mrel_trans d dd) k v). by apply (ssrnat.ltn_trans (ltnSn k) L).
- move => f. simpl in f. move => w w' L. case => k. case; simpl; try done.
  move => v. case: k; first by []. move => k. simpl in w,w'.
  have e:(R (s, f)) w <= (R (s, f)) w' by apply: fmonotonic.
  by apply (e _).
Qed.

Definition upred_mup n (R:TVal n.+1 =-> halve_pcmType W -=> upred_pcmType CValue) (s:TVal n) :
   cmetricCatType (halve_pcmType W -=> upred_pcmType CValue) (halve_pcmType W -=> (upred_pcmType CValue)) :=
   Eval hnf in mk_nemon (upred_mu_ne R s).

Lemma upred_muC n R (s:TVal n) : contractive (upred_mup R s).
move => m. move => f g e.
move => w. simpl. move => k. case ; try done. case: k ; first by []. move => k v L.
have d:(R (s, f)) = m = (R (s, g)) by apply fnonexpansive.
apply: d. by apply L.
Qed.

Definition upred_muc n (R: TVal n.+1 =-> halve_pcmType W -=> upred_pcmType CValue) (s:TVal n) : 
  morphc_pcmType (halve_pcmType W -=> upred_pcmType CValue) (halve_pcmType W -=> upred_pcmType CValue) :=
exist _ (upred_mup R s) (upred_muC R s).

Lemma upred_mun n R : nonexpansive (@upred_muc n R).
move => m s s' e f w. case: m e ; first by []. move => m e k. simpl.
case ; try done. move => v. case: k ; first by []. move => k L.
simpl. have d:(R (s, f)) = m.+1 = (R (s', f)) by apply fnonexpansive.
apply (d w k _). by apply (ssrnat.ltn_trans (ltnSn k) L).
Qed.

(*=upred_mu *)
Definition upred_mu n (R: TVal n.+1 =-> halve_pcmType W -=> upred_pcmType CValue) :
   TVal n =-> morphc_pcmType TV TV := 
    Eval hnf in mk_fmet (@upred_mun n R).
(*=End *)

Definition bool_option (b:bool) : b + not b.
case: b. by left.
by right.
Defined.

(*=heap_world *)
Definition heap_world k (h:Heap) (w:W) := 
    forall j, j < k -> dom h =i dom (Unfold w) /\
    forall l,  match Unfold w l, h l with Some w',Some v' => w' w (j,v')
                     | _,_ => True end.
(*=End *)
(*=IExp *)
Definition IExp (f:TV) (k:nat) (e:Tm.Exp 0) (w:W) :=
   forall j, (j <= k)%N -> 
   forall (h h':Heap) v (D:EV j e h v h'), heap_world k h w ->
    exists w':W, w <= w' /\ heap_world (k - j) h' w' /\ (f w') (k-j,v).
(*=End *)
Lemma IExp_respect (f f':TV) (k:nat) (e:Tm.Exp 0) (w:W) : f =-= f' -> IExp f k e w =-= IExp f' k e w.
move => E. unfold IExp. split.
- move => X j L h h' v ev hv. specialize (X j L h h' v ev hv). case: X => w' [LL [HV Y]].
  exists w'. split ; first by []. split ; first by []. specialize (E w'). simpl in E.
  specialize (E (k - j, v)). rewrite <- E. by apply Y.
- move => X j L h h' v ev hv. specialize (X j L h h' v ev hv). case: X => w' [LL [HV Y]].
  exists w'. split ; first by []. split ; first by []. specialize (E w' (k-j,v)). simpl in E.
  rewrite E. by apply Y. 
Qed.

Lemma upred_all_down n (R:TVal n.+1 =-> halve_pcmType W -=> upred_pcmType CValue)
  (s:TVal n * halve_pcmType W) : downclosed (fun kt => let: (k,v) := kt in
   match v with
    | Tm.TLAM v => forall (r:TV) (w':W) j, (j <= k)%N -> snd s <= w' ->
             (IExp (R (fst s,r)) j v w')
    | _ => False
   end).
move => m k v L. simpl. case: v; try done. case: s => e w.
move => E X r w' j L'. simpl. move => LL. simpl in X. apply X. by apply (leqW (leq_ltn_trans L' L)). by apply LL.
Qed.

Definition upred_allt n R s : upred_pcmType CValue := mk_upred (@upred_all_down n R s).

Require Import ssrfun.
Lemma world_extend n (w0 w1 v0 : W) : w0 = n = v0 -> w0 <= w1 -> exists v1:W, w1 = n = v1 /\ v0 <= v1.
case: n w0 w1 v0. move => w0 w1 v0 _ L. by exists v0.
move => n w0 w1 v0 e l.
exists (Fold (create_findomF (Unfold w1) (fun x => match Unfold v0 x with | None => Unfold w1 x | Some v => Some v end))). 
have e':=fnonexpansive ( Unfold) e. clear e. split.
- have A:=proj1 e'. have B:=proj2 e'. clear e'.
apply Unfold_antinonexp.
refine (Mrel_trans _ (proj2 (Mrefl _ _) (tset_sym (UF_id _)) _)).
split.
  + move => i. rewrite dom_create_findomF. rewrite in_filter.
    specialize (A i). case: (Unfold v0 i). simpl. by rewrite andbT.
    rewrite findom_indom. by case: (Unfold w1 i).
  + move => i I I'. specialize (B i). rewrite create_findomF_simpl. do 2 rewrite findom_indom in B.
    move: B. case_eq (Unfold v0 i).
    * move => s U. rewrite U. simpl. move => X.
      specialize (A i). do 2 rewrite findom_indom in A. rewrite U in A. rewrite A in X.
      specialize (X is_true_true is_true_true). clear A. rewrite I. rewrite <- X.
      have ll:=fmonotonic Unfold l. clear l. specialize (ll i).
      case: (Unfold w0 i) X ll ; last by []. move => w0i e X. specialize (X _ (refl_equal _)). case: X => m [e0 e1].
      rewrite e0. apply Msym. by apply: (proj2 (Mrefl _ _) e1 _).
    * move => e _. specialize (A i). do 2 rewrite findom_indom in A. rewrite e in A. simpl in A.
      rewrite findom_indom. by case: (Unfold w1 i).
- apply Unfold_monic.
  refine (@pcm_respect _ _ _ _ _ (tset_refl _) (tset_sym (UF_id _)) _).
  move => i f E. have ll:=fmonotonic Unfold l. specialize (ll i). clear l.
  have A:=proj2 e' i. do 2 rewrite findom_indom in A. rewrite E in A.
  rewrite create_findomF_simpl. rewrite E. exists f. split ; last by [].
  have e0:=proj1 e' i. do 2 rewrite -> findom_indom in e0. rewrite E in e0.
  rewrite e0 in A. specialize (A is_true_true is_true_true). case: (Unfold w0 i) A ll ; last by [].
  move => w0i A ll. specialize (ll w0i (refl_equal _)). case: ll => w1i [P Q].
  rewrite findom_indom. by rewrite P.
Qed.

Lemma heap_world0 w h : heap_world 0 h w.
by [].
Qed.

Hint Resolve heap_world0.

Lemma heap_world_eq m h w w' j : (j <= m)%N -> w = m = w' -> heap_world j h w -> heap_world j h w'.
case:m h w w' j ; first by move => h w w' j L E _ ; rewrite leqn0 in L ; rewrite (eqP L).
move => m h w w'. case ; first by [].
move => j L E. move => X k l. specialize (X k l). case: X => D X.
have E':=fnonexpansive Unfold E. case: E' => D' E'.
split ; first by move => i ; rewrite -> D ; apply D'.
move => i. specialize (X i). case_eq (Unfold w' i) ; last by [].
move => wi' e'. specialize (D' i). do 2 rewrite findom_indom in D'. rewrite e' in D'.
specialize (E' i). do 2 rewrite findom_indom in E'. rewrite e' in E'. rewrite D' in E'.
specialize (E' is_true_true is_true_true). clear D'. case: (Unfold w i) X E' ; last by [].
move => wi. case: (h i) ; last by []. move => v A X. specialize (X w'). simpl in X.
have Y:=fnonexpansive wi. specialize (Y m.+2 w w' E). rewrite <- (Mmono Y) in X.
specialize (X k v). specialize (X (leq_trans l L)). by rewrite <- X.
Qed.

Lemma upred_allN n R : ne_mono (@upred_allt n R).
split.
- move => m.
  case => x0 x1. case => y0 y1. case:m ; first by [].
  move => m. case => e e'. move => k. case ; try done.
  move => ee Lk. split.
  + move => A r w j Lj. specialize (A r). move => Lw i Li h h' v ev hv.
    simpl in e'. destruct (world_extend (Msym e') Lw) as [w' [X L']].
    specialize (A w' j Lj L' i Li). specialize (A h h' v ev).
    have hv':= heap_world_eq (leq_trans Lj Lk) X hv.
    specialize (A hv'). destruct A as [w0 [lw0 [hv0 A]]].
    destruct (world_extend (Msym X) lw0) as [w1 [E1 L1]]. exists w1. split ; first by [].
    split ; first by apply: (heap_world_eq (leq_trans (leq_subr _ _) (leq_trans Lj Lk)) E1 hv0).
    have EE:(R ((x0, r))) = m.+1 = R ((y0, r)) by apply fnonexpansive.
      specialize (EE w0). have e0:R ((y0, r)) w0 = m.+1 = R ((y0, r)) w1. apply: fnonexpansive. by apply E1.
    have e1:=Mrel_trans EE e0. clear EE e0.
    specialize (e1 (j-i) v). 
    specialize (e1 (leq_trans (leq_subr _ _) (leq_trans Lj Lk))). by rewrite <- e1.
  + move => A r w j Lj. specialize (A r). move => Lw i Li h h' v ev hv.
    simpl in e'. destruct (world_extend e' Lw) as [w' [X L']].
    specialize (A w' j Lj L' i Li). specialize (A h h' v ev).
    have hv':= heap_world_eq (leq_trans Lj Lk) X hv.
    specialize (A hv'). destruct A as [w0 [lw0 [hv0 A]]].
    destruct (world_extend (Msym X) lw0) as [w1 [E1 L1]]. exists w1. split ; first by [].
    split ; first by apply: (heap_world_eq (leq_trans (leq_subr _ _) (leq_trans Lj Lk)) E1 hv0).
    have EE:(R ((x0, r))) = m.+1 = R ((y0, r)) by apply fnonexpansive. specialize (EE w1).
    have e0:R (y0, r) w1 = m.+1 = R (y0, r) w0 by apply: fnonexpansive ; apply (Msym E1).
    have e1:=Mrel_trans EE e0. clear EE e0.
    specialize (e1 (j-i) v (leq_trans (leq_subr _ _) (leq_trans Lj Lk))). by rewrite e1.
- move => s w w' L. case => k v. simpl. case: v ; try done.
  move => v X f we' j Lj Lw'. specialize (X f we' j Lj (Ole_trans L Lw')).
  move => i Li h h' v' ev hv. specialize (X i Li h h' v' ev hv).
  destruct X as [we [Lw [hv' X]]]. exists we. split ; first by []. split ; first by []. by apply X.
Qed.

Definition upred_all n (R : TVal n.+1 =-> halve_pcmType W -=> upred_pcmType CValue) :
      (TVal n) =-> (halve_pcmType W -=> upred_pcmType CValue) := 
  Eval hnf in mk_nemon (upred_allN R).

(*=upred_ref_down *)
Lemma upred_ref_down n 
 (R : TVal n =-> halve_pcmType W -=> upred_pcmType CValue)
 (s:TVal n) (w: halve_pcmType W) :
(*=End *)
   downclosed (fun kt => let: (k,v) := kt in
    match k,(v:Tm.Value O) with
     | O,Tm.LOC l => True
     | S k,Tm.LOC l => Unfold w l = k.+1 = Some (R s)
     | _,_ => False
    end).
move => m k v L. case: m L ; first by []. move => m L. case v ; try done.
move => l P. case: k L ; first by []. move => k L. by apply (Mrel_mono (ltnW L)).
Qed.

(*=upred_reft *)
Definition upred_reft n R w : upred_pcmType CValue := 
  mk_upred (@upred_ref_down n R (fst w) (snd w)).
(*=End *)

Lemma upred_refN n R : ne_mono (@upred_reft n R).
split.
- move => m.
  case => s w. case => s' w'. case: m ; first by []. move => m. case => e e'. move => k v.
  case: k ; first by []. move => k.
  case: v; try done. move => l. have X:=fnonexpansive Unfold e'. clear e'.
  simpl in e. simpl in X. case: m e X ; first by []. move => m e X L. simpl.
  have e0:=proj2 X l. have e1:=fnonexpansive R e. clear e. rewrite <- (proj1 X) in e0.
  rewrite findom_indom in e0. move: (proj1 X l). do 2 rewrite findom_indom.
  case: (Unfold w l) e0 ; last by simpl ; case: (Unfold w' l).
  move => wl. simpl. move => Y. specialize (Y is_true_true is_true_true).
  unfold Mrel. simpl. clear X. case: (Unfold w' l) Y ; last by [].
  move => wl' Y _. unfold Mrel in Y. simpl in Y. rewrite -> (@Mrel_mono _ _ _ k.+1 m.+1 L Y).
  by rewrite -> (@Mrel_mono _ _ _ k.+1 m.+1 L (Mmono e1)).
- move => s. move => w w' Lw. simpl. case => k v. simpl. case: k ; first by []. case: v ; try done.
  move => l k. have L:=fmonotonic Unfold Lw. clear Lw. specialize (L l).
  case: (Unfold w l) L ; last by []. move => wl L. specialize (L wl (refl_equal _)).
  case: L => wl' [e e']. rewrite e. unfold Mrel ; simpl. move => A. rewrite <- A. apply Msym.
  by apply (proj2 (Mrefl _ _) e' k.+1).
Qed.


(*=upred_ref *)
Definition upred_ref n
     (R : TVal n =-> halve_pcmType W -=> upred_pcmType CValue) :
     (TVal n) =-> (halve_pcmType W -=> upred_pcmType CValue) :=
     Eval hnf in mk_nemon (upred_refN R).
(*=End *)

(*=upred_int_down *)
Lemma upred_int_down :
  downclosed (fun kt => match snd kt : Tm.Value O with 
                       | Tm.INT i => True | _ => False end). (*CLEAR*) 
move => k m v l. simpl. by case: v.
Qed.

(*CLEARED*) 
Definition upred_int : upred_pcmType CValue := Eval hnf in mk_upred upred_int_down.
(*=End *)

Lemma upred_unit_down : downclosed (fun kt => match snd kt : Tm.Value O with | Tm.UNIT => True | _ => False end).
move => k m v l. simpl. by case: v.
Qed.

Definition upred_unit : upred_pcmType CValue := Eval hnf in mk_upred upred_unit_down.

(*=upred_arrow_down *)
Lemma upred_arrow_down n
  (R0 R1: TVal n =-> halve_pcmType W -=> upred_pcmType CValue)
  (s:TVal n) (w: halve_pcmType W) : downclosed (fun kt => let: (k,v) := kt in
   match v with
   | Tm.LAM e => forall w' j (va:Tm.Value O), w <= w' -> (j <= k)%N -> 
              (R0 s w') (j,va) -> IExp (R1 s) j (Tm.subExp (cons va (@Tm.idSub _)) e) w'
   | _ => False end).
(*=End *)
move => m k. simpl. case ; try done. move => e L X.
move => w' j va Lw Lj. by apply (X w' j va Lw (ssrnat.leq_trans Lj (leqW L))).
Qed.

(*=upred_arrowt *)
Definition upred_arrowt n R0 R1 s w : upred_pcmType CValue := 
  Eval hnf in mk_upred (@upred_arrow_down n R0 R1 s w).
(*=End *)

Lemma IExp_nonexp m (f f':TV) (k:nat) (e:Tm.Exp 0) (w w':halve_cmetricType W) : f = m = f' -> w = m = w' -> k < m -> IExp f k e w =-= IExp f' k e w'.
move => E Ew l. unfold IExp. case: m E Ew l ; first by []. move => m E Ew l. split.
- move => X j L h h' v ev hv. specialize (X j L h h' v ev).
  have hv':=heap_world_eq _ (Msym Ew) hv. specialize (X (hv' l)). destruct X as [w0 [LL [HV Y]]].
  case: (world_extend Ew LL) => w0' [Ew' LL']. exists w0'. split ; first by [].
  split ; first by apply: (heap_world_eq (ssrnat.leq_trans (leq_subr _ _) _) Ew').
  specialize (E w0). simpl in E.
  have E':f w0 = m.+1 = f' w0' by apply Mrel_trans with (y:=f' w0) ; [by apply E | apply: fnonexpansive].
  specialize (E' (k - j) (v)).
  specialize (E' (leq_ltn_trans (leq_subr j k) l)). rewrite <- E'. by apply Y.
- move => X j L h h' v ev hv. specialize (X j L h h' v ev).
  have hv':=heap_world_eq _ Ew hv. specialize (X (hv' l)). destruct X as [w0 [LL [HV Y]]].
  case: (world_extend (Msym Ew) LL) => w0' [Ew' LL']. exists w0'. split ; first by [].
  split ; first by apply: (heap_world_eq (ssrnat.leq_trans (leq_subr _ _) _) Ew').
  have E':f w0' = m.+1 = f' w0 by apply Mrel_trans with (y:=f' w0') ; [by apply E | apply: fnonexpansive ; apply (Msym Ew')].
  specialize (E' (k - j) v). 
  specialize (E' (leq_ltn_trans (leq_subr j k) l)). rewrite -> E'. by apply Y.
Qed.

Lemma upred_arrowN n R : ne_mono (fun a => @upred_arrowt n (fst R) (snd R) (fst a) (snd a)).
split.
- case: R => R0 R1 m x y E. case: m E ; first by []. move => m E. move => k v. simpl. case: v ; try done.
  move => e.
  move => Lk. split ; move => B w' j va lw Lj T I.
  + have E':=proj2 E. simpl in E'. case: (world_extend (Msym E') lw) => x' [E0 L0]. specialize (B x' j va L0 Lj).
    apply (proj1 (IExp_nonexp (Tm.subExp (cons va _) e) (Mrel_refl m.+1 (R1 y.1)) (Msym E0) (ssrnat.leq_trans Lj Lk))).
    have e2:(R1 x.1) = m.+1 = (R1 y.1) by apply: (fnonexpansive R1) ; apply (proj1 E).
    apply (IExp_nonexp _ e2 (Mrel_refl _ x')). by apply (leq_ltn_trans Lj Lk). apply B.
    have E1:R0 x.1 = m.+1 = R0 y.1 by apply fnonexpansive ; apply (proj1 E).
    specialize (E1 x'). have E1':=fnonexpansive ((R0 y.1)). specialize (E1' m.+1 x' w'  (Msym E0)).
    have E2:=Mrel_trans E1 E1'. clear E1 E1'. specialize (E2 j va (leq_ltn_trans Lj Lk)). by rewrite E2.
  + have E':=proj2 E. simpl in E'. case: (world_extend E' lw) => x' [E0 L0]. specialize (B x' j va L0 Lj).
    apply (proj2 (IExp_nonexp (Tm.subExp (cons va _) e) (Mrel_refl m.+1 (R1 x.1)) (E0) (ssrnat.leq_trans Lj Lk))).
    have e2:(R1 x.1) = m.+1 = (R1 y.1) by apply: (fnonexpansive R1) ; apply (proj1 E).
    apply (IExp_nonexp _ e2 (Mrel_refl _ x')). by apply (leq_ltn_trans Lj Lk). apply B.
    have E1:R0 y.1 = m.+1 = R0 x.1 by apply fnonexpansive ; apply (Msym E). specialize (E1 x').
    have E1':R0 x.1 x' = m.+1 = R0 x.1 w' by apply (fnonexpansive (R0 x.1)) ; apply (Msym E0).
    have E2:=Mrel_trans E1 E1'. clear E1 E1'. specialize (E2 j va (leq_ltn_trans Lj Lk)). by rewrite E2.
- case: R => R0 R1. move => s w w' Lw. case => k v. simpl. case: v; try done. move => e0 X w1 j va Lw1 Lj.
  by apply (X w1 j va (Ole_trans Lw Lw1) Lj).
Qed. 

(*=upred_arrow *)
Definition upred_arrow n 
   (R0 R1:TVal n =-> halve_pcmType W -=> upred_pcmType CValue) :
   cmetricCatType (TVal n) (halve_pcmType W -=> upred_pcmType CValue) :=
   Eval hnf in mk_nemon (upred_arrowN (R0,R1)).
(*=End *)

Add Parametric Morphism n : (@upred_arrow n)
with signature (@tset_eq ((metricCatType (TVal n) TV))) ==> 
               (@tset_eq ((metricCatType (TVal n) TV))) ==>
               (@tset_eq ((metricCatType (TVal n) TV)))
as upred_arrow_eq_compat.
move => x x' e y y' e'. move => s w. case => k. simpl. case ; try done.
move => ee. split ; move => X w' j va Lw Lj ; specialize (X w' j va Lw Lj).
- move => Y. apply: (proj1 (IExp_respect _ _ _ _) (X _)) ; first by move => w0 ; apply: e'.
  specialize (e s w' (j,va)). by rewrite e.
- move => Y. apply: (proj2 (IExp_respect _ _ _ _) (X _)) ; first by move => w0 ; apply: e'.
  specialize (e s w' (j,va)). by rewrite <- e.
Qed.

Fixpoint Prod (T:Type) n : Type :=
match n with
| O => unit
| S n => (Prod T n * T)%type
end.

Lemma Prod_constP n T (p:(upred_pcmType (Prod T n) * upred_pcmType T)) :
  downclosed (fun kt => fst p (fst kt,fst (snd kt)) /\ snd p (fst kt,snd (snd kt))).
case:p => A B.
move => m k. simpl. case => te t l. simpl. move => [C D].
by split ; [apply (upred_downclosed (ltnW l) C) | apply (upred_downclosed (ltnW l) D)].
Qed.

Definition Prod_const n T (p:(upred_pcmType (Prod T n) * upred_pcmType T)%CAT) : upred_pcmType (Prod T n.+1) :=
  Eval hnf in mk_upred (@Prod_constP n T p).


Lemma Prod_consN n T : nonexpansive (@Prod_const n T).
move => m. case => x y. case => x' y'. case: m ; first by [].
move => m. case => e0 e1. move => k. simpl. case => te t l. simpl.
specialize (e0 k te l). specialize (e1 k t l). rewrite e0. by rewrite e1.
Qed.

Lemma Prod_consM n T : monotonic (mk_fmet (@Prod_consN n T)).
case => x t. case => x' t'. case => e0 e1. case => k v. simpl. simpl in v. case: v => vt v.
specialize (e0 (k,vt)). specialize (e1 (k,v)). by move => [A B] ; split ; [apply e0 | apply e1].
Qed.

Definition Prod_cons n T : upred_pcmType (Prod T n) * upred_pcmType T =-> upred_pcmType (Prod T n.+1) :=
  Eval hnf in mk_fpcm (@Prod_consM n T).

Implicit Arguments Prod_cons [n T].

(*=IVal *)
Import Ty.
Fixpoint IVal n (t:Ty.Ty n) : cmetricCatType (TVal n) TV :=
match t with
| TVar J => pick J
| Int => mconst _ (pconst _ upred_int)
| Unit => mconst _ (pconst _ upred_unit)
| Mu t => FIXP << upred_mu (IVal t)
| t ** t' => (exp_fun Pcomp upred_product : metricCatType _ _) << pprod_fun_ne
                                                      << <|IVal t,IVal t'|>
| Sum t t' => (exp_fun Pcomp upred_sum : metricCatType _ _) << Pprod_fun
                                                      << <|IVal t, IVal t'|>
| All t => upred_all (IVal t)
| t --> t' => upred_arrow (IVal t) (IVal t')
| Ref t => upred_ref (IVal t)
end.
(*=End *)

(*=IEnv *)
Fixpoint IEnv E n :
  TEnv E n -> TVal E =-> halve_pcmType W -=> upred_pcmType (Prod CValue n)  :=
  match n with 
  | 0 => fun env => mconst _ (pconst _ (upred_empty unit))
  | n.+1 => fun env => (pcompM _ _ _ << ppair _ Prod_cons << Pprod_fun) << 
                                          <| IEnv (tl env),  (IVal (hd env)) |>
end.
(*=End *)

(*=IStore *)
Lemma IStore_down E (Se:StoreType E) (s:TVal E) : 
  downclosed (fun kt => forall l t, Se l = t ->
                        (IVal (Ref t) s (snd kt)) (fst kt, Tm.LOC l)). (*CLEAR*)
move => m k w Lk. move => X.
move => l t E'. specialize (X l t E').
by apply (upred_downclosed (ltnW Lk) X).
Qed.
(*CLEARED*)
Definition IStore E (Se:StoreType E) (s:TVal E) : upred_pcmType W :=
    Eval hnf in mk_upred (@IStore_down E Se s).
(*=End *)

Definition emptyMap T : FMap 0 T. intros var. Require Import Program. dependent destruction var. Defined.
Fixpoint Prod_subst T n : Prod T n -> FMap n T :=
match n with
| O => fun _ => emptyMap T
| S n => fun P => cons (snd P) (Prod_subst (fst P))
end.

(*=VRel *)
Definition VRel E n (env:TEnv E n) (Se:StoreType E) (v:Tm.Value n) (t:Ty.Ty E) := 
  forall k (s:TVal E) g w,
  (IEnv env s w) (k,g) -> (IStore Se s) (k,w) ->
  (IVal t s w) (k, Tm.subVal (Prod_subst g) v).

Definition ERel E n (env:TEnv E n) (Se:StoreType E) (e:Tm.Exp n) (t:Ty.Ty E) :=
  forall k (s:TVal E) g w,
     (IEnv env s w) (k,g) -> (IStore Se s) (k,w) ->
     IExp (IVal t s) k (Tm.subExp (Prod_subst g) e) w.
(*=End *)

Lemma FT_var E n m (env:TEnv E n) s w k g : (IEnv env s w) (k, g) -> IVal (env m) s w (k,nth m (Prod_subst g)).
Proof.
dependent induction m.
- simpl. by case => A B ; apply B.
- simpl. case => A B. rewrite tlCons. by apply (IHm (tl env)).
Qed.

Lemma IVal_mapTy P (ops:Map.Ops P) n (t:Ty n) s m s' (a:FMap n (P m)) :
     (forall n (t:P n) s s', IVal (Map.vl ops t) s' =-= IVal (Map.vl ops (Map.wk ops t)) (s', s)) ->
     (forall i, pick i s =-= (@IVal m (Map.vl ops (a i)) s')) -> 
                          IVal t s =-= IVal (Map.mapTy ops a t) s'.
move => Y. elim: n / t s m s' a.
- simpl. move => e i s m s' a X. by apply X.
- by [].
- by [].
- move => E t IH t' IH' s m s' a X. simpl. specialize (IH s m s' a X). specialize (IH' s m s' a X).
  move => aa. simpl. specialize (IH aa). specialize (IH' aa). simpl in IH. simpl in IH'.
  by apply (frespect upred_product (pair_eq_compat IH IH')).
- move => E t IH t' IH' s m s' a X. simpl. specialize (IH s m s' a X). specialize (IH' s m s' a X).
  move => aa. simpl. specialize (IH aa). specialize (IH' aa). simpl in IH. simpl in IH'.
  by apply (frespect upred_sum (pair_eq_compat IH IH')).
- move => E t IH s m s' a X. simpl. apply: frespect. move => ss. simpl. move => bb. simpl. case => k v. simpl.
  case: k ; first by []. case: v ; try done. move => v n.
  specialize (IH (s,ss) m.+1 (s',ss)). specialize (IH (Map.lift ops a)).
  apply IH. move => i. clear IH. move: Y X. clear. move => Y X. rewrite Map.liftAsCons.
  dependent destruction i ; simpl ; first by rewrite Map.vlvr. unfold Map.shift. rewrite -> (X i).
  by apply Y.
- move => E t IH s m s' a X. simpl. move => w. simpl. case => k v. case: v ; try done.
  move => e. simpl. split.
  + move => A r w' j Lj Lw. specialize (IH (s,r) m.+1 (s',r) (Map.lift ops a)).
    specialize (A r w' j Lj Lw). apply: (proj1 (IExp_respect _ _ _ (IH _)) A).
    move => i. dependent destruction i ; simpl ; first by rewrite Map.vlvr.
    rewrite -> (X i). by apply Y.
  + move => A r w' j Lj Lw. specialize (IH (s,r) m.+1 (s',r) (Map.lift ops a)).
    specialize (A r w' j Lj Lw). apply: (proj2 (IExp_respect _ _ _ (IH _)) A).
    move => i. dependent destruction i ; simpl ; first by rewrite Map.vlvr.
    rewrite -> (X i). by apply Y.
- move => E t IH t' IH' s m s' a X w. simpl. case => k v. simpl. case: v ; try done.
  move => e. split.
  + move => A w' j v Lw Lj Iv. specialize (A w' j v Lw Lj).
    specialize (IH s m s' a X w' (j,v)).  rewrite <- IH in Iv. simpl in Iv. specialize (A Iv).
    specialize (IH' s m s' a X). by apply(proj1 (IExp_respect _ _ _ IH') A).
  + move => A w' j v Lw Lj Iv. specialize (A w' j v Lw Lj).
    specialize (IH s m s' a X w' (j,v)).  rewrite -> IH in Iv. simpl in Iv. specialize (A Iv).
    specialize (IH' s m s' a X). by apply(proj2 (IExp_respect _ _ _ IH') A).
- move => E t IH s m s' a X w. simpl. case => k v. simpl. case: k ; first by [].
  case: v ; try done. move => l k. specialize (IH s m s' a X). split.
  + move => A. rewrite -> A. by apply: (proj2 (Mrefl _ _) IH).
  + move => A. rewrite -> A. by apply: (proj2 (Mrefl _ _) (tset_sym IH)).
Qed.

Lemma IVal_shiftTy n (t:Ty n) s s' : IVal t s =-= IVal (shiftTy t) (s,s').
by apply IVal_mapTy.
Qed.

(*=IValSubst *)
Lemma IVal_substTy n (t:Ty n) s m s' a :
     (forall i, pick i s =-= (@IVal m (a i) s')) -> IVal t s =-= IVal (subTy a t) s'.
(*=End *) 
move => X. apply IVal_mapTy ; simpl ; last by [].
clear. move => n t s s'. by apply: IVal_shiftTy.
Qed.

Lemma IEnv_shiftTy E n (env:TEnv E n) (s:TVal E) w r : 
  IEnv (fun v : Fin n => shiftTy (env v)) (s, r) w =-= IEnv env s w.
dependent induction n ; first by [].
simpl. specialize (IHn (tl env) s w r).
case => k. case => p v. simpl. split.
- case => A B. split ; first by apply (proj1 (IHn (k,p)) A).
  have X:=IVal_shiftTy (hd env) s r w (k,v). rewrite X. by apply B.
- case => A B. split ; first by apply (proj2 (IHn (k,p)) A).
  have X:=IVal_shiftTy (hd env) s r w (k,v). rewrite <- X. by apply B.
Qed.

Lemma heap_world_down j k h w : j <= k -> heap_world k h w -> heap_world j h w.
move => L X i Li. specialize (X i (ssrnat.leq_trans Li L)). split ; case: X ; move => X Y ; first by apply X.
move => l. specialize (Y l). by apply Y.
Qed.

Lemma IStore_upclosed n t (s:TVal n) j w w' : w <= w' -> (IStore t s) (j,w) -> (IStore t s) (j,w').
move => L. unfold IStore. simpl. move => X l t' E. specialize (X l t' E).
case: j X ; first by []. move => j. have ll:=fmonotonic Unfold L. clear L.
move => A. rewrite <- A. specialize (ll l). case: (Unfold w l) ll A ; last by [].
move => wl ll _. specialize (ll _ (refl_equal _)). case: ll => wl' [e0 e1].
rewrite e0. apply Msym. by apply: (proj2 (Mrefl _ _) e1 _).
Qed.

Lemma IVal_upclosed n (t:Ty n) s w w' k v : w <= w' -> (IVal t s w) (k,v) -> (IVal t s w') (k,v).
move => Lw. apply (fmonotonic (IVal t s) Lw (k,v)).
Qed.

Lemma IEnv_upclosed E n (env:TEnv E n) (s:TVal E) k v w w' : w <= w' -> (IEnv env s w) (k,v) -> (IEnv env s w') (k,v).
elim: n env v ; first by [].
move => n IH env v L. simpl. case => A B.
split.
- specialize (IH (tl env) v.1 L). by apply IH.
- by apply (IVal_upclosed L B).
Qed.

Lemma IExp_eq f k w e e' : e = e' -> IExp f k e w -> IExp f k e' w.
move => E. by rewrite E.
Qed.

Lemma world_update (w:W) f l : l \notin dom (Unfold w) -> w <= (Fold (updMap l f (Unfold w))).
move => X.
apply Unfold_monic. have ee:=UF_id (updMap l f (Unfold w)).
refine (pcm_respect (tset_refl _) (tset_sym ee) _). clear ee. simpl.
move => l0 m e. case_eq (l0 == l) => A.
- rewrite <-(eqP A) in X. rewrite findom_indom in X. by rewrite e in X.
- have B:(l0 != l) by rewrite A. clear A.
  exists m. rewrite updMap_simpl2 ; last by apply B. by rewrite e.
Qed.

Lemma csubst_var n m (g:Prod CValue n)  : Tm.subVal (Prod_subst g) (Tm.VAR m) = nth m (Prod_subst g). 
Proof.
dependent induction m; first by []. simpl. specialize (IHm g.1).
unfold Tm.subVal, Tm.Map.mapVal. simpl. by rewrite tlCons.
Qed.

Lemma negbI (b:bool) : (b -> False) -> ~~ b.
case:b ; last by [].
move => X. simpl. by case: (X is_true_true).
Qed.

(*=Fundamental *)
Lemma FT E (se:StoreType E) : 
  (forall n (env : TEnv E n) v t, VTy se env v t -> VRel env se v t) /\
  (forall n (env : TEnv E n) e t, ETy se env e t -> ERel env se e t).
(*=End *)
move: E se ; apply (@Typing_ind) => E se n env.
(* VAR *)
- move => m k s g w. move => X Y. rewrite csubst_var. by apply FT_var.
(* LOC *)
- move => l k s g w. Tm.UnfoldRenSub. unfold Tm.Map.mapVal. case: k ; first by [].
  move => k Ig Is. simpl. by apply: Is.
(* INT *)
- by []. 
(* UNIT *)
- by [].
(* LAM *)
- move => t0 t1 e D R. unfold VRel. move => k s g w Ie Is. unfold Tm.subVal. rewrite Tm.Map.mapLAM.
  fold Tm.liftSub. fold Tm.subExp. simpl.
  move => w' j v l L Iv. unfold ERel in R. specialize (R j). rewrite <- (proj2 (Tm.applyComposeSub _)).
  rewrite Tm.composeSingleSub. specialize (R s). specialize (R (g,v)). simpl in R. apply R.
  rewrite tlCons. rewrite hdCons. split ; last by []. apply (IEnv_upclosed l). by apply (upred_downclosed L Ie).
  move => ll t sll. clear R. specialize (Is ll _ sll). simpl in Is.
  case: k Ie Is L.
  + rewrite leqn0. move => _ _ ee. by rewrite (eqP ee).
  + move => k Ie Is L. clear Iv. case: j L ; first by [].
    move => j L. case_eq (Unfold w ll) ; last by move => ee ; rewrite ee in Is.
    move => wll wle. case: (fmonotonic Unfold l ll wll wle) => wl'. case => wle' ee.
    rewrite wle'. rewrite wle in Is. rewrite <- (Mrel_mono L Is). unfold Mrel. simpl.
    by apply (proj2 (Mrefl _ _) (tset_sym ee)).
(* TLAM *)
- move => t'. move => e X Y k ts g w. move => A B. unfold Tm.subVal. autorewrite with mapHints.
  fold Tm.subExp. simpl. move => r w' j Lj Lw. specialize (Y j (ts,r) g). apply Y.
  + apply: (IEnv_upclosed Lw). apply (upred_downclosed Lj).
    by apply (proj2 (IEnv_shiftTy _ _ _ _ _) A).
  + simpl. move => l t ee. simpl in B. specialize (B l (se l) (refl_equal _)).
    case: k A B Lj.
    * rewrite leqn0. move => _ _ ke. by rewrite (eqP ke).
    * move => k A B. clear Y. case: j ; first by [].
      move => j Lj. rewrite <- ee. clear t ee. have Lww:=fmonotonic Unfold Lw. clear Lw.
      specialize (Lww l). case: (Unfold w l) B Lww ; last by [].
      move => wl B Lw. specialize (Lw wl (refl_equal _)). case: Lw => wl'. case => ee e'.
      rewrite ee. unfold Mrel. simpl. unfold Mrel in B. simpl in B. apply (Mrel_mono Lj).
      have aa:= Mrel_trans (proj2 (Mrefl _ _) (tset_sym e') k.+1) B. apply (Mrel_trans aa). clear.
      by apply (proj2 (Mrefl _ _) (IVal_shiftTy (se l) _ _)).
(* PAIR *)
- move => t0 t1 e0 e1. move => _ IH0 _ IH1. move => k s g w Ig Is. simpl.
  specialize (IH0 k s g w Ig Is). specialize (IH1 k s g w Ig Is). split.
  + by apply IH0. + by apply IH1. 
(* INL *)
- move => t0 t1 e _ IH0. move => k s g w Ig Is.
  by apply (IH0 k s g w Ig Is). 
(* INR *)
- move => t0 t1 e _ IH0. move => k s g w Ig Is.
  by apply (IH0 k s g w Ig Is). 
(* FOLD *)
- move => e t' td IH. move => k s g w Ig Is. 
  have ee:=FIXP_fp (upred_mu (IVal t') s).
  specialize (ee w (k, Tm.subVal (Prod_subst g) (Tm.FOLD e))). apply (proj2 ee). clear ee.
  case: k Ig Is ; first by []. move => k Ig Is. unfold Tm.subVal. autorewrite with mapHints. fold Tm.subVal.
  specialize (IH k.+1 s g w Ig Is). simpl.
  have A:=proj2 (IVal_substTy _ _ _ _) IH.
  specialize (A (s,FIXP (upred_mu (IVal t') s))). 
  apply: (upred_downclosed (leqW (leqnn _)) (A _)).
  move => i. by dependent destruction i.
(* VAL *)
- move => v t td IH k s g w Ig Is. specialize (IH k s g w Ig Is).
  unfold Tm.subExp. autorewrite with mapHints. fold Tm.subVal.
  move => j Lj h h' v0 ev. inversion ev. clear h0 H0. clear v1 H1.
  move: ev. move => ev.
  move: ev. rewrite <- H2. clear v0 H2. rewrite <- H. clear Lj H j.
  move => ev hv. exists w. split ; first by []. rewrite subn0. split ; first by [].
  by apply IH.
(* LET *)
- move => e0 e1 t0 t1 _ IH0 _ IH1. move => k s g w Ig Is.
  move => j Lj h h' v.  unfold Tm.subExp. autorewrite with mapHints. fold Tm.subExp. move => ev.
  inversion ev. clear h0 H0. clear v1 H3. clear e2 H1 e3 H2 H4.
  move => hv. have Ln0 := leq_addr n1 n0. rewrite H in Ln0.
  specialize (IH0 k s g w Ig Is n0 (leq_trans Ln0 Lj) h _ _ X hv).
  case: IH0 => w1 [Lw [hv0 IH0]]. specialize (IH1 (k-n0) s (g,v0) w1).
  have A:IEnv (cons t0 env) s w1 (k - n0, (g, v0)). split ; simpl ; last by apply IH0.
    rewrite tlCons. by apply: (IEnv_upclosed Lw) ; apply: (upred_downclosed _ Ig) ; apply leq_subr.
  specialize (IH1 A).
  have B: (IStore se s) (k - n0, w1) by apply (IStore_upclosed Lw) ; apply: (upred_downclosed _ Is) ; apply leq_subr.
  specialize (IH1 B n1).
  have Ln1:(n1 <= k - n0)%N. have Ln11:=leq_addl n0 n1. rewrite H in Ln11. rewrite <- (subnKC Ln0) in H.
  have aa:= eqn_addl n0 n1 (j - n0). rewrite H in aa. rewrite eq_refl in aa. rewrite (eqP (sym_eq aa)).
    by apply leq_sub2r.
  specialize (IH1 Ln1 h1 h'). unfold subSingle in X0. rewrite <- (proj2 (Tm.applyComposeSub _)) in X0.
  rewrite -> Tm.composeSingleSub in X0. specialize (IH1 _ X0 hv0). case: IH1 => wr. case => Lw' R.
  exists wr. split ; first by apply (Ole_trans Lw Lw').
  rewrite <- subn_sub. by apply R.
(* FST *)
- move => v t1 t2 td IH k s g w Ig Is. move => j Lj h h' v'.
  unfold Tm.subExp. autorewrite with mapHints. fold Tm.subVal. move => ev. inversion ev. clear h0 H0.
  specialize (IH k s g w Ig Is). move: ev. rewrite <- H. clear j H Lj. rewrite H2 in H1. clear v0 H2.
  move => ev hv. exists w. split ; first by []. rewrite subn0. split ; first by [].
  rewrite <- H1 in IH. simpl in IH. by case: IH.
(* SND *)
- move => v t1 t2 td IH k s g w Ig Is. move => j Lj h h' v'.
  unfold Tm.subExp. autorewrite with mapHints. fold Tm.subVal. move => ev. inversion ev. clear h0 H0.
  specialize (IH k s g w Ig Is). move: ev. rewrite <- H. clear j H Lj. rewrite H2 in H1. clear v1 H2.
  move => ev hv. exists w. split ; first by []. rewrite subn0. split ; first by [].
  rewrite <- H1 in IH. simpl in IH. by case: IH.
(* OP *)
- move => op v. move => A B. move => k s g w Ie Is. simpl. unfold Tm.subExp. autorewrite with mapHints. fold Tm.subVal.
  move => j Lj h h' vv ev. inversion ev. clear op0 H1. rewrite <- H in Lj, ev. clear j H ev.
  clear h0 H0. rewrite <- H4. clear h' H4. clear vv H3. rewrite subn0. simpl. move => hv. exists w. by split ; last split.
(* UNFOLD *)
- move => t v _ IH. move => k s g w Ie Is. move => j' Lj h h' vr.
  unfold Tm.subExp. autorewrite with mapHints. fold Tm.subVal. move => ev. inversion ev.
  rewrite -> H2 in H1. clear v0 H2. rewrite <- H in Lj. clear ev j' H. clear h0 H0.
  rewrite <- H3. clear h' H3.  move => hw. specialize (IH k s g w Ie Is). simpl in IH. rewrite <- H1 in IH.
  clear Ie Is H1 v g. case: k Lj IH hw ; first by [].
  move => k _ IH hw. have IIH:= proj1 (FIXP_fp (upred_muc (IVal t) s) w (k.+1, Tm.FOLD vr)) IH. clear IH.
  simpl in IIH. rewrite subSS. rewrite subn0. unfold unfoldTy. unfold subOneTy.
  exists w ; split ; first by []. split ; first by apply (heap_world_down (leqW (leqnn k))).
  apply: (proj1 (IVal_substTy t _ w _) IIH) => i. by dependent destruction i.
(* REF *)
- move => v t _ IH. move => k s g w Ie Is. move => j' Lj h h' vr.
  unfold Tm.subExp. autorewrite with mapHints. fold Tm.subVal. move => ev. inversion ev.
  rewrite <- H0 in Lj. clear H0 j' ev. clear vr H3. clear v0 H. clear h0 H2. clear h' H4.
  move => hw. case: k Ie Is Lj hw ; first by [].
  move => k Ie Is _ hw. rewrite subSS. rewrite subn0. simpl.
  exists (Fold (updMap l (IVal t s) (Unfold w))).
  have Lw:w <= Fold (updMap l (IVal t s) (Unfold w)).
  + apply: Unfold_monic. move => ll m e. have F:=proj1 (hw k (ltnSn _)). specialize (F l). rewrite F in H1.
    case_eq (l == ll) => ee.
    * rewrite <- (eqP ee) in e. rewrite findom_indom in H1. by rewrite e in H1.
    * case_eq (Unfold (Fold (updMap l (IVal t s) (Unfold w))) ll).
      - move => ufwl eaa. exists ufwl. split ; first by [].
        have xxx:Some m =-= Some ufwl ; last by apply xxx. rewrite <- eaa. clear ufwl eaa.
        have aaa:= (UF_id (updMap l (IVal t s) (Unfold w))). simpl in aaa. unfold Datatypes.id in aaa.
        have bb:= (proj2 aaa ll). rewrite -> bb. rewrite updMap_simpl2. by rewrite e.
        apply negbI => ea. rewrite (eqP ea) in ee. by rewrite eq_refl in ee.
        clear bb. rewrite (proj1 aaa). rewrite indomUpdMap. rewrite findom_indom. rewrite e. simpl. by rewrite orbT.
      - move => a. have b:=UF_id (updMap l (IVal t s) (Unfold w)). simpl in b. unfold Datatypes.id in b.
        have ne:= findom_indom (Unfold (Fold (updMap l (IVal t s) (Unfold w)))) ll. rewrite a in ne. simpl in ne.
        rewrite -> (proj1 b) in ne. rewrite indomUpdMap in ne. rewrite findom_indom in ne. rewrite e in ne.
        simpl in ne. by rewrite orbT in ne.
  split ; first by apply Lw.
  + split. move => j' Lj. split.
    * move => ll. rewrite indomUpdMap. 
      have b:=UF_id (updMap l (IVal t s) (Unfold w)). simpl in b. unfold Datatypes.id in b.
      rewrite (proj1 b ll). rewrite indomUpdMap. have e0:=proj1 (hw k (ltnSn _)) ll. by rewrite e0.
    * move => l0. case_eq (Unfold (Fold (updMap l (IVal t s) (Unfold w))) l0) ; last by [].
      move => ufl0 e0. have e1:=UF_id (updMap l (IVal t s) (Unfold w)). simpl in e1.
      unfold Datatypes.id in e1. have b1:=proj2 e1 l0. rewrite findom_indom in b1. rewrite e0 in b1.
      specialize (b1 is_true_true). clear e0. clear e1. specialize (hw k (ltnSn _)).
      case: hw => dhe hw. specialize (hw l0). case_eq (l == l0).
      - move => e. rewrite (eqP e). simpl.
        rewrite (updMap_simpl l0 (Tm.subVal (Prod_subst g) v) h). rewrite -> (eqP e) in b1.
        rewrite (updMap_simpl l0) in b1. unfold tset_eq in b1. simpl in b1. simpl.
        apply (proj2 ((b1 (Fold (updMap l0 ((IVal t) s) (Unfold w)))) (j', Tm.subVal (Prod_subst g) v))). 
        clear ufl0 b1.
        specialize (IH j' s g w). rewrite <- (eqP e). apply: (IVal_upclosed Lw). apply IH.
        by apply (upred_downclosed (leqW (ltnW Lj)) Ie). by apply (upred_downclosed (leqW (ltnW Lj)) Is).
      - move => ee. simpl. rewrite updMap_simpl2.
        rewrite updMap_simpl2 in b1. specialize (dhe l0). do 2 rewrite findom_indom in dhe.
        case_eq (h l0) ; last by move => F ; rewrite F.
        move => hl0 e. rewrite e. case: (Unfold w l0) hw b1 ; last by [].
        move => uwl0 hw b1. rewrite e in hw. unfold tset_eq in b1. simpl in b1.
        specialize (b1 w (k,hl0)). simpl in b1. have hh := proj2 b1 hw. clear uwl0 b1 hw.
        apply (fmonotonic ufl0 Lw (j',hl0)). by apply (@upred_downclosed _ _ j' k _ (leqW Lj) hh).
      apply negbI => e. rewrite (eqP e) in ee. by rewrite eq_refl in ee.
      apply negbI => e. rewrite (eqP e) in ee. by rewrite eq_refl in ee.
  + case: k Ie Is hw ; first by [].
    move => k Iw Is hw. have ee:=UF_id (updMap l (IVal t s) (Unfold w)). simpl in ee. unfold Datatypes.id in ee.
    have aa:=(proj2 ee l _). rewrite (proj1 ee) in aa. rewrite indomUpdMap in aa. rewrite eq_refl in aa.
    specialize (aa is_true_true).
    rewrite -> (proj2 (Mrefl _ _) aa). by rewrite updMap_simpl.
(* REF *)
- move => v t _ IH. move => k s g w Ie Is. move => j Lj h h' vr.
  unfold Tm.subExp. autorewrite with mapHints. fold Tm.subVal. move => ev. inversion ev.
  clear h0 H2. clear v0 H3. rewrite <- H0 in Lj. clear j H0 ev. rewrite <- H4. rewrite <- H4 in H1. clear h' H4.
  move => hw. exists w ; split ; first by []. split.
  + case: k Lj Ie Is hw ; first by [].
    move => k _ Ie Is hw. rewrite subSS. rewrite subn0. by apply: (heap_world_down (leqW (leqnn k)) hw).
  + specialize (IH k s g w Ie Is). rewrite <- H in IH. simpl in IH.
    case: k IH Lj Ie Is hw ; first by []. move => k IH _ Ie Is hw.
    rewrite subSS. rewrite subn0. specialize (hw k (ltnSn _)). case: hw => D hw.
    specialize (hw l). case: (Unfold w l) IH hw ; last by [].
    move => wl IH hw. rewrite H1 in hw. unfold Mrel in IH. simpl in IH.
    specialize (IH w k vr (ltnSn _)). simpl in IH. by apply (proj1 IH hw).
(* ASSIGN *)
- move => v0 v1 t _ IH0 _ IH1. move => k s g w Ie Is. move => j Lj h h' vr.
  unfold Tm.subExp. autorewrite with mapHints. fold Tm.subVal. move => ev. inversion ev.
  rewrite <- H0 in Lj. clear j ev H0. clear v H2. clear h0 H1. clear vr H3. clear h' H4.
  specialize (IH0 k s g w Ie Is). rewrite <- H in IH0. clear v0 H.
  specialize (IH1 k s g w Ie Is). simpl in IH0. case: k IH0 IH1 Ie Is Lj ; first by [].
  move => k IH0 IH1 Ie Is _ hw. rewrite subSS. rewrite subn0. exists w ; split ;first by [].
  split ; last by [].
  move => j Lj. split.
  + move => ll. rewrite indomUpdMap. specialize (hw k (ltnSn _)). rewrite <- (proj1 hw).
    case_eq (ll == l) => ee ; last by []. rewrite (eqP ee). rewrite findom_indom. by rewrite H5.
  + move => l0. case_eq (Unfold w l0) ; last by []. move => wl0 e0.
    case_eq (l == l0) => e.
    * rewrite <- (eqP e). rewrite updMap_simpl.
      rewrite <- (eqP e) in e0. clear l0 e. rewrite e0 in IH0.
      specialize (IH0 w j (Tm.subVal (Prod_subst g) v1) (ltnW Lj)). simpl in IH0. apply (proj2 IH0). clear IH0 wl0 e0.
      apply: (upred_downclosed _ IH1). by apply (leqW (leqW Lj)).
    * rewrite updMap_simpl2. case_eq (h l0) ; last by move => e1.
      move => hl0 e1. specialize (hw j (leqW Lj)). case: hw => D hw.
      specialize (hw l0). rewrite e0 in hw. rewrite e1 in hw. by apply hw.
    apply negbI => e1. rewrite (eqP e1) in e. by rewrite eq_refl in e.
- move => t0 t1 v0 v1 _ IH0 _ IH1. move => k s g w Ie Is. specialize (IH0 k s g w Ie Is).
  specialize (IH1 k s g w Ie Is). move => j Lj h h' vr.
  unfold Tm.subExp. autorewrite with mapHints. fold Tm.subVal. move => ev. inversion ev.
  clear n0 H. clear h0 H0. clear v2 H3. clear h1 H4. clear v H2. clear ev. move => hw.
  rewrite <- H1 in IH0. clear H1 v0. simpl in IH0. have IH0':= (IH0 w k _ (Ole_refl _) (leqnn _) IH1). clear IH0.
  specialize (IH0' j Lj h h'). unfold subSingle in X. by apply (IH0' _ X hw).
- move => t v t' _ IH. move => k s g w Ie Is. specialize (IH k s g w Ie Is).
  move => j Lj h h' vr.
  unfold Tm.subExp. autorewrite with mapHints. fold Tm.subVal. move => ev. inversion ev.
  clear n0 H. clear h0 H0. clear v0 H2. clear h1 H3. rewrite <- H1 in IH. clear H1 v ev.
  move => hw. simpl in IH. specialize (IH (IVal t' s) w k (leqnn _) (Ole_refl _) j Lj h h' _ X hw).
  unfold subOneTy. case: IH => w'. case => Lw. case => hw' IH. exists w'. split ; first by []. split ; first by [].
  apply: (proj1 (IVal_substTy t _ _ _) IH). move => i. by dependent destruction i.
- move => t0 t1 v e0 e1 t' _ IH0 _ IH1 _ IH2. move => k s g w Ie Is.
  specialize (IH0 k s g w Ie Is). move => j Lj h h' vr.
  unfold Tm.subExp. autorewrite with mapHints. fold Tm.subExp. fold Tm.subVal. move => ev. inversion ev.
  + clear n0 H. clear e2 H2. clear e3 H3. clear h0 H0. clear v1 H4. clear h1 H5. rewrite <- H1 in IH0. clear v H1 ev.
    simpl in IH0. specialize (IH1 k s (g,v0) w).
    have IE2:IEnv (cons t0 env) s w (k, (g, v0)). simpl. rewrite tlCons. split ; first by []. by apply IH0.
    specialize (IH1 IE2 Is j Lj h h'). apply IH1.
    unfold subSingle in X. rewrite <- (proj2 (Tm.applyComposeSub _)) in X. fold Tm.liftSub in X.
    rewrite Tm.composeSingleSub in X. by apply X.
  + clear n0 H. clear e2 H2. clear e3 H3. clear h0 H0. clear v1 H4. clear h1 H5. rewrite <- H1 in IH0. clear v H1 ev.
    simpl in IH0. specialize (IH2 k s (g,v0) w).
    have IE2:IEnv (cons t1 env) s w (k, (g, v0)). simpl. rewrite tlCons. split ; first by []. by apply IH0.
    specialize (IH2 IE2 Is j Lj h h'). apply IH2.
    unfold subSingle in X. rewrite <- (proj2 (Tm.applyComposeSub _)) in X. fold Tm.liftSub in X.
    rewrite Tm.composeSingleSub in X. by apply X.
Qed.
