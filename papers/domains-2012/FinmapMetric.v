(**********************************************************************************
 * Finmap.v                                                                       *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                       *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)

Require Export NSetoid MetricCore Finmap.

Section SET.
Variable T:compType.
Variable S:setoidType.

Lemma finmap_setoid_axiom : Setoid.axiom (fun f f' : FinDom T S => dom f =i dom f' /\ forall t, t \in dom f -> f t =-= f' t).
split ; last split.
- by move => f ; simpl ; split ; last by [].
- move => x y z ; simpl => X Y. case: X => D X. case: Y => D' Y.
  split. move => a. rewrite (D a). by rewrite (D' a).
  move => a A. rewrite -> (X a A). rewrite D in A. by apply (Y _ A).
- move => x y ; simpl => X. case: X => D X.
  split => a. by rewrite (D a). move => A. rewrite <- D in A. by rewrite -> (X a A).
Qed.

Definition findom_setoidMixin := SetoidMixin finmap_setoid_axiom.
Canonical Structure findom_setoidType := Eval hnf in SetoidType findom_setoidMixin.

Lemma indom_app_respect (f f': findom_setoidType) x (P:x \in dom f) (P':x \in dom f') : f =-= f' -> indom_app P =-= indom_app P'.
move => e. have X:Some (indom_app P) =-= Some (indom_app P') ; last by apply X.
do 2 rewrite indom_app_eq. case: f e P => s A. case: f' P' => s' A'. move => P e P'.
unfold tset_eq in e. simpl in e. by apply (proj2 e).
Qed.

Lemma respect_domeq (f f':findom_setoidType) : f =-= f' -> dom f =i dom f'.
case:f => s P. case:f' => s' P'.
unfold dom. simpl. unfold tset_eq. simpl. unfold dom. simpl. by move => [A _].
Qed.

Lemma findom_sapp_respect (x:T) : setoid_respect (fun f:findom_setoidType => f x).
move => f f' e. case_eq (x \in dom f) => D. by apply (proj2 e x D).
rewrite findom_undef ; last by rewrite D. rewrite (proj1 e) in D.
rewrite findom_undef ; last by rewrite D. by [].
Qed.

Definition findom_sapp (x:T) : findom_setoidType =-> option_setoidType S :=
  Eval hnf in mk_fset (findom_sapp_respect x).


End SET.

Section MET.
Variable T:compType.
Variable M:metricType.

Lemma findom_metric_axiom : Metric.axiom (fun n => (fun f f' : FinDom T M => match n with O => True | S _ =>
       dom f =i dom f' /\ forall i, i \in dom f -> i \in dom f' -> f i = n = f' i end)).
move => n x y z. split ; last split ; last split ; last split ; clear.
- split => X.
  + split. specialize (X 1). simpl in X. by apply (proj1 X).
    move => t I. apply: (proj1 (Mrefl _ _)) => n. case: n ; first by []. move => n. specialize (X n.+1).
    simpl in X. apply (proj2 X). by apply I. rewrite (proj1 X) in I. by apply I.
  + case ; first by []. move => n. split ; first by apply (proj1 X). move => i I I'.
    apply (proj2 (Mrefl _ _)). by apply (proj2 X _ I).
- move => A. simpl. simpl in A. case: n A ; first by []. move => n [A B]. split ; first by move => a ; rewrite -> A.
  move => i I I'. specialize (B i I' I). by apply (Msym B).
- move => A B. simpl in A,B. simpl. case: n A B ; first by [].
  move => n [A D] [A' D']. split ; first by move => a ; rewrite A; rewrite A'.
  move => i I I'. specialize (D i I). rewrite A in I. specialize (D I). specialize (D' i I I').
  by apply (Mrel_trans D D').
- move => A. simpl. simpl in A. case: n A ; first by []. move => n [D A]. split ; first by [].
  move => i I I'. specialize (A i I I'). by apply Mmono.
- by [].
Qed.

Canonical Structure findom_metricMixin := MetricMixin findom_metric_axiom.
Canonical Structure findom_metricType := Eval hnf in MetricType findom_metricMixin.

Lemma findom_f_nonexp (f f':findom_metricType) n x : f = n = f' -> f x = n = f' x.
case: n x ; first by [].
move => n x [E P]. case_eq (x \in dom f) => D.
- have D':=D. rewrite E in D'. specialize (P x D D'). by apply P.
  rewrite findom_undef ; last by rewrite D.
  rewrite E in D. rewrite findom_undef ; last by rewrite D. by [].
Qed.

Lemma findom_sapp_ne (x:T) : nonexpansive (fun f:findom_metricType => f x).
move => n f f' e. by apply: findom_f_nonexp.
Qed.

Definition findom_napp (x:T) : findom_metricType =-> option_metricType M :=
  Eval hnf in mk_fmet (findom_sapp_ne x).

End MET.

Section CMET.
Variable T:compType.
Variable M:cmetricType.

Lemma findom_chain_dom x n (c:cchain (findom_metricType T M)) : x \in dom (c 1) -> x \in dom (c n.+1).
elim: n c ; first by [].
move => n IH c X. specialize (IH (cutn 1 c)). simpl in IH. do 2 rewrite -> addSn, -> add0n in IH.
apply IH. clear IH. have C:=cchain_cauchy c. specialize (C 1 1 2 (ltnSn _) (ltnW (ltnSn _))).
by rewrite (proj1 C) in X.
Qed.

Definition findom_chainx (c:cchain (findom_metricType T M)) x (P:x \in dom (c 1)) : cchain M.
exists (fun n => @indom_app _ _ (c n.+1) _ (findom_chain_dom _ n _ P)).
case ; first by [].
move => n i j l l'.
have X: Some (indom_app (findom_chain_dom x i c P)) = n.+1 = Some (indom_app (findom_chain_dom x j c P)) ; last by apply X.
do 2 rewrite indom_app_eq. have a:= (@cchain_cauchy _ c n.+1 i.+1 j.+1 (ltnW l) (ltnW l')).
by apply findom_f_nonexp.
Defined.

Definition findom_lub (c:cchain (findom_metricType T M)) : findom_metricType T M :=
  @findom_map _ _ _ (c 1) (fun x X => umet_complete (@findom_chainx c x X)).

Lemma ff (P:T -> nat -> Prop) (A:forall x n m, n <= m -> P x n -> P x m) (s:seq T) :
  (forall x, x \in s -> exists m, P x m) -> exists m, forall x, x \in s -> P x m.
elim: s ; first by move => X; exists 0.
move => t s IH X. specialize (IH (fun x A => X x (mem_cons t A))). destruct IH as [m IH].
have X':=X t (mem_head t _). destruct X' as [m' Pm']. exists (maxn m m'). move => x I.
rewrite in_cons in I. case_eq (x == t) => E.
- rewrite (eqP E). apply: (A _ _ _ _ Pm'). rewrite leq_maxr. rewrite leqnn. by rewrite orbT.
- rewrite E in I. simpl in I. specialize (IH _ I). apply: (A _ _ _ _ IH). rewrite leq_maxr. by rewrite leqnn.
Qed.

Lemma findom_lubP (c:cchain (findom_metricType T M)) : mconverge c (findom_lub c).
unfold findom_lub. case ; first by exists 0. move => n.
have A:exists m, forall x, x \in dom (c 1) -> forall (X: x \in dom (c 1)) i, m < i -> c i x = n.+1 = Some (umet_complete (findom_chainx _ _ X)).
apply (@ff (fun x m => forall (X:x \in dom (c 1)) i, m < i -> c i x = n.+1 = Some (umet_complete (findom_chainx _ _ X)))).
clear. move => x j i A Y X k L. apply Y. by apply (@ssrnat.leq_ltn_trans _ _ _ A L).
move => x I. destruct (cumet_conv (findom_chainx _ _ I) n.+1) as [m P].
exists m. move => X. case ; first by []. move => i L. specialize (P i L). simpl in P.
rewrite <- (indom_app_eq (findom_chain_dom _ i _ I)).
apply: (Mrel_trans P). apply umet_complete_extn. move=> j. simpl.
have A:Some (indom_app (findom_chain_dom _ j _ I)) = n.+1 = Some (indom_app (findom_chain_dom _ j _ X)) ; last by apply A.
rewrite (indom_app_eq (findom_chain_dom _ j _ I)). by rewrite (indom_app_eq (findom_chain_dom _ j _ X)).
destruct A as [m A]. exists m.+1. case ; first by []. move => i L. split. rewrite <- dom_findom_map.
have B:=cchain_cauchy c. specialize (B 1 i.+1 1 (ltn0Sn i) (ltn0Sn _)). apply (proj1 B).
move => x I I'. specialize (A x).
have J:x \in dom (c 1). have J:=cchain_cauchy c. specialize (J 1 i.+1 1 (ltn0Sn _) (ltn0Sn _)). have X:= (proj1 J).
rewrite X in I. by [].
specialize (A J J i.+1 L). apply (Mrel_trans A).
by rewrite -> (findom_map_app J).
Qed.

Canonical Structure findom_cmetricMixin := CMetricMixin findom_lubP.
Canonical Structure findom_cmetricType := Eval hnf in CMetricType findom_cmetricMixin.

Lemma dom_findom_lub (c:cchain findom_cmetricType) : dom (umet_complete c) = dom (c 1).
unfold umet_complete. simpl. unfold findom_lub.
by rewrite <- dom_findom_map.
Qed.

Lemma findom_lub_eq (c:cchain findom_cmetricType) x : umet_complete c x =-= umet_complete (liftc (findom_napp _ _ x) c).
apply: (proj1 (Mrefl _ _)) => n.
case: (cumet_conv c n). move => m X. 
case: (cumet_conv (liftc (findom_napp T M x) c) n). move => m' Y.
specialize (X ((m+m')%N.+1)%N). specialize (X (leqW (leq_addr _ _))). specialize (Y ((m+m')%N.+1) (leqW (leq_addl _ _))).
case: n X Y ; first by [].
move => n X Y. case: X => D X. specialize (X x).
- case_eq (x \in dom (umet_complete c)) => e.
  have e':=e. rewrite dom_findom_lub in e'. specialize (X (findom_chain_dom _ _ _ e') e).
  rewrite <- X. by rewrite <- Y.
- rewrite findom_undef ; last by rewrite e. clear X. rewrite <- Y. clear Y. simpl.
  rewrite findom_undef ; first by []. rewrite D. by rewrite e.
Qed.

End CMET.



