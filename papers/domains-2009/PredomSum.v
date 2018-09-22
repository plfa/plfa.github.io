(*==========================================================================
  Definition of co-products and associated lemmas
  ==========================================================================*)
Require Import PredomCore.
Set Implicit Arguments.
Unset Strict Implicit.


(*==========================================================================
  Order-theoretic definitions
  ==========================================================================*)
Definition Osum: ord -> ord -> ord.
intros O1 O2. exists ((O1 + O2)%type) 
     (fun x y => match x, y with | inl x, inl y => x <= y | inr x, inr y => x <= y | _,_ =>  False end).
intros x. case x ; intros t ; apply Ole_refl.
intros x y z. case x ; clear x ; intros x.
  case y ; clear y ; intros y ; try (intros ; intuition ; fail).
  case z ; clear z ; intros z ; try (intros ; intuition ; fail). apply Ole_trans.
case y ; clear y ; intros y ; try (intros ; intuition ; fail).
case z ; clear z ; intros z ; try (intros ; intuition ; fail). apply Ole_trans.
Defined.

Definition Inl (O1 O2:ord) : O1 -m> (Osum O1 O2).
intros. exists (fun x => @inl O1 O2 x). unfold monotonic.
intros. auto.
Defined.

Definition Inr (O1 O2 :ord) : O2 -m> (Osum O1 O2).
intros. exists (fun x => @inr O1 O2 x). unfold monotonic. auto.
Defined.

Definition sum_left (D1 D2:cpo) (c:natO -m> Osum D1 D2) (ex:{d| c O = inl D2 d}) : (natO -m> D1).
intros D1 D2 c ex.
destruct ex as [d ex].
exists (fun x => match c x with | inl y => y | inr _ => d end).
unfold monotonic.
intros n m lm. assert (c n <= c m). auto. generalize H. clear H.
assert ((O <= n) % nat) as no by omega. assert (c O <= c n) as con by auto. rewrite ex in con. clear ex no.
generalize con. clear con.
case (c n). intros d1 _. case (c m). intros d1'. auto.
intros d2' incon. inversion incon. intros d1' incon. inversion incon.
Defined.

Definition sum_right (D1 D2:cpo) (c:natO -m> Osum D1 D2) (ex:{d | c O = inr D1 d}) : (natO -m> D2).
intros D1 D2 c ex.
destruct ex as [d ex].
exists (fun x => match c x with | inr y => y | inl _ => d end).
unfold monotonic.
intros n m lm. assert (c n <= c m). auto. generalize H. clear H.
assert ((O <= n) % nat) as no by omega. assert (c O <= c n) as con by auto. rewrite ex in con. clear ex no.
generalize con. clear con.
case (c n). intros d1 _. case (c m). intros d1'. auto.
intros d2' incon. inversion incon. intros d1' _. case (c m). intros tt incon. inversion incon.
intros d2' l. auto.
Defined.

Definition SuminjProof: forall (D1 D2:cpo) (c:natO -m> Osum D1 D2) (n:nat),
      {d | c n = inl D2 d} + {d | c n = inr D1 d}.
intros D1 D2 c n.
assert ((0 <= n)%nat). omega.
assert (c 0 <= c n). auto. clear H.
case_eq (c 0).
intros d1 c0.
case_eq (c n). intros dn cnd.
left.
exists dn. auto.
intros d2 incon. rewrite incon in H0. rewrite c0 in H0. inversion H0.

intros d2 c0. right.
case_eq (c n). intros dn cnd.
rewrite cnd in H0. rewrite c0 in H0. inversion H0.
intros dn cn. exists dn. auto.
Defined.

Definition sum_lub (D1 D2:cpo) (c: natO -m> Osum D1 D2) : (Osum D1 D2).
intros D1 D2 c. case (SuminjProof c 0).
intros X. refine (inl D2 (lub (sum_left X))).
intro X. refine (inr D1 (lub (sum_right X))).
Defined.

(*==========================================================================
  Domain-theoretic definitions
  ==========================================================================*)
Definition Dsum : cpo -> cpo -> cpo.
intros D1 D2. exists (Osum D1 D2) (@sum_lub D1 D2).
intros c n.
case_eq (c 0).
intros d1 c0.
simpl. case_eq (c n). intros dn cn.
unfold sum_lub. destruct (SuminjProof c 0) as [inj|inj].
assert (sum_left inj n = dn).
destruct inj. simpl. rewrite cn. auto.
rewrite <- H.
apply le_lub.

destruct inj as [dd c0n]. rewrite c0n in c0. inversion c0.
intros d2 cn.
assert ((0 <= n) % nat) as A by omega.
assert (c 0 <= c n) by auto. rewrite c0 in H. rewrite cn in H. inversion H.

intros d2 c0. simpl. case_eq (c n). intros dn cn.
unfold sum_lub. destruct (SuminjProof c 0) as [[d inj] | inj].
rewrite inj in c0. inversion c0.
assert ((0 <= n) % nat) as A by omega. assert (c 0 <= c n) by auto.
rewrite c0 in H. rewrite cn in H. inversion H.
intros dn cn. unfold sum_lub. destruct (SuminjProof c 0) as [[dd inj]|[d inj]].
rewrite c0 in inj. inversion inj.
assert (sum_right (exist (fun dd => c 0 = inr D1 dd) d inj) n = dn).
simpl. rewrite cn. auto.
rewrite <- H.
apply (le_lub).

intros c x. case x ; clear x ; intros x cn. unfold sum_lub.
case (SuminjProof c 0). intros s.
assert (lub (sum_left s) <= x).
apply (lub_le). intros n. specialize (cn n). destruct s as [d c0].
simpl. case_eq (c n). intros dn dnl. rewrite dnl in cn. auto.
intros dn cnr. rewrite cnr in cn. inversion cn. auto.
intros s. destruct s. simpl. specialize (cn 0).
rewrite e in cn. inversion cn.

unfold sum_lub. case (SuminjProof c 0). intros s.
destruct s. simpl. specialize (cn 0). rewrite e in cn. inversion cn.
intros s. assert (lub (sum_right s) <= x).
apply lub_le. intros n. specialize (cn n). destruct s as [d c0].
simpl. case_eq (c n). intros dl cnl. rewrite cnl in cn. inversion cn.
intros dl dll. rewrite dll in cn. auto. auto.
Defined.

Definition Sum_fun : forall (D1 D2 D3:cpo) (f:D1 -m> D3) (g:D2-m> D3),
                      Dsum D1 D2 -m> D3.
intros. exists (fun p => match p with inl y => (f y) | inr y => (g y) end).
unfold monotonic. intros x y.
case_eq x. intros xx _. clear x. case_eq y. intros yy _ ll. auto.
intros yy _ incon. inversion incon.
intros xx _. case_eq y. intros yy _ incon. inversion incon.
intros yy _ ll. auto.
Defined.

Definition SUM_fun (D1 D2 D3:cpo)(f:D1 -c> D3) (g:D2 -c> D3) :
       Dsum D1 D2 -c> D3.
intros. exists (Sum_fun (fcontit f) (fcontit g)).
unfold continuous. intros c.
simpl. case_eq (sum_lub c).
intros ll. intros sl. unfold sum_lub in sl.
destruct (SuminjProof c 0).
inversion sl. clear sl.
destruct s as [dd c0]. assert (continuous (fcontit f)) as fC by auto.
unfold continuous in fC. rewrite fC.
apply lub_le_compat. simpl. intros n.
case_eq (c n). intros t cn. simpl. simpl in cn. rewrite cn. auto.
intros t cn. simpl. simpl in cn. rewrite cn.
assert (c 0 <= c n). assert (0 <= n) % nat by omega. auto.
simpl in c0. simpl in H. rewrite c0 in H. rewrite cn in H. inversion H.
inversion sl.

intros ll. intros sl. unfold sum_lub in sl. destruct (SuminjProof c 0).
inversion sl. inversion sl. clear sl. destruct s as [dd c0].
assert (continuous (fcontit g)) as gC by auto.
unfold continuous in gC. rewrite gC. apply lub_le_compat.
simpl. intros n.
simpl. case_eq (c n). intros t cn. simpl. simpl in cn. rewrite cn.
assert (c 0 <= c n). assert (0 <= n)%nat as A by omega. auto.
simpl in H. rewrite c0 in H. rewrite cn in H. inversion H.
intros t cn. simpl in cn. rewrite cn. auto.
Defined.

Implicit Arguments SUM_fun [D1 D2 D3].

Add Parametric Morphism (D E F:cpo) : (@SUM_fun D E F)
with signature (@Ole (D -c> F)) ++> (@Ole (E -c> F)) ++> (@Ole ((Dsum D E) -c> F))
as SUM_fun_le_compat.
intros f f' lf g g' lg.
simpl. intros x ; case x ; clear x ; auto.
Qed.

Add Parametric Morphism (D E F:cpo) : (@SUM_fun D E F)
with signature (@Oeq (D -c> F)) ==> (@Oeq (E -c> F)) ==> (@Oeq ((Dsum D E) -c> F))
as SUM_fun_eq_compat.
intros f f' lf g g' lg.
simpl. apply fcont_eq_intro.
destruct lg. destruct lf.
intros x ; split ; case x ; clear x ; auto.
Qed.

Definition INL (D1 D2:cpo) : D1 -c> Dsum D1 D2.
intros. exists (@Inl D1 D2). unfold continuous.
intros c. simpl. apply lub_le_compat.
simpl. auto.
Defined.

Implicit Arguments INL [D1 D2].

Add Parametric Morphism (D E:cpo) : (@INL D E)
with signature (@Ole D) ++> (@Ole (Dsum D E))
as SUM_INL_le_compat.
intros ; auto.
Qed.

Add Parametric Morphism (D E:cpo) : (@INL D E)
with signature (@Oeq D) ==> (@Oeq (Dsum D E))
as SUM_INL_eq_compat.
intros ; auto.
Qed.

Definition INR (D1 D2:cpo) : D2 -c> Dsum D1 D2.
intros. exists (@Inr D1 D2). unfold continuous. intros c. simpl. apply lub_le_compat.
auto.
Defined.

Implicit Arguments INR [D1 D2].

Add Parametric Morphism (D E:cpo) : (@INR D E)
with signature (@Ole E) ++> (@Ole (Dsum D E))
as SUM_INR_le_compat.
intros ; auto.
Qed.

Add Parametric Morphism (D E:cpo) : (@INR D E)
with signature (@Oeq E) ==> (@Oeq (Dsum D E))
as SUM_INR_eq_compat.
intros ; auto.
Qed.

Definition SUM_map D1 D2 D3 D4 (f:D1 -c> D3) (g:D2 -c> D4) := 
 SUM_fun (INL << f) (INR << g).

Add Parametric Morphism (D E F G:cpo) : (@SUM_map D E F G)
with signature (@Ole (D -c> F)) ++> (@Ole (E -c> G)) ++> (@Ole ((Dsum D E) -c> (Dsum F G)))
as SUM_map_le_compat.
intros f f' lf g g' lg.
simpl. intros x ; case x ; clear x ; auto.
Qed.

Add Parametric Morphism (D E F G:cpo) : (@SUM_map D E F G)
with signature (@Oeq (D -c> F)) ==> (@Oeq (E -c> G)) ==> (@Oeq ((Dsum D E) -c> (Dsum F G)))
as SUM_map_eq_compat.
intros f f' lf g g' lg.
simpl. apply fcont_eq_intro.
destruct lg. destruct lf.
intros x ; split ; case x ; clear x ; auto.
Qed.

Definition SUM_Map1 (D E F G:cpo) : (D -C-> F) -> (E -C-> G) -M-> Dsum D E -C-> Dsum F G.
intros. exists (@SUM_map D E F G X).
unfold monotonic. intros x y xyl. intros xx ; case xx ; auto.
Defined.

Definition SUM_Map (D E F G:cpo) : (D -C-> F) -M-> (E -C-> G) -M-> Dsum D E -C-> Dsum F G.
intros. exists (@SUM_Map1 D E F G). unfold monotonic.
intros x y xyl. intros xx yy ; case xx ; case yy ; simpl ; auto.
Defined.

Lemma SUM_Map_continuous2 : forall D E F G, continuous2 (SUM_Map D E F G).
intros. unfold continuous2. intros c1 c2.
intros p. case p ; auto.
Save.

Definition SUM_MAP (D E F G:cpo) : (D -C-> F) -C-> (E -C-> G) -C-> Dsum D E -C-> Dsum F G :=
  (continuous2_cont (@SUM_Map_continuous2 D E F G)).

Lemma SUM_map_simpl (D E F G:cpo) f g : SUM_MAP D E F G f g = SUM_map f g.
intros. auto.
Qed.

Lemma SUM_fun_simpl (D E F:cpo) f g s : @SUM_fun D E F f g s = Sum_fun (fcontit f) (fcontit g) s.
intros. auto.
Qed.

Lemma Dsum_lcom: forall D1 D2 D3 f g, @SUM_fun D1 D2 D3 f g << INL == f.
intros. apply fcont_eq_intro. intros s. auto.
Qed.

Lemma Dsum_rcom: forall D1 D2 D3 f g, @SUM_fun D1 D2 D3 f g << INR == g.
intros. apply fcont_eq_intro. auto.
Qed.

Lemma Dsum_unique: forall D1 D2 D3 f g h, h << INL == f -> h << INR == g ->
            h == @SUM_fun D1 D2 D3 f g.
intros. apply fcont_eq_intro. intros x.
case x. clear x. intros t.
assert (xx:= fcont_eq_elim H t). auto.
intros t. assert (xx:= fcont_eq_elim H0 t). auto.
Qed.

Lemma SUM_fun_comp : 
  forall C D E F (f:C-c>E) (g:D-c>E) (h:E-c>F), h << SUM_fun f g == SUM_fun (h << f) (h << g).
intros C D E F f g h.
apply fcont_eq_intro. intro x. case x; auto. 
Qed.
 
