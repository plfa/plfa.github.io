(**********************************************************************************
 * PredomFix.v                                                                    *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                       *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)

(*==========================================================================
  Definition of fixpoints and associated lemmas
  ==========================================================================*)
Require Import PredomCore.
Require Import PredomLift.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** ** Fixpoints *)

Section Fixpoints.
 Variable D : cppoType.

Variable f : cpoCatType D D.

Fixpoint iter_ n : D := match n with O => PBot | S m => f (iter_ m) end.

Lemma iter_incr : forall n, iter_ n <= f (iter_ n).
elim ; first by apply: leastP.
move => n L. simpl. apply: fmonotonic. by apply L.
Save.

Hint Resolve iter_incr.

Lemma iter_m : monotonic iter_.
move => n n'. elim: n' n.
- move => n. move => L. unfold Ole in L. simpl in L.
  rewrite -> (leqn0 n) in L. by rewrite (eqP L).
- move => n IH n' L. unfold Ole in L. simpl in L. rewrite leq_eqVlt in L.
  case_eq (n' == n.+1) => E ; rewrite E in L. by rewrite (eqP E).
  specialize (IH _ L). by rewrite -> IH ; simpl.
Qed.

Definition iter : natO =-> D := mk_fmono (iter_m).

Definition fixp : D := lub iter.

Lemma fixp_le : fixp <= f fixp.
unfold fixp.
apply Ole_trans with (lub (ocomp f iter)).
- apply: lub_le_compat. move => x. simpl. by apply iter_incr.
- by rewrite -> lub_comp_le.
Save.
Hint Resolve fixp_le.

Lemma fixp_eq : fixp =-= f fixp.
apply: Ole_antisym; first by [].
unfold fixp. rewrite {2} (lub_lift_left iter (S O)).
rewrite -> (fcontinuous f iter). by apply: lub_le_compat => i.
Save.

Lemma fixp_inv : forall g, f g <= g -> fixp <= g.
unfold fixp; intros g l.
apply: lub_le. elim. simpl. by apply: leastP.
move => n L. apply: (Ole_trans _ l). apply: (fmonotonic f). by apply L.
Save.

End Fixpoints.
Hint Resolve fixp_le fixp_eq fixp_inv.

Definition fixp_cte (D:cppoType) : forall (d:D), fixp (const D d) =-= d.
intros; apply fixp_eq with (f:=const D d); red; intros; auto.
Save.
Hint Resolve fixp_cte.

Add Parametric Morphism (D:cppoType) : (@fixp D)
with signature (@Ole _ : ((D:cpoType) =-> D) -> (D =-> D) -> Prop) ++> (@Ole _)
as fixp_le_compat.
move => x y l. unfold fixp.
apply: lub_le_compat. elim ; first by [].
move => n IH. simpl. rewrite -> IH. by apply l.
Qed.
Hint Resolve fixp_le_compat.

Add Parametric Morphism (D:cppoType) : (@fixp D)
with signature (@tset_eq _) ==> (@tset_eq D)
as fixp_eq_compat.
by intros x y H; apply Ole_antisym ; apply: (fixp_le_compat _) ; case: H.
Save.
Hint Resolve fixp_eq_compat.

Lemma fixp_mon (D:cppoType) : monotonic (@fixp D).
move => x y e. by rewrite -> e.
Qed.

Definition Fixp (D:cppoType) : ordCatType (D -=> D) D := Eval hnf in mk_fmono (@fixp_mon D).

Lemma Fixp_simpl (D:cppoType) : forall (f:D =-> D), Fixp D f = fixp f.
trivial.
Save.

Lemma iter_mon (D:cppoType) : monotonic (@iter D).
move => x y l. elim ; first by [].
move => n IH. simpl. rewrite -> IH. by apply l.
Qed.

Definition Iter (D:cppoType) : ordCatType (D -=> D) (fmon_cpoType natO D) :=
  Eval hnf in mk_fmono (@iter_mon D).

Lemma IterS_simpl (D:cppoType) : forall f n, Iter D f (S n) = f (Iter _ f n).
trivial.
Save.

Lemma iterS_simpl (D:cppoType) : forall (f:cpoCatType D D) n, iter f (S n) = f (iter  f n).
trivial.
Save.

Lemma iter_continuous (D:cppoType) :
    forall h : natO =-> D -=> D,
                  iter (lub h) <= lub (Iter D << h).
move => h. elim ; first by apply: leastP.
move => n IH. simpl. rewrite fcont_app_eq. rewrite -> IH. rewrite <- fcont_app_eq.
rewrite fcont_app_continuous. rewrite lub_diag. by apply lub_le_compat => i.
Qed.

Hint Resolve iter_continuous.

Lemma iter_continuous_eq (D:cppoType) :
    forall h : natO =-> (D -=> D),
                  iter (lub h) =-= lub (Iter _ << h).
intros; apply: Ole_antisym; auto.
exact (lub_comp_le (Iter _ (*D*)) h).
Save.


Lemma fixp_continuous (D:cppoType) : forall (h : natO =-> (D -=> D)), 
       fixp (lub h) <= lub (Fixp D << h).
move => h. unfold fixp. rewrite -> iter_continuous_eq.
apply: lub_le => n. simpl.
apply: lub_le => m. simpl. rewrite <- (le_lub _ m). simpl. unfold fixp. by rewrite <- (le_lub _ n).
Save.
Hint Resolve fixp_continuous.

Lemma fixp_continuous_eq (D:cppoType) : forall (h : natO =-> (D -=> D)), 
        fixp (lub h) =-= lub (Fixp D << h).
intros; apply: Ole_antisym; auto.
by apply (lub_comp_le (Fixp D) h).
Save.

Lemma Fixp_cont (D:cppoType) : continuous (@Fixp D).
move => c.
rewrite Fixp_simpl. by rewrite -> fixp_continuous_eq.
Qed.

Definition FIXP (D:cppoType) : (D -=> D) =-> D := Eval hnf in  mk_fcont (@Fixp_cont D).
Implicit Arguments FIXP [D].

Lemma FIXP_simpl (D:cppoType) : forall (f:D=->D), FIXP f = fixp f.
trivial.
Save.

Lemma FIXP_le_compat (D:cppoType) : forall (f g : D =-> D),
            f <= g -> FIXP f <= FIXP g.
move => f g l. by rewrite -> l.
Save.
Hint Resolve FIXP_le_compat.

Lemma FIXP_eq (D:cppoType) : forall (f:D=->D), FIXP f =-= f (FIXP f).
intros; rewrite FIXP_simpl.
by apply: (fixp_eq).
Save.
Hint Resolve FIXP_eq.

Lemma FIXP_com: forall E D (f:E =-> (D -=> D)) , FIXP << f =-= ev << <| f, FIXP << f |>.
intros E D f. apply: fmon_eq_intro. intros e. simpl. by rewrite {1} fixp_eq.
Qed.

Lemma FIXP_inv (D:cppoType) : forall (f:D=->D)(g : D), f g <= g -> FIXP f <= g.
intros; rewrite FIXP_simpl; apply: fixp_inv; auto.
Save.

(** *** Iteration of functional *)
Lemma FIXP_comp_com (D:cppoType) : forall (f g:D=->D),
       g << f <= f << g-> FIXP g <= f (FIXP g).
intros; apply FIXP_inv.
apply Ole_trans with (f (g (FIXP g))).
assert (X:=H (FIXP g)). simpl. by apply X.
apply: fmonotonic.
case (FIXP_eq g); trivial.
Save.

Lemma FIXP_comp (D:cppoType) : forall (f g:D=->D),
       g << f <= f << g -> f (FIXP g) <= FIXP g -> FIXP (f << g) =-= FIXP g.
intros; apply: Ole_antisym.
- apply FIXP_inv. simpl.
  apply Ole_trans with (f (FIXP g)) ; last by []. by rewrite <- (FIXP_eq g).
- apply: FIXP_inv.
  assert (g (f (FIXP  (f << g))) <= f (g (FIXP  (f << g)))).
  specialize (H (FIXP (f << g))). apply H.
  case (FIXP_eq (f<<g)); intros.
  apply Ole_trans with (2:=H3).
  apply Ole_trans with (2:=H1).
  apply: fmonotonic.
  apply FIXP_inv. simpl. apply: fmonotonic.
  apply Ole_trans with (1:=H1); auto.
Save.

Fixpoint fcont_compn (D:cppoType) (f:D =->D) (n:nat) {struct n} : D =->D := 
             match n with O => f | S p => fcont_compn f p << f end.

Add Parametric Morphism (D1 D2 D3 : cpoType) : (@ccomp D1 D2 D3)
with signature (@Ole (D2 -=> D3) : (D2 =-> D3) -> (D2 =-> D3) -> Prop ) ++> (@Ole (D1 -=> D2)) ++> (@Ole (D1 -=> D3)) 
as fcont_comp_le_compat.
move => f g l h k l' x. simpl. rewrite -> l. by rewrite -> l'.
Save.

Lemma fcont_compn_com (D:cppoType) : forall (f:D =->D) (n:nat), 
            f << (fcont_compn f n) <= fcont_compn f n << f.
induction n; first by [].
simpl fcont_compn. rewrite -> comp_assoc. by apply: (fcont_comp_le_compat _ (Ole_refl f)).
Save.

Lemma FIXP_compn (D:cppoType) : 
     forall  (f:D =->D) (n:nat), FIXP (fcont_compn f n) =-= FIXP f.
move => f. case ; first by []. simpl.
move => n. apply: FIXP_comp ; first by apply fcont_compn_com.
elim: n. simpl. by rewrite <- (FIXP_eq f).
move => n IH. simpl. rewrite <- (FIXP_eq f). by apply IH.
Save.

Lemma fixp_double (D:cppoType) : forall (f:D=->D), FIXP (f << f) =-= FIXP f.
intros; exact (FIXP_compn f (S O)).
Save.


(** *** Induction principle *)
(*=Adm *)
Definition admissible (D:cpoType) (P:D -> Prop) := 
             forall f : natO =-> D, (forall n, P (f n)) -> P (lub f).
Lemma fixp_ind (D:cppoType) : forall  (F: D =-> D)(P:D -> Prop),
             admissible P -> P PBot -> (forall x, P x -> P (F x)) -> P (fixp F). (*CLEAR*)
move => F P Adm B I.
apply Adm. by elim ; simpl ; auto.
Qed.
(*CLEARED*)
(*=End *)

Definition admissibleT (D:cpoType) (P:D -> Type) :=
          forall f : natO =-> D, (forall n, P (f n)) -> P (lub f).

Section SubCPO.
Variable D E:cpoType.
Variable P : D -> Prop.
Variable I:admissible P.

Definition Subchainlub (c:natO =-> (sub_ordType P)) : sub_ordType P.
exists (@lub D (Forgetm P << c)).
unfold admissible in I. specialize (@I (Forgetm P << c)).
apply I. intros i. simpl. case (c i). auto.
Defined.

Lemma subCpoAxiom : CPO.axiom Subchainlub.
intros c e n. unfold Subchainlub. split. case_eq (c n). intros x Px cn.
refine (Ole_trans _ (@le_lub _ (Forgetm P << c) n)).
simpl. rewrite cn. auto.
intros C. simpl.
case_eq e. intros dd pd de.
refine (lub_le _). intros i. simpl. specialize (C i).
case_eq (c i). intros d1 pd1 cn. rewrite cn in C.
simpl in C. rewrite de in C. auto.
Qed.

Canonical Structure sub_cpoMixin := CpoMixin subCpoAxiom.
Canonical Structure sub_cpoType := Eval hnf in CpoType sub_cpoMixin.

Lemma InheritFun_cont (f:E =-> D) (p:forall d, P (f d)) : continuous (InheritFunm _ p).
move => c. simpl. unfold Ole. simpl. rewrite (fcontinuous f). by apply lub_le_compat => i.
Qed.

Definition InheritFun (f:E =-> D) (p:forall d, P (f d)) : E =-> sub_cpoType :=
  Eval hnf in mk_fcont (InheritFun_cont p).

Lemma InheritFun_simpl (f:E =-> D) (p:forall d, P (f d)) d : InheritFun p d = InheritFunm _ p d.
by [].
Qed.

Lemma Forgetm_cont : continuous (Forgetm P).
by move => c.
Qed.

Definition Forget : sub_cpoType =-> D := Eval hnf in mk_fcont Forgetm_cont.

Lemma forgetlub (c:natO =-> (sub_ordType P)) : 
  Forget (Subchainlub c) = (@lub D (Forgetm P << c)).
auto.
Qed.

Lemma ForgetP d : P (Forget d).
intros. case d. auto.
Qed.

End SubCPO.

Lemma Forget_leinj: forall (D:cpoType) (P:D -> Prop) (I:admissible P) (d:sub_cpoType I) e, Forget I d <= Forget I e -> d <= e.
intros D P I d e. case e. clear e. intros e Pe. case d. clear d. intros d Pd.
auto.
Qed.

Hint Resolve Forget_leinj.

Lemma Forget_inj : forall (D:cpoType) (P:D -> Prop) (I:admissible P) (d:sub_cpoType I) e, Forget I d =-= Forget I e -> d =-= e.
intros. by split ; case: H ; case: d ; case: e.
Qed.

Hint Resolve Forget_inj.

Lemma Forget_leinjp: forall (D E:cpoType) (P:D -> Prop) (I:admissible P) (d:E =-> sub_cpoType I) e,
      Forget I << d <= Forget I << e -> d <= e.
intros D E P I d e C x. specialize (C x). simpl in C. unfold FCont.fmono. simpl.
case: (e x) C => e' Pe. case: (d x) => d' Pd l. by apply l.
Qed.

Lemma Forget_injp: forall (D E:cpoType) (P:D -> Prop) (I:admissible P) (d:E =-> sub_cpoType I) e,
      Forget I << d =-= Forget I << e -> d =-= e.
intros D E P I d e C.
apply: fmon_eq_intro. intros x. assert (CC:=fmon_eq_elim C x). simpl in CC.
unfold FCont.fmono. simpl. clear C.
case: (e x) CC. clear e. intros e Pe. case (d x). clear d. intros d Pd.
auto.
Qed.

Lemma InheritFun_eq_compat D E Q Qcc f g X XX : f =-= g ->
    (@InheritFun D E Q Qcc f X) =-= (@InheritFun D E Q Qcc g XX).
intros. refine (fmon_eq_intro _). intros d. have A:=fmon_eq_elim H d. clear H. by split ; case: A.
Qed.

Lemma ForgetInherit (D E:cpoType) (P:D -> Prop) PS f B : Forget PS << @InheritFun D E P PS f B =-= f.
by refine (fmon_eq_intro _).
Qed.

Lemma InheritFun_comp: forall D E F P I (f:E =-> F) X (g:D =-> E) XX,
      @InheritFun F _ P I f X << g =-= @InheritFun _ _ P I (f << g) XX.
intros. refine (fmon_eq_intro _). intros d. simpl.
split ; simpl ; by [].
Qed.

