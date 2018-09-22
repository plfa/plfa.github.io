(*==========================================================================
  Definition of fixpoints and associated lemmas
  ==========================================================================*)
Require Import PredomCore.
Require Import PredomProd.
Require Import PredomLift.

Set Implicit Arguments.
Unset Strict Implicit.

(** ** Fixpoints *)

Section Fixpoints.
 Variable D : cpo.
 Context {dp : Pointed D}.

(* Variable D: cpo. *)
Variable f : D -m>D.

Hypothesis fcont : continuous f. 

Fixpoint iter_ n (* D [Pointed D] (f : D -m> D) *) : D := match n with O => PBot | S m => f (iter_ m (* f *)) end.

Lemma iter_incr (* D [Pointed D] (f : D -m> D)*) : forall n, iter_ n (* f *) <= f (iter_ n (*f *)).
induction n; simpl; auto.
(* apply Pleast. *)
Save.

Hint Resolve iter_incr.

Definition iter : natO -m> D.
exists iter_; red; intros.
induction H; simpl; auto.
apply Ole_trans with (iter_ m); auto.
Defined.

Definition fixp : D := lub iter.

Lemma fixp_le : fixp <= f fixp.
unfold fixp.
apply Ole_trans with (lub (fmon_comp f iter)); auto.
Save.
Hint Resolve fixp_le.

Lemma fixp_eq : fixp == f fixp.
apply Ole_antisym; auto.
unfold fixp.
apply Ole_trans with (1:= fcont iter).
rewrite (lub_lift_left iter (S O)); auto.
Save.

Lemma fixp_inv : forall g, f g <= g -> fixp <= g.
unfold fixp; intros.
apply lub_le.
induction n; intros; auto.
simpl; apply Ole_trans with (f g); auto.
Save.

End Fixpoints.
Hint Resolve fixp_le fixp_eq fixp_inv.


Definition fixp_cte D {pd:Pointed D} : forall (d:D), fixp (fmon_cte D d) == d.
intros; apply fixp_eq with (f:=fmon_cte D d); red; intros; auto.
unfold fmon_cte at 1; simpl.
apply (le_lub (fmon_comp (fmon_cte D (O2:=D) d) c) (O)); simpl; auto.
Save.
Hint Resolve fixp_cte.


Lemma fixp_le_compat D {pd:Pointed D} : forall (*(D:cpo)*) (f g : D-m>D), f<=g -> fixp f <= fixp g.
intros; unfold fixp.
apply lub_le_compat.
intro n; induction n; simpl; auto.
apply Ole_trans with (g (iter_ (D:=D) f n)); auto.
Save.
Hint Resolve fixp_le_compat.


Add Parametric Morphism D {pd : Pointed D} : (@fixp D pd)
with signature (@Oeq (D -m>D)) ==> (@Oeq D)
as fixp_eq_compat.
intros; apply Ole_antisym; auto.
Save.
Hint Resolve fixp_eq_compat.

Definition Fixp D {pd: Pointed D} : (D-m>D) -m> D.
intros; exists (@fixp D pd (* (D:=D) *)).
auto.
Defined. 

Lemma Fixp_simpl D {pd:Pointed D} : forall (* (D:cpo)*) (f:D-m>D), Fixp f = fixp f.
trivial.
Save.

Definition Iter D {pd:Pointed D} : (D-M->D) -m> (natO -M->D).
intros; exists (fun (f:D-M->D) => iter (D:=D) f); red; intros.
intro n; induction n; simpl; intros; auto.
apply Ole_trans with (y (iter_ (D:=D) x n)); auto.
Defined.

Lemma IterS_simpl D {pd:Pointed D} : forall (* (D:cpo)*) f n, Iter f (S n) = f (Iter f n).
trivial.
Save.

Lemma iterS_simpl D {pd:Pointed D} : forall (* (D:cpo)*) f n, iter f (S n) = f (iter  f n).
trivial.
Save.

Lemma iter_continuous D {pd:Pointed D} :(* forall (D:cpo), *)
    forall h : natO -m> (D-M->D), (forall n, continuous (h n)) -> 
                  iter (lub h) <= lub (Iter (* D*) @ h).
red; intros; intro k.
induction k; auto.
(* botbot above just so auto works here *)

rewrite iterS_simpl.
apply Ole_trans with (lub h  (lub (c:=natO -M-> D) (Iter (*D*) @ h) k)); auto.
repeat (rewrite fmon_lub_simpl).
apply Ole_trans with
       (lub (c:=D) (lub (c:=natO-M->D) (double_app h ((Iter (* D*) @ h) <_> k)))).
apply lub_le_compat; simpl; intros.
apply Ole_trans with (lub ((h x)@((Iter (*D*) @ h) <_> k))); auto.
apply Ole_trans 
  with (lub (fmon_diag  (double_app h ((Iter (*D*) @ h) <_> k)))); auto.
case (double_lub_diag (double_app h ((Iter (*D*) @ h) <_> k))); intros L _.
apply Ole_trans with (1:=L); auto.
Save.

Hint Resolve iter_continuous.

Lemma iter_continuous_eq D {pd:Pointed D} :
    forall h : natO -m> (D-M->D), (forall n, continuous (h n)) -> 
                  iter (lub h) == lub (Iter (* D*) @ h).
intros; apply Ole_antisym; auto.
exact (lub_comp_le (Iter (*D*)) h).
Save.


Lemma fixp_continuous D {pd:Pointed D} : forall (* (D:cpo)*) (h : natO -m> (D-M->D)), 
       (forall n, continuous (h n)) -> fixp (lub h) <= lub (Fixp (*D*) @ h).
intros; unfold fixp.
rewrite (iter_continuous_eq H).
simpl; rewrite <- lub_exch_eq; auto.
Save.
Hint Resolve fixp_continuous.

Lemma fixp_continuous_eq D {pd:Pointed D} : forall (h : natO -m> (D -M-> D)), 
       (forall n, continuous (h n)) -> fixp (lub h) == lub (Fixp (*D*) @ h).
intros; apply Ole_antisym; auto.
exact (lub_comp_le (D1:=D -M-> D) (Fixp (*D*)) h).
Save.

Definition FIXP (D:cpo) {p:Pointed D} : (D-C->D) -c> D.
intros D p.
exists (Fixp @ (Fcontit D D)).
unfold continuous.
intros h.
rewrite fmon_comp_simpl.
rewrite Fixp_simpl.
apply Ole_trans with (fixp (D:=D) (lub (c:=D-M->D) (Fcontit D D@h))); auto.
apply Ole_trans with  (lub (Fixp (*D*) @ (Fcontit D D@h))); auto.
apply fixp_continuous; intros n.
change (continuous (D1:=D) (D2:=D) (fcontit (h n))); auto.
Defined.

Lemma FIXP_simpl D {pd:Pointed D} : forall (*(D:cpo)*) (f:D-c>D), FIXP (*D*) f = Fixp (*D*) (fcontit f).
trivial.
Save.

Lemma FIXP_le_compat D {pd:Pointed D} : forall (*(D:cpo)*) (f g : D-C->D),
            f <= g -> FIXP (*D*) f <= FIXP (*D*) g.
intros; repeat (rewrite FIXP_simpl); repeat (rewrite Fixp_simpl).
apply fixp_le_compat; auto.
Save.
Hint Resolve FIXP_le_compat.

Add Parametric Morphism (D:cpo) (p:Pointed D) : (@FIXP D p)
with signature (@Ole (D -c> D)) ++> (@Ole D)
as FIXP_leq_compat.
intros; auto.
Qed.

Add Parametric Morphism (D:cpo) (p:Pointed D) : (@FIXP D p)
with signature (@Oeq (D -c> D)) ==> (@Oeq D)
as FIXP_eq_compat.
intros; apply Ole_antisym; auto.
Qed.

Hint Resolve FIXP_eq_compat.
Hint Resolve FIXP_eq_compat_Morphism.

Lemma FIXP_eq D {pd:Pointed D} : forall (f:D-c>D), FIXP (*D*) f == f (FIXP (*D*) f).
intros; rewrite FIXP_simpl; rewrite Fixp_simpl.
apply (fixp_eq (f:=fcontit f)).
auto.
Save.
Hint Resolve FIXP_eq.

Lemma FIXP_com: forall E D (f:E -C-> (D -C-> D)) {pd:Pointed D}, FIXP << f == EV << <| f, FIXP << f |>.
intros E D f P. apply fcont_eq_intro. intros e. repeat (rewrite fcont_comp_simpl).
rewrite FIXP_eq. auto.
Qed.

Lemma FIXP_inv D {pd:Pointed D} : forall (f:D-c>D)(g : D), f g <= g -> FIXP (*D*) f <= g.
intros; rewrite FIXP_simpl; rewrite Fixp_simpl; apply fixp_inv; auto.
Save.

(** *** Iteration of functional *)
Lemma FIXP_comp_com D {pd:Pointed D} : forall (f g:D-c>D),
       g << f <= f << g-> FIXP (*D*) g <= f (FIXP (*D*) g).
intros; apply FIXP_inv.
apply Ole_trans with (f (g (FIXP (*D*) g))).
assert (X:=fcont_le_elim H (FIXP (*D*) g)). repeat (rewrite fcont_comp_simpl in X). apply X.
apply fcont_monotonic.
case (FIXP_eq g); trivial.
Save.

Lemma FIXP_comp D {pd:Pointed D} : forall (f g:D-c>D),
       g << f <= f << g -> f (FIXP (*D*) g) <= FIXP (*D*) g -> FIXP (*D*) (f << g) == FIXP (*D*) g.
intros; apply Ole_antisym.
(* fix f << g <= fix g *)
apply FIXP_inv.
rewrite fcont_comp_simpl.
apply Ole_trans with (f (FIXP (*D*) g)); auto.
(* fix g <= fix f << g *)
apply FIXP_inv.
assert (g (f (FIXP (*D*) (f << g))) <= f (g (FIXP (*D*) (f << g)))).
specialize (H (FIXP (f << g))). repeat (rewrite fcont_comp_simpl in H). apply H.
case (FIXP_eq (f<<g)); intros.
apply Ole_trans with (2:=H3).
apply Ole_trans with (2:=H1).
apply fcont_monotonic.
apply FIXP_inv.
rewrite fcont_comp_simpl.
apply fcont_monotonic.
apply Ole_trans with (1:=H1); auto.
Save.

Fixpoint fcont_compn D {pd:Pointed D} (f:D-c>D) (n:nat) {struct n} : D-c>D := 
             match n with O => f | S p => fcont_compn f p << f end.

Lemma fcont_compn_com D {pd:Pointed D} : forall (f:D-c>D) (n:nat), 
            f << (fcont_compn f n) <= fcont_compn f n << f.
induction n; auto.
simpl fcont_compn.
apply Ole_trans with ((f << fcont_compn (D:=D) f n) << f); auto.
Save.

Lemma FIXP_compn D {pd:Pointed D} : 
     forall  (f:D-c>D) (n:nat), FIXP (fcont_compn f n) == FIXP f.
induction n; auto.
simpl fcont_compn.
apply FIXP_comp.
apply fcont_compn_com.
apply Ole_trans with (fcont_compn (D:=D) f n (FIXP (fcont_compn (D:=D) f n))); auto.
apply Ole_trans with (FIXP (fcont_compn (D:=D) f n)); auto.
Save.

Lemma fixp_double D {pd:Pointed D} : forall (f:D-c>D), FIXP (f << f) == FIXP f.
intros; exact (FIXP_compn f (S O)).
Save.


(** *** Induction principle *)
Definition admissible (D:cpo) (P:D->Prop) := 
          forall f : natO -m> D, (forall n, P (f n)) -> P (lub f).

Definition fixp_ind D { pd : Pointed D} : forall  (F: D -m> D)(P : D-> Prop),
       admissible P -> P PBot -> (forall x, P x -> P (F x)) -> P (fixp F).
intros D pD F P Adm Pb Pc; unfold fixp.
apply Adm. intros n.
induction n; simpl; auto.
Defined.

Definition SubOrd (D:ord) (P:D -> Prop) : ord.
intros D I. exists ({x : tord D | I x})
   (fun (x' y:{x : D | I x}) => match x' with exist x _ => match y with exist y
_ => @Ole D x y end end).
intros x1. case x1. auto.
intros x1. case x1. clear x1. intros x ix y1. case y1. clear y1.
intros y iy z1. case z1. clear z1. intros z iz l1 l2.
apply (Ole_trans l1 l2).
Defined.

Definition SubOrde (D:cpo) (P:D -> Prop) (d:D)  : P d -> SubOrd P.
intros. exists d. auto.
Defined.

Definition InheritFunm (D E:cpo) (Q:E->Prop) (f:D -m> E) (p:forall d, Q (f d)) :
 D -m> SubOrd Q.
intros D E Q f p.
exists (fun d => @SubOrde E Q (f d) (p d)).
unfold monotonic. intros x y lxy. auto.
Defined.

Definition Forgetm D P : (@SubOrd D P) -m> D.
intros D P. exists (fun (O:SubOrd P) => match O with exist x _ => x end).
unfold monotonic. intros x. case x. clear x. intros x px y. case y. clear y.
intros ; auto.
Defined.

Definition Subchainlub (D:cpo) (P:D -> Prop) (I:admissible P) (c:natO -m> (SubOrd
 P)) : SubOrd P.
intros D P I c.
exists (@lub D (Forgetm P @ c)).
unfold admissible in I. specialize (I (Forgetm P @ c)).
apply I. intros i. simpl. case (c i). auto.
Defined.

Definition SubCPO (D:cpo) (P:D -> Prop) (I: admissible P) : cpo.
intros D P I. exists (SubOrd P) (Subchainlub I).
intros c n. unfold Subchainlub.  simpl. case_eq (c n). intros x Px cn.
refine (Ole_trans _ (@le_lub _ (Forgetm P @ c) n)).
simpl. rewrite cn. auto.
intros c d C. unfold Subchainlub. simpl.
case_eq d. intros dd pd de.
refine (lub_le _). intros n. simpl. specialize (C n).
case_eq (c n). intros d1 pd1 cn. rewrite cn in C.
simpl in C. rewrite de in C. auto.
Defined.

Definition InheritFun (D E:cpo) (Q:E -> Prop) (IQ : admissible Q) (f:D -c> E)
                  (p:forall d, Q (f d)) : D -c> SubCPO IQ.
intros. exists (InheritFunm p). unfold continuous.
intros c. simpl.
rewrite lub_comp_eq.
apply lub_le. intros n.
refine (Ole_trans _ (le_lub (Forgetm Q @ (InheritFunm p @ c)) n)).
auto. auto.
Defined.

Lemma InheritFun_simpl: forall (D E:cpo) (Q:E -> Prop) (IQ : admissible Q) (f:D -c> E)
                  (p:forall d, Q (f d)) d, InheritFun IQ p d = InheritFunm p d.
intros. auto.
Qed.

Definition Forget (D:cpo) (P:D -> Prop) (I: admissible P) : (SubCPO I) -c> D.
intros D P I. exists (@Forgetm D P).
unfold continuous. auto.
Defined.

Lemma ForgetP D P fs d : P (@Forget D P fs d).
intros. case d. auto.
Qed.

Add Parametric Morphism (D:cpo) (P:D -> Prop) (I:admissible P) : (@Forget D P I)
with signature (@Ole _) ++> (@Ole _)
as Forget_le_compat.
intros d0 d1 dle. auto.
Qed.

Add Parametric Morphism (D:cpo) (P:D -> Prop) (I:admissible P) : (@Forget D P I)
with signature (@Oeq _) ==> (@Oeq _)
as Forget_eq_compat.
intros d0 d1 dle. split ; auto.
Qed.

Lemma Forget_leinj: forall (D:cpo) (P:D -> Prop) (I:admissible P) (d:SubCPO I) e, Forget I d <= Forget I e -> d <= e.
intros D P I d e. case e. clear e. intros e Pe. case d. clear d. intros d Pd.
auto.
Qed.

Hint Resolve Forget_leinj.

Lemma Forget_inj : forall (D:cpo) (P:D -> Prop) (I:admissible P) (d:SubCPO I) e, Forget I d == Forget I e -> d == e.
intros. split ; auto.
Qed.

Hint Resolve Forget_inj.

Lemma InheritFun_eq_compat D E Q Qcc f g X XX : Oeq f g ->
    (@InheritFun D E Q Qcc f X) == (@InheritFun D E Q Qcc g XX).
intros. refine (fcont_eq_intro _). intros d. auto.
Qed.

Lemma ForgetInherit (D E:cpo) (P:D -> Prop) PS f B : Forget PS << @InheritFun E D P PS f B == f.
intros D E P PS f B.
refine (fcont_eq_intro _). intros d.
rewrite fcont_comp_simpl. rewrite InheritFun_simpl.
simpl. auto.
Qed.

Lemma InheritFun_comp: forall D E F P I (f:E -C-> F) X (g:D -C-> E) XX,
      @InheritFun _ F P I f X << g == @InheritFun _ F P I (f << g) XX.
intros. refine (fcont_eq_intro _). intros d. repeat (rewrite fcont_comp_simpl).
split ; auto.
Qed.
