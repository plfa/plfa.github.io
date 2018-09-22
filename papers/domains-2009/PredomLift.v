(*==========================================================================
  Lifiting
  ==========================================================================*)
Require Import utility.
Require Import PredomCore.
Set Implicit Arguments.
Unset Strict Implicit.

(** ** Lifting *)

Section Lift_cpo.
Variable D : cpo.

(** ** Definition of underlying stream type *)

(** printing Eps %\eps% *)
(** printing Val %\val% *)
(** printing Stream %\Stream% *)
CoInductive Stream : Type := Eps : Stream -> Stream | Val : D -> Stream.

Lemma DL_inv : forall d, d = match d with Eps x => Eps x | Val d => Val d end.
destruct d; auto.
Save.
Hint Resolve DL_inv.

(** ** Removing Eps steps *)

Definition pred d : Stream := match d with Eps x => x | Val _ => d end.

Fixpoint pred_nth (d:Stream) (n:nat) {struct n} : Stream := 
    match n with 0 => d
              |S m => match d with Eps x => pred_nth x m
                                 | Val _ => d
                      end
    end.

Lemma pred_nth_val : forall x n, pred_nth (Val x) n = Val x.
destruct n; simpl; trivial.
Save.
Hint Resolve pred_nth_val.

Lemma pred_nth_Sn_acc : forall n d, pred_nth d (S n) = pred_nth (pred d) n.
destruct d; simpl; auto.
Save.

Lemma pred_nth_Sn : forall n d, pred_nth d (S n) = pred (pred_nth d n).
induction n; intros; auto.
destruct d.
exact (IHn d).
rewrite pred_nth_val; rewrite pred_nth_val; simpl; trivial.
Save.

(** ** Order *)
CoInductive DLle : Stream -> Stream -> Prop :=
 |  DLleEps : forall x y,  DLle x y -> DLle (Eps x) (Eps y)
 |  DLleEpsVal : forall x d,  DLle x (Val d) -> DLle (Eps x) (Val d)
 |  DLleVal : forall d d' n y, pred_nth y n = Val d' -> d <= d' -> DLle (Val d) y.

Hint Constructors DLle.

Lemma DLle_rec : forall R : Stream -> Stream -> Prop,
   (forall x y, R (Eps x) (Eps y) -> R x y) ->
   (forall x d, R (Eps x) (Val d) -> R x (Val d)) ->
   (forall d y, R (Val d) y -> exists n, exists d', pred_nth y n = Val d' /\ d <= d')
   -> forall x y, R x y -> DLle x y.
intros R REps REpsVal RVal; cofix; destruct x; intros.
destruct y; intros.
apply DLleEps; apply DLle_rec; auto.
apply DLleEpsVal; apply DLle_rec; auto.
case (RVal t y H); intros n H1.
destruct H1.
apply DLleVal with x n; auto.
intuition.
intuition.
Save.

(** *** Properties of the order *)

Lemma DLle_refl : forall x, DLle x x.
intros x. apply DLle_rec with (R:= fun x y => forall n, pred_nth x n = pred_nth y n) ; try (clear x).
intros x y C n. specialize (C (S n)). simpl in C. auto.
intros x d C n. specialize (C (S n)). simpl in C. rewrite C. case n ; auto.
intros d y C. exists 0. exists d. simpl. specialize (C 0). simpl in C. auto.
intros n ; auto.
Save.
Hint Resolve DLle_refl.

Lemma DLvalval : forall d x, DLle (Val d) x -> 
 exists n, exists d', pred_nth x n = Val d' /\ d<=d'.
intros d x H.
inversion H.
exists n; exists d'.
intuition.
Qed.

Lemma pred_nth_epsS n x y: Eps y = pred_nth x n -> y = pred_nth x (S n).
intros n. induction n. intros x y E. simpl in E. rewrite <- E. simpl. auto.
intros x. case x ; clear x. intros x y. intros E. simpl in E. specialize (IHn _ _ E). auto.
intros x y. simpl. intros incon. inversion incon.
Qed.

Lemma pred_nth_valS n d y: Val d = pred_nth y n -> Val d = pred_nth y (S n).
intros n ; induction n. intros d y E. simpl in E. rewrite <- E. auto.
intros d y. case y ; clear y. intros y E. simpl in E. specialize (IHn _ _ E). rewrite IHn. auto.
intros dd E. simpl in E. inversion E. rewrite <- H0 in *. clear dd H0 E. simpl. auto.
Qed.

Lemma pred_nth_comp y : forall m0 n1 m1 : nat,
   m0 = n1 + m1 -> pred_nth y m0 = pred_nth (pred_nth y n1) m1.
intros y m0. induction m0. intros n1 m1. simpl. intros E. assert (n1 = 0) by omega. rewrite H in *.
simpl. assert (m1 = 0) as A by omega. rewrite A in *. auto.
intros n1 m1. case m1 ; clear m1. case n1 ; clear n1. simpl. intros incon. inversion incon.
intros m1 E. assert (m0 = m1) as EE by omega. rewrite EE in *. auto.
intros m1. intros E. assert (m0 = n1 + m1) as A by omega. specialize (IHm0 _ _ A).
clear E A. generalize IHm0. clear IHm0. case_eq (pred_nth y m0).
intros d E. rewrite <- (pred_nth_epsS (sym_eq E)). intros EE. rewrite (pred_nth_epsS EE). auto.
intros d E EE.
rewrite <- (pred_nth_valS (sym_eq E)). rewrite (pred_nth_valS EE). auto.
Qed.

Lemma DLle_pred_nth x y n : DLle x y -> DLle (pred_nth x n) (pred_nth y n).
intros x y n. induction n. simpl. auto. intros C.
specialize (IHn C). inversion IHn.
rewrite (pred_nth_epsS H) in *. clear H x0. rewrite (pred_nth_epsS H0) in *. clear y0 H0. auto.
rewrite (pred_nth_epsS H) in *. clear H x0. rewrite H0 in *.
rewrite <- (pred_nth_valS H0). rewrite <- H0 in *. auto.
rewrite <- H2 in *. rewrite <- H in *.
rewrite <- (pred_nth_valS H).
apply DLleVal with (n:=n0) (d':=d').
rewrite H2 in H0. rewrite <- (@pred_nth_comp y (n+n0)) in H0 ; auto.
rewrite <- (@pred_nth_comp y (S n+n0)) ; auto. rewrite (pred_nth_valS (sym_eq H0)). auto. auto.
Qed.

Lemma DLleEps_right : forall x y,  DLle x y -> DLle x (Eps y).
intros x y C. apply DLle_rec with (R:= fun x y => forall n, DLle (pred_nth x n) (pred_nth y (S n))).
clear x y C. intros x y C n. specialize (C (S n)). auto.
clear x y C. intros x y C n. specialize (C (S n)). auto.
clear x y C. intros d y C. specialize (C 0).
assert (DLle (Val d) (pred_nth y 1)) as CC by auto. clear C.
destruct (DLvalval CC) as [n [dd [X Y]]]. exists (S n). exists dd. split ; auto.
generalize X. clear X. destruct y. simpl. auto. simpl. case n ; auto.
intros n. simpl.
apply DLle_pred_nth ; auto.
Qed.
Hint Resolve DLleEps_right.

Lemma DLleEps_left : forall x y,  DLle x y -> DLle (Eps x) y.
intros x y C. apply DLle_rec with (R:= fun x y => forall n, DLle (pred_nth x (S n)) (pred_nth y n)).
clear x y C. intros x y C n. specialize (C (S n)). auto.
clear x y C. intros x y C n. specialize (C (S n)). destruct n ; auto.
clear x y C. intros d y C. specialize (C 0).
simpl in C.
destruct (DLvalval C) as [n [dd [X Y]]]. exists n. exists dd. split ; auto.
intros n. simpl. apply DLle_pred_nth ; auto.
Qed.
Hint Resolve DLleEps_left.

Lemma DLle_pred_left : forall x y, DLle x y -> DLle (pred x) y.
destruct x; destruct y; simpl; intros; trivial.
inversion H; auto.
inversion H; trivial.
Save.

Lemma DLle_pred_right : forall x y, DLle x y -> DLle x (pred y).
destruct x; destruct y; simpl; intros; trivial.
inversion H; auto.
inversion H; trivial.
destruct n; simpl in H1.
discriminate H1.
apply DLleVal with d' n; auto.
Save.

Hint Resolve DLle_pred_left DLle_pred_right.

Lemma DLle_pred : forall x y, DLle x y -> DLle (pred x) (pred y).
auto.
Save.

Hint Resolve DLle_pred.

Lemma DLle_pred_nth_left : forall n x y, DLle x y -> DLle (pred_nth x n) y.
induction n; intros.
simpl; auto.
rewrite pred_nth_Sn; auto.
Save.

Lemma DLle_pred_nth_right : forall n x y,
      DLle x y -> DLle x (pred_nth y n).
induction n; intros.
simpl; auto.
rewrite pred_nth_Sn; auto.
Save.

Hint Resolve DLle_pred_nth_left DLle_pred_nth_right.


(* should be called leq *)
Lemma DLleVal_leq : forall x y, DLle (Val x) (Val y) -> x <= y.
intros x y H; inversion H.
destruct n; simpl in H1; injection H1;intro; subst y; auto.
Save.
Hint Immediate DLleVal_leq.

(* New *)
Lemma DLle_leVal : forall x y, x<=y -> DLle (Val x) (Val y).
intros x y H.
apply (DLle_rec (R := fun x' y' => x'=Val x /\ y'=Val y)).
intros.
destruct H0; discriminate.
intros.
destruct H0; discriminate.
intros.
destruct H0.
subst y0.
exists 0.
exists y.
simpl.
split; trivial.
injection H0.
intro; subst d; auto.
auto.
Qed.

Require Import utility.

Lemma DLnvalval : forall n y d z, pred_nth y n = Val d -> DLle y z ->
 exists m, exists d', pred_nth z m = Val d' /\ d <= d'.
induction n.
intros.
dcase y.
intros.
subst y.
simpl in H.
discriminate.
intros.
subst y.
simpl in H.
rewrite H in H0. 
apply (DLvalval H0).

intros.
apply (IHn (pred y) d z).
rewrite <- (pred_nth_Sn_acc).
assumption.
apply DLle_pred_left.
assumption.
Qed.

Lemma DLleEpsn n x z xx : pred_nth x n = Val xx -> DLle (Val xx) z -> DLle x z.
intros n. induction n.
intros x z xx. simpl. intros C. rewrite C. auto.
intros x. case x ; clear x. intros d z xx. simpl. intros C DD.
specialize (IHn _ z _ C DD).
generalize IHn. case z. intros zz CC. apply DLleEps. apply (DLle_pred_right CC).
intros zz CC. apply DLleEpsVal. apply CC.
intros x z xx C. simpl in C. inversion C. auto.
Qed.

Lemma DLle_trans : forall x y z, DLle x y -> DLle y z -> DLle x z.
intros x y z D0 D1.
apply DLle_rec with (R:=fun x z => (forall xx n, pred_nth x n = Val xx -> DLle x z)).
clear x y z D0 D1. intros x y C xx n X.
specialize (C xx (S n) X).
apply (DLle_pred C).

clear x y z D0 D1. intros x y C xx n X.
specialize (C _ (S n) X).
apply (DLle_pred_left C).

intros d yy C.
specialize (C d 0).
destruct (fun Z => DLvalval (C Z)) as [n [dd [ZZ Z]]] ; auto.
exists n. exists dd. split ; auto.

intros xx n C.
destruct (DLnvalval C D0) as [m [yy [P Q]]].
destruct (DLnvalval P D1) as [k [zz [Pz Qz]]].
apply (DLleEpsn C). apply (DLleVal Pz). apply (Ole_trans Q Qz).
Qed.

(** *** Declaration of the ordered set *)
Definition DL_ord : ord.
exists Stream DLle; intros; auto.
apply DLle_trans with y; trivial.
Defined.

Canonical Structure DL_ord.


(** ** Definition of the cpo structure *)

Lemma eq_Eps : forall x, x == Eps x.
intros; apply Ole_antisym; repeat red; auto.
Save.
Hint Resolve eq_Eps.

(** *** Bottom is given by an infinite chain of Eps *)
(** printing DL_bot %\DLbot% *)
CoFixpoint DL_bot : DL_ord := Eps DL_bot.

Lemma DL_bot_eq : DL_bot = Eps DL_bot.
transitivity match DL_bot with Eps x => Eps x | Val d => Val d end; auto.
Save.

Lemma DLless_cond : forall (x y : DL_ord), (forall xx, x == Val xx -> x <= y) -> DLle x y.
intros x y P. apply DLle_rec with (R:=fun x y => forall xx, x == Val xx -> x <= y).
intros d0 d1 IH. intros d00 dv.
rewrite (eq_Eps d0) in dv. rewrite (eq_Eps d0).
specialize (IH _ dv).
rewrite (eq_Eps d1). auto.

intros d0 d1 IH dd dv. rewrite (eq_Eps d0) in dv.
specialize (IH _ dv). rewrite (eq_Eps d0). auto.

intros d0 d1 IH.
specialize (IH _ (Oeq_refl _)).
auto using (DLvalval IH).
apply P.
Qed.

Lemma DL_bot_least : forall x, DL_bot <= x.
intros x. apply DLless_cond.
intros xx [_ C].
destruct (DLvalval C) as [n [dd [P Q]]].
assert False as F. induction n. simpl in P. rewrite DL_bot_eq in P. inversion P.
rewrite DL_bot_eq in P. simpl in P. apply (IHn P). inversion F.
Qed.

(** *** More properties of elements in the lifted domain *)

(* This is essentially the same, when fixed up, as DLvalval that I proved above
   I've repeated it here, though
*)
Lemma DLle_Val_exists_pred : 
      forall x d, Val d <= x -> exists k, exists d', pred_nth x k = Val d'
            /\ d <= d'.
intros x d H; inversion H; eauto.
Save.

Lemma Val_exists_pred_le : 
      forall x d, (exists k, pred_nth x k = Val d) -> Val d <= x.
destruct 1; intros.
apply DLleVal with d x0; trivial.
Save.
Hint Immediate DLle_Val_exists_pred Val_exists_pred_le.

Lemma Val_exists_pred_eq : 
      forall x d, (exists k, pred_nth x k = Val d) -> (Val d:DL_ord) == x.
intros.
split.
auto.
destruct H.
rewrite <- H.
apply DLle_pred_nth_right.
auto.
Save.

(** *** Construction of least upper bounds *)

Definition isEps x := match x with Eps _ => True | _ => False end.

Lemma isEps_Eps : forall x, isEps (Eps x).
repeat red; auto.
Save.

Lemma not_isEpsVal : forall d, ~ (isEps (Val d)).
repeat red; auto.
Save.
Hint Resolve isEps_Eps not_isEpsVal.

Lemma isEps_dec : forall x, {d:D|x=Val d}+{isEps x}.
destruct x; auto.
left.
exists t; auto.
Defined.

(* Slightly more radical rewrite, trying to use equality *)

Lemma allvalsfromhere : forall (c:natO -m> DL_ord) n d i,
  c n == Val d -> exists d', c (n+i) == Val d' /\ d <= d'.
intros c n d i (Hnv1,Hnv2).
assert (((Val d):DL_ord) <= c (n+i)).
apply Ole_trans with (c n); auto.
apply fmonotonic.
intuition.
destruct (DLle_Val_exists_pred H) as [k [d' Hkd']].
exists d'.
split.
apply Oeq_sym; apply Val_exists_pred_eq; firstorder.
tauto.
Qed.

Definition hasVal x := exists j, exists d, pred_nth x j = Val d.
Definition valuable := {x | hasVal x}.

Definition projj : valuable -> DL_ord.
intro.
destruct X.
exact x.
Defined.


(* Redoing extract using constructive epsilon *)
Require Import ConstructiveEpsilon.


Definition findindexandval (x : valuable) : {kd | match kd with (k,d) => (pred_nth (projj x) k) = Val d end}.
intro x; destruct x.
unfold hasVal in h; simpl.
cut {n | exists d, pred_nth x n = Val d}.
intro; destruct H.
dcase (pred_nth x x0).
intros. rewrite H in e. absurd (exists d, Eps s = Val d).
intro.
destruct H0.
discriminate.
assumption.
intros.
exists (x0,t).
assumption.

apply constructive_indefinite_description_nat.
intro.
case (isEps_dec (pred_nth x x0)).
intro; left.
destruct s.
exists x1.
assumption.
intro H; right.
intro; destruct H0.
rewrite H0 in H; simpl in H.
contradiction.
exact h.
Defined.


Definition extract (x : valuable) : D.
intro x; generalize (findindexandval x); intro.
destruct X.
destruct x0.
exact t.
Defined.


Lemma extractworks : forall x, projj x == Val (extract x).
intro x; unfold extract.
dcase (findindexandval x).
intros.
destruct x0.
apply Oeq_sym.
apply Val_exists_pred_eq.
exists n.
assumption.
Qed.


Lemma vinj : forall d d', Val d == Val d' -> d == d'.
intros d d' (H1,H2).
split; auto.
Qed.

Lemma vleinj : forall d d', Val d <= Val d' -> d <= d'.
auto.
Qed.

Lemma extractmono : forall (x y : valuable), (projj x) <= (projj y) -> extract x <= extract y.
intros x y H.
apply vleinj.
rewrite <- (extractworks x).
rewrite <- (extractworks y).
assumption.
Qed.

(* This is the simpler one that just takes an equality *)

Lemma eqValpred : forall x d, x == Val d -> exists k, exists d', pred_nth x k = Val d' /\ d==d'.
intros.
destruct H as (H1,H2).
destruct (DLle_Val_exists_pred H2) as [k [d' HH]].
exists k; exists d';split.
tauto.
split.
tauto.
apply vleinj.
destruct HH.
rewrite <- H.
auto.
Qed.

Definition makechain (c:natO -m> DL_ord) k d (Hck:c k == Val d) : nat -> D.
intros c k d Hck i.
eapply extract.
exists (c (k+i)).
destruct (allvalsfromhere i Hck) as [d' [Hd' HHH]].
unfold hasVal.
generalize (eqValpred Hd').
firstorder.
Defined.

Definition makechainm (c:natO -m> DL_ord) k d (Hck:c k == Val d) : natO -m> D.
intros.
exists (makechain Hck).
unfold monotonic.
intros.
unfold makechain.
apply extractmono.
simpl.
apply (fmonotonic c).
intuition.
Defined.


Definition cpred (c:natO -m> DL_ord) : natO-m>DL_ord.
intro c; exists (fun n => pred (c n)); red.
intros x y H; apply DLle_pred.
apply (fmonotonic c); auto.
Defined.

Lemma fValIdx : forall (c:natO -m> DL_ord) (n : nat), 
        {dk: (D*nat)%type | match dk with (d,k) => k<n /\ c k == Val d end} + {forall k, k<n -> isEps (c k)}.
induction n.
right; intros. destruct (lt_n_O k H).
case IHn; intros.
destruct s as [(d,k) [H ck]].
left; exists (d,k).
auto with arith.

case (isEps_dec (c n)); intros.
destruct s as [d H]. left.
exists (d,n); intuition.

right; intros.
assert (L:=lt_n_Sm_le _ _ H). destruct L ; auto with arith.
Defined.

Definition createchain (c:natO -m> DL_ord) (n:nat) 
  (X:{dk: (D*nat)%type | match dk with (d,k) => k<n /\ c k == Val d end}) :
   (natO -m> D) :=
match X with | exist (d,k) (conj Hk Hck) => @makechainm c k d Hck
end.

CoFixpoint DL_lubn (c:natO-m> DL_ord) (n:nat) : DL_ord := 
    match fValIdx c n with inleft X => Val (lub (createchain X))
                                |  inright _  => Eps (DL_lubn (cpred c) (S n))
    end.

Lemma DL_lubn_inv : forall (c:natO-m> DL_ord) (n:nat), DL_lubn c n = 
     match fValIdx c n with inleft X => Val (lub (createchain X))
                                |  inright _  => Eps (DL_lubn (cpred c) (S n))
    end.
intros; rewrite (DL_inv (DL_lubn c n)).
simpl; case (fValIdx c n); trivial. 
Qed.

Lemma makechainworks : forall (c:natO -m> DL_ord) k dk (H2:c k == Val dk) i (d:D), c (k+i) == (Val d) -> makechain H2 i == d.
intros.
apply vinj.
rewrite <- H.
apply Oeq_sym.
unfold makechain.
rewrite <- extractworks.
simpl.
auto.
Qed.

Lemma chainluble : forall (c:natO -m> DL_ord) k dk (Hkdk : c k == Val dk) k' dk' (Hkdk': c k' == Val dk'), 
   lub (makechainm Hkdk) <= lub (makechainm Hkdk').
intros;apply lub_le.
intro n.
assert (Hkn := allvalsfromhere n Hkdk).
destruct Hkn as (dkn,(Hckn,Hdkdkn)).
setoid_replace (makechainm Hkdk n) with (dkn).
destruct (allvalsfromhere (n+k) Hkdk') as [dkk'n [Hckk'n Hddd]].
apply Ole_trans with dkk'n.
apply vleinj; rewrite <- Hckn; rewrite <- Hckk'n.
apply fmonotonic.
intuition.
setoid_replace dkk'n with (makechainm Hkdk' (n+k)).
apply le_lub.
unfold makechainm.
apply Oeq_sym; apply makechainworks.
assumption.
unfold makechainm; apply makechainworks.
assumption.
Qed.

Lemma chainlubinv : forall (c:natO -m> DL_ord) k dk (Hkdk : c k == Val dk) k' dk' (Hkdk': c k' == Val dk'), 
   lub (makechainm Hkdk) == lub (makechainm Hkdk').
intros;split;apply chainluble.
Qed.

Lemma pred_lubn_Val : forall (d:D)(n k p:nat) (c:natO-m> DL_ord),
             (n <k+p)%nat -> pred_nth (c n) k = Val d
                                   -> exists d', DL_lubn c p == Val d'.

induction k; intros.
(* Base case *)
rewrite (DL_lubn_inv c p); simpl.
simpl in H0.
case (fValIdx c p); intros.
case s; intros (d',k) (H1,H2); auto.
simpl.
exists (lub (makechainm H2)).
auto.

absurd (c n = Val d).
intro Hsilly.
assert (isEps (c n)).
apply i.
omega.
rewrite Hsilly in H1.
simpl in H1.
tauto.
assumption.

(* Induction *)
rewrite (DL_lubn_inv c p).
case (fValIdx c p); intros.
unfold createchain.
dependent inversion s.
simpl.
destruct x.
dependent inversion y.
exists (lub (makechainm o)).
auto.

assert (n<k + S p).
omega.
assert (pred_nth (cpred c n) k = Val d).
unfold cpred.
simpl.
rewrite <- pred_nth_Sn_acc.
assumption.
specialize (IHk (S p) (cpred c) H1 H2 ).
destruct IHk as (d',IH); exists d'.
rewrite <-IH; auto.
Qed.

Lemma eqDLeq : forall d d', d == d' -> Val d == (Val d').
  intros.
  destruct H; split; apply DLle_leVal.
  assumption.
  assumption.
Qed.

Lemma predeq : forall x, x == pred x.
  intro; split; auto.
Qed.

Lemma cpredsamelub : forall (c:natO -m> DL_ord) k dk (H1:c k == Val dk) (H2: (cpred c) k == Val dk),
                      lub (makechainm H1) == lub (makechainm H2).
intros; split.
apply lub_le; intro.
setoid_replace (makechainm H1 n) with (makechainm H2 n).
apply le_lub.
assert (Hkn := allvalsfromhere n H1).
destruct Hkn as (dkn,(Hckn,Hdkdkn)).
unfold makechainm; simpl.
setoid_rewrite (makechainworks H1 Hckn).
assert (HH : ((cpred c) (k+n) == Val dkn)).
unfold cpred; simpl.
rewrite <- Hckn.
apply Oeq_sym; apply predeq.
setoid_rewrite (makechainworks H2 HH).
auto.

apply lub_le; intro.
setoid_replace (makechainm H2 n) with (makechainm H1 n).
apply le_lub.
destruct (allvalsfromhere n H2) as (dkn,(Hckn,Hdkdkn)).
unfold makechainm; simpl.
setoid_rewrite (makechainworks H2 Hckn).
assert (HH : ((c) (k+n) == Val dkn)).
unfold cpred in Hckn; simpl in Hckn.
rewrite <- Hckn; apply predeq.
setoid_rewrite (makechainworks H1 HH); auto.
Qed.


Lemma attempt2 : forall kl (c:natO -m> DL_ord) p d, pred_nth (DL_lubn c p) kl = Val d 
                    -> exists k, exists dk, exists Hkdk:c k == Val dk, d == lub (makechainm Hkdk).
induction kl; intros.
rewrite DL_lubn_inv in H; simpl in H.
dcase (fValIdx c p).
intros.
rewrite H0 in H.
destruct s; destruct x; inversion y.

unfold createchain in H.
exists n; exists t.
exists H2.
clear H0.
generalize H.
clear H.
dependent inversion y.
intro.
apply vinj.
rewrite <- H.

apply eqDLeq.
apply chainlubinv.

(* then we get an impossible case *)

Focus 2.
(* this is the tricky one *)
assert (HH := IHkl (cpred c) (S p) d).
dcase (fValIdx c p).
intros.

(* making it up as I go along *)
rewrite DL_lubn_inv in H.
rewrite H0 in H; simpl in H.
clear H0.
destruct s.
destruct x.
generalize H; dependent inversion y; intros.
unfold createchain in H0.
exists n; exists t; exists o.
apply vinj.
rewrite <- H0.
auto.

clear IHkl.
intros.
rewrite DL_lubn_inv in H.
rewrite H0 in H; simpl in H.
specialize (HH H).
(* AHA now we're getting somewhere at last, albeit rather clunkily! *)
destruct HH as (k,(dk,(Hkdk,HH))).
exists k; exists dk.

unfold cpred in Hkdk; simpl in Hkdk.
assert (HHH : c k == Val dk).
rewrite <- Hkdk.
apply predeq.
exists HHH.
rewrite HH.

apply Oeq_sym.
apply cpredsamelub.

(* now back to trivial one *)
intros.
rewrite H0 in H.
discriminate.
Qed.

Lemma pred_nth_sum : forall x m n, pred_nth x (m+n) = pred_nth (pred_nth x m) n.
induction m.
simpl.
intuition.
intro n; replace (S m + n) with (m + S n); intuition.
rewrite IHm.
rewrite (@pred_nth_Sn_acc n (pred_nth x m)).
rewrite pred_nth_Sn.
reflexivity.
Qed.

(* first just wrap pred_lubn_Val to use equality *)
Lemma chainVallubnVal : forall (c:natO -m> DL_ord) n d p, c n == Val d -> exists d', DL_lubn c p == Val d'.
intros.
destruct (eqValpred H) as (k,(d'',(Hcnk,Hdd''))).
apply (pred_lubn_Val (n:=n) (k:=k+n+1) (p:=p) (c:=c) (d:=d'')).
intuition.
replace (k+n+1) with (k+(n+1)).
rewrite pred_nth_sum.
rewrite Hcnk.
auto.
omega.
Qed.

Lemma chainVallubnlub : forall (c:natO -m> DL_ord) n d (H : c n == Val d) p, exists d',  DL_lubn c p == Val d' /\ d' == lub (makechainm H).
intros.
destruct (chainVallubnVal p H) as (d',HH).
exists d'.
split. assumption.
destruct (eqValpred HH) as (k,(d'',(Hk,Hd'd''))).
destruct (attempt2 Hk) as (p',(dp',(Hp',Heq))).
rewrite Hd'd''.
rewrite Heq.
apply chainlubinv.
Qed.


Definition DL_lub (c:natO-m> DL_ord) := DL_lubn c 1.


Lemma DL_lub_upper : forall c:natO-m> DL_ord, forall n, c n <= DL_lub c.
intros c n. apply DLless_cond.
intros d C.
destruct (chainVallubnlub C 1) as [d' [Ln L]].
unfold DL_lub. rewrite Ln.
assert (X:=makechainworks C). specialize (X 0 d). assert (n+0 = n) as A by omega. rewrite A in X. clear A.
specialize (X C). apply Ole_trans with (y:=Val d). auto.
assert (pred_nth (Val d') 0 = Val d') as Y by auto.
apply (DLleVal Y). rewrite L.
apply Ole_trans with (y:=(makechainm (c:=c) (k:=n) (d:=d) C) 0). simpl. auto.
apply le_lub.
Qed.

(* Just realized I should have had Val as a morphism ages ago *)
Add Parametric Morphism : Val
with signature (@Oeq D) ==> (@Oeq DL_ord)
as Val_eq_compat.
intros.
apply eqDLeq.
assumption.
Qed.

Add Parametric Morphism : Val
with signature (@Ole D) ++> (@Ole DL_ord)
as Val_le_compat.
intros.
apply DLle_leVal.
auto.
Qed.

Lemma DLle_Val_exists_eq : forall y d, Val d <= y -> exists d', y == Val d' /\ d <= d'.
intros y d H; inversion H.
exists d'.
split.
symmetry.
apply Val_exists_pred_eq.
exists n; trivial.
assumption.
Qed.


Lemma DL_lub_least : forall (c : natO -m> DL_ord) a, 
                      (forall n, c n <= a) -> DL_lub c <= a.
intros c a C.
apply DLless_cond. intros d X.
destruct (eqValpred X) as [n [dd [P Q]]].
destruct (attempt2 P) as [m [d' [cm Y]]].
apply Ole_trans with (y:= (Val dd)).
refine (proj2 (Val_exists_pred_eq _)). exists n. auto.
assert (Z:= C m). rewrite cm in Z.
destruct (DLvalval Z) as [mm [e [R S]]].
apply (DLleVal R). rewrite Y.
apply lub_le.
intros nn.
assert (A:=makechainworks cm).
specialize (A nn).
clear S Y Z.
destruct (allvalsfromhere nn cm) as [nnv [S T]].
specialize (A _ S). rewrite A. clear A.
assert (a == Val e) as E.
apply Oeq_sym.
apply (Val_exists_pred_eq). exists mm. apply R.
assert (Z := C (m+nn)).
rewrite E in Z. rewrite S in Z. apply (vleinj Z).
Qed.


(** *** Declaration of the lifted cpo *)

Definition DL : cpo.
exists DL_ord  DL_lub; intros.
(* apply DL_bot_least. *)
apply DL_lub_upper.
apply DL_lub_least; trivial.
Defined.

Lemma lubval: forall (c:natO -m> DL) d, lub c == Val d ->
                exists k, exists d', c k == Val d' /\ d' <= d.
intros c d l.
destruct l as [lubval1 lubval2].
destruct (DLle_Val_exists_pred lubval2) as [k xx].
destruct xx as [f' [lubval lf]].
assert (lub c == Val f') as lubval'.
apply Ole_antisym.
eapply Ole_trans. apply lubval1. auto using DLle_leVal.
eapply (DLleVal). apply lubval. apply Ole_refl.
assert (f' <= d).
destruct lubval' as [v1 v2].
assert (Val f' <= Val d).
apply (Ole_trans v2 lubval1).
apply (DLleVal_leq H).
assert (d == f') as feq. auto.
clear H lubval1 lubval2 lf.

assert (xx:=attempt2 lubval).
destruct xx as [n [f0 [chnval lf']]].
exists n. exists f0. split. apply chnval.
assert (w:=makechainworks chnval).
specialize (w 0 f0). assert (n+0 = n) by omega. rewrite H in w.
specialize (w chnval).
destruct w as [_ L2].
refine (Ole_trans L2 (Ole_trans (le_lub (makechainm chnval) 0) _)).
rewrite <- lf'. auto.
Qed.

Lemma DLvalgetchain: forall (c:natO -m> DL) k d, c k == Val d -> exists c':natO -m> D, forall n, c(k+n) == Val (c' n).
intros c k d chk.
exists (makechainm chk).
intros n.
destruct (allvalsfromhere n chk) as [d' [chd ld]].
refine (Oeq_trans chd _).
apply eqDLeq.
apply (Oeq_sym (makechainworks chk chd)).
Qed.

Hint Immediate DLle_leVal.

(*==========================================================================
  Eta
  ==========================================================================*)

Definition eta_m : D -m> DL.
exists (fun (x:D) => Val x).
unfold monotonic.
intros;auto.
Defined.

(** printing eta %\ensuremath{\eta}% *)
Definition eta : D -c> DL.
exists (eta_m).
red.
intro c.
set (LHS := eta_m (lub c)).
unfold DL, DL_lub.
unfold lub.
rewrite DL_lubn_inv.
simpl.
subst LHS.
simpl.
apply DLle_leVal.
apply lub_le; intro n.
setoid_replace (c n) with (makechainm  (c:= eta_m @ c) (k:=0) (d := c 0) (Oeq_refl_eq (refl_equal (Val (c 0)))) n).
apply le_lub.
unfold makechainm.
simpl.
symmetry. apply makechainworks.
simpl.
trivial.
Defined.

Add Parametric Morphism : (@eta)
with signature (@Ole D) ++> (@Ole (DL))
as eta_le_compat.
intros d0 d1 Eq.
assert (monotonic (eta)). auto. apply H.
auto.
Qed.

Add Parametric Morphism : (@eta)
with signature (@Oeq D) ==> (@Oeq (DL))
as eta_eq_compat.
intros d0 d1 Eq. split ; auto.
Qed.

Hint Resolve eta_eq_compat.

End Lift_cpo.

Implicit Arguments eta [D].

(** printing _BOT %\LIFTED% *)
Notation "x '_BOT'" := (DL x) (at level 28).

Instance lift_pointed D : Pointed (D _BOT).
intro D.
exists (DL_bot D).
intro. red. simpl.
apply DL_bot_least.
Defined.

Lemma PBot_app D E {pd:Pointed E} : forall d, @PBot _ (fun_pointed D E) d == PBot.
intros D E pd d. split. case pd. auto.
auto.
Qed.

Lemma PBot_comp D F {pd:Pointed F} : forall E (h:E -C-> D),
            @PBot _ (fun_pointed D F) << h == @PBot _ (fun_pointed E F).
intros D F pd E h. apply fcont_eq_intro.
intros e. rewrite fcont_comp_simpl. rewrite PBot_app. rewrite PBot_app.
auto.
Qed.
