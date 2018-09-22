(**********************************************************************************
 * PredomLift.v                                                                   *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                       *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)

(*==========================================================================
  Lifting
  ==========================================================================*)

Require Import PredomCore.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** ** Lifting *)

Section Lift_type.

(** ** Definition of underlying stream type *)

(** printing Eps %\eps% *)
(** printing Val %\val% *)
(** printing Stream %\Stream% *)
Variable D : Type.

(*=Stream *)
CoInductive Stream := Eps : Stream -> Stream | Val : D -> Stream.
(*=End *)

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

Lemma pred_nth_sum : forall x m n, pred_nth x (m+n) = pred_nth (pred_nth x m) n.
induction m.
simpl.
intuition.
intro n; replace (S m + n)%N with (m + S n)%N; intuition ; last by rewrite addSn ; rewrite addnS.
rewrite IHm.
rewrite (@pred_nth_Sn_acc n (pred_nth x m)).
rewrite pred_nth_Sn.
reflexivity.
Qed.

End Lift_type.

Section Lift_ord.

Variable D : ordType.

(** ** Order *)
(*=DLle *)
CoInductive DLle : Stream D -> Stream D -> Prop :=
 |  DLleEps : forall x y,  DLle x y -> DLle (Eps x) (Eps y)
 |  DLleEpsVal : forall x d,  DLle x (Val d) -> DLle (Eps x) (Val d)
 |  DLleVal : forall d d' n y, pred_nth y n = Val d' -> d <= d' -> DLle (Val d) y.
(*=End *)

Hint Constructors DLle.

(*=DLle_rec *)
Lemma DLle_rec : forall R : Stream D -> Stream D -> Prop,
   (forall x y, R (Eps x) (Eps y) -> R x y) ->
   (forall x d, R (Eps x) (Val d) -> R x (Val d)) ->
   (forall d y, R (Val d) y -> exists n, exists d', pred_nth y n = Val d' /\ d <= d')
   -> forall x y, R x y -> DLle x y.
(*=End *)
move => R REps REpsVal RVal; cofix; case => x.
- case => y H.
  + apply DLleEps. apply DLle_rec. by apply REps.
  + by apply DLleEpsVal; apply DLle_rec; auto.
move => y H.
case (RVal _ _ H); move => n [d [X L]].
by apply DLleVal with d n.
Qed.

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

Lemma pred_nth_epsS n (x y:Stream D): Eps y = pred_nth x n -> y = pred_nth x (S n).
elim:n x y. move => x y E. simpl in E. rewrite <- E. simpl. auto.
move => n IH x. case x ; clear x. intros x y. intros E. simpl in E. specialize (IH _ _ E). auto.
intros x y. simpl. intros incon. inversion incon.
Qed.

Lemma pred_nth_valS n d (y:Stream D): Val d = pred_nth y n -> Val d = pred_nth y (S n).
elim: n d y.
- move => d y E. simpl in E. by rewrite <- E.
- move => n IH d. case => y E.
  + simpl in E. by rewrite (IH _ _ E).
  + apply E.
Qed.

Lemma pred_nth_comp (y:Stream D) : forall m0 n1 m1 : nat,
   m0 == (n1 + m1)%N -> pred_nth y m0 = pred_nth (pred_nth y n1) m1.
move => m0.
elim: m0 y.
- move => y n1 m1 E. have X:=addn_eq0 n1 m1. rewrite <- (eqP E) in X. rewrite eq_refl in X.
  have Y:=proj1 (andP (sym_eq X)). rewrite (eqP Y). simpl. by rewrite (eqP (proj2 (andP (sym_eq X)))).
- move => m0 IH y n1. case.
  + rewrite addn0. case: n1 ; first by [].
    case: y ; last by [].
    simpl. move => y n E. specialize (IH y n 0). by rewrite IH ; last rewrite addn0.
  + move => n. rewrite addnS => E. simpl. case_eq (pred_nth y n1).
    * move => y' X. case: y X ; last by case: n1 E.
      move => y X. rewrite (pred_nth_epsS (sym_eq X)). simpl. by apply IH.
    * move => y' X. case: y X => y.
      - case: n1 E ; first by []. move => n1 E. simpl.
        specialize (IH y n1). move => X. rewrite X in IH. specialize (IH n.+1). rewrite addnS in IH. specialize (IH E).
        by apply IH.
      - move => X. have EE:= (pred_nth_val y n1). rewrite EE in X. by apply X.
Qed.

Lemma DLle_pred_nth x y n : DLle x y -> DLle (pred_nth x n) (pred_nth y n).
elim: n x y ; first by [].
move => n IH x y C. case: x y / C.
- move => x y C. simpl. apply IH. by apply C.
- move => x d C. simpl. specialize (IH _ _ C). rewrite pred_nth_val in IH. by apply IH.
- move => d d' m y E L. specialize (IH (Val d)).
  case: y E.
  + move => y. specialize (IH y). move => X. simpl. rewrite (pred_nth_val) in IH. apply IH.
    case: m X ; first by [].
    move => m X. simpl in X. by apply:(DLleVal X).
  + move => y. rewrite pred_nth_val. case. move => E. simpl. rewrite E.
    by apply DLleVal with d' 0 ; last by [].
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

Lemma DLnvalval : forall n y d z, pred_nth y n = Val d -> DLle y z ->
 exists m, exists d', pred_nth z m = Val d' /\ d <= d'.
elim.
- move => y d z E L. simpl in E. case: L E ; [by [] | by [] | idtac].
  move => d1 d2 n y' E L. case => E'. rewrite E' in L. clear E' d1.
  exists n. exists d2. by split.
- move => n IH y d z E L. specialize (IH (pred y) d z). rewrite pred_nth_Sn_acc in E.
  specialize (IH E). apply IH. by apply DLle_pred_left.
Qed.

Lemma DLleEpsn n x z xx : pred_nth x n = Val xx -> DLle (Val xx) z -> DLle x z.
elim:n x z xx => x.
- move => z xx. simpl => E. by rewrite E.
- move => IH. case.
  + move => d z xx. simpl. move => C DD.
    specialize (IH d z xx C DD). by apply: (DLle_pred_right (DLleEps _)).
  + move => d z xx. simpl. case => e. by rewrite e.
Qed.

Lemma DLle_trans : forall x y z, DLle x y -> DLle y z -> DLle x z.
move => x y z D0 D1.
apply DLle_rec with (R:=fun x z => (forall xx n, pred_nth x n = Val xx -> DLle x z)).
- clear x y z D0 D1. move => x y C xx n X.
  specialize (C xx (S n) X). by apply (DLle_pred C).
- clear x y z D0 D1. move => x y C xx n X. specialize (C _ (S n) X).
  by apply (DLle_pred_left C).
- move => d yy C. specialize (C d 0).
  case (fun Z => DLvalval (C Z)) ; first by [].
  move => n [dd [ZZ Z]]. exists n. exists dd. by split.
- move => xx n C. case (DLnvalval C D0) => m [yy [P Q]].
  case (DLnvalval P D1) => k [zz [Pz Qz]].
  apply (DLleEpsn C). apply (DLleVal Pz). by apply (Ole_trans Q Qz).
Qed.

(** *** Declaration of the ordered set *)

Lemma LiftOrdAxiom : PreOrd.axiom DLle.
move => x. split ; first by [].
move => y z. by apply DLle_trans.
Qed.

Canonical Structure lift_ordMixin := OrdMixin LiftOrdAxiom.
Canonical Structure lift_ordType := Eval hnf in OrdType lift_ordMixin.

Lemma ordSetoidAxiom (X:ordType) : Setoid.axiom (@tset_eq X).
split ; first by [].
split ; last by apply: tset_sym.
by apply: tset_trans.
Qed.

Canonical Structure ordSetoidMixin D := SetoidMixin (ordSetoidAxiom D).
Canonical Structure ordSetoidType D := Eval hnf in SetoidType (ordSetoidMixin D).

Lemma lift_setoidAxiom : @Setoid.axiom (Stream D) (@tset_eq lift_ordType).
split ; last split ; first by [].
move => x y z. by apply tset_trans.
move => x y ; by apply tset_sym.
Qed.

Canonical Structure lift_setoidMixin := SetoidMixin lift_setoidAxiom.
Canonical Structure lift_setoidType := Eval hnf in SetoidType lift_setoidMixin.

(** ** Definition of the cpo structure *)

Lemma eq_Eps : forall x, x =-= Eps x.
intros; apply: Ole_antisym; repeat red; auto.
Save.
Hint Resolve eq_Eps.

(** *** Bottom is given by an infinite chain of Eps *)
(** printing DL_bot %\DLbot% *)
CoFixpoint DL_bot : lift_ordType := Eps DL_bot.

Lemma DL_bot_eq : DL_bot = Eps DL_bot.
transitivity match DL_bot with Eps x => Eps x | Val d => Val d end ; auto.
destruct DL_bot ; auto.
Save.

Lemma DLless_cond : forall x y, (forall xx, x =-= Val xx -> x <= y) -> DLle x y.
move => x y P. apply DLle_rec with (R:=fun x y => forall xx, x =-= Val xx -> x <= y).
- move => d0 d1 IH d00 dv.
  rewrite -> (eq_Eps d0) in dv. rewrite -> (eq_Eps d0). specialize (IH _ dv).
  by rewrite -> (eq_Eps d1).
- move => d0 d1 IH dd dv. rewrite -> (eq_Eps d0) in dv. specialize (IH _ dv).
  by rewrite -> (eq_Eps d0).
- move => d0 d1 IH. specialize (IH _ (Oeq_refl _)). by apply (DLvalval IH).
- by apply P.
Qed.

Lemma DL_bot_least : forall x, DL_bot <= x.
move => x. apply DLless_cond => xx [_ C].
case (DLvalval C) => n [dd [P Q]].
have F:False ; last by [].
elim: n P ; first by rewrite DL_bot_eq.
move => n IH. rewrite DL_bot_eq. by apply IH.
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
      forall x d, (exists k, pred_nth x k = Val d) -> (Val d:lift_ordType) =-= x.
move => x d X. split. simpl. case: X => k e. by apply: (DLleVal e).
case: X => n X. rewrite <- X. by apply DLle_pred_nth_right.
Save.

(** *** Construction of least upper bounds *)

Definition isEps (x:Stream D) := match x with Eps _ => True | _ => False end.

Lemma isEps_Eps : forall x, isEps (Eps x).
repeat red; auto.
Save.

Lemma not_isEpsVal : forall d, ~ (isEps (Val d)).
repeat red; auto.
Save.
Hint Resolve isEps_Eps not_isEpsVal.

Lemma isEpsEps (x x': Stream D) : x = Eps x' -> isEps x.
move => E. by rewrite E.
Qed.

Definition isEps_dec (x: Stream D) : {d:D|x=Val d}+{isEps x} :=
match x as x0 return x = x0 -> {d:D|x=Val d}+{isEps x} with
| Eps x' => fun E => inright _ (isEpsEps E)
| Val d => fun E => inleft _ (exist _ d E)
end (refl_equal x).


(* Slightly more radical rewrite, trying to use equality *)

Lemma allvalsfromhere : forall (c:natO =-> lift_ordType) n d i,
  c n =-= Val d -> exists d', c (n+i)%N =-= Val d' /\ d <= d'.
move => c n d i [Hnv1 Hnv2].
have X:Val d <= c (n+i)%N. apply Ole_trans with (c n) ; first by []. apply fmonotonic. by apply: leq_addr.
case (DLle_Val_exists_pred X) => k [d' [P Q]].
exists d'. split ; last by [].
apply Oeq_sym. apply Val_exists_pred_eq. by exists k.
Qed.

Definition hasVal (x:Stream D) := exists j, exists d, pred_nth x j = Val d.
Definition valuable := {x | hasVal x}.

Definition projj (x:valuable) : lift_ordType :=
match x with exist x X => x end.

(* Redoing extract using constructive epsilon *)
Require Import ConstructiveEpsilon.

Lemma hasValEps x x' : x = Eps x' -> hasVal x -> hasVal x'.
move => e. rewrite e. clear e x.
case => n. case => d e. case: n e ; first by []. move => n. simpl => e. exists n. exists d. by apply e.
Qed.

Definition inc x' (X:{kd : nat * D | let (k, d) := kd in pred_nth x' k = Val d}) :
                 {kd : nat * D | let (k, d) := kd in pred_nth (Eps x') k = Val d} :=
match X with exist (k,d) X0 =>
  exist (fun kd : nat * D => let (k, d) := kd in pred_nth (Eps x') k = Val d) (k.+1,d) X0
end.

Lemma pred_nth_notEps x' : ~ (exists d : D, pred_nth (Eps x') 0 = Val d).
by case.
Qed.

Lemma pred_nthvalval d' n : (exists d : D, pred_nth (Val d') n = Val d).
exists d'. by case: n.
Qed.

Fixpoint hasVal_dec x n : { (exists d : D, pred_nth x n = Val d) } + {~ (exists d : D, pred_nth x n = Val d)} :=
match x,n return { (exists d : D, pred_nth x n = Val d) } + {~ (exists d : D, pred_nth x n = Val d)} with 
| Eps x', S n => hasVal_dec x' n
| Eps x', O => right (exists d : D, pred_nth (Eps x') O = Val d) (@pred_nth_notEps x')
| Val d, n' => left (~ (exists d' : D, pred_nth (Val d) n = Val d')) (pred_nthvalval d n)
end.

Fixpoint getVal x n :=
match x as x0, n as n0 return (exists d, pred_nth x0 n0 = Val d) -> D with
| Eps x', S n' => getVal x' n'
| Eps x', O => fun P => match pred_nth_notEps P with end
| Val d, n => fun _ => d
end.

Lemma getValVal n x (P:exists d, pred_nth x n = Val d) : pred_nth x n = Val (@getVal x n P).
elim: n x P.
- by case ; first by move => x [d F].
- move => n IH. by case; first by apply IH.
Qed.

Definition findindexandval (x:valuable) : {kd | match kd with (k,d) => (pred_nth (projj x) k) = Val d end} :=
match x as x0 return {kd | match kd with (k,d) => (pred_nth (projj x0) k) = Val d end} with
| exist x' P =>
  match @constructive_indefinite_description_nat (fun n => exists d:D, pred_nth x' n = Val d) (hasVal_dec x') P
  with exist n Px => exist (fun kd => match kd with (k,d) => (pred_nth x' k) = Val d end) (n,getVal Px) (getValVal  Px)
  end
end.

Definition extract (x:valuable) : D :=
match (findindexandval x) with exist (n,d) _ => d end.

Lemma extractworks x : projj x =-= Val (extract x).
unfold extract. case (findindexandval x).
case => n d. move => X. apply Oeq_sym. apply Val_exists_pred_eq. exists n. by apply X.
Qed.

Lemma vinj : forall d d', (Val d:lift_ordType) =-= Val d' -> d =-= d'.
intros d d' (H1,H2). by split ; apply DLleVal_leq.
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

Lemma pred_nth_eq k x : pred_nth x k =-= x.
elim: k x; first by [].
move => n IH. case ; last by [].
simpl. move => x. rewrite -> (IH x). split ; first by apply DLleEps_right. by apply DLleEps_left.
Qed.

Lemma eqValpred : forall x d, x =-= Val d -> exists k, exists d', pred_nth x k = Val d' /\ d=-=d'.
move => x d [H1 H2].
case (DLle_Val_exists_pred H2) => k [d' [H L]].
exists k; exists d';split ; first by [].
split ; first by [].
apply vleinj. rewrite <- H. clear L d' H. 
rewrite <- H1. by rewrite -> pred_nth_eq.
Qed.

Lemma hasValShift (c:natO -=> lift_ordType) k d (Hck:c k =-= Val d) n : hasVal (c (n + k)%N).
rewrite addnC. case: (allvalsfromhere n Hck) => d' [A L].
case: (eqValpred A) => i [dd [XX _]]. exists i. by exists dd.
Qed.

Definition makechain (c:natO -=> lift_ordType) k d (Hck:c k =-= Val d) : nat -> D :=
fun n => @extract (exist hasVal (c (n+k)%N) (hasValShift Hck n)).

Lemma makechan_mono (c:natO -=> lift_ordType) k d (Hck:c k =-= Val d) : monotonic (makechain Hck).
move => n n' L. apply extractmono. simpl. apply fmonotonic. by apply: (leq_add L).
Qed.

Definition makechainm (c:natO -=> lift_ordType) k d (Hck:c k =-= Val d) : natO =-> D :=
  Eval hnf in mk_fmono (makechan_mono Hck).

Lemma pred_mono (c:natO =-> lift_ordType) : monotonic (fun n => pred (c n)).
move => x y H. apply: DLle_pred. by apply (fmonotonic c).
Qed.

Definition cpred (c:natO =-> lift_ordType) : natO =-> lift_ordType := Eval hnf in mk_fmono (pred_mono c).

Lemma fValIdx : forall (c:natO =-> lift_ordType) (n : nat), 
        {dk: (D*nat)%type | match dk with (d,k) => k<n /\ c k =-= Val d end} + {(forall k, k<n -> isEps (c k))}.
move => c. elim ; first by right.
move => n. case.
- case. case => d k [H ck]. left. exists (d,k). split ; last by []. rewrite ltn_neqAle in H.
  by apply (proj2 (andP H)).
- move => X. case: (isEps_dec (c n)).
  + case => d E. left. exists (d,n). by rewrite E.
  + move => E. right => k. case_eq (k == n) => EE ; first by rewrite (eqP EE).
    move => L. rewrite ltnS in L. rewrite leq_eqVlt in L. rewrite EE in L. by apply X.
Defined.

Definition createchain (c:natO =-> lift_ordType) (n:nat) 
  (X:{dk: (D*nat)%type | match dk with (d,k) => k<n /\ c k =-= Val d end}) :
   (natO =-> D) :=
match X with | exist (d,k) (conj Hk Hck) => @makechainm c k d Hck
end.

Lemma makechainworks : forall (c:natO =-> lift_ordType) k dk (H2:c k =-= Val dk) i (d:D), c (k+i)%N =-= (Val d) -> makechain H2 i =-= d.
move => c k dk Hck i d e.
apply vinj.
rewrite <- e.
apply Oeq_sym.
unfold makechain.
rewrite <- extractworks.
simpl. by rewrite addnC.
Qed.

Lemma eqDLeq : forall d d', d =-= d' -> Val d =-= (Val d').
move => d d'. by case ; split ; apply DLle_leVal.
Qed.

Lemma predeq : forall x, x =-= pred x.
move => x. case: x ; last by [].
move => x. simpl. by rewrite <-( @pred_nth_eq 1 (Eps x)).
Qed.

(* Just realized I should have had Val as a morphism ages ago *)
Add Parametric Morphism : (@Val D)
with signature (@tset_eq D) ==> (@tset_eq lift_ordType)
as Val_eq_compat.
intros.
apply eqDLeq.
assumption.
Qed.


Add Parametric Morphism : (@Val D)
with signature (@Ole D) ++> (@Ole lift_ordType)
as Val_le_compat.
intros.
apply DLle_leVal.
auto.
Qed.

Lemma DLle_Val_exists_eq : forall y d, Val d <= y -> exists d', y =-= Val d' /\ d <= d'.
intros y d H; inversion H.
exists d'.
split.
symmetry.
apply Val_exists_pred_eq.
exists n; trivial.
assumption.
Qed.

Lemma DLvalgetchain: forall (c:natO =-> lift_ordType) k d, c k =-= Val d -> exists c':natO =-> D, forall n, c(k+n)%N =-= Val (c' n).
intros c k d chk.
exists (makechainm chk).
intros n.
destruct (allvalsfromhere n chk) as [d' [chd ld]].
refine (Oeq_trans chd _).
apply eqDLeq.
apply (Oeq_sym (makechainworks chk chd)).
Qed.

Hint Immediate DLle_leVal.

Lemma eta_mono : monotonic (@Val D).
move => x y L. by rewrite -> L.
Qed.

Definition eta_m : D =-> lift_ordType := Eval hnf in mk_fmono eta_mono.

End Lift_ord.

Implicit Arguments eta_m [D].

Section Lift_cpo.

Variable D:cpoType.

CoFixpoint DL_lubn (c:natO =-> lift_ordType D) (n:nat) : lift_ordType D := 
    match fValIdx c n with inleft X => Val (lub (createchain X))
                                |  inright _  => Eps (DL_lubn (cpred c) (S n))
    end.

Lemma DL_lubn_inv : forall (c:natO =-> lift_ordType D) (n:nat), DL_lubn c n = 
     match fValIdx c n with inleft X => Val (lub (createchain X))
                                |  inright _  => Eps (DL_lubn (cpred c) (S n))
    end.
intros; rewrite (DL_inv (DL_lubn c n)).
simpl; case (fValIdx c n); trivial. 
Qed.

Lemma chainluble : forall (c:natO =-> lift_ordType D) k dk (Hkdk : c k =-= Val dk) k' dk' (Hkdk': c k' =-= Val dk'), 
   lub (makechainm Hkdk) <= lub (makechainm Hkdk').
intros;apply lub_le.
intro n.
assert (Hkn := allvalsfromhere n Hkdk).
destruct Hkn as (dkn,(Hckn,Hdkdkn)).
setoid_replace (makechainm Hkdk n) with (dkn).
destruct (allvalsfromhere (n+k) Hkdk') as [dkk'n [Hckk'n Hddd]].
apply Ole_trans with dkk'n.
apply vleinj; rewrite <- Hckn; rewrite <- Hckk'n.
apply fmonotonic. rewrite addnC. by apply: (leq_addl k').
setoid_replace dkk'n with (makechainm Hkdk' (n+k)%N).
apply le_lub.
unfold makechainm.
apply Oeq_sym; apply makechainworks.
assumption.
unfold makechainm; apply makechainworks.
assumption.
Qed.

Lemma chainlubinv : forall (c:natO =-> lift_ordType D) k dk (Hkdk : c k =-= Val dk) k' dk' (Hkdk': c k' =-= Val dk'), 
   lub (makechainm Hkdk) =-= lub (makechainm Hkdk').
intros;split;apply chainluble.
Qed.

Lemma pred_lubn_Val : forall (d:D)(n k p:nat) (c:natO =-> lift_ordType D),
             (n <k+p)%nat -> pred_nth (c n) k = Val d
                                   -> exists d', DL_lubn c p =-= Val d'.
move => d n. elim.
- move => p c L E. rewrite (DL_lubn_inv c p). simpl in E.
  case: (fValIdx c p).
  + case.
    * move => [d' k] [H1 H2]. simpl. by exists (lub (makechainm H2)).
    * move => X. specialize (X _ L). by rewrite E in X.
  + move => k IH p c L E. rewrite (DL_lubn_inv c p).
    case: (fValIdx c p).
    * unfold createchain. case. case. move => d' k'. case => LL EE.
      by exists (lub (makechainm EE)).
    * move => X. rewrite addSn in L. rewrite <- addnS in L.
      have A: (pred_nth (cpred c n) k = Val d) by simpl ; rewrite <- pred_nth_Sn_acc.
      specialize (IH (S p) (cpred c) L A).
      case: IH => d' IH. exists d'. rewrite <- IH. by rewrite <- eq_Eps.
Qed.

Lemma cpredsamelub : forall (c:natO =-> lift_ordType D) k dk (H1:c k =-= Val dk) (H2: (cpred c) k =-= Val dk),
                      lub (makechainm H1) =-= lub (makechainm H2).
intros; split.
apply: lub_le; intro.
setoid_replace (makechainm H1 n) with (makechainm H2 n).
apply le_lub.
assert (Hkn := allvalsfromhere n H1).
destruct Hkn as (dkn,(Hckn,Hdkdkn)).
unfold makechainm; simpl.
setoid_rewrite (makechainworks H1 Hckn).
assert (HH : ((cpred c) (k+n)%N =-= Val dkn)).
unfold cpred; simpl.
rewrite <- Hckn.
apply Oeq_sym; apply predeq.
setoid_rewrite (makechainworks H2 HH).
auto.

apply: lub_le; intro.
setoid_replace (makechainm H2 n) with (makechainm H1 n).
apply le_lub.
destruct (allvalsfromhere n H2) as (dkn,(Hckn,Hdkdkn)).
unfold makechainm; simpl.
setoid_rewrite (makechainworks H2 Hckn).
assert (HH : ((c) (k+n)%N =-= Val dkn)).
unfold cpred in Hckn; simpl in Hckn.
rewrite <- Hckn; apply predeq.
setoid_rewrite (makechainworks H1 HH); auto.
Qed.

Lemma attempt2 : forall kl (c:natO =-> lift_ordType D) p d, pred_nth (DL_lubn c p) kl = Val d 
                    -> exists k, exists dk, exists Hkdk:c k =-= Val dk, d =-= lub (makechainm Hkdk).
elim.
- simpl. move => c p d E. rewrite -> DL_lubn_inv in E.
  case: (fValIdx c p) E ; last by [].
  move => s. case => e. rewrite <- e. clear d e.
  case: s. case => d n [L E]. simpl. exists n. exists d. by exists E.
- move => k IH c p d E. simpl in E. unfold createchain in E.
  have HH:=IH (cpred c) (S p) d.
  case: (fValIdx c p) E. 
  + case. case => d' n [P Q] E.
    specialize (IH c p d). rewrite E in IH. apply IH. by apply pred_nth_val.
  + move => X E. case: (HH E) => n [x [P Q]].
    exists n. exists x. have PP:=P. simpl in PP. have P0:=Oeq_trans (predeq _) P. exists P0. rewrite -> Q.
    by apply (Oeq_sym (cpredsamelub P0 P)).
Qed.

(* first just wrap pred_lubn_Val to use equality *)
Lemma chainVallubnVal : forall (c:natO =-> lift_ordType D) n d p, c n =-= Val d -> exists d', DL_lubn c p =-= Val d'.
intros.
destruct (eqValpred H) as (k,(d'',(Hcnk,Hdd''))).
apply (pred_lubn_Val (n:=n) (k:=k+n+1) (p:=p) (c:=c) (d:=d'')).
apply ltn_addr. rewrite <- addnA. apply ltn_addl. rewrite addnS. rewrite addn0. by apply ltnSn.
rewrite addnS. rewrite addn0. rewrite <- addnS.
rewrite pred_nth_sum.
rewrite Hcnk. by [].
Qed.

Lemma chainVallubnlub : forall (c:natO =-> lift_ordType D) n d (H : c n =-= Val d) p, exists d',  DL_lubn c p =-= Val d' /\ d' =-= lub (makechainm H).
intros.
destruct (chainVallubnVal p H) as (d',HH).
exists d'.
split. assumption.
destruct (eqValpred HH) as (k,(d'',(Hk,Hd'd''))).
destruct (attempt2 Hk) as (p',(dp',(Hp',Heq))).
rewrite Hd'd''.
rewrite -> Heq.
apply chainlubinv.
Qed.


Definition DL_lub (c:natO =-> lift_ordType D) := DL_lubn c 1.


Lemma DL_lub_upper : forall c:natO =-> lift_ordType D, forall n, c n <= DL_lub c.
intros c n. simpl. apply: DLless_cond.
intros d C.
destruct (chainVallubnlub C 1) as [d' [Ln L]].
unfold DL_lub. rewrite -> Ln.
assert (X:=makechainworks C). specialize (X 0 d). rewrite addn0 in X.
specialize (X C). apply Ole_trans with (y:=Val d). by auto.
assert (pred_nth (Val d') 0 = Val d') as Y by auto.
apply (DLleVal Y). rewrite -> L.
apply Ole_trans with (y:=(makechainm (c:=c) (k:=n) (d:=d) C) 0). simpl. by auto.
by apply le_lub.
Qed.

Lemma DL_lub_least : forall (c : natO =-> lift_ordType D) a, 
                      (forall n, c n <= a) -> DL_lub c <= a.
intros c a C. simpl.
apply: DLless_cond. intros d X.
destruct (eqValpred X) as [n [dd [P Q]]].
destruct (attempt2 P) as [m [d' [cm Y]]].
apply Ole_trans with (y:= (Val dd)).
refine (proj2 (Val_exists_pred_eq _)). exists n. auto.
assert (Z:= C m). rewrite -> cm in Z.
destruct (DLvalval Z) as [mm [e [R S]]].
apply (DLleVal R). rewrite -> Y.
apply lub_le.
intros nn.
assert (A:=makechainworks cm).
specialize (A nn).
clear S Y Z.
destruct (allvalsfromhere nn cm) as [nnv [S T]].
specialize (A _ S). rewrite -> A. clear A.
assert (a =-= Val e) as E.
apply Oeq_sym.
apply (Val_exists_pred_eq). exists mm. apply R.
assert (Z := C (m+nn)%N).
rewrite -> E in Z. rewrite -> S in Z. apply (vleinj Z).
Qed.


(** *** Declaration of the lifted cpo *)

Lemma DLCpoAxiom : CPO.axiom DL_lub.
move => x y n.
split ; first by apply DL_lub_upper.
by apply DL_lub_least.
Qed.

Canonical Structure lift_cpoMixin := CpoMixin DLCpoAxiom.
Canonical Structure lift_cpoType := Eval hnf in CpoType lift_cpoMixin.

Lemma lubval: forall (c:natO =-> lift_cpoType) d, lub c =-= Val d ->
                exists k, exists d', c k =-= Val d' /\ d' <= d.
intros c d l.
destruct l as [lubval1 lubval2].
destruct (DLle_Val_exists_pred lubval2) as [k xx].
destruct xx as [f' [lubval lf]].
assert (lub c =-= Val f') as lubval'.
apply: Ole_antisym.
eapply Ole_trans. apply lubval1. by apply: DLle_leVal.
simpl.
apply: (DLleVal). apply lubval. apply Ole_refl.
assert (f' <= d).
destruct lubval' as [v1 v2].
assert (Val f' <= Val d).
apply (Ole_trans v2 lubval1).
apply (DLleVal_leq H).
assert (d =-= f') as feq. auto.
clear H lubval1 lubval2 lf.

assert (xx:=attempt2 lubval).
destruct xx as [n [f0 [chnval lf']]].
exists n. exists f0. split. apply chnval.
assert (w:=makechainworks chnval).
specialize (w 0 f0). rewrite addn0 in w.
specialize (w chnval).
destruct w as [_ L2].
refine (Ole_trans L2 (Ole_trans (le_lub (makechainm chnval) 0) _)).
rewrite <- lf'. by auto.
Qed.

(*==========================================================================
  Eta
  ==========================================================================*)

(** printing eta %\ensuremath{\eta}% *)

Lemma eta_cont : continuous (@eta_m D).
move => c. simpl. unfold lub. simpl. unfold DL_lub. rewrite -> DL_lubn_inv. simpl.
apply: DLle_leVal.
apply lub_le => n. apply: (Ole_trans _ (le_lub _ n)). simpl.
 rewrite -> makechainworks. by apply Ole_refl. by apply Oeq_refl.
Qed.

Definition eta : D =-> lift_cpoType := Eval hnf in mk_fcont eta_cont.

End Lift_cpo.

Implicit Arguments eta [D].

(** printing _BOT %\LIFTED% *)
Notation "x '_BOT'" := (lift_cpoType x) (at level 28).

Lemma liftOrdPointed (D:ordType) : Pointed.axiom (DL_bot D).
move => x. by apply DL_bot_least.
Qed.

Canonical Structure liftOrdPointedMixin D := PointedMixin (@liftOrdPointed D).
Canonical Structure liftOrdPointedType D := Eval hnf in PointedType (liftOrdPointedMixin D).

Lemma liftCpoPointed (D:cpoType) : Pointed.axiom (DL_bot D).
move => x. by apply DL_bot_least.
Qed.

Canonical Structure liftCppoMixin D := PointedMixin (@liftCpoPointed D).
Canonical Structure liftCppoType D := Eval hnf in CppoType (liftCppoMixin D).
Canonical Structure liftCpoPointedType (D:cpoType) := Eval hnf in @PointedType (D _BOT) (liftCppoMixin D).

Lemma liftFunPointed C (D:pointedType) : Pointed.axiom (@fmon_cte C D PBot).
move => f x. simpl. by apply leastP.
Qed.

Canonical Structure funOrdPointedMixin C D := PointedMixin (@liftFunPointed C D).
Canonical Structure funOrdPointedType C D := Eval hnf in PointedType (funOrdPointedMixin C D).

Lemma PBot_app D (E:cppoType) : forall d, (PBot:D -=> E) d =-= PBot.
move => d. by simpl.
Qed.

Lemma PBot_incon  (D:cpoType) (x:D) : eta x <= PBot -> False.
move => incon.
inversion incon. subst. clear x H1 incon.
elim: n H0.
- simpl. unfold Pointed.least. simpl. by rewrite -> DL_bot_eq.
- move => n IH. unfold Pointed.least. simpl. by apply IH.
Qed.

Lemma PBot_incon_eq (D:cpoType) (x:D) : eta x =-= PBot -> False.
intros [incon _].
apply (PBot_incon incon).
Qed.
