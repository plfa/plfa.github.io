Require Import PredomAll.
Require Export lc.
Require Export uni.

Set Implicit Arguments.
Unset Strict Implicit.

Definition SimpleOpm (A B : Type) (op : A -> B) : Discrete A -m>  Discrete B.
intros A B op.
exists (op).
unfold monotonic.
intros.
simpl in *.
rewrite H. auto.
Defined.

Definition SimpleOp A B (op:A -> B) :
    Discrete A -c> Discrete B.
intros.
exists (SimpleOpm op).
simpl in *.
unfold continuous.
intros.
simpl. auto.
Defined.

(*

Definition SimpleOp2mm (A B C : Type) (op : A -> B -> C) : Discrete A -> Discrete B -m>  Discrete C.
intros.
exists (op X).
unfold monotonic.
intros.
simpl in *.
rewrite H. auto.
Defined.

Definition SimpleOp2c A B C (op:A -> B -> C) :
    Discrete A -> Discrete B -c> Discrete C.
intros.
exists (SimpleOp2mm op X).
simpl in *.
unfold continuous.
intros.
simpl. auto.
Defined.

Definition SimpleOp2m (A B C:Type) (op : A -> B -> C) :
    Discrete A -m> Discrete B -C-> Discrete C.
intros.
exists (SimpleOp2c op).
unfold monotonic.
intros.
simpl in *.
rewrite H. auto.
Defined.

Definition SimpleOp2 A B C (op:A -> B -> C) :
    Discrete A -c> Discrete B -C-> Discrete C.
intros.
exists (SimpleOp2m op).
unfold continuous ; intros ; simpl ; auto.
Defined.
*)

Definition FS := BiLift_strict (BiSum (BiConst (Discrete nat)) BiArrow).
Definition DInf := DInf FS.
Definition VInf := Dsum (Discrete nat) (DInf -C-> DInf).

Definition Roll : DL VInf -C-> DInf := ROLL FS.
Definition Unroll : DInf -C-> DL VInf := UNROLL FS.

Lemma UR_eq : forall x, Unroll (Roll x) == x.
intros y. rewrite <- fcont_comp_simpl.
apply Oeq_trans with (y:= ID y).
refine (app_eq_compat _ (Oeq_refl _)). unfold Unroll. unfold Roll. apply (DIso_ur FS). auto.
Qed.

Lemma RU_eq : forall x, Roll (Unroll x) == x.
intros x.
assert (xx := fcont_eq_elim (DIso_ru FS) x). rewrite fcont_comp_simpl in xx. rewrite ID_simpl in xx.
simpl in xx. unfold Unroll. unfold Roll. apply xx.
Qed.

Definition monic D E (f:D -c> E) := forall x y, f x <= f y -> x <= y.

Lemma Roll_monic: monic Roll.
unfold monic.
assert (zz:=@ROLL_monic _ FS). fold Roll in zz. fold DInf in zz. unfold VInf.
apply zz.
Qed.

Lemma Unroll_monic: monic Unroll.
assert (yy:=@UNROLL_monic _ FS). fold Unroll in yy. fold DInf in yy.
unfold monic. apply yy.
Qed.

Lemma inj_monic: forall D E  (f:D -c> E), monic f -> forall x y, f x == f y -> x == y.
intros D E f mm. unfold monic in mm. intros x y.
assert (xx:= mm x y). specialize (mm y x).
intros [xy1 xy2]. split ; auto.
Qed.

Fixpoint SemEnv n : cpo :=
match n with
| O => DOne
| S n => SemEnv n *c* VInf
end.

Fixpoint projenv (m n:nat) : (m < n) -> SemEnv n -c> VInf :=
match m,n with
| m,O => fun inconsistant => match (lt_n_O m inconsistant) with end
| O, S n => fun _ => SND
| S m, S n => fun h => projenv (lt_S_n _ _ h) << FST
end.

(*
Lemma K_com2: forall E F (f:E -C-> F),
              EV << PROD_fun (@K E _ f) ID == f.
intros. apply fcont_eq_intro. auto.
Qed.

Lemma uncurry_PROD_fun: forall D D' E F G f g1 (g2:G -C-> D') h,
  uncurry D E F f << PROD_fun (g1 << g2) h == uncurry D' E F (f << g1) << PROD_fun g2 h.
intros. apply fcont_eq_intro. auto.
Qed.

Add Parametric Morphism D E F : (@curry D E F)
with signature (@Oeq (Dprod D E -C-> F)) ==> (@Oeq (D -C-> E -C-> F))
as Curry_eq_compat.
intros f0 f1 feq. refine (fcont_eq_intro _). intros d. refine (fcont_eq_intro _). intros e.
repeat (rewrite curry_simpl). auto.
Qed.
*)

Definition Dlift : (VInf -C-> DInf) -C-> DInf -C-> DInf := curry (Roll << EV <<
     PROD_map (KLEISLI << (fcont_COMP VInf DInf _ Unroll)) Unroll).

Definition Dapp := EV << PROD_map (SUM_fun (PBot : Discrete nat -C-> DInf -C-> DL VInf)
                                               (fcont_COMP _ _ _ Unroll))
                                      (Roll << eta) : Dprod VInf VInf -C-> DL VInf.

Definition zeroCasem : Discrete nat -m> Dsum DOne (Discrete nat).
exists (fun (n:Discrete nat) => match n with | O => @INL DOne _ tt | S m => @INR _ (Discrete nat) m end).
unfold monotonic. intros x y xy. assert (x = y) as E by auto.
rewrite E in *. auto.
Defined.

Definition zeroCase : Discrete nat -c> Dsum DOne (Discrete nat).
exists zeroCasem. unfold continuous. intros c.
refine (Ole_trans _ (le_lub _ 0)). auto.
Defined.

Lemma zeroCase_simplS: forall n, zeroCase (S n) = @INR _ (Discrete nat) n.
intros n ; auto.
Qed.

Lemma zeroCase_simplO: zeroCase O = @INL DOne _ tt.
auto.
Qed.

Definition DiscProdm S T : Dprod (Discrete S) (Discrete T) -m> Discrete (S * T).
intros S T. exists (fun (p:Dprod (Discrete S) (Discrete T)) => (fst p, snd p)).
unfold monotonic. intros. destruct x. destruct y. inversion H. simpl in *.
rewrite H0. rewrite H1. auto.
Defined.

Definition DiscProd S T : Dprod (Discrete S) (Discrete T) -c> Discrete (S * T).
intros S T. exists (DiscProdm S T).
unfold continuous. auto.
Defined.

Fixpoint SemVal v n (vt : VTyping n v) : (SemEnv n -C-> VInf) :=
match vt with
| TNUM n => INL << (@K _ (Discrete nat) n)
| TVAR m nthm => projenv nthm
| TLAMBDA _  e => INR << Dlift << curry (Roll << SemExp e)
end
with SemExp pe n (e : ETyping n pe) : (SemEnv n -C-> DL VInf) :=
match e with
| TAPP _ _ v1 v2 => Dapp << <| SemVal v1, SemVal v2 |>
| TVAL _ v => eta << SemVal v
| TLET _ _ e1 e2 => EV << <| curry (KLEISLIR (SemExp e2)), SemExp e1 |>
| TOP op _ _ v1 v2 =>
       uncurry (Operator2 (eta << INL << (SimpleOp (fun p => op (fst p) (snd p))) << DiscProd _ _)) <<
        <| SUM_fun eta (PBot : _ -C-> DL _) << SemVal v1,
           SUM_fun eta (PBot : _ -C-> DL _) << SemVal v2 |>
| TIFZ _ _ _ v e1 e2 => EV <<
        <| SUM_fun (SUM_fun (K _ (SemExp e1)) (K _ (SemExp e2)) << zeroCase)
                          (PBot : _ -C-> SemEnv n -C-> DL VInf) << SemVal v, ID |>
end.

Lemma Sem_eq:
 (forall n v (tv0:VTyping n v) n' k x
                          (tv1:VTyping n' (shiftV x k v)) env0 env1,
    (forall i (nli:i < n) nlik,
       projenv nli env0 ==
       @projenv (i+(if bleq_nat x i then k else 0)) _ nlik env1) ->
              SemVal tv0 env0 == SemVal tv1 env1) /\
 (forall n e (te0:ETyping n e) n' k x
             (te1:ETyping n' (shiftE x k e)) env0 env1,
    (forall i (nli:i < n) nlik,
       projenv nli env0 == @projenv (i+(if bleq_nat x i then k else 0)) _ nlik env1) ->
              SemExp te0 env0 == SemExp te1 env1).
Proof.
apply Typing_ind.
intros n m l n' k x.
simpl. case_eq (bleq_nat x m) ; intros xm tv1; dependent inversion tv1 ; clear tv1 ; intros env0 env1 C.
simpl.
specialize (C _ l). rewrite xm in C. specialize (C l0). apply C.
specialize (C _ l). rewrite xm in C. assert (m+0 = m) as A by omega. rewrite A in C.
apply (C l0).

intros n m n' k x tv1. dependent inversion tv1 ; clear tv1 ; intros env0 env1 C.
simpl.
repeat (rewrite fcont_comp_simpl).
refine (app_eq_compat (Oeq_refl (@INL (Discrete nat) (DInf -C-> DInf))) _).
repeat (rewrite K_simpl). auto.

intros n e te IHe n' k x tv1 ; dependent inversion tv1 ; clear tv1 ; intros env0 env1 C.
simpl. repeat (rewrite fcont_comp_simpl).
refine (app_eq_compat (Oeq_refl (@INR (Discrete nat) (DInf -C-> DInf))) _).
refine (app_eq_compat (Oeq_refl _) _).
refine (fcont_eq_intro _).
intros v. repeat (rewrite curry_simpl).
specialize (IHe _ _ _ e1 (env0,v) (env1,v)).
repeat (rewrite fcont_comp_simpl).
refine (app_eq_compat (Oeq_refl _) _).
apply IHe. intros i ; case i ; clear i ; simpl. intros _ _.
repeat (rewrite SND_simpl). auto.
intros i nli nlik. repeat (rewrite fcont_comp_simpl ; rewrite FST_simpl).
simpl. apply C.

intros n v tv IHv n' k x te ; dependent inversion te ; intros env0 env1 C.
simpl. repeat (rewrite fcont_comp_simpl).
refine (app_eq_compat (Oeq_refl _) _).
apply IHv. apply C.

intros n v1 v2 tv1 IH1 tv2 IH2 n' k x ta ; dependent inversion ta ; intros env0 env1 C.
simpl.
repeat (rewrite fcont_comp_simpl).
refine (app_eq_compat (Oeq_refl _) _).
repeat (rewrite PROD_fun_simpl). repeat (rewrite PAIR_simpl). simpl.
specialize (IH1 _ _ _ v env0 env1 C).
specialize (IH2 _ _ _ v0 env0 env1 C).
refine (pair_eq_compat IH1 IH2).

intros n e1 e2 te1 IH1 te2 IH2 n' k x ta ; dependent inversion ta ; intros env0 env1 C.
simpl.
repeat (rewrite fcont_comp_simpl).
repeat (rewrite PROD_fun_simpl).
repeat (rewrite curry_simpl).
specialize (IH1 _ _ _ e env0 env1 C).
refine (Oeq_trans (app_eq_compat (Oeq_refl _) (pair_eq_compat (Oeq_refl _) IH1)) _).
refine (KLEISLIR_eq _ _ _).
intros v0 v1 sv0 sv1.
specialize (IH2 _ _ _ e4 (env0,v0) (env1,v1)).
refine (IH2 _). intros i. case i ; clear i.
simpl. intros _ _. repeat (rewrite SND_simpl). simpl.
apply (vinj (Oeq_trans (Oeq_sym sv0) sv1)).

simpl. intros i nli nlik.
repeat (rewrite fcont_comp_simpl ; rewrite FST_simpl). simpl.
apply C.

intros vv v1. exists vv. auto.
intros vv v1. exists vv. auto.

intros n v e1 e2 tv IHv te1 IH1 te2 IH2 n' k x tif env0 env1 C.
dependent inversion tif.
simpl. repeat (rewrite fcont_comp_simpl). repeat (rewrite PROD_fun_simpl).
repeat (rewrite ID_simpl). simpl.
rewrite EV_simpl. rewrite EV_simpl. 
repeat (rewrite fcont_comp_simpl).
specialize (IH1 _ _ _ e env0 env1 C).
specialize (IHv _ _ _ v1 env0 env1 C).
specialize (IH2 _ _ _ e4 env0 env1 C).
refine (Oeq_trans _ (App_eq_compat (app_eq_compat (Oeq_refl (SUM_fun _ _)) IHv) (Oeq_refl env1))).
repeat (rewrite SUM_fun_simpl). fold VInf. case (SemVal tv env0) ; intros tt ; simpl ; case tt.
unfold INL ; auto. unfold INR ; auto.  intros ff _. auto.

(* TOP *)
intros n op v1 v2 tv1 IH1 tv2 IH2 n' k x te1 env0 env1 C.
dependent inversion te1. simpl.
repeat (rewrite fcont_comp_simpl).
refine (app_eq_compat (Oeq_refl _) _).
rewrite PROD_fun_simpl. rewrite PROD_fun_simpl. simpl.
repeat (rewrite fcont_comp_simpl).
refine (@pair_eq_compat (DL (Discrete nat)) (DL (Discrete nat)) _ _ _ _ _ _).
refine (app_eq_compat (Oeq_refl _) _).
apply (IH1 _ _ _ v env0 env1 C).
refine (app_eq_compat (Oeq_refl _) _).
apply (IH2 _ _ _ v4 env0 env1 C).
Qed.

Lemma shift_nil: (forall v k, shiftV k 0 v = v) /\
                 (forall e k, shiftE k 0 e = e).
apply ExpValue_ind ; intros ; simpl ;
 try (try (rewrite (H0 k)) ; try (rewrite (H1 k)) ; try (rewrite (H2 k));
      try (rewrite (H k)) ; try (rewrite (H (S k))) ; try (rewrite (H0 (S k))) ;
      try (rewrite (H (S (S k)))) ; auto).
  case_eq (bleq_nat k n) ; intros beq ; auto.
Qed.

Lemma projenv_irr: forall n i (p1:i < n) (p2:i < n), projenv p1 == projenv p2.
intros n. induction n.
intros i incon. inversion incon.

intros i. case i. simpl. auto. clear i.
intros i p1 p2. simpl. specialize (IHn _ (lt_S_n i n p1) (lt_S_n i n p2)).
rewrite IHn. auto.
Qed.

Lemma Sem_eqV: forall n v (ty0: VTyping n v) (ty1: VTyping n v), SemVal ty0 == SemVal ty1.
intros n v tv1 tv2.
simpl. refine (fcont_eq_intro _).
intros e.
assert (xx := proj1 Sem_eq _ _ tv1).
specialize (xx n 0 0). rewrite (proj1 shift_nil) in xx.
specialize (xx tv2 e e). apply xx.
intros i. simpl. assert (i + 0 = i) as A by omega. rewrite A.
intros nli nlik.
apply (fcont_eq_elim (projenv_irr nli nlik) e).
Qed.

Lemma Sem_eqE: forall n v (ty0: ETyping n v) (ty1: ETyping n v), SemExp ty0 == SemExp ty1.
intros n v tv1 tv2.
simpl. refine (fcont_eq_intro _).
intros e.
assert (xx := proj2 Sem_eq _ _ tv1).
specialize (xx n 0 0). rewrite (proj2 shift_nil) in xx.
specialize (xx tv2 e e). apply xx.
intros i. simpl. assert (i + 0 = i) as A by omega. rewrite A.
intros nli nlik.
apply (fcont_eq_elim (projenv_irr nli nlik) e).
Qed.

