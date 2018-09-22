Require Import utility.
Require Import PredomCore.
Require Import PredomProd.
Require Import PredomSum.
Require Import PredomFix.
Require Import PredomLift.
Require Import PredomKleisli.

Set Implicit Arguments.
Unset Strict Implicit.

Record BiFunctor : Type := mk_functor
  { ob : cpo -> cpo -> cpo ;
    morph : forall (A B C D : cpo),
               (B -C-> A) *c* (C -C-> D) -C-> (ob A C -C-> ob B D) ;
    morph_comp: forall A B C D E F f g h k,
                 morph B E D F (f,g) <<  morph A B C D (h, k) 
                 == morph _ _ _ _ (h << f, g << k) ;
    morph_id : forall A B, morph _ _ _ _ (@ID A , @ID B) == ID
  }.

Add Parametric Morphism lc D E F G : (@morph lc D E F G)
with signature (@Oeq (Dprod (E -C-> D) (F -C-> G))) ==> (@Oeq _)
as morph_eq_compat.
intros p0 p1 peq. split ; auto.
Qed.

Add Parametric Morphism lc D E F G : (@morph lc D E F G)
with signature (@Ole (Dprod (E -C-> D) (F -C-> G))) ++> (@Ole _)
as morph_le_compat.
intros ; auto.
Qed.

Definition FStrict : BiFunctor -> Type :=
  fun BF => forall D E, Pointed D -> Pointed E -> (Pointed (ob BF D E)).

Definition EPpair (D E :cpo) (f : D -C-> E) (g:E -C-> D) := f << g <= (@ID E) /\ g << f == (@ID D).

Lemma ProjectionUnique: forall D E (f:D -C-> E) g g', EPpair f g -> EPpair f g' -> g == g'.
intros D E f g g' [l1 e1] [l2 e2].
split.
assert (xx:=fcont_comp_eq_compat e2 (Oeq_refl g)).
rewrite fcont_comp_assoc in xx. rewrite fcont_comp_unitL in xx.
rewrite <- xx. clear xx.
refine (Ole_trans (fcont_comp_le_compat (Ole_refl _) l1) _).
rewrite fcont_comp_unitR. auto.

assert (yy := fcont_comp_eq_compat e1 (Oeq_refl g')).
rewrite fcont_comp_assoc in yy. rewrite fcont_comp_unitL in yy.
rewrite <- yy. clear yy.
refine (Ole_trans (fcont_comp_le_compat (Ole_refl _) l2) _).
rewrite fcont_comp_unitR. auto.
Qed.

Lemma EPstrict : forall D E (f:D -C-> E) g {pd:Pointed D} {pe:Pointed E}, 
   EPpair f g -> f PBot == PBot /\ g PBot == PBot.
intros D E f g PD PE ep. unfold EPpair in ep.
destruct ep as [p e].
assert (PBot <= f PBot) as L by auto.
assert (monotonic g) as M by auto.
unfold monotonic in M. specialize (M _ _ L).
assert (xx:=fcont_eq_elim e PBot). rewrite fcont_comp_simpl in xx.
rewrite xx in M. rewrite ID_simpl in M. simpl in M.
clear xx L.
assert (PBot <= g PBot) as L by auto.
assert (monotonic f) as F by auto.
unfold monotonic in F. specialize (F _ _ L).
assert (xx := fcont_le_elim p PBot).
rewrite fcont_comp_simpl in xx. rewrite ID_simpl in xx.
rewrite xx in F. simpl in F. auto.
Qed.

Section RecursiveDomains.

Variable lc : BiFunctor.

(*
Add Parametric Morphism lc D E F G : (fun x y => (@morph lc D E F G) (x,y))
with signature (@Ole (E -c> D)) ++> (@Ole (F -c> G)) ++> (@Ole _)
as morph_le_compat2.
intros ; auto.
Qed.
*)

Add Parametric Morphism (D E F G:cpo) : (fun x y => (x,y))
with signature (@Ole (D -C-> E)) ++> (@Ole (F -C-> G)) ++> (@Ole (Dprod (D -C-> E) (F -C-> G)))
as pair_le_compat2.
intros ; auto.
Qed.

Add Parametric Morphism (D E F G:cpo) : (fun x y => (x,y))
with signature (@Oeq (D -C-> E)) ==> (@Oeq (F -C-> G)) ==> (@Oeq (Dprod (D -C-> E) (F -C-> G)))
as pair_eq_compat2.
intros ; auto.
Qed.


Lemma BiFuncEPtoEP: forall A B (f:A -C-> B) (g:B -C-> A), EPpair f g ->
          EPpair (morph lc _ _ _ _ (g,f))
                 (morph lc _ _ _ _ (f,g)).
intros A B f g ep.
unfold EPpair in *.
destruct ep as [e p].
repeat (rewrite morph_comp).
split.
rewrite (pair_le_compat2 e e).
rewrite morph_id. auto.
rewrite (pair_eq_compat2 p p).
rewrite morph_id. auto.
Qed.

Fixpoint Diter (n:nat) :=
match n with
| O => DOne
| S n => ob lc (Diter n) (Diter n)
end.

Variable fs : FStrict lc.

Lemma Diter_pointed: forall n, Pointed (Diter n).
intros n. induction n.
apply DOne_pointed.
simpl. apply (fs IHn IHn) ; auto.
Defined.

Fixpoint Injection (n:nat) : (Diter n) -c> (Diter (S n)) :=
match n with
| O => (@PBot _ (@fun_pointed (Diter O) _ (@Diter_pointed (S O))))
| S n => morph lc (Diter n) (Diter (S n)) (Diter n) (Diter (S n))
           (Projection n, Injection n)
end
with Projection (n:nat) : (Diter (S n)) -c> (Diter n) :=
match n with
| O => @PBot (Diter (S O) -C-> Diter O) (fun_pointed _ _)
| S n => morph lc (Diter (S n)) (Diter n) (Diter (S n)) (Diter n)
        (Injection n,Projection n)
end.

Lemma EP_IP: forall n, EPpair (Injection n) (Projection n).
intros n. induction n. simpl. split. simpl. intros x.
rewrite (@PBot_app DOne (ob lc DOne DOne) (@fs DOne DOne DOne_pointed DOne_pointed) tt).
refine (Pleast _).
rewrite <- K_com. refine (DOne_final _ _).
simpl.
apply (BiFuncEPtoEP IHn).
Qed.

Add Parametric Morphism n : (@Projection n)
with signature (@Oeq (Diter (S n))) ==> (@Oeq (Diter n))
as Projection_eq_compat.
induction n ; split ; auto.
Qed.

Add Parametric Morphism n : (@Injection n)
with signature (@Oeq (Diter n)) ==> (@Oeq (Diter (S n)))
as Injection_eq_compat.
induction n ; split ; auto.
Qed.

Add Parametric Morphism n : (Projection n)
with signature (@Ole (Diter (S n))) ++> (@Ole (Diter n))
as Projection_le_compat.
induction n ; auto.
Qed.

Add Parametric Morphism n : (Injection n)
with signature (@Ole (Diter n)) ++> (@Ole (Diter (S n)))
as Injection_le_compat.
induction n ; auto.
Qed.

Definition ProjSet := fun d => forall n, PROJ Diter n d == Projection n (PROJ Diter (S n) d).

Lemma ProjSet_inclusive: admissible ProjSet.
unfold ProjSet. unfold admissible.
intros c C n. simpl.
rewrite PROJ_simpl.
rewrite (fun d => Projection_eq_compat (Oeq_refl_eq (PROJ_simpl (S n) d (Di:=Diter)))).
assert (continuous (fcontit (Projection n))) as Cont by auto.
rewrite (lub_comp_eq (Proj (fun x => Diter x) (S n) @ c) Cont). clear Cont.
refine (lub_eq_compat _).
refine (fmon_eq_intro _).
intros m.
simpl. specialize (C m n). rewrite PROJ_simpl in C. rewrite C. auto.
Qed.

(** printing DInf %\ensuremath{D_\infty}% *)
Definition DInf : cpo := SubCPO (ProjSet_inclusive).

Fixpoint Projection_nm m (n:nat) : (Diter (n + m)) -c> (Diter m) :=
match n with 
| O => ID
| S n => Projection_nm m n << (Projection _)
end.

Fixpoint Injection_nm m (n:nat) : Diter m -c> Diter (n + m) :=
match n with
| O => ID
| S n => Injection _ << (Injection_nm m n)
end.

Require Import Eqdep_dec.
Definition nat_eq_unique := eq_proofs_unicity dec_eq_nat.

Definition Diter_coercionm n m (Eq:n = m) : (Diter n -m> Diter m).
intros n m Eq. exists (fun d => eq_rect n Diter d m Eq).
unfold monotonic.
intros d0 d1 dle. generalize Eq. rewrite <- Eq. clear Eq m.
intros Eq.
rewrite (nat_eq_unique Eq (refl_equal _)). auto.
Defined.

Definition Diter_coercion n m (Eq: n = m) : Diter n -c> Diter m.
intros n m Eq. exists (Diter_coercionm Eq).
unfold continuous. generalize Eq. rewrite <- Eq. clear Eq m. intros Eq c.
rewrite (nat_eq_unique Eq (refl_equal _)). clear Eq.
simpl. refine (lub_le _).
intros m. refine (Ole_trans _ (le_lub _ m)). auto.
Defined.

Definition t_nm n m : Diter n -c> (Diter m) :=
match (le_lt_dec m n) with
| left  ee => let Eq := (trans_eq (@le_plus_minus m n ee) (plus_comm _ _)) in 
                 Projection_nm m (n-m) << (Diter_coercion Eq)
| right ee => let Eq := (trans_eq (plus_comm _ _) (sym_eq (le_plus_minus _ _ (lt_n_Sm_le _ _ (lt_S _ _ ee))))) in
     Diter_coercion Eq << Injection_nm n (m-n)
end.

Lemma Diter_coercion_simpl: forall n (Eq:n = n), Diter_coercion Eq == ID.
intros n Eq. refine (fcont_eq_intro _). intros d.
rewrite ID_simpl. simpl. rewrite (nat_eq_unique Eq (refl_equal _)). auto.
Qed.

Lemma Proj_left_comp: forall k m, Projection_nm m (S k) == 
                     Projection m << Projection_nm (S m) k << Diter_coercion (plus_Snm_nSm _ _).
intros k. induction k. intros m. simpl. rewrite fcont_comp_unitL. rewrite fcont_comp_unitR.
rewrite (Diter_coercion_simpl). rewrite fcont_comp_unitR. auto.
intros m. simpl. simpl in IHk. rewrite IHk. clear IHk. repeat (rewrite fcont_comp_assoc).
refine (fcont_comp_eq_compat (Oeq_refl _) _).
refine (fcont_comp_eq_compat (Oeq_refl _) _).
assert (xx:=plus_Snm_nSm k m). assert (yy:= eq_S _ _ xx). rewrite <- (nat_eq_unique yy (plus_Snm_nSm (S k) m)).
rewrite <- (nat_eq_unique xx (plus_Snm_nSm _ _)).
generalize xx yy. rewrite <- xx. clear xx yy. intros e1 e2. repeat (rewrite (Diter_coercion_simpl)).
rewrite fcont_comp_unitL. rewrite fcont_comp_unitR. simpl. auto.
Qed.

Lemma Inject_right_comp: forall k m, Injection_nm m (S k) ==
          (Diter_coercion (sym_equal (plus_Snm_nSm _ _))) << Injection_nm (S m) k << Injection m.
intros k. induction k. intros m. simpl. rewrite fcont_comp_unitR. rewrite fcont_comp_unitR.
rewrite (Diter_coercion_simpl). rewrite fcont_comp_unitL. auto.
intros m. simpl. simpl in IHk. rewrite IHk. clear IHk. repeat (rewrite <- fcont_comp_assoc).
refine (fcont_comp_eq_compat _ (Oeq_refl _)).
refine (fcont_comp_eq_compat _ (Oeq_refl _)).
assert (xx := sym_equal (plus_Snm_nSm k m)).
rewrite <- (fun E => nat_eq_unique xx (sym_equal E)).
assert (yy := (sym_equal (plus_Snm_nSm (S k) m))).
rewrite <- (fun E => nat_eq_unique yy (sym_equal E)).
generalize xx yy. simpl. rewrite xx. clear xx yy. intros e1 e2. repeat (rewrite Diter_coercion_simpl).
rewrite fcont_comp_unitL. rewrite fcont_comp_unitR. simpl. auto.
Qed.

Lemma Diter_coercion_simpl_point: forall n (Eq:n = n) d, Diter_coercion Eq d = d.
intros n Eq d. rewrite (nat_eq_unique Eq (refl_equal _)). auto.
Qed.

Lemma le_lt_dec_left : forall n m (p:(n <= m) % nat), exists pp, le_lt_dec n m = left _ pp.
intros. case_eq (le_lt_dec n m). intros pp ll. exists pp. auto.
intro incon. assert False as F by omega. inversion F.
Qed.

Lemma Diter_coercion_comp: forall x y z (Eq1:x = y) (Eq2 : y = z), 
     Diter_coercion Eq2 << Diter_coercion Eq1 == Diter_coercion (trans_equal Eq1 Eq2).
intros x y z Eq1. generalize Eq1. rewrite Eq1. clear x Eq1.
intros Eq1 Eq2. generalize Eq2. rewrite <- Eq2. clear Eq2. intros Eq2.
repeat (rewrite Diter_coercion_simpl). rewrite fcont_comp_unitL. auto.
Qed.

Lemma le_lt_dec_right : forall n m , n > m -> exists pp, le_lt_dec n m = right _ pp.
intros n m x. case_eq (le_lt_dec n m). intros l. assert False as F by omega. inversion F.
intros. eexists ; auto.
Qed.

Lemma t_nmProjection: forall n m, t_nm n m == Projection m << t_nm n (S m).
intros n m.
unfold t_nm.
case_eq (le_lt_dec m n). case_eq (le_lt_dec (S m) n).
intros l0 _ l1 _.
rewrite <- fcont_comp_assoc.
assert (xx:=Proj_left_comp (n-S m) m).
assert (yy:=(plus_Snm_nSm (n - S m) m)).
rewrite <- (nat_eq_unique yy (plus_Snm_nSm _ _)) in xx.
assert (zz:= fcont_comp_eq_compat xx (Oeq_refl (Diter_coercion (sym_equal yy)))).
rewrite fcont_comp_assoc in zz.
rewrite Diter_coercion_comp in zz. rewrite Diter_coercion_simpl in zz. rewrite fcont_comp_unitR in zz.
rewrite <- zz.
clear xx zz.
assert ((S (n - S m)) + m = n - m + m) as A by omega.
assert (Projection_nm m (S (n - S m)) == Projection_nm m (n - m) << Diter_coercion A).
generalize A.
assert (S (n - S m) = n - m) as AA by omega. rewrite AA. clear A AA.
intros Eq. rewrite Diter_coercion_simpl. rewrite fcont_comp_unitR. auto.
rewrite H. repeat (rewrite fcont_comp_assoc).
refine (fcont_comp_eq_compat (Oeq_refl _) _). repeat (rewrite Diter_coercion_comp).
rewrite <- (nat_eq_unique (trans_eq (le_plus_minus m n l1) (plus_comm m (n - m)))
           ((trans_equal
        (trans_equal
           (trans_eq (le_plus_minus (S m) (n) l0)
              (plus_comm (S m) (n - S m))) (sym_equal yy)) A))).
auto.

intros l _ ll _. assert (n = m). omega.  generalize l ll. rewrite H. clear H l ll n.
intros l ll.
assert (xx := (trans_eq (le_plus_minus m m ll) (plus_comm m (m - m)))).
rewrite <- (nat_eq_unique xx (trans_eq (le_plus_minus m m ll) (plus_comm m (m - m)))).
assert (S m - m + m = S m) as yy by omega.
rewrite <- (nat_eq_unique yy (trans_eq (plus_comm (S m - m) m)
            (sym_eq
               (le_plus_minus m (S m)
                  (lt_n_Sm_le m (S m) (lt_S m (S m) l)))))).
assert (S m - m = S O) as A by omega. generalize yy. rewrite A. clear A yy.
intros yy. simpl. rewrite fcont_comp_unitR.
assert (m - m = 0) as A by omega. generalize xx. rewrite A. clear A xx.
intros xx. simpl. rewrite fcont_comp_unitL. repeat (rewrite Diter_coercion_simpl).
rewrite fcont_comp_unitL.
destruct (EP_IP m) as [_ A]. rewrite A. auto.

intros ll _. assert (S m > n) as l by omega.
destruct (le_lt_dec_right l) as [pp xx].
rewrite xx. clear xx.

assert (m - n + n = m) as xx by omega.
rewrite <- (nat_eq_unique xx (trans_eq (plus_comm (m - n) n)
         (sym_eq
            (le_plus_minus n m (lt_n_Sm_le n m (lt_S n m ll)))))).
assert (S m - n + n = S m) as yy by omega.
rewrite <- (nat_eq_unique yy (trans_eq (plus_comm (S m - n) n)
            (sym_eq
               (le_plus_minus n (S m)
                  (lt_n_Sm_le n (S m) (lt_S n (S m) pp)))))).
generalize yy.
assert (S m - n = S (m - n)) as A. clear xx yy pp l. omega.
rewrite A. simpl. clear A yy. intros yy.
rewrite <- fcont_comp_assoc. rewrite <- fcont_comp_assoc.
refine (fcont_comp_eq_compat _ (Oeq_refl _)).
generalize xx yy. rewrite xx. clear xx yy. intros xx yy. repeat (rewrite Diter_coercion_simpl).
rewrite (fcont_comp_unitR).
destruct (EP_IP m) as [_ X]. rewrite X. auto.
Qed.

Lemma t_nn_ID: forall n, t_nm n n == @ID (Diter n).
intros n.
unfold t_nm. case_eq (le_lt_dec n n). intros l _. assert (n - n = 0) by omega.
assert (xx := (trans_eq (le_plus_minus n n l) (plus_comm n (n - n)))).
rewrite (nat_eq_unique (trans_eq (le_plus_minus n n l) (plus_comm n (n - n))) xx).
generalize xx. rewrite H. simpl. intros yy. rewrite (Diter_coercion_simpl). rewrite fcont_comp_unitL.
auto.
intros incon. assert False as F by omega. inversion F.
Qed.

Lemma t_nmProjection2: forall n m, (m <= n) % nat -> t_nm (S n) m == t_nm n m << Projection n.
intros n m nm.
assert (exists x, n - m = x) as X by (exists (n - m) ; auto).
destruct X as [x X].
generalize n m X nm. clear n m nm X.
induction x. intros n m E EE.
assert (n = m) as e by omega. rewrite e in *. clear e n E EE.
rewrite t_nmProjection. repeat (rewrite t_nn_ID).
rewrite fcont_comp_unitR. rewrite fcont_comp_unitL. auto.
intros n. case n. clear n. intros m I. assert False as F by omega. inversion F.
clear n. intros n m E EE.
rewrite (t_nmProjection (S n)). rewrite fcont_comp_assoc. rewrite <- (IHx (S n) (S m)) ; try omega.
rewrite t_nmProjection. auto.
Qed.

Lemma t_nmEmbedding: forall n i, t_nm n i == t_nm (S n) i << Injection n.
intros n i.
unfold t_nm.
case_eq (le_lt_dec i n). intros l E.
assert (i <= S n) % nat as A by omega.
unfold t_nm.
destruct (le_lt_dec_left A) as [pp ll]. rewrite ll. clear ll E.
assert (S n = S n - i + i) as xx by omega.
rewrite <- (nat_eq_unique xx (trans_eq (le_plus_minus i (S n) pp) (plus_comm i (S n - i)))).
generalize xx.
assert (S n - i = S (n - i)) by omega. rewrite H. clear H xx.
intros xx. simpl. repeat (rewrite fcont_comp_assoc). refine (fcont_comp_eq_compat (Oeq_refl _) _).
assert (n = n - i + i) as yy by omega.
rewrite <- (nat_eq_unique yy (trans_eq (le_plus_minus i n l) (plus_comm i (n - i)))).
assert (S n = S (n - i + i)) by auto. rewrite (nat_eq_unique xx H).
generalize H yy. rewrite <- yy. clear yy xx H.
intros xx yy. repeat (rewrite Diter_coercion_simpl). rewrite fcont_comp_unitL.
destruct (EP_IP n) as [_ a]. rewrite a. auto.
intros l _. unfold t_nm. case_eq (le_lt_dec i (S n)).
intros ll E. assert (i = S n) as A by omega.
assert (i - n + n = i) as xx by omega.
rewrite <- (nat_eq_unique xx (trans_eq (plus_comm (i - n) n)
        (sym_eq (le_plus_minus n i (lt_n_Sm_le n i (lt_S n i l)))))).
assert (S n = S n - i + i) as yy by omega.
rewrite <- (nat_eq_unique yy (trans_eq (le_plus_minus i (S n) ll) (plus_comm i (S n - i)))).
assert (S n - i = 0) as B by omega.
generalize yy. rewrite B. clear B.
simpl. clear yy. intros yy. rewrite fcont_comp_unitL.
assert (i - n = 1). omega. generalize xx. rewrite H. simpl.
clear H xx. intros xx. rewrite (nat_eq_unique xx yy). rewrite fcont_comp_unitR.
auto.

intros ll _.
assert (i - n + n = i) as xx by omega.
rewrite <- (nat_eq_unique xx (trans_eq (plus_comm (i - n) n)
        (sym_eq (le_plus_minus n i (lt_n_Sm_le n i (lt_S n i l)))))).
assert (i - S n + S n = i) as yy by omega.
rewrite <- (nat_eq_unique yy (trans_eq (plus_comm (i - S n) (S n))
         (sym_eq
            (le_plus_minus (S n) i (lt_n_Sm_le (S n) i (lt_S (S n) i ll)))))).
assert (i - n = S (i - S n)) by omega. generalize xx.
rewrite H. simpl.
assert (bla:=Inject_right_comp (i - S n) n).
assert (lll := (sym_equal (plus_Snm_nSm (i - S n) n))).
assert (bb := fun a b => @fcont_comp_eq_compat _ _ a _ _ (Oeq_refl b) _ _ bla).
specialize (bb _ (Diter_coercion (sym_equal lll))).
clear bla.
repeat (rewrite <- fcont_comp_assoc in bb). rewrite Diter_coercion_comp in bb.
rewrite Diter_coercion_simpl in bb. rewrite fcont_comp_unitL in bb.
clear xx. intros xx. rewrite fcont_comp_assoc. rewrite <- bb.
clear bb. simpl.
repeat (rewrite <- fcont_comp_assoc).
generalize lll yy xx. simpl. clear xx yy lll. intros lll yy xx.
refine (fcont_comp_eq_compat _ (Oeq_refl _)).
refine (fcont_comp_eq_compat _ (Oeq_refl _)).
generalize xx yy lll. simpl. rewrite yy. clear xx yy lll.
intros xx yy lll. rewrite Diter_coercion_simpl. rewrite fcont_comp_unitL.
rewrite (nat_eq_unique (sym_equal lll) xx). auto.
Qed.

Lemma t_nmEmbedding2: forall n m, (n <= m) % nat -> t_nm n (S m) == Injection m << t_nm n m.
intros n m nm.
assert (exists x, m - n = x) as X by (exists (m - n) ; auto).
destruct X as [x X].
generalize n m X nm. clear n m nm X.
induction x. intros n m E EE.
assert (n = m) as e by omega. rewrite e in *. clear e n E EE.
rewrite t_nmEmbedding. repeat (rewrite t_nn_ID).
rewrite fcont_comp_unitR. rewrite fcont_comp_unitL. auto.
intros n m. case m. clear m. intros I. assert False as F by omega. inversion F.
clear m. intros m E.
rewrite (t_nmEmbedding n (S m)). rewrite <- fcont_comp_assoc. rewrite <- (IHx (S n) (S m)) ; try omega.
rewrite t_nmEmbedding. auto.
Qed.

Lemma t_nm_bla: forall n i d, ProjSet d -> t_nm n i (d n) <= d i.
intros n i d P.
case_eq (le_lt_dec i n).
intros l ll.
assert (exists x, x = n - i). eexists. apply refl_equal. destruct H as [nn nne].
generalize n i l nne. clear nne ll l n i. induction nn.
intros n m leq nn. assert (n = m). assert (xx:=le_plus_minus _ _ leq). omega.
rewrite H. 
rewrite (fcont_eq_elim (t_nn_ID m) (d m)). auto.

intros n m lnm SS. assert (nn = n - (S m)) as A by omega.
assert (S m <= n) % nat as B by omega.
specialize (IHnn _ _ B A).
assert (aa:= t_nmProjection n m). destruct aa as [aa _].
refine (Ole_trans (app_le_compat aa (Ole_refl _)) _). clear aa.
simpl.
refine (Ole_trans (app_le_compat (Ole_refl _) IHnn) _).
unfold ProjSet in P. specialize (P m). repeat (rewrite PROJ_simpl in P). rewrite P. auto.

assert (exists m, m = i - n) by (eexists ; auto).
destruct H as [m meq]. intros l _. assert (n <= i) % nat as A by omega.
generalize i n meq A. clear A l meq i n. induction m.
intros n m nmeq leq. assert (n = m) as A. assert (xx:=le_plus_minus _ _ leq). omega.
rewrite A in *.
rewrite (fcont_eq_elim (t_nn_ID m) (d m)). auto.

intros i n Sn leq.
assert (m = i - (S n)) as A by omega. assert (S n <= i) % nat as B by omega.
specialize (IHm _ _ A B).
assert (aa := t_nmEmbedding n i).
simpl. rewrite (app_eq_compat aa (Oeq_refl _)).
rewrite fcont_comp_simpl. rewrite <- IHm.
refine (app_le_compat (Ole_refl _) _).
unfold ProjSet in P. specialize (P n). repeat (rewrite PROJ_simpl in P).
destruct P as [P _]. rewrite P.
destruct (EP_IP n) as [xx _]. rewrite <- fcont_comp_simpl.
assert (yy:=fcont_le_elim xx (d (S n))). apply yy.
Qed.

Lemma t_nmProjSet n : forall d, ProjSet (PRODI_fun (t_nm n) d).
intros n. intros d. unfold ProjSet. intros m.
rewrite PROJ_com_point. rewrite PROJ_com_point.
rewrite <- fcont_comp_simpl.
refine (app_eq_compat _ (Oeq_refl _)).
apply (t_nmProjection n m).
Qed.

Definition Embeddings n := InheritFun ProjSet_inclusive (@t_nmProjSet n) : Diter n -C-> DInf.

Definition Projections n := PROJ _ n << Forget ProjSet_inclusive : DInf -C-> Diter n.

Lemma Projection_comp: forall n, (Projections n) == Projection n << Projections (S n).
intros n. unfold Projections.
refine (fcont_eq_intro _). intros d.
assert (exists dd, dd = Forget ProjSet_inclusive d). eexists ; auto.
destruct H as [dd F].
repeat (rewrite fcont_comp_simpl).
rewrite <- F.
assert (yy:= @ForgetP _ _ ProjSet_inclusive d n). rewrite <- F in yy.
apply yy.
Qed.

Lemma Embedding_comp: forall n, Embeddings n == Embeddings (S n) << Injection n.
intros. unfold Embeddings.

assert (forall d, ProjSet ((PRODI_fun (t_nm (S n)) << Injection n) d)) as XX.
intros d. rewrite fcont_comp_simpl. unfold ProjSet.
intros m. rewrite PROJ_com_point. rewrite PROJ_com_point.
rewrite <- (fun D E F G => @fcont_comp_simpl _ D E F G (Injection n d)).
refine (app_eq_compat _ (Oeq_refl _)).
refine (t_nmProjection (S n) m).
rewrite (InheritFun_comp (ProjSet_inclusive) (@t_nmProjSet (S n)) XX).
refine (InheritFun_eq_compat _ _ _ _). clear XX.
refine (Dprodi_unique _).
intros i. rewrite PROJ_com. rewrite <- fcont_comp_assoc. rewrite PROJ_com.
refine (t_nmEmbedding n i).
Qed.

Lemma EPD : forall n, EPpair (Embeddings n) (Projections n).
intros n. unfold Embeddings. unfold Projections.
simpl. split. apply fcont_le_intro.
intros x. simpl. case x. clear x.
intros x P i0.
apply t_nm_bla. auto.
repeat (rewrite fcont_comp_assoc).
rewrite ForgetInherit. rewrite PROJ_com.
apply t_nn_ID.
Qed.

Definition Unroll : natO -m> DInf -C-> ob lc DInf DInf.
exists (fun n => morph lc (Diter n) (DInf) (Diter n) (DInf)
                    (Projections n, Embeddings n) << Projections (S n)).
unfold monotonic. intros n0 n1 leq.
refine (fcont_le_intro _). intros d.
repeat (rewrite fcont_comp_simpl).
assert (exists n, n = n1 - n0). eexists ; auto. destruct H as [n neq].
generalize n1 n0 leq neq. clear neq n1 n0 leq. induction n.
intros n1 n0 leq neq. assert (n0 = n1) as A. assert (xx:=le_plus_minus _ _ leq).
rewrite <- neq  in xx. omega. rewrite A. clear n0 neq leq A. auto.

intros n1 n0 leq neq. assert (S n0 <= n1) % nat as lleq. omega. clear leq.
assert (n = n1 - (S n0)) as nneq. omega. clear neq.
specialize (IHn _ _ lleq nneq).
rewrite <- IHn. clear IHn lleq nneq n1 n.
destruct ((morph_eq_compat lc (pair_eq_compat (Projection_comp n0) (Embedding_comp n0)))) as [A _].
refine (Ole_trans (app_le_compat A (Ole_refl _)) _). clear A.
assert (xx := proj2 (morph_comp lc (Projections (S n0)) (Embeddings (S n0)) (Projection n0) (Injection n0))).
refine (Ole_trans (app_le_compat xx (Ole_refl _)) _).
clear xx.
simpl. rewrite fcont_comp_simpl.
refine (app_le_compat _ _) ; auto.
assert (xx := ForgetP d (S n0)).
rewrite PROJ_simpl in xx. rewrite PROJ_simpl in xx. destruct xx as [x1 x2].
refine (Ole_trans (app_le_compat (Ole_refl _) x1) _).
simpl.
destruct (EP_IP (S n0)) as [xx _].
assert (yy:=fcont_le_elim xx (Forget (ProjSet_inclusive) d (S (S n0)))).
rewrite ID_simpl in yy. rewrite fcont_comp_simpl in yy. rewrite yy.
auto.
Defined.

(** printing UNROLL %\UNROLL% *)
Definition UNROLL := lub Unroll.

Definition Roll : natO -m> ob lc DInf DInf -C-> DInf.
exists (fun n => Embeddings (S n) << (morph lc _ _ _ _ (Embeddings n, Projections n))).
unfold monotonic. intros n0 n1 leq.
assert (exists n, n = n1 - n0). eexists ; auto.
destruct H as [n neq].
generalize n1 n0 leq neq. clear  neq n0 n1 leq.
induction n. intros n1 n0 l n. assert (n1 = n0).
assert (xx:=le_plus_minus _ _ l). omega.
rewrite H. auto.

intros n1 n0 leq neq. assert (n = n1 - S n0) as A by omega. assert (S n0 <= n1) % nat as B by omega.
specialize (IHn _ _ B A). rewrite <- IHn. clear IHn n neq A.
destruct ((morph_eq_compat lc (pair_eq_compat (Embedding_comp n0) (Projection_comp n0)))) as [A _].
rewrite A. clear A.
rewrite <- (morph_comp lc (Injection n0) (Projection n0) (Embeddings (S n0)) (Projections (S n0))).
rewrite <- fcont_comp_assoc.
refine (fcont_comp_le_compat _ (Ole_refl _)).
rewrite (Embedding_comp (S n0)). rewrite fcont_comp_assoc.
rewrite (proj1 (EP_IP (S n0))). rewrite fcont_comp_unitR. auto.
Defined.

(** printing ROLL %\ROLL% *)
Definition ROLL := lub Roll.

Definition ProjEmbed : natO -m> DInf -C-> DInf.
exists (fun n => Embeddings n << Projections n).
unfold monotonic. intros n0 n1 neq.
simpl. intros d i. case d. clear d. intros d Pd.
assert (exists n, n = n1 - n0). eexists ; auto.
destruct H as [n nn].
generalize n0 n1 neq nn. clear n0 n1 neq nn. induction n.
intros n0 n1 ll ee. assert (n0 = n1) as A. assert (xx:=le_plus_minus _ _ ll). omega.
rewrite A in *.  auto.
intros n0 n1 ll nn. assert (n = n1 - S n0) as A by omega.
assert (S n0 <= n1) % nat as B. omega.
specialize (IHn _ _ B A). rewrite <- IHn. clear IHn.
specialize (Pd n0). repeat (rewrite IPROJ_f in Pd).
assert (monotonic (t_nm n0 i)). auto.
unfold monotonic in H. destruct Pd as [Pd1 Pd2].
specialize (H _ _ Pd1). rewrite H. clear H.
rewrite <- fcont_comp_simpl.
destruct (t_nmEmbedding n0 i) as [xx _].
refine (Ole_trans (app_le_compat (fcont_comp_le_compat xx (Ole_refl _)) (Ole_refl _)) _).
assert (((t_nm (S n0) i << Injection n0) << Projection n0) <= t_nm (S n0) i) as X.
rewrite fcont_comp_assoc. destruct (EP_IP n0) as [aa _]. rewrite aa. rewrite fcont_comp_unitR.
auto.
refine (Ole_trans (app_le_compat X (Ole_refl _)) _). auto.
Defined.

Lemma ProjEmbed_simpl : forall n d, ProjEmbed n d = 
           (Embeddings n (Projections n d)).
intros n d. auto.
Qed.

Lemma DInf_unique : forall X (f g : X -c> DInf), 
  (forall n, PROJ Diter n << Forget ProjSet_inclusive << f ==  PROJ Diter n << Forget ProjSet_inclusive << g) -> f == g.
intros X f g C.
assert (Forget ProjSet_inclusive << f == Forget ProjSet_inclusive << g).
refine (Dprodi_unique _). apply C.
apply fcont_eq_intro. intros x. apply Forget_inj.
apply (fcont_eq_elim H x).
Qed.

(*
Lemma ID_lub : ID DInf == lub (ProjEmbed).
refine (fcont_eq_intro _). intros d. split.
refine (Forget_leinj _). rewrite ID_simpl. simpl.
refine (Dprodi_le_intro _).
intros n. simpl.
assert (ProjEmbed n d <= fcont_lub ProjEmbed d).
assert (xx := app_le_compat (le_lub (ProjEmbed) n) (Ole_refl d)).
rewrite xx. clear xx. auto. assert (aa := Forget_le_compat H). simpl in aa. rewrite <- aa.
clear H aa. unfold Embeddings. repeat (rewrite fcont_comp_simpl).
assert (xx := fcont_eq_elim (ForgetInherit  (ProjSet_inclusive) (t_nmProjSet (n:=n)))).
specialize (xx (PROJ (Diter) n
           (Forget (D:=Dprodi (Diter))
              (P:=fun d0 : forall i : nat, Diter i => ProjSet d0)
              (ProjSet_inclusive) d))).
rewrite fcont_comp_simpl in xx.
assert (yy := app_eq_compat (Oeq_refl (PROJ (Diter) n)) xx).
rewrite yy. clear yy xx.
rewrite PROJ_com_point.
rewrite (fcont_eq_elim (t_nn_ID n)). rewrite ID_simpl. simpl.
rewrite PROJ_simpl. auto.

refine (lub_le _). intros n. rewrite ID_simpl.
simpl. case d. clear d. intros d Fd i.
apply t_nm_bla. auto.
Qed.
*)

Lemma ID_lub : @ID DInf == lub (ProjEmbed).
apply DInf_unique. intros n.
assert (continuous (fcontit (PROJ Diter n << Forget ProjSet_inclusive))) as cc by auto.
apply fcont_eq_intro. intros d.
repeat (rewrite fcont_comp_simpl).
rewrite ID_simpl.
rewrite fcont_lub_simpl.
repeat (rewrite <- fcont_comp_simpl).
rewrite (lub_comp_eq (ProjEmbed <__> d) cc). clear cc.
repeat (rewrite fcont_comp_simpl).
split.
refine (Ole_trans _ (le_lub _ n)).
simpl. case d. clear d. intros d Pd. simpl.
rewrite PROJ_simpl. apply Ole_trans with (y:=d n). auto.
apply Ole_trans with (y:= t_nm n n (d n)) ; auto. assert (X:=fcont_eq_elim (t_nn_ID n) (d n)).
rewrite X. auto.
rewrite (lub_lift_left _ n). refine (lub_le _).
intros m. simpl. case d. clear d. intros d Pd.
rewrite PROJ_simpl. apply Ole_trans with (y:=d n) ; auto.
apply Ole_trans with (y:=t_nm (n+m) n (d (n+m))) ; auto.
assert (n+m = m + n) as A by omega. rewrite A. clear A.
induction m. simpl. apply (proj1 (fcont_eq_elim (t_nn_ID n) (d n))).
assert (X:=t_nmProjection2). specialize (X (m + n) n). rewrite (fun x => fcont_eq_elim (X x)  (d (S m + n))) ; try omega.
rewrite fcont_comp_simpl. unfold ProjSet in Pd.
specialize (Pd (m+n)). rewrite PROJ_simpl in Pd. rewrite PROJ_simpl in Pd.
assert (stable (t_nm (m + n) n)) as st by auto.
specialize (st _ _ Pd). rewrite <- st. apply IHm.
Qed.

Lemma DIso_ru: ROLL << UNROLL == ID.
assert (yy := fun X Y => @lub_comp2_eq _ _ _ (fcont_Comp DInf (ob lc DInf DInf) DInf) X Y 
                                Roll Unroll).
rewrite fcont_Comp_simpl in yy.
rewrite yy ; auto using fcont_Comp_continuous2. clear yy.
rewrite ID_lub.
apply Oeq_sym.
refine (Oeq_trans (lub_lift_left ProjEmbed 1) _).
refine (lub_eq_compat (c:=DInf -C-> DInf) _).
refine (fmon_eq_intro _).
intros n. simpl.
repeat (rewrite fcont_comp_assoc). 
rewrite <- (fun D G B C E p => @fcont_comp_assoc G D _ _ (morph lc DInf B C E p)).
destruct (BiFuncEPtoEP (EPD n)) as [_ xx].
rewrite xx. clear xx. rewrite fcont_comp_unitL. auto.
assert (xx := @fcont_Comp_continuous2 DInf (ob lc DInf DInf) DInf).
apply (continuous2_app xx).
Qed.

Lemma min_invariant: forall (d:DInf), d == lub (ProjEmbed <__> d).
intros d.
rewrite <- fcont_lub_simpl.
apply (fcont_eq_elim ID_lub d).
Qed.

Lemma DIso_ur: UNROLL << ROLL == ID.
unfold ROLL. unfold UNROLL.
assert (yy := fun X Y => @lub_comp2_eq _ _ _ (fcont_Comp (ob lc DInf DInf) DInf (ob lc DInf DInf)) X Y 
                                Unroll Roll).
rewrite fcont_Comp_simpl in yy.
rewrite yy ; auto using fcont_Comp_continuous2. clear yy.
rewrite <- morph_id.
assert ((@PAIR (DInf -C-> DInf) (DInf -C-> DInf) (@ID DInf) (@ID DInf)) == <| ID, ID |> (lub ProjEmbed)).
rewrite PROD_fun_simpl. rewrite PAIR_simpl. simpl.
rewrite (pair_eq_compat2 ID_lub ID_lub). auto.
rewrite H. clear H.
assert (continuous (fcontit (<| ID, @ID (DInf -C-> DInf)|>))) as C by auto.
rewrite (lub_comp_eq ProjEmbed C).
clear C. assert (continuous (fcontit (morph lc DInf DInf DInf DInf))) as C by auto.
rewrite (lub_comp_eq (fcontit (<| ID, ID|>) <m< ProjEmbed) C).
clear C.
refine (lub_eq_compat (c:=ob lc DInf DInf -C-> ob lc DInf DInf) _).
refine (fmon_eq_intro _). intros n.
simpl.
rewrite <- fcont_comp_assoc. rewrite (fun D G f => @fcont_comp_assoc D _ _ G f (Projections (S n))).
rewrite (proj2 (EPD (S n))). rewrite fcont_comp_unitR. rewrite morph_comp. auto.
clear yy. apply (continuous2_app).
apply fcont_Comp_continuous2.
Qed.

Lemma UNROLL_monic: forall x y, UNROLL x <= UNROLL y -> x <= y.
intros x y r. assert (monotonic ROLL) as M by auto.
specialize (M _ _ r). assert (xx:=fun x => fcont_eq_elim DIso_ru x).
assert (yx:=xx x). specialize (xx y). rewrite ID_simpl in *. rewrite fcont_comp_simpl in *. simpl in xx, yx.
rewrite xx in M. rewrite yx in M. apply M.
Qed.

Lemma ROLL_monic: forall x y, ROLL x <= ROLL y -> x <= y.
intros x y r. assert (monotonic UNROLL) as M by auto.
specialize (M _ _ r). assert (xx:=fun x => fcont_eq_elim DIso_ur x).
assert (yx:=xx x). specialize (xx y). rewrite ID_simpl in *. rewrite fcont_comp_simpl in *. simpl in xx, yx.
rewrite xx in M. rewrite yx in M. apply M.
Qed.

Instance DInf_pointed : Pointed DInf.
exists (Embeddings 0 tt).
intros d. case d. clear d. intros d pd.
unfold Embeddings. simpl. intros i.
refine (Ole_trans _ (t_nm_bla 0 i pd)).
case (d 0). auto.
Defined.

Instance FDInf_pointed : Pointed (ob lc DInf DInf).
exists (UNROLL PBot).
intros d.
refine (ROLL_monic _).
assert (xx:=fcont_eq_elim DIso_ru PBot).
rewrite fcont_comp_simpl in xx. rewrite ID_simpl in xx. rewrite xx.
rewrite Id_simpl. apply Pleast.
Defined.

(** printing delta %\ensuremath{\delta}% *)
Definition delta := curry (ROLL << uncurry (morph lc _ _ _ _) << ((<| ID, ID |>) *f* UNROLL)).

Lemma delta_simpl : forall e, delta e == ROLL << (morph lc _ _ _ _ (e,e)) << UNROLL.
intros e. unfold delta. simpl. refine (fcont_eq_intro _). auto.
Qed.

Lemma emp: forall i j, Projections i << Embeddings j == t_nm j i.
intros i j. case_eq (le_lt_dec i j). intros ij ltij.
assert (exists n, j - i = n) as A. exists (j - i). auto.
destruct A as [n nij]. clear ltij. generalize dependent i. generalize j. clear j.
induction n. intros j i ij ijn. assert (j = i) as A. omega. rewrite A. rewrite t_nn_ID.
apply (EPD i). intros j i ij ijs. specialize (IHn j (S i)).
assert (j - S i = n) as A by omega. assert (S i <= j) % nat as AA by omega.
specialize (IHn AA A). rewrite (Projection_comp i).
rewrite fcont_comp_assoc. rewrite IHn. rewrite <- (t_nmProjection). auto.
intros l. assert (j <= i) % nat as A by omega. intros _. clear l.
assert (exists n, i - j = n) as B. exists (i - j). auto.
destruct B as [n nij].
generalize j i A nij. clear i j A nij. induction n.
intros j i A e. assert (i = j) as B by omega. rewrite B. rewrite (t_nn_ID j).
apply (EPD j).
intros j i A B. assert (S j <= i) % nat as AA by omega.
assert (i - S j = n) as BB by omega.
specialize (IHn _ _ AA BB).
rewrite (Embedding_comp j). rewrite <- fcont_comp_assoc.
rewrite IHn. rewrite <- (t_nmEmbedding ). auto.
Qed.

Lemma t_nm_morph: forall m n, morph lc (Diter n) (Diter m) (Diter n) (Diter m)
     (t_nm m n, t_nm n m) == t_nm (S n) (S m).
intros m n. case_eq (le_lt_dec m n). intros l le.
assert (exists i, i = n - m) as A by (eexists ; auto).
destruct A as [i A].
generalize n m A l. clear le l A n m. induction i.
intros n m A B. assert (n = m) as Eq by omega. rewrite Eq.
rewrite (t_nn_ID (S m)).
rewrite (pair_eq_compat2 (t_nn_ID m) (t_nn_ID m)).
rewrite morph_id. auto.

intros n m A B. assert (i = n - S m) as AA by omega. assert (S m <= n) % nat as BB by omega.
specialize (IHi _ _ AA BB).
rewrite (pair_eq_compat2 (t_nmEmbedding m n) (t_nmProjection n m)).
rewrite <- morph_comp.
rewrite IHi. rewrite (t_nmProjection (S n) (S m)). auto.

intros l _. assert (exists i, i = m - n) as A by (eexists ; auto).
destruct A as [i A]. assert (n <= m) % nat as ll by omega.
generalize n m A ll. clear ll l A n m. induction i.
intros n m A B. assert (n = m) as Eq by omega. rewrite Eq.
rewrite (t_nn_ID (S m)).
rewrite (pair_eq_compat2 (t_nn_ID m) (t_nn_ID m)).
apply morph_id.

intros m n A B.
rewrite (pair_eq_compat2 (t_nmProjection n m) (t_nmEmbedding m n)).
rewrite <- morph_comp.
specialize (IHi (S m) n).
assert (i = n - S m) as AA by omega. assert (S m <= n) % nat as BB by omega.
rewrite (IHi AA BB). rewrite (t_nmEmbedding (S m) (S n)). auto.
Qed.

Lemma ROLL_Embed: forall n, ROLL << morph lc _ _ _ _ (Projections n, Embeddings n) == Embeddings (S n).
intros n.
refine (fcont_eq_intro _).
intros d. refine (Forget_inj _).
repeat (rewrite fcont_comp_simpl). unfold ROLL.
rewrite fcont_lub_simpl.
assert (continuous (fcontit (Forget ProjSet_inclusive))) as C by auto.
assert (forall d, Forget ProjSet_inclusive d == fcontit (Forget ProjSet_inclusive) d) as F. auto.
rewrite F. rewrite (fun c => lub_comp_eq c C). clear C F.
refine (Dprodi_eq_intro _).
intros i. simpl.
split.
refine (Ole_trans (proj1 (lub_lift_left _ i)) _). simpl.
refine (lub_le _). intros m. simpl.
assert (xx:=(morph_comp lc (Embeddings ((i + m))) (Projections ((i+m))) (Projections n) (Embeddings n))).
rewrite (pair_eq_compat2 (emp n ((i + m))) (emp ((i + m)) n)) in xx.
assert (yy := (fcont_eq_elim xx d)). rewrite fcont_comp_simpl in yy.
assert (stable (t_nm (S (i+m)) i)) as st by auto.
specialize (st _ _ yy).
clear yy. refine (Ole_trans (proj1 st) _). clear st xx.
assert ((Projections i << Embeddings (S n)) d == Forget (D:=Dprodi Diter) (P:=ProjSet) ProjSet_inclusive
     (Embeddings (S n) d) i) as xx by auto.
rewrite <- xx. clear xx.
rewrite <- fcont_comp_simpl. refine (app_le_compat _ (Ole_refl _)).
assert (t_nm (S (i + m)) i << t_nm (S n) (S(i + m)) == t_nm (S n) i) as A.
induction m. assert (i+0 = i) as I by omega. rewrite I. clear I.
rewrite t_nmProjection2 ; auto. rewrite fcont_comp_assoc.
rewrite t_nn_ID. rewrite fcont_comp_unitL. rewrite <- t_nmProjection. auto.
assert (i+S m = S (i+m)) as I by omega. rewrite I. clear I.
rewrite <- IHm. clear IHm. rewrite t_nmProjection2 ; try omega. rewrite fcont_comp_assoc.
rewrite <- t_nmProjection. auto.
rewrite emp. rewrite t_nm_morph. rewrite A. auto.

refine (Ole_trans _ (le_lub (c:=Diter i) _ i)). simpl.
assert (xx:=(morph_comp lc (Embeddings i) (Projections i) (Projections n) (Embeddings n))).
rewrite (pair_eq_compat2 (emp n i) (emp i n)) in xx. rewrite t_nm_morph in xx.
assert (yy := (fcont_eq_elim xx d)). rewrite fcont_comp_simpl in yy.
clear xx.
assert (stable (t_nm (S i) i)) as sf by auto. specialize (sf _ _ yy).
rewrite sf. assert (t_nm (S i) i << (t_nm (S n) (S i)) == t_nm (S n) i) as ee.
rewrite t_nmProjection2 ; auto. rewrite t_nn_ID. rewrite fcont_comp_unitL.
rewrite <- t_nmProjection. auto. rewrite (fcont_eq_elim ee d).
auto.
Qed.

Lemma UNROLL_Embed: forall n, (morph lc _ _ _ _ (Embeddings n, Projections n) << UNROLL == Projections (S n)).
intros n.
assert (EPpair (Embeddings (S n)) (morph lc DInf (Diter n) DInf (Diter n) (Embeddings n, Projections n) <<
   UNROLL)).
split.
rewrite <- ROLL_Embed. rewrite <- fcont_comp_assoc.
rewrite (fun D E => @fcont_comp_assoc D E _ _ ROLL).
assert (xx:= proj1 (BiFuncEPtoEP (EPD n))). rewrite xx. rewrite fcont_comp_unitR.
rewrite DIso_ru. auto.
rewrite <- ROLL_Embed. rewrite fcont_comp_assoc.
rewrite <- (fun D E => @fcont_comp_assoc D E _ _ UNROLL).
rewrite DIso_ur. rewrite fcont_comp_unitL. 
rewrite (proj2 (BiFuncEPtoEP (EPD n))). auto.
assert (E:=EPD (S n)).
apply (ProjectionUnique H E).
Qed.

Lemma id_min: @ID DInf == FIXP delta.
rewrite ID_lub. rewrite FIXP_simpl. rewrite Fixp_simpl.
unfold fixp. refine (lub_eq_compat (c:=DInf -C-> DInf) _).
refine (fmon_eq_intro _).
intros n. induction n. simpl. refine (fcont_eq_intro _).
intros d. rewrite fcont_comp_simpl. simpl.
rewrite K_simpl. simpl. case_eq (Projections 0 d). simpl. intros P. rewrite P. auto.

rewrite iterS_simpl. assert (stable (fcontit delta)) as sd by auto.
specialize (sd _ _ IHn). rewrite <- sd. clear sd IHn.
assert (fcontit delta (ProjEmbed n) == delta (ProjEmbed n)) as P by auto.
rewrite P. clear P. rewrite delta_simpl.
assert (forall n, ProjEmbed n == Embeddings n << Projections n). auto.
rewrite H. rewrite H.
rewrite <- morph_comp.
rewrite <- fcont_comp_assoc. rewrite ROLL_Embed.
rewrite fcont_comp_assoc. rewrite UNROLL_Embed. auto.
Qed.

End RecursiveDomains.

Definition Var : BiFunctor.
exists (ob := fun (D E:cpo) => E) (morph:=fun A B C D => SND).
intros.
repeat (rewrite SND_simpl). repeat (rewrite PAIR_simpl). simpl. auto.
intros. rewrite SND_simpl. auto.
Defined.

Definition Var_strict : FStrict Var.
unfold FStrict. intros. auto.
Defined.

Lemma PROD_MAP_simpl: forall D E F G f g, PROD_MAP D E F G f g = PROD_map f g.
intros. auto.
Qed.

Definition BiPair (A:BiFunctor) (B:BiFunctor) : BiFunctor.
intros A B.
exists (ob := fun (D E:cpo) => Dprod (ob A D E) (ob B D E))
  (morph:=fun D E F G => (@PROD_MAP (ob A D F) (ob B D F) (ob A E G) (ob B E G) @2_ (morph A D E F G)) (morph B D E F G)).
intros C D E F G H f g h k.
repeat (rewrite fcont_comp2_simpl).
repeat (rewrite PROD_MAP_simpl).
repeat (rewrite PROD_map_fun).
refine (Dprod_unique _ _).
rewrite <- fcont_comp_assoc. unfold PROD_map.
rewrite FST_PROD_fun. rewrite fcont_comp_assoc. rewrite FST_PROD_fun.
rewrite <- fcont_comp_assoc. rewrite morph_comp.
rewrite FST_PROD_fun.
auto.
rewrite <- fcont_comp_assoc. unfold PROD_map. rewrite SND_PROD_fun.
rewrite fcont_comp_assoc. rewrite SND_PROD_fun.
rewrite SND_PROD_fun. rewrite <- fcont_comp_assoc.
rewrite morph_comp. auto.

intros D E. rewrite fcont_comp2_simpl.
rewrite PROD_MAP_simpl. unfold PROD_map.
refine (Dprod_unique _ _).
rewrite FST_PROD_fun. rewrite fcont_comp_unitR.
rewrite morph_id. rewrite fcont_comp_unitL.
auto.
rewrite SND_PROD_fun.
rewrite fcont_comp_unitR. rewrite morph_id.
rewrite fcont_comp_unitL. auto.
Defined.

Definition BiPair_strict A B (fsA:FStrict A) (fsB:FStrict B) : FStrict (BiPair A B).
intros A B fA fB. unfold FStrict.
intros D E pD pE. unfold FStrict in fA. unfold FStrict in fB.
specialize (fA _ _ pD pE). specialize (fB _ _ pD pE).
exists (@PBot _ fA,@PBot _ fB).
intros p. simpl in p. case p. clear p.
intros p0 p1. auto.
Defined.

Lemma SUM_MAP_simpl: forall D E F G f g, SUM_MAP D E F G f g = SUM_map f g.
intros ; auto.
Qed.

Definition BiSum (A:BiFunctor) (B:BiFunctor) : BiFunctor.
intros A B. exists (ob:=fun D E => Dsum (ob A D E) (ob B D E))
  (morph:=fun D E F G => (@SUM_MAP (ob A D F) (ob B D F) (ob A E G) (ob B E G) @2_ (morph A D E F G)) (morph B D E F G)).
intros C D E F G H f g h k. repeat (rewrite fcont_comp2_simpl).
repeat (rewrite SUM_MAP_simpl).
simpl. refine (Dsum_unique _ _).
unfold SUM_map. rewrite fcont_comp_assoc. rewrite Dsum_lcom.
rewrite <- fcont_comp_assoc. rewrite Dsum_lcom. rewrite fcont_comp_assoc.
refine (fcont_comp_eq_compat (Oeq_refl _) _).
rewrite <- morph_comp. auto.

unfold SUM_map. rewrite fcont_comp_assoc. rewrite Dsum_rcom.
rewrite <- fcont_comp_assoc. rewrite Dsum_rcom. rewrite fcont_comp_assoc.
refine (fcont_comp_eq_compat (Oeq_refl _) _).
rewrite <- morph_comp. auto.

intros D E.
simpl.
rewrite fcont_comp2_simpl. rewrite SUM_MAP_simpl.
unfold SUM_map. refine (Oeq_sym (Dsum_unique _ _)).
rewrite fcont_comp_unitL. rewrite morph_id. rewrite fcont_comp_unitR.
auto.

rewrite fcont_comp_unitL. rewrite morph_id. rewrite fcont_comp_unitR. auto.
Defined.

Definition BiComp (A:BiFunctor) (B:BiFunctor) (C:BiFunctor) : BiFunctor.
intros A B C.
exists (ob := fun D E => ob C (ob A E D) (ob B D E)) 
 (morph := fun D E F G => (morph C (ob A F D) (ob A G E) (ob B D F) (ob B E G)) <<
           (PROD_fun ((morph A G F E D) << SWAP) (morph B D E F G))).

intros D E F G H J f g h k.
rewrite fcont_comp_simpl.
rewrite PROD_fun_simpl.
rewrite fcont_comp_simpl. assert ((SWAP (f, g)) == (g,f)).
simpl. unfold SWAP. rewrite PROD_fun_simpl. auto.
refine (Oeq_trans (fcont_comp_eq_compat (morph_eq_compat _ 
       (pair_eq_compat (morph_eq_compat _ H0) (Oeq_refl _))) (Oeq_refl _)) _). clear H0.
rewrite fcont_comp_simpl. rewrite PROD_fun_simpl.
rewrite fcont_comp_simpl.
assert ((SWAP (h, k)) == (k,h)) as X.
 unfold SWAP. rewrite PROD_fun_simpl. auto.
refine (Oeq_trans (fcont_comp_eq_compat (Oeq_refl _) (morph_eq_compat _ 
       (pair_eq_compat (morph_eq_compat _ X) (Oeq_refl _)))) _). clear X.
rewrite fcont_comp_simpl. rewrite PROD_fun_simpl.
rewrite fcont_comp_simpl.
assert ((@SWAP (_ -C-> _) (_ -C-> _) (h << f, g << k)) == (g << k,h << f)) as X.
unfold SWAP. rewrite PROD_fun_simpl. auto.
refine (Oeq_trans _ ((morph_eq_compat _
       (pair_eq_compat (morph_eq_compat _ (Oeq_sym X)) (Oeq_refl _))))). clear X.
rewrite <- morph_comp. rewrite  <- morph_comp. rewrite <- morph_comp. auto.

intros D E. rewrite fcont_comp_simpl. rewrite PROD_fun_simpl.
rewrite fcont_comp_simpl. assert ((@SWAP (D -C-> D) (E -C-> E) (ID, ID)) == (ID, ID)) as X.
unfold SWAP. rewrite PROD_fun_simpl. auto.
refine (Oeq_trans (morph_eq_compat _ (pair_eq_compat (morph_eq_compat _ X) (Oeq_refl _))) _).
rewrite morph_id. rewrite morph_id. rewrite morph_id. auto.

Defined.

Definition BiComp_strict A B C (fA:FStrict A) (fB:FStrict B) (fC:FStrict C) : FStrict (BiComp A B C).
intros A B C fA fB fC.
unfold FStrict. unfold FStrict in fA,fB,fC.
intros D E pD pE. simpl.
specialize (fA E D pE pD). specialize (fB D E pD pE).
apply fC ; auto.
Defined.

Definition BiArrow : BiFunctor.
exists (ob:= fun D E => D -C-> E)
     (morph:=fun D E F G => curry ((fcont_COMP _ _ _  @2_ (SND << FST))
                                     ((fcont_COMP _ _ _ @2_ @SND _ (D -C-> F))
                                                            (@FST (E -C-> D) (F -C-> G) << FST)))).
intros A B C D E F f g h k.
refine (fcont_eq_intro _). intros d.
repeat (rewrite curry_simpl). repeat (rewrite fcont_comp2_simpl).
rewrite fcont_comp_simpl. rewrite curry_simpl. rewrite fcont_comp2_simpl.
rewrite fcont_comp2_simpl. rewrite curry_simpl. repeat (rewrite fcont_comp_simpl).
repeat (rewrite fcont_COMP_simpl).
repeat (rewrite FST_simpl). simpl. repeat (rewrite SND_simpl). simpl.
rewrite fcont_comp_assoc. refine (fcont_comp_eq_compat (Oeq_refl _) _).
repeat (rewrite <- fcont_comp_assoc). refine (fcont_comp_eq_compat _ (Oeq_refl _)).
rewrite fcont_comp2_simpl. repeat (rewrite fcont_COMP_simpl).
repeat (rewrite fcont_comp_simpl). repeat (rewrite FST_simpl). simpl. rewrite fcont_comp2_simpl.
rewrite fcont_COMP_simpl. repeat (rewrite SND_simpl). simpl. rewrite fcont_comp_simpl.
repeat (rewrite FST_simpl). simpl. rewrite fcont_comp_assoc. auto.

intros A B. refine (fcont_eq_intro _). intros h.
rewrite curry_simpl. repeat (rewrite fcont_comp2_simpl). repeat (rewrite fcont_COMP_simpl).
repeat (rewrite fcont_comp_simpl). repeat (rewrite FST_simpl). simpl.
repeat (rewrite SND_simpl). simpl. rewrite fcont_comp_unitL.
rewrite fcont_comp_unitR. rewrite ID_simpl. auto.
Defined.

Definition BiArrow_strict : FStrict BiArrow.
unfold FStrict.
intros D E pD pE.
simpl.
apply (fun_pointed D).
apply pE.
Defined.

Definition BiConst (D:cpo) : BiFunctor.
intros D. exists (ob:= fun _ _ => D) (morph:=fun E F G H => @K _ (D -C-> D) (@ID D)).
intros A B C E F G f g h k.
repeat (rewrite K_simpl). rewrite fcont_comp_unitL. auto.

intros A B. rewrite K_simpl. auto.
Defined.

Definition BiConst_strict D {pd:Pointed D} : FStrict (BiConst D).
intros D pD. unfold FStrict.
intros E F _ _. simpl. auto.
Defined.

Definition BiLift_morph (F:BiFunctor) (A B C D : cpo) : 
        (Dprod (B -C-> A) (C -C-> D) -c> (DL (ob F A C)) -C-> DL (ob F B D)) :=
 (curry (uncurry KLEISLI << (curry (eta << uncurry (morph F A B C D))) *f* ID)).
(*
Lemma 
exists (fun p => kleisli (eta << morph F A B C D p)).
unfold monotonic. intros p0 p1 leq.
assert (monotonic (@KLEISLI (ob F A C) (ob F B D))) as M by auto.
repeat (rewrite <- KLEISLI_simpl).
apply M. rewrite leq. auto.
Defined.

Definition BiLift_morph (F:BiFunctor) (A B C D :cpo) :
        (Dprod (B -C-> A) (C -C-> D) -C-> (DL (ob F A C)) -C-> DL (ob F B D)).
intros F A B C D.
exists (BiLift_morphm F A B C D).
unfold continuous. intros c.
assert (continuous (BiLift_morphm F A B C D)) as cb.

assert (xx := @lub_comp_eq _ _ (fcontit (morph F A B C D)) c).
simpl in xx. assert (yy:= fun X=>fcont_comp_eq_compat (Oeq_refl eta) (xx X)).
refine (Ole_trans (@app_le_compat (ob F A C _BOT) _ _ _ _ _ _ (Ole_refl d)) _).
clear xx. Check (fun Z Y => App_eq_compat _ (yy Z)).
Check (app_eq_compat (Oeq_refl (@eta ()))).
refine (Ole_trans (Oeq_le (app_eq_compat (Oeq_refl eta) (fcont_comp_eq_compat (Oeq_refl eta) (xx _)))) _).
refine (Ole_trans (Oeq_le (kleisli_eq_compat _ (fcont_comp_eq_compat (Oeq_refl _) (xx _)))) _).
auto.
clear xx.
assert (xx:=@lub_comp_eq _ _ (fcont_Comp (ob F A C) _ _ (eta (ob F B D))) (fcontit (morph F A B C D) @ c)).
refine (Ole_trans (Oeq_le (kleisli_eq_compat (Oeq_refl _) (xx _))) _).
assert (continuous (fcontit (fcont_COMP (ob F A C) _ _ (eta (ob F B D))))). auto.
apply H.
clear xx.
assert (continuous (fcontit (kleisli_c (ob F B D) d))). auto.
assert(xx:=fun c => Oeq_le (lub_comp_eq c H)).
refine (Ole_trans (xx _) _).
refine (lub_le_compat _). refine (fmon_le_intro _).
intros n. simpl.
clear xx H.
refine (Ole_refl _).
Defined.
*)

Lemma BiLift_morph_simpl:
  forall F A B C D p,  BiLift_morph F A B C D p == kleisli (eta << morph F A B C D p).
intros. refine (fcont_eq_intro _). auto.
Qed.

Definition BiLift (F:BiFunctor) : BiFunctor.
intros F.
exists (ob := fun D E => DL (ob F D E)) (morph:=BiLift_morph F).
intros A B C D E G f g h k.
repeat (rewrite BiLift_morph_simpl).
rewrite <- morph_comp.
rewrite <- kleisli_comp2.
rewrite fcont_comp_assoc. auto.

intros A B. rewrite BiLift_morph_simpl.
rewrite morph_id. rewrite fcont_comp_unitR.
rewrite kleisli_unit. auto.
Defined.

Definition BiLift_strict F : FStrict (BiLift F).
intros F. unfold FStrict.
intros D E _ _. simpl. apply (lift_pointed (ob F D E)).
Defined.
