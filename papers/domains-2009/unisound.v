Require Import PredomAll.
Require Import unisem.

Set Implicit Arguments.
Unset Strict Implicit.

Fixpoint NSem n n' : (forall i, i < n -> SemEnv n' -C-> VInf) -> SemEnv n' -C-> SemEnv n :=
match n as n0 return (forall i, i < n0 -> SemEnv n' -C-> VInf) -> SemEnv n' -C-> SemEnv n0 with
| O => (fun _ => @K (SemEnv n') DOne tt)
| S n => (fun C => PROD_fun (NSem (fun i nth => C (S i) (lt_n_S _ _ nth))) (C 0 (lt_O_Sn _)))
end.

Lemma NSem_proof_irr: forall n n'
              (tvs1:forall i, i < n -> SemEnv n' -C-> VInf)
              (tvs2:forall i, i < n -> SemEnv n' -C-> VInf),
              (forall i (p:i < n), tvs1 i p == tvs2 i p) ->
            NSem tvs1 == NSem tvs2.
Proof.
intros n. induction n ; auto.
simpl.
intros n' tvs1 tvs2 C. refine (Dprod_unique _ _).
repeat (rewrite FST_PROD_fun).
apply (IHn n'). intros. apply (C (S i) (lt_n_S _ _ p)).
repeat (rewrite SND_PROD_fun).
refine (C 0 _).
Qed.

Fixpoint getTyping n n' vs : n = length vs -> (forall i v, nth_error vs i = value v -> VTyping n' v) -> 
                   forall i, i < n -> SemEnv n' -C-> VInf :=
match n as n0, vs as vs0 return n0 = length vs0 -> (forall i v, nth_error vs0 i = value v -> VTyping n' v) -> 
                   forall i, i < n0 -> SemEnv n' -C-> VInf with
| O,_ => (fun _ _ i incon => match (lt_n_O i incon) with end)
| S n, nil => (fun l _ i _ => match (O_S _ (sym_eq l)) with end)
| S n, v :: vs => (fun l C i => 
   match i with
   | O => (fun _ => SemVal (C 0 v (refl_equal _)))
   | S i => (fun li => getTyping (eq_add_S _ _ l) (fun i v nth => C (S i) v nth) (lt_S_n _ _ li))
   end)
end.

(*
Definition getTyping: forall n n' vs (l:n = length vs)
          (tvs:forall i v, nth_error vs i = value v -> VTyping n' v),
              (forall i, i < n -> SemEnv n' -C-> VInf).
intros n.
induction n.
intros n' vs l C i p. assert False as F by omega. inversion F.

intros n' vs. destruct vs.
intros incon. simpl in incon. assert False as F by omega. inversion F.
intros l C i. case i. clear i. intros _.
apply (SemVal (C 0 v (refl_equal _))).

clear i ; intros i si.
specialize (IHn n' vs (eq_add_S _ _ l)).
eapply (IHn (fun i v nth => C (S i) v nth) i (lt_S_n _ _ si)).
Defined.
*)

Lemma getTyping_irr: forall n n' vs (l1 l2:n = length vs)
     (tvs1: forall i v, nth_error vs i = value v -> VTyping n' v)
     (tvs2: forall i v, nth_error vs i = value v -> VTyping n' v)
     i (nth1 nth2 : i < n), @getTyping n n' vs l1 tvs1 i nth1 == getTyping l2 tvs2 nth2.
intros n. induction n. intros n' vs l1 l2 tvs1 tvs2 i incon. assert False as F by omega. inversion F.

intros n' vs. destruct vs.
intros l1. simpl in l1. assert False as F by omega. inversion F.
intros l1 l2 tvs1 tvs2 i nth1 nth2. destruct i. simpl. refine (Sem_eqV _ _).

simpl. refine (IHn _ _ _ _ _ _ _ _ _).
Qed.

Lemma NSem_ext: forall n n' f g, (forall a b, f a b == g a b) -> @NSem n n' f == NSem g.
intros n n' f g C.
induction n. simpl. auto.
simpl. refine (Dprod_unique _ _).
repeat (rewrite FST_PROD_fun).
apply IHn. apply (fun a ll => C (S a) (lt_n_S _ _ ll)).
repeat (rewrite SND_PROD_fun).
refine (C 0 _).
Qed.

Lemma projNSem: forall n' v (tv:VTyping n' v) n vs (l:n = length vs) m
       (nm : m < n)
       (nthv: nth_error vs m = value v)
       (tvs : forall (i : nat) (v : Value),
        nth_error vs i = value v -> VTyping n' v),
      @projenv m n nm << NSem (getTyping l tvs) == SemVal tv.
Proof.
intros n' v tv n.
induction n. intros vs ntht m. intros incon. assert False as F by omega. inversion F.
intros vs l m. destruct m. destruct vs. simpl in l. assert False as F by omega. inversion F.
simpl. intros _ vv. inversion vv.
generalize l. rewrite H0 in *. clear H0 v0 l. intros l tvs. rewrite SND_PROD_fun.
refine (Sem_eqV _ _).

destruct vs. simpl in l. assert False as F by omega. inversion F.
intros nm nth tvs. simpl. rewrite fcont_comp_assoc. rewrite FST_PROD_fun.
refine (Oeq_trans _ (IHn vs (eq_add_S _ _ l) m (lt_S_n m n nm) nth (fun i v nth => tvs (S i) v nth))).
refine (fcont_comp_eq_compat (Oeq_refl _) _).
refine (NSem_ext _). intros. refine (getTyping_irr _ _ _ _ _ _).
Qed.

Lemma NSemShift: forall n n' vs (l1:n = length vs) (l2:n = length (map (shiftV 0 1) vs))
              (tvs1:forall i v, nth_error vs i = value v -> VTyping n' v)
              (tvs2:forall i v, nth_error (map (shiftV 0 1) vs) i = value v -> VTyping (S n') v),
     NSem (getTyping l1 tvs1) << FST == NSem (getTyping l2 tvs2).
Proof.
intros n. induction n.
intros n' vs. destruct vs. intros l1 l2 tvs1 tvs2.
simpl. rewrite <- K_com. auto.
intros l. simpl in l. assert False as F by omega. inversion F.
intros n' vs. destruct vs. intros l. simpl in l. assert False as F by omega. inversion l.
intros l1 l2 tvs1 tvs2.
simpl. refine (Dprod_unique _ _).
rewrite <- fcont_comp_assoc. repeat (rewrite FST_PROD_fun).

refine (Oeq_trans _ (Oeq_trans (IHn n' vs (eq_add_S _ _ l1) (eq_add_S _ _ l2) (fun i => tvs1 (S i)) (fun i => tvs2 (S i))) _)).
refine (fcont_comp_eq_compat _ (Oeq_refl _)).
refine (NSem_ext _). intros. apply getTyping_irr.
refine (@NSem_ext n (S n') _ _ _). intros. refine (getTyping_irr _ _ _ _ _ _).

rewrite <- fcont_comp_assoc. rewrite SND_PROD_fun.
rewrite SND_PROD_fun.

refine (fcont_eq_intro _). intros E.
rewrite (fcont_comp_simpl).
apply (proj1 Sem_eq _ _ (tvs1 0 v (refl_equal (value v))) (S n') 1 0
                             (tvs2 0 (shiftV 0 1 v) (refl_equal (value (shiftV 0 1 v))))
                             (FST E) E).
intros i nli.
case_eq (bleq_nat 0 i).
assert (i+1 = S i) as A by omega. rewrite A. clear A.
intros _ nlik.
simpl. rewrite fcont_comp_simpl.
refine (fcont_eq_elim (projenv_irr _ _) _).

intros incon. inversion incon.
Qed.

Lemma Substitution:
   (forall n v (tv : VTyping n v) n' vs (l:n = length vs)
              (tvs:forall i v, nth_error vs i = value v -> VTyping n' v),
         SemVal tv << NSem (getTyping l tvs) == SemVal (subst_typingV tv l tvs)) /\
   (forall n e (te : ETyping n e) n' vs (l:n = length vs)
              (tvs:(forall i v, nth_error vs i = value v -> VTyping n' v)),
         SemExp te << NSem (getTyping l tvs) == SemExp (subst_typingE te l tvs)).
apply Typing_ind.

(* TVAR *)
intros n m ntht n' vs l tvs.
assert (exists v, nth_error vs m = value v).
clear tvs n'.
rewrite l in ntht. clear n l. generalize vs ntht. clear ntht vs. induction m.
intros vs l. destruct vs. simpl in l. assert False as F by omega. inversion F.
exists v. auto.
intros vs l. destruct vs. simpl in l. assert False as F by omega. inversion F.
apply IHm. simpl in l. omega.

destruct H as [v nthv]. simpl.
assert (tv := tvs m v nthv).
assert (ss:=Sem_eqV (subst_typingV (TVAR ntht) l tvs)).
assert (tv2 : VTyping n' (substVal vs (VAR m))).
simpl. rewrite nthv. simpl. apply tv.
rewrite (ss tv2). clear ss.
generalize tv2. clear tv2. simpl substVal. rewrite nthv. simpl.
intros tv2. refine (Oeq_trans _ (Sem_eqV tv tv2)). clear tv2.
apply (projNSem tv) ; auto.

(* TNUM *)
intros n m n' vs l tvs. simpl. rewrite fcont_comp_assoc. rewrite <- K_com. auto.

(* LAMBDA *)
intros n body tyb IH n' vs l tvs.

assert (tt:=subst_typingV (TLAMBDA tyb) l tvs).
refine (Oeq_trans _ (Sem_eqV tt _)).
generalize tt. clear tt. simpl substVal.
simpl.

specialize (IH (S n') (VAR 0 :: (map (shiftV 0 1) vs))).
simpl length in IH. assert (S n = length (VAR 0 :: map (shiftV 0 1) vs)).
simpl. rewrite map_length. auto.
specialize (IH H).
assert (forall i v, nth_error (VAR 0:: map (shiftV 0 1) vs) i = value v -> VTyping (S n') v).
intros i v. destruct i. simpl. intros ta. inversion ta.
eapply TVAR. omega.
simpl. specialize (tvs i). rewrite nth_error_map.
case_eq (nth_error vs i). intros vv. intros nthvv. specialize (tvs _ nthvv).
intros vvv. inversion vvv.
assert (xx:=WeakeningV tvs 1 0). assert (n'+1 = S n') as A by omega. rewrite A in xx.
apply xx.
intros ; discriminate.
specialize (IH H0).

intros tt.

dependent inversion tt. clear e H2.
simpl. repeat (rewrite fcont_comp_assoc).
refine (fcont_comp_eq_compat (Oeq_refl _) _).
refine (fcont_comp_eq_compat (Oeq_refl _) _).

apply curry_unique.

assert (PROD_map (curry (Roll << SemExp tyb) << NSem (getTyping l tvs)) ID ==
        PROD_map (curry (Roll << SemExp tyb)) ID << PROD_fun (NSem (getTyping l tvs) << FST) (SND (D2:=VInf))).
unfold PROD_map.
refine (Dprod_unique _ _).
rewrite FST_PROD_fun.
repeat (rewrite <- fcont_comp_assoc).
rewrite FST_PROD_fun.
repeat (rewrite fcont_comp_assoc). rewrite FST_PROD_fun. auto.
rewrite SND_PROD_fun. repeat (rewrite <- fcont_comp_assoc). rewrite SND_PROD_fun.
repeat (rewrite fcont_comp_assoc). rewrite SND_PROD_fun. auto.
rewrite H1. rewrite <- fcont_comp_assoc. rewrite <- curry_com.
clear H1. rewrite fcont_comp_assoc.
refine (fcont_comp_eq_compat (Oeq_refl _) _).

rewrite <- (Sem_eqE e0) in IH.
rewrite <- IH. clear IH tt e0.
refine (fcont_comp_eq_compat (Oeq_refl _) _).

clear tyb body. simpl.
refine (Dprod_unique _ _).
repeat (rewrite <- fcont_comp_assoc).
repeat (rewrite FST_PROD_fun).

assert (ss := NSemShift (n':= n') l (eq_add_S _ _ H) tvs).
assert (forall (i : nat) (v : Value),
                nth_error (map (shiftV 0 1) vs) i = value v ->
                VTyping (S n') v). intros i v.
rewrite nth_error_map. case_eq (nth_error vs i). intros vv nth va. inversion va.
assert (xx:=WeakeningV (tvs i _ nth) 1 0). assert (S n' = n'+1) as A by omega. rewrite A.
apply xx.
intros _ incon. inversion incon.

refine (Oeq_trans _ (Oeq_trans (Oeq_sym (ss H1)) _)). clear ss.
refine (@NSem_ext n (S n') _ _ _). intros. refine (getTyping_irr _ _ _ _ _ _).
auto.
rewrite SND_PROD_fun.
rewrite SND_PROD_fun.

assert (tv:= @TVAR (S n') 0 (lt_O_Sn _)).
rewrite <- (@Sem_eqV (S n') _ tv).
dependent inversion tv. simpl.
auto.

intros n v tv IH n' vs l tvs.
assert (tt:= subst_typingE (TVAL tv) l tvs).
rewrite <- (Sem_eqE tt).
dependent inversion tt.
simpl. rewrite fcont_comp_assoc.
refine (fcont_comp_eq_compat (Oeq_refl _) _).
rewrite IH. rewrite <- (Sem_eqV v1). auto.

(* TAPP *)
intros n e1 e2 te1 IH1 te2 IH2 E' vs l tvs.
assert (tt:= subst_typingE (TAPP te1 te2) l tvs).
rewrite <- (Sem_eqE tt).
dependent inversion tt.
simpl. rewrite fcont_comp_assoc. refine (fcont_comp_eq_compat (Oeq_refl _) _).
refine (Dprod_unique _ _).
rewrite <- fcont_comp_assoc.
repeat (rewrite FST_PROD_fun).
rewrite (IH1 _ _ l tvs). rewrite <- (Sem_eqV v) ; auto.
rewrite <- fcont_comp_assoc. repeat (rewrite SND_PROD_fun).
rewrite (IH2 _ _ l tvs). rewrite <- (Sem_eqV v0) ; auto.

(* TLET *)
intros n e1 e2 te2 IH2 te1 IH1 n' vs l tvs.
assert (tt:= subst_typingE (TLET te2 te1) l tvs).
rewrite <- (Sem_eqE tt).
dependent inversion tt.
assert (xx:= subst_typingE te2 l tvs).
simpl.
rewrite fcont_comp_assoc.
specialize (IH2 _ _ l tvs).
refine (fcont_comp_eq_compat (Oeq_refl _) _).
refine (Dprod_unique _ _).
rewrite <- fcont_comp_assoc. repeat (rewrite FST_PROD_fun).
refine (curry_unique _).
assert (PROD_map (curry (KLEISLIR (SemExp te1)) << NSem (getTyping l tvs)) ID ==
        PROD_map (curry (KLEISLIR (SemExp te1))) ID << PROD_map (NSem (getTyping l tvs)) (ID (D:=DL VInf))).
unfold PROD_map.
refine (Dprod_unique _ _).
repeat (rewrite FST_PROD_fun).
rewrite <- fcont_comp_assoc. rewrite FST_PROD_fun.
repeat (rewrite fcont_comp_assoc). rewrite FST_PROD_fun.
auto. rewrite <- fcont_comp_assoc. rewrite SND_PROD_fun.
repeat (rewrite <- fcont_comp_assoc). rewrite SND_PROD_fun.
rewrite fcont_comp_assoc. rewrite SND_PROD_fun.
rewrite fcont_comp_unitL. rewrite fcont_comp_unitL. auto.

rewrite H. clear H. rewrite <- fcont_comp_assoc.
rewrite <- curry_com.
unfold PROD_map.
rewrite KLEISLIR_comp.
assert (PROD_map (NSem (getTyping l tvs) << FST) ID == 
        PROD_map (NSem (getTyping l tvs)) ID << PROD_map (FST (D2:=DL VInf)) (ID( D:=VInf))).
rewrite PROD_map_PROD_map. rewrite fcont_comp_unitL. auto.
rewrite H. rewrite <- fcont_comp_assoc.
rewrite <- KLEISLIR_comp. rewrite fcont_comp_unitL.
rewrite (fun D E => Dprod_unique (f := <| @FST D E, SND |>) (g:=ID)).
rewrite fcont_comp_unitR.
clear H.

refine (KLEISLIR_eq_compat _).
specialize (IH1 (S n') (VAR 0::map (shiftV 0 1) vs)).
assert (S n = S (length (map (shiftV 0 1) vs))). rewrite map_length. auto.
specialize (IH1 H).
assert (forall i v,
     nth_error (VAR 0 :: map (shiftV 0 1) vs) i = value v -> VTyping (S n') v).
intros i s. destruct i. simpl. 
intros vv. inversion vv.
eapply TVAR. omega. simpl. 
intros nthv. rewrite nth_error_map in nthv. case_eq (nth_error vs i).
intros v nthvv. rewrite nthvv in nthv. inversion nthv.
assert (S n' = n' + 1) as A by omega. rewrite A.
eapply (WeakeningV). apply (tvs i v nthvv). intros nth. rewrite nth in nthv. inversion nthv.

specialize (IH1 H2).
rewrite <- (Sem_eqE e4) in IH1. rewrite <- IH1. clear IH1 H1.
simpl. unfold PROD_map.
refine (fcont_comp_eq_compat (Oeq_refl _) (PROD_fun_eq_compat _ _ )).
assert (sh := NSemShift l (eq_add_S _ _ H) tvs (fun i => H2 (S i))).
rewrite sh. clear sh. refine (@NSem_ext n (S n') _ _ _).
intros. refine (getTyping_irr _ _ _ _ _ _).
assert (VTyping (S n') (VAR 0)) as tv by (eapply TVAR ; omega).
rewrite <- (Sem_eqV tv).
dependent inversion tv. simpl. rewrite fcont_comp_unitL. auto.
rewrite fcont_comp_unitR. apply FST_PROD_fun. rewrite fcont_comp_unitR. apply SND_PROD_fun.
rewrite <- fcont_comp_assoc. rewrite SND_PROD_fun. rewrite SND_PROD_fun.
rewrite IH2. refine (Sem_eqE _ _).

(* TIFZ *)
intros n v e1 e2 tv IHv te1 IH1 te2 IH2 n' vs l tvs.
specialize (IHv _ _ l tvs). specialize (IH1 _ _ l tvs). specialize (IH2 _ _ l tvs).
assert (tt := subst_typingE (TIFZ tv te1 te2) (vs:=vs) l tvs). rewrite <- (Sem_eqE tt).
generalize tt. simpl. clear tt. intros tt.
dependent inversion tt. clear H0 H1 H2 v0 e0 e3. simpl.
rewrite fcont_comp_assoc.
rewrite PROD_fun_compl.
rewrite (PROD_fun_eq_compat (fcont_comp_assoc _ _ _) (Oeq_refl _)).
rewrite <- (Sem_eqV v1) in IHv. rewrite IHv. rewrite fcont_comp_unitL.
rewrite <- (PROD_fun_eq_compat (Oeq_refl _) (fcont_comp_unitR (NSem (getTyping l tvs)))).

Lemma xx D E F G (f:E -C-> F -C-> G) (h:D -C-> F) (g: E -C-> D) : 
          EV << PROD_fun f (h << g) == 
   EV << PROD_fun (curry (uncurry f << SWAP << PROD_map h ID << SWAP)) g.
intros ; apply fcont_eq_intro ; auto.
Qed.

rewrite xx. refine (fcont_comp_eq_compat (Oeq_refl _) _).
refine (PROD_fun_eq_compat _ (Oeq_refl _)). apply Oeq_sym.
refine (curry_unique _). rewrite fcont_comp_assoc. rewrite fcont_comp_assoc.
assert (forall D, SWAP << ((NSem (n:=n) (n':=n') (getTyping (vs:=vs) l tvs) *f* ID) << SWAP) ==
         @ID  D *f* (NSem (n:=n) (n':=n') (getTyping (vs:=vs) l tvs))) as eeq by
(intros D ; rewrite <- fcont_comp_assoc ; apply fcont_eq_intro ; auto).
rewrite eeq. clear eeq.
rewrite <- (Sem_eqE e4) in IH2.
rewrite <- (Sem_eqE e) in IH1.
apply fcont_eq_intro.
intros d. repeat (rewrite fcont_comp_simpl). case d ; clear d. intros ds dn.
repeat (rewrite PROD_map_simpl). rewrite ID_simpl. simpl. repeat (rewrite ID_simpl). simpl.
repeat (rewrite EV_simpl). rewrite uncurry_simpl. repeat (rewrite fcont_comp_simpl).
rewrite SUM_fun_simpl.
unfold VInf. rewrite SUM_fun_simpl. fold VInf. simpl.
case (SemVal v1 ds). intros t. case t ; auto. unfold INL. simpl.
auto using (fcont_eq_elim IH1 dn). clear t. intros t. auto using (fcont_eq_elim IH2 dn).
auto.

(* TOP *)
intros n op v1 v2 tv1 IH1 tv2 IH2 n' vs l tvs.
specialize (IH1 _ _ l tvs). specialize (IH2 _ _ l tvs).
simpl subst_typingE. simpl.
refine (Oeq_trans (fcont_comp_assoc _ _ _) _).
refine (fcont_comp_eq_compat (Oeq_refl _) _).
refine (Dprod_unique _ _). rewrite <- fcont_comp_assoc.
repeat (rewrite FST_PROD_fun).
rewrite <- IH1. clear IH1.
rewrite <- fcont_comp_assoc. auto.
rewrite <- fcont_comp_assoc. 
repeat (rewrite SND_PROD_fun). rewrite <- IH2. clear IH2.
rewrite <- fcont_comp_assoc. auto.
Qed.

Lemma Soundness: forall e v, (e =>> v) -> forall (et : ETyping 0 e) (vt : VTyping 0 v), SemExp et == eta << SemVal vt.
Proof.
intros e v  ev. induction ev ; intros te ; dependent inversion te.
clear H0 v0 te. intros tv. simpl. refine (fcont_comp_eq_compat (Oeq_refl _) _).
apply (Sem_eqV v1 tv).

clear e2 H0 H1 te. intros tv. simpl. assert (ETyping 1 e1) as te1 by (inversion v0 ; auto).
rewrite (PROD_fun_eq_compat (Sem_eqV v0 (TLAMBDA te1)) (Oeq_refl _)).
clear e0 v0. unfold Dapp.
simpl.
assert (forall D E F G H (a: D -c> F) (b : E -c> G) (c : H -c> D) (d : H -c> E), a *f* b << <|c, d|> == <| a << c, b << d |>).
intros. unfold PROD_map. refine (Dprod_unique _ _). rewrite <- fcont_comp_assoc. repeat (rewrite FST_PROD_fun).
rewrite fcont_comp_assoc. rewrite FST_PROD_fun. auto.
rewrite <- fcont_comp_assoc. repeat (rewrite SND_PROD_fun). rewrite fcont_comp_assoc. rewrite SND_PROD_fun. auto.
rewrite (fun D E => @fcont_comp_assoc D E (Dprod (DInf -C-> (DL VInf)) DInf) (DL VInf) (EV )).
rewrite H. clear H.
assert (SUM_fun (D1:=Discrete nat) (D2:=DInf -C-> DInf) (D3:=
        DInf -C-> DL VInf)
        (K (Discrete nat) (D2:=DInf -C-> DL VInf)
           (K DInf (D2:=DL VInf) (DL_bot VInf)))
        (fcont_COMP DInf DInf (DL VInf) Unroll) <<
      ((@INR (Discrete nat) (DInf -C-> DInf) << Dlift) <<
       curry (D1:=DOne) (D2:=VInf) (D3:=DInf) (Roll << SemExp te1)) == 
        (fcont_COMP DInf DInf (DL VInf) Unroll) << Dlift << curry (Roll << SemExp te1)).
repeat (rewrite <- fcont_comp_assoc). rewrite Dsum_rcom.  auto.
rewrite (PROD_fun_eq_compat H (Oeq_refl ((Roll << eta) << SemVal v1))). clear H.
unfold Dlift.
refine (fcont_eq_intro _).
intros tt. rewrite fcont_comp_simpl. rewrite PROD_fun_simpl. simpl. rewrite EV_simpl.
repeat (rewrite fcont_comp_simpl). rewrite fcont_COMP_simpl.
repeat (rewrite fcont_comp_simpl). rewrite curry_simpl.
repeat (rewrite fcont_comp_simpl). rewrite PROD_map_simpl. simpl. rewrite EV_simpl.
rewrite UR_eq.
rewrite fcont_comp_simpl. rewrite fcont_COMP_simpl. rewrite KLEISLI_simpl.
rewrite UR_eq.
rewrite eta_val. rewrite kleisli_simpl. rewrite kleisli_Val.
rewrite <- fcont_comp_simpl. rewrite <- fcont_comp_simpl.
assert (xx := subst_typingE te1).
assert (1 = length [v2]) as A by (simpl ; auto). specialize (xx 0 _ A).
assert ((forall (i : nat) (v' : Value),
        nth_error [v2] i = Some v' -> VTyping 0 v')) as C. intros i. destruct i. intros vv. simpl. intro incon. inversion incon.
rewrite <- H0. apply v1. simpl. intros vv. destruct i ; simpl ; intros incon ; inversion incon.
specialize (xx C).
specialize (IHev xx).
specialize (IHev tv).
rewrite <- (fcont_eq_elim IHev tt).
refine (app_eq_compat _ (Oeq_refl tt)).
assert (yy:=Oeq_trans (proj2 Substitution 1 _ te1 0 _ A C) (Sem_eqE _ xx)).
rewrite <- yy.
simpl. assert (zz:=Sem_eqV (C 0 v2 (refl_equal (value v2))) v1).
rewrite (PROD_fun_eq_compat (Oeq_refl (K DOne (D2:=DOne) Datatypes.tt)) zz).
clear zz yy xx IHev. refine (fcont_eq_intro _). intros t. repeat (rewrite fcont_comp_simpl).
rewrite curry_simpl. rewrite fcont_comp_simpl. rewrite UR_eq.
refine (app_eq_compat (Oeq_refl _) _). rewrite PROD_fun_simpl. simpl. rewrite K_simpl. case tt. auto.

(* TLET *)
intros tv2. simpl.
assert (<|curry (KLEISLIR (SemExp e4)), SemExp e |> == (curry (KLEISLIR (SemExp e4)) *f* ID) << <| ID, SemExp e|>).
unfold PROD_map.
refine (Dprod_unique _ _). rewrite <- fcont_comp_assoc. repeat (rewrite FST_PROD_fun). rewrite fcont_comp_assoc. rewrite FST_PROD_fun.
rewrite fcont_comp_unitR. auto.
rewrite <- fcont_comp_assoc. repeat (rewrite SND_PROD_fun). rewrite fcont_comp_assoc. rewrite SND_PROD_fun. rewrite fcont_comp_unitL.
auto.
rewrite H. clear H. rewrite <- fcont_comp_assoc. rewrite <- curry_com.
specialize (IHev1 e). assert (tv1 := eval_preserve_type ev1 e).
specialize (IHev1 tv1). rewrite (PROD_fun_eq_compat (Oeq_refl ID) IHev1).
rewrite KLEISLIR_unit.
clear H0 H1 e0 e3 te.
assert (1 = length [v1]) as l by (simpl ; auto).
assert ((forall (i : nat) (v' : Value),
        nth_error [v1] i = Some v' -> VTyping 0 v')) as C.
intros i ; destruct i. simpl. intros vv incon ; inversion incon. rewrite <- H0. clear H0 incon vv.
apply tv1. simpl. intros vv incon ; destruct i ; simpl in incon ; inversion incon.
assert (xx:=subst_typingE e4 l C).
specialize (IHev2 xx tv2). rewrite <- IHev2.
assert (yy:=proj2 Substitution 1 _ e4 0 _ l C).
rewrite <- (Sem_eqE xx) in yy. rewrite <- yy.
simpl. refine (fcont_comp_eq_compat (Oeq_refl _) _).
refine (Dprod_unique _ _).
repeat (rewrite FST_PROD_fun).
refine (DOne_final _ _).
repeat (rewrite SND_PROD_fun). refine (Sem_eqV tv1 _).

(* TIFZ zero *)
intros tv1. clear e0 e3 H0 H1 H2 te. rewrite <- (IHev e tv1). clear IHev.
simpl. rewrite (PROD_fun_eq_compat (fcont_comp_eq_compat (Oeq_refl _) (Sem_eqV v0 (TNUM 0 0))) (Oeq_refl _)).
clear v0.
simpl.
rewrite <- (PROD_fun_eq_compat (fcont_comp_assoc _ _ _) (Oeq_refl _)).
rewrite (PROD_fun_eq_compat (fcont_comp_eq_compat (Dsum_lcom _ _) (Oeq_refl _)) (Oeq_refl _)).
rewrite (PROD_fun_eq_compat (fcont_comp_assoc _ _ _) (Oeq_refl _)).
assert ((zeroCase << K DOne (D2:=Discrete nat) 0) == INL << ID) as zeq by
   (apply fcont_eq_intro ;intros x ; case x ; auto).
rewrite (PROD_fun_eq_compat (fcont_comp_eq_compat (Oeq_refl _) zeq) (Oeq_refl _)).
rewrite <- (PROD_fun_eq_compat (fcont_comp_assoc _ _ _) (Oeq_refl _)).
rewrite (PROD_fun_eq_compat (fcont_comp_eq_compat (Dsum_lcom _ _) (Oeq_refl _)) (Oeq_refl _)).
apply fcont_eq_intro ; auto.

(* TIFZ > 0 *)
intros tv2. clear e0 e3 H0 H1 H2 te. rewrite <- (IHev e4 tv2). clear IHev.
simpl.
rewrite (PROD_fun_eq_compat (fcont_comp_eq_compat (Oeq_refl _) (Sem_eqV v0 (TNUM 0 _))) (Oeq_refl _)).
clear v0.
simpl.
rewrite <- (PROD_fun_eq_compat (fcont_comp_assoc _ _ _) (Oeq_refl _)).
rewrite (PROD_fun_eq_compat (fcont_comp_eq_compat (Dsum_lcom _ _) (Oeq_refl _)) (Oeq_refl _)).
rewrite (PROD_fun_eq_compat (fcont_comp_assoc _ _ _) (Oeq_refl _)).
assert ((zeroCase << K DOne (D2:=Discrete nat) (S n)) == INR << (K DOne (n:Discrete nat))) as zeq by
  (apply fcont_eq_intro ; auto).
rewrite (PROD_fun_eq_compat (fcont_comp_eq_compat (Oeq_refl _) zeq) (Oeq_refl _)).
rewrite <- (PROD_fun_eq_compat (fcont_comp_assoc _ _ _) (Oeq_refl _)).
rewrite (PROD_fun_eq_compat (fcont_comp_eq_compat (Dsum_rcom _ _) (Oeq_refl _)) (Oeq_refl _)).
apply fcont_eq_intro ; auto.

intros tv. clear op0 H0 H1 H2.
dependent inversion tv. clear m H0. simpl.
rewrite (PROD_fun_eq_compat (fcont_comp_eq_compat (Oeq_refl _) (Sem_eqV v (TNUM 0 n1)))
                            (fcont_comp_eq_compat (Oeq_refl _) (Sem_eqV v0 (TNUM 0 n2)))).
simpl. clear v v1 v2 te.
rewrite <- (PROD_fun_eq_compat (fcont_comp_assoc _ _ _) (fcont_comp_assoc _ _ _)).
rewrite (PROD_fun_eq_compat (fcont_comp_eq_compat (Dsum_lcom _ _) (Oeq_refl _)) (fcont_comp_eq_compat (Dsum_lcom _ _) (Oeq_refl _))).
refine (fcont_eq_intro _). intros tt.
repeat (rewrite fcont_comp_simpl).
rewrite PROD_fun_simpl. simpl. repeat (rewrite fcont_comp_simpl).
rewrite eta_val. rewrite eta_val. rewrite uncurry_simpl.
repeat (rewrite K_simpl). rewrite Operator2_simpl. auto.
Qed.

