Require Export utility.

Set Implicit Arguments.
Unset Strict Implicit.

Inductive Value : Set :=
| VAR : nat -> Value
| NUM : nat -> Value
| LAMBDA : Exp -> Value
with Exp : Set :=
| VAL : Value -> Exp
| APP : Value -> Value -> Exp
| LET : Exp -> Exp -> Exp
| IFZ : Value -> Exp -> Exp -> Exp
| OP : (nat -> nat -> nat) -> Value -> Value -> Exp.

Scheme Value_rec2 := Induction for Value Sort Set
  with Exp_rec2 := Induction for Exp Sort Set.

Scheme Value_type2 := Induction for Value Sort Type
  with Exp_type2 := Induction for Exp Sort Type.

Scheme Value_ind2 := Induction for Value Sort Prop
  with Exp_ind2 := Induction for Exp Sort Prop.

Combined Scheme ExpValue_ind from Value_ind2, Exp_ind2.

Inductive VTyping (n:nat) : Value -> Type :=
| TVAR : forall m, m < n -> VTyping n (VAR m)
| TNUM : forall m, VTyping n (NUM m)
| TLAMBDA : forall e, ETyping (S n) e -> VTyping n (LAMBDA e)
with ETyping (n:nat) : Exp -> Type :=
| TVAL : forall v, VTyping n v -> ETyping n (VAL v)
| TAPP : forall e1 e2, VTyping n e1 -> VTyping n e2 -> ETyping n (APP e1 e2)
| TLET : forall e1 e2, ETyping n e1 -> ETyping (S n) e2 -> ETyping n (LET e1 e2)
| TIFZ : forall v e1 e2, VTyping n v -> ETyping n e1 -> ETyping n e2 -> ETyping n (IFZ v e1 e2)
| TOP : forall op v1 v2, VTyping n v1 -> VTyping n v2 -> ETyping n (OP op v1 v2).

Hint Resolve TVAR TNUM TLAMBDA TVAL TAPP TLET TOP TIFZ.

Scheme VTyping_rec2 := Induction for VTyping Sort Set
  with ETyping_rec2 := Induction for ETyping Sort Set.

Scheme VTyping_rect2 := Induction for VTyping Sort Type
  with ETyping_rect2 := Induction for ETyping Sort Type.

Scheme VTyping_ind2 := Induction for VTyping Sort Prop
  with ETyping_ind2 := Induction for ETyping Sort Prop.

Combined Scheme Typing_ind from VTyping_ind2, ETyping_ind2.

Fixpoint shiftV (k n:nat) (e:Value) {struct e} : Value :=
match e with 
| VAR m => (if bleq_nat k m then VAR (m + n) else VAR m)
| NUM m => NUM m
| LAMBDA e => LAMBDA (shiftE (S k) n e)
end
with shiftE (k n:nat) (e:Exp) {struct e} : Exp :=
match e with 
| VAL v => VAL (shiftV k n v)
| APP e1 e2 => APP (shiftV k n e1) (shiftV k n e2)
| LET e1 e2 => LET (shiftE k n e1) (shiftE (S k) n e2)
| IFZ v e1 e2 => IFZ (shiftV k n v) (shiftE k n e1) (shiftE k n e2)
| OP op v1 v2 => OP op (shiftV k n v1) (shiftV k n v2)
end.

Lemma WeakeningV n v (tv:VTyping n v) x k : VTyping (n + x) (shiftV k x v).
intros n v tv x.
apply (@VTyping_rect2 (fun m v tv => forall k, VTyping (m + x) (shiftV k x v))
                      (fun m e te => forall k, ETyping (m + x) (shiftE k x e))) ;
try (intros ; simpl ; auto ; fail).

intros y m ym k. simpl.
case (bleq_nat k m).
eapply TVAR. omega.
eapply TVAR. omega.
Defined.

Lemma WeakeningE n e (te:ETyping n e) x k : ETyping (n + x) (shiftE k x e).
intros n e te x.
apply (@ETyping_rect (fun m e te => forall k, ETyping (m + x) (shiftE k x e))) ;
try (intros ; simpl ; auto ; fail).

intros m v tv k.
simpl. eapply TVAL. eapply WeakeningV. apply tv.

intros m v1 v2 tv1 tv2 k. simpl. eapply TAPP. eapply WeakeningV. apply tv1.
eapply WeakeningV. apply tv2.

intros m v e1 e2 tv te1 IH1 te2 IH2 k.
simpl. eapply TIFZ. eapply WeakeningV. apply tv. apply IH1. apply IH2.

intros m op v1 v2 tv1 tv2 k. simpl.
eapply TOP ; eapply WeakeningV ; auto.
Defined.

Fixpoint substVal (vl:list Value) (e:Value) : Value :=
match e with
| VAR m => (match nth_error vl m with | value ee => ee | error => VAR m end)
| NUM m => NUM m
| LAMBDA e => LAMBDA (substExp (VAR 0 :: (map (shiftV 0 1) vl)) e)
end
with substExp (vl:list Value) (e:Exp) : Exp :=
match e with
| VAL v => VAL (substVal vl v)
| APP e1 e2 => APP (substVal vl e1) (substVal vl e2)
| LET e1 e2 => LET (substExp vl e1) (substExp (VAR 0 :: map (shiftV 0 1) vl) e2)
| IFZ v e1 e2 => IFZ (substVal vl v) (substExp vl e1) (substExp vl e2)
| OP op v1 v2 => OP op (substVal vl v1) (substVal vl v2)
end.

Lemma subst_typingV:
   forall n v (tv:VTyping n v) n' vs, n = length vs ->
        (forall i v', nth_error vs i = Some v' -> VTyping n' v') ->
         VTyping n' (substVal vs v).
Proof.
apply (@VTyping_rect2
(fun n v dv => forall n' vs, n = length vs ->
        (forall i v', nth_error vs i = Some v' -> VTyping n' v') ->
         VTyping n' (substVal vs v))
(fun n e de => forall n' vs, n = length vs ->
        (forall i v', nth_error vs i = Some v' -> VTyping n' v') ->
         ETyping n' (substExp vs e))) ; intros n.

intros m mn n' vs nl C.
simpl. case_eq (nth_error vs m).
intros v nth.
specialize (C _ _ nth).
apply C.
intros nth.
assert False as F.  clear C n'.
generalize dependent m.
generalize dependent n.
induction vs. intros n nl m mn.
rewrite nl in mn. simpl in mn. intros. omega.
intros n nl m. simpl in nl. specialize (IHvs (length vs) (refl_equal _)).
case m. intros _ incon. simpl in incon. inversion incon.
clear m. intros m sm. simpl. rewrite nl in sm.
specialize (IHvs _ (lt_S_n _ _ sm)). auto.
inversion F.

simpl. intros. eapply TNUM.
simpl.
intros e te IH1 n' vs nl C.
eapply TLAMBDA. apply IH1.
simpl. rewrite map_length. auto.
intros i v'. case i ; clear i.
simpl. intros va. inversion va. eapply TVAR. omega.
intros i. simpl. rewrite nth_error_map.
case_eq (nth_error vs i). intros v nth va.
inversion va. clear H0 va.
simpl.
assert (S n' = n' + 1) as A by omega. rewrite A.
eapply (WeakeningV). eapply (C _ _ nth).
intros _ incon. inversion incon.

intros v tv IH n' vs nl C. simpl.
eapply (TVAL). apply IH ; auto.

intros v1 v2 tv1 IH1 tv2 IH2 n' vs nl C.
simpl. eapply (TAPP). eapply IH1 ; auto. eapply IH2 ; auto.

intros e1 e2 te1 IH1 te2 IH2 n' vs nl C.
simpl. eapply TLET. eapply IH1 ; auto.
eapply IH2 ; simpl ; auto. rewrite map_length. auto.
intros i v'. case i. simpl. intros va. inversion va.
eapply TVAR. omega.
clear i. intros i. simpl.
rewrite nth_error_map. case_eq (nth_error vs i).
intros v nth va. inversion va. clear H0 va.
assert (S n' = n' + 1) as A by omega. rewrite A.
eapply (WeakeningV).
apply (C _ _ nth).
intros _ incon. inversion incon.

intros v e1 e2 tv IHv te1 IH1 te2 IH2 n' vs nl C. simpl.
eapply TIFZ. apply IHv ; auto. apply IH1 ; auto. apply IH2 ; auto.

intros op v1 v2 tv1 IH1 tv2 IH2 n' vs nl C. simpl.
eapply TOP. apply IH1 ; auto. apply IH2 ; auto.
Defined.

Lemma subst_typingE:
   forall n e (te:ETyping n e) n' vs, n = length vs ->
        (forall i v', nth_error vs i = Some v' -> VTyping n' v') ->
         ETyping n' (substExp vs e).
Proof.
eapply (@ETyping_rect (fun n e _ => forall n' vs, n = length vs ->
        (forall i v', nth_error vs i = Some v' -> VTyping n' v') ->
         ETyping n' (substExp vs e))).

intros n v tv n' vs nl C. simpl. eapply TVAL.
apply (subst_typingV tv) ; auto.

intros n v1 v2 tv1 tv2 n' vs nl C.
simpl. eapply TAPP. apply (subst_typingV tv1) ; auto.
apply (subst_typingV tv2) ; auto.

intros n e1 e2 te1 IH1 te2 IH2 n' vs nl C.
simpl. eapply TLET ; auto.
apply IH2. simpl. rewrite map_length. auto.
intros i v'. case i. simpl. intros va. inversion va. eapply TVAR ; auto. omega.
clear i ; intros i. simpl. rewrite nth_error_map.
case_eq (nth_error vs i). intros v nth va. inversion va. clear H0 va.
assert (S n' = n' + 1) as A by omega. rewrite A.
eapply (WeakeningV). apply (C _ _ nth).
intros nth incon. inversion incon.

intros n v e1 e2 tv te1 IH1 te2 IH2 n' vs nl C. simpl.
eapply TIFZ.
eapply (subst_typingV (n:=n)) ; auto. apply IH1 ; auto. apply IH2 ; auto.

intros n op v1 v2 tv1 tv2 n' vs nl C. simpl.
eapply TOP ; eapply (subst_typingV (n:=n)) ; auto.
Defined.

Reserved Notation "e '=>>' v" (at level 75).

Inductive Evaluation : Exp -> Value -> Type :=
| e_Value : forall v, VAL v =>> v
| e_App : forall e1 v2 v, 
                 substExp [v2] e1 =>> v ->
                   (APP (LAMBDA e1) v2) =>> v
| e_Let : forall e1 v1 e2 v2, e1 =>> v1 -> substExp [v1] e2 =>> v2 ->
                   (LET e1 e2) =>> v2
| e_Ifz1 : forall e1 e2 v1, e1 =>> v1 -> IFZ (NUM 0) e1 e2 =>> v1
| e_Ifz2 : forall e1 e2 v2 n, e2 =>> v2 -> IFZ (NUM (S n)) e1 e2 =>> v2
| e_Op : forall op n1 n2, OP op (NUM n1) (NUM n2) =>> NUM (op n1 n2)
where "e =>> v" := (Evaluation e v).

Lemma eval_preserve_type: forall e v, e =>> v -> ETyping 0 e -> VTyping 0 v.
intros e v ev.
induction ev ; intros ty ; auto.
inversion ty. auto.

apply IHev. eapply (subst_typingE (n:=1)) ; auto.
inversion ty. inversion H1. auto.

intros i. case i ; clear i. simpl. intros v' va. inversion va.
rewrite <- H0.
inversion ty. auto.
intros i v'. simpl. intro incon. destruct i ; simpl in incon ; inversion incon.

apply IHev2. inversion ty.
clear e0 e3 H H0.
eapply (subst_typingE (n:=1)) ; simpl ; auto.
intros i. case i ; clear i. intros v. simpl. intros va. inversion va.
rewrite <- H0. apply IHev1. apply H1.
intros n v'. simpl. intros incon. destruct n ; simpl in * ; inversion incon.

inversion ty.
apply IHev ; auto.

inversion ty. apply IHev ; auto.
Qed.

