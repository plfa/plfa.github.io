(* utility.v

   Generally useful stuff that doesn't belong anywhere else for

   Abstracting Allocation : The New New Thing
   Nick Benton

   (c) 2006 Microsoft Research

   This also exports a bunch of pervasive stuff from the standard library
*)

Require Export Arith.
Require Export EqNat.
Require Export Bool.
Require Export BoolEq.
Require Export Setoid.
Require Export Omega.
Require Export Bool_nat.
Require Export List.
Require Export Max.
Require Export Min.

Lemma generalise_recursion : forall (P:nat->Prop), (forall k , P k) <-> (forall k k0, k0<=k -> P k0).
Proof.
  intuition; apply (H k k); trivial. 
Qed.

Ltac dcase x := generalize (refl_equal x); pattern x at -1; case x.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Tactic Notation "hreplace" constr(h) "with" constr(t) := let id:=fresh in (assert (id := t); clear h; rename id into h).

Tactic Notation "omega_replace" constr(m) "with" constr(n) := replace m with n ; try omega.


(*Tactic Notation "deconstruct" hyp(h) := _deconstruct h.*)
Tactic Notation "deconstruct" hyp(h) "as" simple_intropattern(ip) := generalize h; clear h; intros ip.

Tactic Notation "witness" ident(p) "in" hyp(h) := elim h; clear h; intros p h.

Axiom Extensionality : forall (A B : Type) (f g : A->B), (forall a:A, f a = g a) <-> f =g.

Lemma strictPosSucc: forall n, n>0 -> exists m , S m =n.
Proof.
  intros.
  induction n.
  destruct H.
  exists n; trivial.
  exists m; trivial.
  exists n; trivial.
Qed.  

Ltac unfold_plus:=
  try repeat rewrite <- plus_n_Sm;
  try rewrite plus_0_r;
  try rewrite plus_0_l.

Tactic Notation (at level 0) "unfold_plus" "in" constr(H) := try repeat rewrite <- plus_n_Sm in H;
  try rewrite plus_0_r in H;
  try rewrite plus_0_l in H.

Lemma beq_nat_neq :forall m n, m<>n ->  false = (beq_nat m n).
     double induction m n; simpl in |-*.
    intros.
    tauto.
    firstorder.
    firstorder.
    intros.
    set(Hn := (H0 n)).
    assert (n1 <> n).
    omega.
    apply (Hn H2).
Qed.

(* bleq_nat, ble_nat ... *)


Fixpoint bleq_nat (n m: nat) {struct n} : bool :=
  match n with 
    | 0 => true
    | S n1 => match m with
		| 0 => false
		| S m1 => bleq_nat n1 m1
	      end
  end.


Fixpoint ble_nat (n m : nat) {struct n} : bool :=
  match n with 
    | 0 => match m with
	     | 0 => false
	     | S _ => true
	    end
    | S n1 => match m with
		| 0 => false
		| S m1 => ble_nat n1 m1
	      end
  end.


Lemma ble_nat_false : forall m n, m >=n -> false = ble_nat m n.
  double induction m n.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
Qed.

Lemma bleq_nat_false : forall m n, m > n -> false = bleq_nat m n.
double induction m n.
 simpl.
 intro; absurd (0>0).
 omega.
 assumption.

 intros.
 simpl.
 absurd (0> S n0).
 omega.
 assumption.

 intros.
 simpl.
 tauto.

 intros.
 simpl.
 apply H0.
 omega.
Qed.

Lemma bleq_nat_true : forall m n, m <= n -> true = bleq_nat m n.
double induction m n; intros; simpl.
tauto.
tauto.
absurd (S n <=0).
 omega.
 assumption.
apply H0.
omega.
Qed.

Lemma true_bleq_nat : forall m n, true = bleq_nat m n -> m <= n.
double induction m n.
simpl.
omega.
simpl; intros.
omega.
simpl; intros.
discriminate H0.
simpl; intros.
intuition.
Qed.

Lemma false_bleq_nat : forall m n, false = bleq_nat m n -> m > n.
intros.
assert (~ m <= n).
intro Habs; generalize (bleq_nat_true m n Habs); intro.
rewrite <- H0 in H; discriminate H.
omega.
Qed.

Lemma ble_nat_true : forall m n, m < n -> true = ble_nat m n.
double induction m n.
intro; absurd (0<0).
omega.
assumption.

intros.
simpl.
tauto.

intros.
simpl.
absurd (S n < 0).
omega.
assumption.

intros.
simpl.
apply H0.
omega.
Qed.

Lemma booleq : forall (a b : bool), ((true = a) <-> (true = b)) -> (a = b).
intros; dcase a.
intuition.
intuition.
dcase b.
rewrite H0 in H2.
intro; symmetry; apply H2; symmetry; assumption.
tauto.
Qed.


Definition compose (A B C : Type) (g : B -> C) (f : A -> B) a := g(f a).

Implicit Arguments compose [A B C].

Definition opt_map : forall (A B : Type), (A -> B) -> (option A -> option B) := 
  fun A B f o =>
    match o with
      | None => None
      | Some a => Some (f a)
    end.

Implicit Arguments opt_map [A B].

Definition opt_lift : forall (A B : Type), (A -> option B) -> option A -> option B :=
  fun A B f o =>
    match o with
    | Some a => f a
    | None => None
    end.

Implicit Arguments opt_lift [A B].

Section Lists_extras.

  Variable A : Type.

  Set Implicit Arguments.

  (* cons_nth *)

  Fixpoint cons_nth (a:A) (l:list A) (m:nat) {struct l} : list A :=
    match l with
      | nil => a :: nil
      | b :: bs =>
	match m with
	  | 0 => a :: l
	  | S m' => b :: cons_nth a bs m'
	end
    end.

  Lemma cons_nth_S : forall a b l m, cons_nth a (b::l) (S m) = b :: (cons_nth a l m).
  Proof.
    firstorder.
  Qed.

  Lemma nth_error_nil : forall n, nth_error (nil : list A) n = error.
  Proof.
    destruct n; trivial.
  Qed.

  Lemma nth_error_cons : forall (l:list A) n a b, (nth_error l n = Some a) = (nth_error (b::l) (S n) = Some a).
    simpl; auto.
  Qed.

  Lemma nth_error_cons_nth_lt : forall (l:list A) n a b m (h:n<m), 
         (nth_error l n = Some a) -> (nth_error (cons_nth b l m) n = Some a).
  Proof.
    induction l.
    intros; rewrite (nth_error_nil n) in H; inversion H.
    intros until m;  case m.
    intro h;  absurd (n < 0); [apply  (lt_n_O n) | assumption].
    case n ;[ trivial | simpl; intros ; apply (IHl n0 a0 b n1) ; [omega |trivial]].
  Qed.

  Lemma nth_error_cons_nth_ltI : forall (l:list A) n a b m (h : n < m) (hn:n < length l),
          (nth_error (cons_nth b l m) n = Some a) -> (nth_error l n = Some a).
  Proof.
    induction l.
    intros. simpl in hn. destruct (lt_n_O n). auto.
    intros. destruct n. simpl in H. destruct m. destruct (lt_irrefl 0) ; auto.
    auto. simpl. simpl in H ; destruct m. destruct (lt_n_O (S n)). auto.
    assert (S n < S (length l)). auto.
    apply (IHl n a0 b m (lt_S_n _ _ h) (lt_S_n _ _ H0)). auto.
  Qed.

  Lemma nth_error_cons_nth_ge : forall (l:list A) n a b m (h:n>=m), 
         (nth_error l n = Some a) -> (nth_error (cons_nth b l m) (S n) = Some a).
  Proof.
    induction l.
    intro n; rewrite (nth_error_nil n); intros; inversion H.
    intros until m;case m.
    trivial.
    case n.
    intros n0 h; absurd (0 >= S n0) ; [omega | trivial].
    intros n0 n1 h; simpl; simpl in IHl.
    apply IHl; omega.
  Qed.

  Lemma nth_error_cons_nth_geI : forall (l:list A) n a b m (h:n>=m),
          (nth_error (cons_nth b l m) (S n) = Some a) -> (nth_error l n = Some a).
  Proof.
    induction l.
    intro n. auto.
    intros. destruct m. simpl in H. auto.
    simpl in H. destruct n. destruct (le_not_gt _ _ h).
    apply neq_O_lt. auto.
    apply (IHl n a0 b _ (le_S_n _ _ h) H).
  Qed.

  Lemma nth_error_cons_nth_eq : forall a l n,
        n <= length l -> nth_error (cons_nth a l n) n = value a.
  Proof.
    intros.
    generalize dependent l.
    induction n. intros. destruct l ; simpl ; reflexivity.
    intros.
    destruct l. simpl in H.
    destruct (absurd False H (le_Sn_O n)).
    simpl.
    assert (length (a0 :: l) = S (length l)). auto.
    rewrite -> H0 in H.
    apply (IHn _ (le_S_n _ _ H)).
  Qed.

  Lemma nth_error_length : forall l n (a:A), nth_error l n = value a -> n < length l.
  Proof.
    intros. generalize dependent l.
    induction n. destruct l. simpl.
    intros. inversion H.
    simpl. intros. apply gt_Sn_O.
    intro l. destruct l. simpl. intro. inversion H.
    simpl. intro. apply gt_n_S. apply (IHn _ H).
  Qed.

  Lemma nth_error_lengthI : forall (l:list A) n, n < length l -> exists a, nth_error l n = value a.
  Proof.
    intros l. induction l. simpl. intros n incon. inversion incon.
    intros n ; case n ; clear n. simpl. intros _. exists a. auto.
    intros n. simpl. intros C ; apply IHl. omega.
  Qed.

  Lemma cons_nth_length_S: forall a l n, length (cons_nth a l n) = S (length l).
  Proof.
    intros. generalize dependent l. induction n.
    intros. destruct l ; auto.
    intros. destruct l. auto.
    simpl. apply eq_S. apply IHn.
  Qed.

  Lemma nth_error_0 : forall (l:list A) (a:A), nth_error l 0 = Some a <-> (exists l', l = a::l').
  Proof.
    intros; split.
    induction l.
    simpl;  intro.
    inversion H.
    simpl;  intro.
    inversion H.
    exists l;trivial.
    intro; destruct H.
    rewrite H.
    simpl;trivial.
  Qed.
  
  Lemma nth_error_Sn : forall (l:list A) (a:A) (n:nat), 
    nth_error l (S n) = Some a <-> (exists l', exists a0,  l = a0::l' /\ nth_error l' n = Some a).
  Proof.
    intros; split.
    induction l.
    simpl;  intro.
    inversion H.
    simpl;  intro.
    exists l;exists a0;intuition.
    intro; destruct H as [l' [a0 (H0,H1)]].
    rewrite H0.
    simpl;trivial.
  Qed.


Lemma nth_error_map: forall B (f:A -> B) (l:list A) i,
  nth_error (map f l) i = (match nth_error l i with Some e => Some (f e) | error => error end).
Proof.
intros B f l.
induction l.
simpl. intros i. destruct i ; simpl ; auto.
intros i. destruct i. simpl. auto.
simpl. apply IHl.
Qed.


  Lemma split_list : forall (a:A) l , a :: l = (a :: nil) ++ l.
  Proof.
    trivial.
  Qed.

  Fixpoint takedrop n (l1 l2 : list A) {struct n} := match n with
    | 0 => (l1,l2)
    | S n => match l2 with 
       | nil => (l1,l2)
       | h::t => takedrop n (l1++(h::nil)) t
       end
    end. 

  Definition fuse (couple:list A * list A) := match couple with (l1,l2) => l1++l2 end.
  
  Lemma fuse_unfold : forall l1 l2, fuse (l1,l2) = l1++l2.
  Proof.
    unfold fuse; intuition.
  Qed.

  Opaque fuse.

  Unset Implicit Arguments.

End Lists_extras.
