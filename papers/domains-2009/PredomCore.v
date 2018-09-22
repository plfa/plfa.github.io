(** * Predom.v: Specification and properties of a cpo *)

(* Modified from Christine's original *)

Require Export Setoid.
Require Export Arith.
Require Export Omega.
Set Implicit Arguments.
Unset Strict Implicit.
Open Scope nat_scope.

(** printing -c> %\cont% *)
(** printing -m> %\mon% *)

(** %\include{macros}% *)

(** printing O1 %\ensuremath{O_1}% *)
(** printing O2 %\ensuremath{O_2}% *)
(** printing O3 %\ensuremath{O_3}% *)
(** printing O4 %\ensuremath{O_4}% *)
(** printing D1 %\ensuremath{D_1}% *)
(** printing D2 %\ensuremath{D_2}% *)
(** printing D3 %\ensuremath{D_3}% *)
(** printing x1 %\ensuremath{x_1}% *)
(** printing x2 %\ensuremath{x_2}% *)
(** printing x3 %\ensuremath{x_3}% *)
(** printing y1 %\ensuremath{y_1}% *)
(** printing y2 %\ensuremath{y_2}% *)
(** printing y3 %\ensuremath{y_3}% *)
(** printing p1 %\ensuremath{p_1}% *)
(** printing p2 %\ensuremath{p_2}% *)
(** printing p3 %\ensuremath{p_3}% *)

(** printing natO %\natO% *)
(** printing nat %\nat% *)
(** printing lub %\lub% *)
(** printing cpo %\cpo% *)
(** printing ord %\ord% *)




(** ** Ordered type *)
Record ord : Type := mk_ord
  {tord :> Type; 
   Ole : tord -> tord -> Prop; 
   Ole_refl : forall x : tord, Ole x x; 
   Ole_trans : forall x y z : tord, Ole x y -> Ole y z -> Ole x z}.

Hint Resolve Ole_refl Ole_trans.

Hint Extern 2  (Ole (o:=?X1) ?X2 ?X3 ) => simpl Ole.

Bind Scope O_scope with tord.
Delimit Scope O_scope with tord.

(** printing <= %\ensuremath{\sqsubseteq}% *)
Infix "<=" := Ole : O_scope.
Open Scope O_scope.

(** *** Associated equality *)
(** printing == %\eqeq% *)
Definition Oeq (O : ord) (x y : O) := x <= y /\ y <= x.
Infix "==" := Oeq (at level 70) : O_scope.

Lemma Ole_refl_eq : forall  (O:ord) (x y:O), x = y -> x <= y.
intros O x y H; rewrite H; auto.
Save.

Hint Resolve Ole_refl_eq.

Lemma Ole_antisym : forall (O:ord) (x y:O), x <= y -> y <= x -> x == y.
red; auto.
Save.
Hint Immediate Ole_antisym.

Lemma Oeq_refl : forall (O:ord) (x:O), x == x.
red; auto.
Save.
Hint Resolve Oeq_refl.

Lemma Oeq_refl_eq : forall (O:ord) (x y:O), x=y -> x == y.
intros O x y H; rewrite H; auto.
Save.
Hint Resolve Oeq_refl_eq.

Lemma Oeq_sym : forall (O:ord) (x y:O), x == y -> y == x.
unfold Oeq; intuition.
Save.

Lemma Oeq_le : forall (O:ord) (x y:O), x == y -> x <= y.
unfold Oeq; intuition.
Save.

Lemma Oeq_le_sym : forall (O:ord) (x y:O), x == y -> y <= x.
unfold Oeq; intuition.
Save.

Hint Resolve Oeq_le.
Hint Immediate Oeq_sym Oeq_le_sym.

Lemma Oeq_trans : forall (O:ord) (x y z:O), x == y -> y == z -> x == z.
unfold Oeq; split; apply Ole_trans with y; auto.
Save.
Hint Resolve Oeq_trans.

(** *** Setoid relations *)

Add Parametric Relation (O:ord) : O (@Oeq O)
       reflexivity proved by (@Oeq_refl O) symmetry proved by (@Oeq_sym O)
       transitivity proved by (@Oeq_trans O) as Oeq_Relation.

Add Parametric Relation (O:ord) : O (@Ole O)
       reflexivity proved by (@Ole_refl O) 
       transitivity proved by (@Ole_trans O) as Ole_Relation.

Add Parametric Morphism (O:ord) : (@Ole O) with signature (@Oeq O) ==> (@Oeq O) ==> iff as Ole_eq_compat_iff.
split; intuition.
apply Ole_trans with x; firstorder using Ole_trans.
apply Ole_trans with y.
firstorder.
apply Ole_trans with y0.
assumption.
intuition.
Save.

Lemma Ole_eq_compat : 
     forall (O : ord) (x1 x2 : O),
       x1 == x2 -> forall x3 x4 : O, x3 == x4 -> x1 <= x3 -> x2 <= x4.
intros; apply Ole_trans with x1; firstorder using Ole_trans.
Save.

Lemma Ole_eq_right : forall (O : ord) (x y z: O),
             x <= y -> y == z -> x <= z.
intros; apply Ole_eq_compat with x y; auto.
Save.

Lemma Ole_eq_left : forall (O : ord) (x y z: O),
             x == y -> y <= z -> x <= z.
intros; apply Ole_eq_compat with y z; auto.
Save.

(** *** Dual order *)

Definition Iord (O:ord):ord.
intros O; exists O (fun x y : O => y <= x); intros; auto.
apply Ole_trans with y; auto.
Defined.

(** *** Order on functions *)

Definition ford (A:Type) (O:ord) : ord.
intros A O; exists (A -> O) (fun f g:A->O => forall x, f x <= g x); intros; auto.
apply Ole_trans with (y x0); auto.
Defined.

Infix "-o>" := ford (right associativity, at level 30) : O_scope .

Lemma ford_le_elim : forall A (O:ord) (f g:A -o> O), f <= g ->forall n, f n <= g n.
auto.
Save.
Hint Immediate ford_le_elim.

Lemma ford_le_intro : forall A (O:ord) (f g:A-o>O), (forall n, f n <= g n) -> f <= g.
auto.
Save.
Hint Resolve ford_le_intro.

Lemma ford_eq_elim : forall A (O:ord) (f g:A -o> O), f == g ->forall n, f n == g n.
firstorder.
Save.
Hint Immediate ford_eq_elim.

Lemma ford_eq_intro : forall A (O:ord) (f g:A -o> O), (forall n, f n == g n) -> f == g.
red; auto.
Save.
Hint Resolve ford_eq_intro.

Hint Extern 2 (Ole (o:=ford ?X1 ?X2) ?X3 ?X4) => intro.

(** ** Monotonicity *)

(** *** Definition and properties *)

Definition monotonic (O1 O2 : ord) (f : O1 -> O2) := 
   forall x y, x <= y -> f x <= f y.
Hint Unfold monotonic.

Definition stable (O1 O2:ord) (f : O1 -> O2) := forall x y, x == y -> f x == f y.
Hint Unfold stable.

Lemma monotonic_stable : forall (O1 O2 : ord) (f:O1 -> O2), 
             monotonic f -> stable f.
unfold monotonic, stable; firstorder.
Save.
Hint Resolve monotonic_stable.

(** *** Type of monotonic functions *)

Record fmono (O1 O2 : ord) : Type := mk_fmono
            {fmonot :> O1 -> O2; 
             fmonotonic: monotonic fmonot}.
Hint Resolve fmonotonic.

Definition fmon (O1 O2:ord) : ord.
intros O1 O2; exists (fmono O1 O2) (fun f g:fmono O1 O2 => forall x, f x <= g x); intros; auto.
apply Ole_trans with (y x0); auto.
Defined.

(** printing -m> %\mon% *)
Infix "-m>" := fmon (at level 30, right associativity) : O_scope.

Lemma fmon_stable : forall (O1 O2 : ord) (f:O1 -m> O2), stable f.
intros; apply monotonic_stable; auto.
Save.
Hint Resolve fmon_stable.

Lemma fmon_le_elim : forall (O1 O2:ord) (f g:O1 -m> O2), f <= g ->forall n, f n <= g n.
auto.
Save.
Hint Immediate fmon_le_elim.

Lemma fmon_le_intro : forall (O1 O2:ord) (f g:O1 -m> O2), (forall n, f n <= g n) -> f <= g.
auto.
Save.
Hint Resolve fmon_le_intro.

Lemma fmon_eq_elim : forall (O1 O2:ord) (f g:O1 -m> O2), f == g ->forall n, f n == g n.
firstorder.
Save.
Hint Immediate fmon_eq_elim.

Lemma fmon_eq_intro : forall (O1 O2:ord) (f g:O1 -m> O2), (forall n, f n == g n) -> f == g.
red; auto.
Save.
Hint Resolve fmon_eq_intro.

Hint Extern 2 (Ole (o:=fmon ?X1 ?X2) ?X3 ?X4) => intro.

(** *** Monotonicity and dual order *)

Definition Imon : forall O1 O2, (O1-m>O2) -> Iord O1 -m> Iord O2.
intros O1 O2 f; exists (f:Iord O1 -> Iord O2); red; simpl; intros.
apply (fmonotonic f); auto.
Defined.

Definition Imon2 : forall O1 O2 O3, (O1-m>O2-m>O3) -> Iord O1 -m> Iord O2 -m> Iord O3.
intros O1 O2 O3 f; exists (fun (x:Iord O1) => Imon (f x)); red; simpl; intros.
apply (fmonotonic f); auto.
Defined.

(** *** Monotonic functions with 2 arguments *)
Definition le_compat2_mon : forall (O1 O2 O3:ord)(f:O1 -> O2 -> O3),
     (forall (x y:O1) (z t:O2), x<=y -> z <= t -> f x z <= f y t) -> (O1-m>O2-m>O3).
intros O1 O2 O3 f Hle; exists (fun (x:O1) => mk_fmono (fun z t => Hle x x z t (Ole_refl x))).
red; intros; intro a; simpl; auto. 
Defined.

(** ** Sequences *)
(** *** Order on natural numbers *)
Definition natO : ord.
    exists nat (fun n m : nat => (n <= m)%nat); intros; auto with arith.
    apply le_trans with y; auto.
Defined.

Definition fnatO_intro : forall (O:ord) (f:nat -> O), (forall n, f n <= f (S n)) -> natO-m>O.
intros; exists f; red; simpl; intros.
elim H0; intros; auto.
apply Ole_trans with (f m); trivial.
Defined.

Lemma fnatO_elim : forall (O:ord) (f:natO -m> O) (n:nat), f n <= f (S n).
intros; apply (fmonotonic f); auto.
Save.
Hint Resolve fnatO_elim.


(** - (mseq_lift_left f n) k = f (n+k) *)
Definition mseq_lift_left : forall (O:ord) (f:natO -m> O) (n:nat), natO -m> O.
intros; exists (fun k => f (n+k)%nat); red; intros.
apply (fmonotonic f); auto with arith.
Defined.

Lemma mseq_lift_left_le_compat : forall (O:ord) (f g:natO -m> O) (n:nat), 
             f <= g -> mseq_lift_left f n <= mseq_lift_left g n.
intros; intro; simpl; auto.
Save.
Hint Resolve mseq_lift_left_le_compat.

Add Parametric Morphism (O:ord) : (@mseq_lift_left O)
 with signature (@Oeq (natO -m> O))  ==> (@eq nat) ==> (@Oeq (natO -m> O))
as mseq_lift_left_eq_compat.
intros; apply Ole_antisym; auto.
Save.
Hint Resolve mseq_lift_left_eq_compat.

(** - (mseq_lift_left f n) k = f (k+n) *)
Definition mseq_lift_right : forall (O:ord) (f:natO -m> O) (n:nat), natO -m> O.
intros; exists (fun k => f (k+n)%nat); red; intros.
apply (fmonotonic f); auto with arith.
Defined.

Lemma mseq_lift_right_le_compat : forall (O:ord) (f g:natO -m> O) (n:nat), 
             f <= g -> mseq_lift_right f n <= mseq_lift_right g n.
intros; intro; simpl; auto.
Save.
Hint Resolve mseq_lift_right_le_compat.

Add Parametric Morphism (O:ord) : (@mseq_lift_right O) 
with signature (@Oeq (natO -m> O)) ==> (@eq nat) ==> (@Oeq (natO -m> O))
as mseq_lift_right_eq_compat.
intros; apply Ole_antisym; auto.
Save.

Lemma mseq_lift_right_left : forall (O:ord) (f:natO -m> O) n, 
       mseq_lift_left f n  == mseq_lift_right f n.
intros; apply fmon_eq_intro; unfold mseq_lift_left,mseq_lift_right; simpl; intros.
replace (n0+n)%nat with (n+n0)%nat; auto with arith.
Save.

(** *** Monotonicity and functions *)
(** -  (ford_app f x) n = f n x *) 
Definition ford_app : forall (A:Type)(O1 O2:ord)(f:O1 -m> (A -o> O2))(x:A), O1 -m> O2.
intros; exists (fun n => f n x); intros.
intro n; intros.
assert (f n <= f y); auto.
apply (fmonotonic f); trivial.
Defined.

Infix "<o>" := ford_app (at level 30, no associativity) : O_scope.

Lemma ford_app_simpl : forall (A:Type)(O1 O2:ord)  (f : O1 -m> A -o> O2) (x:A)(y:O1),
            (f <o> x) y = f y x.
trivial.
Save.

Lemma ford_app_le_compat : forall (A:Type)(O1 O2:ord) (f g:O1 -m> A -o> O2) (x:A), 
             f <= g -> f <o> x  <= g <o> x.
intros; intro; simpl; auto.
Save.
Hint Resolve ford_app_le_compat.

Add Parametric Morphism (A:Type) (O1 O2 : ord) : (@ford_app A O1 O2)
with signature (@Oeq (O1 -m> (A -o> O2))) ==> (@eq A) ==> (@Oeq (O1 -m> O2))
as ford_app_eq_compat.
intros; apply Ole_antisym; auto.
Save.

(** - ford_shift f x y == f y x *)
Definition ford_shift : forall (A:Type)(O1 O2:ord)(f:A -o> (O1 -m> O2)), O1 -m> (A-o>O2).
intros; exists (fun x y => f y x); intros.
intros n x H y.
apply (fmonotonic (f y)); trivial.
Defined.

Lemma ford_shift_le_compat : forall (A:Type)(O1 O2:ord) (f g: A -o> (O1 -m> O2)), 
             f <= g -> ford_shift f  <= ford_shift g.
intros; intro; simpl; auto.
Save.
Hint Resolve ford_shift_le_compat.

Add Parametric Morphism (A:Type) (O1 O2 : ord) : (@ford_shift A O1 O2)
with signature (@Oeq (A -o> (O1 -m> O2))) ==> (@Oeq (O1 -m> (A -o> O2)))
as ford_shift_eq_compat.
intros; apply Ole_antisym; auto.
Save.

(**  - (fmon_app f x) n = f n x *) 

Definition fmon_app : forall (O1 O2 O3:ord)(f:O1 -m> O2 -m> O3)(x:O2), O1 -m> O3.
intros; exists (fun n => f n x); intros.
intro n; intros.
assert (f n <= f y); auto.
apply (fmonotonic f); trivial.
Defined.

Infix "<_>" := fmon_app (at level 35, no associativity) : O_scope.

Lemma fmon_app_simpl : forall  (O1 O2 O3:ord)(f:O1 -m> O2 -m> O3)(x:O2)(y:O1),
      (f <_> x)  y = f y x.
trivial.
Save.

(*
Lemma fmon_app_le_compat : forall (O1 O2 O3:ord) (f g:O1 -m> (O2 -m> O3)) (x y:O2), 
             f <= g -> x <= y -> f <_> x  <= g <_> y.
red; intros; simpl; intros; auto.
apply Ole_trans with (f x0 y); auto.
apply (fmonotonic (f x0)); auto.
Save.*)

Add Parametric Morphism (O1 O2 O3 : ord) : (@fmon_app O1 O2 O3)
with signature (@Ole (O1 -m> O2 -m> O3)) ++> (@Ole O2) ++> (@Ole (O1 -m> O3))
as fmon_app_le_compat.
intros f g; intros ; simpl; intros; auto.
apply Ole_trans with (f x y0); auto.
apply (fmonotonic (f x)); auto.
Save.

Hint Resolve fmon_app_le_compat.

Add Parametric Morphism (O1 O2 O3 : ord) : (@fmon_app O1 O2 O3)
with signature (@Oeq (O1 -m> O2 -m> O3)) ==> (@Oeq O2) ==> (@Oeq (O1 -m> O3))
as fmon_app_eq_compat.
intros; apply Ole_antisym; intros; auto.
Save.

(** - fmon_id c = c *)
Definition fmon_id :  forall (O:ord), O -m> O.
intros; exists (fun (x:O)=>x).
intro n; auto.
Defined.

Lemma fmon_id_simpl : forall (O:ord) (x:O), fmon_id O x = x.
trivial.
Save.

(**  - (fmon_cte c) n = c *) 
Definition fmon_cte :  forall (O1 O2:ord)(c:O2), O1 -m> O2.
intros; exists (fun (x:O1)=>c).
intro n; auto.
Defined.

Lemma fmon_cte_simpl : forall  (O1 O2:ord)(c:O2)(c:O2) (x:O1), fmon_cte O1 c x = c.
trivial.
Save.


Definition mseq_cte : forall O:ord, O -> natO-m>O := fmon_cte natO.

Lemma fmon_cte_le_compat : forall (O1 O2:ord) (c1 c2:O2), 
             c1 <= c2 -> fmon_cte O1 c1 <= fmon_cte O1 c2.
intros; intro; auto.
Save.

Add Parametric Morphism (O1 O2 : ord) : (@fmon_cte O1 O2) 
with signature (@Oeq O2) ==>  (@Oeq (O1 -m> O2))
as fmon_cte_eq_compat.
intros; apply Ole_antisym; auto.
Save.

(** - (fmon_diag h) n = h n n *) 
Definition fmon_diag : forall (O1 O2:ord)(h:O1 -m> (O1 -m> O2)), O1 -m> O2.
intros; exists (fun n => h n n).
red; intros.
apply Ole_trans with (h x y); auto.
apply (fmonotonic (h x)); auto.
assert (h x <= h y); auto.
apply (fmonotonic h); trivial.
Defined.

Lemma fmon_diag_le_compat :  forall (O1 O2:ord) (f g:O1 -m> (O1 -m> O2)), 
             f <= g -> fmon_diag f <= fmon_diag g.
intros; intro; simpl; auto.
Save.
Hint Resolve fmon_diag_le_compat.

Lemma fmon_diag_simpl : forall (O1 O2:ord) (f:O1 -m> (O1 -m> O2)) (x:O1), 
             fmon_diag f x = f x x.
trivial.
Save.

Add Parametric Morphism (O1 O2 : ord) : (@fmon_diag O1 O2)
with signature (@Oeq (O1 -m> (O1 -m> O2))) ==> (@Oeq (O1 -m> O2))
as fmon_diag_eq_compat.
intros; apply Ole_antisym; auto.
Save.

(** - (fmon_shift h) n m = h m n *) 
Definition fmon_shift : forall (O1 O2 O3:ord)(h:O1 -m> O2 -m>  O3), O2 -m> O1 -m>  O3.
intros; exists (fun m => h <_> m).
intro n; simpl; intros.
apply (fmonotonic (h x)); trivial.
Defined.

Lemma fmon_shift_simpl : forall (O1 O2 O3:ord)(h:O1 -m> O2 -m>  O3) (x : O2) (y:O1),
      fmon_shift h x y = h y x.
trivial.
Save.

Lemma fmon_shift_le_compat :  forall (O1 O2 O3:ord) (f g:O1 -m>  O2 -m>  O3), 
             f <= g -> fmon_shift f <= fmon_shift g.
intros; intro; simpl; intros.
assert (f x0 <= g x0); auto.
Save.
Hint Resolve fmon_shift_le_compat.

Add Parametric Morphism (O1 O2 O3 : ord) : (@fmon_shift O1 O2 O3)
with signature (@Oeq (O1 -m> O2 -m> O3)) ==> (@Oeq (O2 -m> O1 -m> O3))
as fmon_shift_eq_compat.
intros; apply Ole_antisym; auto.
Save.

Lemma fmon_shift_shift_eq :  forall (O1 O2 O3:ord) (h : O1 -m> O2 -m>  O3),
             fmon_shift (fmon_shift h) == h.
intros; apply fmon_eq_intro; unfold fmon_shift; simpl; auto.
Save.

(** - (f@g) x = f (g x) *)
Definition fmon_comp : forall O1 O2 O3:ord, (O2 -m> O3) -> (O1 -m> O2) -> O1 -m> O3.
intros O1 O2 O3 f g; exists (fun n => f (g n)); red; intros.
apply (fmonotonic f).
apply (fmonotonic g); auto.
Defined.

(* this doesnt work printing @ %\moncomp% *)
(** printing <m< %\moncomp% *)
Infix "@" := fmon_comp (at level 35) : O_scope.
Infix "<m<" := fmon_comp (at level 35) : O_scope.


Lemma fmon_comp_simpl : forall (O1 O2 O3:ord) (f :O2 -m> O3) (g:O1 -m> O2) (x:O1),
            (f @ g) x = f (g x).
trivial.
Save.

(** - (f@2 g) h x = f (g x) (h x) *)
Definition fmon_comp2 : 
    forall O1 O2 O3 O4:ord, (O2 -m> O3 -m> O4) -> (O1 -m> O2) -> (O1 -m> O3) -> O1-m>O4.
intros O1 O2 O3 O4 f g h; exists (fun n => f (g n) (h n)); red; intros.
apply Ole_trans with (f (g x) (h y)); auto.
apply (fmonotonic (f (g x))).
apply (fmonotonic h); auto.
apply (fmonotonic f); auto. 
apply (fmonotonic g); auto. 
Defined.

Infix "@2" := fmon_comp2 (at level 70) : O_scope.

Lemma fmon_comp2_simpl : 
    forall (O1 O2 O3 O4:ord) (f:O2 -m> O3 -m> O4) (g:O1 -m> O2) (h:O1 -m> O3) (x:O1),
            (f @2 g) h x = f (g x) (h x).
trivial.
Save.

Add Parametric Morphism (O1 O2 O3 : ord) : (@fmon_comp O1 O2 O3)
with signature (@Ole (O2 -m> O3)) ++> (@Ole (O1 -m> O2)) ++> (@Ole (O1 -m> O3)) 
as fmon_comp_le_compat_morph.
intros f1 f2 H g1 g2 H1; red; intros.
simpl.
intros.
apply Ole_trans with (f2 (g1 x)); auto.
apply (fmonotonic f2); auto.
Save.

Lemma fmon_comp_le_compat : 
      forall (O1 O2 O3:ord) (f1 f2: O2 -m> O3) (g1 g2:O1 -m> O2),
                 f1 <= f2 -> g1<= g2 -> f1 @ g1 <= f2 @ g2.
intros; exact (fmon_comp_le_compat_morph H H0).
Save.
Hint Immediate fmon_comp_le_compat.

Add Parametric Morphism (O1 O2 O3 : ord) : (@fmon_comp O1 O2 O3) 
with signature (@Oeq (O2 -m> O3)) ==> (@Oeq (O1 -m> O2)) ==> (@Oeq (O1 -m> O3)) 
as fmon_comp_eq_compat.
intros; apply Ole_antisym; apply fmon_comp_le_compat; auto.
Save.
Hint Immediate fmon_comp_eq_compat.


Lemma fmon_comp_monotonic2 : 
      forall (O1 O2 O3:ord) (f: O2 -m> O3) (g1 g2:O1 -m> O2),
               g1<= g2 -> f @ g1 <= f @ g2.
auto.
Save.
Hint Resolve fmon_comp_monotonic2.

Lemma fmon_comp_monotonic1 : 
      forall (O1 O2 O3:ord) (f1 f2: O2 -m> O3) (g:O1 -m> O2),
               f1<= f2 -> f1 @ g <= f2 @ g.
auto.
Save.
Hint Resolve fmon_comp_monotonic1.

Definition fcomp : forall O1 O2 O3:ord,  (O2 -m> O3) -m> (O1 -m> O2) -m> (O1 -m> O3).
   intros; exists (fun f : O2 -m> O3 => 
                  mk_fmono (fmonot:=fun g : O1 -m> O2 => fmon_comp f g)
                                    (fmon_comp_monotonic2 f)).
red; intros; simpl; intros.
apply H.
Defined.

Lemma fmon_le_compat : forall (O1 O2:ord) (f: O1 -m> O2) (x y:O1), x<=y -> f x <= f y.
intros; apply (fmonotonic f); auto.
Save.
Hint Resolve fmon_le_compat.

Lemma fmon_le_compat2 : forall (O1 O2 O3:ord) (f: O1 -m> O2 -m> O3) (x y:O1) (z t:O2),
             x<=y -> z <=t -> f x z <= f y t.
intros; apply Ole_trans with (f x t).
apply (fmonotonic (f x)); auto.
apply (fmonotonic f); auto.
Save.
Hint Resolve fmon_le_compat2.

Lemma fmon_cte_comp : forall (O1 O2 O3:ord)(c:O3)(f:O1-m>O2),
              fmon_cte O2 c @ f == fmon_cte O1 c.
intros; apply fmon_eq_intro; intro x; auto.
Save.

(** ** Basic operators of omega-cpos *)
(** - Constant : $0$ REMOVED
     - lub : limit of monotonic sequences
*)


(** *** Definition of cpos *)
Record cpo : Type := mk_cpo 
  {tcpo :> ord;
   lub : (natO -m> tcpo) -> tcpo;
   le_lub : forall (c : natO -m> tcpo) (n : nat), c n <= lub c;
   lub_le : forall (c : natO -m> tcpo) (x : tcpo), (forall n, c n <= x) -> lub c <= x}.


Hint Resolve le_lub lub_le.

(** *** Least upper bounds *)

Add Parametric Morphism (c:cpo) : (@lub c) 
with signature (@Ole (natO -m> c)) ++> (@Ole c) 
as lub_le_compat_morph.
intros f g H; apply lub_le; intros.
apply Ole_trans with (g n); auto.
Save.
Hint Resolve lub_le_compat_morph.

Lemma lub_le_compat : forall (D:cpo) (f g:natO -m> D), f <= g -> lub f <= lub g.
intros; apply lub_le; intros.
apply Ole_trans with (g n); auto.
Save.
Hint Resolve lub_le_compat.

Definition Lub : forall (D:cpo), (natO -m> D) -m> D.
intro D; exists (fun (f :natO-m>D) => lub f); red; auto.
Defined.

Add Parametric Morphism (c:cpo) : (@lub c) 
with signature (@Oeq (natO -m> c)) ==> (@Oeq c) as lub_eq_compat.
intros; apply Ole_antisym; auto.
Save.
Hint Resolve lub_eq_compat.



Lemma lub_cte : forall (D:cpo) (d:D), lub (fmon_cte natO d) == d.
intros; apply Ole_antisym; auto.
apply (le_lub (fmon_cte natO d) (O)); auto.
Save.

Hint Resolve lub_cte.

Lemma lub_lift_right : forall (D:cpo) (f:natO -m> D) n, lub f == lub (mseq_lift_right f n).
intros; apply Ole_antisym; auto.
apply lub_le_compat; intro.
unfold mseq_lift_right; simpl.
apply (fmonotonic f); auto with arith.
Save.
Hint Resolve lub_lift_right.

Lemma lub_lift_left : forall (D:cpo) (f:natO -m> D) n, lub f == lub (mseq_lift_left f n).
intros; apply Ole_antisym; auto.
apply lub_le_compat; intro.
unfold mseq_lift_left; simpl.
apply (fmonotonic f); auto with arith.
Save.
Hint Resolve lub_lift_left.

Lemma lub_le_lift : forall (D:cpo) (f g:natO -m> D) (n:natO), 
        (forall k, n <= k -> f k <= g k) -> lub f <= lub g.
intros; apply lub_le; intros.
apply Ole_trans with (f (n+n0)).
apply (fmonotonic f); simpl; auto with arith.
apply Ole_trans with (g (n+n0)); auto.
apply H; simpl; auto with arith.
Save.

Lemma lub_eq_lift : forall (D:cpo) (f g:natO -m> D) (n:natO), 
        (forall k, n <= k -> f k == g k) -> lub f == lub g.
intros; apply Ole_antisym; apply lub_le_lift with n; intros; auto.
apply Oeq_le_sym; auto.
Save.

(** - (lub_fun h) x = lub_n (h n x) *)
Definition lub_fun : forall (O:ord) (D:cpo) (h : natO -m> O -m> D), O -m> D.
intros; exists (fun m => lub (h <_> m)).
red; intros.
apply lub_le_compat; simpl; intros.
apply (fmonotonic (h x0)); auto.
Defined.

Lemma lub_fun_eq : forall (O:ord) (D:cpo) (h : natO -m> O -m> D) (x:O), 
           lub_fun h x == lub (h <_> x).
auto.
Save.

Lemma lub_fun_shift :  forall (D:cpo) (h : natO -m> (natO -m>  D)),
             lub_fun h == Lub D @ (fmon_shift h).
intros; apply fmon_eq_intro; unfold lub_fun; simpl; auto.
Save.

Lemma double_lub_simpl : forall (D:cpo) (h : natO -m> natO -m>  D),
        lub (Lub D @ h) == lub (fmon_diag h). 
intros; apply Ole_antisym.
apply lub_le; intros; simpl; apply lub_le; intros.
apply Ole_trans with (h n (n+n0)).
apply (fmonotonic (h n)); auto with arith.
apply Ole_trans with (h (n+n0) (n+n0)).
apply (fmonotonic h); auto with arith.
apply (le_lub (fmon_diag h) ((n + n0)%nat)).
apply lub_le_compat.
unfold fmon_diag; simpl; auto.
Save.

Lemma lub_exch_le : forall (D:cpo) (h : natO -m> (natO -m>  D)),
                    lub (Lub D @ h) <= lub (lub_fun h).
intros; apply lub_le; intros; simpl.
apply lub_le; intros.
apply Ole_trans with (lub (h n)); auto.
apply lub_le_compat; intro.
unfold lub_fun; simpl.
apply (le_lub (h <_> x) (n)).
Save.
Hint Resolve lub_exch_le.

Lemma lub_exch_eq : forall (D:cpo) (h : natO -m> (natO -m>  D)),
 lub (Lub D @ h) == lub (lub_fun h).
intros; apply Ole_antisym; auto.
Save.

Hint Resolve lub_exch_eq.

(** *** Functional cpos *)

Definition fcpo : Type -> cpo -> cpo.
intros A D; exists (ford A D)  
                   (fun f (x:A) => lub(c:=D) (f <o> x)); intros; auto.
intro x; apply Ole_trans with ((c <o> x) n); auto.
Defined.

Infix "-O->" := fcpo (right associativity, at level 30) : O_scope.

Lemma fcpo_lub_simpl : forall A (D:cpo) (h:natO-m> A-O->D)(x:A),
      (lub h) x = lub(c:=D) (h<o> x).
trivial.
Save.

(** ** Continuity *)

Lemma lub_comp_le : 
    forall (D1 D2 : cpo) (f:D1 -m> D2) (h : natO -m> D1),  lub (f @ h) <= f (lub h).
intros; apply lub_le; simpl; intros.
apply (fmonotonic f); auto.
Save.
Hint Resolve lub_comp_le.

Lemma lub_comp2_le : forall (D1 D2 D3: cpo) (F:D1 -m> D2-m>D3) (f : natO -m> D1) (g: natO -m> D2), 
        lub ((F @2 f) g) <= F (lub f)  (lub g).
intros; apply lub_le; simpl; auto.
Save.
Hint Resolve lub_comp2_le.

Definition continuous (D1 D2 : cpo) (f : D1 -m> D2) :=
                forall c : natO -m> D1,  f (lub c) <= lub (f <m< c).

Lemma continuous_eq_compat : forall (D1 D2 : cpo) (f g:D1 -m> D2), 
                 f == g -> continuous f -> continuous g.
red; intros.
apply Ole_trans with (f (lub c)).
assert (g <= f); auto.
rewrite <- H; auto.
Save. 

Add Parametric Morphism (D1 D2 : cpo) : (@continuous D1 D2)
with signature (@Oeq (D1 -m> D2)) ==> iff as continuous_eq_compat_iff.
split; intros.
apply continuous_eq_compat with x; trivial.
apply continuous_eq_compat with y; auto.
Save.

Lemma lub_comp_eq : 
    forall (D1 D2 : cpo) (f:D1 -m> D2) (h : natO -m> D1),  continuous f -> f (lub h) == lub (f @ h).
intros; apply Ole_antisym; auto.
Save.
Hint Resolve lub_comp_eq.



(** - double_app f g n m = f m (g n) *)
Definition double_app (O1 O2 O3 O4: ord) (f:O1 -m> O3 -m> O4) (g:O2 -m> O3) 
        : O2 -m> (O1 -m> O4) := (fmon_shift f) @ g.
 
(** ** Cpo of monotonic functions *)

Definition fmon_cpo : forall (O:ord) (D:cpo), cpo.
intros; exists (fmon O D) 
               (* (mon0 O D) *)
               (lub_fun (O:=O) (D:=D)); auto.
simpl; intros.
apply (le_lub (fmon_app c x) (n)); auto.
Defined.

Infix "-M->" := fmon_cpo (at level 30, right associativity) : O_scope.

Lemma fmon_lub_simpl : forall (O:ord) (D:cpo) (h:natO-m>O-M->D) (x:O),
             (lub h) x = lub (h <_> x).
trivial.
Save.

Lemma double_lub_diag : forall (D:cpo) (h:natO-m>natO-M->D),
             lub (lub h) == lub (fmon_diag h).
intros.
intros; apply Ole_antisym.
apply lub_le; intros; simpl; apply lub_le; intros; simpl.
apply Ole_trans with (h (n+n0) (n+n0)); auto with arith.
apply (le_lub (fmon_diag h) ((n + n0)%nat)).
apply lub_le_compat.
unfold fmon_diag; simpl; intros.
apply (le_lub (h <_> x) (x)).
Save.



(** *** Continuity *)

Definition continuous2 (D1 D2 D3: cpo) (F:D1 -m> D2 -m> D3)
     := forall (f : natO-m>D1) (g :natO-m>D2), F (lub f) (lub g) <= lub ((F @2 f) g).

Lemma continuous2_app : forall (D1 D2 D3:cpo) (F : D1-m>D2-m>D3),
            continuous2 F -> forall k, continuous (F k).
red.
intros.
apply Ole_trans with (F (lub (mseq_cte k))  (lub c)); auto.
apply Ole_trans with (lub ((F @2 (mseq_cte k)) c)); auto.
Save.

Lemma continuous2_continuous : forall (D1 D2 D3:cpo) (F : D1-m>D2-M->D3),
            continuous2 F -> continuous F.
red; intros; intro k.
apply Ole_trans with (F (lub c) (lub (mseq_cte k)) ); auto.
apply Ole_trans with (lub ((F @2 c) (mseq_cte k))); auto.
Save.

Lemma continuous2_left : forall (D1 D2 D3:cpo) (F : D1-m>D2-M->D3) (h:natO-m>D1) (x:D2),
            continuous2 F -> F (lub h) x <= lub ((F <_> x) @h).
intros; apply (continuous2_continuous H h x).
Save.

Lemma continuous2_right : forall (D1 D2 D3:cpo) (F : D1-m>D2-M->D3) (x:D1)(h:natO-m>D2),
            continuous2 F -> F x (lub h) <= lub (F x @h).
intros; apply (continuous2_app H x).
Save.

Lemma continuous_continuous2 : forall (D1 D2 D3:cpo) (F : D1-m>D2-M->D3),
      (forall k:D1, continuous (F k)) -> continuous F -> continuous2 F.
red; intros.
apply Ole_trans with (lub (F (lub f) @ g)); auto.
apply lub_le; simpl; intros.
apply Ole_trans with (lub ((F <_> (g n))@f)).
apply Ole_trans with (lub (c:=D2 -M-> D3) (F@f) (g n)); auto.
rewrite (lub_lift_right ((F @2 f) g) n).
apply lub_le_compat; simpl; intros.
apply Ole_trans with (F (f x) (g (x+n))); auto with arith.
Save.

Hint Resolve continuous2_app continuous2_continuous continuous_continuous2.

Lemma lub_comp2_eq : forall (D1 D2 D3:cpo) (F : D1 -m> D2 -M-> D3),
      (forall k:D1, continuous (F k)) -> continuous F -> 
      forall (f : natO-m>D1) (g :natO-m>D2),
      F (lub f) (lub g) == lub ((F@2 f) g).
intros; apply Ole_antisym; auto.
apply (continuous_continuous2 (F:=F)); trivial.
Save.

Lemma continuous_sym : forall (D1 D2:cpo) (F : D1-m> D1 -M-> D2),
      (forall x y, F x y == F y x) -> (forall k:D1, continuous (F k)) -> continuous F.
red; intros; intro k.
apply Ole_trans with (F k (lub c)); auto.
apply Ole_trans with (lub ((F k) @ c)); auto.
Save.

Lemma continuous2_sym : forall (D1 D2:cpo) (F : D1-m>D1-m>D2),
      (forall x y, F x y == F y x) -> (forall k, continuous (F k)) -> continuous2 F.
intros; apply continuous_continuous2; auto.
apply continuous_sym; auto.
Save.
Hint Resolve continuous2_sym.

(** - continuity is preserved by composition *)

Lemma continuous_comp : forall (D1 D2 D3:cpo) (f:D2-m>D3)(g:D1-m>D2),
             continuous f -> continuous g -> continuous (f@g).
red; intros.
rewrite fmon_comp_simpl.
apply Ole_trans with (f (lub (g @ c))); auto.
apply Ole_trans with (lub (f @ (g @ c))); auto.
Save.
Hint Resolve continuous_comp.

(** ** Cpo of continuous functions *)

Lemma cont_lub : forall (D1 D2 : cpo) (f:natO -m> (D1 -m> D2)),
                                        (forall n, continuous (f n)) ->
                                        continuous  (lub (c:=D1-M->D2) f).
red; intros; simpl.
apply Ole_trans with   
                        (lub (c:=D2) (Lub D2 @ (fmon_shift (double_app f c)))).
apply lub_le_compat; intro n; simpl.
apply Ole_trans with (lub ((f n) @ c)); auto.
rewrite lub_exch_eq.
apply lub_le_compat; intro n; simpl.
apply lub_le_compat; intro m; simpl; auto.
Save.

Record fconti (D1 D2:cpo): Type := mk_fconti 
   {fcontit : D1 -m> D2; 
    fcontinuous : continuous fcontit}.
Hint Resolve fcontinuous.

Definition fconti_fun (D1 D2 :cpo) (f:fconti D1 D2) : D1-> D2 :=fun x => fcontit f x.
Coercion fconti_fun : fconti >-> Funclass.

Definition fcont_ord : cpo -> cpo -> ord.
intros D1 D2; exists (fconti D1 D2) (fun f g => fcontit f <= fcontit g); intros; auto.
apply Ole_trans with (fcontit y); auto.
Defined.

(** printing -c> %\cont% *)
Infix "-c>" := fcont_ord (at level 30, right associativity) : O_scope.

Lemma fcont_le_intro : forall (D1 D2:cpo) (f g : D1 -c> D2), (forall x, f x <= g x) -> f <= g.
trivial.
Save.

Lemma fcont_le_elim : forall (D1 D2:cpo) (f g : D1 -c> D2), f <= g -> forall x, f x <= g x.
trivial.
Save.

Lemma fcont_eq_intro : forall (D1 D2:cpo) (f g : D1 -c> D2), (forall x, f x == g x) -> f == g.
intros; apply Ole_antisym; apply fcont_le_intro; auto.
Save.

Lemma fcont_eq_elim : forall (D1 D2:cpo) (f g : D1 -c> D2), f == g -> forall x, f x == g x.
intros; apply Ole_antisym; apply fcont_le_elim; auto.
Save.

Lemma fcont_monotonic : forall (D1 D2:cpo) (f : D1 -c> D2) (x y : D1),
            x <= y -> f x <= f y.
intros; apply (fmonotonic (fcontit f) H).
Save.
Hint Resolve fcont_monotonic.

Lemma fcont_stable : forall (D1 D2:cpo) (f : D1 -c> D2) (x y : D1),
            x == y -> f x == f y.
intros; apply (fmon_stable (fcontit f) H).
Save.
Hint Resolve fcont_monotonic.

(*
Definition fcont0 (D1 D2:cpo) : D1 -c> D2 := mk_fconti (cont0 D1 D2).
*)

Definition Fcontit (D1 D2:cpo) : (D1 -c> D2) -m> D1-m> D2.
intros D1 D2; exists (fcontit (D1:=D1) (D2:=D2)); auto.
Defined.


Definition fcont_lub (D1 D2:cpo) : (natO -m> D1 -c> D2) -> D1 -c> D2.
intros D1 D2 f; exists (lub (c:=D1-M->D2) (Fcontit D1 D2 @f)).
apply cont_lub; intros; simpl; auto.
Defined.

Definition fcont_cpo : cpo -> cpo -> cpo.
intros D1 D2; exists (fcont_ord D1 D2) 
                     (* (fcont0 D1 D2) *)
                     (fcont_lub (D1:=D1) (D2:=D2)); 
simpl; intros; auto.
apply (le_lub ((Fcontit D1 D2 @ c) <_> x) (n)).
Defined.

(** printing -C-> %\Cont% *)
Infix "-C->" := fcont_cpo (at level 30, right associativity) : O_scope.

Add Parametric Morphism (D E:cpo) : (fun f d => f d)
with signature (@Oeq (D -c> E)) ==> (@Oeq D) ==> (@Oeq E)
as app_eq_compat.
intros x y xeq a b aeq.
refine (Oeq_trans  _ _).
assert (stable x) by auto. unfold stable in H. apply H. apply aeq. auto.
Qed.

Add Parametric Morphism (D E:cpo) : (fun f d => f d)
with signature (@Ole (D -c> E)) ==> (@Ole D) ==> (@Ole E)
as app_le_compat.
intros x y xeq a b aeq.
refine (Ole_trans  _ _).
assert (monotonic x) by auto. apply H. apply aeq. auto.
Qed.

Add Parametric Morphism (D E:cpo) : (fun f d => f d)
with signature (@Oeq (D -C-> E)) ==> (@Oeq D) ==> (@Oeq E)
as App_eq_compat.
intros x y xeq a b aeq.
refine (Oeq_trans  _ _).
assert (stable x) by auto. unfold stable in H. apply H. apply aeq. auto.
Qed.

Add Parametric Morphism (D E:cpo) : (fun f d => f d)
with signature (@Ole (D -C-> E)) ==> (@Ole D) ==> (@Ole E)
as App_le_compat.
intros x y xeq a b aeq.
refine (Ole_trans  _ _).
assert (monotonic x) by auto. apply H. apply aeq. auto.
Qed.

Add Parametric  Morphism (D E:cpo) (f:D -C-> E) : (@fcontit D E)
with signature (@Ole (D -c> E)) ++> (@Ole (D -m> E))
as fcontit_le_compat.
intros ; auto.
Qed.

Add Parametric  Morphism (D E:cpo) (f:D -C-> E) : (@fcontit D E)
with signature (@Oeq (D -c> E)) ==> (@Oeq (D -m> E))
as fcontit_eq_compat.
intros ; auto.
Qed.

Definition fcont_app (O:ord) (D1 D2:cpo) (f: O -m> D1-c> D2) (x:D1) : O -m> D2
         := Fcontit D1 D2 @ f <_> x.

Infix "<__>" := fcont_app (at level 70) : O_scope.

Lemma fcont_app_simpl : forall (O:ord) (D1 D2:cpo) (f: O -m> D1-c> D2) (x:D1)(y:O),
            (f <__> x) y = f y x.
trivial.
Save.

Definition ford_fcont_shift (A:Type) (D1 D2:cpo) (f: A -o> (D1-c> D2)) : D1 -c> A -O-> D2.
intros; exists (ford_shift (fun x => Fcontit D1 D2 (f x))).
red; intros; intro x.
simpl.
apply Ole_trans with (lub (fcontit (f x) @ c)); auto.
Defined.

Definition fmon_fcont_shift (O:ord) (D1 D2:cpo) (f: O -m> D1-c> D2) : D1 -c> O -M-> D2.
intros; exists (fmon_shift (Fcontit D1 D2@f)).
red; intros; intro x.
simpl.
rewrite (fcontinuous (f x) c); auto.
Defined.

Lemma fcont_app_continuous : 
       forall (O:ord) (D1 D2:cpo) (f: O -m> D1-c> D2) (h:natO-m>D1),
            f <__> (lub h) <= lub (c:=O-M->D2) (fcontit (fmon_fcont_shift f) @ h).
intros; intro x.
rewrite fcont_app_simpl.
rewrite (fcontinuous (f x) h); auto.
Save.

Lemma fcont_lub_simpl : forall (D1 D2:cpo) (h:natO-m>D1-C->D2)(x:D1),
            lub h x = lub (h <__> x).
trivial.
Save.

Definition continuous2_cont_app : forall (D1 D2 D3 :cpo) (f:D1-m> D2 -M-> D3), 
            (forall k, continuous (f k)) -> D1 -m> (D2 -C-> D3).
intros; exists (fun k => mk_fconti (H k)); red; intros; auto.
Defined.

Lemma continuous2_cont_app_simpl : 
forall (D1 D2 D3 :cpo) (f:D1-m> D2 -M-> D3)(H:forall k, continuous (f k))
        (k:D1),  continuous2_cont_app H k = mk_fconti (H k).
trivial.
Save.

Lemma continuous2_cont : forall (D1 D2 D3 :cpo) (f:D1-m> D2 -M-> D3), 
            continuous2 f -> D1 -c> (D2 -C-> D3).
intros; exists (continuous2_cont_app (f:=f) (continuous2_app H)).
red; intros; rewrite continuous2_cont_app_simpl; intro k; simpl.
apply Ole_trans with (lub (c:=D2-M->D3) (f @ c) k); auto.
assert (continuous f); auto.
Defined.

Lemma Fcontit_cont : forall D1 D2, continuous (D1:=D1-C->D2) (D2:=D1-M->D2) (Fcontit D1 D2).
red; intros; auto.
Save.
Hint Resolve Fcontit_cont.


Definition fcont_comp : forall (D1 D2 D3:cpo), (D2 -c> D3) -> (D1-c> D2) -> D1 -c> D3.
intros D1 D2 D3 f g.
exists (fcontit f @ fcontit g); auto.
Defined.

(** printing << %\contcomp% *)
Infix "<<" := fcont_comp (at level 35) : O_scope.

Lemma fcont_comp_assoc: forall (D E F G:cpo) (f:F -C-> G) (g:E -C-> F) (h:D -C-> E),
          (f << g) << h == f << (g << h).
intros D E F G f g h. apply fcont_eq_intro. auto.
Qed.

Lemma fcont_comp_simpl : forall (D1 D2 D3:cpo)(f:D2 -c> D3)(g:D1-c> D2) (x:D1),
       (f << g) x = f (g x).
trivial.
Save.

Lemma fcontit_comp_simpl : forall (D1 D2 D3:cpo)(f:D2 -c> D3)(g:D1-c> D2) (x:D1),
       fcontit (f << g) = fcontit f @ fcontit g.
trivial.
Save.

Lemma fcont_comp_le_compat : forall (D1 D2 D3:cpo) (f g : D2 -c> D3) (k l :D1-c> D2),
      f <= g -> k <= l -> f << k <= g << l.
intros; apply fcont_le_intro; intro x.
repeat (rewrite fcont_comp_simpl).
apply Ole_trans with (g (k x)); auto.
Save.
Hint Resolve fcont_comp_le_compat.

Add Parametric Morphism (D1 D2 D3 : cpo) : (@fcont_comp D1 D2 D3)
with signature (@Ole (D2 -c> D3)) ++> (@Ole (D1 -c> D2)) ++> (@Ole (D1 -c> D3)) 
as fcont_comp_le_morph.
intros.
exact (fcont_comp_le_compat H H0).
Save.

Add Parametric Morphism (D1 D2 D3 : cpo) : (@fcont_comp D1 D2 D3)
with signature (@Oeq (D2 -c> D3)) ==> (@Oeq (D1 -c> D2)) ==> (@Oeq (D1 -c> D3))
as fcont_comp_eq_compat.
intros.
apply Ole_antisym; auto.
Save.

Definition fcont_Comp (D1 D2 D3:cpo) : (D2 -C-> D3) -m> (D1-C-> D2) -m> D1 -C-> D3 
      := le_compat2_mon (fcont_comp_le_compat (D1:=D1) (D2:=D2) (D3:=D3)).

Lemma fcont_Comp_simpl : forall (D1 D2 D3:cpo) (f:D2 -c> D3) (g:D1-c> D2),
               fcont_Comp D1 D2 D3 f g = f << g.
trivial.
Save.

Lemma fcont_Comp_continuous2 : forall (D1 D2 D3:cpo), continuous2 (fcont_Comp D1 D2 D3).
red; intros.
change ((lub  f) << (lub g) <= lub (c:=D1 -C-> D3) ((fcont_Comp D1 D2 D3 @2 f) g)).
apply fcont_le_intro; intro x; rewrite fcont_comp_simpl.
repeat (rewrite fcont_lub_simpl).
rewrite fcont_app_continuous.
rewrite double_lub_diag.
apply lub_le_compat; simpl; auto.
Save.

Definition fcont_COMP  (D1 D2 D3:cpo) : (D2 -C-> D3) -c> (D1-C-> D2) -C-> D1 -C-> D3 
      := continuous2_cont (fcont_Comp_continuous2 (D1:=D1) (D2:=D2) (D3:=D3)).

Lemma fcont_COMP_simpl : forall (D1 D2 D3:cpo) (f: D2 -C-> D3) (g:D1-C-> D2),
	fcont_COMP D1 D2 D3 f g = f << g.
trivial.
Save.

Definition fcont2_COMP  (D1 D2 D3 D4:cpo) : (D3 -C-> D4) -c> (D1-C-> D2-C->D3) -C-> D1 -C-> D2 -C-> D4 := 
   (fcont_COMP D1 (D2-C->D3) (D2 -C-> D4)) << (fcont_COMP D2 D3 D4).

Definition fcont2_comp  (D1 D2 D3 D4:cpo) (f:D3 -C-> D4)(F:D1-C-> D2-C->D3) := fcont2_COMP D1 D2 D3 D4 f F.

Infix "@@_" := fcont2_comp (at level 35) : O_scope.

Lemma fcont2_comp_simpl : forall (D1 D2 D3 D4:cpo) (f:D3 -C-> D4)(F:D1-C-> D2-C->D3)(x:D1)(y:D2),
       (f @@_ F) x y = f (F x y).
trivial.
Save.
            
Lemma fcont_le_compat2 : forall (D1 D2 D3:cpo) (f : D1-c>D2-C->D3)
    (x y : D1) (z t : D2), x <= y -> z <= t -> f x z <= f y t.
intros; apply Ole_trans with (f y z); unfold fconti_fun; auto.
apply fmon_le_elim.
apply  (fmonotonic (Fcontit D2 D3) (x:=fcontit f x) (y:=fcontit f y)); auto.
Save.
Hint Resolve fcont_le_compat2.

Lemma fcont_eq_compat2 : forall (D1 D2 D3:cpo) (f : D1-c>D2-C->D3)
    (x y : D1) (z t : D2), x == y -> z == t -> f x z == f y t.
intros; apply Ole_antisym; auto.
Save.
Hint Resolve fcont_eq_compat2.

Lemma fcont_continuous : forall (D1 D2 : cpo) (f:D1 -c> D2)(h:natO-m>D1),
            f (lub h) <= lub (fcontit f @ h).
intros; apply (fcontinuous f h).
Save.
Hint Resolve fcont_continuous.

Lemma fcont_continuous2 : forall (D1 D2 D3:cpo) (f:D1-c>(D2-C->D3)), 
                                             continuous2 (Fcontit D2 D3 @ fcontit f).
intros; apply continuous_continuous2; intros.
change (continuous (fcontit (f k))); auto.
apply (continuous_comp (D1:=D1) (D2:=D2-C->D3) (D3:=D2-M->D3) (f:=Fcontit D2 D3)); auto.
Save.
Hint Resolve fcont_continuous2.

Definition fcont_shift (D1 D2 D3 : cpo) (f:D1-c>D2-C->D3) : D2-c>D1-C->D3.
intros.
apply continuous2_cont with (f:=fmon_shift (Fcontit D2 D3 @ fcontit f)).
red; intros; repeat rewrite fmon_shift_simpl.
repeat rewrite fmon_comp_simpl; auto.
change (f (lub g) (lub f0) <= lub ((fmon_shift (Fcontit D2 D3 @ fcontit f) @2 f0) g)).
apply Ole_trans with (1:=fcont_continuous2 f g f0).
apply lub_le_compat; intro n.
repeat rewrite fmon_comp_simpl; auto.
Defined.

Lemma fcont_shift_simpl : forall (D1 D2 D3 : cpo) (f:D1-c>D2-C->D3) (x:D2) (y:D1),
            fcont_shift f x y = f y x.
trivial.
Save.

Definition fcont_SEQ  (D1 D2 D3:cpo) : (D1-C-> D2) -C-> (D2 -C-> D3) -C-> D1 -C-> D3 
      := fcont_shift (fcont_COMP D1 D2 D3).

Lemma fcont_SEQ_simpl : forall (D1 D2 D3:cpo) (f: D1 -C-> D2) (g:D2-C-> D3),
	fcont_SEQ D1 D2 D3 f g = g << f.
trivial.
Save.

Definition fcont_comp2 : forall (D1 D2 D3 D4:cpo), 
                (D2 -c> D3 -C->D4) -> (D1-c> D2) -> (D1 -c> D3) -> D1-c>D4.
intros D1 D2 D3 D4 f g h.
exists (((Fcontit D3 D4 @fcontit f) @2 fcontit g) (fcontit h)).
red; intros; simpl.
change (f (g (lub c)) (h (lub c)) <= lub (c:=D4) ((Fcontit D3 D4 @ fcontit f @2 fcontit g) (fcontit h) @ c)).
apply Ole_trans with (f (lub (c:=D2) (fcontit g @ c)) (lub (c:=D3) (fcontit h @ c))); auto.
apply (fcont_continuous2 f (fcontit g @ c) (fcontit h @ c)).
Defined.

Infix "@2_" := fcont_comp2 (at level 35, right associativity) : O_scope.

Lemma fcont_comp2_simpl : forall (D1 D2 D3 D4:cpo)
                (F:D2 -c> D3 -C->D4) (f:D1-c> D2) (g:D1 -c> D3) (x:D1), (F@2_ f) g x = F (f x) (g x).
trivial.
Save.

Add Parametric Morphism (D1 D2 D3 D4:cpo) : (@fcont_comp2 D1 D2 D3 D4)
with signature (@Ole (D2 -c> D3 -C->D4)) ++> (@Ole (D1-c> D2)) ++> (@Ole (D1 -c> D3)) ++> (@Ole (D1-c>D4))
as fcont_comp2_le_morph.
intros F G HF f1 f2 Hf g1 g2 Hg x.
apply Ole_trans with (fcontit (fcontit G (fcontit f1 x)) (fcontit g1 x)); auto.

(* auto.*)
Focus 2.
change (Fcontit D3 D4 (fcontit G (fcontit f1 x)) (fcontit g1 x) <=
              Fcontit D3 D4 (fcontit G (fcontit f2 x)) (fcontit g2 x)).
apply (fmon_le_compat2 (Fcontit D3 D4)); auto.
simpl.
auto.
(* not entirely sure I've got the right signature here
   auto was supposed to deal with first sibgoal but doesn't
   I want to just setoid rewrite with HF
   but that doesn't work either
*)
unfold Ole in HF.
simpl in HF.
apply HF.
Save.

Add Parametric Morphism (D1 D2 D3 D4:cpo) : (@fcont_comp2 D1 D2 D3 D4)
with signature (@Oeq (D2 -c> D3 -C->D4)) ==> (@Oeq (D1-c> D2)) ==> 
   (@Oeq (D1 -c> D3)) ==> (@Oeq (D1-c>D4))
as fcont_comp2_eq_compat.
intros F G (HF1,HF2) f1 f2 (Hf1,Hf2) g1 g2 (Hg1,Hg2).
apply Ole_antisym.
exact (fcont_comp2_le_morph HF1 Hf1 Hg1).
exact (fcont_comp2_le_morph HF2 Hf2 Hg2).
Save.

Lemma fcont_comp2_comp: forall (D E F G H:cpo) (f:D -C-> E -C-> F) (g:H -C-> D) (h: H -C-> E) (a:G -C-> H),
         (f @2_ g) h << a == (f @2_ (g << a)) (h << a).
intros. apply fcont_eq_intro.
intros gg. auto.
Qed.

(*==========================================================================
  Constant map
  ==========================================================================*)

Definition kab (O1 O2:ord) (b : O2): O1-m>O2.
intros; exists (fun a => b).
red. auto.
Defined.

Definition K (D1 D2 : cpo) (d:D2) : D1 -c> D2.
intros; exists (kab D1 d).
red.
intros.
simpl.
setoid_replace d with ((kab D1 (O2:=D2) d @ c) 0).
apply le_lub.
simpl.
trivial.
Defined.



Lemma K_com: forall (D E A:cpo) (f:D -C-> E) (e:A), @K D A e == @K E A e << f.
Proof.
intros D E A f e. apply fcont_eq_intro. intros d. rewrite fcont_comp_simpl. auto.
Qed.

Lemma K_simpl: forall (D E:cpo) (e:E) (d:D), K E d e = d.
auto.
Qed.

(*==========================================================================
  Identity function
  ==========================================================================*)

Definition Id : forall O:ord, O-m>O.
intros; exists (fun x => x); red; auto.
Defined.

(** printing ID %\ID% *)
Definition ID : forall D:cpo, D-c>D.
intros; exists (Id D); red; auto.
Defined.
Implicit Arguments ID [D].

Lemma fcont_comp_unitR: forall D E (f:D -C-> E), f << ID == f.
intros D E f. apply fcont_eq_intro. auto.
Qed.

Lemma fcont_comp_unitL: forall D E (f:D -C-> E), ID << f == f.
intros. apply fcont_eq_intro. auto.
Qed.

Lemma Id_simpl : forall O x, Id O x = x.
trivial.
Save.

Lemma ID_simpl : forall (D:cpo) (x:D), ID x = Id D x.
trivial.
Save.

Definition AP (D1 D2:cpo) : (D1-C->D2)-c>D1-C->D2:=ID. 

Lemma AP_simpl : forall (D1 D2:cpo) (f : D1-C->D2) (x:D1), AP D1 D2 f x = f x.
trivial.
Save.

Definition fcont_comp3 (D1 D2 D3 D4 D5:cpo)
                (F:D2 -c> D3 -C->D4-C->D5)(f:D1-c> D2)(g:D1 -c> D3)(h:D1-c>D4): D1-c>D5
  := (AP D4 D5 @2_ ((F @2_ f) g)) h.

Infix "@3_" := fcont_comp3 (at level 35, right associativity) : O_scope.

Lemma fcont_comp3_simpl : forall (D1 D2 D3 D4 D5:cpo)
                (F:D2 -c> D3 -C->D4-C->D5) (f:D1-c> D2) (g:D1 -c> D3) (h:D1-c>D4) (x:D1), 
                (F@3_ f) g h x = F (f x) (g x) (h x).
trivial.
Save.

Add Parametric Morphism (D E F G H:cpo) : (@fcont_comp3 D E F G H)
with signature (@Oeq (E -c> (F -C-> G -C-> H))) ==> (@Oeq (D -c> E)) ==> (@Oeq (D -c> F)) ==> (@Oeq (D -c> G)) ==> (@Oeq (D -c> H))
as fcont_comp3_eq_compat.
intros h0 h1 heq e0 e1 eeq f0 f1 feq g0 g1 geq.
simpl. apply fcont_eq_intro. intros d.
repeat (rewrite fcont_comp3_simpl).
repeat (refine (App_eq_compat _ _) ; auto).
Qed.

Add Parametric Morphism (D E F G H:cpo) : (@fcont_comp3 D E F G H)
with signature (@Oeq (E -c> F -C-> G -C-> H)) ==> (@Oeq (D -c> E)) ==> (@Oeq (D -c> F)) ==> (@Oeq (D -c> G)) ==> (@Oeq (D -c> H))
as fcont_comp3_eq_compat_aux.
intros h0 h1 heq e0 e1 eeq f0 f1 feq g0 g1 geq.
simpl. apply fcont_eq_intro. intros d.
repeat (rewrite fcont_comp3_simpl).
repeat (refine (App_eq_compat _ _)) ; auto.
Qed.

Lemma fcont_comp3_comp: forall (D E F G H A:cpo) (f:D -C-> E -C-> F -C-> G) (g:H -C-> D)
           (h:H -C-> E) (k:H -C-> F) (a:A -C-> H),
        (f @3_ g) h k << a == (f @3_ (g << a)) (h << a) (k << a).
intros. refine (fcont_eq_intro _). auto.
Qed.

(** Discrete cpo on a Set. This should really be an arbitrary Setoid, I guess. *)
Definition Discrete_ord (X:Type) : ord.
intro X.
exists X (fun x y => x=y); intuition.
subst.
trivial.
Defined.

Definition Discrete (X:Type) : cpo.
intro X; exists (Discrete_ord X) (fun (c:natO -m> Discrete_ord X) => c 0).
 intros; assert (c 0 <= c n).
 apply fmonotonic.
 intuition.
 intuition.

 intros.
 apply H.
Defined.

(* Empty cpo *)
Inductive DEmp : Set := .

Definition DZero : cpo := Discrete DEmp.

Lemma DZero_initial : forall D (f g : DZero -c> D), f == g.
intros D f g. refine (fcont_eq_intro _).
intros x. case x.
Qed.

(** printing PBot %\ensuremath{\bot}% *)
(** printing Pointed %\Pointed% *)
(* Messing with classes *)
Class Pointed (D : cpo) := {
 PBot : D;
 Pleast : forall d:D, PBot <= d }.

Hint Resolve @Pleast.

Definition strict D E {pd : Pointed D} {pe : Pointed E} (f:D -C-> E) := f PBot == PBot.

Instance fun_pointed A B {pb : Pointed B} : Pointed (A -C-> B).
intros; destruct pb.
exists (K A PBot0).
intro; simpl.
intro; auto.
Defined.

