(**********************************************************************************
 * Fin.v                                                                          *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                       *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)

(* Finite nats and maps *)

Require Export ssreflect ssrnat.
Require Export NaryFunctions.
Require Import Program.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Inductive Fin : nat -> Type :=
| FinZ : forall n, Fin n.+1
| FinS : forall n, Fin n -> Fin n.+1.

Definition FMap n D := Fin n -> D.

(* Head, tail and cons *)
Definition tl n D (m:FMap n.+1 D) : FMap n D := fun v => m (FinS v).
Definition hd n D (m:FMap n.+1 D) : D := m (FinZ _).

Definition cons n D (hd:D) (tl : FMap n D) : FMap n.+1 D :=
  (fun var =>
    match var in Fin n return FMap n.-1 D -> D with 
      | FinZ _      => fun _   => hd
      | FinS _ var' => fun tl' => tl' var'
    end tl). 

Fixpoint nth n D (v : Fin n) : FMap n D -> D :=
  match v with
  | FinZ _ => fun m => hd m
  | FinS _ i => fun m => nth i (tl m) 
  end.

Fixpoint asTuple n D : FMap n D -> D ^ n :=
  match n with 
  | 0 => fun m => tt
  | n.+1 => fun m => (hd m, asTuple (tl m))
  end. 

Lemma hdCons : forall n D (v : D) (m : FMap n D), hd (cons v m) = v. 
Proof. by []. Qed.

Axiom Extensionality : forall n D (m1 m2 : FMap n D), (forall i, m1 i = m2 i) -> m1 = m2.

Lemma tlCons : forall n D (v : D) (s : FMap n D), tl (cons v s) = s. 
Proof. move => n D v s. by apply Extensionality. Qed.

Ltac extFMap i :=  (apply Extensionality; intros i; dependent destruction i).

Lemma consEta : forall n D (m:FMap n.+1 D), m = cons (hd m) (tl m).
Proof. move => n D m. extFMap i; by []. Qed.



