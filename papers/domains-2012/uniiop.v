(**********************************************************************************
 * uniiop.v                                                                       *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                       *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)

Require Export unii.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Reserved Notation "e '=>>' v" (at level 75).

(*=Evaluation *)
Inductive Evaluation : Exp O -> Value O -> Prop :=
| e_Val : forall v, VAL v =>> v
| e_App : forall e1 v2 v, subExp [v2] e1 =>> v -> APP (LAMBDA e1) v2 =>> v
| e_Let : forall e1 v1 e2 v2, e1 =>> v1 -> subExp [v1] e2 =>> v2 -> LET e1 e2 =>> v2
| e_Ifz1 : forall e1 e2 v1, e1 =>> v1 -> IFZ (INT 0) e1 e2 =>> v1
| e_Ifz2 : forall e1 e2 v2 n, e2 =>> v2 -> IFZ (INT (S n)) e1 e2 =>> v2
| e_Op : forall op n1 n2, OP op (INT n1) (INT n2) =>> INT (op n1 n2)
where "e =>> v" := (Evaluation e v).

(*=End *)

