(**********************************************************************************
 * KSOp.v                                                                 *
 * Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages *
 * Nick Benton, Lars Birkedal, Andrew Kennedy and Carsten Varming                 *
 * Jan 2012                                                                       *
 * Build with Coq 8.3pl2 plus SSREFLECT                                           *
 **********************************************************************************)

(* Operational semantics of the kitchen sink language *)

Require Import Finmap KSTm Fin.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import Tm.

Definition Heap := FinDom [compType of nat] (Value O).

Definition subSingle E (v:Value E) e := subExp (cons v (@idSub _)) e.

(*=EV *)
Inductive EV : nat -> Exp 0 -> Heap -> Value O -> Heap -> Type :=
| EvVAL h v : EV O (VAL v) h v h
| EvFST h v0 v1 : EV O (FST (PAIR v0 v1)) h v0 h
| EvSND h v0 v1 : EV O (SND (PAIR v0 v1)) h v1 h
| EvOP h op n0 n1 : EV O (OP op (PAIR (INT n0) (INT n1))) h (INT (op n0 n1)) h
| EvUNFOLD h v : EV 1 (UNFOLD (FOLD v)) h v h
| EvREF (h:Heap) v (l:nat) : l \notin dom h -> EV 1 (REF v) h (LOC l) (updMap l v h)
| EvBANG (h:Heap) v (l:nat) : h l = Some v -> EV 1 (BANG (LOC l)) h v h
| EvASSIGN (h:Heap) v l : h l -> EV 1 (ASSIGN (LOC l) v) h UNIT (updMap l v h)
| EvLET h n0 e0 v0 h0 n1 e1 v h1 : EV n0 e0 h v0 h0 -> 
    EV n1 (subSingle v0 e1) h0 v h1 -> EV (n0 + n1) (LET e0 e1) h v h1
| EvAPP h n e v0 v h0 : EV n (subSingle v e) h v0 h0 ->
    EV n (APP (LAM e) v) h v0 h0
| EvTAPP h n e v0 h0 : EV n e h v0 h0 -> EV n (TAPP (TLAM e)) h v0 h0
| EvCASEL h n v e0 e1 v0 h0 : EV n (subSingle v e0) h v0 h0 ->
    EV n (CASE (INL v) e0 e1) h v0 h0
| EvCASER h n v e0 e1 v0 h0 : EV n (subSingle v e1) h v0 h0 ->
    EV n (CASE (INR v) e0 e1) h v0 h0.
(*=End *)

