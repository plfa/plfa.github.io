---
title     : "Substitution in the untyped lambda calculus"
layout    : page
prev      : /Untyped/
permalink : /Substitution/
next      : /LambdaReduction/
---


\begin{code}
module plfa.Substitution where
\end{code}

## Imports

\begin{code}
open import plfa.Untyped
  using (Type; Context; _⊢_; ★; _∋_; ∅; _,_; Z; S_; `_; ƛ_; _·_;
         rename; subst; ext; exts; _[_]; subst-zero)
open import plfa.Denotational using (Rename; extensionality)
open import plfa.Soundness using (Subst)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Function using (_∘_)
\end{code}

## Overview 

The primary purpose of this chapter is to prove that substitution
commutes with itself. Barendgredt (1984) refers to this
as the substitution lemma:
  
    M [x:=N] [y:=L] = M [y:=L] [x:= N[y:=L] ]

In our setting, with de Bruijn indices for variables, the statement of
the lemma becomes:

    M [ N ] [ L ] ≡  M〔 L 〕[ N [ L ] ]                     (substitution)

where the notation M 〔 L 〕 is for subsituting L for index 1 inside
M.  In addition, because we define substitution in terms of parallel
substitution, we have the following generalization, replacing the
substitution of L with an arbitrary parallel substitution σ.

    subst σ (M [ N ]) ≡ (subst (exts σ) M) [ subst σ N ]
                                                            (subst-commute)

The special case for renamings is also useful.

    rename ρ (M [ N ]) ≡ (rename (ext ρ) M) [ rename ρ N ]
                                                     (rename-subst-commute)

The secondary purpose of this chapter is to define the σ algebra of
parallel substitution due to Abadi, Cardelli, Curien, and Levy
(1991). The equations of this algebra not only help us prove the
substitution lemma, but they are generally useful. Futhermore, when
the equations are applied from left to right, they form a rewrite
system that _decides_ whether any two substitutions are equal.

We use the following more succinct notation the `subst` function.

\begin{code}
⧼_⧽ : ∀{Γ Δ A} → Subst Γ Δ → Γ ⊢ A → Δ ⊢ A
⧼ σ ⧽ = λ M → subst σ M
\end{code}


## The σ algebra of substitution

Substitutions map de Bruijn indices (natural numbers) to terms, so we
can view a substitution simply as a sequence of terms, or more
precisely, as an infinite sequence of terms. The σ algebra consists of
four operations for building such sequences: identity `ids`, shift
`↑`, cons `M • σ`, and sequencing `σ ⨟ τ`.  The sequence `0, 1, 2, ...`
is constructed by the identity subsitution.

\begin{code}
ids : ∀{Γ} → Subst Γ Γ
ids x = ` x
\end{code}

The sequence `1, 2, 3, ...` is constructed by the shift operation.

\begin{code}
↑ : ∀{Γ A} → Subst Γ (Γ , A)
↑ x = ` (S x)
\end{code}

Given a term `M` and substitution `σ`, the operation
`M • σ` constructs the sequence `M , σ 0, σ 1, σ 2, ...`.
This operation is analogous to the `cons` operation of Lisp.

\begin{code}
infixr 6 _•_

_•_ : ∀{Γ Δ A} → (Δ ⊢ A) → Subst Γ Δ → Subst (Γ , A) Δ
(M • σ) Z = M
(M • σ) (S x) = σ x
\end{code}

Given two substitutions `σ` and `τ`, the sequencing operation `σ ⨟ τ`
produces the sequence `⧼τ⧽(σ 0), ⧼τ⧽(σ 1), ⧼τ⧽(σ 2), ...`.
That is, it composes the two substitutions by first applying
`σ` and then applying `τ`.

\begin{code}
infixr 5 _⨟_

_⨟_ : ∀{Γ Δ Σ} → Subst Γ Δ → Subst Δ Σ → Subst Γ Σ
σ ⨟ τ = ⧼ τ ⧽ ∘ σ
\end{code}

For the sequencing operation, Abadi et al. use the notation of
function composition, writting `σ ∘ τ`, but still with `σ` applied
before `τ`, which is the opposite of standard mathematical
practice. We instead write `σ ⨟ τ`, because the semicolon has become
the standard notation for forward function composition.

## The σ algebra equations

The σ algebra includes the following equations.

    (sub-head)  ⧼ M • σ ⧽ (` Z) ≡ M
    (sub-tail)  ↑ ⨟ (M • σ)    ≡ σ
    (sub-η)     (⧼ σ ⧽ (` Z)) • (↑ ⨟ σ) ≡ σ
    (Z-shift)   (` Z) • ↑      ≡ ids
    
    (sub-id)    ⧼ ids ⧽ M      ≡ M
    (sub-app)   ⧼ σ ⧽ (L · M)  ≡ (⧼ σ ⧽ L) · (⧼ σ ⧽ M)
    (sub-abs)   ⧼ σ ⧽ (ƛ N)    ≡ ƛ ⧼ σ ⧽ N
    (sub-sub)   ⧼ τ ⧽ ⧼ σ ⧽ M  ≡ ⧼ σ ⨟ τ ⧽ M

    (sub-idL)   ids ⨟ σ        ≡ σ
    (sub-idR)   σ ⨟ ids        ≡ σ
    (sub-assoc) (σ ⨟ τ) ⨟ θ    ≡ σ ⨟ (τ ⨟ θ)
    (sub-dist)  (M • σ) ⨟ τ    ≡ (⧼ τ ⧽ M) • (σ ⨟ τ)

The first group of equations describe how the `•` operator acts like cons.
The equation `sub-head` says that the variable zero `Z` returns the
head of the sequence (it acts like the `car` of Lisp).  Similarly,
`sub-tail` says that sequencing with shift `↑` returns the tail of the
sequence (it acts like `cdr` of Lisp).  The `sub-η` equation is the
η-expansion rule for sequences, saying that taking the head and tail
of a sequence, and then cons'ing them together yields the original
sequence. The `Z-shift` equation says that cons'ing zero onto the
shifted sequence produces the identity sequence.

The next four equations involve applying substitutions to terms.  The
equation `sub-id` says that the identity substitution returns the term
unchanged. The equations `sub-app` and `sub-abs` says that
substitution is a congruence for the lambda calculus. The `sub-sub`
equation says that the sequence operator `⨟` behaves as intended.

The last four equations concern the sequencing of substitutions.
The first two equations, `sub-idL` and `sub-idR`, say that
`ids` is the left and right unit of the sequencing operator.
The `sub-assoc` equation says that sequencing is associative.
Finally, `sub-dist` says that post-sequencing distributes through cons.

## Relating the σ algebra and subsitution functions

The definitions of substitution `N [ M ]` and parallel subsitution
`subst σ N` depend on several auxiliary functions: `rename`, `exts`,
`ext`, and `subst-zero`. We shall relate those functions to terms in
the σ algebra.


To begin with, renaming can be expressed in terms of substitution.
We have

    rename ρ M ≡ ⧼ ren ρ ⧽ M               (rename-subst-ren)

where `ren` turns a renaming `ρ` into a substitution by post-composing
`ρ` with the identity substitution.

\begin{code}
ren : ∀{Γ Δ} → Rename Γ Δ → Subst Γ Δ
ren ρ = ids ∘ ρ
\end{code}

When the renaming is the increment function, then it is equivalent to
shift.

    ren S_ ≡ ↑                           (ren-shift)
    
    rename S_ M ≡ ⧼ ↑ ⧽ M                 (rename-shift)

Next we relate the `exts` function to the σ algebra.  Recall that the
`exts` function extends a substitution as follows:

    exts σ = ` Z, rename S_ (σ 0), rename S_ (σ 1), rename S_ (σ 2), ...

So `exts` is equivalent to cons'ing Z onto the sequence formed
by applying `σ` and then shifting.

    exts σ ≡ ` Z • (σ ⨟ ↑)                (exts-cons-shift)

The `ext` function does the same job as `exts` but for renamings
instead of substitutions. So composing `ext` with `ren` is the same as
composing `ren` with `exts`.

    ren (ext ρ) ≡ exts (ren ρ)            (ren-ext)

Thus, we can recast the `exts-cons-shift` equation in terms of
renamings.

    ren (ext ρ) ≡ ` Z • (ren ρ ⨟ ↑)       (ext-cons-Z-shift)

It is also useful to specialize the `sub-sub` equation of the σ
algebra to the situation where the first substitution is a renaming.

    ⧼ σ ⧽ (rename ρ M) ≡ ⧼ σ ∘ ρ ⧽ M       (rename-subst)

Finally, the `subst-zero M` substitution is equivalent to cons'ing
`M` onto the identity substitution.

    subst-zero M ≡ M • ids                (subst-Z-cons-ids)


## Proofs of sub-head, sub-tail, sub-η, Z-shift, sub-idL, sub-dist, and sub-app

We start with the proofs that are immediate from the definitions of
the operators.

\begin{code}
sub-head : ∀ {Γ Δ} {A} {M : Δ ⊢ A}{σ : Subst Γ Δ}
         → ⧼ M • σ ⧽ (` Z) ≡ M
sub-head = refl
\end{code}

\begin{code}
sub-tail : ∀{Γ Δ} {A B} {M : Δ ⊢ A} {σ : Subst Γ Δ}
         → (↑ ⨟ M • σ) {A = B} ≡ σ
sub-tail = extensionality λ x → refl
\end{code}

\begin{code}
sub-η : ∀{Γ Δ} {A B} {σ : Subst (Γ , A) Δ} 
      → (⧼ σ ⧽ (` Z) • (↑ ⨟ σ)) {A = B} ≡ σ
sub-η {Γ}{Δ}{A}{B}{σ} = extensionality λ x → lemma
   where 
   lemma : ∀ {x} → ((⧼ σ ⧽ (` Z)) • (↑ ⨟ σ)) x ≡ σ x
   lemma {x = Z} = refl
   lemma {x = S x} = refl
\end{code}

\begin{code}
Z-shift : ∀{Γ}{A B}
        → ((` Z) • ↑) ≡ ids {Γ , A} {B}
Z-shift {Γ}{A}{B} = extensionality lemma 
   where
   lemma : (x : Γ , A ∋ B) → ((` Z) • ↑) x ≡ ids x
   lemma Z = refl
   lemma (S y) = refl
\end{code}

\begin{code}
sub-idL : ∀{Γ Δ} {σ : Subst Γ Δ} {A}
       → ids ⨟ σ ≡ σ {A}
sub-idL = extensionality λ x → refl

{- todo: remove this and directly use sub-idL  -}
sub-idL-x : ∀{Γ Δ} {B} {σ : Subst Γ Δ} {x : Γ ∋ B}
       → (ids ⨟ σ) x ≡ σ x
sub-idL-x = refl
\end{code}

\begin{code}
sub-dist :  ∀{Γ Δ Σ : Context} {A B} {σ : Subst Γ Δ} {τ : Subst Δ Σ}
              {M : Δ ⊢ A} {x : Γ , A ∋ B}
         → ((M • σ) ⨟ τ) x ≡ ((subst τ M) • (σ ⨟ τ)) x
sub-dist {x = Z} = refl
sub-dist {x = S x} = refl
\end{code}

\begin{code}
sub-app : ∀{Γ Δ} {σ : Subst Γ Δ} {L : Γ ⊢ ★}{M : Γ ⊢ ★}
        → ⧼ σ ⧽ (L · M)  ≡ (⧼ σ ⧽ L) · (⧼ σ ⧽ M)
sub-app = refl        
\end{code}


## Interlude: congruences

In this section we establish congruence rules for the σ algebra
operators, in preparation for using them during equational
reasononing.

\begin{code}
cong-cons : ∀{Γ Δ}{A}{M N : Δ ⊢ A}{σ τ : Subst Γ Δ}
  → M ≡ N → (∀{A} → σ {A} ≡ τ {A})
  → ∀{A} → (M • σ) {A} ≡ (N • τ) {A}
cong-cons{Γ}{Δ}{A}{M}{N}{σ}{τ} refl st {A'} = extensionality lemma
  where
  lemma : (x : Γ , A ∋ A') → (M • σ) x ≡ (M • τ) x
  lemma Z = refl
  lemma (S x) = cong-app st x
\end{code}

\begin{code}
cons-congL : ∀{Γ Δ : Context} {A B} {σ : Subst Γ Δ} {M M' : Δ ⊢ A}
            {x : Γ , A ∋ B}
           → M ≡ M'
           → (M • σ) x ≡ (M' • σ) x
cons-congL{σ = σ}{x = x} s = cong (λ z → (z • σ) x) s

cons-congR : ∀{Γ Δ : Context} {A B} {σ τ : Subst Γ Δ} {M : Δ ⊢ A}
            {x : Γ , A ∋ B}
           → (∀{x : Γ ∋ B} → σ x ≡ τ x)
           → (M • σ) x ≡ (M • τ) x
cons-congR {x = Z} s = refl
cons-congR {x = S x} s = s
\end{code}

The following same-subst business is an ugly workaround :(

I'm having trouble with equalities involving the subst function.

\begin{code}
same-subst : ∀{Γ Δ} → Subst Γ Δ → Subst Γ Δ → Set
same-subst{Γ}{Δ} σ σ' = ∀{A}{x : Γ ∋ A} → σ x ≡ σ' x

same-subst-ext : ∀{Γ Δ}{σ σ' : Subst Γ Δ}{B}
   → same-subst σ σ'
   → same-subst (exts σ {B = B}) (exts σ' )
same-subst-ext ss {x = Z} = refl
same-subst-ext ss {x = S x} = cong (rename (λ {A} → S_)) ss

cong-sub : ∀{Γ Δ}{σ σ' : Subst Γ Δ}{A}{M M' : Γ ⊢ A}
            → same-subst σ σ' → M ≡ M'
            → subst σ M ≡ subst σ' M'
cong-sub {Γ} {Δ} {σ} {σ'} {A} {` x} ss refl = ss
cong-sub {Γ} {Δ} {σ} {σ'} {A} {ƛ M} ss refl =
   let ih = cong-sub {Γ = Γ , ★} {Δ = Δ , ★}
            {σ = exts σ}{σ' = exts σ'} {M = M}
            (λ {x}{A} → same-subst-ext {Γ}{Δ}{σ}{σ'} ss {x}{A}) refl in
   cong ƛ_ ih
cong-sub {Γ} {Δ} {σ} {σ'} {A} {L · M} ss refl = 
   let ih1 = cong-sub {Γ} {Δ} {σ} {σ'} {A} {L} ss refl in
   let ih2 = cong-sub {Γ} {Δ} {σ} {σ'} {A} {M} ss refl in
   cong₂ _·_ ih1 ih2

subst-equal : ∀{Γ Δ}{σ σ' : Subst Γ Δ}{A}{M : Γ ⊢ A}
            → same-subst σ σ' 
            → subst σ M ≡ subst σ' M
subst-equal{M = M} ss = cong-sub{M = M} ss refl

subst-equal2 : ∀{Γ Δ}{σ σ' : Subst Γ Δ}{A}{M : Γ ⊢ A}
            → (∀{A} → σ {A} ≡ σ' {A})
            → subst σ M ≡ subst σ' M
subst-equal2{Γ}{Δ}{σ}{σ'}{A}{M} s =
   subst-equal{M = M} λ {A}{x} → cong-app {f = σ {A}} {g = σ' {A}} (s{A}) x
\end{code}


\begin{code}
same-rename : ∀{Γ Δ} → Rename Γ Δ → Rename Γ Δ → Set
same-rename{Γ}{Δ} σ σ' = ∀{A}{x : Γ ∋ A} → σ x ≡ σ' x

same-rename-ext : ∀{Γ Δ}{σ σ' : Rename Γ Δ}
   → same-rename σ σ'
   → same-rename (ext σ {B = ★}) (ext σ' )
same-rename-ext ss {x = Z} = refl
same-rename-ext ss {x = S x} = cong S_ ss

rename-equal : ∀{Γ Δ}{ρ ρ' : Rename Γ Δ}{M : Γ ⊢ ★}
        → same-rename ρ ρ'
        → rename ρ M ≡ rename ρ' M
rename-equal {M = ` x} s = cong `_ s
rename-equal {ρ = ρ} {ρ' = ρ'} {M = ƛ N} s =
   cong ƛ_ (rename-equal {ρ = ext ρ}{ρ' = ext ρ'}{M = N} (same-rename-ext s))
rename-equal {M = L · M} s = cong₂ _·_ (rename-equal s) (rename-equal s)
\end{code}


\begin{code}
cong-seq : ∀{Γ Δ Σ}{σ σ' : Subst Γ Δ}{τ τ' : Subst Δ Σ}
  → (∀{A} → σ {A} ≡ σ' {A}) → (∀{A} → τ {A} ≡ τ' {A})
  → ∀{A} → (σ ⨟ τ) {A} ≡ (σ' ⨟ τ') {A}
cong-seq {Γ}{Δ}{Σ}{σ}{σ'}{τ}{τ'} ss' tt' {A} = extensionality lemma
  where
  lemma : (x : Γ ∋ A) → (σ ⨟ τ) x ≡ (σ' ⨟ τ') x
  lemma x =
     begin
       (σ ⨟ τ) x 
     ≡⟨⟩
       subst τ (σ x)
     ≡⟨ cong (subst τ) (cong-app ss' x) ⟩
       subst τ (σ' x)
     ≡⟨ subst-equal2{M = σ' x} tt' ⟩
       subst τ' (σ' x)
     ≡⟨⟩
       (σ' ⨟ τ') x  
     ∎
\end{code}

\begin{code}
cong-seqL : ∀{Γ Δ Σ : Context} {B} {σ σ' : Subst Γ Δ} {τ : Subst Δ Σ}
            {x : Γ ∋ B}
          → (∀{x : Γ ∋ B} → σ x ≡ σ' x)
          → (σ ⨟ τ) x ≡ (σ' ⨟ τ) x
cong-seqL {τ = τ}{x = x} s = cong (subst τ) s
\end{code}

\begin{code}
cong-seqR : ∀{Γ Δ Σ : Context} {B} {σ : Subst Γ Δ} {τ τ' : Subst Δ Σ}
            {x : Γ ∋ B}
          → (∀{A}{x : Δ ∋ A} → τ x ≡ τ' x)
          → (σ ⨟ τ) x ≡ (σ ⨟ τ') x
cong-seqR {Γ}{Δ}{Σ}{B}{σ}{τ}{τ'}{x} tt' =
  cong-app (cong-seq {σ = σ}
                     (λ {A} → refl)
                     (λ{A} → extensionality λ x → tt'{A}{x}))
           x
\end{code}


\begin{code}
cong-subst-zero : ∀{Γ}{A B : Type}{M M' : Γ ⊢ B}{x : Γ , B ∋ A}
  → M ≡ M'
  → subst-zero M x ≡ subst-zero M' x
cong-subst-zero {x = x} mm' = cong (λ z → subst-zero z x) mm'
\end{code}


## Relating `rename`, `exts`, `ext`, and `subst-zero` to the σ algebra

In this section we prove the equations that relate the functions
involved with defining substution (`rename`, `exts`, `ext`, and
`subst-zero`) to terms in the σ algebra.

The first equation we shall prove is

    rename ρ M ≡ ⧼ ren ρ ⧽ M              (rename-subst-ren)
               
Because `subst` uses the `exts` function, we need the following lemma
which says that `exts` and `ext` do the same thing except that `ext`
works on renamings and `exts` works on substitutions.

\begin{code}
ren-ext-x : ∀ {Γ Δ}{B C : Type} {ρ : Rename Γ Δ} {x : Γ , B ∋ C}
        → (ren (ext ρ)) x ≡ exts (ren ρ) x
ren-ext-x {x = Z} = refl
ren-ext-x {x = S x} = refl

ren-ext : ∀ {Γ Δ}{B C : Type} {ρ : Rename Γ Δ} {x : Γ , B ∋ C}
        → ren (ext ρ {B = B}) ≡ exts (ren ρ) {C}
ren-ext = extensionality λ x → ren-ext-x {x = x}
\end{code}

With this lemma in hand, the proof is a straightforward induction on
the term `M`.

\begin{code}
rename-subst-ren : ∀ {Γ Δ}{A} {ρ : Rename Γ Δ}{M : Γ ⊢ A}
                 → rename ρ M ≡ ⧼ ren ρ ⧽ M
rename-subst-ren {M = ` x} = refl
rename-subst-ren {ρ = ρ}{M = ƛ N} =
  begin
      rename ρ (ƛ N)
    ≡⟨⟩
      ƛ rename (ext ρ) N
    ≡⟨ cong ƛ_ (rename-subst-ren {ρ = ext ρ}{M = N}) ⟩
      ƛ ⧼ ren (ext ρ) ⧽ N
    ≡⟨ cong ƛ_ (subst-equal {M = N} ren-ext-x) ⟩
      ƛ ⧼ exts (ren ρ) ⧽  N
    ≡⟨⟩
      ⧼ ren ρ ⧽ (ƛ N)
  ∎
rename-subst-ren {M = L · M} = cong₂ _·_ rename-subst-ren rename-subst-ren
\end{code}

The substitution `ren S_` is equivalent to `↑`.

\begin{code}
ren-shift : ∀{Γ}{A}{B} {x : Γ ∋ A}
          → ren (S_{B = B}) x ≡ ↑ {A = B} x
ren-shift {x = Z} = refl
ren-shift {x = S x} = refl
\end{code}

The substitution `rename S_` is equivalent to shifting: `⧼ ↑ ⧽`.

\begin{code}
rename-shift : ∀{Γ} {A} {B} {M : Γ ⊢ A}
             → rename (S_{B = B}) M ≡ ⧼ ↑ ⧽ M
rename-shift{Γ}{A}{B}{M} =
  begin
    rename S_ M
  ≡⟨ rename-subst-ren ⟩
    ⧼ ren S_ ⧽ M
  ≡⟨ subst-equal{M = M} ren-shift ⟩
    ⧼ ↑ ⧽ M
  ∎
\end{code}

Next we prove the equation `exts-cons-shift`, which states that `exts`
is equivalent to cons'ing Z onto the sequence formed by applying `σ`
and then shifting. The proof is by case analysis on the variable `x`,
using `rename-subst-ren` for when `x = S y`.

\begin{code}
exts-cons-shift-x : ∀{Γ Δ} {A B} {σ : Subst Γ Δ} {x : Γ , B ∋ A}
                → exts σ x ≡ (` Z • (σ ⨟ ↑)) x
exts-cons-shift-x {x = Z} = refl
exts-cons-shift-x {x = S y} = rename-subst-ren

exts-cons-shift : ∀{Γ Δ} {A B} {σ : Subst Γ Δ}
                → exts σ {A} {B} ≡ (` Z • (σ ⨟ ↑))
exts-cons-shift = extensionality λ x → exts-cons-shift-x{x = x}
\end{code}

As a corollary, we have a similar correspondence for `ren (ext ρ)`.

\begin{code}
ext-cons-Z-shift : ∀{Γ Δ} {ρ : Rename Γ Δ}{A}{B} 
                 → ren (ext ρ {B = B}) ≡ (` Z • (ren ρ ⨟ ↑)) {A}
ext-cons-Z-shift {Γ}{Δ}{ρ}{A}{B} =
  extensionality λ x → 
  begin
    ren (ext ρ) x
  ≡⟨ ren-ext-x ⟩
    exts (ren ρ) x
  ≡⟨ exts-cons-shift-x{σ = ren ρ}{x = x} ⟩
   ((` Z) • (ren ρ ⨟ ↑)) x
  ∎
\end{code}

Finally, the `subst-zero M` substitution is equivalent to cons'ing `M`
onto the identity substitution.

\begin{code}
subst-Z-cons-ids-x : ∀{Γ}{A B : Type}{M : Γ ⊢ B}{x : Γ , B ∋ A}
                    → subst-zero M x ≡ (M • ids) x
subst-Z-cons-ids-x {x = Z} = refl
subst-Z-cons-ids-x {x = S x} = refl

subst-Z-cons-ids : ∀{Γ}{A B : Type}{M : Γ ⊢ B}
                 → subst-zero M ≡ (M • ids) {A}
subst-Z-cons-ids = extensionality λ x → subst-Z-cons-ids-x {x = x}
\end{code}


## Proofs of sub-abs and sub-id

The equation `sub-abs` follows immediately from the equation
`exts-cons-shift`.

\begin{code}
sub-abs : ∀{Γ Δ} {σ : Subst Γ Δ} {N : Γ , ★ ⊢ ★}
        → ⧼ σ ⧽ (ƛ N) ≡ ƛ ⧼ (` Z) • (σ ⨟ ↑) ⧽ N
sub-abs {σ = σ}{N = N} =
   begin
     ⧼ σ ⧽ (ƛ N)
   ≡⟨⟩
     ƛ ⧼ exts σ ⧽ N
   ≡⟨ cong ƛ_ (subst-equal2{M = N} exts-cons-shift) ⟩
     ƛ ⧼ (` Z) • (σ ⨟ ↑) ⧽ N
   ∎
\end{code}

The proof of `sub-id` requires the following lemma which says that
extending the identity substitution produces the identity
substitution.

\begin{code}
exts-ids : ∀{Γ}{A B}
         → exts ids ≡ ids {Γ , B} {A}
exts-ids {Γ}{A}{B} = extensionality lemma
  where lemma : (x : Γ , B ∋ A) → exts ids x ≡ ids x
        lemma Z = refl
        lemma (S x) = refl
\end{code}

The proof of `⧼ ids ⧽ M ≡ M` now follows easily by induction on `M`,
using `exts-ids` in the case for `M ≡ ƛ N`.

\begin{code}
sub-id : ∀{Γ} {A} {M : Γ ⊢ A}
         → ⧼ ids ⧽ M ≡ M
sub-id {M = ` x} = refl
sub-id {M = ƛ N} = 
   begin
     ⧼ ids ⧽ (ƛ N)
   ≡⟨⟩
     ƛ ⧼ exts ids ⧽ N
   ≡⟨ cong ƛ_ (subst-equal2{M = N} exts-ids)  ⟩
     ƛ ⧼ ids ⧽ N
   ≡⟨ cong ƛ_ sub-id ⟩
     ƛ N
   ∎
sub-id {M = L · M} = cong₂ _·_ sub-id sub-id
\end{code}


## Proof of sub-idR

The proof of `sub-idR` follows directly from `sub-id`.

\begin{code}
sub-idR : ∀{Γ Δ} {σ : Subst Γ Δ} {A}
       → (σ ⨟ ids) ≡ σ {A}
sub-idR {Γ}{σ = σ}{A} =
          begin
            σ ⨟ ids
          ≡⟨⟩
            (subst ids) ∘ σ
          ≡⟨ extensionality (λ x → sub-id) ⟩
            σ
          ∎

{- todo: remove this and use sub-idR dirctly. -}
sub-idR-x : ∀{Γ Δ} {B} {σ : Subst Γ Δ} {x : Γ ∋ B}
       → (σ ⨟ ids) x ≡ σ x
sub-idR-x {Γ}{σ = σ}{x = x} = cong-app (sub-idR{σ = σ}) x
\end{code}


## Proof of sub-sub

The `sub-sub` equation states that sequenced substitutions `σ ⨟ τ`
are equivalent to first applying `σ` then applying `τ`.

    ⧼ τ ⧽ ⧼ σ ⧽ M  ≡ ⧼ σ ⨟ τ ⧽ M

The proof requires several lemmas. First, we need to prove the
specialization for renaming.

    rename ρ (rename ρ' M) ≡ rename (ρ ∘ ρ') M

This in turn requires the following lemma about `ext`.

\begin{code}
compose-ext : ∀{Γ Δ Σ}{ρ : Rename Δ Σ} {ρ' : Rename Γ Δ} {A B} {x : Γ , B ∋ A}
            → ((ext ρ) ∘ (ext ρ')) x ≡ ext (ρ ∘ ρ') x
compose-ext {x = Z} = refl
compose-ext {x = S x} = refl
\end{code}

To prove that composing renamings is equivalent to appying one after
the other using `rename`, we proceed by induction on the term `M`,
using the `compose-ext` lemma in the case for `M ≡ ƛ N`.

\begin{code}
compose-rename : ∀{Γ Δ Σ}{A}{M : Γ ⊢ A}{ρ : Rename Δ Σ}{ρ' : Rename Γ Δ} 
  → rename ρ (rename ρ' M) ≡ rename (ρ ∘ ρ') M
compose-rename {M = ` x} = refl
compose-rename {Γ}{Δ}{Σ}{A}{ƛ N}{ρ}{ρ'} = cong ƛ_ G
  where
  G : rename (ext ρ) (rename (ext ρ') N) ≡ rename (ext (ρ ∘ ρ')) N
  G =
      begin
        rename (ext ρ) (rename (ext ρ') N)
      ≡⟨ compose-rename{ρ = ext ρ}{ρ' = ext ρ'} ⟩
        rename ((ext ρ) ∘ (ext ρ')) N
      ≡⟨ rename-equal compose-ext ⟩
        rename (ext (ρ ∘ ρ')) N
      ∎        
compose-rename {M = L · M} = cong₂ _·_ compose-rename compose-rename
\end{code}

The next lemma states that if a renaming and subtitution commute on
variables, then they also commute on terms. We explain the proof in
detail below.

\begin{code}
commute-subst-rename : ∀{Γ Δ}{M : Γ ⊢ ★}{σ : Subst Γ Δ}
                        {ρ : ∀{Γ} → Rename Γ (Γ , ★)}
     → (∀{x : Γ ∋ ★} → exts σ {B = ★} (ρ x) ≡ rename ρ (σ x))
     → subst (exts σ {B = ★}) (rename ρ M) ≡ rename ρ (subst σ M)
commute-subst-rename {M = ` x} r = r
commute-subst-rename{Γ}{Δ}{ƛ N}{σ}{ρ} r =
   cong ƛ_ (commute-subst-rename{Γ , ★}{Δ , ★}{N}
               {exts σ}{ρ = ρ'} (λ {x} → H {x}))
   where
   ρ' : ∀ {Γ} → Rename Γ (Γ , ★)
   ρ' {∅} = λ ()
   ρ' {Γ , ★} = ext ρ

   H : {x : Γ , ★ ∋ ★} → exts (exts σ) (ext ρ x) ≡ rename (ext ρ) (exts σ x)
   H {Z} = refl
   H {S y} =
     begin
       exts (exts σ) (ext ρ (S y))
     ≡⟨⟩
       rename S_ (exts σ (ρ y)) 
     ≡⟨ cong (rename S_) r ⟩
       rename S_ (rename ρ (σ y))
     ≡⟨ compose-rename ⟩
       rename (S_ ∘ ρ) (σ y)
     ≡⟨ rename-equal (λ {A} {x₁} → refl) ⟩
       rename ((ext ρ) ∘ S_) (σ y)
     ≡⟨ sym compose-rename ⟩
       rename (ext ρ) (rename S_ (σ y))
     ≡⟨⟩
       rename (ext ρ) (exts σ (S y))
     ∎
commute-subst-rename {M = L · M}{ρ = ρ} r =
   cong₂ _·_ (commute-subst-rename{M = L}{ρ = ρ} r)
             (commute-subst-rename{M = M}{ρ = ρ} r)
\end{code}

The proof is by induction on the term `M`.

* If `M` is a variable, then we use the premise to conclude.

* If `M ≡ ƛ N`, we conclude using the induction hypothesis for
  `N`. However, to use the induction hypothesis, we must show
  that

        exts (exts σ) (ext ρ x) ≡ rename (ext ρ) (exts σ x)

  We prove this equation by cases on x.

    * If `x = Z`, the two sides are equal by definition.

    * If `x = S y`, we obtain the goal by the following equational reasoning.

          exts (exts σ) (ext ρ (S y))
        ≡ rename S_ (exts σ (ρ y)) 
        ≡ rename S_ (rename S_ (σ (ρ y)      (by the premise)
        ≡ rename (ext ρ) (exts σ (S y))      (by compose-rename)
        ≡ rename ((ext ρ) ∘ S_) (σ y)
        ≡ rename (ext ρ) (rename S_ (σ y))   (by compose-rename)
        ≡ rename (ext ρ) (exts σ (S y))

* If `M` is an application, we obtain the goal using the induction
  hypothesis for each subterm.


The last lemma needed to prove `sub-sub` states that the `exts`
function distributes with sequencing. It is a corollary of
`commute-subst-rename`. We describe the proof below.

\begin{code}
subst-exts : ∀{Γ Δ Δ'}{A}{x : Γ , ★ ∋ A} {σ₁ : Subst Γ Δ}{σ₂ : Subst Δ Δ'}
   → (exts σ₁ ⨟ exts σ₂) x ≡ exts (σ₁ ⨟ σ₂) x
subst-exts {x = Z} = refl
subst-exts {A = ★}{x = S x}{σ₁}{σ₂} =
   begin
     (exts σ₁ ⨟ exts σ₂) (S x)
   ≡⟨⟩
     subst (exts σ₂) (rename S_ (σ₁ x))
   ≡⟨ commute-subst-rename{M = σ₁ x}{σ = σ₂}{ρ = S_} (λ {x₁} → refl) ⟩
     rename S_ (subst σ₂ (σ₁ x))
   ≡⟨⟩
     rename S_ ((σ₁ ⨟ σ₂) x)
   ∎
\end{code}

The proof proceed by cases on `x`.

* If `x = Z`, the two sides are equal by the definition of `exts`
  and sequencing.

* If `x = S x`, we unfold the first use of `exts` and sequencing, then
  apply the lemma `commute-subst-rename`. We conclude by the
  definition of sequencing.


Now we come to the proof of `sub-sub`, which we explain below.

\begin{code}
sub-sub : ∀{Γ Δ Σ}{A}{M : Γ ⊢ A} {σ₁ : Subst Γ Δ}{σ₂ : Subst Δ Σ} 
            → ⧼ σ₂ ⧽ (⧼ σ₁ ⧽ M) ≡ ⧼ σ₁ ⨟ σ₂ ⧽ M
sub-sub {M = ` x} = refl
sub-sub {Γ}{Δ}{Σ}{A}{ƛ N}{σ₁}{σ₂} =
   begin
     ⧼ σ₂ ⧽ (⧼ σ₁ ⧽ (ƛ N))
   ≡⟨⟩
     ƛ ⧼ exts σ₂ ⧽ (⧼ exts σ₁ ⧽ N)
   ≡⟨ cong ƛ_ (sub-sub{M = N}{σ₁ = exts σ₁}{σ₂ = exts σ₂}) ⟩
     ƛ ⧼ exts σ₁ ⨟ exts σ₂ ⧽ N
   ≡⟨ cong ƛ_ (subst-equal{M = N} (λ {A}{x} → subst-exts{x = x})) ⟩
     ƛ ⧼ exts ( σ₁ ⨟ σ₂) ⧽ N
   ∎
sub-sub {M = L · M} = cong₂ _·_ (sub-sub{M = L}) (sub-sub{M = M})
\end{code}

We proceed by induction on the term `M`.

* If `M = x`, then both sides are equal to `σ₂ (σ₁ x)`.

* If `M = ƛ N`, we first use the induction hypothesis to show that 

     ƛ ⧼ exts σ₂ ⧽ (⧼ exts σ₁ ⧽ N) ≡ ƛ ⧼ exts σ₁ ⨟ exts σ₂ ⧽ N

  and then use the lemma `subst-exts` to show

    ƛ ⧼ exts σ₁ ⨟ exts σ₂ ⧽ N ≡ ƛ ⧼ exts ( σ₁ ⨟ σ₂) ⧽ N

* If `M` is an application, we use the induction hypothesis
  for both subterms.


The following corollary of `sub-sub` specializes the first
substitution to a renaming.

\begin{code}
rename-subst : ∀{Γ Δ Δ'}{M : Γ ⊢ ★}{ρ : Rename Γ Δ}{σ : Subst Δ Δ'}
             → ⧼ σ ⧽ (rename ρ M) ≡ ⧼ σ ∘ ρ ⧽ M
rename-subst {Γ}{Δ}{Δ'}{M}{ρ}{σ} =
   begin
     ⧼ σ ⧽ (rename ρ M)
   ≡⟨ cong ⧼ σ ⧽ (rename-subst-ren{M = M}) ⟩
     ⧼ σ ⧽ (⧼ ren ρ ⧽ M)
   ≡⟨ sub-sub{M = M} ⟩
     ⧼ ren ρ ⨟ σ ⧽ M
   ≡⟨⟩
     ⧼ σ ∘ ρ ⧽ M
   ∎
\end{code}


## Proof of seq-assoc

The proof of `seq-assoc` follows directly from `sub-sub` and the
definition of sequencing.

\begin{code}
seq-assoc : ∀{Γ Δ Σ Ψ : Context}{B} {σ : Subst Γ Δ} {τ : Subst Δ Σ}
             {θ : Subst Σ Ψ} {x : Γ ∋ B}
          → ((σ ⨟ τ) ⨟ θ) x ≡ (σ ⨟ τ ⨟ θ) x
seq-assoc{Γ}{Δ}{Σ}{Ψ}{B}{σ}{τ}{θ}{x} =
    begin
      ((σ ⨟ τ) ⨟ θ) x
    ≡⟨⟩
      ⧼ θ ⧽ (⧼ τ ⧽ (σ x))
    ≡⟨ sub-sub{M = σ x} ⟩
      ⧼ τ ⨟ θ ⧽ (σ x)
    ≡⟨⟩
      (σ ⨟ τ ⨟ θ) x
    ∎
\end{code}


## Proof of the substitution lemma

We first prove the generalized form of the substitution lemma, showing
that a substitution `σ` commutes with the subusitution of `M` into
`N`.

    ⧼ exts σ ⧽ N [ ⧼ σ ⧽ M ] ≡ ⧼ σ ⧽ (N [ M ])

This proof is where the σ algebra pays off.  The proof is by direct
equational reasoning. Starting with the left-hand side, we apply σ
algebra equations, oriented left-to-right, until we arive at the
normal form

    ⧼ ⧼ σ ⧽ M • σ ⧽ N

We then do the same with the right-hand side, arriving at the same
normal form. 

\begin{code}
subst-commute : ∀{Γ Δ}{N : Γ , ★ ⊢ ★}{M : Γ ⊢ ★}{σ : Subst Γ Δ }
    → ⧼ exts σ ⧽ N [ ⧼ σ ⧽ M ] ≡ ⧼ σ ⧽ (N [ M ])
subst-commute {Γ}{Δ}{N}{M}{σ} =
     begin
       ⧼ exts σ ⧽ N [ ⧼ σ ⧽ M ]
     ≡⟨⟩
       ⧼ subst-zero (⧼ σ ⧽ M) ⧽ (⧼ exts σ ⧽ N)
     ≡⟨ subst-equal{M = ⧼ exts σ ⧽ N}
          (λ {A}{x} → subst-Z-cons-ids-x{A = A}{x = x}) ⟩
       ⧼ ⧼ σ ⧽ M • ids ⧽ (⧼ exts σ ⧽ N)
     ≡⟨ sub-sub{M = N} ⟩
       ⧼ (exts σ) ⨟ ((⧼ σ ⧽ M) • ids) ⧽ N
     ≡⟨ subst-equal{M = N}
         (λ {A}{x} → cong-seqL{σ = exts σ}{σ' = ((` Z) • (σ ⨟ ↑))}
            {x = x} (λ {x} → exts-cons-shift-x{x = x}) ) ⟩
       ⧼ (` Z • (σ ⨟ ↑)) ⨟ (⧼ σ ⧽ M • ids) ⧽ N
     ≡⟨ subst-equal{M = N} (λ {A}{x} → sub-dist{M = ` Z}{x = x}) ⟩
       ⧼ ⧼ ⧼ σ ⧽ M • ids ⧽ (` Z) • ((σ ⨟ ↑) ⨟ (⧼ σ ⧽ M • ids)) ⧽ N
     ≡⟨⟩
       ⧼ ⧼ σ ⧽ M • ((σ ⨟ ↑) ⨟ (⧼ σ ⧽ M • ids)) ⧽ N
     ≡⟨ subst-equal{M = N} (λ {A} {x} → cons-congR {x = x}
                                        λ {x} → seq-assoc{σ = σ}) ⟩
       ⧼ ⧼ σ ⧽ M • (σ ⨟ ↑ ⨟ ⧼ σ ⧽ M • ids) ⧽ N
     ≡⟨ (subst-equal{M = N} λ {A} {x} → cons-congR {x = x}
                              λ {x} → cong-seqR {σ = σ} λ {A}{x} → refl) ⟩
       ⧼ ⧼ σ ⧽ M • (σ ⨟ ids) ⧽ N
     ≡⟨ (subst-equal{M = N} λ {A} {x} → cons-congR{x = x} (sub-idR-x{σ = σ})) ⟩
       ⧼ ⧼ σ ⧽ M • σ ⧽ N
     ≡⟨ subst-equal{M = N} (λ {A}{x} → cons-congR{x = x} (sub-idL-x{σ = σ})) ⟩
       ⧼ ⧼ σ ⧽ M • (ids ⨟ σ) ⧽ N
     ≡⟨ (subst-equal{M = N} λ {A}{x} → sym (sub-dist{x = x})) ⟩
       ⧼ M • ids ⨟ σ ⧽ N
     ≡⟨ sym (sub-sub{M = N}) ⟩
       ⧼ σ ⧽ (⧼ M • ids ⧽ N)
     ≡⟨ cong ⧼ σ ⧽ (sym (subst-equal{M = N}λ{A}{x} → subst-Z-cons-ids-x{x = x})) ⟩
       ⧼ σ ⧽ (N [ M ])
     ∎
\end{code}

A corollary of `subst-commute` is that `rename` also commutes with
substitution. In the proof below, we first exchange `rename ρ` for
the substitution `⧼ ren ρ ⧽`, and apply `subst-commute`, and
then convert back to `rename ρ`.

\begin{code}
rename-subst-commute : ∀{Γ Δ}{N : Γ , ★ ⊢ ★}{M : Γ ⊢ ★}{ρ : Rename Γ Δ }
    → (rename (ext ρ) N) [ rename ρ M ] ≡ rename ρ (N [ M ])
rename-subst-commute {Γ}{Δ}{N}{M}{ρ} =
     begin
       (rename (ext ρ) N) [ rename ρ M ]
     ≡⟨ cong-sub (λ{A}{x} → cong-subst-zero (rename-subst-ren{M = M}))
                 (rename-subst-ren{M = N}) ⟩
       (⧼ ren (ext ρ) ⧽ N) [ ⧼ ren ρ ⧽ M ]
     ≡⟨ cong-sub ((λ {A}{x} → refl)) (subst-equal{M = N} ren-ext-x) ⟩
       (⧼ exts (ren ρ) ⧽ N) [ ⧼ ren ρ ⧽ M ]
     ≡⟨ subst-commute{N = N} ⟩
       subst (ren ρ) (N [ M ])
     ≡⟨ sym (rename-subst-ren) ⟩
       rename ρ (N [ M ])
     ∎
\end{code}

To present the substitution lemma, we introduce the following notation
for substituting a term `M` for index 1 within term `N`.

\begin{code}
_〔_〕 : ∀ {Γ A B C}
        → Γ , B , C ⊢ A
        → Γ ⊢ B
          ---------
        → Γ , C ⊢ A
_〔_〕 {Γ} {A} {B} {C} N M =
   subst {Γ , B , C} {Γ , C} (exts (subst-zero M)) {A} N
\end{code}

The substitution lemma is stated as follows and proved as a corollary
of the `subst-commute` lemma.

\begin{code}
substitution : ∀{Γ}{M : Γ , ★ , ★ ⊢ ★}{N : Γ , ★ ⊢ ★}{L : Γ ⊢ ★}
    → (M [ N ]) [ L ] ≡ (M 〔 L 〕) [ (N [ L ]) ]
substitution{M = M}{N = N}{L = L} =
   sym (subst-commute{N = M}{M = N}{σ = subst-zero L})
\end{code}


## Notes

Most of the properties and proofs in this file are based on the paper
_Autosubst: Reasoning with de Bruijn Terms and Parallel Substitution_
by Schafer, Tebbi, and Smolka (ITP 2015). That paper, in turn, is
based on the paper of Abadi, Cardelli, Curien, and Levy (1991) that
defines the σ algebra.

