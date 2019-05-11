\begin{code}
module extra.Substitution where
\end{code}

## Imports

\begin{code}
open import plfa.Untyped
  using (Type; Context; _⊢_; ★; _∋_; ∅; _,_; Z; S_; `_; ƛ_; _·_; rename; subst;
         ext; exts; _[_]; subst-zero)
open import plfa.Denotational using (Rename; extensionality)
open import plfa.Soundness using (Subst)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Function using (_∘_)
open import Agda.Primitive using (lzero)
\end{code}

## Overview 

The primary purpose of this chapter is to prove that substitution
commutes with itself. Barendgredt (1984) refers to this
as the substitution lemma:
  
    M[x:=N][y:=L] = M [y:=L] [x:= N[y:=L] ]

In our setting, with de Bruijn indices for variables, the statement of
the lemma becomes:

    M [ N ] [ L ] ≡  M〔 L 〕[ N [ L ] ]

where the notation M 〔 L 〕 is for subsituting L for index 1 inside M.
In addition, because we define substitution in terms of parallel substitution,
we have the following generalization, replacing the substitution
of L with an arbitrary parallel substitution σ.

    subst σ (M [ N ]) ≡ (subst (exts σ) M) [ subst σ N ]

The special case for renamings is also useful.

    rename ρ (M [ N ]) ≡ (rename (ext ρ) M) [ rename ρ N ]


The secondary purpose of this chapter is to define the σ algebra of
parallel substitution due to Abadi, Cardelli, Curien, and Levy
(1991). The equations not only help us prove the substitution lemma,
but they are generally useful. Futhermore, when the equations are
applied from left to right, they form a rewrite system that _decides_
whether any two substitutions are equal.

We use the following more-succinct notation the `subst` function.

\begin{code}
⧼_⧽ : ∀{Γ Δ A} → Subst Γ Δ → Γ ⊢ A → Δ ⊢ A
⧼ σ ⧽ = λ M → subst σ M
\end{code}

## The σ Algebra of Substitution

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

## The Equations

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


## Useful corollaries of the equations


    (subst-subst)    ((subst σ₂) ∘ (subst σ₁)) M ≡ subst (subst σ₂ ∘ σ₁) M

    (rename-subst)   ((subst σ) ∘ (rename ρ)) M ≡ subst (σ ∘ ρ) M


equations about ren, etc?

    ren ρ = ids ∘ ρ

    rename ρ M ≡ ⧼ ren ρ ⧽ M

    exts σ ≡ (` Z) • (σ ⨟ ↑)

    ren (ext ρ) x ≡ cons (` Z) (ren ρ ⨟ ↑) x


## Proofs of sub-head, sub-tail, sub-η, Z-shift, sub-idL, sub-dist, and sub-app

The proofs of these equations are all immediate from the definitions
of the operators.

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
Z-shift : ∀{Γ}{A B}{x : Γ , A ∋ B}
        → ((` Z) • ↑) x ≡ ids x
Z-shift {x = Z} = refl
Z-shift {x = S x} = refl
\end{code}

\begin{code}
sub-idL : ∀{Γ Δ} {σ : Subst Γ Δ} {A}
       → ids ⨟ σ ≡ σ {A}
sub-idL = extensionality λ x → refl

{- old version -}
id-seq : ∀{Γ Δ} {B} {σ : Subst Γ Δ} {x : Γ ∋ B}
       → (ids ⨟ σ) x ≡ σ x
id-seq = refl
\end{code}

\begin{code}
sub-dist :  ∀{Γ Δ Σ : Context} {A B} {σ : Subst Γ Δ} {τ : Subst Δ Σ}
              {M : Δ ⊢ A} {x : Γ , A ∋ B}
         → ((M • σ) ⨟ τ) x ≡ ((subst τ M) • (σ ⨟ τ)) x
sub-dist {x = Z} = refl
sub-dist {x = S x} = refl
\end{code}


The equation `sub-app` is immediate from the definition of
substitution.

\begin{code}
sub-app : ∀{Γ Δ} {σ : Subst Γ Δ} {L : Γ ⊢ ★}{M : Γ ⊢ ★}
        → ⧼ σ ⧽ (L · M)  ≡ (⧼ σ ⧽ L) · (⧼ σ ⧽ M)
sub-app = refl        
\end{code}


## Interlude: congruences

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

This is an ugly workaround :(

I'm having trouble with equalities involving the subst function.

\begin{code}
same-subst : ∀{Γ Δ} → Subst Γ Δ → Subst Γ Δ → Set
same-subst{Γ}{Δ} σ σ' = ∀{A}{x : Γ ∋ A} → σ x ≡ σ' x

same-subst-ext : ∀{Γ Δ}{σ σ' : Subst Γ Δ}{B}
   → same-subst σ σ'
   → same-subst (exts σ {B = B}) (exts σ' )
same-subst-ext ss {x = Z} = refl
same-subst-ext ss {x = S x} = cong (rename (λ {A} → S_)) ss

subst-equal : ∀{Γ Δ}{σ σ' : Subst Γ Δ}{A}{M : Γ ⊢ A}
            → same-subst σ σ' 
            → subst σ M ≡ subst σ' M
subst-equal {Γ} {Δ} {σ} {σ'} {A} {` x} ss = ss
subst-equal {Γ} {Δ} {σ} {σ'} {A} {ƛ M} ss =
   let ih = subst-equal {Γ = Γ , ★} {Δ = Δ , ★}
            {σ = exts σ}{σ' = exts σ'} {M = M}
            (λ {x}{A} → same-subst-ext {Γ}{Δ}{σ}{σ'} ss {x}{A}) in
   cong ƛ_ ih
subst-equal {Γ} {Δ} {σ} {σ'} {A} {L · M} ss =
   let ih1 = subst-equal {Γ} {Δ} {σ} {σ'} {A} {L} ss in
   let ih2 = subst-equal {Γ} {Δ} {σ} {σ'} {A} {M} ss in
   cong₂ _·_ ih1 ih2

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




## Relating `rename`, `exts`, and `ext` to the σ algebra

To relate renamings to the σ algebra, we define the following function
`ren` that turns a renaming `ρ` into a substitution by post-composing
`ρ` with the identity substitutino.

\begin{code}
ren : ∀{Γ Δ} → Rename Γ Δ → Subst Γ Δ
ren ρ = ids ∘ ρ
\end{code}

We can now relate the `rename` function to the combination of
`ren` and `subst`. That is, we show that 

    rename ρ M ≡ ⧼ ren ρ ⧽ M
               
Because `subst` uses the `exts` function, we need the following lemma
which says that `exts` and `ext` do the same thing except that `ext`
works on renamings and `exts` works on substitutions.

\begin{code}
ren-ext : ∀ {Γ Δ}{B C : Type} {ρ : Rename Γ Δ} {x : Γ , B ∋ C}
        → (ren (ext ρ)) x ≡ exts (ren ρ) x
ren-ext {x = Z} = refl
ren-ext {x = S x} = refl
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
    ≡⟨ cong ƛ_ (subst-equal {M = N} ren-ext) ⟩
      ƛ ⧼ exts (ren ρ) ⧽  N
    ≡⟨⟩
      ⧼ ren ρ ⧽ (ƛ N)
  ∎
rename-subst-ren {M = L · M} = cong₂ _·_ rename-subst-ren rename-subst-ren
\end{code}

The substitution `ren S_` is equivalent to `↑`.

\begin{code}
ren-shift : ∀{Γ}{A}{B} {x : Γ ∋ A}
          → ren (S_{B = B}) x ≡ ↑ x
ren-shift {x = Z} = refl
ren-shift {x = S x} = refl
\end{code}

The substitution `rename S_` is equivalent to `⧼ ↑ ⧽`.

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

Next we relate the `exts` function to the σ algebra.  Recall that the
`exts` function extends a substitution as follows:

    exts σ = ` Z, rename S_ (σ 0), rename S_ (σ 1), rename S_ (σ 2), ...

So `exts` is equivalent to cons'ing Z onto the sequence formed
by applying `σ` and then shifting.

\begin{code}
exts-cons-shift : ∀{Γ Δ} {A B} {σ : Subst Γ Δ} {x : Γ , B ∋ A}
                → exts σ x ≡ (` Z • (σ ⨟ ↑)) x
exts-cons-shift {x = Z} = refl
exts-cons-shift {x = S x} = rename-subst-ren

exts-cons-shift2 : ∀{Γ Δ} {A B} {σ : Subst Γ Δ}
                → exts σ {A} {B} ≡ (` Z • (σ ⨟ ↑))
exts-cons-shift2 = extensionality λ x → exts-cons-shift{x = x}
\end{code}

As a corollary, we have a similar correspondence for `ren (ext ρ)`.

\begin{code}
ext-cons-Z-shift : ∀{Γ Δ} {ρ : Rename Γ Δ}{A}{B} {x : Γ , B ∋ A}
                 → ren (ext ρ) x ≡ ((` Z) • (ren ρ ⨟ ↑)) x
ext-cons-Z-shift {Γ}{Δ}{ρ}{A}{B}{x} = 
  begin
    ren (ext ρ) x
  ≡⟨ ren-ext ⟩
    exts (ren ρ) x
  ≡⟨ exts-cons-shift{σ = ren ρ}{x = x} ⟩
   ((` Z) • (ren ρ ⨟ ↑)) x
  ∎
\end{code}

\begin{code}
{- obsolete: because ext-cons-Z-shift -}
ren-ext-cons-shift : ∀ {Γ Δ}{B C : Type} {ρ : Rename Γ Δ} {x : Γ , B ∋ C}
  → ren (ext ρ) x ≡ ((` Z) • ((ren ρ) ⨟ (ren S_))) x
ren-ext-cons-shift{Γ}{Δ}{B}{C}{ρ}{x} =
   begin
       ren (ext ρ) x
     ≡⟨ ren-ext ⟩
       exts (ren ρ) x
     ≡⟨ exts-cons-shift{x = x} ⟩
       ((` Z) • ((ren ρ) ⨟ (ren S_))) x
   ∎
\end{code}

## Proofs of sub-id, sub-app, sub-abs


To prove `⧼ ids ⧽ M ≡ M`, we need the following lemma which says that
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
using the above lemma in the case for `M ≡ ƛ N`.

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


The equation `sub-abs` follows from the equation `exts-cons-shift2`.

\begin{code}
sub-abs : ∀{Γ Δ} {σ : Subst Γ Δ} {N : Γ , ★ ⊢ ★}
        → ⧼ σ ⧽ (ƛ N) ≡ ƛ ⧼ (` Z) • (σ ⨟ ↑) ⧽ N
sub-abs {σ = σ}{N = N} =
   begin
     ⧼ σ ⧽ (ƛ N)
   ≡⟨⟩
     ƛ ⧼ exts σ ⧽ N
   ≡⟨ cong ƛ_ (subst-equal2{M = N} exts-cons-shift2) ⟩
     ƛ ⧼ (` Z) • (σ ⨟ ↑) ⧽ N
   ∎
\end{code}


## Proof of sub-idR


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

{- obsolete -}
seq-id : ∀{Γ Δ} {B} {σ : Subst Γ Δ} {x : Γ ∋ B}
       → (σ ⨟ ids) x ≡ σ x
seq-id {Γ}{σ = σ}{x = x} = cong-app (sub-idR{σ = σ}) x
\end{code}


## Proof of sub-sub

The `sub-sub` equation states that sequenced substitutions `σ ⨟ τ`
are equivalent to first applying `σ` then applying `τ`.

    ⧼ τ ⧽ ⧼ σ ⧽ M  ≡ ⧼ σ ⨟ τ ⧽ M

The proof of this equation requires several lemmas. First, we need to
prove the specialization for renaming.

    rename ρ (rename ρ' M) ≡ rename (ρ ∘ ρ') M

This in turn requires the following lemma about `ext`.

\begin{code}
compose-ext : ∀{Γ Δ Σ}{ρ : Rename Δ Σ} {ρ' : Rename Γ Δ} {A B} {x : Γ , B ∋ A}
            → ((ext ρ) ∘ (ext ρ')) x ≡ ext (ρ ∘ ρ') x
compose-ext {x = Z} = refl
compose-ext {x = S x} = refl
\end{code}

We proceed by induction on the term `M`, using the `compose-ext`
lemma in the case for `M ≡ ƛ N`.

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
variables, then they also commute on terms.

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
function distributes with sequencing. 

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


Now we come to the proof of `sub-sub`. 

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


## More stuff




rename-subst used by ℍ-ext in CallByName.

\begin{code}
rename-subst : ∀{Γ Δ Δ'}{M : Γ ⊢ ★}{ρ : Rename Γ Δ}{σ : Subst Δ Δ'}
             → ((subst σ) ∘ (rename ρ)) M ≡ subst (σ ∘ ρ) M
rename-subst {M = ` x} = refl
rename-subst {Γ}{Δ}{Δ'}{M = ƛ M}{ρ}{σ} =
  let ih : subst (exts σ) (rename (ext ρ) M)
           ≡ subst ((exts σ) ∘ ext ρ) M
      ih = rename-subst {M = M}{ρ = ext ρ}{σ = exts σ} in
  cong ƛ_ g
  where
        ss : same-subst ((exts σ) ∘ (ext ρ)) (exts (σ ∘ ρ))
        ss {A} {Z} = refl
        ss {A} {S x} = refl
        h : subst ((exts σ) ∘ (ext ρ)) M ≡ subst (exts (σ ∘ ρ)) M
        h = subst-equal{Γ , ★}{Δ = Δ' , ★}{σ = ((exts σ) ∘ (ext ρ))}
             {σ' = (exts (σ ∘ ρ))}{M = M} (λ {A} {x} → ss{A}{x})
        g : subst (exts σ) (rename (ext ρ) M)
           ≡ subst (exts (σ ∘ ρ)) M
        g =
           begin
             subst (exts σ) (rename (ext ρ) M)
           ≡⟨ rename-subst {M = M}{ρ = ext ρ}{σ = exts σ} ⟩
             subst ((exts σ) ∘ ext ρ) M
           ≡⟨ h ⟩
             subst (exts (σ ∘ ρ)) M
           ∎
rename-subst {M = L · M} =
   cong₂ _·_ (rename-subst{M = L}) (rename-subst{M = M})
\end{code}


\begin{code}
seq-assoc : ∀{Γ Δ Σ Ψ : Context}{B} {σ : Subst Γ Δ} {τ : Subst Δ Σ}
             {θ : Subst Σ Ψ} {x : Γ ∋ B}
          → ((σ ⨟ τ) ⨟ θ) x ≡ (σ ⨟ (τ ⨟ θ)) x
seq-assoc{Γ}{Δ}{Σ}{Ψ}{B}{σ}{τ}{θ}{x} =
          begin
            ((σ ⨟ τ) ⨟ θ) x
          ≡⟨⟩
            subst θ (subst τ (σ x))
          ≡⟨ sub-sub{M = σ x} ⟩
            (subst ((subst θ) ∘ τ)) (σ x)
          ≡⟨⟩
            (σ ⨟ (τ ⨟ θ)) x
          ∎
\end{code}

\begin{code}
{- Z-shift -}
cons-zero-S : ∀{Γ}{A B}{x : Γ , A ∋ B} → ((` Z) • (ren S_)) x ≡ ids x
cons-zero-S {x = Z} = refl
cons-zero-S {x = S x} = refl
\end{code}

\begin{code}
seq-congL : ∀{Γ Δ Σ : Context} {B} {σ σ' : Subst Γ Δ} {τ : Subst Δ Σ}
            {x : Γ ∋ B}
          → (∀{x : Γ ∋ B} → σ x ≡ σ' x)
          → (σ ⨟ τ) x ≡ (σ' ⨟ τ) x
seq-congL {τ = τ}{x = x} s = cong (subst τ) s

seq-congR : ∀{Γ Δ Σ : Context} {B} {σ : Subst Γ Δ} {τ τ' : Subst Δ Σ}
            {x : Γ ∋ B}
          → (∀{A}{x : Δ ∋ A} → τ x ≡ τ' x)
          → (σ ⨟ τ) x ≡ (σ ⨟ τ') x
seq-congR {Γ}{Δ}{Σ}{B}{σ}{τ}{τ'}{x} s =
     begin
       (σ ⨟ τ) x
     ≡⟨⟩
       subst τ (σ x)
     ≡⟨ subst-equal{M = σ x} s ⟩
       subst τ' (σ x)
     ≡⟨⟩
       (σ ⨟ τ') x
     ∎

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

\begin{code}
subst-zero-cons-ids : ∀{Γ}{A B : Type}{M : Γ ⊢ B}{x : Γ , B ∋ A}
                    → subst-zero M x ≡ (M • ids) x
subst-zero-cons-ids {x = Z} = refl
subst-zero-cons-ids {x = S x} = refl
\end{code}


rename-subst-commute is used in Confluence

\begin{code}
rename-subst-commute : ∀{Γ Δ}{N : Γ , ★ ⊢ ★}{M : Γ ⊢ ★}{ρ : Rename Γ Δ }
    → (rename (ext ρ) N) [ rename ρ M ] ≡ rename ρ (N [ M ])
rename-subst-commute {Γ}{Δ}{N}{M}{ρ} =
     begin
       (rename (ext ρ) N) [ rename ρ M ]
     ≡⟨⟩
       subst (subst-zero (rename ρ M)) (rename (ext ρ) N)
     ≡⟨ subst-equal{M = rename (ext ρ) N}
           (λ {A}{x} → subst-zero-cons-ids{x = x}) ⟩
       subst ((rename ρ M) • ids) (rename (ext ρ) N)
     ≡⟨ (subst-equal{M = rename (ext ρ) N}
             λ{A}{x} → cons-congL {σ = ids}{x = x} rename-subst-ren) ⟩
       subst ((subst (ren ρ) M) • ids) (rename (ext ρ) N)
     ≡⟨ cong (subst ((subst (ren ρ) M) • ids))
           (rename-subst-ren{ρ = ext ρ}{M = N}) ⟩
       subst ((subst (ren ρ) M) • ids) (subst (ren (ext ρ)) N)
     ≡⟨ sub-sub {M = N} ⟩
       subst ((ren (ext ρ)) ⨟ ((subst (ren ρ) M) • ids)) N
     ≡⟨ (subst-equal{M = N}
             λ{A}{x} → seq-congL{σ = ren (ext ρ)}
                         {σ' = ((` Z) • ((ren ρ) ⨟ (ren S_)))}{x = x}
             λ{x} → ren-ext-cons-shift{ρ = ρ}{x = x} ) ⟩
       subst (((` Z) • ((ren ρ) ⨟ (ren S_))) ⨟
                  ((subst (ren ρ) M) • ids)) N
     ≡⟨ (subst-equal{M = N} λ{A}{x} → sub-dist{x = x} ) ⟩
       subst ( (subst ((subst (ren ρ) M) • ids) (` Z)) •
           ( ((ren ρ) ⨟ (ren S_)) ⨟ ((subst (ren ρ) M) • ids))) N
     ≡⟨ subst-equal{M = N} (λ{A}{x} → cons-congL{x = x}
                (sub-head{σ = ids})) ⟩
       subst ((subst (ren ρ) M) •
                   (((ren ρ) ⨟ (ren S_)) ⨟ ((subst (ren ρ) M) • ids))) N
     ≡⟨ subst-equal{M = N} (λ{A}{x} → cons-congR{x = x}
         (λ{x} → seq-assoc {σ = ren ρ} {τ = ren S_}
                           {θ = ((subst (ren ρ) M) • ids)} {x = x})) ⟩
       subst ((subst (ren ρ) M) •
                   ((ren ρ) ⨟ ((ren S_) ⨟ ((subst (ren ρ) M) • ids)))) N
     ≡⟨ (subst-equal{M = N}λ{A}{x} → cons-congR{x = x}
            λ{x} → seq-congR {σ = ren ρ}
                             {τ = ( (ren S_) ⨟ ((subst (ren ρ) M) • ids))}
                             {τ' = ids} {x = x}
            λ{A}{x} → refl ) ⟩
       subst ((subst (ren ρ) M) • ( (ren ρ) ⨟ ids)) N
     ≡⟨ (subst-equal{M = N}λ{A}{x} → sym (sub-dist{x = x}) ) ⟩
       subst ((M • ids) ⨟ (ren ρ)) N
     ≡⟨ sym (sub-sub {M = N}) ⟩
       subst (ren ρ) (subst (M • ids) N)
     ≡⟨ sym (rename-subst-ren) ⟩
       rename ρ (subst (M • ids) N)
     ≡⟨ cong (rename ρ) (subst-equal{M = N}
           (λ {A}{x} → sym (subst-zero-cons-ids{x = x}))) ⟩
       rename ρ (subst (subst-zero M) N)
     ≡⟨⟩
       rename ρ (N [ M ])
     ∎
\end{code}

\begin{code}
subst-commute : ∀{Γ Δ}{N : Γ , ★ ⊢ ★}{M : Γ ⊢ ★}{σ : Subst Γ Δ }
    → (subst (exts σ) N) [ subst σ M ] ≡ subst σ (N [ M ])
subst-commute {Γ}{Δ}{N}{M}{σ} =
     begin
       (subst (exts σ) N) [ subst σ M ]
     ≡⟨⟩
       subst (subst-zero (subst σ M)) (subst (exts σ) N)
     ≡⟨ subst-equal{M = subst (exts σ) N}
            (λ {A}{x} → subst-zero-cons-ids{A = A}{x = x}) ⟩
       subst ((subst σ M) • ids) (subst (exts σ) N)
     ≡⟨ sub-sub{M = N} ⟩
       subst ((exts σ) ⨟ ((subst σ M) • ids)) N
     ≡⟨ subst-equal{M = N}
         (λ {A}{x} → seq-congL{σ = exts σ}{σ' = ((` Z) • (σ ⨟ (ren S_)))}
            {x = x} (λ {x} → exts-cons-shift{x = x}) ) ⟩
       subst (((` Z) • (σ ⨟ (ren S_))) ⨟ ((subst σ M) • ids)) N
     ≡⟨ subst-equal{M = N} (λ {A}{x} → sub-dist{M = ` Z}{x = x}) ⟩
       subst ((subst ((subst σ M) • ids) (` Z)) •
                   ((σ ⨟ (ren S_)) ⨟ ((subst σ M) • ids))) N
     ≡⟨⟩
       subst ((subst σ M) •
                   ((σ ⨟ (ren S_)) ⨟ ((subst σ M) • ids))) N
     ≡⟨ subst-equal{M = N} (λ {A} {x} → cons-congR {x = x}
           λ {x} → seq-assoc{σ = σ}) ⟩
       subst ((subst σ M) •
                   (σ ⨟ ((ren S_) ⨟ ((subst σ M) • ids)))) N
     ≡⟨ (subst-equal{M = N} λ {A} {x} → cons-congR {x = x}
          λ {x} → seq-congR {σ = σ}
          λ {A}{x} → refl) ⟩
       subst ((subst σ M) • (σ ⨟ ids)) N
     ≡⟨ (subst-equal{M = N} λ {A} {x} → cons-congR{x = x} (seq-id{σ = σ})) ⟩
       subst ((subst σ M) • σ) N
     ≡⟨ subst-equal{M = N} (λ {A}{x} → cons-congR{x = x} (id-seq{σ = σ})) ⟩
       subst ((subst σ M) • (ids ⨟ σ)) N
     ≡⟨ (subst-equal{M = N} λ {A}{x} → sym (sub-dist{x = x})) ⟩
       subst ((M • ids) ⨟ σ) N
     ≡⟨ sym (sub-sub{M = N}) ⟩
       subst σ (subst (M • ids) N)
     ≡⟨ cong (subst σ) (sym (subst-equal{M = N}
          λ {A}{x} → subst-zero-cons-ids{x = x})) ⟩
       subst σ (N [ M ])
     ∎
\end{code}

\begin{code}
_〔_〕 : ∀ {Γ A B C}
        → Γ , B , C ⊢ A
        → Γ ⊢ B
          ---------
        → Γ , C ⊢ A
_〔_〕 {Γ} {A} {B} {C} N M =
   subst {Γ , B , C} {Γ , C} (exts (subst-zero M)) {A} N
\end{code}

\begin{code}
substitution : ∀{Γ}{M : Γ , ★ , ★ ⊢ ★}{N : Γ , ★ ⊢ ★}{L : Γ ⊢ ★}
    → (M [ N ]) [ L ] ≡ (M 〔 L 〕) [ (N [ L ]) ]
substitution{M = M}{N = N}{L = L} =
   sym (subst-commute{N = M}{M = N}{σ = subst-zero L})
\end{code}






## Notes

Most of the properties and proofs in this file are based on the paper
_Autosubst: Reasoning with de Bruijn Terms and Parallel Substitution_
by Schafer, Tebbi, and Smolka (ITP 2015).

