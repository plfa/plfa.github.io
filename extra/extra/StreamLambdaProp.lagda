---
title     : "StreamLambdaProp: Properties of Simply-Typed Lambda Calculus"
permalink : /StreamLambdaProp/
---

[Variant of normalise that uses streams is at end]


\begin{code}
module StreamLambdaProp where
\end{code}

[Parts of this chapter take their text from chapter _Stlc_
of _Software Foundations_ (_Programming Language Foundations_).
Those parts will be revised.]

This chapter develops the fundamental theory of the Simply
Typed Lambda Calculus, particularly progress and preservation.

The development in this chapter was inspired by the corresponding
development in Chapter _StlcProp_ of _Software Foundations_
(_Programming Language Foundations_).  It will turn
out that one of our technical choices in the previous chapter
(to introduce an explicit judgment `Γ ∋ x ⦂ A` in place of
treating a context as a function from identifiers to types)
permits a simpler development. In particular, we can prove substitution preserves
types without needing to develop a separate inductive definition of the
`appears_free_in` relation.


## Imports

\begin{code}
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)
open import plta.Lambda
open Chain (Term) (_⟶_)
\end{code}


## Canonical Forms

The first step in establishing basic properties of reduction and typing
is to identify the possible _canonical forms_ (i.e., well-typed closed values)
belonging to each type.  For function types the canonical forms are lambda-abstractions,
while for boolean types they are values `true` and `false`.

\begin{code}
infix  4 Canonical_⦂_

data Canonical_⦂_ : Term → Type → Set where

  C-ƛ : ∀ {x A N B}
      -----------------------------
    → Canonical (ƛ x ⇒ N) ⦂ (A ⇒ B)

  C-zero :
      --------------------
      Canonical `zero ⦂ `ℕ

  C-suc : ∀ {V}
    → Canonical V ⦂ `ℕ
      ---------------------
    → Canonical `suc V ⦂ `ℕ

canonical : ∀ {M A}
  → ∅ ⊢ M ⦂ A
  → Value M
    ---------------
  → Canonical M ⦂ A
canonical (Ax ())          ()
canonical (⊢ƛ ⊢N)          V-ƛ         =  C-ƛ
canonical (⊢L · ⊢M)        ()
canonical ⊢zero            V-zero      =  C-zero
canonical (⊢suc ⊢V)        (V-suc VV)  =  C-suc (canonical ⊢V VV)
canonical (⊢case ⊢L ⊢M ⊢N) ()
canonical (⊢μ ⊢M)          ()

value : ∀ {M A}
  → Canonical M ⦂ A
    ----------------
  → Value M
value C-ƛ         = V-ƛ
value C-zero      = V-zero
value (C-suc CM)  = V-suc (value CM)
\end{code}

## Progress

As before, the _progress_ theorem tells us that closed, well-typed
terms are not stuck: either a well-typed term can take a reduction
step or it is a value.

\begin{code}
data Progress (M : Term) : Set where

  step : ∀ {N}
    → M ⟶ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

progress : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Progress M
progress (Ax ())
progress (⊢ƛ ⊢N)                             =  done V-ƛ
progress (⊢L · ⊢M) with progress ⊢L
... | step L⟶L′                            =  step (ξ-·₁ L⟶L′)
... | done VL with progress ⊢M
...   | step M⟶M′                          =  step (ξ-·₂ VL M⟶M′)
...   | done VM with canonical ⊢L VL
...     | C-ƛ                                =  step (β-ƛ· VM)
progress ⊢zero                               =  done V-zero
progress (⊢suc ⊢M) with progress ⊢M
...  | step M⟶M′                           =  step (ξ-suc M⟶M′)
...  | done VM                               =  done (V-suc VM)
progress (⊢case ⊢L ⊢M ⊢N) with progress ⊢L
... | step L⟶L′                            =  step (ξ-case L⟶L′)
... | done VL with canonical ⊢L VL
...   | C-zero                               =  step β-case-zero
...   | C-suc CL                             =  step (β-case-suc (value CL))
progress (⊢μ ⊢M)                            =  step β-μ
\end{code}

This code reads neatly in part because we consider the
`step` option before the `done` option. We could, of course,
do it the other way around, but then the `...` abbreviation
no longer works, and we will need to write out all the arguments
in full. In general, the rule of thumb is to consider the easy case
(here `step`) before the hard case (here `done`).
If you have two hard cases, you will have to expand out `...`
or introduce subsidiary functions.

\begin{code}
postulate
  progress′ : ∀ M {A} → ∅ ⊢ M ⦂ A → Progress M
\end{code}

## Prelude to preservation

The other half of the type soundness property is the preservation
of types during reduction.  For this, we need to develop
technical machinery for reasoning about variables and
substitution.  Working from top to bottom (from the high-level
property we are actually interested in to the lowest-level
technical lemmas), the story goes like this:

  - The _preservation theorem_ is proved by induction on a typing derivation.
    The definition of `β-ƛ· uses substitution.  To see that
    this step preserves typing, we need to know that the substitution itself
    does.  So we prove a ...

  - _substitution lemma_, stating that substituting a (closed) term
    `V` for a variable `x` in a term `N` preserves the type of `N`.
    The proof goes by induction on the typing derivation of `N`.
    The lemma does not require that `V` be a value,
    though in practice we only substitute values.  The tricky cases
    are the ones for variables and those that do binding, namely,
    function abstraction, case over a natural, and fixpoints.  In each
    case, we discover that we need to take a term `V` that has been
    shown to be well-typed in some context `Γ` and consider the same
    term in a different context `Δ`.  For this we prove a ...

  - _renaming lemma_, showing that typing is preserved
    under weakening of the context---a term `M`
    well typed in `Γ` is also well typed in `Δ`, so long as
    every free variable found in `Γ` is also found in `Δ`.

To make Agda happy, we need to formalize the story in the opposite
order.


### Renaming

Sometimes, when we have a proof `Γ ⊢ M ⦂ A`, we will need to
replace `Γ` by a different context `Δ`.  When is it safe
to do this?  Intuitively, whenever every variable given a type
by `Γ` is also given a type by `Δ`.

*(((Need to explain ext)))*

\begin{code}
ext : ∀ {Γ Δ}
  → (∀ {w B}     →        Γ ∋ w ⦂ B →         Δ ∋ w ⦂ B)
    -----------------------------------------------------
  → (∀ {w x A B} → Γ , x ⦂ A ∋ w ⦂ B → Δ , x ⦂ A ∋ w ⦂ B)
ext σ Z          =  Z
ext σ (S w≢ ∋w)  =  S w≢ (σ ∋w)

rename : ∀ {Γ Δ}
        → (∀ {w B} → Γ ∋ w ⦂ B → Δ ∋ w ⦂ B)
          ----------------------------------
        → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A)
rename σ (Ax ∋w)           =  Ax (σ ∋w)
rename σ (⊢ƛ ⊢N)           =  ⊢ƛ (rename (ext σ) ⊢N)
rename σ (⊢L · ⊢M)         =  (rename σ ⊢L) · (rename σ ⊢M)
rename σ ⊢zero             =  ⊢zero
rename σ (⊢suc ⊢M)         =  ⊢suc (rename σ ⊢M)
rename σ (⊢case ⊢L ⊢M ⊢N)  =  ⊢case (rename σ ⊢L) (rename σ ⊢M) (rename (ext σ) ⊢N)
rename σ (⊢μ ⊢M)           =  ⊢μ (rename (ext σ) ⊢M)
\end{code}

We have three important corollaries.  First,
any closed term can be weakened to any context.
\begin{code}
rename-∅ : ∀ {Γ M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Γ ⊢ M ⦂ A
rename-∅ {Γ} ⊢M = rename σ ⊢M
  where
  σ : ∀ {z C}
    → ∅ ∋ z ⦂ C
      ---------
    → Γ ∋ z ⦂ C
  σ ()
\end{code}

Second, if the last two variables in a context are
equal, the term can be renamed to drop the redundant one.
\begin{code}
rename-≡ : ∀ {Γ x M A B C}
  → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ B ⊢ M ⦂ C
rename-≡ {Γ} {x} {M} {A} {B} {C} ⊢M = rename σ ⊢M
  where
  σ : ∀ {z C}
    → Γ , x ⦂ A , x ⦂ B ∋ z ⦂ C
      -------------------------
    → Γ , x ⦂ B ∋ z ⦂ C
  σ Z                   =  Z
  σ (S z≢x Z)           =  ⊥-elim (z≢x refl)
  σ (S z≢x (S z≢y ∋z))  =  S z≢x ∋z
\end{code}

Third, if the last two variables in a context differ,
the term can be renamed to flip their order.
\begin{code}
rename-≢ : ∀ {Γ x y M A B C}
  → x ≢ y
  → Γ , y ⦂ A , x ⦂ B ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ B , y ⦂ A ⊢ M ⦂ C
rename-≢ {Γ} {x} {y} {M} {A} {B} {C} x≢y ⊢M = rename σ ⊢M
  where
  σ : ∀ {z C}
    → Γ , y ⦂ A , x ⦂ B ∋ z ⦂ C
      --------------------------
    → Γ , x ⦂ B , y ⦂ A ∋ z ⦂ C
  σ Z                    =  S (λ{refl → x≢y refl}) Z
  σ (S z≢x Z)            =  Z
  σ (S z≢x (S z≢y ∋z))   =  S z≢y (S z≢x ∋z)
\end{code}


## Substitution

Now we come to the conceptual heart of the proof that reduction
preserves types---namely, the observation that _substitution_
preserves types.

Formally, the _Substitution Lemma_ says this: Suppose we
have a term `N` with a free variable `x`, where `N` has
type `B` under the assumption that `x` has some type `A`.
Also, suppose that we have some other term `V`,
where `V` has type `A`.  Then, since `V` satisfies
the assumption we made about `x` when typing `N`, we should be
able to substitute `V` for each of the occurrences of `x` in `N`
and obtain a new term that still has type `B`.

_Lemma_: If `Γ , x ⦂ A ⊢ N ⦂ B` and `∅ ⊢ V ⦂ A`, then
`Γ ⊢ (N [ x := V ]) ⦂ B`.

One technical subtlety in the statement of the lemma is that we assume
`V` is closed; it has type `A` in the _empty_ context.  This
assumption simplifies the `λ` case of the proof because the context
invariance lemma then tells us that `V` has type `A` in any context at
all---we don't have to worry about free variables in `V` clashing with
the variable being introduced into the context by `λ`. It is possible
to prove the theorem under the more general assumption `Γ ⊢ V ⦂ A`,
but the proof is more difficult.

<!--
Intuitively, the substitution lemma says that substitution and typing can
be done in either order: we can either assign types to the terms
`N` and `V` separately (under suitable contexts) and then combine
them using substitution, or we can substitute first and then
assign a type to `N [ x := V ]`---the result is the same either
way.
-->

\begin{code}
subst : ∀ {Γ x N V A B}
  → Γ , x ⦂ A ⊢ N ⦂ B
  → ∅ ⊢ V ⦂ A
    --------------------
  → Γ ⊢ N [ x := V ] ⦂ B

subst {x = y} (Ax {x = x} Z) ⊢V with x ≟ y
... | yes refl        =  rename-∅ ⊢V
... | no  x≢y         =  ⊥-elim (x≢y refl)
subst {x = y} (Ax {x = x} (S x≢y ∋x)) ⊢V with x ≟ y
... | yes refl        =  ⊥-elim (x≢y refl)
... | no  _           =  Ax ∋x
subst {x = y} (⊢ƛ {x = x} ⊢N) ⊢V with x ≟ y
... | yes refl        =  ⊢ƛ (rename-≡ ⊢N)
... | no  x≢y         =  ⊢ƛ (subst (rename-≢ x≢y ⊢N) ⊢V)
subst (⊢L · ⊢M) ⊢V    = (subst ⊢L ⊢V) · (subst ⊢M ⊢V)
subst ⊢zero ⊢V        =  ⊢zero
subst (⊢suc ⊢M) ⊢V    =  ⊢suc (subst ⊢M ⊢V)
subst {x = y} (⊢case {x = x} ⊢L ⊢M ⊢N) ⊢V with x ≟ y
... | yes refl        =  ⊢case (subst ⊢L ⊢V) (subst ⊢M ⊢V) (rename-≡ ⊢N)
... | no  x≢y         =  ⊢case (subst ⊢L ⊢V) (subst ⊢M ⊢V) (subst (rename-≢ x≢y ⊢N) ⊢V)
subst {x = y} (⊢μ {x = x} ⊢M) ⊢V with x ≟ y
... | yes refl        =  ⊢μ (rename-≡ ⊢M)
... | no  x≢y         =  ⊢μ (subst (rename-≢ x≢y ⊢M) ⊢V)
\end{code}


### Main Theorem

We now have the tools we need to prove preservation: if a closed
term `M` has type `A` and takes a step to `N`, then `N`
is also a closed term with type `A`.  In other words, small-step
reduction preserves types.

\begin{code}
preserve : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M ⟶ N
    ----------
  → ∅ ⊢ N ⦂ A
preserve (Ax ())
preserve (⊢ƛ ⊢N)                 ()
preserve (⊢L · ⊢M)               (ξ-·₁ L⟶L′)     =  (preserve ⊢L L⟶L′) · ⊢M
preserve (⊢L · ⊢M)               (ξ-·₂ VL M⟶M′)  =  ⊢L · (preserve ⊢M M⟶M′)
preserve ((⊢ƛ ⊢N) · ⊢V)          (β-ƛ· VV)        =  subst ⊢N ⊢V
preserve ⊢zero                   ()
preserve (⊢suc ⊢M)               (ξ-suc M⟶M′)    =  ⊢suc (preserve ⊢M M⟶M′)
preserve (⊢case ⊢L ⊢M ⊢N)        (ξ-case L⟶L′)   =  ⊢case (preserve ⊢L L⟶L′) ⊢M ⊢N
preserve (⊢case ⊢zero ⊢M ⊢N)     β-case-zero      =  ⊢M
preserve (⊢case (⊢suc ⊢V) ⊢M ⊢N) (β-case-suc VV)  =  subst ⊢N ⊢V
preserve (⊢μ ⊢M)                 (β-μ)            =  subst ⊢M (⊢μ ⊢M)
\end{code}


## Normalisation

\begin{code}
Gas : Set
Gas = ℕ

data Normalise (M : Term) : Set where

  out-of-gas : ∀ {N A}
    → M ⟶* N
    → ∅ ⊢ N ⦂ A
      -------------
    → Normalise M

  normal : ∀ {V}
    → Gas
    → M ⟶* V
    → Value V
     --------------
    → Normalise M

normalise : ∀ {M A}
  → Gas
  → ∅ ⊢ M ⦂ A
    -----------
  → Normalise M
normalise {L} zero    ⊢L                   =  out-of-gas (L ∎) ⊢L
normalise {L} (suc m) ⊢L with progress ⊢L
...  | done VL                             =  normal (suc m) (L ∎) VL
...  | step L⟶M with normalise m (preserve ⊢L L⟶M)
...          | out-of-gas M⟶*N ⊢N        =  out-of-gas (L ⟶⟨ L⟶M ⟩ M⟶*N) ⊢N
...          | normal n M⟶*V VV          =  normal n (L ⟶⟨ L⟶M ⟩ M⟶*V) VV
\end{code}

### Examples

\begin{code}
_ : normalise 100 ⊢four ≡
  normal 88
  ((μ "+" ⇒
    (ƛ "m" ⇒
     (ƛ "n" ⇒
      `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (⌊ "+" ⌋ · ⌊ "m" ⌋ · ⌊ "n" ⌋)
      ])))
   · `suc (`suc `zero)
   · `suc (`suc `zero)
   ⟶⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
   (ƛ "m" ⇒
    (ƛ "n" ⇒
     `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒
     `suc
     ((μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (⌊ "+" ⌋ · ⌊ "m" ⌋ · ⌊ "n" ⌋)
         ])))
      · ⌊ "m" ⌋
      · ⌊ "n" ⌋)
     ]))
   · `suc (`suc `zero)
   · `suc (`suc `zero)
   ⟶⟨ ξ-·₁ (β-ƛ· (V-suc (V-suc V-zero))) ⟩
   (ƛ "n" ⇒
    `case `suc (`suc `zero) [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒
    `suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (⌊ "+" ⌋ · ⌊ "m" ⌋ · ⌊ "n" ⌋)
        ])))
     · ⌊ "m" ⌋
     · ⌊ "n" ⌋)
    ])
   · `suc (`suc `zero)
   ⟶⟨ β-ƛ· (V-suc (V-suc V-zero)) ⟩
   `case `suc (`suc `zero) [zero⇒ `suc (`suc `zero) |suc "m" ⇒
   `suc
   ((μ "+" ⇒
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (⌊ "+" ⌋ · ⌊ "m" ⌋ · ⌊ "n" ⌋)
       ])))
    · ⌊ "m" ⌋
    · `suc (`suc `zero))
   ]
   ⟶⟨ β-case-suc (V-suc V-zero) ⟩
   `suc
   ((μ "+" ⇒
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (⌊ "+" ⌋ · ⌊ "m" ⌋ · ⌊ "n" ⌋)
       ])))
    · `suc `zero
    · `suc (`suc `zero))
   ⟶⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
   `suc
   ((ƛ "m" ⇒
     (ƛ "n" ⇒
      `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒
      `suc
      ((μ "+" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (⌊ "+" ⌋ · ⌊ "m" ⌋ · ⌊ "n" ⌋)
          ])))
       · ⌊ "m" ⌋
       · ⌊ "n" ⌋)
      ]))
    · `suc `zero
    · `suc (`suc `zero))
   ⟶⟨ ξ-suc (ξ-·₁ (β-ƛ· (V-suc V-zero))) ⟩
   `suc
   ((ƛ "n" ⇒
     `case `suc `zero [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒
     `suc
     ((μ "+" ⇒
       (ƛ "m" ⇒
        (ƛ "n" ⇒
         `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (⌊ "+" ⌋ · ⌊ "m" ⌋ · ⌊ "n" ⌋)
         ])))
      · ⌊ "m" ⌋
      · ⌊ "n" ⌋)
     ])
    · `suc (`suc `zero))
   ⟶⟨ ξ-suc (β-ƛ· (V-suc (V-suc V-zero))) ⟩
   `suc
   `case `suc `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒
   `suc
   ((μ "+" ⇒
     (ƛ "m" ⇒
      (ƛ "n" ⇒
       `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (⌊ "+" ⌋ · ⌊ "m" ⌋ · ⌊ "n" ⌋)
       ])))
    · ⌊ "m" ⌋
    · `suc (`suc `zero))
   ]
   ⟶⟨ ξ-suc (β-case-suc V-zero) ⟩
   `suc
   (`suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (⌊ "+" ⌋ · ⌊ "m" ⌋ · ⌊ "n" ⌋)
        ])))
     · `zero
     · `suc (`suc `zero)))
   ⟶⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
   `suc
   (`suc
    ((ƛ "m" ⇒
      (ƛ "n" ⇒
       `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒
       `suc
       ((μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (⌊ "+" ⌋ · ⌊ "m" ⌋ · ⌊ "n" ⌋)
           ])))
        · ⌊ "m" ⌋
        · ⌊ "n" ⌋)
       ]))
     · `zero
     · `suc (`suc `zero)))
   ⟶⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ· V-zero))) ⟩
   `suc
   (`suc
    ((ƛ "n" ⇒
      `case `zero [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒
      `suc
      ((μ "+" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (⌊ "+" ⌋ · ⌊ "m" ⌋ · ⌊ "n" ⌋)
          ])))
       · ⌊ "m" ⌋
       · ⌊ "n" ⌋)
      ])
     · `suc (`suc `zero)))
   ⟶⟨ ξ-suc (ξ-suc (β-ƛ· (V-suc (V-suc V-zero)))) ⟩
   `suc
   (`suc
    `case `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒
    `suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        `case ⌊ "m" ⌋ [zero⇒ ⌊ "n" ⌋ |suc "m" ⇒ `suc (⌊ "+" ⌋ · ⌊ "m" ⌋ · ⌊ "n" ⌋)
        ])))
     · ⌊ "m" ⌋
     · `suc (`suc `zero))
    ])
   ⟶⟨ ξ-suc (ξ-suc β-case-zero) ⟩ `suc (`suc (`suc (`suc `zero))) ∎)
  (V-suc (V-suc (V-suc (V-suc V-zero))))
_ = refl
\end{code}

\begin{code}
_ : normalise 100 ⊢fourᶜ ≡
  normal 88
  ((ƛ "m" ⇒
    (ƛ "n" ⇒
     (ƛ "s" ⇒ (ƛ "z" ⇒ ⌊ "m" ⌋ · ⌊ "s" ⌋ · (⌊ "n" ⌋ · ⌊ "s" ⌋ · ⌊ "z" ⌋)))))
   · (ƛ "s" ⇒ (ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋)))
   · (ƛ "s" ⇒ (ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋)))
   · (ƛ "n" ⇒ `suc ⌊ "n" ⌋)
   · `zero
   ⟶⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ· V-ƛ))) ⟩
   (ƛ "n" ⇒
    (ƛ "s" ⇒
     (ƛ "z" ⇒
      (ƛ "s" ⇒ (ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋))) · ⌊ "s" ⌋ ·
      (⌊ "n" ⌋ · ⌊ "s" ⌋ · ⌊ "z" ⌋))))
   · (ƛ "s" ⇒ (ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋)))
   · (ƛ "n" ⇒ `suc ⌊ "n" ⌋)
   · `zero
   ⟶⟨ ξ-·₁ (ξ-·₁ (β-ƛ· V-ƛ)) ⟩
   (ƛ "s" ⇒
    (ƛ "z" ⇒
     (ƛ "s" ⇒ (ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋))) · ⌊ "s" ⌋ ·
     ((ƛ "s" ⇒ (ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋))) · ⌊ "s" ⌋ · ⌊ "z" ⌋)))
   · (ƛ "n" ⇒ `suc ⌊ "n" ⌋)
   · `zero
   ⟶⟨ ξ-·₁ (β-ƛ· V-ƛ) ⟩
   (ƛ "z" ⇒
    (ƛ "s" ⇒ (ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋))) · (ƛ "n" ⇒ `suc ⌊ "n" ⌋)
    ·
    ((ƛ "s" ⇒ (ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋))) · (ƛ "n" ⇒ `suc ⌊ "n" ⌋)
     · ⌊ "z" ⌋))
   · `zero
   ⟶⟨ β-ƛ· V-zero ⟩
   (ƛ "s" ⇒ (ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋))) · (ƛ "n" ⇒ `suc ⌊ "n" ⌋)
   ·
   ((ƛ "s" ⇒ (ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋))) · (ƛ "n" ⇒ `suc ⌊ "n" ⌋)
    · `zero)
   ⟶⟨ ξ-·₁ (β-ƛ· V-ƛ) ⟩
   (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ((ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ⌊ "z" ⌋)) ·
   ((ƛ "s" ⇒ (ƛ "z" ⇒ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋))) · (ƛ "n" ⇒ `suc ⌊ "n" ⌋)
    · `zero)
   ⟶⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ· V-ƛ)) ⟩
   (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ((ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ⌊ "z" ⌋)) ·
   ((ƛ "z" ⇒ (ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ((ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ⌊ "z" ⌋)) ·
    `zero)
   ⟶⟨ ξ-·₂ V-ƛ (β-ƛ· V-zero) ⟩
   (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ((ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ⌊ "z" ⌋)) ·
   ((ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ((ƛ "n" ⇒ `suc ⌊ "n" ⌋) · `zero))
   ⟶⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ· V-zero)) ⟩
   (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ((ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ⌊ "z" ⌋)) ·
   ((ƛ "n" ⇒ `suc ⌊ "n" ⌋) · `suc `zero)
   ⟶⟨ ξ-·₂ V-ƛ (β-ƛ· (V-suc V-zero)) ⟩
   (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ((ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ⌊ "z" ⌋)) ·
   `suc (`suc `zero)
   ⟶⟨ β-ƛ· (V-suc (V-suc V-zero)) ⟩
   (ƛ "n" ⇒ `suc ⌊ "n" ⌋) · ((ƛ "n" ⇒ `suc ⌊ "n" ⌋) · `suc (`suc `zero))
   ⟶⟨ ξ-·₂ V-ƛ (β-ƛ· (V-suc (V-suc V-zero))) ⟩
   (ƛ "n" ⇒ `suc ⌊ "n" ⌋) · `suc (`suc (`suc `zero)) ⟶⟨
   β-ƛ· (V-suc (V-suc (V-suc V-zero))) ⟩
   `suc (`suc (`suc (`suc `zero))) ∎)
  (V-suc (V-suc (V-suc (V-suc V-zero))))
_ = refl
\end{code}




#### Exercise: 2 stars, recommended (subject_expansion_stlc)

<!--
An exercise in the [Types]({{ "Types" | relative_url }}) chapter asked about the
subject expansion property for the simple language of arithmetic and boolean
expressions.  Does this property hold for STLC?  That is, is it always the case
that, if `M ==> N` and `∅ ⊢ N ⦂ A`, then `∅ ⊢ M ⦂ A`?  It is easy to find a
counter-example with conditionals, find one not involving conditionals.
-->

We say that `M` _reduces_ to `N` if `M ⟶ N`,
and that `M` _expands_ to `N` if `N ⟶ M`.
The preservation property is sometimes called _subject reduction_.
Its opposite is _subject expansion_, which holds if
`M ==> N` and `∅ ⊢ N ⦂ A`, then `∅ ⊢ M ⦂ A`.
Find two counter-examples to subject expansion, one
with case expressions and one not involving case expressions.

## Type Soundness

#### Exercise: 2 stars, optional (type_soundness)

Put progress and preservation together and show that a well-typed
term can _never_ reach a stuck state.

\begin{code}
Normal : Term → Set
Normal M = ∀ {N} → ¬ (M ⟶ N)

Stuck : Term → Set
Stuck M = Normal M × ¬ Value M

postulate
  Soundness : ∀ {M N A}
    → ∅ ⊢ M ⦂ A
    → M ⟶* N
      -----------
    → ¬ (Stuck N)
\end{code}

<div class="hidden">
\begin{code}
Soundness′ : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M ⟶* N
    -----------
  → ¬ (Stuck N)
Soundness′ ⊢M (M ∎) ⟨ ¬M⟶N , ¬VM ⟩ with progress ⊢M
... | step M⟶N                      =  ¬M⟶N M⟶N
... | done VM                         =  ¬VM VM
Soundness′ ⊢L (L ⟶⟨ L⟶M ⟩ M⟶*N)  =  Soundness′ (preserve ⊢L L⟶M) M⟶*N
\end{code}
</div>


## Additional Exercises

#### Exercise: 1 star (progress_preservation_statement)

Without peeking at their statements above, write down the progress
and preservation theorems for the simply typed lambda-calculus.

#### Exercise: 2 stars (stlc_variation1)

Suppose we add a new term `zap` with the following reduction rule

                     ---------                  (ST_Zap)
                     M ⟶ zap

and the following typing rule:

                    -----------                 (T_Zap)
                    Γ ⊢ zap : A

Which of the following properties of the STLC remain true in
the presence of these rules?  For each property, write either
"remains true" or "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation


#### Exercise: 2 stars (stlc_variation2)

Suppose instead that we add a new term `foo` with the following
reduction rules:

                 -------------------              (Foo₁)
                 (λ x ⇒ ⌊ x ⌋) ⟶ foo

                    ------------                  (Foo₂)
                    foo ⟶ true

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation

#### Exercise: 2 stars (stlc_variation3)

Suppose instead that we remove the rule `ξ·₁` from the `⟶`
relation. Which of the following properties of the STLC remain
true in the absence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation

#### Exercise: 2 stars, optional (stlc_variation4)
Suppose instead that we add the following new rule to the
reduction relation:

     ----------------------------------------      (FunnyCaseZero)
     case zero [zero⇒ M |suc x ⇒ N ] ⟶ true

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation


#### Exercise: 2 stars, optional (stlc_variation5)

Suppose instead that we add the following new rule to the typing
relation:

             Γ ⊢ L ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
             Γ ⊢ M ⦂ `ℕ
             ------------------------------          (FunnyApp)
             Γ ⊢ L · M ⦂ `ℕ

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation



#### Exercise: 2 stars, optional (stlc_variation6)

Suppose instead that we add the following new rule to the typing
relation:

                Γ ⊢ L ⦂ `ℕ
                Γ ⊢ M ⦂ `ℕ
                ---------------------               (FunnyApp')
                Γ ⊢ L · M ⦂ `ℕ

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation



#### Exercise : 2 stars, optional (stlc_variation7)

Suppose we add the following new rule to the typing relation
of the STLC:

                --------------------              (T_FunnyAbs)
                ∅ ⊢ ƛ x ⇒ N ⦂ `ℕ

Which of the following properties of the STLC remain true in
the presence of this rule?  For each one, write either
"remains true" or else "becomes false." If a property becomes
false, give a counterexample.

  - Determinism of `step`

  - Progress

  - Preservation


## Normalisation with streams

\begin{code}
record Lift (M : Term) : Set
data Steps (M : Term) : Set

record Lift (M : Term) where
  coinductive
  field
    force : Steps M

open Lift

data Steps (M : Term) where

  done :
      Value M
      -------
    → Steps M

  step : ∀ {N : Term}
    → M ⟶ N
    → Lift N
      --------------
    → Steps M

norm : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Lift M
force (norm ⊢M) with progress ⊢M
... | done VM   =   done VM
... | step M↦N  =   step M↦N (norm (preserve ⊢M M↦N))

data Cut (M : Term) : Set where

  out-of-gas : ∀ {N : Term}
    → M ⟶* N
      --------
    → Cut M

  normal : ∀ {V : Term}
    → Gas
    → M ⟶* V
    → Value V
      -------
    → Cut M

cut : ∀ {L} → Gas → Lift L → Cut L
cut {L} zero _                               =  out-of-gas (L ∎)
cut {L} (suc n) LiftL with force LiftL
... | done VL                                =  normal n (L ∎) VL
... | step L↦M LiftM  with  cut n LiftM
...   |  out-of-gas M↠N                      =  out-of-gas (L ⟶⟨ L↦M ⟩ M↠N)
...   |  normal g M↠V VV                     =  normal g (L ⟶⟨ L↦M ⟩ M↠V) VV

take : ∀ {L} → Gas → Lift L → ∃[ N ](L ⟶* N)
take {L} zero _                               =  ⟨ L , L ∎ ⟩
take {L} (suc n) LiftL with force LiftL
... | done _                                  =  ⟨ L , L ∎ ⟩
... | step L↦M LiftM  with  take n LiftM
...   |  ⟨ N , M↠N ⟩                          =  ⟨ N , L ⟶⟨ L↦M ⟩ M↠N ⟩
\end{code}
