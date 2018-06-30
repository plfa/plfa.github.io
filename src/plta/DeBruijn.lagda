---
title     : "DeBruijn: Inherently typed de Bruijn representation"
layout    : page
permalink : /DeBruijn/
---

\begin{code}
module plta.DeBruijn where
\end{code}

The previous two chapters introduced lambda calculus, with a
formalisation based on named variables, and terms defined separately
from types.  We began with that approach because it is traditional,
but it is not the one we recommend.  This chapter presents an
alternative approach, where named variables are replaced by de Bruijn
indices and terms are inherently typed.  Our new presentation is more
compact, using less than half the lines of code required previously to
do cover the same ground.

## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (map)
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Nullary.Product using (_×-dec_)
\end{code}

## Introduction

There is a close correspondence between the structure of a term and
the structure of the derivation showing that it is well-typed.  For
example, here is the term for the Church numeral two:

    twoᶜ  : Term
    twoᶜ  = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

And here is its corresponding type derivation:

    ⊢twoᶜ  :  ∀ {A} ⇒ ∅ ⊢ two ⦂ Ch A
    ⊢twoᶜ  =  ⊢ƛ (⊢ƛ (Ax ∋s · (Ax ∋s · Ax ∋z)))
               where    
               ∋s = S ("s" ≠ "z") Z
               ∋z = Z

(These are both taken from
Chapter [Lambda]({{ site.baseurl }}{% link out/plta/Lambda.md %})
and you can see the corresponding derivation tree written out in full
[here]({{ site.baseurl }}{% link out/plta/Lambda.md %}/#derivation).)
The two definitions are in close correspondence, where

  * `` `_ `` corresponds to `Ax`
  * `ƛ_⇒_`   corresponds to `⊢ƛ`
  * `_·_`    corresponds to `_·_`

Further, if we think of `Z` as zero and `S` as successor, then the
lookup derivation for each variable corresponds to a number which
tells us how many enclosing binding terms to count to find the binding
of that variable.  Here `"z"` corresponds to `Z` or zero and `"s"`
corresponds to `S Z` or one.  And, indeed, "z" is bound by the inner
abstraction (count outward past zero abstractions) and "s" is bound by
the outer abstraction (count outward past one abstraction).

In this chapter, we are going to exploit this correspondence, and
introduce a new notation for terms that simultaneously represents the
term and its type derivation.  Now we will write the following.

    twoᶜ  :  ∅ ⊢ Ch `ℕ
    twoᶜ  =  ƛ ƛ (# 1 · (# 1 · # 0))

A variable is represented by a natural number (written with `Z` and `S`, and
abbreviated in the usual way), and tells us how many enclosing binding terms
to count to find the binding of that variable. Thus, `# 0` is bound at the
inner `ƛ`, and `# 1` at the outer `ƛ`.

Replacing variables by numbers in this way is called _de Bruijn
representation_, and the numbers themselves are called _de Bruijn
indices_, after the Dutch mathematician Nicolaas Govert (Dick) de
Bruijn (1918—2012), a pioneer in the creation of proof assistants.
One advantage of replacing named variables with de Bruijn indices
is that each term now has a unique representation, rather than being
represented by the equivalence class of terms under alpha renaming.

The other important feature of our chosen representation is that it is
_inherently typed_.  In the previous two chapters, the definition of
terms and the definition of types are completely separate.  All terms
have type `Term`, and nothing in Agda prevents one from writing a
nonsense term such as `` `zero · `suc `zero `` which has no type.  Such
terms that exist independent of types are sometimes called _preterms_
or _raw terms_.  Here we are going to replace the type `Term` of raw
terms by the more sophisticated type `Γ ⊢ A` of inherently typed
terms, which in context `Γ` have type `A`.

While these two choices fit well, they are independent.  One can use
De Bruijn indices in raw terms, or (with more difficulty) have
inherently typed terms with names.  In
Chapter [Untyped]({{ site.baseurl }}{% link out/plta/Untyped.md %},
we will terms that are not typed with De Bruijn indices
are inherently scoped.


## A second example

De Bruijn indices can be tricky to get the hang of, so before
proceeding further let's consider a second example.  Here is the
term that adds two naturals:

    plus : Term
    plus =  μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
             `case ` "m"
               [zero⇒ ` "n"
               |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]
  
Note variable "m" is bound twice, once in a lambda abstraction and once
in the successor branch of the case.  Any appearance of "m" in the successor
branch must refer to the latter binding, due to shadowing.

Here is its corresponding type derivation:

    ⊢plus : ∅ ⊢ plus ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
    ⊢plus = ⊢μ (⊢ƛ (⊢ƛ (⊢case (Ax ∋m) (Ax ∋n)
             (⊢suc (Ax ∋+ · Ax ∋m′ · Ax ∋n′)))))
      where
      ∋+  = (S ("+" ≠ "m") (S ("+" ≠ "n") (S ("+" ≠ "m") Z)))
      ∋m  = (S ("m" ≠ "n") Z)
      ∋n  = Z
      ∋m′ = Z
      ∋n′ = (S ("n" ≠ "m") Z)

The two definitions are in close correspondence, where in addition
to the previous correspondences we have

  * `` `zero `` corresponds to `⊢zero`
  * `` `suc_ `` corresponds to `⊢suc`
  * `` `case_[zero⇒_|suc_⇒_] `` corresponds to `⊢case`
  * `μ_⇒_` corresponds to `⊢μ`

Note the two lookup judgements `∋m` and `∋m′` refer to two different
bindings of variables named `"m"`.  In contrast, the two judgements `∋n` and
`∋n′` both refer to the same binding of `"n"` but accessed in different
contexts, the first where "n" is the last binding in the context, and
the second after "m" is bound in the successor branch of the case.

Here is the term and its type derivation in the notation of this chapter.

    plus : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
    plus = μ ƛ ƛ `case (# 1) (# 0) (`suc (# 3 · # 0 · # 1))

Readering from left to right, each de Bruijn index corresponds to a lookup derivation:

  * `# 1` corresponds to `∋m`
  * `# 0` corresponds to `∋n`
  * `# 3` corresponds to `∋+`
  * `# 0` corresponds to `∋m′`
  * `# 1` corresponds to `∋n′`

The de Bruijn index counts the number of `S` constructs in the
corresponding lookup derivation.  Variable "n" bound in the inner
abstraction is referred to as `# 0` in the zero branch of the case but
as `# 1` in the successor banch of the case, because of the
intervening binding.  Variable "m" bound in the lambda abstraction is
referred to by the first `# 1` in the code, while variable "m" bound
in the successor branch of the case is referred to by the second
`# 0`.  There is no shadowing: with variable names, there is no way to
refer to the former binding in the scope of the latter, but with de
Bruijn indices it could be referred to as `# 2`.


## Inherently typed terms

With two examples under our belt, we can begin our formal development.

First, we get all our infix declarations out of the way.  For ease of reading,
we list operators in order from least tightly binding to most.
\begin{code}
infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_
infix  5 ƛ_
infix  5 μ_
infixr 7 _⇒_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
infix  9 S_
infix  9 #_ 
\end{code}

Since terms are inherently typed, we must define types and contexts
before terms.

### Types

As before, we have just two types, functions and naturals.  The formal definition
is unchanged.
\begin{code}
data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ  : Type
\end{code}
For example,
\begin{code}
_ : Type
_ = (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ
\end{code}
is a type that can be assigned to a Church numeral.

### Contexts

Contexts are as before, but we drop the names.
Contexts are formalised as follows.
\begin{code}
data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context
\end{code}
A context is just a list of types, with the type of the most recently
bound variable on the right.  As before, we let `Γ` and `Δ` range over contexts.
We write `∅` for the empty context, and `Γ , A` for the context `Γ` extended
by type `A`.  For example
\begin{code}
_ : Context
_ = ∅ , `ℕ ⇒ `ℕ , `ℕ
\end{code}
is a context with two variables in scope, where the outer bound one has
type `` `ℕ → `ℕ ``, and the inner bound one has type `` `ℕ ``.

### Variables and the lookup judgement

Inherently typed variables correspond to the lookup judgement.
They are represented by de Bruijn indices, and hence also correspond to natural numbers.
We write

    Γ ∋ A

for variables which in context `Γ` have type `A`.
Their formalisation looks exactly like the old lookup judgement,
but with all names dropped.
\begin{code}
data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
      ----------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A
\end{code}
Constructor `S` no longer requires an additional parameter, since
without names shadowing is no longer an issue.  Now constructors
`Z` and `S` correspond even more closely to the constructors
`here` and `there` for the element-of relation `_∈_` on lists,
as well as to constructors `zero` and `suc` for natural numbers.

For example, consider the following old-style lookup judgements:

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "z" ⦂ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "s" ⦂ `ℕ ⇒ `ℕ ``

They correspond to the following inherently-typed variables.
\begin{code}
_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ∋ `ℕ
_ = Z

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ∋ `ℕ ⇒ `ℕ
_ = S Z
\end{code}
In the given context, `"z"` is represented by `Z`, and `"s"` by `S Z`.

### Terms and the typing judgement

Inherently typed terms correspond to the typing judgement.
We write

    Γ ⊢ A

for terms which in context `Γ` has type `A`.
Their formalisation looks exactly like the old typing judgement,
but with all terms and names dropped.
\begin{code}
data _⊢_ : Context → Type → Set where

  `_ : ∀ {Γ} {A}
    → Γ ∋ A
      ------
    → Γ ⊢ A

  ƛ_  :  ∀ {Γ} {A B}
    → Γ , A ⊢ B
      ----------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ} {A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ----------
    → Γ ⊢ B

  `zero : ∀ {Γ}
      ----------
    → Γ ⊢ `ℕ

  `suc_ : ∀ {Γ}
    → Γ ⊢ `ℕ
      -------
    → Γ ⊢ `ℕ

  `case : ∀ {Γ A}
    → Γ ⊢ `ℕ
    → Γ ⊢ A
    → Γ , `ℕ ⊢ A
      -----------
    → Γ ⊢ A

  μ_ : ∀ {Γ A}
    → Γ , A ⊢ A
      ----------
    → Γ ⊢ A
\end{code}
The definition exploits the close correspondence between the
structure of terms and the structure of a derivation showing that it
is well-typed: now we use the derivation _as_ the term.  For example,
consider the following three terms, building up the Church numeral
two.

For example, consider the following old-style typing judgements:

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "z" ⦂ `ℕ
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" ⦂ `ℕ ⇒ `ℕ
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` ` "s" · ` "z" ⦂  `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" · (` "s" · ` "z") ⦂  `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ ⊢ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) ⦂  `ℕ ⇒ `ℕ ``
* `` ∅ ⊢ ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) ⦂  (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ ``

They correspond to the following inherently-typed terms.
\begin{code}
_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ
_ = ` Z

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ ⇒ `ℕ
_ = ` S Z

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ
_ = ` S Z · ` Z

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ
_ = ` S Z · (` S Z · ` Z)

_ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
_ = ƛ (` S Z · (` S Z · ` Z))

_ : ∅ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ
_ = ƛ ƛ (` S Z · (` S Z · ` Z))
\end{code}
The final inherently-typed term represents the Church numeral two.

### A convenient abbreviation

We can use a natural number to select a type from a context.
\begin{code}
lookup : Context → ℕ → Type
lookup (Γ , A) zero     =  A
lookup (Γ , _) (suc n)  =  lookup Γ n
lookup ∅       _        =  ⊥-elim impossible
  where postulate impossible : ⊥
\end{code}
We intend to apply the function only when the natural is shorter
than the length of the context, which we indicate by postulating
an `impossible` term, just as we did
[here]({{ site.baseurl }}{% link out/plta/Lambda.md %}/#impossible).

Given the above, we can convert a natural to a corresponding
De Bruijn indice, looking up its type in the context.
\begin{code}
count : ∀ {Γ} → (n : ℕ) → Γ ∋ lookup Γ n
count {Γ , _} zero     =  Z
count {Γ , _} (suc n)  =  S (count n)
count {∅}     _        =  ⊥-elim impossible
  where postulate impossible : ⊥
\end{code}
This requires the same trick as before.

We can then introduce a convenient abbreviation for variables.
\begin{code}
#_ : ∀ {Γ} → (n : ℕ) → Γ ⊢ lookup Γ n
# n  =  ` count n
\end{code}

With this abbreviation, we can rewrite the Church numeral two more compactly.
\begin{code}
_ : ∅ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ
_ = ƛ ƛ (# 1 · (# 1 · # 0))
\end{code}


## Test examples

We repeat the test examples from
Chapter [Lambda]({{ site.baseurl }}{% link out/plta/Lambda.md %}).
You can find the 
[here]({{ site.baseurl }}{% link out/plta/Lambda.md %}/#derivation)
for comparison.
\begin{code}
two : ∀ {Γ} → Γ ⊢ `ℕ
two = `suc `suc `zero

plus : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
plus = μ ƛ ƛ `case (` S Z) (` Z) (`suc (` S S S Z · ` Z · ` S Z))

2+2 : ∅ ⊢ `ℕ
2+2 = plus · two · two

Ch : Type → Type
Ch A  =  (A ⇒ A) ⇒ A ⇒ A

plusᶜ : ∀ {Γ A} → Γ ⊢ Ch A ⇒ Ch A ⇒ Ch A
plusᶜ = ƛ ƛ ƛ ƛ ` S S S Z · ` S Z · (` S S Z · ` S Z · ` Z)

twoᶜ : ∀ {Γ A} → Γ ⊢ Ch A
twoᶜ = ƛ ƛ ` S Z · (` S Z · ` Z)

sucᶜ : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ
sucᶜ = ƛ `suc ` Z

2+2ᶜ : ∅ ⊢ `ℕ
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero
\end{code}

## Operational semantics

Simultaneous substitution, a la McBride

## Renaming

\begin{code}
ext : ∀ {Γ Δ}
  → (∀ {B}   →     Γ ∋ B →     Δ ∋ B)
    ----------------------------------
  → (∀ {A B} → Γ , A ∋ B → Δ , A ∋ B)
ext σ Z      =  Z
ext σ (S x)  =  S (σ x)

rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    ------------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename σ (` n)         =  ` σ n
rename σ (ƛ N)           =  ƛ (rename (ext σ) N)
rename σ (L · M)         =  (rename σ L) · (rename σ M)
rename σ (`zero)         =  `zero
rename σ (`suc M)        =  `suc (rename σ M)
rename σ (`case L M N)  =  `case (rename σ L) (rename σ M) (rename (ext σ) N)
rename σ (μ N)           =  μ (rename (ext σ) N)
\end{code}

## Substitution

\begin{code}
exts : ∀ {Γ Δ}
  → (∀ {B}   →     Γ ∋ B →     Δ ⊢ B)
    ----------------------------------
  → (∀ {A B} → Γ , A ∋ B → Δ , A ⊢ B)
exts ρ Z      =  ` Z
exts ρ (S x)  =  rename S_ (ρ x)

subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    ------------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst ρ (` k)         =  ρ k
subst ρ (ƛ N)           =  ƛ (subst (exts ρ) N)
subst ρ (L · M)         =  (subst ρ L) · (subst ρ M)
subst ρ (`zero)         =  `zero
subst ρ (`suc M)        =  `suc (subst ρ M)
subst ρ (`case L M N)  =  `case (subst ρ L) (subst ρ M) (subst (exts ρ) N)
subst ρ (μ N)           =  μ (subst (exts ρ) N)

_[_] : ∀ {Γ A B} → Γ , A ⊢ B → Γ ⊢ A → Γ ⊢ B
_[_] {Γ} {A} N M =  subst {Γ , A} {Γ} ρ N
  where
  ρ : ∀ {B} → Γ , A ∋ B → Γ ⊢ B
  ρ Z      =  M
  ρ (S x)  =  ` x
\end{code}

## Value

\begin{code}
data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  V-zero : ∀ {Γ} →
      -----------------
      Value (`zero {Γ})

  V-suc : ∀ {Γ} {V : Γ ⊢ `ℕ}
    → Value V
      --------------
    → Value (`suc V)
\end{code}

Here `zero` requires an implicit parameter to aid inference (much in the same way that `[]` did in [Lists]({{ site.baseurl }}{% link out/plta/Lists.md %})).

## Reduction step

\begin{code}
infix 2 _↦_

data _↦_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L ↦ L′
      -----------------
    → L · M ↦ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M ↦ M′
      -----------------
    → V · M ↦ V · M′

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
      ---------------------
    → (ƛ N) · W ↦ N [ W ]

  ξ-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
    → M ↦ M′
      -------------------
    → `suc M ↦ `suc M′

  ξ-case : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → L ↦ L′
      -------------------------------
    → `case L M N ↦ `case L′ M N

  β-zero :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
      -----------------------
    → `case `zero M N ↦ M

  β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → Value V
      --------------------------------
    → `case (`suc V) M N ↦ N [ V ]

  β-μ : ∀ {Γ A} {N : Γ , A ⊢ A}
      ------------------
    → μ N ↦ N [ μ N ]
\end{code}

Two possible formulations of `μ`

    μ N  ↦  N [ μ N ]

    (μ N) · V  ↦  N [ μ N , V ]

    (μ (ƛ N)) · V  ↦  N [ μ (ƛ N) , V ]

The first is odd in that we substitute for `f` a term that is not a value.

The second has two values of function type, both lambda abstractions and fixpoints.

    What if the body of μ must first reduce to a value? Two cases.

    Value is a lambda.

    (μ f → N) · V
      ↦  (μ f → ƛ x → N′) · V
      ↦  (ƛ x → N′) [ f := μ f → ƛ x → N ] · V
      ↦  (ƛ x → N′ [ f := μ f → ƛ x → N ]) · V
      ↦  N′ [ f := μ f → ƛ x → N , x := V ]

    Value is itself a mu.

    (μ f → μ g → N) · V
      ↦ (μ f → μ g → N′) · V
      ↦ (μ f → μ g → λ x → N″) · V
      ↦ (μ g → λ x → N″) [ f := μ f → μ g → λ x → N″ ] · V
      ↦ (μ g → λ x → N″ [ f := μ f → μ g → λ x → N″ ]) · V
      ↦ (λ x → N″ [ f := μ f → μ g → λ x → N″ ])
            [ g := μ g → λ x → N″ [ f := μ f → μ g → λ x → N″ ] · V
      ↦ (λ x → N″ [ f := μ f → μ g → λ x → N″ ]
            [ g := μ g → λ x → N″ [ f := μ f → μ g → λ x → N″ ]) · V
      ↦ N″ [ f := μ f → μ g → λ x → N″ ]
             [ g := μ g → λ x → N″ [ f := μ f → μ g → λ x → N″ ]
             [ x := V ]

    This is something you would *never* want to do, because f and g are
    bound to the same function. Better to avoid it by building functions
    into the syntax, I expect.

## Reflexive and transitive closure

\begin{code}
infix  2 _↠_
infix 1 begin_
infixr 2 _↦⟨_⟩_
infix 3 _∎

data _↠_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : ∀ {Γ A} (M : Γ ⊢ A)
      --------
    → M ↠ M

  _↦⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L ↦ M
    → M ↠ N
      ---------
    → L ↠ N

begin_ : ∀ {Γ} {A} {M N : Γ ⊢ A} → (M ↠ N) → (M ↠ N)
begin M↠N = M↠N
\end{code}


## Example reduction sequences

\begin{code}
id : ∀ (A : Type) → ∅ ⊢ A ⇒ A
id A = ƛ ` Z

_ : ∀ {A} → id (A ⇒ A) · id A  ↠ id A
_ =
  begin
    (ƛ ` Z) · (ƛ ` Z)
  ↦⟨ β-ƛ V-ƛ ⟩
    ƛ ` Z
  ∎

_ : plus {∅} · two · two ↠ `suc `suc `suc `suc `zero
_ =
    plus · two · two
  ↦⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ ƛ `case (` S Z) (` Z) (`suc (plus · ` Z · ` S Z))) · two · two
  ↦⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ `case two (` Z) (`suc (plus · ` Z · ` S Z))) · two
  ↦⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    `case two two (`suc (plus · ` Z · two))
  ↦⟨ β-suc (V-suc V-zero) ⟩
    `suc (plus · `suc `zero · two)
  ↦⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc ((ƛ ƛ `case (` S Z) (` Z) (`suc (plus · ` Z · ` S Z)))
      · `suc `zero · two)
  ↦⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
    `suc ((ƛ `case (`suc `zero) (` Z) (`suc (plus · ` Z · ` S Z))) · two)
  ↦⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
    `suc (`case (`suc `zero) (two) (`suc (plus · ` Z · two)))
  ↦⟨ ξ-suc (β-suc V-zero) ⟩
    `suc (`suc (plus · `zero · two))
  ↦⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
    `suc (`suc ((ƛ ƛ `case (` S Z) (` Z) (`suc (plus · ` Z · ` S Z)))
      · `zero · two))
  ↦⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
    `suc (`suc ((ƛ `case `zero (` Z) (`suc (plus · ` Z · ` S Z))) · two))
  ↦⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
    `suc (`suc (`case `zero (two) (`suc (plus · ` Z · two))))
  ↦⟨ ξ-suc (ξ-suc β-zero) ⟩
   `suc (`suc (`suc (`suc `zero)))
  ∎
\end{code}

\begin{code}
_ : plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero ↠ `suc `suc `suc `suc `zero {∅}
_ =
  begin
    plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero
  ↦⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
    (ƛ ƛ ƛ twoᶜ · ` S Z · (` S S Z · ` S Z · ` Z)) · twoᶜ · sucᶜ · `zero
  ↦⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ ƛ twoᶜ · ` S Z · (twoᶜ · ` S Z · ` Z)) · sucᶜ · `zero
  ↦⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ twoᶜ · sucᶜ · (twoᶜ · sucᶜ · ` Z)) · `zero
  ↦⟨ β-ƛ V-zero ⟩
    twoᶜ · sucᶜ · (twoᶜ · sucᶜ · `zero)
  ↦⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ sucᶜ · (sucᶜ · ` Z)) · (twoᶜ · sucᶜ · `zero)
  ↦⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ sucᶜ · (sucᶜ · ` Z)) · ((ƛ sucᶜ · (sucᶜ · ` Z)) · `zero)
  ↦⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ sucᶜ · (sucᶜ · ` Z)) · (sucᶜ · (sucᶜ · `zero))
  ↦⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ V-zero)) ⟩
    (ƛ sucᶜ · (sucᶜ · ` Z)) · (sucᶜ · `suc `zero)
  ↦⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ sucᶜ · (sucᶜ · ` Z)) · `suc (`suc `zero)
  ↦⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    sucᶜ · (sucᶜ · `suc (`suc `zero))
  ↦⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    sucᶜ · `suc (`suc (`suc `zero))
  ↦⟨ β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
    `suc (`suc (`suc (`suc `zero)))
  ∎
\end{code}

## Values do not reduce

Values do not reduce.
\begin{code}
Value-lemma : ∀ {Γ A} {M N : Γ ⊢ A} → Value M → ¬ (M ↦ N)
Value-lemma V-ƛ ()
Value-lemma V-zero ()
Value-lemma (V-suc VM) (ξ-suc M↦N)  =  Value-lemma VM M↦N
\end{code}

As a corollary, terms that reduce are not values.
\begin{code}
↦-corollary : ∀ {Γ A} {M N : Γ ⊢ A} → (M ↦ N) → ¬ Value M
↦-corollary M↦N VM  =  Value-lemma VM M↦N
\end{code}


## Progress

\begin{code}
data Progress {A} (M : ∅ ⊢ A) : Set where
  step : ∀ {N : ∅ ⊢ A}
    → M ↦ N
      -------------
    → Progress M
  done :
      Value M
      ----------
    → Progress M

progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (` ())
progress (ƛ N)                            =  done V-ƛ
progress (L · M) with progress L
...    | step L↦L′                      =  step (ξ-·₁ L↦L′)
...    | done V-ƛ with progress M
...        | step M↦M′                  =  step (ξ-·₂ V-ƛ M↦M′)
...        | done VM                      =  step (β-ƛ VM)
progress (`zero)                          =  done V-zero
progress (`suc M) with progress M
...    | step M↦M′                      =  step (ξ-suc M↦M′)
...    | done VM                          =  done (V-suc VM)
progress (`case L M N) with progress L
...    | step L↦L′                       =  step (ξ-case L↦L′)
...    | done V-zero                         =  step (β-zero)
...    | done (V-suc VL)                     =  step (β-suc VL)
progress (μ N)                             =  step (β-μ)
\end{code}


## Evaluation

By analogy, we will use the name _gas_ for the parameter which puts a
bound on the number of reduction steps.  Gas is specified by a natural number.
\begin{code}
data Gas : Set where
  gas : ℕ → Gas
\end{code}
When our evaluator returns a term `N`, it will either give evidence that
`N` is a value or indicate that it ran out of gas.
\begin{code}
data Finished {Γ A} (N : Γ ⊢ A) : Set where

   done :
       Value N
       ----------
     → Finished N

   out-of-gas :
       ----------
       Finished N
\end{code}
Given a term `L` of type `A`, the evaluator will, for some `N`, return
a reduction sequence from `L` to `N` and an indication of whether
reduction finished.
\begin{code}
data Steps : ∀ {A} → ∅ ⊢ A → Set where

  steps : ∀ {A} {L N : ∅ ⊢ A}
    → L ↠ N
    → Finished N
      ----------
    → Steps L
\end{code}
The evaluator takes gas and evidence that a term is well-typed,
and returns the corresponding steps.
\begin{code}
eval : ∀ {A}
  → Gas
  → (L : ∅ ⊢ A)
    -----------
  → Steps L
eval (gas zero)    L                     =  steps (L ∎) out-of-gas
eval (gas (suc m)) L with progress L
... | done VL                            =  steps (L ∎) (done VL)
... | step {M} L↦M with eval (gas m) M
...    | steps M↠N fin                   =  steps (L ↦⟨ L↦M ⟩ M↠N) fin
\end{code}

## Examples

\begin{code}
_ : eval (gas 100) (plus · two · two) ≡
  steps
  ((μ
    (ƛ
     (ƛ
      `case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
   · `suc (`suc `zero)
   · `suc (`suc `zero)
   ↦⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
   (ƛ
    (ƛ
     `case (` (S Z)) (` Z)
     (`suc
      ((μ
        (ƛ
         (ƛ
          `case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
       · ` Z
       · ` (S Z)))))
   · `suc (`suc `zero)
   · `suc (`suc `zero)
   ↦⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
   (ƛ
    `case (`suc (`suc `zero)) (` Z)
    (`suc
     ((μ
       (ƛ
        (ƛ
         `case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
      · ` Z
      · ` (S Z))))
   · `suc (`suc `zero)
   ↦⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
   `case (`suc (`suc `zero)) (`suc (`suc `zero))
   (`suc
    ((μ
      (ƛ
       (ƛ
        `case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
     · ` Z
     · `suc (`suc `zero)))
   ↦⟨ β-suc (V-suc V-zero) ⟩
   `suc
   ((μ
     (ƛ
      (ƛ
       `case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · `suc `zero
    · `suc (`suc `zero))
   ↦⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
   `suc
   ((ƛ
     (ƛ
      `case (` (S Z)) (` Z)
      (`suc
       ((μ
         (ƛ
          (ƛ
           `case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
        · ` Z
        · ` (S Z)))))
    · `suc `zero
    · `suc (`suc `zero))
   ↦⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
   `suc
   ((ƛ
     `case (`suc `zero) (` Z)
     (`suc
      ((μ
        (ƛ
         (ƛ
          `case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
       · ` Z
       · ` (S Z))))
    · `suc (`suc `zero))
   ↦⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
   `suc
   `case (`suc `zero) (`suc (`suc `zero))
   (`suc
    ((μ
      (ƛ
       (ƛ
        `case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
     · ` Z
     · `suc (`suc `zero)))
   ↦⟨ ξ-suc (β-suc V-zero) ⟩
   `suc
   (`suc
    ((μ
      (ƛ
       (ƛ
        `case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
     · `zero
     · `suc (`suc `zero)))
   ↦⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
   `suc
   (`suc
    ((ƛ
      (ƛ
       `case (` (S Z)) (` Z)
       (`suc
        ((μ
          (ƛ
           (ƛ
            `case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
         · ` Z
         · ` (S Z)))))
     · `zero
     · `suc (`suc `zero)))
   ↦⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
   `suc
   (`suc
    ((ƛ
      `case `zero (` Z)
      (`suc
       ((μ
         (ƛ
          (ƛ
           `case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
        · ` Z
        · ` (S Z))))
     · `suc (`suc `zero)))
   ↦⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
   `suc
   (`suc
    `case `zero (`suc (`suc `zero))
    (`suc
     ((μ
       (ƛ
        (ƛ
         `case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
      · ` Z
      · `suc (`suc `zero))))
   ↦⟨ ξ-suc (ξ-suc β-zero) ⟩ `suc (`suc (`suc (`suc `zero))) ∎)
  (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
_ = refl
\end{code}

\begin{code}
_ : eval (gas 100) (plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero) ≡
  steps
  ((ƛ
    (ƛ
     (ƛ (ƛ ` (S (S (S Z))) · ` (S Z) · (` (S (S Z)) · ` (S Z) · ` Z)))))
   · (ƛ (ƛ ` (S Z) · (` (S Z) · ` Z)))
   · (ƛ (ƛ ` (S Z) · (` (S Z) · ` Z)))
   · (ƛ `suc (` Z))
   · `zero
   ↦⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
   (ƛ
    (ƛ
     (ƛ
      (ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · ` (S Z) ·
      (` (S (S Z)) · ` (S Z) · ` Z))))
   · (ƛ (ƛ ` (S Z) · (` (S Z) · ` Z)))
   · (ƛ `suc (` Z))
   · `zero
   ↦⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
   (ƛ
    (ƛ
     (ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · ` (S Z) ·
     ((ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · ` (S Z) · ` Z)))
   · (ƛ `suc (` Z))
   · `zero
   ↦⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
   (ƛ
    (ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · (ƛ `suc (` Z)) ·
    ((ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · (ƛ `suc (` Z)) · ` Z))
   · `zero
   ↦⟨ β-ƛ V-zero ⟩
   (ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · (ƛ `suc (` Z)) ·
   ((ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · (ƛ `suc (` Z)) · `zero)
   ↦⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
   (ƛ (ƛ `suc (` Z)) · ((ƛ `suc (` Z)) · ` Z)) ·
   ((ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · (ƛ `suc (` Z)) · `zero)
   ↦⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
   (ƛ (ƛ `suc (` Z)) · ((ƛ `suc (` Z)) · ` Z)) ·
   ((ƛ (ƛ `suc (` Z)) · ((ƛ `suc (` Z)) · ` Z)) · `zero)
   ↦⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
   (ƛ (ƛ `suc (` Z)) · ((ƛ `suc (` Z)) · ` Z)) ·
   ((ƛ `suc (` Z)) · ((ƛ `suc (` Z)) · `zero))
   ↦⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ V-zero)) ⟩
   (ƛ (ƛ `suc (` Z)) · ((ƛ `suc (` Z)) · ` Z)) ·
   ((ƛ `suc (` Z)) · `suc `zero)
   ↦⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc V-zero)) ⟩
   (ƛ (ƛ `suc (` Z)) · ((ƛ `suc (` Z)) · ` Z)) · `suc (`suc `zero) ↦⟨
   β-ƛ (V-suc (V-suc V-zero)) ⟩
   (ƛ `suc (` Z)) · ((ƛ `suc (` Z)) · `suc (`suc `zero)) ↦⟨
   ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
   (ƛ `suc (` Z)) · `suc (`suc (`suc `zero)) ↦⟨
   β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
   `suc (`suc (`suc (`suc `zero))) ∎)
  (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
_ = refl
\end{code}
