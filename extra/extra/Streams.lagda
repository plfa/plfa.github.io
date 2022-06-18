---
title     : "Streams: Streams and coinduction"
permalink : /Streams
---

This chapter introduces streams and coinduction.

## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Coinduction using (∞; ♯_; ♭)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
\end{code}

We assume [extensionality][extensionality].
\begin{code}
postulate
  extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g
\end{code}

[extensionality]: Equality/index.html#extensionality


## Streams

Streams are defined in Agda as follows.
\begin{code}
record Stream (A : Set) : Set where
  coinductive
  field
    hd : A
    tl : Stream A

open Stream
\end{code}

A constructor for streams may be defined via *co-pattern matching*.
\begin{code}
infixr 5 _∷_

_∷_ : ∀ {A : Set} → A → Stream A → Stream A
hd (x ∷ xs)  =  x
tl (x ∷ xs)  =  xs
\end{code}

\begin{code}
even : ∀ {A} → Stream A → Stream A
hd (even x) = hd x
tl (even x) = even (tl (tl x))
\end{code}

## Lifting

\begin{code}
record Lift (A : Set) : Set where
  coinductive
  field
    force : A

open Lift
\end{code}

\begin{code}
delay : ∀ {A : Set} → A → Lift A
force (delay x)  =  x
\end{code}

## Alternative definition of stream

\begin{code}
data Stream′ (A : Set) : Set where
  _∷′_ : A → ∞ (Stream′ A) → Stream′ A

hd′ : ∀ {A} → Stream′ A → A
hd′ (x ∷′ xs)  =  x

tl′ : ∀ {A} → Stream′ A → Stream′ A
tl′ (x ∷′ xs)  =  ♭ xs
\end{code}

## Maps between the two definitions

\begin{code}
to : ∀ {A} → Stream A → Stream′ A
to xs = hd xs ∷′ ♯ (to (tl xs))

from : ∀ {A} → Stream′ A → Stream A
hd (from (x ∷′ xs′)) = x
tl (from (x ∷′ xs′)) = from (♭ xs′)
\end{code}

Termination check does not succeed if I replace `∞`, `♯`, `♭` by `Lift`,
`delay`, `force`.

Trying to show full-blown isomorphism appears difficult.

## How to be lazy without even being odd

This is the approach hinted at by Abel in his [lecture].

[lecture]: https://cs.ioc.ee/~tarmo/tsem12/abel-slides.pdf

\begin{code}
record EStream (A : Set) : Set
data OStream (A : Set) : Set

record EStream (A : Set) where
  coinductive
  field
    force : OStream A

open EStream

data OStream (A : Set) where
  cons : A → EStream A → OStream A
\end{code}

Type `OStream` can also include a `nil` clause, if needed.

## Conversions between `Stream` and `EStream`.

\begin{code}
toE : ∀ {A} → Stream A → EStream A
force (toE xs) = cons (hd xs) (toE (tl xs))

fromE : ∀ {A} → EStream A → Stream A
hd (fromE xs′) with force xs′
...               | cons x xs″ = x
tl (fromE xs′) with force xs′
...               | cons x xs″ = fromE xs″

record _∼_ {A : Set} (xs : Stream A) (ys : Stream A) : Set where
  coinductive
  field
    hd-∼ : hd xs ≡ hd ys
    tl-∼ : tl xs ∼ tl ys

open _∼_

record _≈_ {A : Set} (xs′ ys′ : EStream A) : Set
_≋_ : ∀ {A : Set} (xs″ ys″ : OStream A) → Set

record _≈_ {A : Set} (xs′ ys′ : EStream A) where
  coinductive
  field
    force-≈ : force xs′ ≋ force ys′

open _≈_

cons x xs ≋ cons y ys = (x ≡ y) × (xs ≈ ys)

fromE∘toE : ∀ {A} (xs : Stream A) → fromE (toE xs) ∼ xs
hd-∼ (fromE∘toE xs) = refl
tl-∼ (fromE∘toE xs) = fromE∘toE (tl xs)

toE∘fromE : ∀ {A} (xs′ : EStream A) → toE (fromE xs′) ≈ xs′
force-≈ (toE∘fromE xs′) with force xs′
...                        | cons x xs  =  ⟨ refl , toE∘fromE xs ⟩
\end{code}

## Standard Library

Definitions similar to those in this chapter can be found in the standard library.
\begin{code}
\end{code}


## Unicode

This chapter uses the following unicode.

    ∷  U+2237  PROPORTION  (\::)
    ⊗  U+2297  CIRCLED TIMES  (\otimes)
    ∈  U+2208  ELEMENT OF  (\in)
    ∉  U+2209  NOT AN ELEMENT OF  (\inn)
