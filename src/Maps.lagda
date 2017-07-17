---
title     : "Maps: Total and Partial Maps"
layout    : page
permalink : /Maps
---

Maps (or dictionaries) are ubiquitous data structures, both in software
construction generally and in the theory of programming languages in particular;
we're going to need them in many places in the coming chapters.  They also make
a nice case study using ideas we've seen in previous chapters, including
building data structures out of higher-order functions (from [Basics]({{
"Basics" | relative_url }}) and [Poly]({{ "Poly" | relative_url }}) and the use
of reflection to streamline proofs (from [IndProp]({{ "IndProp" | relative_url
}})).

We'll define two flavors of maps: _total_ maps, which include a
"default" element to be returned when a key being looked up
doesn't exist, and _partial_ maps, which return an `Maybe` to
indicate success or failure.  The latter is defined in terms of
the former, using `nothing` as the default element.

## The Agda Standard Library

One small digression before we start.

Unlike the chapters we have seen so far, this one does not
import the chapter before it (and, transitively, all the
earlier chapters).  Instead, in this chapter and from now, on
we're going to import the definitions and theorems we need
directly from Agda's standard library.  You should not notice
much difference, though, because we've been careful to name our
own definitions and theorems the same as their counterparts in the
standard library, wherever they overlap.

\begin{code}
open import Data.Nat         using (ℕ)
open import Data.Empty       using (⊥; ⊥-elim)
open import Data.Maybe       using (Maybe; just; nothing)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
                             using (_≡_; refl; _≢_; trans; sym)
\end{code}

Documentation for the standard library can be found at
<https://agda.github.io/agda-stdlib/>.

## Identifiers

First, we need a type for the keys that we use to index into our
maps.  For this purpose, we again use the type `Id` from the
[Lists](sf/Lists.html) chapter.  To make this chapter self contained,
we repeat its definition here.

\begin{code}
data Id : Set where
  id : ℕ → Id
\end{code}

We recall a standard fact of logic.

\begin{code}
contrapositive : ∀ {ℓ₁ ℓ₂} {P : Set ℓ₁} {Q : Set ℓ₂} → (P → Q) → (¬ Q → ¬ P)
contrapositive p→q ¬q p = ¬q (p→q p)
\end{code}

Using the above, we can decide equality of two identifiers
by deciding equality on the underlying strings.

\begin{code}
_≟_ : (x y : Id) → Dec (x ≡ y)
id x ≟ id y with x Data.Nat.≟ y
id x ≟ id y | yes refl  =  yes refl
id x ≟ id y | no  x≢y   =  no (contrapositive id-inj x≢y)
  where
    id-inj : ∀ {x y} → id x ≡ id y → x ≡ y
    id-inj refl  =  refl
\end{code}

## Total Maps

Our main job in this chapter will be to build a definition of
partial maps that is similar in behavior to the one we saw in the
[Lists](sf/Lists.html) chapter, plus accompanying lemmas about their
behavior.

This time around, though, we're going to use _functions_, rather
than lists of key-value pairs, to build maps.  The advantage of
this representation is that it offers a more _extensional_ view of
maps, where two maps that respond to queries in the same way will
be represented as literally the same thing (the same function),
rather than just "equivalent" data structures.  This, in turn,
simplifies proofs that use maps.

We build partial maps in two steps.  First, we define a type of
_total maps_ that return a default value when we look up a key
that is not present in the map.

\begin{code}
TotalMap : Set → Set
TotalMap A = Id → A
\end{code}

Intuitively, a total map over anﬁ element type `A` _is_ just a
function that can be used to look up ids, yielding `A`s.

\begin{code}
module TotalMap where
\end{code}

The function `always` yields a total map given a
default element; this map always returns the default element when
applied to any id.

\begin{code}
  always : ∀ {A} → A → TotalMap A
  always v x = v
\end{code}

More interesting is the update function, which (as before) takes
a map `ρ`, a key `x`, and a value `v` and returns a new map that
takes `x` to `v` and takes every other key to whatever `ρ` does.

\begin{code}
  infixl 15 _,_↦_  

  _,_↦_ : ∀ {A} → TotalMap A → Id → A → TotalMap A
  (ρ , x ↦ v) y with x ≟ y
  ... | yes x≡y = v
  ... | no  x≢y = ρ y
\end{code}

This definition is a nice example of higher-order programming.
The update function takes a _function_ `ρ` and yields a new
function that behaves like the desired map.

For example, we can build a map taking ids to naturals, where `x`
maps to 42, `y` maps to 69, and every other key maps to 0, as follows:

\begin{code}
  module example where

    x y z : Id
    x = id 0
    y = id 1
    z = id 2

    ρ₀ : TotalMap ℕ
    ρ₀ = always 0 , x ↦ 42 , y ↦ 69

    test₁ : ρ₀ x ≡ 42
    test₁ = refl

    test₂ : ρ₀ y ≡ 69
    test₂ = refl

    test₃ : ρ₀ z ≡ 0
    test₃ = refl
\end{code}

This completes the definition of total maps.  Note that we don't
need to define a `find` operation because it is just function
application!

To use maps in later chapters, we'll need several fundamental
facts about how they behave.  Even if you don't work the following
exercises, make sure you understand the statements of
the lemmas!

#### Exercise: 1 star, optional (apply-always)
The `always` map returns its default element for all keys:

\begin{code}
  postulate
    apply-always : ∀ {A} (v : A) (x : Id) → always v x ≡ v
\end{code}

<div class="hidden">
\begin{code}
  apply-always′ : ∀ {A} (v : A) (x : Id) → always v x ≡ v
  apply-always′ v x = refl
\end{code}
</div>

#### Exercise: 2 stars, optional (update-eq)
Next, if we update a map `ρ` at a key `x` with a new value `v`
and then look up `x` in the map resulting from the update, we get
back `v`:

\begin{code}
  postulate
    update-eq : ∀ {A} (ρ : TotalMap A) (x : Id) (v : A)
              → (ρ , x ↦ v) x ≡ v
\end{code}

<div class="hidden">
\begin{code}
  update-eq′ : ∀ {A} (ρ : TotalMap A) (x : Id) (v : A)
             → (ρ , x ↦ v) x ≡ v
  update-eq′ ρ x v with x ≟ x
  ... | yes x≡x = refl
  ... | no  x≢x = ⊥-elim (x≢x refl)
\end{code}
</div>

#### Exercise: 2 stars, optional (update-neq)
On the other hand, if we update a map `m` at a key `x` and
then look up a _different_ key `y` in the resulting map, we get
the same result that `m` would have given:

\begin{code}
  update-neq : ∀ {A} (ρ : TotalMap A) (x : Id) (v : A) (y : Id)
             → x ≢ y → (ρ , x ↦ v) y ≡ ρ y
  update-neq ρ x v y x≢y with x ≟ y
  ... | yes x≡y = ⊥-elim (x≢y x≡y)
  ... | no  _   = refl
\end{code}

For the following lemmas, since maps are represented by functions, to
show two maps equal we will need to postulate extensionality.

\begin{code}
  postulate
    extensionality : ∀ {A : Set} {ρ ρ′ : TotalMap A} → (∀ x → ρ x ≡ ρ′ x) → ρ ≡ ρ′
\end{code}

#### Exercise: 2 stars, optional (update-shadow)
If we update a map `ρ` at a key `x` with a value `v` and then
update again with the same key `x` and another value `w`, the
resulting map behaves the same (gives the same result when applied
to any key) as the simpler map obtained by performing just
the second update on `ρ`:

\begin{code}
  postulate
    update-shadow : ∀ {A} (ρ : TotalMap A) (x : Id) (v w : A) 
                  → (ρ , x ↦ v , x ↦ w) ≡ (ρ , x ↦ w)
\end{code}

<div class="hidden">
\begin{code}
  update-shadow′ :  ∀ {A} (ρ : TotalMap A) (x : Id) (v w : A) 
                  → ((ρ , x ↦ v) , x ↦ w) ≡ (ρ , x ↦ w)
  update-shadow′ ρ x v w = extensionality lemma
    where
    lemma : ∀ y → ((ρ , x ↦ v) , x ↦ w) y ≡ (ρ , x ↦ w) y
    lemma y with x ≟ y
    ... | yes refl = refl
    ... | no  x≢y  = update-neq ρ x v y x≢y
\end{code}
</div>

#### Exercise: 2 stars (update-same)
Prove the following theorem, which states that if we update a map `ρ` to
assign key `x` the same value as it already has in `ρ`, then the
result is equal to `ρ`:

\begin{code}
  postulate
    update-same : ∀ {A} (ρ : TotalMap A) (x : Id) → (ρ , x ↦ ρ x) ≡ ρ
\end{code}

<div class="hidden">
\begin{code}
  update-same′ : ∀ {A} (ρ : TotalMap A) (x : Id) → (ρ , x ↦ ρ x) ≡ ρ
  update-same′ ρ x  =  extensionality lemma
    where
    lemma : ∀ y → (ρ , x ↦ ρ x) y ≡ ρ y
    lemma y with x ≟ y
    ... | yes refl = refl
    ... | no  x≢y  = refl
\end{code}
</div>

#### Exercise: 3 stars, recommended (update-permute)
Prove one final property of the `update` function: If we update a map
`m` at two distinct keys, it doesn't matter in which order we do the
updates.

\begin{code}
  postulate
    update-permute : ∀ {A} (ρ : TotalMap A) (x : Id) (v : A) (y : Id) (w : A)
                   → x ≢ y → (ρ , x ↦ v , y ↦ w) ≡ (ρ , y ↦ w , x ↦ v)
\end{code}

<div class="hidden">
\begin{code}
  update-permute′ : ∀ {A} (ρ : TotalMap A) (x : Id) (v : A) (y : Id) (w : A)
                   → x ≢ y → (ρ , x ↦ v , y ↦ w) ≡ (ρ , y ↦ w , x ↦ v)
  update-permute′ {A} ρ x v y w x≢y  =  extensionality lemma
    where
    lemma : ∀ z → (ρ , x ↦ v , y ↦ w) z ≡ (ρ , y ↦ w , x ↦ v) z
    lemma z with x ≟ z | y ≟ z
    ... | yes refl | yes refl  =  ⊥-elim (x≢y refl)
    ... | no  x≢z  | yes refl  =  sym (update-eq′ ρ z w)
    ... | yes refl | no  y≢z   =  update-eq′ ρ z v
    ... | no  x≢z  | no  y≢z   =  trans (update-neq ρ x v z x≢z) (sym (update-neq ρ y w z y≢z))  
\end{code}

And a slightly different version of the same proof.

\begin{code}  
  update-permute′′ : ∀ {A} (ρ : TotalMap A) (x : Id) (v : A) (y : Id) (w : A) (z : Id)
                   → x ≢ y → (ρ , x ↦ v , y ↦ w) z ≡ (ρ , y ↦ w , x ↦ v) z
  update-permute′′ {A} ρ x v y w z x≢y with x ≟ z | y ≟ z
  ... | yes x≡z | yes y≡z = ⊥-elim (x≢y (trans x≡z (sym y≡z)))
  ... | no  x≢z | yes y≡z rewrite y≡z  =  sym (update-eq′ ρ z w)  
  ... | yes x≡z | no  y≢z rewrite x≡z  =  update-eq′ ρ z v
  ... | no  x≢z | no  y≢z  =  trans (update-neq ρ x v z x≢z) (sym (update-neq ρ y w z y≢z))  
\end{code}
</div>

## Partial maps

Finally, we define _partial maps_ on top of total maps.  A partial
map with elements of type `A` is simply a total map with elements
of type `Maybe A` and default element `nothing`.

\begin{code}
PartialMap : Set → Set
PartialMap A = TotalMap (Maybe A)
\end{code}

\begin{code}
module PartialMap where
\end{code}

\begin{code}
  ∅ : ∀ {A} → PartialMap A
  ∅ = TotalMap.always nothing
\end{code}

\begin{code}
  infixl 15 _,_↦_  

  _,_↦_ : ∀ {A} (ρ : PartialMap A) (x : Id) (v : A) → PartialMap A
  ρ , x ↦ v = TotalMap._,_↦_ ρ x (just v)
\end{code}

We now lift all of the basic lemmas about total maps to partial maps.

\begin{code}
  apply-∅ : ∀ {A} → (x : Id) → (∅ {A} x) ≡ nothing
  apply-∅ x  = TotalMap.apply-always nothing x
\end{code}

\begin{code}
  update-eq : ∀ {A} (ρ : PartialMap A) (x : Id) (v : A)
            → (ρ , x ↦ v) x ≡ just v
  update-eq ρ x v = TotalMap.update-eq ρ x (just v)
\end{code}

\begin{code}
  update-neq : ∀ {A} (ρ : PartialMap A) (x : Id) (v : A) (y : Id)
             → x ≢ y → (ρ , x ↦ v) y ≡ ρ y
  update-neq ρ x v y x≢y = TotalMap.update-neq ρ x (just v) y x≢y
\end{code}

\begin{code}
  update-shadow : ∀ {A} (ρ : PartialMap A) (x : Id) (v w : A) 
                → (ρ , x ↦ v , x ↦ w) ≡ (ρ , x ↦ w)
  update-shadow ρ x v w = TotalMap.update-shadow ρ x (just v) (just w)
\end{code}

\begin{code}
  update-same : ∀ {A} (ρ : PartialMap A) (x : Id) (v : A) 
              → ρ x ≡ just v
              → (ρ , x ↦ v) ≡ ρ
  update-same ρ x v ρx≡v rewrite sym ρx≡v = TotalMap.update-same ρ x
\end{code}

\begin{code}
  update-permute : ∀ {A} (ρ : PartialMap A) (x : Id) (v : A) (y : Id) (w : A) 
                 → x ≢ y → (ρ , x ↦ v , y ↦ w) ≡ (ρ , y ↦ w , x ↦ v)
  update-permute ρ x v y w x≢y = TotalMap.update-permute ρ x (just v) y (just w) x≢y
\end{code}

We will also need the following basic facts about the `Maybe` type.

\begin{code}
  just≢nothing : ∀ {X : Set} → ∀ {x : X} → ¬ (_≡_ {A = Maybe X} (just x) nothing)
  just≢nothing ()

  just-injective : ∀ {X : Set} {x y : X} → _≡_ {A = Maybe X} (just x) (just y) → x ≡ y
  just-injective refl = refl
\end{code}
