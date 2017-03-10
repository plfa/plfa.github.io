---
title         : "Maps: Total and Partial Maps"
layout        : default
hide-implicit : false
extra-script : [agda-extra-script.html]
extra-style  : [agda-extra-style.html]
permalink     : "sf/Maps.html"
---

# Maps: Total and Partial Maps

Maps (or dictionaries) are ubiquitous data structures, both in
software construction generally and in the theory of programming
languages in particular; we're going to need them in many places in
the coming chapters.  They also make a nice case study using ideas
we've seen in previous chapters, including building data structures
out of higher-order functions (from [Basics](sf/Basics.html)
and [Poly](sf/Poly.html) and the use of reflection to streamline
proofs (from [IndProp](sf/IndProp.html).

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
directly from Agda's standard library stuff.  You should not notice
much difference, though, because we've been careful to name our
own definitions and theorems the same as their counterparts in the
standard library, wherever they overlap.

\begin{code}
open import Function         using (_∘_)
open import Data.Bool        using (Bool; true; false)
open import Data.Empty       using (⊥; ⊥-elim)
open import Data.Maybe       using (Maybe; just; nothing)
open import Data.Nat         using (ℕ)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
\end{code}

Documentation for the standard library can be found at
<https://agda.github.io/agda-stdlib/>.

## Identifiers

First, we need a type for the keys that we use to index into our
maps.  For this purpose, we again use the type Id` from the
[Lists](sf/Lists.html) chapter.  To make this chapter self contained,
we repeat its definition here, together with the equality comparison
function for ids and its fundamental property.

\begin{code}
data Id : Set where
  id : ℕ → Id
\end{code}

\begin{code}
_≟_ : (x y : Id) → Dec (x ≡ y)
id x ≟ id y with x Data.Nat.≟ y
id x ≟ id y | yes x=y rewrite x=y = yes refl
id x ≟ id y | no  x≠y = no (x≠y ∘ id-inj)
  where
    id-inj : ∀ {x y} → id x ≡ id y → x ≡ y
    id-inj refl = refl
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

Intuitively, a total map over anﬁ element type $$A$$ _is_ just a
function that can be used to look up ids, yielding $$A$$s.

\begin{code}
module TotalMap where
\end{code}

The function `empty` yields an empty total map, given a
default element; this map always returns the default element when
applied to any id.

\begin{code}
  empty : ∀ {A} → A → TotalMap A
  empty x = λ _ → x
\end{code}

More interesting is the `update` function, which (as before) takes
a map $$m$$, a key $$x$$, and a value $$v$$ and returns a new map that
takes $$x$$ to $$v$$ and takes every other key to whatever $$m$$ does.

\begin{code}
  update : ∀ {A} → TotalMap A -> Id -> A -> TotalMap A
  update m x v y with x ≟ y
  ... | yes x=y = v
  ... | no  x≠y = m y
\end{code}

This definition is a nice example of higher-order programming.
The `update` function takes a _function_ $$m$$ and yields a new
function $$\lambda x'.\vdots$$ that behaves like the desired map.

For example, we can build a map taking ids to bools, where `id
3` is mapped to `true` and every other key is mapped to `false`,
like this:

\begin{code}
  examplemap : TotalMap Bool
  examplemap = update (update (empty false) (id 1) false) (id 3) true
\end{code}

This completes the definition of total maps.  Note that we don't
need to define a `find` operation because it is just function
application!

\begin{code}
  test_examplemap0 : examplemap (id 0) ≡ false
  test_examplemap0 = refl

  test_examplemap1 : examplemap (id 1) ≡ false
  test_examplemap1 = refl

  test_examplemap2 : examplemap (id 2) ≡ false
  test_examplemap2 = refl

  test_examplemap3 : examplemap (id 3) ≡ true
  test_examplemap3 = refl
\end{code}

To use maps in later chapters, we'll need several fundamental
facts about how they behave.  Even if you don't work the following
exercises, make sure you thoroughly understand the statements of
the lemmas!  (Some of the proofs require the functional
extensionality axiom, which is discussed in the [Logic]
chapter and included in the Agda standard library.)

#### Exercise: 1 star, optional (apply-empty)
First, the empty map returns its default element for all keys:

\begin{code}
  postulate
    apply-empty : ∀ {A x v} → empty {A} v x ≡ v
\end{code}

<div class="hidden">
\begin{code}
  apply-empty′ : ∀ {A x v} → empty {A} v x ≡ v
  apply-empty′ = refl
\end{code}
</div>

#### Exercise: 2 stars, optional (update-eq)
Next, if we update a map $$m$$ at a key $$x$$ with a new value $$v$$
and then look up $$x$$ in the map resulting from the `update`, we get
back $$v$$:

\begin{code}
  postulate
    update-eq : ∀ {A v} (m : TotalMap A) (x : Id)
              → (update m x v) x ≡ v
\end{code}

<div class="hidden">
\begin{code}
  update-eq′ : ∀ {A v} (m : TotalMap A) (x : Id)
             → (update m x v) x ≡ v
  update-eq′ m x with x ≟ x
  ... | yes x=x = refl
  ... | no  x≠x = ⊥-elim (x≠x refl)
\end{code}
</div>

#### Exercise: 2 stars, optional (update-neq)
On the other hand, if we update a map $$m$$ at a key $$x$$ and
then look up a _different_ key $$y$$ in the resulting map, we get
the same result that $$m$$ would have given:

\begin{code}
  update-neq : ∀ {A v} (m : TotalMap A) (x y : Id)
             → x ≢ y → (update m x v) y ≡ m y
  update-neq m x y x≠y with x ≟ y
  ... | yes x=y = ⊥-elim (x≠y x=y)
  ... | no  _   = refl
\end{code}

#### Exercise: 2 stars, optional (update-shadow)
If we update a map $$m$$ at a key $$x$$ with a value $$v_1$$ and then
update again with the same key $$x$$ and another value $$v_2$$, the
resulting map behaves the same (gives the same result when applied
to any key) as the simpler map obtained by performing just
the second `update` on $$m$$:

\begin{code}
  postulate
    update-shadow : ∀ {A v1 v2} (m : TotalMap A) (x y : Id)
                  → (update (update m x v1) x v2) y ≡ (update m x v2) y
\end{code}

<div class="hidden">
\begin{code}
  update-shadow′ : ∀ {A v1 v2} (m : TotalMap A) (x y : Id)
                 → (update (update m x v1) x v2) y ≡ (update m x v2) y
  update-shadow′ m x y
      with x ≟ y
  ... | yes x=y = refl
  ... | no  x≠y = update-neq m x y x≠y
\end{code}
</div>

#### Exercise: 2 stars (update-same)
Prove the following theorem, which states that if we update a map to
assign key $$x$$ the same value as it already has in $$m$$, then the
result is equal to $$m$$:

\begin{code}
  postulate
    update-same : ∀ {A} (m : TotalMap A) (x y : Id)
                → (update m x (m x)) y ≡ m y
\end{code}

<div class="hidden">
\begin{code}
  update-same′ : ∀ {A} (m : TotalMap A) (x y : Id)
               → (update m x (m x)) y ≡ m y
  update-same′ m x y
    with x ≟ y
  ... | yes x=y rewrite x=y = refl
  ... | no  x≠y = refl
\end{code}
</div>

#### Exercise: 3 stars, recommended (update-permute)
Prove one final property of the `update` function: If we update a map
$$m$$ at two distinct keys, it doesn't matter in which order we do the
updates.

\begin{code}
  postulate
    update-permute : ∀ {A v1 v2} (m : TotalMap A) (x1 x2 y : Id)
                   → x1 ≢ x2 → (update (update m x2 v2) x1 v1) y
                             ≡ (update (update m x1 v1) x2 v2) y
\end{code}

<div class="hidden">
\begin{code}
  update-permute′ : ∀ {A v1 v2} (m : TotalMap A) (x1 x2 y : Id)
                  → x1 ≢ x2 → (update (update m x2 v2) x1 v1) y
                            ≡ (update (update m x1 v1) x2 v2) y
  update-permute′ {A} {v1} {v2} m x1 x2 y x1≠x2
    with x1 ≟ y | x2 ≟ y
  ... | yes x1=y | yes x2=y = ⊥-elim (x1≠x2 (trans x1=y (sym x2=y)))
  ... | no  x1≠y | yes x2=y rewrite x2=y = update-eq′ m y
  ... | yes x1=y | no  x2≠y rewrite x1=y = sym (update-eq′ m y)
  ... | no  x1≠y | no  x2≠y =
    trans (update-neq m x2 y x2≠y) (sym (update-neq m x1 y x1≠y))
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
  empty : ∀ {A} → PartialMap A
  empty = TotalMap.empty nothing
\end{code}

\begin{code}
  update : ∀ {A} (m : PartialMap A) (x : Id) (v : A) → PartialMap A
  update m x v = TotalMap.update m x (just v)
\end{code}

We can now lift all of the basic lemmas about total maps to
partial maps.

\begin{code}
  update-eq : ∀ {A v} (m : PartialMap A) (x : Id)
            → (update m x v) x ≡ just v
  update-eq m x = TotalMap.update-eq m x
\end{code}

\begin{code}
  update-neq : ∀ {A v} (m : PartialMap A) (x y : Id)
             → x ≢ y → (update m x v) y ≡ m y
  update-neq m x y x≠y = TotalMap.update-neq m x y x≠y
\end{code}

\begin{code}
  update-shadow : ∀ {A v1 v2} (m : PartialMap A) (x y : Id)
                → (update (update m x v1) x v2) y ≡ (update m x v2) y
  update-shadow m x y = TotalMap.update-shadow m x y
\end{code}

\begin{code}
  update-same : ∀ {A v} (m : PartialMap A) (x y : Id)
              → m x ≡ just v
              → (update m x v) y ≡ m y
  update-same m x y mx=v rewrite sym mx=v = TotalMap.update-same m x y
\end{code}

\begin{code}
  update-permute : ∀ {A v1 v2} (m : PartialMap A) (x1 x2 y : Id)
                 → x1 ≢ x2 → (update (update m x2 v2) x1 v1) y
                           ≡ (update (update m x1 v1) x2 v2) y
  update-permute m x1 x2 y x1≠x2 = TotalMap.update-permute m x1 x2 y x1≠x2
\end{code}
