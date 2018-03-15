---
title     : "Negation: Negation, with Classical and Intuitionistic Logic"
layout    : page
permalink : /Negation
---

## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Isomorphism using (_≃_; ≃-sym; ≃-trans; _≲_)
open Isomorphism.≃-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties.Simple using (+-suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_)
\end{code}


## Negation

Given a proposition `A`, the negation `¬ A` holds if `A` cannot hold.
We formalise this idea by declaring negation to be the same
as implication of false. 
\begin{code}
¬_ : Set → Set
¬ A = A → ⊥
\end{code}
This is a form of *proof by contradiction*: if assuming `A` leads
to the conclusion `⊥` (a contradiction), then we must have `¬ A`.

Evidence that `¬ A` holds is of the form

    λ (x : A) → N

where `N` is a term of type `⊥` containing as a free variable `x` of type `A`.
In other words, evidence that `¬ A` holds is a function that converts evidence
that `A` holds into evidence that `⊥` holds.

Given evidence that both `¬ A` and `A` hold, we can conclude that `⊥` holds.
In other words, if both `¬ A` and `A` hold, then we have a contradiction.
\begin{code}
¬-elim : ∀ {A : Set} → ¬ A → A → ⊥
¬-elim ¬a a = ¬a a
\end{code}
Here we write `¬a` for evidence of `¬ A` and `a` for evidence of `A`.  This
means that `¬a` must be a function of type `A → ⊥`, and hence the application
`¬a a` must be of type `⊥`.  Note that this rule is just a special case of `→-elim`.

We set the precedence of negation so that it binds more tightly
than disjunction and conjunction, but more tightly than anything else.
\begin{code}
infix 3 ¬_
\end{code}
Thus, `¬ A × ¬ B` parses as `(¬ A) × (¬ B)`.

In *classical* logic, we have that `A` is equivalent to `¬ ¬ A`.
As we discuss below, in Agda we use *intuitionistic* logic, wher
we have only half of this equivalence, namely that `A` implies `¬ ¬ A`.
\begin{code}
¬¬-intro : ∀ {A : Set} → A → ¬ ¬ A
¬¬-intro a ¬a = ¬a a
\end{code}
Let `a` be evidence of `A`. We will show that assuming
`¬ A` leads to a contradiction, and hence `¬ ¬ A` must hold.
Let `¬a` be evidence of `¬ A`.  Then from `A` and `¬ A`
we have a contradiction (evidenced by `¬a a`).  Hence, we have
shown `¬ ¬ A`.

We cannot show that `¬ ¬ A` implies `A`, but we can show that
`¬ ¬ ¬ A` implies `¬ A`.
\begin{code}
¬¬¬-elim : ∀ {A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬¬-elim ¬¬¬a a = ¬¬¬a (¬¬-intro a)
\end{code}
Let `¬¬¬a` be evidence of `¬ ¬ ¬ A`. We will show that assuming
`A` leads to a contradiction, and hence `¬ A` must hold.
Let `a` be evidence of `A`. Then by the previous result, we
can conclude `¬ ¬ A` (evidenced by `¬¬-intro a`).  Then from
`¬ ¬ ¬ A` and `¬ ¬ A` we have a contradiction (evidenced by
`¬¬¬a (¬¬-intro a)`.  Hence we have shown `¬ A`.

Another law of logic is the *contrapositive*,
stating that if `A` implies `B`, then `¬ B` implies `¬ A`.
\begin{code}
contrapositive : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
contrapositive a→b ¬b a = ¬b (a→b a)
\end{code}
Let `a→b` be evidence of `A → B` and let `¬b` be evidence of `¬ B`.  We
will show that assuming `A` leads to a contradiction, and hence
`¬ A` must hold. Let `a` be evidence of `A`.  Then from `A → B` and
`A` we may conclude `B` (evidenced by `a→b a`), and from `B` and `¬ B`
we may conclude `⊥` (evidenced by `¬b (a→b a)`).  Hence, we have shown
`¬ A`.

Given the correspondence of implication to exponentiation and
false to the type with no members, we can view negation as
raising to the zero power.  This indeed corresponds to what
we know for arithmetic, where

    0 ^ n  =  1,  if n = 0
           =  0,  if n ≠ 0

Indeed, there is exactly one proof of `⊥ → ⊥`.
\begin{code}
id : ⊥ → ⊥
id x = x
\end{code}
However, there are no possible values of type `Bool → ⊥`
or `ℕ → bot`.

[TODO?: Give the proof that one cannot falsify law of the excluded middle,
including a variant of the story from Call-by-Value is Dual to Call-by-Name.]

The law of the excluded middle is irrefutable.
\begin{code}
excluded-middle-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
excluded-middle-irrefutable k = k (inj₂ (λ a → k (inj₁ a)))
\end{code}

*Exercise* (`¬⊎≃×¬`)

Show that conjunction, disjunction, and negation are related by a
version of De Morgan's Law.
\begin{code}
postulate
  ¬⊎≃×¬ : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
\end{code}
This result is an easy consequence of something we've proved previously.

Do we also have the following?

    ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)

If so, prove; if not, explain why.


## Intuitive and Classical logic

In Gilbert and Sullivan's *The Gondoliers*, Casilda is told that
as an infant she was married to the heir of the King of Batavia, but
that due to a mix-up no one knows which of two individuals, Marco or
Giuseppe, is the heir.  Alarmed, she wails ``Then do you mean to say
that I am married to one of two gondoliers, but it is impossible to
say which?''  To which the response is ``Without any doubt of any kind
whatever.''

Logic comes in many varieties, and one distinction is between
*classical* and *intuitionistic*. Intuitionists, concerned
by cavalier assumptions made by some logicians about the nature of
infinity, insist upon a constructionist notion of truth.  In
particular, they insist that a proof of `A ⊎ B` must show
*which* of `A` or `B` holds, and hence they would reject the
claim that Casilda is married to Marco or Giuseppe until one of the
two was identified as her husband.  Perhaps Gilbert and Sullivan
anticipated intuitionism, for their story's outcome is that the heir
turns out to be a third individual, Luiz, with whom Casilda is,
conveniently, already in love.

Intuitionists also reject the law of the excluded
middle, which asserts `A ⊎ ¬ A` for every `A`, since the law
gives no clue as to *which* of `A` or `¬ A` holds. Heyting
formalised a variant of Hilbert's classical logic that captures the
intuitionistic notion of provability. In particular, the law of the
excluded middle is provable in Hilbert's logic, but not in Heyting's.
Further, if the law of the excluded middle is added as an axiom to
Heyting's logic, then it becomes equivalent to Hilbert's.
Kolmogorov
showed the two logics were closely related: he gave a double-negation
translation, such that a formula is provable in classical logic if and
only if its translation is provable in intuitionistic logic.

Propositions as Types was first formulated for intuitionistic logic.
It is a perfect fit, because in the intuitionist interpretation the
formula `A ⊎ B` is provable exactly when one exhibits either a proof
of `A` or a proof of `B`, so the type corresponding to disjunction is
a disjoint sum.

(The passage above is taken from "Propositions as Types", Philip Wadler,
*Communications of the ACM*, December 2015.)

**Exercise** Prove the following five formulas are equivalent.

\begin{code}
¬¬-elim excluded-middle peirce implication de-morgan : Set₁
¬¬-elim = ∀ {A : Set} → ¬ ¬ A → A
excluded-middle = ∀ {A : Set} → A ⊎ ¬ A
peirce = ∀ {A B : Set} → (((A → B) → A) → A)
implication = ∀ {A B : Set} → (A → B) → ¬ A ⊎ B
de-morgan = ∀ {A B : Set} → ¬ (A × B) → ¬ A ⊎ ¬ B
\end{code}

<!-- 

It turns out that an assertion such as `Set : Set` is paradoxical.
Therefore, there are an infinite number of different levels of sets,
where `Set lzero : Set lone` and `Set lone : Set ltwo`, and so on,
where `lone` is `lsuc lzero`, and `ltwo` is `lsuc lone`, analogous to
the way we represent the natural nuambers. So far, we have only used
the type `Set`,  which is equivalent to `Set lzero`.  Here, since each
of `double-negation` and the others defines a type, we need to use
`Set₁` as the "type of types".

-->

[NOTES]

Two halves of de Morgan's laws hold intuitionistically.  The other two
halves are each equivalent to the law of double negation.

\begin{code}
dem1 : ∀ {A B : Set} → A × B → ¬ (¬ A ⊎ ¬ B)
dem1 (a , b) (inj₁ ¬a) = ¬a a
dem1 (a , b) (inj₂ ¬b) = ¬b b

dem2 : ∀ {A B : Set} → A ⊎ B → ¬ (¬ A × ¬ B)
dem2 (inj₁ a) (¬a , ¬b) = ¬a a
dem2 (inj₂ b) (¬a , ¬b) = ¬b b
\end{code}

For the other variant of De Morgan's law, one way is an isomorphism.
\begin{code}
-- dem-≃ : ∀ {A B : Set} → (¬ (A ⊎ B)) ≃ (¬ A × ¬ B)
-- dem-≃ = →-distributes-⊎
\end{code}

The other holds in only one direction.
\begin{code}
dem-half : ∀ {A B : Set} → ¬ A ⊎ ¬ B → ¬ (A × B)
dem-half (inj₁ ¬a) (a , b) = ¬a a
dem-half (inj₂ ¬b) (a , b) = ¬b b
\end{code}

The other variant does not appear to be equivalent to classical logic.
So that undermines my idea that basic propositions are either true
intuitionistically or equivalent to classical logic.

For several of the laws equivalent to classical logic, the reverse
direction holds in intuitionistic long.
\begin{code}
implication-inv : ∀ {A B : Set} → (¬ A ⊎ B) → A → B
implication-inv (inj₁ ¬a) a = ⊥-elim (¬a a)
implication-inv (inj₂ b)  a = b

demorgan-inv : ∀ {A B : Set} → A ⊎ B → ¬ (¬ A × ¬ B)
demorgan-inv (inj₁ a) (¬a , ¬b) =  ¬a a
demorgan-inv (inj₂ b) (¬a , ¬b) =  ¬b b
\end{code}

    
