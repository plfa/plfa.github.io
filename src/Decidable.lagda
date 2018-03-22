---
title     : "Decidable: Booleans and decision procedures"
layout    : page
permalink : /Decidable
---

We have a choice as to how to represent relations:
as an inductive data type of *evidence* that the relation holds,
or as a function that *computes* whether the relation holds.
Here we explore the relation between these choices.

## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contraposition)
  renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; foldr; map)
open import Function using (_∘_)
\end{code}

## Evidence vs Computation

Recall that Chapter [Relations](Relations) defined comparison
an inductive datatype, which provides *evidence* that one number
is less than or equal to another.
\begin{code}
infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n
\end{code}
For example, we can provide evidence that `2 ≤ 4`,
and show there is no possible evidence that `4 ≤ 2`.
\begin{code}
2≤4 : 2 ≤ 4
2≤4 = s≤s (s≤s z≤n)

¬4≤2 : ¬ (4 ≤ 2)
¬4≤2 (s≤s (s≤s ()))
\end{code}
The occurrence of `()` attests to the fact that there is
no possible evidence for `2 ≤ 0`, which `z≤n` cannot match
(because `2` is not `zero`) and `s≤s` cannot match
(because `0` cannot match `suc n`).

An alternative, which may seem more familiar, is to define a
type of booleans.
\begin{code}
data Bool : Set where
  true  : Bool
  false : Bool
\end{code}
We will use `true` to represent the case where a proposition holds,
and `false` to represent the case where a proposition fails to hold.

Given booleans, we can define a function of two numbers that
*computes* to true if the comparison holds, and false otherwise.
\begin{code}
infix 4 _≤ᵇ_

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ n       =  true
suc m ≤ᵇ zero   =  false
suc m ≤ᵇ suc n  =  m ≤ᵇ n
\end{code}
The first and last clauses of this definition resemble the two
constructors of the corresponding inductive datatype, while the
middle clause arises because there is no possible evidence that
`suc m ≤ zero` for any `m`.
For example, we can compute that `2 ≤ 4` holds,
and we can compute that `4 ≤ 2` does not hold.
\begin{code}
_ : (2 ≤ᵇ 4) ≡ true
_ =
  begin
    2 ≤ᵇ 4
  ≡⟨⟩
    1 ≤ᵇ 3
  ≡⟨⟩
    0 ≤ᵇ 2
  ≡⟨⟩
    true
  ∎

_ : (4 ≤ᵇ 2) ≡ false
_ =
  begin
    4 ≤ᵇ 2
  ≡⟨⟩
    3 ≤ᵇ 1
  ≡⟨⟩
    2 ≤ᵇ 0
  ≡⟨⟩
    false
  ∎
\end{code}
In the first case, it takes two steps to reduce the first argument to zero,
and one more step to compute true, corresponding to the two uses of `s≤s`
and the one use of `z≤n` when providing evidence that `2 ≤ 4`.
In the second case, it takes two steps to reduce the second argument to zero,
and one more step to compute false, corresponding to the two uses of `s≤s`
and the one use of `()` when showing there can be no evidence that `4 ≤ 2`.

## Relating evidence and computation

We would hope to be able to show these two approaches are related, and
indeed we can.  First, we define a function that lets us map from the
computation world to the evidence world.  
\begin{code}
T : Bool → Set
T true = ⊤
T false = ⊥
\end{code}
Recall that `⊤` is the unit type which contains the single element `tt`,
and the `⊥` is the empty type which contains no values.  (Also note that
`T` is a capital letter t, and distinct from `⊤`.)  If `b` is of type `Bool`,
then `tt` provides evidence that `T b` holds if `b` is true, while there is
no possible evidence that `T b` holds if `b` is false.

Another way to put this is that `T b` is inhabited exactly when `b ≡ true`
is inhabited.
In the forward direction, we need to do a case analysis on the boolean `b`.
\begin{code}
T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true tt = refl
T→≡ false ()
\end{code}
If `b` is true then `T b` is inhabited by `tt` and `b ≡ true` is inhabited
by `refl`, while if `b` is false then `T b` in uninhabited.

In the reverse direction, there is no need for a case analysis.
\begin{code}
≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl = tt
\end{code}
If `b ≡ true` is inhabited by `refl` we know that `b` is `true` and
hence `T b` is inhabited by `tt`.

Now we can show that `T (m ≤ᵇ n)` is inhabited exactly when `m ≤ n` is inhabited.

In the forward direction, we consider the three clauses in the definition
of `_≤ᵇ_`. 
\begin{code}
≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ zero n tt = z≤n
≤ᵇ→≤ (suc m) zero ()
≤ᵇ→≤ (suc m) (suc n) t =  s≤s (≤ᵇ→≤ m n t)
\end{code}
In the first clause, we immediately have that `zero ≤ᵇ n` is
true, so `T (m ≤ᵇ n)` is evidenced by `tt`, and correspondingly `m ≤ n` is
evidenced by `z≤n`. In the middle clause, we immediately have that
`suc m ≤ᵇ zero` is false, and hence `T (m ≤ᵇ n)` is empty, so we need
not provide evidence that `m ≤ n`, which is just as well since there is no
such evidence.  In the last clause, we have the `suc m ≤ suc n` recurses
to `m ≤ n` and we let `t` be the evidence of `T (m ≤ᵇ n)` if it exists.
We recursively invoke the function to get evidence that `m ≤ n`, which
`s≤s` converts to evidence that `suc m ≤ suc n`.

In the reverse direction, we consider the possible forms of evidence
that `m ≤ n`.
\begin{code}
≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ z≤n = tt
≤→≤ᵇ (s≤s m≤n) = ≤→≤ᵇ m≤n
\end{code}
If the evidence is `z≤n` then we immediately have that `zero ≤ᵇ n` is
true, so `T (m ≤ᵇ n)` is evidenced by `tt`. If the evidence is `s≤s`
applied to `m≤n`, then `suc m ≤ᵇ suc n` reduces to `m ≤ᵇ n`, and we
may recursively invoke the function to produce evidence that `T (m ≤ᵇ n)`.

The forward proof has one more clause than the reverse proof,
precisely because in the forward proof we need clauses corresponding to
the comparison yielding both true and false, while in the reverse proof
we only need clauses corresponding to the case where there is evidence
that the comparision holds.  This is exactly why we tend to prefer the
evidence formulation to the computation formulation, because it allows
us to do less work: we consider only cases where the relation holds,
and can ignore those where it does not.

On the other hand, sometimes the computation formulation may be just what
we want.  Given a non-obvious relation over large values, it might be
handy to have the computer work out the answer for us.  Fortunately,
rather than choosing between *evidence* and *computation*,
there is a way to get the benefits of both.

## The best of both worlds

A function that returns a boolean returns exactly a single bit of information:
does the relation hold or does it not? Conversely, the evidence approach tells
us exactly why the relation holds, but we are responsible for generating the
evidence.  But it is easy to define a type that combines the benefits of
both approaches.  It is called `Dec A`, where `Dec` is short for *decidable*.
\begin{code}
data Dec (A : Set) : Set where
  yes : A → Dec A
  no : ¬ A → Dec A
\end{code}
Like booleans, the type has two constructors.  A value of type `Dec A`
is either of the form `yes x`, where `x` provides evidence that `A` holds,
or of the form `no ¬x`, where `¬x` provides evidence that `A` cannot hold
(that is, `¬x` is a function which given evidence of `A` yields a contradiction).

For example, here is a function which given two numbers decides whether one
is less than or equal to the other, and provides evidence to justify its conclusion.

First, we introduce two functions useful for constructing evidence that
an inequality does not hold.
\begin{code}
¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n
\end{code}
The first of these asserts that `¬ (suc m ≤ zero)`, and follows by
absurdity, since any evidence of inequality has the form `zero ≤ n`
or `suc m ≤ suc n`, neither of which match `suc m ≤ suc n`. The second
of these takes evidence `¬m≤n` of `¬ (m ≤ n)` and returns a proof of
`¬ (suc m ≤ suc n)`.  Any evidence of `suc m ≤ suc n` must have the
form `s≤s m≤n` where `m≤n` is evidence that `m ≤ n`.  Hence, we have
a contradiction, evidenced by `¬m≤n m≤n`.

Using these, it is straightforward to decide an inequality.
\begin{code}
_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero ≤? n = yes z≤n
suc m ≤? zero = no ¬s≤z
suc m ≤? suc n with m ≤? n
... | yes m≤n = yes (s≤s m≤n)
... | no ¬m≤n = no (¬s≤s ¬m≤n)
\end{code}
As with `_≤ᵇ_`, the definition has three clauses.  In the first
clause, it is immediate that `zero ≤ n` holds, and it is evidenced by
`z≤n`.  In the second clause, it is immediate that `suc m ≤ n` does
not hold, and it is evidenced by `¬s≤z`.
In the third clause, to decide whether `suc m ≤ suc n` holds we
recursively invoke `m ≤? n`.  There are two possibilities.  In the
`yes` case it returns evidence `m≤n` that `m ≤ n`, and `s≤s m≤n`
provides evidence that `suc m ≤ suc n`.  In the `no` case it returns
evidence `¬m≤n` that `¬ (m ≤ n)`, and `¬s≤s ¬m≤n` provides evidence
that `¬ (suc m ≤ suc n)`.

When we wrote `_≤ᵇ_`, we had to write two other functions, `≤ᵇ→≤` and `≤→≤ᵇ`,
in order to show that it was correct.  In contrast, the definition of `_≤?_`
proves itself correct, as attested to by its type.  The code of `_≤?_`
is far more compact than the combined code of `_≤ᵇ_`, `≤ᵇ→≤`, and `≤→≤ᵇ`.
And, as we will later show, if you really want the latter three, it is easy
to derive them from the first.

We can use our new function to *compute* the *evidence* that earlier we had to
think up on our own.
\begin{code}
_ : 2 ≤? 4 ≡ yes (s≤s (s≤s z≤n))
_ = refl

_ : 4 ≤? 2 ≡ no (¬s≤s (¬s≤s ¬s≤z))
_ = refl
\end{code}
You can check that Agda will indeed compute these values.  Typing
`^C ^N` and providing `2 ≤? 4` or `4 ≤? 2` as the requested expression
causes Agda to print the values given above.

(A subtlety: if we do not define `¬s≤z` and `¬s≤s` as top-level functions,
but instead use inline anonymous functions then Agda may have
trouble normalising evidence of negation.)

## Decidables from booleans, and booleans from decidables

Curious readers might wonder if we could reuse the definition of
`m ≤ᵇ n`, together with the proofs that it is equivalent to `m ≤ n`, to show
decidability.  Indeed we can do so as follows.
\begin{code}
_≤?′_ : ∀ (m n : ℕ) → Dec (m ≤ n)
m ≤?′ n with m ≤ᵇ n | ≤ᵇ→≤ m n | ≤→≤ᵇ {m} {n}
...        | true   | p        | _            = yes (p tt)
...        | false  | _        | ¬p           = no ¬p
\end{code}
If `m ≤ᵇ n` is true then `≤ᵇ→≤` yields a proof that `m ≤ n` holds,
while if it is false then `≤→≤ᵇ` takes a proof the `m ≤ n` holds into a contradiction.

The triple binding of the `with` clause in this proof is essential.
If instead we wrote

    _≤?″_ : ∀ (m n : ℕ) → Dec (m ≤ n)
    m ≤?″ n with m ≤ᵇ n
    ... | true  = yes (≤ᵇ→≤ m n tt)
    ... | false = no (≤→≤ᵇ {m} {n})

then Agda would make two complaints, one for each clause

    ⊤ !=< (T (m ≤ᵇ n)) of type Set
    when checking that the expression tt has type T (m ≤ᵇ n)

    T (m ≤ᵇ n) !=< ⊥ of type Set
    when checking that the expression ≤→≤ᵇ {m} {n} has type ¬ m ≤ n

Putting the expressions into the `with` clause permits Agda to exploit
the fact that `T (m ≤ᵇ n)` is `⊤` when `m ≤ᵇ n` is true, and that
`T (m ≤ᵇ n)` is `⊥` when `m ≤ᵇ n` is false.

However, overall it is simpler to just define `_≤?_` directly, as in the previous
section.  If one really wants `_≤ᵇ_`, then it and its properties are easily derived
from `_≤?_`, as we will now show.

Erasure takes a decidable value to a boolean.
\begin{code}
⌊_⌋ : ∀ {A : Set} → Dec A → Bool
⌊ yes x ⌋ = true
⌊ no ¬x ⌋ = false
\end{code}
Using erasure, we can easily derive `_≤ᵇ_` from `_≤?_`.
\begin{code}
_≤ᵇ′_ : ℕ → ℕ → Bool
m ≤ᵇ′ n = ⌊ m ≤? n ⌋
\end{code}

Further, if `D` is a value of type `Dec A`, then `T ⌊ D ⌋` is
inhabited exactly when `A` is inhabited.
\begin{code}
toWitness : ∀ {A : Set} → {D : Dec A} → T ⌊ D ⌋ → A
toWitness {A} {yes x} tt  = x
toWitness {A} {no ¬x} ()

fromWitness : ∀ {A : Set} → {D : Dec A} → A → T ⌊ D ⌋
fromWitness {A} {yes x} _ = tt
fromWitness {A} {no ¬x} x = ¬x x
\end{code}
Using these, we can easily derive that `T (m ≤ᵇ′ n)` is inhabited
exactly when `m ≤ n` is inhabited.
\begin{code}
≤ᵇ′→≤ : ∀ {m n : ℕ} → T (m ≤ᵇ′ n) → m ≤ n
≤ᵇ′→≤ = toWitness

≤→≤ᵇ′ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ′ n)
≤→≤ᵇ′ = fromWitness
\end{code}

In summary, it is usually best to eschew booleans and rely on decidables instead.  If you
need booleans, they and their properties are easily derived from the
corresponding decidables.

## Logical connectives

Most readers will be familiar with the logical connectives for booleans.
Each of these extends to decidables.

The conjunction of two booleans is true if both are true,
and false is either is false.
\begin{code}
infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ true  = true
false ∧ _     = false
_     ∧ false = false
\end{code}
In Emacs, the left-hand side of the third equation displays in grey,
indicating that the order of the equations determines which of the
second or the third can match.  However, regardless of which matches
the answer is the same.

Correspondingly, given two decidable propositions, we can
decide their conjunction.
\begin{code}
infixr 6 _×-dec_

_×-dec_ : {A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes y = yes ⟨ x , y ⟩
no ¬x ×-dec _     = no λ{ ⟨ x , y ⟩ → ¬x x }
_     ×-dec no ¬y = no λ{ ⟨ x , y ⟩ → ¬y y }
\end{code}
The conjunction of two propositions holds if they both hold,
and its negation holds if the negation of either holds.
If both hold, then we pair the evidence for each to yield
evidence of the conjunct.  If the negation of either holds,
assuming the conjunct will lead to a contradiction.

Again in Emacs, the left-hand side of the third equation displays in grey,
indicating that the order of the equations determines which of the
second or the third can match.  This time the answer is different depending
on which matches; if both conjuncts fail to hold we pick the first to
yield the contradiction, but it would be equally valid to pick the second.

The disjunction of two booleans is true if either is true,
and false if both are false.
\begin{code}
infixr 5 _∨_

_∨_ : Bool → Bool → Bool
true  ∨ _      = true
_     ∨ true   = true
false ∨ false  = false
\end{code}
In Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  However, regardless of which matches
the answer is the same.

Correspondingly, given two decidable propositions, we can
decide their disjunction.
\begin{code}
infixr 5 _⊎-dec_

_⊎-dec_ : {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎-dec _     = yes (inj₁ x)
_     ⊎-dec yes y = yes (inj₂ y)
no ¬x ⊎-dec no ¬y = no λ{ (inj₁ x) → ¬x x ; (inj₂ y) → ¬y y }
\end{code}
The disjunction of two propositions holds if either holds,
and its negation holds if the negation of both hold.
If either holds, we inject the evidence to yield
evidence of the disjunct.  If the negation of both hold,
assuming either disjunct will lead to a contradiction.

Again in Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  This time the answer is different depending
on which matches; if both disjuncts hold we pick the first,
but it would be equally valid to pick the second.

The negation of a boolean is false if its argument is true,
and vice versa.
\begin{code}
not : Bool → Bool
not true  = false
not false = true
\end{code}
Correspondingly, given a decidable proposition, we
can decide its negation.
\begin{code}
¬? : {A : Set} → Dec A → Dec (¬ A)
¬? (yes x)  =  no (¬¬-intro x)
¬? (no ¬x)  =  yes ¬x
\end{code}
We simply swap yes and no.  In the first equation,
the right-hand side asserts that the negation of `¬ A` holds,
in other words, that `¬ ¬ A` holds, which is an easy consequence
of the fact that `A` holds.

There is also a slightly less familiar connective,
corresponding to implication.
\begin{code}
_⊃_ : Bool → Bool → Bool
_     ⊃ true   =  true
false ⊃ _      =  true
true  ⊃ false  =  false
\end{code}
One boolean implies another if
whenever the first is true then the second is true.
Hence, the implication of two booleans is true if
the second is true or the first is false,
and false if the first is true and the second is false.
In Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  However, regardless of which matches
the answer is the same.

Correspondingly, given two decidable propositions,
we can decide if the first implies the second.
\begin{code}
_→-dec_ : {A B : Set} → Dec A → Dec B → Dec (A → B)
_     →-dec yes y  =  yes (λ _ → y)
no ¬x →-dec _      =  yes (λ x → ⊥-elim (¬x x))
yes x →-dec no ¬y  =  no (λ f → ¬y (f x))
\end{code}
The implication holds if either the second holds or
the negatioin of the first holds, and its negation
holds if the first holds and the negation of the second holds.
Evidence for the implication is a function from evidence
of the first to evidence of the second.
If the second holds, the function returns the evidence for it.
If the negation of the first holds, the function takes the
evidence of the first and derives a contradiction.
If the first holds and the negation of the second holds,
given evidence of the implication we must derive a contradiction;
we apply the evidence of the implication `f` to the evidence of the
first `x`, yielding a contradiction with the evidence `¬y` of
the negation of the second.

Again in Emacs, the left-hand side of the second equation displays in grey,
indicating that the order of the equations determines which of the
first or the second can match.  This time the answer is different depending
on which matches; but either is equally valid.


## Decidability of All

Recall that in Chapter [Lists](Lists#All) we defined a predicate `All P`
that holds if a given predicate is satisfied by every element of a list.
\begin{code}
data All {A : Set} (P : A → Set) : List A → Set where
  [] : All P []
  _∷_ : {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)
\end{code}

If instead we consider a predicate as a function that yields a boolean,
it is easy to define an analogue of `All`, which returns true if
a given predicate returns true for every element of a list.
\begin{code}
all : ∀ {A : Set} → (A → Bool) → List A → Bool
all p  =  foldr _∧_ true ∘ map p
\end{code}
The function can be written in a particularly compact style by
using the higher-order functions `map` and `foldr` as defined in
the sections on [Map](Lists#Map) and [Fold](Lists#Fold).

As one would hope, if we replace booleans by decidables there is again
an analogue of `All`.  First, return to the notion of a predicate `P` as
a function of type `A → Set`, taking a value `x` of type `A` into evidence
`P x` that a property holds for `x`.  Say that a predicate `P` is *decidable*
if we have a function that for a given `x` can decide `P x`.
\begin{code}
Decidable : ∀ {A : Set} → (A → Set) → Set
Decidable {A} P  =  ∀ (x : A) → Dec (P x)
\end{code}
Then if predicate `P` is decidable, it is also decidable whether every
element of a list satisfies the predicate.
\begin{code}
All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P)
All? P? [] = yes []
All? P? (x ∷ xs) with P? x   | All? P? xs
...                 | yes Px | yes Pxs     = yes (Px ∷ Pxs)
...                 | no ¬Px | _           = no λ{ (Px ∷ Pxs) → ¬Px Px   }
...                 | _      | no ¬Pxs     = no λ{ (Px ∷ Pxs) → ¬Pxs Pxs }
\end{code}
If the list is empty, then trivially `P` holds for every element of
the list.  Otherwise, the structure of the proof is similar to that
showing that the conjuction of two decidable propositions is itself
decidable, using `_∷_` rather than `⟨_,_⟩` to combine the evidence for
the head and tail of the list.

*Exercise* `any` `any?`

Just as `All` has analogues `all` and `all?` which determine whether a
predicate holds for every element of a list, so does `Any` have
analogues `any` and `any?` which determine whether a predicates holds
for some element of a list.  Give their definitions.

## Standard Library

\begin{code}
import Data.Bool.Base using (Bool; T; _∧_; _∨_; not)
import Data.Nat.Base using (_≤?_)
import Data.List.All using (All; []; _∷_) renaming (all to All?)
import Relation.Nullary using (Dec; yes; no)
import Relation.Nullary.Decidable using (⌊_⌋; toWitness; fromWitness)
import Relation.Nullary.Negation using (¬?)
import Relation.Nullary.Product using (_×-dec_)
import Relation.Nullary.Sum using (_⊎-dec_)
\end{code}


## Unicode

    ᵇ  U+1D47  MODIFIER LETTER SMALL B  (\^b)

