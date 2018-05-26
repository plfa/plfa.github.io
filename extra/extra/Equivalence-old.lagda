---
title     : "Equivalence: Equivalence and equational reasoning"
layout    : page
permalink : /Equivalence
---

<!-- TODO: Consider changing `Equivalence` to `Equality` or `Identity`.
Possibly introduce the name `Martin Löf Identity` early on. -->

Much of our reasoning has involved equivalence.  Given two terms `M`
and `N`, both of type `A`, we write `M ≡ N` to assert that `M` and `N`
are interchangeable.  So far we have taken equivalence as a primitive,
but in fact it can be defined using the machinery of inductive
datatypes.


## Imports

Pretty much every module in the Agda
standard library, and every chapter in this book, imports the standard
definition of equivalence. Since we define equivalence here, any such
import would create a conflict.  The only import we make is the
definition of type levels, which is so primitive that it precedes
the definition of equivalence.
\begin{code}
open import Agda.Primitive using (Level; lzero; lsuc)
open import Data.Nat using (ℕ; zero; suc; _+_)
\end{code}


## Equivalence

We declare equivalence as follows.
\begin{code}
data _≡_ {ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x
\end{code}
In other words, for any type `A` and for any `x` of type `A`, the
constructor `refl` provides evidence that `x ≡ x`. Hence, every value
is equivalent to itself, and we have no other way of showing values
are equivalent.  We have quantified over all levels, so that we can
apply equivalence to types belonging to any level.  The definition
features an asymetry, in that the first argument to `_≡_` is given by
the parameter `x : A`, while the second is given by an index in `A → Set ℓ`.

We declare the precedence of equivalence as follows.
\begin{code}
infix 4 _≡_
\end{code}
We set the precedence of `_≡_` at level 4, the same as `_≤_`,
which means it binds less tightly than any arithmetic operator.
It associates neither to the left nor right; writing `x ≡ y ≡ z`
is illegal.


## Equivalence is an equivalence relation

An equivalence relation is one which is reflexive, symmetric, and transitive.
Reflexivity is built-in to the definition of equivalence, via the
constructor `refl`.  It is straightforward to show symmetry.
\begin{code}
sym : ∀ {ℓ} {A : Set ℓ} {x y : A} →  x ≡ y → y ≡ x
sym refl = refl
\end{code}
How does this proof work? The argument to `sym` has type `x ≡ y`,
but on the left-hand side of the equation the argument has been instantiated to the pattern `refl`,
which requires that `x` and `y` are the same.  Hence, for the right-hand side of the equation
we need a term of type `x ≡ x`, and `refl` will do.

It is instructive to develop `sym` interactively.
To start, we supply a variable for the argument on the left, and a hole for the body on the right:

    sym : ∀ {ℓ} {A : Set ℓ} {x y : A} →  x ≡ y → y ≡ x
    sym r = {! !}

If we go into the hole and type `C-C C-,` then Agda reports:

    Goal: .y ≡ .x
    ————————————————————————————————————————————————————————————
    r  : .x ≡ .y
    .y : .A
    .x : .A
    .A : Set .ℓ
    .ℓ : .Agda.Primitive.Level

If in the hole we type `C-C C-C r` then Agda will instantiate `r` to all possible constructors,
with one equation for each. There is only one possible constructor:

    sym : ∀ {ℓ} {A : Set ℓ} {x y : A} →  x ≡ y → y ≡ x
    sym refl = {! !}

If we go into the hole again and type `C-C C-,` then Agda now reports:

     Goal: .x ≡ .x
     ————————————————————————————————————————————————————————————
     .x : .A
     .A : Set .ℓ
     .ℓ : .Agda.Primitive.Level

This is the key step---Agda has worked out that `x` and `y` must be the same to match the pattern `refl`!

Finally, if we go back into the hole and type `C-C C-R` it will
instantiate the hole with the one constructor that yields a value of
the expected type.

    sym : ∀ {ℓ} {A : Set ℓ} {x y : A} →  x ≡ y → y ≡ x
    sym refl = refl

This completes the definition as given above.

Transitivity is equally straightforward.
\begin{code}
trans : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl
\end{code}
Again, a useful exercise is to carry out an interactive development, checking
how Agda's knowledge changes as each of the two arguments is
instantiated.

Equivalence also satisfies *congruence*.  If two terms are equivalent,
then they remain so after the same function is applied to both.
\begin{code}
cong : ∀ {ℓ} {A B : Set ℓ} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl
\end{code}
Once more, a useful exercise is to carry out an interactive development.


## Tabular reasoning

A few declarations allow us to support the form of tabular reasoning
that we have used throughout the book.  We package the declarations
into a module, named `≡-Reasoning`, to match the format used in Agda's
standard library.
\begin{code}
module ≡-Reasoning {ℓ} {A : Set ℓ} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  begin x≡y = x≡y

  _≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z =  trans x≡y y≡z

  _∎ : ∀ (x : A) → x ≡ x
  x ∎ = refl

open ≡-Reasoning
\end{code}
Opening the module makes all of the definitions
available in the current environment.

As a simple example, let's look at the proof of transitivity
rewritten in tabular form.
\begin{code}
trans′ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans′ {_} {_} {x} {y} {z} x≡y y≡z =
  begin
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎
\end{code}
Tabular proofs begin with `begin`, end with `∎`
(which is sometimes pronounced "qed" or "tombstone")
and consist of a string of equations.  Due to the
fixity declarations, the body parses as follows.

    begin (x ≡⟨ x≡y ⟩ (y ≡⟨ y≡z ⟩ (z ∎)))

The application of `begin` is purely cosmetic, as it simply returns
its argument.  That argument consists of `_≡⟨_⟩_` applied to `x`,
`x≡y`, and `y ≡⟨ y≡z ⟩ (z ∎)`.  The first argument is a term, `x`,
while the second and third arguments are both proofs of equations, in
particular proofs of `x ≡ y` and `y ≡ z` respectively, which are
combined by `trans` in the body of `_≡⟨_⟩_` to yield a proof of `x ≡
z`.  The proof of `y ≡ z` consists of `_≡⟨_⟩_` applied to `y`, `y≡z`,
and `z ∎`.  The first argument is a term, `y`, while the second and
third arguments are both proofs of equations, in particular proofs of
`y ≡ z` and `z ≡ z` respectively, which are combined by `trans` in the
body of `_≡⟨_⟩_` to yield a proof of `y ≡ z`.  Finally, the proof of
`z ≡ z` consists of `_∎` applied to the term `z`, which yields `refl`.
After simplification, the body is equivalent to the following term.

    trans x≡y (trans y≡z refl)

We could replace all uses of tabular reasoning by a chain of
applications of `trans`, but the result would be far less perspicuous.
Also note that the syntactic trick behind `∎` means that the chain
always ends in the form `trans e refl` even though `e` alone would do,
where `e` is a proof of an equivalence.

<!--

## Tabular reasoning, another example

As a second example of tabular reasoning, we consider the proof that addition
is commutative.  We first repeat the definitions of naturals and addition.
We cannot import them because (as noted at the beginning of this chapter)
it would cause a conflict.
\begin{code}
{-
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)
-}
\end{code}

To save space we postulate (rather than prove in full) two lemmas,
and then repeat the proof of commutativity.
\begin{code}
postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

{-
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identity m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎
-}
\end{code}
The tabular reasoning here is similar to that in the
preceding section, the one addition being the use of
`_≡⟨⟩_`, which we use when no justification is required.
One can think of occurrences of `≡⟨⟩` as an equivalent
to `≡⟨ refl ⟩`.

Agda always treats a term as equivalent to its
simplified term.  The reason that one can write

      suc (n + m)
    ≡⟨⟩
      suc n + m

is because Agda treats both terms as the same.
This also means that one could instead interchange
the lines and write

      suc n + m
    ≡⟨⟩
      suc (n + m)

and Agda would not object. Agda only checks that the terms
separated by `≡⟨⟩` are equivalent; it's up to us to write
them in an order that will make sense to the reader.
-->

## Rewriting

Consider a property of natural numbers, such as being even.

\begin{code}
data even : ℕ → Set where
  ev0 : even zero
  ev+2 : ∀ {n : ℕ} → even n → even (suc (suc n))
\end{code}
In the previous section, we proved addition is commutative.
Given evidence that `even (m + n)` holds,
we ought also to be able to take that as evidence
that `even (n + m)` holds.

Agda includes special notation to support just this
kind of reasoning.  To enable this notation, we use
pragmas to tell Agda which type
corresponds to equivalence.
\begin{code}
{-# BUILTIN EQUALITY _≡_ #-}
\end{code}

We can then prove the desired property as follows.
\begin{code}
postulate
  +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

even-comm : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm m n ev rewrite +-comm m n = ev
\end{code}
Here `ev` ranges over evidence that `even (m + n)` holds, and we show
that it is also provides evidence that `even (n + m)` holds.  In
general, the keyword `rewrite` is followed by evidence of an
equivalence, and that equivalence is used to rewrite the type of the
goal and of any variable in scope.

It is instructive to develop `even-comm` interactively.
To start, we supply variables for the arguments on the left, and a hole for the body on the right:

    even-comm : ∀ (m n : ℕ) → even (m + n) → even (n + m)
    even-comm m n ev = {! !}

If we go into the hole and type `C-C C-,` then Agda reports:

    Goal: even (n + m)
    ————————————————————————————————————————————————————————————
    ev : even (m + n)
    n  : ℕ
    m  : ℕ

Now we add the rewrite.

    even-comm : ∀ (m n : ℕ) → even (m + n) → even (n + m)
    even-comm m n ev rewrite +-comm m n = {! !}

If we go into the hole again and type `C-C C-,` then Agda now reports:

    Goal: even (n + m)
    ————————————————————————————————————————————————————————————
    ev : even (n + m)
    n  : ℕ
    m  : ℕ

Now it is trivial to see that `ev` satisfies the goal, and typing `C-C C-A` in the
hole causes it to be filled with `ev`.


## Multiple rewrites

One may perform multiple rewrites, each separated by a vertical bar.  For instance,
here is a second proof that addition is commutative, relying on rewrites rather
than tabular reasoning.
\begin{code}
+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ zero n rewrite +-identity n = refl
+-comm′ (suc m) n rewrite +-suc n m | +-comm m n = refl
\end{code}
This is far more compact.  Among other things, whereas the previous
proof required `cong suc (+-comm m n)` as the justification to invoke the
inductive hypothesis, here it is sufficient to rewrite with `+-comm m n`, as
rewriting automatically takes congruence into account.  Although proofs
with rewriting are shorter, proofs in tabular form make the reasoning
involved easier to follow, and we will stick with the latter when feasible.


## Rewriting expanded

The `rewrite` notation is in fact shorthand for an appropriate use of `with`
abstraction.
\begin{code}
even-comm′ : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm′ m n ev with   m + n  | +-comm m n
...                  | .(n + m) | refl        = ev
\end{code}
The first clause asserts that `m + n` and `n + m` are identical, and
the second clause justifies that assertion with evidence of the
appropriate equivalence.  Note the use of the "dot pattern" `.(n +
m)`.  A dot pattern is followed by an expression and is made when
other information allows one to identify the expession in the `with`
clause with the expression it matches against.  In this case, the
identification of `m + n` and `n + m` is justified by the subsequent
matching of `+-comm m n` against `refl`.  One might think that the
first clause is redundant as the information is inherent in the second
clause, but in fact Agda is rather picky on this point: omitting the
first clause or reversing the order of the clauses will cause Agda to
report an error.  (Try it and see!)


## Leibniz equality

The form of asserting equivalence that we have used is due to Martin Löf,
and was published in 1975.  An older form is due to Leibniz, and was published
in 1686.  Leibniz asserted the *identity of indiscernibles*: two objects are
equal if and only if they satisfy the same properties. This
principle sometimes goes by the name Leibniz' Law, and is closely
related to Spock's Law, ``A difference that makes no difference is no
difference''.  Here we define Leibniz equality, and show that two terms
satsisfy Lebiniz equality if and only if they satisfy Martin Löf equivalence.

Leibniz equality is usually formalized to state that `x ≐ y`
holds if every property `P` that holds of `x` also holds of
`y`.  Perhaps surprisingly, this definition is
sufficient to also ensure the converse, that every property `P` that
holds of `y` also holds of `x`.

Let `x` and `y` be objects of type $A$. We say that `x ≐ y` holds if
for every predicate $P$ over type $A$ we have that `P x` implies `P y`.
\begin{code}
_≐_ : ∀ {ℓ} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐_ {ℓ} {A} x y = (P : A → Set ℓ) → P x → P y
\end{code}
Here we must make use of levels: if `A` is a set at level `ℓ` and `x` and `y`
are two values of type `A` then `x ≐ y` is at the next level `lsuc ℓ`.

Leibniz equality is reflexive and transitive,
where the first follows by a variant of the identity function
and the second by a variant of function composition.
\begin{code}
refl-≐ : ∀ {ℓ} {A : Set ℓ} {x : A} → x ≐ x
refl-≐ P Px  =  Px

trans-≐ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≐ y → y ≐ z → x ≐ z
trans-≐ x≐y y≐z P Px  =  y≐z P (x≐y P Px)
\end{code}

Symmetry is less obvious.  We have to show that if `P x` implies `P y`
for all predicates `P`, then the implication holds the other way round
as well.  Given a specific `P` and a proof `Py` of `P y`, we have to
construct a proof of `P x` given `x ≐ y`.  To do so, we instantiate
the equality with a predicate `Q` such that `Q z` holds if `P z`
implies `P x`.  The property `Q x` is trivial by reflexivity, and
hence `Q y` follows from `x ≐ y`.  But `Q y` is exactly a proof of
what we require, that `P y` implies `P x`.
\begin{code}
sym-≐ : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≐ y → y ≐ x
sym-≐ {ℓ} {A} {x} {y} x≐y P  =  Qy
  where
    Q : A → Set ℓ
    Q z = P z → P x
    Qx : Q x
    Qx = refl-≐ P
    Qy : Q y
    Qy = x≐y Q Qx
\end{code}

We now show that Martin Löf equivalence implies
Leibniz equality, and vice versa.  In the forward direction, if we know
`x ≡ y` we need for any `P` to take evidence of `P x` to evidence of `P y`,
which is easy since equivalence of `x` and `y` implies that any proof
of `P x` is also a proof of `P y`.
\begin{code}
≡-implies-≐ : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → x ≐ y
≡-implies-≐ refl P Px = Px
\end{code}
The function `≡-implies-≐` is often called *substitution* because it
says that if we know `x ≡ y` then we can substitute `y` for `x`,
taking a proof of `P x` to a proof  of `P y` for any property `P`.

In the reverse direction, given that for any `P` we can take a proof of `P x`
to a proof of `P y` we need to show `x ≡ y`. The proof is similar to that
for symmetry of Leibniz equality. We take $Q$
to be the predicate that holds of `z` if `x ≡ z`. Then `Q x` is trivial
by reflexivity of Martin Löf equivalence, and hence `Q y` follows from
`x ≐ y`.  But `Q y` is exactly a proof of what we require, that `x ≡ y`.
\begin{code}
≐-implies-≡ : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≐ y → x ≡ y
≐-implies-≡ {ℓ} {A} {x} {y} x≐y = Qy
  where
    Q : A → Set ℓ
    Q z = x ≡ z
    Qx : Q x
    Qx = refl
    Qy : Q y
    Qy = x≐y Q Qx
\end{code}

(Parts of this section are adapted from *≐≃≡: Leibniz Equality is
Isomorphic to Martin-Löf Identity, Parametrically*, by Andreas Abel,
Jesper Cockx, Dominique Devries, Andreas Nuyts, and Philip Wadler,
draft paper, 2017.)
