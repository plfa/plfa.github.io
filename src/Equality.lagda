---
title     : "Equality: Equality and equational reasoning"
layout    : page
permalink : /Equality
---

Much of our reasoning has involved equality.  Given two terms `M`
and `N`, both of type `A`, we write `M ≡ N` to assert that `M` and `N`
are interchangeable.  So far we have treated equality as a primitive,
but in fact it can be defined an an inductive datatype.


## Imports

This chapter has no imports.  Every chapter in this book, and nearly
every module in the Agda, imports equality.  Since we define equality
here, any import would create a conflict.


## Equality

We declare equality as follows.
\begin{code}
data _≡_ {A : Set} : A → A → Set where
  refl : ∀ {x : A} → x ≡ x
\end{code}
In other words, for any type `A` and for any `x` of type `A`, the
constructor `refl` provides evidence that `x ≡ x`. Hence, every value
is equivalent to itself, and we have no other way of showing values
are equivalent.  We have quantified over all levels, so that we can
apply equivalence to types belonging to any level.  The definition
features an asymmetry, in that the first argument to `_≡_` is given by
the parameter `x : A`, while the second is given by an index in `A → Set ℓ`.
This follows our policy of using parameters wherever possible.
The first argument to `_≡_` can be a parameter because it doesn't vary,
while the second must be an index.

We declare the precedence of equivalence as follows.
\begin{code}
infix 4 _≡_
\end{code}
We set the precedence of `_≡_` at level 4, the same as `_≤_`,
which means it binds less tightly than any arithmetic operator.
It associates neither to the left nor right; writing `x ≡ y ≡ z`
is illegal.


## Equality is an equivalence relation

An equivalence relation is one which is reflexive, symmetric, and transitive.
Reflexivity is built-in to the definition of equivalence, via the
constructor `refl`.  It is straightforward to show symmetry.
\begin{code}
sym : ∀ {A : Set} {x y : A} →  x ≡ y → y ≡ x
sym refl = refl
\end{code}
How does this proof work? The argument to `sym` has type `x ≡ y`,
but on the left-hand side of the equation the argument has been instantiated to the pattern `refl`,
which requires that `x` and `y` are the same.  Hence, for the right-hand side of the equation
we need a term of type `x ≡ x`, and `refl` will do.

It is instructive to develop `sym` interactively.  To start, we supply
a variable for the argument on the left, and a hole for the body on
the right:

    sym : ∀ {A : Set} {x y : A} →  x ≡ y → y ≡ x
    sym e = {! !}

If we go into the hole and type `C-C C-,` then Agda reports:

    Goal: .y ≡ .x
    ————————————————————————————————————————————————————————————
    e  : .x ≡ .y
    .y : .A
    .x : .A
    .A : Set

If in the hole we type `C-C C-C e` then Agda will instantiate `e` to
all possible constructors, with one equation for each. There is only
one possible constructor:

    sym : ∀ {A : Set} {x y : A} →  x ≡ y → y ≡ x
    sym refl = {! !}

If we go into the hole again and type `C-C C-,` then Agda now reports:

     Goal: .x ≡ .x
     ————————————————————————————————————————————————————————————
     .x : .A
     .A : Set

This is the key step---Agda has worked out that `x` and `y` must be
the same to match the pattern `refl`!

Finally, if we go back into the hole and type `C-C C-R` it will
instantiate the hole with the one constructor that yields a value of
the expected type.

    sym : ∀ {A : Set} {x y : A} →  x ≡ y → y ≡ x
    sym refl = refl

This completes the definition as given above.

Transitivity is equally straightforward.
\begin{code}
trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl
\end{code}
Again, a useful exercise is to carry out an interactive development, checking
how Agda's knowledge changes as each of the two arguments is
instantiated.

## Congruence and substitution

Equality satisfies *congruence*.  If two terms are equal,
they remain so after the same function is applied to both.
\begin{code}
cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl
\end{code}

Equality is also a congruence in the application position.
If two functions are equal, then applying them to the same term
yields equal terms.
\begin{code}
cong-app : ∀ {A B : Set} {f g : A → B} → f ≡ g → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl
\end{code}

Equality also satisfies *substitution*.
If two values are equal and a predicate holds of the first then it also holds of the second.
\begin{code}
subst : ∀ {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
subst P refl px = px
\end{code}


## Chains of equations

Here we show how to support reasoning with chains of equations
as used throughout the book.  We package the declarations
into a module, named `≡-Reasoning`, to match the format used in Agda's
standard library.
\begin{code}
module ≡-Reasoning {A : Set} where

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

As an example, let's look at a proof of transitivity
as a chain of equations.
\begin{code}
trans′ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans′ {A} {x} {y} {z} x≡y y≡z =
  begin
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎
\end{code}
According to the fixity declarations, the body parses as follows:

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
After simplification, the body is equivalent to the term:

    trans x≡y (trans y≡z refl)

We could replace any use of a chain of equations by a chain of
applications of `trans`; the result would be more compact but harder
to read.  The trick behind `∎` means that a chain of equalities simplifies
to a chain of applications of `trans` than ends in `trans e refl`,
where `e` is a term that proves some equality, even though `e` alone would do.


## Chains of equations, another example

As a second example of chains of equations, we repeat the proof that addition
is commutative.  We first repeat the definitions of naturals and addition.
We cannot import them because (as noted at the beginning of this chapter)
it would cause a conflict.
\begin{code}
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)
\end{code}

To save space we postulate (rather than prove in full) two lemmas.
\begin{code}
postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
\end{code}
This is our first use of a *postulate*.  A postulate specifies a
signature for an identifier but no definition.  Here we postulate
something proved earlier to save space.  Postulates must be used with
caution.  If we postulate something false then we could use Agda to
prove anything whatsoever.

We then repeat the proof of commutativity.
\begin{code}
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
\end{code}
The reasoning here is similar to that in the
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
separated by `≡⟨⟩` have the same simplified form; it's up to us to write
them in an order that will make sense to the reader.


## Rewriting

Consider a property of natural numbers, such as being even.
We repeat the earlier definition.
\begin{code}
data even : ℕ → Set
data odd  : ℕ → Set

data even where
  even-zero : even zero
  even-suc  : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  odd-suc   : ∀ {n : ℕ} → even n → odd (suc n)
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
than chains of equalities.
\begin{code}
+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ zero n rewrite +-identity n = refl
+-comm′ (suc m) n rewrite +-suc n m | +-comm m n = refl
\end{code}
This is far more compact.  Among other things, whereas the previous
proof required `cong suc (+-comm m n)` as the justification to invoke the
inductive hypothesis, here it is sufficient to rewrite with `+-comm m n`, as
rewriting automatically takes congruence into account.  Although proofs
with rewriting are shorter, proofs as chains of equalities are easier to follow,
and we will stick with the latter when feasible.


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
appropriate equivalence.  Note the use of the "dot pattern", `.(n + m)`.
A dot pattern is followed by an expression and is made when
other information forces the value matched to be equal to the value of
the expression in the dot pattern.  In this case, the identification
of `m + n` and `n + m` is justified by the subsequent matching of
`+-comm m n` against `refl`.  One might think that the first clause is
redundant as the information is inherent in the second clause, but in
fact Agda is rather picky on this point: omitting the first clause or
reversing the order of the clauses will cause Agda to report an error.
(Try it and see!)

In this case, we can avoid rewrite by simply applying substitution.
\begin{code}
even-comm″ : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm″ m n  =  subst even (+-comm m n)
\end{code}
Nonetheless, rewrite is a vital part of the Agda toolkit,
as earlier examples have shown.


## Extensionality {#extensionality}

Extensionality asserts that they only way to distinguish functions is
by applying them; if two functions applied to the same argument always
yield the same result, then they are the same functions.  It is the
converse of `cong-app`, introduced earlier.

Agda does not presume extensionality, but we can postulate that it holds.
\begin{code}
postulate
  extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g
\end{code}
Postulating extensionality does not lead to difficulties, as it is
known to be consistent with the theory that underlies Agda.

As an example, consider that we need results from two libraries,
one where addition is defined as above, and one where it is
defined the other way around.
\begin{code}
_+′_ : ℕ → ℕ → ℕ
m +′ zero  = m
m +′ suc n = suc (m +′ n)
\end{code}
Applying commutativity, it is easy to show that both operators always
return the same result given the same arguments.
\begin{code}
same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m n rewrite +-comm m n = helper m n
  where
  helper : ∀ (m n : ℕ) → m +′ n ≡ n + m
  helper m zero    = refl
  helper m (suc n) = cong suc (helper m n)
\end{code}
However, it might be convenient to assert that the two operators are
actually indistinguishable. This we can do via two applications of
extensionality.
\begin{code}
same : _+′_ ≡ _+_
same = extensionality λ{m → extensionality λ{n → same-app m n}}
\end{code}
We will occasionally have need to postulate extensionality in what follows.


## Leibniz equality

The form of asserting equivalence that we have used is due to Martin Löf,
and was published in 1975.  An older form is due to Leibniz, and was published
in 1686.  Leibniz asserted the *identity of indiscernibles*: two objects are
equal if and only if they satisfy the same properties. This
principle sometimes goes by the name Leibniz' Law, and is closely
related to Spock's Law, ``A difference that makes no difference is no
difference''.  Here we define Leibniz equality, and show that two terms
satisfy Leibniz equality if and only if they satisfy Martin Löf equivalence.

Leibniz equality is usually formalised to state that `x ≐ y`
holds if every property `P` that holds of `x` also holds of
`y`.  Perhaps surprisingly, this definition is
sufficient to also ensure the converse, that every property `P` that
holds of `y` also holds of `x`.

Let `x` and `y` be objects of type $A$. We say that `x ≐ y` holds if
for every predicate $P$ over type $A$ we have that `P x` implies `P y`.
\begin{code}
_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y
\end{code}
One might expect to write the left-hand side of the equation as `x ≐ y`,
but instead we write `_≐_ {A} x y` to provide access to the implicit
parameter `A` which appears on the right-hand side.

This is our first use of *levels*.  We cannot assign `Set` the type
`Set`, since this would lead to contradictions such as Russel's
Paradox and Girard's Paradox.  Instead, there is a hierarchy of types,
where `Set : Set₁`, `Set₁ : Set₂`, and so on.  In fact, `Set` itself
is just an abbreviation for `Set₀`.  Since the equation defining `_≐_`
mentions `Set` on the right-hand side, the corresponding signature
must use `Set₁`.  Further information on levels can be found in
the [Agda Wiki][wiki].

[wiki]: http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.UniversePolymorphism

Leibniz equality is reflexive and transitive,
where the first follows by a variant of the identity function
and the second by a variant of function composition.
\begin{code}
refl-≐ : ∀ {A : Set} {x : A} → x ≐ x
refl-≐ P Px  =  Px

trans-≐ : ∀ {A : Set} {x y z : A} → x ≐ y → y ≐ z → x ≐ z
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
sym-≐ : ∀ {A : Set} {x y : A} → x ≐ y → y ≐ x
sym-≐ {A} {x} {y} x≐y P  =  Qy
  where
    Q : A → Set
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
≡-implies-≐ : ∀ {A : Set} {x y : A} → x ≡ y → x ≐ y
≡-implies-≐ x≡y P = subst P x≡y
\end{code}
This direction follows from substitution, which we showed earlier.

In the reverse direction, given that for any `P` we can take a proof of `P x`
to a proof of `P y` we need to show `x ≡ y`. The proof is similar to that
for symmetry of Leibniz equality. We take `Q`
to be the predicate that holds of `z` if `x ≡ z`. Then `Q x` is trivial
by reflexivity of Martin Löf equivalence, and hence `Q y` follows from
`x ≐ y`.  But `Q y` is exactly a proof of what we require, that `x ≡ y`.
\begin{code}
≐-implies-≡ : ∀ {A : Set} {x y : A} → x ≐ y → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y = Qy
  where
    Q : A → Set
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


## Universe polymorphism {#unipoly}

As we have seen, not every type belongs to `Set`, but instead every
type belongs somewhere in the hierarchy `Set₀`, `Set₁`, `Set₂`, and so on,
where `Set` abbreviates `Set₀`, and `Set₀ : Set₁`, `Set₁ : Set₂`, and so on.
The definition of equality given above is fine if we want to compare two
values of a type that belongs to `Set`, but what if we want to compare
two values of a type that belongs to `Set ℓ` for some arbitrary level `ℓ`?

The answer is *universe polymorphism*, where a definition is made
with respect to an arbitrary level `ℓ`. To make use of levels, we
first import the following.
\begin{code}
open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
\end{code}
Levels are isomorphic to natural numbers, and have similar constructors:

    lzero : Level
    lsuc  : Level → Level

The names `Set₀`, `Set₁`, `Set₂` and so on are abbreviations for

    Set lzero
    Set (lsuc lzero)
    Set (lsuc (lsuc lzero))

and so on. There is also an operator

    _⊔_ : Level → Level → Level

that given two levels returns the larger of the two.

Here is the definition of equality, generalised to an arbitrary level.
\begin{code}
data _≡′_ {ℓ : Level} {A : Set ℓ} : A → A → Set ℓ where
  refl′ : ∀ {x : A} → x ≡′ x
\end{code}
Similarly, here is the generalised definition of symmetry.
\begin{code}
sym′ : ∀ {ℓ : Level} {A : Set ℓ} {x y : A} →  x ≡′ y → y ≡′ x
sym′ refl′ = refl′
\end{code}
For simplicity, we avoid universe polymorphism in the definitions given in
the text, but most definitions in the standard library, including those for
equality, are generalised to arbitrary levels as above.

Here is the generalised definition of Leibniz equality.
\begin{code}
_≐′_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐′_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y
\end{code}
Before the signature used `Set₁` as the type of a term that includes
`Set`, whereas here the signature uses `Set (suc ℓ)` as the type of a
term that includes `Set ℓ`.


## Standard library

Definitions similar to those in this chapter can be found in the standard library.

    import Relation.Binary.PropositionalEquality as Eq
    open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
    open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

Here the import is shown as comment rather than code to avoid collisions,
as mentioned in the introduction.


## Unicode

This chapter uses the following unicode.

    ≡  U+2261  IDENTICAL TO (\==)  =
    ⟨  U+27E8  MATHEMATICAL LEFT ANGLE BRACKET (\<)
    ⟩  U+27E9  MATHEMATICAL RIGHT ANGLE BRACKET (\>)
    ∎  U+220E  END OF PROOF (\qed)
    ≐  U+2250  APPROACHES THE LIMIT (\.=)
    ℓ  U+2113  SCRIPT SMALL L (\ell)
