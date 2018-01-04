---
title     : "Relations: Inductive Definition of Relations"
layout    : page
permalink : /Relations
---

After having defined operations such as addition and multiplication,
the next step is to define relations, such as *less than or equal*.

## Imports

\begin{code}
open import Naturals using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Properties using (com+; com+zero; com+suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
\end{code}

## Defining relations

The relation *less than or equal* has an infinite number of
instances.  Here are just a few of them:

   0 ≤ 0     0 ≤ 1     0 ≤ 2     0 ≤ 3     ...
             1 ≤ 1     1 ≤ 2     1 ≤ 3     ...
                       2 ≤ 2     2 ≤ 3     ...
                                 3 ≤ 3     ...
                                           ...

And yet, we can write a finite definition that encompasses
all of these instances in just a few lines.  Here is the
definition as a pair of inference rules:

    z≤n --------
        zero ≤ n

        m ≤ n
    s≤s -------------
        suc m ≤ suc n

And here is the definition in Agda:
\begin{code}
data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {m : ℕ} → zero ≤ m
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n
\end{code}
Here `z≤n` and `s≤s` (with no spaces) are constructor names,
while `m ≤ m`, and `m ≤ n` and `suc m ≤ suc n` (with spaces)
are propositions.

Both definitions above tell us the same two things:

+ *Base case*: for all naturals `n`, the proposition `zero ≤ n` holds
+ *Inductive case*: for all naturals `m` and `n`, if the proposition
  `m ≤ n` holds, then the proposition `suc m ≤ suc n` holds.

In fact, they each give us a bit more detail:

+ *Base case*: for all naturals `n`, the constructor `z≤n` 
  produces evidence that `zero ≤ n` holds.
+ *Inductive case*: for all naturals `m` and `n`, the constructor
  `s≤s` takes evidence that `m ≤ n` holds into evidence that
  `suc m ≤ suc n` holds.

Here we have used the word *evidence* as interchangeable with the
word *proof*.  We will tend to say *evidence* when we want to stress
that proofs are just terms in Agda.

For example, here in inference rule notation is the proof that
`2 ≤ 4`.

      z≤n -----
          0 ≤ 2
     s≤s -------
          1 ≤ 3
    s≤s ---------
          2 ≤ 4

And here is the corresponding Agda proof.
\begin{code}
ex₁ : 2 ≤ 4
ex₁ = s≤s (s≤s z≤n)
\end{code}

## Implicit arguments

In the Agda definition, the two lines defining the constructors
use `∀`, very similar to our use of `∀` in propositions such as:

    com+ : ∀ (m n : ℕ) → m + n ≡ n + m

However, here the declarations are surrounded by curly braces `{ }`
rather than parentheses `( )`.  This means that the arguments are
*implicit* and need not be written explicitly.  Thus, we would write,
for instance, `com+ m n` for the proof that `m + n ≡ n + m`, but
here will write `z≤n` for the proof that `m ≤ m`, leaving the `m` implicit,
or if `m≤n` is evidence that `m ≤ n`, we write write `s≤s m≤n` for the
evidence that `suc m ≤ suc n`, leaving both `m` and `n` implicit.

It is possible to provide implicit arguments explicitly if we wish, by
writing the arguments inside curly braces.  For instance, here is the
Agda proof that `2 ≤ 4` repeated, with the implicit arguments made
explicit.
\begin{code}
ex₂ : 2 ≤ 4
ex₂ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))
\end{code}

## Precedence

We declare the precedence for comparison as follows.
\begin{code}
infix 4 _≤_
\end{code}
We set the precedence of `_≤_` at level 4, which means it binds less
tightly that `_+_` at level 6 or `_*_` at level 7, meaning that `1 + 2
≤ 3` parses as `(1 + 2) ≤ 3`.  We write `infix` to indicate that the
operator does not associate to either the left or right, as it makes
no sense to give `1 ≤ 2 ≤ 3` either the meaning `(1 ≤ 2) ≤ 3` or `1 ≤
(2 ≤ 3)`.

## Properties of ordering relations

Relations occur all the time, and mathematicians have agreed
on names for some of the most common properties.

+ *Reflexive* For all `n`, the relation `n ≤ n` holds.
+ *Transitive* For all `m`, `n`, and `p`, if `m ≤ n` and
`n ≤ p` hold, then `m ≤ p` holds.
+ *Anti-symmetric* For all `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds.
+ *Total* For all `m` and `n`, either `m ≤ n` or `n ≤ m`
holds.

The relation `_≤_` satisfies all four of these properties.

There are also names for some combinations of these properties.

+ *Preorder* Any relation that is reflexive and transitive.
+ *Partial order* Any preorder that is also anti-symmetric.
+ *Total order* Any partial order that is also total.

If you ever bump into a relation at a party, you now know how
to make small talk, by asking it whether it is reflexive, transitive,
anti-symmetric, and total. Or instead you might ask whether it is a
preorder, partial order, or total order.

Less frivolously, if you ever bump into a relation while reading
a technical paper, this gives you an easy way to orient yourself,
by checking whether or not it is a preorder, partial order, or total order.
A careful author will often make it explicit, for instance by saying
that a given relation is a preoder but not a partial order, or a
partial order but not a total order. (Can you think of examples of
such relations?)


## Reflexivity

The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.
\begin{code}
refl≤ : ∀ (n : ℕ) → n ≤ n
refl≤ zero = z≤n
refl≤ (suc n) = s≤s (refl≤ n)
\end{code}
The proof is a straightforward induction on `n`.  In the base case,
`zero ≤ zero` holds by `z≤n`.  In the inductive case, the inductive
hypothesis `refl≤ n` gives us a proof of `n ≤ n`, and applying `s≤s`
to that yields a proof of `suc n ≤ suc n`.

It is a good exercise to prove reflexivity interactively in Emacs,
using holes and the `^C ^C`, `^C ^,`, and `^C ^R` commands.


## Transitivity

The second property to prove about comparison is that it is
transitive: for any naturals `m`, `n`, andl `p`, if `m ≤ n` and `n ≤
p` hold, then `m ≤ p` holds.
\begin{code}
trans≤ : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
trans≤ z≤n _ = z≤n
trans≤ (s≤s m≤n) (s≤s n≤p) = s≤s (trans≤ m≤n n≤p)
\end{code}
Here the proof is most easily thought of as by induction on the
*evidence* that `m ≤ n`, so we have left `m`, `n`, and `p` implicit.

In the base case, `m ≤ n` holds by `z≤n`, so it must be that
`m` is `zero`, in which case `m ≤ p` also holds by `z≤n`. In this
case, the fact that `n ≤ p` is irrelevant, and we write `_` as the
pattern to indicate that the corresponding evidence is unused. We
could instead have written `n≤p` but not used that variable on the
right-hand side of the equation.

In the inductive case, `m ≤ n` holds by `s≤s m≤n`, so it must be that `m`
is `suc m′` and `n` is `suc n′` for some `m′` and `n′`, and `m≤n` is
evidence that `m′ ≤ n′`.  In this case, the only way that `p ≤ n` can
hold is by `s≤s n≤p`, where `p` is `suc p′` for some `p′` and `n≤p` is
evidence that `n′ ≤ p′`.  The inductive hypothesis `trans≤ m≤n n≤p`
provides evidence that `m′ ≤ p′`, and applying `s≤s` to that gives
evidence of the desired conclusion, `suc m′ ≤ suc p′`.

The case `trans≤ (s≤s m≤n) z≤n` cannot arise, since the first piece of
evidence implies `n` must be `suc n′` for some `n′` while the second
implies `n` must be `zero`.  Agda can determine that such a case cannot
arise, and does not require it to be listed.

Alternatively, we could make the implicit parameters explicit.
\begin{code}
trans≤′ : ∀ (m n p : ℕ) → m ≤ n → n ≤ p → m ≤ p
trans≤′ zero n p z≤n _ = z≤n
trans≤′ (suc m) (suc n) (suc p) (s≤s m≤n) (s≤s n≤p) = s≤s (trans≤′ m n p m≤n n≤p)
\end{code}
One might argue that this is clearer, since it shows us the forms of `m`, `n`,
and `p`, or one might argue that the extra length obscures the essence of the
proof.  We will usually opt for shorter proofs.

The technique of inducting on evidence that a property holds (e.g.,
inducting on evidence that `m ≤ n`)---rather than induction on the
value of which the property holds (e.g., inducting on `m`)---will turn
out to be immensely valuable, and one that we use often.

Again, it is a good exercise to prove transitivity interactively in Emacs,
using holes and the `^C ^C`, `^C ^,`, and `^C ^R` commands.

## Anti-symmetry

The third property to prove about comparison is that it is antisymmetric:
for all naturals `m` and `n`, if both `m ≤ n` and `n ≤ m` hold, then
`m ≡ n` holds.
\begin{code}
antisym≤ : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
antisym≤ z≤n z≤n = refl
antisym≤ (s≤s m≤n) (s≤s n≤m) rewrite antisym≤ m≤n n≤m = refl
\end{code}
Again, the proof is by induction over the evidence that `m ≤ n`
and `n ≤ m` hold, and so we have left `m` and `n` implicit.

In the base case, both relations hold by `z≤n`,
so it must be the case that `m` and `n` are both `zero`,
in which case `m ≡ n` holds by reflexivity. (The reflexivity
of equivalance, that is, not the reflexivity of comparison.)

In the inductive case, `m ≤ n` holds by `s≤s m≤n` and `n ≤ m` holds by
`s≤s n≤m`, so it must be that `m` is `suc m′` and `n` is `suc n′`, for
some `m′` and `n′`, where `m≤n` is evidence that `m′ ≤ n′` and `n≤m`
is evidence that `n′ ≤ m′`.  The inductive hypothesis `antisym≤ m≤n n≤m`
establishes that `m′ ≡ n′`, and rewriting by this equation establishes
that `m ≡ n` holds by reflexivity.

## Disjunction

In order to state totality, we need a way to formalise disjunction,
the notion that given two propositions either one or the other holds.
In Agda, we do so by declaring a suitable inductive type.
\begin{code}
data _⊎_ : Set → Set → Set where
  left  : ∀ {A B : Set} → A → A ⊎ B
  right : ∀ {A B : Set} → B → A ⊎ B
\end{code}
This tells us that if `A` and `B` are propositions then `A ⊎ B` is
also a proposition.  Evidence that `A ⊎ B` holds is either of the form
`left a`, where `a` is evidence that `A` holds, or `right b`, where
`b` is evidence that `B` holds.

We set the precedence of disjunction so that it binds less tightly
than comparison.
\begin{code}
infix 1 _⊎_
\end{code}
Thus, `m ≤ n ⊎ n ≤ m` parses as `(m ≤ n) ⊎ (n ≤ m)`.

## Total

The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.
\begin{code}
total≤ : ∀ (m n : ℕ) → m ≤ n ⊎ n ≤ m
total≤ zero n =  left z≤n
total≤ (suc m) zero =  right z≤n
total≤ (suc m) (suc n) with total≤ m n
... | left m≤n = left (s≤s m≤n)
... | right n≤m = right (s≤s n≤m)
\end{code}
In this case the proof is by induction over both the first
and second arguments.  We perform a case analysis:

+ *First base case*: If the first argument is `zero` and the
  second argument is `n` then
  the left disjunct holds, with `z≤n` as evidence that `zero ≤ n`.

+ *Second base case*: If the first argument is `suc m` and the
  second argument is `n` then the right disjunct holds, with
  `z≤n` as evidence that `n ≤ m`.

+ *Inductive case*: If the first argument is `suc m` and the
  second argument is `suc n`, then the inductive hypothesis
  `total≤ m n` establishes one of the following:

  - The left disjunct of the inductive hypothesis holds with `m≤n` as
    evidence that `m ≤ n`, in which case the left disjunct of the
    proposition holds with `s≤s m≤n` as evidence that `suc m ≤ suc n`.

  - The right disjunct of the inductive hypothesis holds with `n≤m` as
    evidence that `n ≤ m`, in which case the right disjunct of the
    proposition holds with `s≤s n≤m` as evidence that `suc n ≤ suc m`.

This is our first use of the `with` clause in Agda.  The keyword
`with` is followed by an expression, and one or more subsequent lines.
Each line begins with an ellipsis (`...`) and a vertical bar (`|`),
followed by a pattern to be matched against the expression, an equal
sign, and the right-hand side of the equation.

Every use of `with` is equivalent to defining a helper function.  For
example, the definition above is equivalent to the following.
\begin{code}
total≤′ : ∀ (m n : ℕ) → m ≤ n ⊎ n ≤ m
total≤′ zero n = left z≤n
total≤′ (suc m) zero = right z≤n
total≤′ (suc m) (suc n) = helper (total≤′ m n)
  where
  helper : m ≤ n ⊎ n ≤ m → suc m ≤ suc n ⊎ suc n ≤ suc m
  helper (left m≤n) = left (s≤s m≤n)
  helper (right n≤m) = right (s≤s n≤m)
\end{code}
This is also our first use of a `where` clause in Agda.  The keyword
`where` is followed by one or more definitions, which must be
indented.  Any identifiers bound in the nested definition are in scope
in the right-hand side of the preceding equation (in this case,
`helper`), and any variables bound of the left-hand side of the
preceding equation are in scope within the nested definition (in this
case, `m` and `n`).

If both arguments are equal, then both the left and right disjuncts
hold and we could return evidence of either.  In the code above we
always return the left disjunct, but there is a minor variant that
always returns the right disjunct.
\begin{code}
total≤″ : ∀ (m n : ℕ) → m ≤ n ⊎ n ≤ m
total≤″ m zero =  right z≤n
total≤″ zero (suc n) =  left z≤n
total≤″ (suc m) (suc n) with total≤″ m n
... | left m≤n = left (s≤s m≤n)
... | right n≤m = right (s≤s n≤m)
\end{code}


## Monotonicity

If one bumps into both an operator and an order relation at
a party, one may ask if the operator is *monotonic* with regard
to the order relation.  For example, addition is monotonic
with regard to comparison, meaning

  ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

Addition (precedence level 6) binds more tightly than comparison
(precedence level 4), so `m + n ≤ p + q` parses as
`(m + n) ≤ (p + q)`.

The proof is straightforward using the techniques we have learned,
and is best broken into three parts. First, we deal with the special
case where the left arguments of addition are identical.
\begin{code}
mono+≤l : ∀ (m p q : ℕ) → p ≤ q → m + p ≤ m + q
mono+≤l zero p q p≤q =  p≤q
mono+≤l (suc m) p q p≤q =  s≤s (mono+≤l m p q p≤q) 
\end{code}
The proof is by induction on the first argument.

+ *Base case*: The first argument is `zero` in which case
  `zero + p ≤ zero + q` simplifies to `p ≤ q`, the evidence
  for which is given by the explicit argument `p≤q`.

+ *Inductive case*: The first argument is `suc m`, in which case
  `suc m + p ≤ suc m + q` simplifies to `suc (m + p) ≤ suc (m + q)`.
  The inductive hypothesis `mono+≤₁ {m} p≤q` establishes that
  `m + p ≤ m + q`, from which the desired conclusion follows
  by an application of `s≤s`.

Second, we deal with the special case where the right arguments
of the addition are identical. This follows from the previous
result and the commutativity of addition.
\begin{code}
mono+≤r : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
mono+≤r m n p m≤n rewrite com+ m p | com+ n p = mono+≤l p m n m≤n
\end{code}
Rewriting by `com+ m p` and `com+ n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `mono+≤left p m n m≤n`.

Third, we combine the two previous results.
\begin{code}
mono+≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
mono+≤ m n p q m≤n p≤q = trans≤ (mono+≤r m n p m≤n) (mono+≤l n p q p≤q)
\end{code}
Invoking `mono+≤r m n p m≤n` proves `m + p ≤ n + p` and invoking
`mono+≤l n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.


## Other results --- use these as exercises

\begin{code}
assoc+∸ : ∀ (m n : ℕ) → m ≤ n → m + (n ∸ m) ≡ n
assoc+∸ zero n z≤n = refl
assoc+∸ (suc m) (suc n) (s≤s m≤n) rewrite assoc+∸ m n m≤n = refl

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ} → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

infix 4 _<_

<implies≤ : ∀ {m n : ℕ} → m < n → suc m ≤ n
<implies≤ z<s = s≤s z≤n
<implies≤ (s<s m<n) = s≤s (<implies≤ m<n)

≤implies< : ∀ {m n : ℕ} → suc m ≤ n → m < n
≤implies< (s≤s z≤n) = z<s
≤implies< (s≤s (s≤s m≤n)) = s<s (≤implies< (s≤s m≤n))
\end{code}

## Trichotomy

\begin{code}
_>_ : ℕ → ℕ → Set
n > m = m < n

infix 4 _>_

data Trichotomy : ℕ → ℕ → Set where
  less : ∀ {m n : ℕ} → m < n → Trichotomy m n
  same : ∀ {m n : ℕ} → m ≡ n → Trichotomy m n
  more : ∀ {m n : ℕ} → m > n → Trichotomy m n

trichotomy : ∀ (m n : ℕ) → Trichotomy m n
trichotomy zero zero = same refl
trichotomy zero (suc n) = less z<s
trichotomy (suc m) zero = more z<s
trichotomy (suc m) (suc n) with trichotomy m n
... | less m<n = less (s<s m<n)
... | same refl = same refl
... | more n<m = more (s<s n<m)

\end{code}

## Unicode

In this chapter we use the following unicode.

    ≡  U+2261  IDENTICAL TO (\==)
    ∀  U+2200  FOR ALL (\forall)
    λ  U+03BB  GREEK SMALL LETTER LAMBDA (\Gl, \lambda)
