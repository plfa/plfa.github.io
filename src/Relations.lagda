---
title     : "Relations: Inductive definition of relations"
layout    : page
permalink : /Relations
---

After having defined operations such as addition and multiplication,
the next step is to define relations, such as *less than or equal*.


## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Nat.Properties using (+-comm; +-suc)
\end{code}


## Defining relations

The relation *less than or equal* has an infinite number of
instances.  Here are a few of them:

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
are types.  This is our first use of an *indexed* datatype,
where we say the type `m ≤ n` is indexed by two naturals, `m` and `n`.

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
_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)
\end{code}


## Implicit arguments

This is our first use of implicit arguments.
In the definition of inequality, the two lines defining the constructors
use `∀`, very similar to our use of `∀` in propositions such as:

    +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

However, here the declarations are surrounded by curly braces `{ }` rather than
parentheses `( )`.  This means that the arguments are *implicit* and need not be
written explicitly; instead, they are *inferred* by Agda's typechecker. Thus, we
write `+-comm m n` for the proof that `m + n ≡ n + m`, but `z≤n` for the proof
that `m ≤ m`, leaving `m` implicit.  Similarly, if `m≤n` is evidence that `m ≤
n`, we write write `s≤s m≤n` for evidence that `suc m ≤ suc n`, leaving both `m`
and `n` implicit.

If we wish, it is possible to provide implicit arguments explicitly by
writing the arguments inside curly braces.  For instance, here is the
Agda proof that `2 ≤ 4` repeated, with the implicit arguments made
explicit.
\begin{code}
_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))
\end{code}


## Precedence

We declare the precedence for comparison as follows.
\begin{code}
infix 4 _≤_
\end{code}
We set the precedence of `_≤_` at level 4, so it binds less tightly
that `_+_` at level 6 and hence `1 + 2 ≤ 3` parses as `(1 + 2) ≤ 3`.
We write `infix` to indicate that the operator does not associate to
either the left or right, as it makes no sense to parse `1 ≤ 2 ≤ 3` as
either `(1 ≤ 2) ≤ 3` or `1 ≤ (2 ≤ 3)`.


## Decidability

Given two numbers, it is straightforward to compute whether or not the first is
less than or equal to the second.  We don't give the code for doing so here, but
will return to this point in Chapter [Decidability](Decidability).


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
that a given relation is a preorder but not a partial order, or a
partial order but not a total order. (Can you think of examples of
such relations?)


## Reflexivity

The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.
\begin{code}
≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s (≤-refl {n})
\end{code}
The proof is a straightforward induction on `n`.  In the base case,
`zero ≤ zero` holds by `z≤n`.  In the inductive case, the inductive
hypothesis `≤-refl n` gives us a proof of `n ≤ n`, and applying `s≤s`
to that yields a proof of `suc n ≤ suc n`.

It is a good exercise to prove reflexivity interactively in Emacs,
using holes and the `^C ^C`, `^C ^,`, and `^C ^R` commands.


## Transitivity

The second property to prove about comparison is that it is
transitive: for any naturals `m`, `n`, and `p`, if `m ≤ n` and `n ≤
p` hold, then `m ≤ p` holds.
\begin{code}
≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)
\end{code}
Here the proof is most easily thought of as by induction on the
*evidence* that `m ≤ n`, so we have left `m`, `n`, and `p` implicit.

In the base case, the first inequality holds by `z≤n`, and so
we are given `zero ≤ n` and `n ≤ p` and must show `zero ≤ p`,
which follows immediately by `z≤n`.  In this
case, the fact that `n ≤ p` is irrelevant, and we write `_` as the
pattern to indicate that the corresponding evidence is unused.

In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality by `s≤s n≤p`, and so we are given
`suc m ≤ suc n` and `suc n ≤ suc p`, and must show `suc m ≤ suc p`.
The inductive hypothesis `≤-trans m≤n n≤p` establishes
that `m ≤ p`, and our goal follows by applying `s≤s`.

<!--

In the base case, `m ≤ n` holds by `z≤n`, so it must be that
`m` is `zero`, in which case `m ≤ p` also holds by `z≤n`. In this
case, the fact that `n ≤ p` is irrelevant, and we write `_` as the
pattern to indicate that the corresponding evidence is unused.

In the inductive case, `m ≤ n` holds by `s≤s m≤n`, so it must be that `m`
is `suc m′` and `n` is `suc n′` for some `m′` and `n′`, and `m≤n` is
evidence that `m′ ≤ n′`.  In this case, the only way that `p ≤ n` can
hold is by `s≤s n≤p`, where `p` is `suc p′` for some `p′` and `n≤p` is
evidence that `n′ ≤ p′`.  The inductive hypothesis `≤-trans m≤n n≤p`
provides evidence that `m′ ≤ p′`, and applying `s≤s` to that gives
evidence of the desired conclusion, `suc m′ ≤ suc p′`.

-->

The case `≤-trans (s≤s m≤n) z≤n` cannot arise, since the first
inequality implies the middle value is `suc n` while the second
inequality implies that it is `zero`.  Agda can determine that
such a case cannot arise, and does not require it to be listed.

Alternatively, we could make the implicit parameters explicit.
\begin{code}
≤-trans′ : ∀ (m n p : ℕ) → m ≤ n → n ≤ p → m ≤ p
≤-trans′ zero n p z≤n _ = z≤n
≤-trans′ (suc m) (suc n) (suc p) (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans′ m n p m≤n n≤p)
\end{code}
One might argue that this is clearer or one might argue that the extra
length obscures the essence of the proof.  We will usually opt for
shorter proofs.

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
≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)
\end{code}
Again, the proof is by induction over the evidence that `m ≤ n`
and `n ≤ m` hold, and so we have left `m` and `n` implicit.

In the base case, both inequalities hold by `z≤n`,
and so we are given `zero ≤ zero` and `zero ≤ zero` and must
show `zero ≡ zero`, which follows by reflexivity.  (Reflexivity
of equality, that is, not reflexivity of inequality.)

In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality holds by `s≤s n≤m`, and so we are
given `suc m ≤ suc n` and `suc n ≤ suc m` and must show `suc m ≡ suc n`.
The inductive hypothesis `≤-antisym m≤n n≤m` establishes that `m ≡ n`,
and our goal follows by congruence.


## Total

The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.

We specify what it means for inequality to be total.
\begin{code}
data Total (m n : ℕ) : Set where
  forward : m ≤ n → Total m n
  flipped : n ≤ m → Total m n
\end{code}
Evidence that `Total m n` holds is either of the form
`forward m≤n` or `flipped n≤m`, where `m≤n` and `n≤m` are
evidence of `m ≤ n` and `n ≤ m` respectively.

This is our first use of a datatype with *parameters*,
in this case `m` and `n`.  It is equivalent to the following
indexed datatype.
\begin{code}
data Total′ : ℕ → ℕ → Set where
  forward′ : ∀ {m n : ℕ} → m ≤ n → Total′ m n
  flipped′ : ∀ {m n : ℕ} → n ≤ m → Total′ m n
\end{code}
Each parameter of the type translates as an implicit
parameter of each constructor.
Unlike an indexed datatype, where the indexes can vary
(as in `zero ≤ n` and `suc m ≤ suc n`), in a parameterised
datatype the parameters must always be the same (as in `Total m n`).
Parameterised declarations are shorter, easier to read, and let Agda
exploit the uniformity of the parameters, so we will use them in
preference to indexed types when possible.

With that preliminary out of the way, we specify and prove totality.
\begin{code}
≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n                         =  forward z≤n
≤-total (suc m) zero                      =  flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n  =  forward (s≤s m≤n)
...                        | flipped n≤m  =  flipped (s≤s n≤m)
\end{code}
In this case the proof is by induction over both the first
and second arguments.  We perform a case analysis:

+ *First base case*: If the first argument is `zero` and the
  second argument is `n` then the forward case holds, 
  with `z≤n` as evidence that `zero ≤ n`.

+ *Second base case*: If the first argument is `suc m` and the
  second argument is `zero` then the flipped case holds, with
  `z≤n` as evidence that `zero ≤ suc m`.

+ *Inductive case*: If the first argument is `suc m` and the
  second argument is `suc n`, then the inductive hypothesis
  `≤-total m n` establishes one of the following:

  - The forward case of the inductive hypothesis holds with `m≤n` as
    evidence that `m ≤ n`, from which it follows that the forward case of the
    proposition holds with `s≤s m≤n` as evidence that `suc m ≤ suc n`.

  - The flipped case of the inductive hypothesis holds with `n≤m` as
    evidence that `n ≤ m`, from which it follows that the flipped case of the
    proposition holds with `s≤s n≤m` as evidence that `suc n ≤ suc m`.

This is our first use of the `with` clause in Agda.  The keyword
`with` is followed by an expression and one or more subsequent lines.
Each line begins with an ellipsis (`...`) and a vertical bar (`|`),
followed by a pattern to be matched against the expression
and the right-hand side of the equation.

Every use of `with` is equivalent to defining a helper function.  For
example, the definition above is equivalent to the following.
\begin{code}
≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero    n        =  forward z≤n
≤-total′ (suc m) zero     =  flipped z≤n
≤-total′ (suc m) (suc n)  =  helper (≤-total′ m n)
  where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward m≤n)  =  forward (s≤s m≤n)
  helper (flipped n≤m)  =  flipped (s≤s n≤m)
\end{code}
This is also our first use of a `where` clause in Agda.  The keyword `where` is
followed by one or more definitions, which must be indented.  Any variables
bound of the left-hand side of the preceding equation (in this case, `m` and
`n`) are in scope within the nested definition, and any identifiers bound in the
nested definition (in this case, `helper`) are in scope in the right-hand side
of the preceding equation.

If both arguments are equal, then both cases hold and we could return evidence
of either.  In the code above we return the forward case, but there is a
variant that returns the flipped case.
\begin{code}
≤-total″ : ∀ (m n : ℕ) → Total m n
≤-total″ m       zero                      =  flipped z≤n
≤-total″ zero    (suc n)                   =  forward z≤n
≤-total″ (suc m) (suc n) with ≤-total″ m n
...                        | forward m≤n   =  forward (s≤s m≤n)
...                        | flipped n≤m   =  flipped (s≤s n≤m)
\end{code}
It differs from the original code in that it pattern
matches on the second argument before the first argument.


## Monotonicity

If one bumps into both an operator and an ordering at a party, one may ask if
the operator is *monotonic* with regard to the ordering.  For example, addition
is monotonic with regard to inequality, meaning

  ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

The proof is straightforward using the techniques we have learned, and is best
broken into three parts. First, we deal with the special case of showing
addition is monotonic on the right.
\begin{code}
+-monoʳ-≤ : ∀ (m p q : ℕ) → p ≤ q → m + p ≤ m + q
+-monoʳ-≤ zero    p q p≤q  =  p≤q
+-monoʳ-≤ (suc m) p q p≤q  =  s≤s (+-monoʳ-≤ m p q p≤q) 
\end{code}
The proof is by induction on the first argument.

+ *Base case*: The first argument is `zero` in which case
  `zero + p ≤ zero + q` simplifies to `p ≤ q`, the evidence
  for which is given by the argument `p≤q`.

+ *Inductive case*: The first argument is `suc m`, in which case
  `suc m + p ≤ suc m + q` simplifies to `suc (m + p) ≤ suc (m + q)`.
  The inductive hypothesis `+-monoʳ-≤ m p q p≤q` establishes that
  `m + p ≤ m + q`, and our goal follows by applying `s≤s`.

Second, we deal with the special case of showing addition is
monotonic on the left. This follows from the previous
result and the commutativity of addition.
\begin{code}
+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n
\end{code}
Rewriting by `+-comm m p` and `+-comm n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `+-monoʳ-≤ p m n m≤n`.

Third, we combine the two previous results.
\begin{code}
+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)
\end{code}
Invoking `+-monoˡ-≤ m n p m≤n` proves `m + p ≤ n + p` and invoking
`+-monoʳ-≤ n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.


## Strict inequality.

We can define strict inequality similarly to inequality.
\begin{code}
infix 4 _<_

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ} → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n
\end{code}
The key difference is that zero is less than the successor of an
arbitrary number, but is not less than zero.

Clearly, strict inequality is not reflexive. However it is
*irreflexive* in that `n < n` never holds for any value of `n`.
Like inequality, strict inequality is transitive.
Strict inequality is not total, but satisfies the closely related property of
*trichotomy*: for any `m` and `n`, exactly one of `m < n`, `m ≡ n`, or `m > n`
holds (where we define `m > n` to hold exactly where `n < m`).
It is also monotonic with regards to addition and multiplication.

Most of the above are considered in exercises below.  Irreflexivity
requires logical negation, as does the fact that the three cases in
trichotomy are mutually exclusive, so those points are deferred
until the negation is introduced in Chapter [Logic](Logic).

It is straightforward to show that `suc m ≤ n` implies `m < n`,
and conversely.  One can then give an alternative derivation of the
properties of strict inequality, such as transitivity, by directly
exploiting the corresponding properties of inequality.

### Exercise (`<-trans`)

Show that strict inequality is transitive.

### Exercise (`trichotomy`)

Show that strict inequality satisfies a weak version of trichotomy, in the sense
that for any `m` and `n` that one of `m < n`, `m ≡ n`, or `m > n`
holds. You will need to define a suitable data structure, similar
to the one used for totality.  (After negation is introduced in Chapter [Logic](Logic),
we will be in a position to show that the three cases are mutually exclusive.)

### Exercise (`+-mono-<`)

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

### Exercise (`≤-implies-<`, `<-implies-≤`)

Show that `suc m ≤ n` implies `m < n`, and conversely.

### Exercise (`<-trans′`)

Give an alternative proof that strict inequality is transitive,
using the relating between strict inequality and inequality and
the fact that inequality is transitive.


## Even and odd

As a further example, let's specify even and odd numbers.  
Inequality and strict inequality are *binary relations*,
while even and odd are *unary relations*, sometimes called *predicates*.
\begin{code}
data even : ℕ → Set
data odd  : ℕ → Set

data even where
  even-zero : even zero
  even-suc  : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  odd-suc   : ∀ {n : ℕ} → even n → odd (suc n)
\end{code}
A number is even if it is zero or the successor of an odd number,
and odd if it is the successor of an even number.

This is our first use of a mutually recursive datatype declaration.
Since each identifier must be defined before it is used, we first
declare the indexed types `even` and `odd` (omitting the `where`
keyword and the declarations of the constructors) and then
declare the constructors (omitting the signatures `ℕ → Set`
which were given earlier).

We show that the sum of two even numbers is even.
\begin{code}
e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)
o+e≡o : ∀ {m n : ℕ} → odd  m → even n → odd  (m + n)

e+e≡e even-zero     en  =  en
e+e≡e (even-suc om) en  =  even-suc (o+e≡o om en)

o+e≡o (odd-suc  em) en  =  odd-suc  (e+e≡e em en)
\end{code}
Corresponding to the mutually recursive types, we use two mutually recursive
functions, one to show that the sum of two even numbers is even, and the other
to show that the sum of an odd and an even number is odd.

To show that the sum of two even numbers is even, consider the evidence that the
first number is even. If it because it is zero, then the sum is even because the
second number is even.  If it is because it is the successor of an odd number,
then the result is even because it is the successor of the sum of an odd and an
even number, which is odd.

To show that the sum of an odd and even number is odd, consider the evidence
that the first number is odd. If it is because it is the successor of an even
number, then the result is odd because it is the successor of the sum of two
even numbers, which is even.

This is our first use of mutually recursive functions.  Since each identifier
must be defined before it is used, we first give the signatures for both
functions and then the equations that define them.

### Exercise (`o+o≡e`)

Show that the sum of two odd numbers is even.


## Formalising preorder

\begin{code}
record IsPreorder {A : Set} (_≤_ : A → A → Set) : Set where
  field
    reflexive : ∀ {x : A} → x ≤ x
    trans : ∀ {x y z : A} → x ≤ y → y ≤ z → x ≤ z

IsPreorder-≤ : IsPreorder _≤_
IsPreorder-≤ =
  record
    { reflexive = ≤-refl
    ; trans = ≤-trans
    }
\end{code}



## Standard prelude

Definitions similar to those in this chapter can be found in the standard library.
\begin{code}
import Data.Nat using (_≤_; z≤n; s≤s)
import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; ≤-total;
                                  +-monoʳ-≤; +-monoˡ-≤; +-mono-≤)
\end{code}
In the standard library, `≤-total` is formalised in terms of disjunction (which
we define in Chapter [Logic](Logic)), and `+-monoʳ-≤`, `+-monoˡ-≤`, `+-mono-≤`
make implicit arguments that here are explicit.

## Unicode

This chapter uses the following unicode.

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    ≥  U+2265  GREATER-THAN OR EQUAL TO (̄\>=, \ge)
    ˡ  U+02E1  MODIFIER LETTER SMALL L (\^l)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)

The commands `\^l` and `\^r` give access to a variety of superscript
leftward and rightward arrows, and also superscript letters `l` and `r`.

