---
title     : "Assignment1: TSPL Assignment 1"
permalink : /TSPL/2023/Assignment1/
---

```
module Assignment1 where
```

## YOUR NAME AND EMAIL GOES HERE


## Introduction

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises labelled "(practice)" are included for those who want extra practice.

Submit your homework using Gradescope. Go to the course page under Learn.
Select `Assessment`, then select `Assignment Submission`.
Please ensure your files execute correctly under Agda!


## Good Scholarly Practice.

Please remember the University requirement as
regards all assessed work. Details about this can be found at:

> [https://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct](https://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct)

Furthermore, you are required to take reasonable measures to protect
your assessed work from unauthorised access. For example, if you put
any such work on a public repository then you must set access
permissions appropriately (generally permitting access only to
yourself, or your group in the case of group practicals).


## Naturals

```
module Naturals where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
```

#### Exercise `seven` (practice) {#seven}

Write out `7` in longhand.

```agda
  -- Your code goes here
```

You will need to give both a type signature and definition for the
variable `seven`. Type `C-c C-l` in Emacs to instruct Agda to re-load.


#### Exercise `+-example` (practice) {#plus-example}

Compute `3 + 4`, writing out your reasoning as a chain of equations, using the equations for `+`.

```agda
  -- Your code goes here
```


#### Exercise `*-example` (practice) {#times-example}

Compute `3 * 4`, writing out your reasoning as a chain of equations, using the equations for `*`.
(You do not need to step through the evaluation of `+`.)

```agda
  -- Your code goes here
```


#### Exercise `_^_` (recommended) {#power}

Define exponentiation, which is given by the following equations:

    m ^ 0        =  1
    m ^ (1 + n)  =  m * (m ^ n)

Check that `3 ^ 4` is `81`.

```agda
  -- Your code goes here
```



#### Exercise `∸-example₁` and `∸-example₂` (recommended) {#monus-examples}

Compute `5 ∸ 3` and `3 ∸ 5`, writing out your reasoning as a chain of equations.

```agda
  -- Your code goes here
```


#### Exercise `Bin` (stretch) {#Bin}

A more efficient representation of natural numbers uses a binary
rather than a unary system.  We represent a number as a bitstring:
```agda
  data Bin : Set where
    ⟨⟩ : Bin
    _O : Bin → Bin
    _I : Bin → Bin
```
For instance, the bitstring

    1011

standing for the number eleven is encoded as

    ⟨⟩ I O I I

Representations are not unique due to leading zeros.
Hence, eleven is also represented by `001011`, encoded as:

    ⟨⟩ O O I O I I

Define a function

    inc : Bin → Bin

that converts a bitstring to the bitstring for the next higher
number.  For example, since `1100` encodes twelve, we should have:

    inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O

Confirm that this gives the correct answer for the bitstrings
encoding zero through four.

Using the above, define a pair of functions to convert
between the two representations.

    to   : ℕ → Bin
    from : Bin → ℕ

For the former, choose the bitstring to have no leading zeros if it
represents a positive natural, and represent zero by `⟨⟩ O`.
Confirm that these both give the correct answer for zero through four.

```agda
  -- Your code goes here
```



## Induction

```
module Induction where
```

## Imports

We require equality as in the previous chapter, plus the naturals
and some operations upon them.  We also require a couple of new operations,
`cong`, `sym`, and `_≡⟨_⟩_`, which are explained below:
```agda
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; sym)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
  open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)
```
(Importing `step-≡` defines `_≡⟨_⟩_`.)


```
  open import plfa.part1.Induction
    hiding ()
```

#### Exercise `operators` (practice) {#operators}

Give another example of a pair of operators that have an identity
and are associative, commutative, and distribute over one another.
(You do not have to prove these properties.)

Give an example of an operator that has an identity and is
associative but is not commutative.
(You do not have to prove these properties.)


#### Exercise `finite-+-assoc` (stretch) {#finite-plus-assoc}

Write out what is known about associativity of addition on each of the
first four days using a finite story of creation, as
[earlier](/Naturals/#finite-creation).

```agda
  -- Your code goes here
```

#### Exercise `+-swap` (recommended) {#plus-swap}

Show

    m + (n + p) ≡ n + (m + p)

for all naturals `m`, `n`, and `p`. No induction is needed,
just apply the previous results which show addition
is associative and commutative.

```agda
  -- Your code goes here
```


#### Exercise `*-distrib-+` (recommended) {#times-distrib-plus}

Show multiplication distributes over addition, that is,

    (m + n) * p ≡ m * p + n * p

for all naturals `m`, `n`, and `p`.

```agda
  -- Your code goes here
```


#### Exercise `*-assoc` (recommended) {#times-assoc}

Show multiplication is associative, that is,

    (m * n) * p ≡ m * (n * p)

for all naturals `m`, `n`, and `p`.

```agda
  -- Your code goes here
```


#### Exercise `*-comm` (practice) {#times-comm}

Show multiplication is commutative, that is,

    m * n ≡ n * m

for all naturals `m` and `n`.  As with commutativity of addition,
you will need to formulate and prove suitable lemmas.

```agda
  -- Your code goes here
```


#### Exercise `0∸n≡0` (practice) {#zero-monus}

Show

    zero ∸ n ≡ zero

for all naturals `n`. Did your proof require induction?

```agda
  -- Your code goes here
```


#### Exercise `∸-+-assoc` (practice) {#monus-plus-assoc}

Show that monus associates with addition, that is,

    m ∸ n ∸ p ≡ m ∸ (n + p)

for all naturals `m`, `n`, and `p`.

```agda
  -- Your code goes here
```


#### Exercise `+*^` (stretch)

Show the following three laws

     m ^ (n + p) ≡ (m ^ n) * (m ^ p)  (^-distribˡ-+-*)
     (m * n) ^ p ≡ (m ^ p) * (n ^ p)  (^-distribʳ-*)
     (m ^ n) ^ p ≡ m ^ (n * p)        (^-*-assoc)

for all `m`, `n`, and `p`.

```
  -- Your code goes here
```


#### Exercise `Bin-laws` (stretch) {#Bin-laws}

Recall that
Exercise [Bin](/Naturals/#Bin)
defines a datatype `Bin` of bitstrings representing natural numbers,
and asks you to define functions

    inc   : Bin → Bin
    to    : ℕ → Bin
    from  : Bin → ℕ

Consider the following laws, where `n` ranges over naturals and `b`
over bitstrings:

    from (inc b) ≡ suc (from b)
    to (from b) ≡ b
    from (to n) ≡ n

For each law: if it holds, prove; if not, give a counterexample.

```agda
  -- Your code goes here
```



## Relations

```
module Relations where
```

## Imports

```agda
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong)
  open import Data.Nat using (ℕ; zero; suc; _+_)
  open import Data.Nat.Properties using (+-comm; +-identityʳ)
  open import Data.Nat using (_≤_; z≤n; s≤s)
  open import Data.Nat.Properties
    using (≤-refl; ≤-trans; ≤-antisym; ≤-total;
           +-monoʳ-≤; +-monoˡ-≤; +-mono-≤)
```


#### Exercise `orderings` (practice) {#orderings}

Give an example of a preorder that is not a partial order.

```agda
  -- Your code goes here
```

Give an example of a partial order that is not a total order.

```agda
  -- Your code goes here
```

#### Exercise `≤-antisym-cases` (practice) {#leq-antisym-cases}

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?

```agda
  -- Your code goes here
```


#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.

```agda
  -- Your code goes here
```


#### Exercise `<-trans` (recommended) {#less-trans}

Show that strict inequality is transitive. Use a direct proof. (A later
exercise exploits the relation between < and ≤.)

```agda
  -- Your code goes here
```

#### Exercise `trichotomy` (practice) {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
* `m < n`,
* `m ≡ n`, or
* `m > n`.

Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation](/Negation/).)

```agda
  -- Your code goes here
```

#### Exercise `+-mono-<` (practice) {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

```agda
  -- Your code goes here
```

#### Exercise `≤→<, <→≤` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

```agda
  -- Your code goes here
```

#### Exercise `<-trans-revisited` (practice) {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relation between strict inequality and inequality and
the fact that inequality is transitive.

```agda
  -- Your code goes here
```


#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}

Show that the sum of two odd numbers is even.

```agda
  -- Your code goes here
```

#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that
Exercise [Bin](/Naturals/#Bin)
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following:

    ⟨⟩ I O I I
    ⟨⟩ O O I O I I

Define a predicate

    Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate

    One : Bin → Set

that holds only if the bitstring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).

Show that increment preserves canonical bitstrings:

    Can b
    ------------
    Can (inc b)

Show that converting a natural to a bitstring always yields a
canonical bitstring:

    ----------
    Can (to n)

Show that converting a canonical bitstring to a natural
and back is the identity:

    Can b
    ---------------
    to (from b) ≡ b

Hint: For each of these, you may first need to prove related
properties of `One`. It may also help to prove the following:

    One b
    ----------
    1 ≤ from b

    1 ≤ n
    ---------------------
    to (2 * n) ≡ (to n) O

The hypothesis `1 ≤ n` is required for the latter, because
`to (2 * 0) ≡ ⟨⟩ O` but `(to 0) O ≡ ⟨⟩ O O`.

```agda
  -- Your code goes here
```
