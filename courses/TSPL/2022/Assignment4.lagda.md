---
title     : "Assignment4: TSPL Assignment 4"
permalink : /TSPL/2022/Assignment4/
---

```
module Assignment4 where
```

## YOUR NAME AND EMAIL GOES HERE

## Introduction

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises labelled "(practice)" are included for those who want extra practice.

Submit your homework using the "submit" command.
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


## DeBruijn

```
module DeBruijn where
```

## Imports

```agda
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
  open import Relation.Nullary using (¬_)
  open import Relation.Nullary.Decidable using (True; toWitness)
```

```
  open import plfa.part2.DeBruijn
    hiding ()
```

#### Exercise `mul` (recommended)

Write out the definition of a lambda term that multiplies
two natural numbers, now adapted to the intrinsically-typed
de Bruijn representation.

```agda
  -- Your code goes here
```


#### Exercise `V¬—→` (practice)

Following the previous development, show values do
not reduce, and its corollary, terms that reduce are not
values.

```agda
  -- Your code goes here
```

#### Exercise `mul-example` (recommended)

Using the evaluator, confirm that two times two is four.

```agda
  -- Your code goes here
```



## More

```
module More where
```

```agda
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Nat using (ℕ; zero; suc; _*_; _<_; _≤?_; z≤n; s≤s)
  open import Relation.Nullary using (¬_)
  open import Relation.Nullary.Decidable using (True; toWitness)
```

```
  open import plfa.part2.More
    hiding (double-subst)
```

#### Exercise `More` (recommended and practice)

Formalise the remaining constructs defined in this chapter.
Make your changes in this file.
Evaluate each example, applied to data as needed,
to confirm it returns the expected answer:

  * sums (recommended)
  * unit type (practice)
  * an alternative formulation of unit type (practice)
  * empty type (recommended)
  * lists (practice)

Please delimit any code you add as follows:

    -- begin
    -- end


#### Exercise `double-subst` (stretch)

Show that a double substitution is equivalent to two single
substitutions.
```agda
  postulate
    double-subst :
      ∀ {Γ A B C} {V : Γ ⊢ A} {W : Γ ⊢ B} {N : Γ , A , B ⊢ C} →
        N [ V ][ W ] ≡ (N [ rename S_ W ]) [ V ]
```
Note the arguments need to be swapped and `W` needs to have
its context adjusted via renaming in order for the right-hand
side to be well typed.


## Inference

```
module Inference where
```

## Imports

```agda
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
  open import Data.String using (String; _≟_)
  open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Decidable using (False; toWitnessFalse)
```

Once we have a type derivation, it will be easy to construct
from it the intrinsically-typed representation.  In order that we
can compare with our previous development, we import
module `plfa.part2.More`:

```agda
  import plfa.part2.More as DB
```

The phrase `as DB` allows us to refer to definitions
from that module as, for instance, `DB._⊢_`, which is
invoked as `Γ DB.⊢ A`, where `Γ` has type
`DB.Context` and `A` has type `DB.Type`.


```
  open import plfa.part2.Inference
    hiding ()
```

#### Exercise `bidirectional-mul` (recommended) {#bidirectional-mul}

Rewrite your definition of multiplication from
Chapter [Lambda](/Lambda/), decorated to support inference.

```agda
  -- Your code goes here
```


#### Exercise `bidirectional-products` (recommended) {#bidirectional-products}

Extend the bidirectional type rules to include products from
Chapter [More](/More/).

```agda
  -- Your code goes here
```


#### Exercise `bidirectional-rest` (stretch)

Extend the bidirectional type rules to include the rest of the constructs from
Chapter [More](/More/).

```agda
  -- Your code goes here
```


#### Exercise `inference-multiplication` (recommended)

Apply inference to your decorated definition of multiplication from
exercise [`bidirectional-mul`](/Inference/#bidirectional-mul), and show that
erasure of the inferred typing yields your definition of
multiplication from Chapter [DeBruijn](/DeBruijn/).

```agda
  -- Your code goes here
```

#### Exercise `inference-products` (recommended)

Using your rules from exercise
[`bidirectional-products`](/Inference/#bidirectional-products), extend
bidirectional inference to include products.

```agda
  -- Your code goes here
```

#### Exercise `inference-rest` (stretch)

Extend the bidirectional type rules to include the rest of the constructs from
Chapter [More](/More/).

```agda
  -- Your code goes here
```



## Untyped

```
module Untyped where
```

## Imports

```agda
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; sym; trans; cong)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
  open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
  open import Data.Unit using (⊤; tt)
  open import Function using (_∘_)
  open import Function.Equivalence using (_⇔_; equivalence)
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Decidable using (map)
  open import Relation.Nullary.Negation using (contraposition)
  open import Relation.Nullary.Product using (_×-dec_)
```


```
  open import plfa.part2.Untyped
    hiding ()
```

#### Exercise (`Type≃⊤`) (practice)

Show that `Type` is isomorphic to `⊤`, the unit type.

```agda
  -- Your code goes here
```

#### Exercise (`Context≃ℕ`) (practice)

Show that `Context` is isomorphic to `ℕ`.

```agda
  -- Your code goes here
```

#### Exercise (`variant-1`) (practice)

How would the rules change if we want call-by-value where terms
normalise completely?  Assume that `β` should not permit reduction
unless both terms are in normal form.

```agda
  -- Your code goes here
```

#### Exercise (`variant-2`) (practice)

How would the rules change if we want call-by-value where terms
do not reduce underneath lambda?  Assume that `β`
permits reduction when both terms are values (that is, lambda
abstractions).  What would `2+2ᶜ` reduce to in this case?

```agda
  -- Your code goes here
```


#### Exercise `plus-eval` (practice)

Use the evaluator to confirm that `plus · two · two` and `four`
normalise to the same term.

```agda
  -- Your code goes here
```

#### Exercise `multiplication-untyped` (recommended)

Use the encodings above to translate your definition of
multiplication from previous chapters with the Scott
representation and the encoding of the fixpoint operator.
Confirm that two times two is four.

```agda
  -- Your code goes here
```

#### Exercise `encode-more` (stretch)

Along the lines above, encode all of the constructs of
Chapter [More](/More/),
save for primitive numbers, in the untyped lambda calculus.

```agda
  -- Your code goes here
```
