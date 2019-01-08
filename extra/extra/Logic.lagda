---
title     : "Logic: Propositions as Types"
layout    : page
permalink : /Logic
---

This chapter introduces the basic concepts of logic, by observing
that each concept of logic is represented by a corresponding
data type.

+ *conjunction* is *product*
+ *disjunction* is *sum*
+ *true* is *unit type*
+ *false* is *empty type*
+ *implication* is *function space*
+ *negation* is *function to empty type*
+ *universal quantification* is *dependent function*
+ *existential quantification* is *dependent product*

We also discuss the relation between *intuitionistic* and *classical*
logic.

## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Isomorphism using (_≃_; ≃-sym; ≃-trans; _≲_)
open Isomorphism.≃-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties.Simple using (+-suc)
open import Agda.Primitive using (Level; lzero; lsuc)
\end{code}


## Conjunction is product

Given two propositions `A` and `B`, the conjunction `A × B` holds
if both `A` holds and `B` holds.  We formalise this idea by
declaring a suitable inductive type.
\begin{code}
data _×_ : Set → Set → Set where
  _,_ : ∀ {A B : Set} → A → B → A × B
\end{code}
Evidence that `A × B` holds is of the form
`(M , N)`, where `M` is evidence that `A` holds and
`N` is evidence that `B` holds.

Given evidence that `A × B` holds, we can conclude that either
`A` holds or `B` holds.
\begin{code}
fst : ∀ {A B : Set} → A × B → A
fst (x , y) = x

snd : ∀ {A B : Set} → A × B → B
snd (x , y) = y
\end{code}
If `L` is evidence that `A × B` holds, then `fst L` is evidence
that `A` holds, and `snd L` is evidence that `B` holds.

Equivalently, we could also declare product as a record type.
\begin{code}
record _×′_ (A B : Set) : Set where
  field
    fst′ : A
    snd′ : B
open _×′_
\end{code}
We construct values of the record type with the syntax:

    record
      { fst′ = M
      ; snd′ = N
      }

which corresponds to using the constructor of the corresponding
inductive type:

    ( M , N )

where `M` is a term of type `A` and `N` is a term of type `B`.

We set the precedence of conjunction so that it binds less
tightly than anything save disjunction, and of the pairing
operator so that it binds less tightly than any arithmetic
operator.
\begin{code}
infixr 2 _×_
infixr 4 _,_
\end{code}
Thus, `m ≤ n × n ≤ p` parses as `(m ≤ n) × (n ≤ p)` and
`(m * n , p)` parses as `((m * n) , p)`.

Given two types `A` and `B`, we refer to `A x B` as the
*product* of `A` and `B`.  In set theory, it is also sometimes
called the *cartesian product*, and in computing it corresponds
to a *record* type. Among other reasons for
calling it the product, note that if type `A` has `m`
distinct members, and type `B` has `n` distinct members,
then the type `A × B` has `m * n` distinct members.
For instance, consider a type `Bool` with two members, and
a type `Tri` with three members.
\begin{code}
data Bool : Set where
  true : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri
\end{code}
Then the type `Bool × Tri` has six members:

    (true  , aa)    (true  , bb)    (true ,  cc)
    (false , aa)    (false , bb)    (false , cc)

For example, the following function enumerates all
possible arguments of type `Bool × Tri`:
\begin{code}
×-count : Bool × Tri → ℕ
×-count (true , aa) = 1
×-count (true , bb) = 2
×-count (true , cc) = 3
×-count (false , aa) = 4
×-count (false , bb) = 5
×-count (false , cc) = 6
\end{code}

Product on types also shares a property with product on numbers in
that there is a sense in which it is commutative and associative.  In
particular, product is commutative and associative *up to
isomorphism*.

For commutativity, the `to` function swaps a pair, taking `(x , y)` to
`(y , x)`, and the `fro` function does the same (up to renaming).
Instantiating the patterns correctly in `invˡ` and `invʳ` is essential.
Replacing the definition of `invˡ` by `λ w → refl` will not work;
and similarly for `invʳ`, which does the same (up to renaming).
\begin{code}
×-comm : ∀ {A B : Set} → (A × B) ≃ (B × A)
×-comm =
  record
    { to      = λ { (x , y) → (y , x)}
    ; from    = λ { (y , x) → (x , y)}
    ; from∘to = λ { (x , y) → refl }
    ; to∘from = λ { (y , x) → refl }
    } 
\end{code}

Being *commutative* is different from being *commutative up to
isomorphism*.  Compare the two statements:

    m * n ≡ n * m
    A × B ≃ B × A

In the first case, we might have that `m` is `2` and `n` is `3`, and
both `m * n` and `n * m` are equal to `6`.  In the second case, we
might have that `A` is `Bool` and `B` is `Tri`, and `Bool × Tri` is
*not* the same as `Tri × Bool`.  But there is an isomorphism
between the two types.  For
instance, `(true , aa)`, which is a member of the former, corresponds
to `(aa , true)`, which is a member of the latter.

For associativity, the `to` function reassociates two uses of pairing,
taking `((x , y) , z)` to `(x , (y , z))`, and the `fro` function does
the inverse.  Again, the evidence of left and right inverse requires
matching against a suitable pattern to enable simplificition.
\begin{code}
×-assoc : ∀ {A B C : Set} → ((A × B) × C) ≃ (A × (B × C))
×-assoc =
  record
    { to      = λ { ((x , y) , z) → (x , (y , z)) }
    ; from    = λ { (x , (y , z)) → ((x , y) , z) }
    ; from∘to = λ { ((x , y) , z) → refl }
    ; to∘from = λ { (x , (y , z)) → refl }
    } 
\end{code}

Being *associative* is not the same as being *associative
up to isomorphism*.  Compare the two statements:

  (m * n) * p ≡ m * (n * p)
  (A × B) × C ≃ A × (B × C)

For example, the type `(ℕ × Bool) × Tri` is *not* the same as `ℕ ×
(Bool × Tri)`. But there is an isomorphism between the two types. For
instance `((1 , true) , aa)`, which is a member of the former,
corresponds to `(1 , (true , aa))`, which is a member of the latter.

Here we have used lambda-expressions with pattern matching.
For instance, the term

    λ { (x , y) → (y , x) }

corresponds to the function `h`, where `h` is defined by
\begin{code}
h : ∀ {A B : Set} → A × B → B × A
h (x , y) = (y , x)
\end{code}
Often using an anonymous lambda expression is more convenient than
using a named function: it avoids a lengthy type declaration; and the
definition appears exactly where the function is used, so there is no
need for the writer to remember to declare it in advance, or for the
reader to search for the definition elsewhere in the code.

## Truth is unit

Truth `⊤` always holds. We formalise this idea by
declaring a suitable inductive type.
\begin{code}
data ⊤ : Set where
  tt : ⊤
\end{code}
Evidence that `⊤` holds is of the form `tt`.

Given evidence that `⊤` holds, there is nothing more of interest we
can conclude.  Since truth always holds, knowing that it holds tells
us nothing new.

We refer to `⊤` as *the unit type* or just *unit*. And, indeed,
type `⊤` has exactly once member, `tt`.  For example, the following
function enumerates all possible arguments of type `⊤`:
\begin{code}
⊤-count : ⊤ → ℕ
⊤-count tt = 1
\end{code}

For numbers, one is the identity of multiplication. Correspondingly,
unit is the identity of product *up to isomorphism*.

For left identity, the `to` function takes `(tt , x)` to `x`, and the `fro` function
does the inverse.  The evidence of left inverse requires matching against
a suitable pattern to enable simplification.
\begin{code}
⊤-identityˡ : ∀ {A : Set} → (⊤ × A) ≃ A
⊤-identityˡ =
  record
    { to      = λ { (tt , x) → x }
    ; from    = λ { x → (tt , x) }
    ; from∘to = λ { (tt , x) → refl }
    ; to∘from = λ { x → refl}
    }
\end{code}

Having an *identity* is different from having an identity
*up to isomorphism*.  Compare the two statements:

    1 * m ≡ m
    ⊤ × A ≃ A

In the first case, we might have that `m` is `2`, and both
`1 * m` and `m` are equal to `2`.  In the second
case, we might have that `A` is `Bool`, and `⊤ × Bool` is *not* the
same as `Bool`.  But there is an isomorphism betwee the two types.
For instance, `(tt, true)`, which is a member of the former,
corresponds to `true`, which is a member of the latter.

That unit is also a right identity follows immediately from
commutativity of product and left identity.
\begin{code}
⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎
\end{code}
Here we have used tabular reasoning for isomorphism,
analogous to than used for equivalence.


## Disjunction is sum

Given two propositions `A` and `B`, the disjunction `A ⊎ B` holds
if either `A` holds or `B` holds.  We formalise this idea by
declaring a suitable inductive type.
\begin{code}
data _⊎_ : Set → Set → Set where
  inj₁  : ∀ {A B : Set} → A → A ⊎ B
  inj₂ : ∀ {A B : Set} → B → A ⊎ B
\end{code}
Evidence that `A ⊎ B` holds is either of the form
`inj₁ M`, where `M` is evidence that `A` holds, or `inj₂ N`, where
`N` is evidence that `B` holds.

Given evidence that `A → C` and `B → C` both hold, then given
evidence that `A ⊎ B` holds we can conlude that `C` holds.
\begin{code}
⊎-elim : ∀ {A B C : Set} → (A → C) → (B → C) → (A ⊎ B → C)
⊎-elim f g (inj₁ x) = f x
⊎-elim f g (inj₂ y) = g y
\end{code}
Pattern matching against `inj₁` and `inj₂` is typical of how we exploit
evidence that a disjunction holds.

We set the precedence of disjunction so that it binds less tightly
than any other declared operator.
\begin{code}
infix 1 _⊎_
\end{code}
Thus, `A × C ⊎ B × C` parses as `(A × C) ⊎ (B × C)`.

Given two types `A` and `B`, we refer to `A ⊎ B` as the
*sum* of `A` and `B`.  In set theory, it is also sometimes
called the *disjoint union*, and in computing it corresponds
to a *variant record* type. Among other reasons for
calling it the sum, note that if type `A` has `m`
distinct members, and type `B` has `n` distinct members,
then the type `A ⊎ B` has `m + n` distinct members.
For instance, consider a type `Bool` with two members, and
a type `Tri` with three members, as defined earlier.
Then the type `Bool ⊎ Tri` has five
members:

    (inj₁ true)     (inj₂ aa)
    (inj₁ false)    (inj₂ bb)
                    (inj₂ cc)

For example, the following function enumerates all
possible arguments of type `Bool ⊎ Tri`:
\begin{code}
⊎-count : Bool ⊎ Tri → ℕ
⊎-count (inj₁ true)  = 1
⊎-count (inj₁ false) = 2
⊎-count (inj₂ aa)    = 3
⊎-count (inj₂ bb)    = 4
⊎-count (inj₂ cc)    = 5
\end{code}

Sum on types also shares a property with sum on numbers in that it is
commutative and associative *up to isomorphism*.

For commutativity, the `to` function swaps the two constructors,
taking `inj₁ x` to `inj₂ x`, and `inj₂ y` to `inj₁ y`; and the `fro`
function does the same (up to renaming). Replacing the definition of
`invˡ` by `λ w → refl` will not work; and similarly for `invʳ`, which
does the same (up to renaming).
\begin{code}
⊎-comm : ∀ {A B : Set} → (A ⊎ B) ≃ (B ⊎ A)
⊎-comm = record
  { to      = λ { (inj₁ x) → (inj₂ x)
              ; (inj₂ y) → (inj₁ y)
              }
  ; from    = λ { (inj₁ y) → (inj₂ y)
              ; (inj₂ x) → (inj₁ x)
              }
  ; from∘to = λ { (inj₁ x) → refl
                ; (inj₂ y) → refl
                } 
  ; to∘from = λ { (inj₁ y) → refl
                ; (inj₂ x) → refl
                }  
  }
\end{code}
Being *commutative* is different from being *commutative up to
isomorphism*.  Compare the two statements:

    m + n ≡ n + m
    A ⊎ B ≃ B ⊎ A

In the first case, we might have that `m` is `2` and `n` is `3`, and
both `m + n` and `n + m` are equal to `5`.  In the second case, we
might have that `A` is `Bool` and `B` is `Tri`, and `Bool ⊎ Tri` is
*not* the same as `Tri ⊎ Bool`.  But there is an isomorphism between
the two types.  For instance, `inj₁ true`, which is a member of the
former, corresponds to `inj₂ true`, which is a member of the latter.

For associativity, the `to` function reassociates, and the `fro` function does
the inverse.  Again, the evidence of left and right inverse requires
matching against a suitable pattern to enable simplificition.
\begin{code}
⊎-assoc : ∀ {A B C : Set} → ((A ⊎ B) ⊎ C) ≃ (A ⊎ (B ⊎ C))
⊎-assoc = record
  { to   = λ { (inj₁ (inj₁ x)) → (inj₁ x)
             ; (inj₁ (inj₂ y)) → (inj₂ (inj₁ y))
             ; (inj₂ z)        → (inj₂ (inj₂ z))
             }
  ; fro  = λ { (inj₁ x)        → (inj₁ (inj₁ x))
             ; (inj₂ (inj₁ y)) → (inj₁ (inj₂ y))
             ; (inj₂ (inj₂ z)) → (inj₂ z)
             }
  ; invˡ = λ { (inj₁ (inj₁ x)) → refl
             ; (inj₁ (inj₂ y)) → refl
             ; (inj₂ z)        → refl
             }
  ; invʳ = λ { (inj₁ x)        → refl
             ; (inj₂ (inj₁ y)) → refl
             ; (inj₂ (inj₂ z)) → refl
             }
  }
\end{code}

Again, being *associative* is not the same as being *associative
up to isomorphism*.  For example, the type `(ℕ + Bool) + Tri`
is *not* the same as `ℕ + (Bool + Tri)`. But there is an
isomorphism between the two types. For instance `inj₂ (inj₁ true)`,
which is a member of the former, corresponds to `inj₁ (inj₂ true)`,
which is a member of the latter.

Here we have used lambda-expressions with pattern matching
and multiple cases. For instance, the term

    λ { (inj₁ x) → (inj₂ x)
      ; (inj₂ y) → (inj₁ y)
      }

corresponds to the function `k`, where `k` is defined by
\begin{code}
k : ∀ {A B : Set} → A ⊎ B → B ⊎ A
k (inj₁ x) = inj₂ x
k (inj₂ y) = inj₁ y
\end{code}


## False is empty

False `⊥` never holds.  We formalise this idea by declaring
a suitable inductive type.
\begin{code}
data ⊥ : Set where
  -- no clauses!
\end{code}
There is no possible evidence that `⊥` holds.

Given evidence that `⊥` holds, we might conclude anything!  Since
false never holds, knowing that it holds tells us we are in a
paradoxical situation.

is a basic principle of logic, known in medieval times by the
latin phrase *ex falso*, and known to children through phrases
such as "if pigs had wings, then I'd be the Queen of Sheba".
\begin{code}
⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()
\end{code}
Here since `⊥` is a type with no members, we indicate that it is
*never* possible to match against a value of this type by using
the pattern `()`.  In medieval times, this rule was know by the
latin name *ex falso*.  It is also known to children by phrases
such as "If pigs had wings then I'd be the Queen of Sheba".

We refer to `⊥` as *the empty type* or just *empty*. And, indeed,
type `⊥` has no members. For example, the following function
enumerates all possible arguments of type `⊥`:
\begin{code}
⊥-count : ⊥ → ℕ
⊥-count ()
\end{code}
Here, again, pattern `()` indicates that no value can match
type `⊥`.

For numbers, zero is the identity of additition. Correspondingly,
empty is the identity of sums *up to isomorphism*.

For left identity, the `to` function observes that `inj₁ ()` can never arise,
and takes `inj₂ x` to `x`, and the `fro` function
does the inverse.  The evidence of left inverse requires matching against
a suitable pattern to enable simplification.
\begin{code}
⊥-identityˡ : ∀ {A : Set} → (⊥ ⊎ A) ≃ A
⊥-identityˡ =
  record
    { to   = λ { (inj₁ ())
               ; (inj₂ x) → x
               }
    ; fro  = λ { x → inj₂ x }
    ; invˡ = λ { (inj₁ ())
               ; (inj₂ x) → refl
               }
    ; invʳ = λ { x → refl }
    }
\end{code}

Having an *identity* is different from having an identity
*up to isomorphism*.  Compare the two statements:

    0 + m ≡ m
    ⊥ ⊎ A ≃ A

In the first case, we might have that `m` is `2`, and both `0 + m` and
`m` are equal to `2`.  In the second case, we might have that `A` is
`Bool`, and `⊥ ⊎ Bool` is *not* the same as `Bool`.  But there is an
isomorphism betwee the two types.  For instance, `inj₂ true`, which is
a member of the former, corresponds to `true`, which is a member of
the latter.

That empty is also a right identity follows immediately from
commutativity of sum and left identity.  
\begin{code}
⊥-identityʳ : ∀ {A : Set} → (A ⊎ ⊥) ≃ A
⊥-identityʳ {A} =
  ≃-begin
    (A ⊎ ⊥)
  ≃⟨ ⊎-comm ⟩
    (⊥ ⊎ A)
  ≃⟨ ⊥-identityˡ ⟩
    A
  ≃-∎
\end{code}
Here we have used tabular reasoning for isomorphism,
analogous to that used for equivalence.


## Implication is function

Given two propositions `A` and `B`, the implication `A → B` holds if
whenever `A` holds then `B` must also hold.  We formalise implication using
the function type, which has appeared throughout this book.

Evidence that `A → B` holds is of the form

    λ (x : A) → N[x]

where `N[x]` is a term of type `B` containing as a free variable `x` of type `A`.
Given a term `L` providing evidence that `A → B` holds, and a term `M`
providing evidence that `A` holds, the term `L M` provides evidence that
`B` holds.  In other words, evidence that `A → B` holds is a function that
converts evidence that `A` holds into evidence that `B` holds.

Put another way, if we know that `A → B` and `A` both hold,
then we may conclude that `B` holds. In medieval times, this rule was
known by the name *modus ponens*.

If we introduce an implication and then immediately eliminate it, we can
always simplify the resulting term.  Thus

    (λ (x : A) → N[x]) M

simplifies to `N[M]` of type `B`, where `N[M]` stands for the term `N[x]` with each
free occurrence of `x` replaced by `M` of type `A`.

<!--
Given evidence that `A → B` holds and that `A` holds, we can conclude that
`B` holds.
\begin{code}
→-elim : ∀ {A B : Set} → (A → B) → A → B
→-elim f x = f x
\end{code}
In medieval times, this rule was known by the latin name *modus ponens*.
-->

Implication binds less tightly than any other operator. Thus, `A ⊎ B →
B ⊎ A` parses as `(A ⊎ B) → (B ⊎ A)`.

Given two types `A` and `B`, we refer to `A → B` as the *function*
from `A` to `B`.  It is also sometimes called the *exponential*,
with `B` raised to the `A` power.  Among other reasons for calling
it the exponential, note that if type `A` has `m` distinct
memebers, and type `B` has `n` distinct members, then the type
`A → B` has `n ^ m` distinct members.  For instance, consider a
type `Bool` with two members and a type `Tri` with three members,
as defined earlier. The the type `Bool → Tri` has nine (that is,
three squared) members:

    {true → aa; false → aa}  {true → aa; false → bb}  {true → aa; false → cc}
    {true → bb; false → aa}  {true → bb; false → bb}  {true → bb; false → cc}
    {true → cc; false → aa}  {true → cc; false → bb}  {true → cc; false → cc}

For example, the following function enumerates all possible
arguments of the type `Bool → Tri`:
\begin{code}
→-count : (Bool → Tri) → ℕ
→-count f with f true | f false
...           | aa    | aa      = 1
...           | aa    | bb      = 2  
...           | aa    | cc      = 3
...           | bb    | aa      = 4
...           | bb    | bb      = 5
...           | bb    | cc      = 6
...           | cc    | aa      = 7
...           | cc    | bb      = 8
...           | cc    | cc      = 9  
\end{code}

Exponential on types also share a property with exponential on
numbers in that many of the standard identities for numbers carry
over to the types.

Corresponding to the law

    (p ^ n) ^ m  =  p ^ (n * m)

we have that the types `A → B → C` and `A × B → C` are isomorphic.
Both types can be viewed as functions that given evidence that `A` holds
and evidence that `B` holds can return evidence that `C` holds.
This isomorphism sometimes goes by the name *currying*.
The proof of the right inverse requires extensionality.
\begin{code}
postulate
  extensionality : ∀ {A B : Set} → {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g
  
currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to   =  λ f → λ { (x , y) → f x y }
    ; fro  =  λ g → λ x → λ y → g (x , y)
    ; invˡ =  λ f → refl
    ; invʳ =  λ g → extensionality (λ { (x , y) → refl })
    }
\end{code}

Currying tells us that instead of a function that takes a pair of arguments,
we can have a function that takes the first argument and returns a function that
expects the second argument.  Thus, for instance, instead of

    _+′_ : (ℕ × ℕ) → ℕ

we have

    _+_ : ℕ → ℕ → ℕ

The syntax of Agda, like that of other functional languages such as ML and
Haskell, is designed to make currying easy to use.  Function arrows associate
to the left and application associates to the right.  Thus

    A → B → C    *stands for*    A → (B → C)

and

    f x y    *stands for*   (f x) y

Currying is named for Haskell Curry, after whom the programming language Haskell
is also named.  However, Currying was introduced earlier by both Gotlob Frege
and Moses Schönfinkel.  When I first learned about currying, I was told a joke:
"It should be called schönfinkeling, but currying is tastier". Only later did I
learn that the idea actually goes all the way back to Frege!

Corresponding to the law

    p ^ (n + m) = (p ^ n) * (p ^ m)

we have that the types `A ⊎ B → C` and `(A → C) × (B → C)` are isomorphic.
That is, the assertion that if either `A` holds or `B` holds then `C` holds
is the same as the assertion that if `A` holds then `C` holds and if
`B` holds then `C` holds.
\begin{code}
→-distributes-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distributes-⊎ =
  record
    { to   = λ f → ( (λ x → f (inj₁ x)) , (λ y → f (inj₂ y)) ) 
    ; fro  = λ {(g , h) → λ { (inj₁ x) → g x ; (inj₂ y) → h y } }
    ; invˡ = λ f → extensionality (λ { (inj₁ x) → refl ; (inj₂ y) → refl })
    ; invʳ = λ {(g , h) → refl}
    }
\end{code}

Corresponding to the law

    (p * n) ^ m = (p ^ m) * (n ^ m)

we have that the types `A → B × C` and `(A → B) × (A → C)` are isomorphic.
That is, the assertion that if either `A` holds then `B` holds and `C` holds
is the same as the assertion that if `A` holds then `B` holds and if
`A` holds then `C` holds.  The proof requires that we recognise the eta
rule for products, which states that `(fst w , snd w) ≡ w` for any product `w`.
\begin{code}
postulate
  η-× : ∀ {A B : Set} → ∀ (w : A × B) → (fst w , snd w) ≡ w

→-distributes-× : ∀ {A B C : Set} → (A → B × C) ≃ ((A → B) × (A → C))
→-distributes-× =
  record
    { to   = λ f → ( (λ x → fst (f x)) , (λ y → snd (f y)) ) 
    ; fro  = λ {(g , h) → (λ x → (g x , h x))}
    ; invˡ = λ f → extensionality (λ x → η-× (f x))
    ; invʳ = λ {(g , h) → refl}
    }
\end{code}


## Distribution

Products distributes over sum, up to isomorphism.  The code to validate
this fact is similar in structure to our previous results.
\begin{code}
×-distributes-⊎ : ∀ {A B C : Set} → ((A ⊎ B) × C) ≃ ((A × C) ⊎ (B × C))
×-distributes-⊎ =
  record
    { to   = λ { ((inj₁ x) , z) → (inj₁ (x , z)) 
               ; ((inj₂ y) , z) → (inj₂ (y , z))
               }
    ; fro  = λ { (inj₁ (x , z)) → ((inj₁ x) , z)
               ; (inj₂ (y , z)) → ((inj₂ y) , z)
               }
    ; invˡ = λ { ((inj₁ x) , z) → refl
               ; ((inj₂ y) , z) → refl
               }
    ; invʳ = λ { (inj₁ (x , z)) → refl
               ; (inj₂ (y , z)) → refl
               }               
    }
\end{code}

Sums do not distribute over products up to isomorphism, but it is an embedding.
\begin{code}
⊎-distributes-× : ∀ {A B C : Set} → ((A × B) ⊎ C) ≲ ((A ⊎ C) × (B ⊎ C))
⊎-distributes-× =
  record
    { to   = λ { (inj₁ (x , y)) → (inj₁ x , inj₁ y)
               ; (inj₂ z)       → (inj₂ z , inj₂ z)
               }
    ; fro  = λ { (inj₁ x , inj₁ y) → (inj₁ (x , y))
               ; (inj₁ x , inj₂ z) → (inj₂ z)
               ; (inj₂ z , _ )     → (inj₂ z)
               }
    ; invˡ = λ { (inj₁ (x , y)) → refl
               ; (inj₂ z)       → refl
               }
    }
\end{code}
Note that there is a choice in how we write the `fro` function.
As given, it takes `(inj₂ z , inj₂ z′)` to `(inj₂ z)`, but it is
easy to write a variant that instead returns `(inj₂ z′)`.  We have
an embedding rather than an isomorphism because the
`fro` function must discard either `z` or `z′` in this case.

In the usual approach to logic, both of the distribution laws
are given as equivalences, where each side implies the other:

    A & (B ∨ C) ⇔ (A & B) ∨ (A & C)
    A ∨ (B & C) ⇔ (A ∨ B) & (A ∨ C)

But when we consider the two laws in terms of evidence, where `_&_`
corresponds to `_×_` and `_∨_` corresponds to `_⊎_`, then the first
gives rise to an isomorphism, while the second only gives rise to an
embedding, revealing a sense in which one of these laws is "more
true" than the other.


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
lone ltwo : Level
lone = lsuc lzero
ltwo = lsuc lone

¬¬-elim excluded-middle peirce implication de-morgan : Set lone
¬¬-elim = ∀ {A : Set} → ¬ ¬ A → A
excluded-middle = ∀ {A : Set} → A ⊎ ¬ A
peirce = ∀ {A B : Set} → (((A → B) → A) → A)
implication = ∀ {A B : Set} → (A → B) → ¬ A ⊎ B
de-morgan = ∀ {A B : Set} → ¬ (A × B) → ¬ A ⊎ ¬ B
\end{code}

It turns out that an assertion such as `Set : Set` is paradoxical.
Therefore, there are an infinite number of different levels of sets,
where `Set lzero : Set lone` and `Set lone : Set ltwo`, and so on,
where `lone` is `lsuc lzero`, and `ltwo` is `lsuc lone`, analogous to
the way we represent the natural nuambers. So far, we have only used
the type `Set`, Here is the demonstration that the reverse direction of one of the five
formulas equivalent to which is equivalent to `Set lzero`.  Here, since each
of `double-negation` and the others defines a type, we need to use
`Set lone` as the "type of types".


## Universals

Given a variable `x` of type `A` and a proposition `B[x]` which
contains `x` as a free variable, the universally quantified
proposition `∀ (x : A) → B[x]` holds if for every term `M` of type
`A` the proposition `B[M]` holds.  Here `B[M]` stands for
the proposition `B[x]` with each free occurrence of `x` replaced by
`M`.  The variable `x` appears free in `B[x]` but bound in
`∀ (x : A) → B[x]`.  We formalise universal quantification using the
dependent function type, which has appeared throughout this book.

Evidence that `∀ (x : A) → B[x]` holds is of the form

    λ (x : A) → N[x]

where `N[x]` is a term of type `B[x]`; here `N[x]` is a term and `B[x]`
is a proposition (or type) both containing as a free variable `x` of
type `A`.  Given a term `L` providing evidence that `∀ (x : A) → B[x]`
holds and a term `M` of type `A`, the term `L M` provides evidence
that `B[M]` holds.  In other words, evidence that `∀ (x : A) → B[x]`
holds is a function that converts a term `M` of type `A` into evidence
that `B[M]` holds.

Put another way, if we know that `∀ (x : A) → B[x]` holds and that `M`
is a term of type `A` then we may conclude that `B[M]` holds. In
medieval times, this rule was known by the name *dictum de omni*.

If we introduce a universal and the immediately eliminate it, we can
always simplify the resulting term. Thus

    (λ (x : A) → N[x]) M

simplifies to `N[M]` of type `B[M]`, where `N[M]` stands for the term
`N[x]` with each free occurrence of `x` replaced by `M` of type `A`.

Unlike with conjunction, disjunction, and implication, there is no simple
analogy between universals and arithmetic.


## Existentials

Given a variable `x` of type `A` and a proposition `B[x]` which
contains `x` as a free variable, the existentially quantified
proposition `∃ (λ (x : A) → B[x])` holds if for some term `M` of type
`A` the proposition `B[M]` holds.  Here `B[M]` stands for
the proposition `B[x]` with each free occurrence of `x` replaced by
`M`.  The variable `x` appears free in `B[x]` but bound in
`∃ (λ (x : A) → B[x])`.

It is common to adopt a notation such as `∃[ x : A ]→ B[x]`,
which introduces `x` as a bound variable of type `A` that appears
free in `B[x]` and bound in `∃[ x : A ]→ B[x]`.  We won't do
that here, but instead use the lambda notation built-in to Agda
to introduce `x` as a bound variable.

We formalise existential quantification by declaring a suitable
inductive type.
\begin{code}
data ∃ {A : Set} (B : A → Set) : Set where
  _,_ : (x : A) → B x → ∃ B
\end{code}
Evidence that `∃ (λ (x : A) → B[x])` holds is of the form
`(M , N)` where `M` is a term of type `A`, and `N` is evidence
that `B[M]` holds.

Given evidence that `∃ (λ (x : A) → B[x])` holds, and
given evidence that `∀ (x : A) → B[x] → C` holds, where `C` does
not contain `x` as a free variable, we may conclude that `C` holds.
\begin{code}
∃-elim : ∀ {A : Set} {B : A → Set} {C : Set} → ∃ B → (∀ (x : A) → B x → C) → C
∃-elim (M , N) P = P M N
\end{code}
In other words, if we know for every `x` of type `A` that `B[x]`
implies `C`, and we know for some `x` of type `A` that `B[x]` holds,
then we may conclude that `C` holds.  This is because we may
instantiate that proof that `∀ (x : A) → B[x] → C` to any `x`, and we
may choose the particular `x` provided by the evidence that `∃ (λ (x :
A) → B[x])`.


[It would be better to have even and odd as an exercise.  Is there
a simpler example that I could start with?]

As an example, recall the definitions of `even` from
Chapter [Relations](Relations).  
\begin{code}
data even : ℕ → Set where
  ev0 : even zero
  ev+2 : ∀ {n : ℕ} → even n → even (suc (suc n))
\end{code}
A number is even if it is zero, or if it is two
greater than an even number.

We will show that a number is even if and only if it is twice some
other number.  That is, number `n` is even if and only if there exists
a number `m` such that twice `m` is `n`.

First, we need a lemma, which allows us to
simplify twice the successor of `m` to two
more than twice `m`.
\begin{code}
lemma : ∀ (m : ℕ) → 2 * suc m ≡ suc (suc (2 * m))
lemma m =
  begin
    2 * suc m
  ≡⟨⟩
    suc m + (suc m + zero)
  ≡⟨⟩
    suc (m + (suc (m + zero)))
  ≡⟨ cong suc (+-suc m (m + zero)) ⟩
    suc (suc (m + (m + zero)))
  ≡⟨⟩
    suc (suc (2 * m))
  ∎
\end{code}
The lemma is straightforward, and uses the lemma
`+-suc` from Chapter [Properties](Properties), which
allows us to simplify `m + suc n` to `suc (m + n)`.

Here is the proof in the forward direction.
\begin{code}  
ev-ex : ∀ {n : ℕ} → even n → ∃(λ (m : ℕ) → 2 * m ≡ n)
ev-ex ev0 =  (zero , refl)
ev-ex (ev+2 ev) with ev-ex ev
... | (m , refl) = (suc m , lemma m)
\end{code}
Given an even number, we must show it is twice some
other number.  The proof is a function, which
given a proof that `n` is even
returns a pair consisting of `m` and a proof
that twice `m` is `n`.  The proof is by induction over
the evidence that `n` is even.

- If the number is even because it is zero, then we return a pair
consisting of zero and the (trivial) proof that twice zero is zero.

- If the number is even because it is two more than another even
number `n`, then we apply the induction hypothesis, giving us a number
`m` and a proof that `2 * m ≡ n`, which we match against `refl`.  We
return a pair consisting of `suc m` and a proof that `2 * suc m ≡ suc
(suc n)`, which follows from `2 * m ≡ n` and the lemma.

Here is the proof in the reverse direction.
\begin{code}
ex-ev : ∀ {n : ℕ} → ∃(λ (m : ℕ) → 2 * m ≡ n) → even n
ex-ev (zero , refl) = ev0
ex-ev (suc m , refl) rewrite lemma m = ev+2 (ex-ev (m , refl))
\end{code}
Given a number that is twice some other number,
we must show that it is even.  The proof is a function,
which given a number `m` and a proof that `n` is twice `m`,
returns a proof that `n` is even.  The proof is by induction
over the number `m`.

- If it is zero, then we must show that twice zero is even,
which follows by rule `ev0`. 

- If it is `suc m`, then we must show that `2 * suc m` is
even.  After rewriting with our lemma, we must show that
`suc (suc (2 * m))` is even.  The inductive hypothesis tells
us `2 * m` is even, from which the desired result follows
by rule `ev+2`.

Negation of an existential is isomorphic to universal
of a negation.  Considering that existentials are generalised
disjuntion and universals are generalised conjunction, this
result is analogous to the one which tells us that negation
of a disjuntion is isomorphic to a conjunction of negations.
\begin{code}
¬∃∀ : ∀ {A : Set} {B : A → Set} → (¬ ∃ (λ (x : A) → B x)) ≃ ∀ (x : A) → ¬ B x
¬∃∀ =
  record
    { to   =  λ { ¬∃bx x bx → ¬∃bx (x , bx) }
    ; fro  =  λ { ∀¬bx (x , bx) → ∀¬bx x bx }
    ; invˡ =  λ { ¬∃bx → extensionality (λ { (x , bx) → refl }) } 
    ; invʳ =  λ { ∀¬bx → refl } 
    }
\end{code}
In the `to` direction, we are given a value `¬∃bx` of type
`¬ ∃ (λ (x : A) → B x)`, and need to show that given a value
`x` of type `A` that `¬ B x` follows, in other words, from
a value `bx` of type `B x` we can derive false.  Combining
`x` and `bx` gives us a value `(x , bx)` of type `∃ (λ (x : A) → B x)`,
and applying `¬∃bx` to that yields a contradiction.

In the `fro` direction, we are given a value `∀¬bx` of type
`∀ (x : A) → ¬ B x`, and need to show that from a value `(x , bx)`
of type `∃ (λ (x : A) → B x)` we can derive false.  Applying `∀¬bx`
to `x` gives a value of type `¬ B x`, and applying that to `bx` yields
a contradiction.

The two inverse proofs are straightforward, where one direction
requires extensionality.

*Exercise* Show `∃ (λ (x : A) → ¬ B x) → ¬ (∀ (x : A) → B x)`.



## Decidability

\begin{code}
data Dec : Set → Set where
  yes : ∀ {A : Set} → A → Dec A
  no  : ∀ {A : Set} → (¬ A) → Dec A
\end{code}

## Unicode

This chapter introduces the following unicode.

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)


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
dem-≃ : ∀ {A B : Set} → (¬ (A ⊎ B)) ≃ (¬ A × ¬ B)
dem-≃ = →-distributes-⊎
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



    
