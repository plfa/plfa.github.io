---
title     : "Connectives: Conjunction, disjunction, and implication"
layout    : page
permalink : /Connectives
---

This chapter introduces the basic logical connectives, by observing
a correspondence between connectives of logic and data types,
a principal known as *Propositions as Types*.

+ *conjunction* is *product*
+ *disjunction* is *sum*
+ *true* is *unit type*
+ *false* is *empty type*
+ *implication* is *function space*


## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Isomorphism using (_≃_; ≃-sym; ≃-trans; _≲_)
open Isomorphism.≃-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties.Simple using (+-suc)
open import Function using (_∘_)
\end{code}

We assume [extensionality][extensionality].
\begin{code}
postulate
  extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g
\end{code}

[extensionality]: Equality/index.html#extensionality


## Conjunction is product

Given two propositions `A` and `B`, the conjunction `A × B` holds
if both `A` holds and `B` holds.  We formalise this idea by
declaring a suitable inductive type.
\begin{code}
data _×_ : Set → Set → Set where
  ⟨_,_⟩ : ∀ {A B : Set} → A → B → A × B
\end{code}
Evidence that `A × B` holds is of the form
`⟨ M , N ⟩`, where `M` provides evidence that `A` holds and
`N` provides evidence that `B` holds.  In the standard library,
the pair constructor is `_,_`, but here we rename it to
`⟨_,_⟩` so that comma is available for other notations
(in particular, lists and environments).

<!-- 
By convention, we parenthesise pairs, even though `M , N` is also
accepted by Agda.
-->

Given evidence that `A × B` holds, we can conclude that either
`A` holds or `B` holds.
\begin{code}
proj₁ : ∀ {A B : Set} → A × B → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set} → A × B → B
proj₂ ⟨ x , y ⟩ = y
\end{code}
If `L` provides evidence that `A × B` holds, then `proj₁ L` provides evidence
that `A` holds, and `proj₂ L` provides evidence that `B` holds.

Equivalently, we could also declare conjunction as a record type.
\begin{code}
record _×′_ (A B : Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B
open _×′_
\end{code}
Here record construction

    record
      { proj₁′ = M
      ; proj₂′ = N
      }

corresponds to the term

    ⟨ M , N ⟩

where `M` is a term of type `A` and `N` is a term of type `B`.

When `⟨_,_⟩` appears in a term on the right-hand side of an equation
we refer to it as a *constructor*, and when it appears in a pattern on
the left-hand side of an equation we refer to it as a *destructor*.
We also refer to `proj₁` and `proj₂` as destructors, since they play a
similar role.  Other terminology refers to a constructor as
*introducing* a conjunction, and to a destructor as *eliminating* a
conjunction.  Indeed, `proj₁` and `proj₂` are sometimes given the
names `×-elim₁` and `×-elim₂`.

Applying each destructor and reassembling the results with the
constructor is the identity over products.
\begin{code}
η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl
\end{code}
The pattern matching on the left-hand side is essential, since
replacing `w` by `⟨ x , y ⟩` allows both sides of the equation to
simplify to the same term.

We set the precedence of conjunction so that it binds less
tightly than anything save disjunction.
\begin{code}
infixr 2 _×_
\end{code}
Thus, `m ≤ n × n ≤ p` parses as `(m ≤ n) × (n ≤ p)`.

<!--
and of the pairing operator so that it binds less tightly
than any arithmetic operator.
`(m * n , p)` parses as `((m * n) , p)`.
-->

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

    ⟨ true  , aa ⟩    ⟨ true  , bb ⟩    ⟨ true ,  cc ⟩
    ⟨ false , aa ⟩    ⟨ false , bb ⟩    ⟨ false , cc ⟩

For example, the following function enumerates all
possible arguments of type `Bool × Tri`:
\begin{code}
×-count : Bool × Tri → ℕ
×-count ⟨ true  , aa ⟩  =  1
×-count ⟨ true  , bb ⟩  =  2
×-count ⟨ true  , cc ⟩  =  3
×-count ⟨ false , aa ⟩  =  4
×-count ⟨ false , bb ⟩  =  5
×-count ⟨ false , cc ⟩  =  6
\end{code}

Product on types also shares a property with product on numbers in
that there is a sense in which it is commutative and associative.  In
particular, product is commutative and associative *up to
isomorphism*.

For commutativity, the `to` function swaps a pair, taking `(x , y)` to
`(y , x)`, and the `from` function does the same (up to renaming).
Instantiating the patterns correctly in `from∘to` and `to∘from` is essential.
Replacing the definition of `from∘to` by `λ w → refl` will not work;
and similarly for `to∘from`, which does the same (up to renaming).
\begin{code}
×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to       =  λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from     =  λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ } 
    ; from∘to  =  λ{ ⟨ x , y ⟩ → refl }
    ; to∘from  =  λ{ ⟨ y , x ⟩ → refl }
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
taking `((x , y) , z)` to `(x , (y , z))`, and the `from` function does
the inverse.  Again, the evidence of left and right inverse requires
matching against a suitable pattern to enable simplification.
\begin{code}
×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
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

The nullary case of `η-×` is `η-⊤`, which asserts that any
term of type `⊤` must be equal to `tt`.
\begin{code}
η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl
\end{code}
The pattern matching on the left-hand side is essential.  Replacing
`w` by `tt` allows both sides of the equation to simplify to the
same term.

We refer to `⊤` as the *unit* type. And, indeed,
type `⊤` has exactly once member, `tt`.  For example, the following
function enumerates all possible arguments of type `⊤`:
\begin{code}
⊤-count : ⊤ → ℕ
⊤-count tt = 1
\end{code}

For numbers, one is the identity of multiplication. Correspondingly,
unit is the identity of product *up to isomorphism*.  For left
identity, the `to` function takes `(tt , x)` to `x`, and the `from`
function does the inverse.  The evidence of left inverse requires
matching against a suitable pattern to enable simplification.
\begin{code}
⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to      = λ{ ⟨ tt , x ⟩ → x }
    ; from    = λ{ x → ⟨ tt , x ⟩ }
    ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
    ; to∘from = λ{ x → refl }
    }
\end{code}

Having an *identity* is different from having an identity
*up to isomorphism*.  Compare the two statements:

    1 * m ≡ m
    ⊤ × A ≃ A

In the first case, we might have that `m` is `2`, and both
`1 * m` and `m` are equal to `2`.  In the second
case, we might have that `A` is `Bool`, and `⊤ × Bool` is *not* the
same as `Bool`.  But there is an isomorphism between the two types.
For instance, `(tt, true)`, which is a member of the former,
corresponds to `true`, which is a member of the latter.

Right identity follows from commutativity of product and left identity.
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
Here we have used a chain of isomorphisms,
analogous to that used for equality.


## Disjunction is sum

Given two propositions `A` and `B`, the disjunction `A ⊎ B` holds
if either `A` holds or `B` holds.  We formalise this idea by
declaring a suitable inductive type.
\begin{code}
data _⊎_ : Set → Set → Set where
  inj₁ : ∀ {A B : Set} → A → A ⊎ B
  inj₂ : ∀ {A B : Set} → B → A ⊎ B
\end{code}
Evidence that `A ⊎ B` holds is either of the form `inj₁ M`, where `M`
provides evidence that `A` holds, or `inj₂ N`, where `N` provides
evidence that `B` holds.

Given evidence that `A → C` and `B → C` both hold, then given
evidence that `A ⊎ B` holds we can conclude that `C` holds.
\begin{code}
⊎-elim : ∀ {A B C : Set} → (A → C) → (B → C) → (A ⊎ B → C)
⊎-elim f g (inj₁ x) = f x
⊎-elim f g (inj₂ y) = g y
\end{code}
Pattern matching against `inj₁` and `inj₂` is typical of how we exploit
evidence that a disjunction holds.

When `inj₁` and `inj₂` appear on the right-hand side of an equation we
refer to them as *constructors*, and when they appears on the
left-hand side we refer to them as *destructors*.  We also refer
to `⊎-elim` as a destructor, since it plays a similar role.
Other terminology refers to constructors as *introducing* a disjunction,
and to a destructors as *eliminating* a disjunction.

Applying the destructor to each of the constructors is the identity.
\begin{code}
η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → ⊎-elim inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl
\end{code}
More generally, we can also throw in an arbitrary function from a disjunction.
\begin{code}
uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  ⊎-elim (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl
\end{code}
The pattern matching on the left-hand side is essential.  Replacing
`w` by `inj₁ x` allows both sides of the equation to simplify to the
same term, and similarly for `inj₂ y`.

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

    inj₁ true     inj₂ aa
    inj₁ false    inj₂ bb
                  inj₂ cc

For example, the following function enumerates all
possible arguments of type `Bool ⊎ Tri`:
\begin{code}
⊎-count : Bool ⊎ Tri → ℕ
⊎-count (inj₁ true)   =  1
⊎-count (inj₁ false)  =  2
⊎-count (inj₂ aa)     =  3
⊎-count (inj₂ bb)     =  4
⊎-count (inj₂ cc)     =  5
\end{code}

Sum on types also shares a property with sum on numbers in that it is
commutative and associative *up to isomorphism*.

For commutativity, the `to` function swaps the two constructors,
taking `inj₁ x` to `inj₂ x`, and `inj₂ y` to `inj₁ y`; and the `from`
function does the same (up to renaming). Replacing the definition of
`from∘to` by `λ w → refl` will not work; and similarly for `to∘from`, which
does the same (up to renaming).
\begin{code}
⊎-comm : ∀ {A B : Set} → (A ⊎ B) ≃ (B ⊎ A)
⊎-comm = record
  { to       =  λ{ (inj₁ x) → (inj₂ x)
                 ; (inj₂ y) → (inj₁ y)
                 }
  ; from     =  λ{ (inj₁ y) → (inj₂ y)
                 ; (inj₂ x) → (inj₁ x)
                 }
  ; from∘to  =  λ{ (inj₁ x) → refl
                 ; (inj₂ y) → refl
                 }
  ; to∘from  =  λ{ (inj₁ y) → refl
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

For associativity, the `to` function reassociates, and the `from` function does
the inverse.  Again, the evidence of left and right inverse requires
matching against a suitable pattern to enable simplification.
\begin{code}
⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc = record
  { to       =  λ{ (inj₁ (inj₁ x)) → (inj₁ x)
                 ; (inj₁ (inj₂ y)) → (inj₂ (inj₁ y))
                 ; (inj₂ z)        → (inj₂ (inj₂ z))
                 }
  ; from     =  λ{ (inj₁ x)        → (inj₁ (inj₁ x))
                 ; (inj₂ (inj₁ y)) → (inj₁ (inj₂ y))
                 ; (inj₂ (inj₂ z)) → (inj₂ z)
                 }
  ; from∘to  =  λ{ (inj₁ (inj₁ x)) → refl
                 ; (inj₁ (inj₂ y)) → refl
                 ; (inj₂ z)        → refl
                 }
  ; to∘from  =  λ{ (inj₁ x)        → refl
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

## False is empty

False `⊥` never holds.  We formalise this idea by declaring
a suitable inductive type.
\begin{code}
data ⊥ : Set where
  -- no clauses!
\end{code}
There is no possible evidence that `⊥` holds.

Since false never holds, knowing that it holds tells us we are in a
paradoxical situation.  Given evidence that `⊥` holds, we might
conclude anything!  This is a basic principle of logic, known in
medieval times by the latin phrase *ex falso*, and known to children
through phrases such as "if pigs had wings, then I'd be the Queen of
Sheba".  We formalise it as follows.
\begin{code}
⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()
\end{code}
This is our first use of the *absurd pattern* `()`.
Here since `⊥` is a type with no members, we indicate that it is
*never* possible to match against a value of this type by using
the pattern `()`.

The nullary case of `uniq-⊎` is `uniq-⊥`, which asserts that `⊥-elim`
is equal to any arbitrary function from `⊥`.
\begin{code}
uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()
\end{code}
Using the absurd pattern asserts there are no possible values for `w`,
so the equation holds trivially.

We refer to `⊥` as *empty* type. And, indeed,
type `⊥` has no members. For example, the following function
enumerates all possible arguments of type `⊥`:
\begin{code}
⊥-count : ⊥ → ℕ
⊥-count ()
\end{code}
Here again the absurd pattern `()` indicates that no value can match
type `⊥`.

For numbers, zero is the identity of addition. Correspondingly,
empty is the identity of sums *up to isomorphism*.
For left identity, the `to` function observes that `inj₁ ()` can never arise,
and takes `inj₂ x` to `x`, and the `from` function
does the inverse.  The evidence of left inverse requires matching against
a suitable pattern to enable simplification.
\begin{code}
⊥-identityˡ : ∀ {A : Set} → (⊥ ⊎ A) ≃ A
⊥-identityˡ =
  record
    { to       =  λ{ (inj₁ ())
                   ; (inj₂ x) → x
                   }
    ; from     =  λ{ x → inj₂ x }
    ; from∘to  =  λ{ (inj₁ ())
                   ; (inj₂ x) → refl
                   }
    ; to∘from  =  λ{ x → refl }
    }
\end{code}

Having an *identity* is different from having an identity
*up to isomorphism*.  Compare the two statements:

    0 + m ≡ m
    ⊥ ⊎ A ≃ A

In the first case, we might have that `m` is `2`, and both `0 + m` and
`m` are equal to `2`.  In the second case, we might have that `A` is
`Bool`, and `⊥ ⊎ Bool` is *not* the same as `Bool`.  But there is an
isomorphism between the two types.  For instance, `inj₂ true`, which is
a member of the former, corresponds to `true`, which is a member of
the latter.

Right identity follows from commutativity of sum and left identity.  
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

## Implication is function {#implication}

Given two propositions `A` and `B`, the implication `A → B` holds if
whenever `A` holds then `B` must also hold.  We formalise implication using
the function type, which has appeared throughout this book.

Evidence that `A → B` holds is of the form

    λ (x : A) → N x

where `N x` is a term of type `B` containing as a free variable `x` of type `A`.
Given a term `L` providing evidence that `A → B` holds, and a term `M`
providing evidence that `A` holds, the term `L M` provides evidence that
`B` holds.  In other words, evidence that `A → B` holds is a function that
converts evidence that `A` holds into evidence that `B` holds.

Put another way, if we know that `A → B` and `A` both hold,
then we may conclude that `B` holds.
\begin{code}
→-elim : ∀ {A B : Set} → (A → B) → A → B
→-elim L M = L M
\end{code}
In medieval times, this rule was known by the name *modus ponens*.
It corresponds to function application.

Defining a function, with an named definition or a lambda expression,
is referred to as *introducing* a function,
while applying a function is referred to as *eliminating* the function.

Elimination followed by introduction is the identity.
\begin{code}
η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ {A} {B} f = extensionality η-helper
  where
  η-helper : (x : A) → (λ (x : A) → f x) x ≡ f x
  η-helper x = refl
\end{code}
The proof depends on extensionality.

<!--

If we introduce an implication and then immediately eliminate it, we can
always simplify the resulting term.  Thus

    λ{ x → N } M

simplifies to `N[x := M]`, where `N[x := M]` stands for the term `N` with each
free occurrence of `x` replaced by `M`.

-->

Implication binds less tightly than any other operator. Thus, `A ⊎ B →
B ⊎ A` parses as `(A ⊎ B) → (B ⊎ A)`.

Given two types `A` and `B`, we refer to `A → B` as the *function*
space from `A` to `B`.  It is also sometimes called the *exponential*,
with `B` raised to the `A` power.  Among other reasons for calling
it the exponential, note that if type `A` has `m` distinct
members, and type `B` has `n` distinct members, then the type
`A → B` has `n ^ m` distinct members.  For instance, consider a
type `Bool` with two members and a type `Tri` with three members,
as defined earlier. The the type `Bool → Tri` has nine (that is,
three squared) members:

    λ{true → aa; false → aa}  λ{true → aa; false → bb}  λ{true → aa; false → cc}
    λ{true → bb; false → aa}  λ{true → bb; false → bb}  λ{true → bb; false → cc}
    λ{true → cc; false → aa}  λ{true → cc; false → bb}  λ{true → cc; false → cc}

For example, the following function enumerates all possible
arguments of the type `Bool → Tri`:
\begin{code}
→-count : (Bool → Tri) → ℕ
→-count f with f true | f false
...           | aa    | aa      =   1
...           | aa    | bb      =   2  
...           | aa    | cc      =   3
...           | bb    | aa      =   4
...           | bb    | bb      =   5
...           | bb    | cc      =   6
...           | cc    | aa      =   7
...           | cc    | bb      =   8
...           | cc    | cc      =   9  
\end{code}

Exponential on types also share a property with exponential on
numbers in that many of the standard identities for numbers carry
over to the types.

Corresponding to the law

    (p ^ n) ^ m  =  p ^ (n * m)

we have the isomorphism

    A → (B → C)  ≃  (A × B) → C

Both types can be viewed as functions that given evidence that `A` holds
and evidence that `B` holds can return evidence that `C` holds.
This isomorphism sometimes goes by the name *currying*.
The proof of the right inverse requires extensionality.
\begin{code}
currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }
\end{code}

Currying tells us that instead of a function that takes a pair of arguments,
we can have a function that takes the first argument and returns a function that
expects the second argument.  Thus, for instance, our way of writing addition:

    _+_ : ℕ → ℕ → ℕ

is isomorphic to a function that accepts a pair of arguments:

    _+′_ : (ℕ × ℕ) → ℕ

Agda is optimised for currying, so `2 + 3` abbreviates `_+_ 2 3`.
In a language optimised for pairing, we would instead take `2 +′ 3` as
an abbreviation for `_+′_ (2 , 3)`.

Corresponding to the law

    p ^ (n + m) = (p ^ n) * (p ^ m)

we have the isomorphism

    (A ⊎ B) → C  ≃  (A → C) × (B → C)

That is, the assertion that if either `A` holds or `B` holds then `C` holds
is the same as the assertion that if `A` holds then `C` holds and if
`B` holds then `C` holds.  The proof of the left inverse requires extensionality.
\begin{code}
→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to      = λ{ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ{ (inj₁ x) → g x ; (inj₂ y) → h y } }
    ; from∘to = λ{ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }
\end{code}

Corresponding to the law

    (p * n) ^ m = (p ^ m) * (n ^ m)

we have the isomorphism

    A → B × C  ≃  (A → B) × (A → C)

That is, the assertion that if either `A` holds then `B` holds and `C` holds
is the same as the assertion that if `A` holds then `B` holds and if
`A` holds then `C` holds.  The proof of left inverse requires both extensionality
and the rule `η-×` for products.
\begin{code}
→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
    { to      = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ{ x → ⟨ g x , h x ⟩ } }
    ; from∘to = λ{ f → extensionality λ{ x → η-× (f x) } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }
\end{code}


## Distribution

Products distributes over sum, up to isomorphism.  The code to validate
this fact is similar in structure to our previous results.
\begin{code}
×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
  record
    { to      = λ{ ⟨ inj₁ x , z ⟩ → (inj₁ ⟨ x , z ⟩) 
                 ; ⟨ inj₂ y , z ⟩ → (inj₂ ⟨ y , z ⟩)
                 }
    ; from    = λ{ (inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x , z ⟩
                 ; (inj₂ ⟨ y , z ⟩) → ⟨ inj₂ y , z ⟩
                 }
    ; from∘to = λ{ ⟨ inj₁ x , z ⟩ → refl
                 ; ⟨ inj₂ y , z ⟩ → refl
                 }
    ; to∘from = λ{ (inj₁ ⟨ x , z ⟩) → refl
                 ; (inj₂ ⟨ y , z ⟩) → refl
                 }               
    }
\end{code}

Sums do not distribute over products up to isomorphism, but it is an embedding.
\begin{code}
⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
    { to      = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
                 ; (inj₂ z)         → ⟨ inj₂ z , inj₂ z ⟩
                 }  
    ; from    = λ{ ⟨ inj₁ x , inj₁ y ⟩ → (inj₁ ⟨ x , y ⟩)
                 ; ⟨ inj₁ x , inj₂ z ⟩ → (inj₂ z)
                 ; ⟨ inj₂ z , _      ⟩ → (inj₂ z)
                 }
    ; from∘to = λ{ (inj₁ ⟨ x , y ⟩) → refl
                 ; (inj₂ z)         → refl
                 } 
    }
\end{code}
Note that there is a choice in how we write the `from` function.
As given, it takes `⟨ inj₂ z , inj₂ z′ ⟩` to `inj₂ z`, but it is
easy to write a variant that instead returns `inj₂ z′`.  We have
an embedding rather than an isomorphism because the
`from` function must discard either `z` or `z′` in this case.

In the usual approach to logic, both of the distribution laws
are given as equivalences, where each side implies the other:

    A & (B ∨ C) ⇔ (A & B) ∨ (A & C)
    A ∨ (B & C) ⇔ (A ∨ B) & (A ∨ C)

But when we consider the two laws in terms of evidence, where `_&_`
corresponds to `_×_` and `_∨_` corresponds to `_⊎_`, then the first
gives rise to an isomorphism, while the second only gives rise to an
embedding, revealing a sense in which one of these laws is "more
true" than the other.


### Exercise (`×⊎-implies-⊎×`)

Show that a conjunct of disjuncts implies a disjunct of conjuncts.
\begin{code}
×⊎-Implies-⊎× = ∀ {A B C D : Set} → (A ⊎ B) × (C ⊎ D) → (A × C) ⊎ (B × D)
\end{code}
Does the converse hold? If so, prove; if not, explain why.


### Exercise (`⇔-refl`, `⇔-sym`, `⇔-trans`)

Define equivalence of propositions (also known as "if and only if") as follows.
\begin{code}
record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
\end{code}
Show that equivalence is reflexive, symmetric, and transitive.


### Exercise (`⇔-iso`)

Show that `A ⇔ B` is isomorphic to `(A → B) × (B → A)`.


## Standard library

Definitions similar to those in this chapter can be found in the standard library.
\begin{code}
import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
import Data.Unit using (⊤; tt)
import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to ⊎-elim)
import Data.Empty using (⊥; ⊥-elim)
\end{code}


## Unicode

This chapter uses the following unicode.

    ×  U+00D7  MULTIPLICATION SIGN (\x)
    ⊎  U+228E  MULTISET UNION (\u+)
    ⊤  U+22A4  DOWN TACK (\top)
    ⊥  U+22A5  UP TACK (\bot)
    η  U+03B7  GREEK SMALL LETTER ETA (\eta)
    ₁  U+2081  SUBSCRIPT ONE (\_1)
    ₂  U+2082  SUBSCRIPT TWO (\_2)
    ⇔  U+21D4  LEFT RIGHT DOUBLE ARROW (\<=>)

