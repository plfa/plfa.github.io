---
title     : "Denot: Denotational semantics for the untyped lambda calculus"
layout    : page
prev      : /Untyped/
permalink : /Denot/
next      : /Acknowledgements/
---

\begin{code}
module plfa.Denot where
\end{code}

[PLW:
  Perhaps break this chapter into three chapters:
    - The denotational semantics.
    - The proof that the semantics is compositional.
    - The proof that reduction preserves and reflects the semantics.]

The lambda calculus is a language about _functions_, that is, mappings
from input to output. In computing we often think of such
mappings as being carried out by a sequence of
operations that transform an input into an output.  But 
functions can also be represented as data. For example, one
can tabulate a function, that is, create a table where each row has
two entries, an input and the corresponding output for the function.
Function application is then the process of looking up the row for
a given input and reading off the output.

We shall create a semantics for the untyped lambda calculus based on
this idea of functions-as-tables. However, there are two difficulties
that arise. First, functions often have an infinite domain, so it
would seem that we would need infinitely long tables to represent
functions. Second, in the lambda calculus, functions can be applied to
functions. They can even be applied to themselves! So it would seem
that the tables would contain cycles. One might start to worry that
advanced techniques are necessary to to address these issues, but
fortunately this is not the case!

The first problem, of functions with infinite domains, is solved by
observing that in the execution of a terminating program, each lambda
abstraction will only be applied to a finite number of distinct
arguments. (We come back later to discuss diverging programs.) This
observation is another way of looking at Dana Scott's insight that
only continuous functions are needed to model the lambda calculus.

The second problem, that of self-application, is solved by relaxing
the way in which we lookup an argument in a function's table.
Naively, one would look in the table for a row in which the input
entry exactly matches the argument. In the case of self-application,
this would require the table to contain a copy of itself. Impossible!
(At least, it is impossible if we want to build tables using inductive
data type definitions, which indeed we do.)  Instead it is sufficient
to find an input such that every row of the input appears as a row of
the argument (that is, the input is a subset of the argument).  In the
case of self-application, the table only needs to contain a smaller
copy of itself, which is fine.

With these two observations in hand, it is straightforward to write
down a denotational semantics of the lambda calculus.

## Imports

\begin{code}
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum
open import Agda.Primitive using (lzero)
open import plfa.Untyped
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Empty using (⊥-elim)
open import Data.Unit
open import Relation.Nullary using (Dec; yes; no)
open import Function using (_∘_)
-- open import plfa.Isomorphism using (extensionality)  -- causes a bug!
\end{code}

\begin{code}
postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
\end{code}

## Values

The `Value` data type represents a finite portion of a function.  We
think of a value as a finite set of pairs that represent input-output
mappings. The `Value` data type represents the set as a binary tree
whose internal nodes are the union operator and whose leaves represent
either a single mapping or the empty set.

  * The ⊥ value is an empty function. We think of this value as
    providing no information about the computation.

  * A value of the form `v ↦ v′` is a single input-output mapping, from
    input `v` to output `v′`.

  * A value of the form `v₁ ⊔ v₂` is a function that maps inputs to
    outputs according to both `v₁` and `v₂`.  Think of it as taking the
    union of the two sets.

\begin{code}
infixr 7 _↦_
infixl 5 _⊔_

data Value : Set where
  ⊥ : Value
  _↦_ : Value → Value → Value
  _⊔_ : Value → Value → Value
\end{code}

The ⊑ relation adapts the familiar notion of subset to the Value data
type. This relation plays the key role in enabling self-application.
There are two rules that are specific to functions, Fun⊑ and Dist⊑,
which we discuss below.

\begin{code}
infix 4 _⊑_

data _⊑_ : Value → Value → Set where

  Bot⊑ : ∀ {v} → ⊥ ⊑ v

  ConjL⊑ : ∀ {v v₁ v₂}
      → v₁ ⊑ v
      → v₂ ⊑ v
        -----------------
      → (v₁ ⊔ v₂) ⊑ v

  ConjR1⊑ : ∀ {v v₁ v₂}
     → v ⊑ v₁
       -------------
     → v ⊑ (v₁ ⊔ v₂)

  ConjR2⊑ : ∀ {v v₁ v₂}
     → v ⊑ v₂
       -------------
     → v ⊑ (v₁ ⊔ v₂)

  Trans⊑ : ∀ {v₁ v₂ v₃}
     → v₁ ⊑ v₂
     → v₂ ⊑ v₃
       --------
     → v₁ ⊑ v₃

  Fun⊑ : ∀ {v₁ v₂ v₃ v₄}
       → v₃ ⊑ v₁
       → v₂ ⊑ v₄
         ---------------------
       → (v₁ ↦ v₂) ⊑ (v₃ ↦ v₄)

  Dist⊑ : ∀{v₁ v₂ v₃}
         --------------------------------------
       → v₁ ↦ (v₂ ⊔ v₃) ⊑ (v₁ ↦ v₂) ⊔ (v₁ ↦ v₃)

{-
  Dist⊑ : ∀{v₁ v₂ v₃ w}
       → v₁ ↦ v₂ ⊑ w
       → v₁ ↦ v₃ ⊑ w
         --------------------------------------
       → v₁ ↦ (v₂ ⊔ v₃) ⊑ w
-}
\end{code}
[PLW: If we reformulate Dist⊑, perhaps Trans⊑ becomes a theorem.

  Dist⊑ : ∀{v₁ v₂ v₃ v}
         v₁ ↦ v₂ ⊑ v
         v₁ ↦ v₃ ⊑ v
         ------------------
       → v₁ ↦ (v₂ ⊔ v₃) ⊑ v
]

The first five rules are straightforward.
The rule `Fun⊑` captures when it is OK to match a higher-order argument
`v₃ ↦ v₄` to a table entry whose input is `v₁ ↦ v₂`.  Considering a
call to the higher-order argument. It is OK to pass a larger argument
than expected, so `v₁` can be larger than `v₃`. Also, it is OK to
disregard some of the output, so `v₂` can be smaller than `v₄`.
The rule `Dist⊑` says that if you have two entries for the same input,
then you can combine them into a single entry and joins the two
outputs.

The `⊑` relation is reflexive.

\begin{code}
Refl⊑ : ∀ {v} → v ⊑ v
Refl⊑ {⊥} = Bot⊑
Refl⊑ {v ↦ v'} = Fun⊑ Refl⊑ Refl⊑
Refl⊑ {v₁ ⊔ v₂} = ConjL⊑ (ConjR1⊑ Refl⊑) (ConjR2⊑ Refl⊑)
\end{code}

With reflexivity in hand, the old distributivity rule is a consequence of the new.
\begin{code}
{-
dist⊑ : ∀{v₁ v₂ v₃}
         --------------------------------------
       → v₁ ↦ (v₂ ⊔ v₃) ⊑ (v₁ ↦ v₂) ⊔ (v₁ ↦ v₃)
dist⊑ {v₁} {v₂} {v₃} =
  Dist⊑ (ConjR1⊑ Refl⊑)
        (ConjR2⊑ Refl⊑)
-}
\end{code}

The `⊔` operation is monotonic with respect to `⊑`, that is, given two
larger values it produces a larger value.

\begin{code}
⊔⊑⊔ : ∀ {v₁ v₂ v₃ v₄}
      → v₁ ⊑ v₃  →  v₂ ⊑ v₄
        -----------------------
      → (v₁ ⊔ v₂) ⊑ (v₃ ⊔ v₄)
⊔⊑⊔ d₁ d₂ = ConjL⊑ (ConjR1⊑ d₁) (ConjR2⊑ d₂)
\end{code}

The (Dist⊑) rule can be used to combine two entries even when the
input values are not identical. One can first combine the two inputs
using ⊔ and then apply the (Dist⊑) rule to obtain the following
property.

\begin{code}
Dist⊔↦⊔ : ∀{v₁ v₁' v₂ v₂' : Value}
        → (v₁ ⊔ v₁') ↦ (v₂ ⊔ v₂') ⊑ (v₁ ↦ v₂) ⊔ (v₁' ↦ v₂')
Dist⊔↦⊔{v₁}{v₁'}{v₂}{v₂'} =
    Trans⊑ (Dist⊑ {v₁ = v₁ ⊔ v₁'}{v₂ = v₂}{v₃ = v₂'})
           (⊔⊑⊔ (Fun⊑ (ConjR1⊑ Refl⊑) Refl⊑)
                      (Fun⊑ (ConjR2⊑ Refl⊑) Refl⊑))
\end{code}

<!-- above might read more nicely if we introduce inequational reasoning -->


## Environments

An environment gives meaning to the free variables in a term.  Because
variables are represented as de Bruijn indices, they are numbers, so
an environment can be represented simply as a sequence of values.

\begin{code}
Env : Context → Set
Env Γ = ∀ (x : Γ ∋ ★) → Value
\end{code}

We have the empty environment, and we can extend an environment.
\begin{code}
`∅ : Env ∅
`∅ ()

_`,_ : ∀ {Γ} → Env Γ → Value → Env (Γ , ★)
(γ `, v) Z = v
(γ `, v) (S x) = γ x
\end{code}

We can recover the initial environment from an extended environment,
and the last value. Putting them back together again takes us where we started.
\begin{code}
init : ∀ {Γ} → Env (Γ , ★) → Env Γ
init γ x = γ (S x)

last : ∀ {Γ} → Env (Γ , ★) → Value
last γ = γ Z

init-last : ∀ {Γ} → (γ : Env (Γ , ★)) → γ ≡ (init γ `, last γ)
init-last {Γ} γ = extensionality lemma
  where
  lemma : ∀ (x : Γ , ★ ∋ ★) → γ x ≡ (init γ `, last γ) x
  lemma Z      =  refl
  lemma (S x)  =  refl
\end{code}

The nth function takes a De Bruijn index and finds the corresponding
value in the environment.

\begin{code}
nth : ∀{Γ} → (Γ ∋ ★) → Env Γ → Value
nth x ρ = ρ x
\end{code}

We extend the `⊑` relation point-wise to environments with the
following definition.

\begin{code}
_`⊑_ : ∀ {Γ} → Env Γ → Env Γ → Set
_`⊑_ {Γ} γ δ = ∀ (x : Γ ∋ ★) → γ x ⊑ δ x
\end{code}

We define a bottom environment and a join operator on environments,
which takes the point-wise join of their values.

\begin{code}
`⊥ : ∀ {Γ} → Env Γ
`⊥ x = ⊥

_`⊔_ : ∀ {Γ} → Env Γ → Env Γ → Env Γ
(γ `⊔ δ) x = γ x ⊔ δ x
\end{code}

The Refl⊑, ConjR1⊑, and ConjR2⊑ rules lift to environments.  So the join of
two environments γ and δ is greater than the first environment γ
or the second environment δ.

\begin{code}
`Refl⊑ : ∀ {Γ} {γ : Env Γ} → γ `⊑ γ
`Refl⊑ {Γ} {γ} x = Refl⊑ {γ x}

EnvConjR1⊑ : ∀ {Γ} → (γ : Env Γ) → (δ : Env Γ) → γ `⊑ (γ `⊔ δ)
EnvConjR1⊑ γ δ x = ConjR1⊑ Refl⊑

EnvConjR2⊑ : ∀ {Γ} → (γ : Env Γ) → (δ : Env Γ) → δ `⊑ (γ `⊔ δ)
EnvConjR2⊑ γ δ x = ConjR2⊑ Refl⊑
\end{code}

## Denotational Semantics

We define the semantics with a judgment of the form `ρ ⊢ M ↓ v`,
where `ρ` is the environment, `M` the program, and `v` is a result value.
For readers familiar with big-step semantics, this notation will feel
quite natural, but don't let the similarity fool you.  There are
subtle but important differences! So here is the definition of the
semantics, which we discuss in detail in the following paragraphs.

[PLW: PLFA doesn't mention big-step semantics. But perhaps it should!]

\begin{code}
infix 3 _⊢_↓_

data _⊢_↓_ : ∀{Γ} → Env Γ → (Γ ⊢ ★) → Value → Set where

  var : ∀ {Γ} {γ : Env Γ} {x}
        -------------------
      → γ ⊢ (` x) ↓ γ x

  ↦-elim : ∀ {Γ} {γ : Env Γ} {M₁ M₂ v₁ v₂}
        → γ ⊢ M₁ ↓ (v₁ ↦ v₂)
        → γ ⊢ M₂ ↓ v₁
          ------------------
        → γ ⊢ (M₁ · M₂) ↓ v₂

  ↦-intro : ∀ {Γ} {γ : Env Γ} {M v₁ v₂}
        → γ `, v₁ ⊢ M ↓ v₂
          ---------------------
        → γ ⊢ (ƛ M) ↓ (v₁ ↦ v₂)

  ⊥-intro : ∀ {Γ} {γ : Env Γ} {M}
          ---------
        → γ ⊢ M ↓ ⊥

  ⊔-intro : ∀ {Γ} {γ : Env Γ} {M v₁ v₂}
        → γ ⊢ M ↓ v₁
        → γ ⊢ M ↓ v₂
          -----------------
        → γ ⊢ M ↓ (v₁ ⊔ v₂)
     
  sub : ∀ {Γ} {γ : Env Γ} {M v₁ v₂}
        → γ ⊢ M ↓ v₁
        → v₂ ⊑ v₁
          ----------
        → γ ⊢ M ↓ v₂
\end{code}

[PLW: Say we redefine:
  var : ∀ {Γ} {γ : Env Γ} {x}
      → v ⊑ γ x
        -------------
      → γ ⊢ (` x) ↓ v
Then does sub (downward closure) follow from the other rules?]

Consider the rule for lambda abstractions, `↦-intro`.  It says that a
lambda abstraction results in a single-entry table that maps the input
`v₁` to the output `v₂`, provided that evaluating the body in an
environment with `v₁` bound to its parameter produces the output `v₂`.
As a simple example of this rule, we can see that the identity function
maps `⊥` to `⊥`. 

\begin{code}
id : ∅ ⊢ ★
id = ƛ # 0
\end{code}

\begin{code}
denot-id : ∀ {γ v} → γ ⊢ id ↓ v ↦ v
denot-id = ↦-intro var

denot-id-two : ∀ {γ v w} → γ ⊢ id ↓ (v ↦ v) ⊔ (w ↦ w)
denot-id-two = ⊔-intro denot-id denot-id
\end{code}

Of course, we will need tables with many rows for our lambda
abstractions. These can be constructed using the (⊔-intro) rule.  If
term M (typically a lambda abstraction) can produce both tables v₁ and
v₂, then it produces the combined table v₁ ⊔ v₂. One can take an
operational view of the rules (↦-intro) and (⊔-intro) by 
imagining that when an interpreter first comes to a lambda
abstraction, it pre-evaluates the function on a bunch of randomly
chosen arguments, using many instances of the rule (↦-intro), and then
joins them into one table using many instances of the rule (⊔-intro).
In the following we show that the identity function produces a table
containing both of the previous results, ⊥ ↦ ⊥ and (⊥ ↦ ⊥) ↦ (⊥ ↦ ⊥).

\begin{code}
denot-id3 : `∅ ⊢ id ↓ (⊥ ↦ ⊥) ⊔ (⊥ ↦ ⊥) ↦ (⊥ ↦ ⊥)
denot-id3 = denot-id-two
\end{code}

We most often think of the judgment γ ⊢ M ↓ v as taking the
environment γ and term M as input, producing the result v.  However,
it is worth emphasizing that the semantics is a _relation_.  The above
results for the identity function show that the same environment and
term can be mapped to different results. However, the results for a
given γ and M are not _too_ different, they are all finite
approximations of the same function. Perhaps a better way of thinking
about the judgment γ ⊢ M ↓ v is that the γ, M, and v are all inputs
and the semantics either confirms or denies whether v is an accurate
partial description of the result of M in environment γ.

Next we consider the meaning of function application as given by the
(↦-elim) rule. In the premise of the rule we have that M₁ maps v₁ to
v₂. So if M₂ produces v₁, then the application of M₁ to M₂ produces
v₂.

As an example of function application and the (↦-elim) rule, we apply
the identity function to itself.  Indeed, we have both that ∅ ⊢ id
↓ (v' ↦ v') ↦ (v' ↦ v') and also ∅ ⊢ id ↓ (v' ↦ v'), so we can
apply the rule (↦-elim).

\begin{code}
id-app-id : ∀ {v' : Value} → `∅ ⊢ id · id ↓ (v' ↦ v')
id-app-id {v'} = ↦-elim (↦-intro var) (↦-intro var)
\end{code}

Next we revisit the Church numeral two.  This function has two
parameters: a function and an arbitrary value v₁, and it applies the
function twice. So the function must map v₁ to some value, which we'll
name v₂. Then for the second application, it must map v₂ to some
value. Let's name it v₃. So the parameter's table must contain two
entries, both v₁ ↦ v₂ and v₂ ↦ v₃. For each application of the table,
we extract the appropriate entry from it using the (sub) rule.  In
particular, we use the ConjR1⊑ and ConjR2⊑ to select v₁ ↦ v₂ and v₂ ↦
v₃, respectively, from the table v₁ ↦ v₂ ⊔ v₂ ↦ v₃. So the meaning of
twoᶜ is that it takes this table and parameter v₁, and it returns v₃.
Indeed we derive this as follows.

\begin{code}
denot-twoᶜ : ∀{v₁ v₂ v₃ : Value} → `∅ ⊢ twoᶜ ↓ ((v₁ ↦ v₂ ⊔ v₂ ↦ v₃) ↦ (v₁ ↦ v₃))
denot-twoᶜ {v₁}{v₂}{v₃} =
  ↦-intro (↦-intro (↦-elim (sub var lt1) (↦-elim (sub var lt2) var)))
  where lt1 : v₂ ↦ v₃ ⊑ v₁ ↦ v₂ ⊔ v₂ ↦ v₃
        lt1 = ConjR2⊑ (Fun⊑ Refl⊑ Refl⊑)
     
        lt2 : v₁ ↦ v₂ ⊑ v₁ ↦ v₂ ⊔ v₂ ↦ v₃
        lt2 = (ConjR1⊑ (Fun⊑ Refl⊑ Refl⊑))
\end{code}


Next we have a classic example of self application: Δ = λx. (x x).
The input value for x needs to be a table, and it needs to have an
entry that maps a smaller version of itself, call it v₁, to some value
v₂. So the input value looks like v₁ ↦ v₂ ⊔ v₁. Of course, then the
output of Δ is v₂. The derivation is given below.  The first occurrences
of x evaluates to v₁ ↦ v₂, the second occurrence of x evaluates to v₁,
and then the result of the application is v₂.

\begin{code}
Δ : ∅ ⊢ ★
Δ = (ƛ (# 0) · (# 0))

denot-Δ : ∀ {v₁ v₂} → `∅ ⊢ Δ ↓ ((v₁ ↦ v₂ ⊔ v₁) ↦ v₂)
denot-Δ {v₁}{v₂} = ↦-intro (↦-elim (sub var (ConjR1⊑ Refl⊑))
                                   (sub var (ConjR2⊑ Refl⊑)))
\end{code}

One might worry whether this semantics can deal with diverging
programs.  The ⊥ value and the (⊥-intro) rule provide a way to handle
them. (The (⊥-intro) rule is also what enables β reduction on
non-terminating arguments.)  The classic Ω program is a particularly
simple program that diverges. It applies Δ to itself. The semantics
assigns to Ω the meaning ⊥. There are several ways to derive this, we
shall start with one that makes use of the (⊔-intro) rule.  First,
denot-Δ tells us that Δ evaluates to ((⊥ ↦ ⊥) ⊔ ⊥) ↦ ⊥ (choose v₁ = v₂
= ⊥).  Next, Δ also evaluates to ⊥ ↦ ⊥ by use of (↦-intro) and
(⊥-intro) and to ⊥ by (⊥-intro). As we saw previously, whenever we can
show that a program evaluates to two values, we can apply (⊔-intro) to
join them together, so Δ evaluates to (⊥ ↦ ⊥) ⊔ ⊥. This matches the
input of the first occurrence of Δ, so we can conclude that the result
of the application is ⊥.

\begin{code}
Ω : ∅ ⊢ ★
Ω = Δ · Δ

denot-Ω : `∅ ⊢ Ω ↓ ⊥
denot-Ω = ↦-elim denot-Δ (⊔-intro (↦-intro ⊥-intro) ⊥-intro) 
\end{code}

A shorter derivation of the same result is by just one use of the
(⊥-intro) rule.

\begin{code}
denot-Ω' : `∅ ⊢ Ω ↓ ⊥
denot-Ω' = ⊥-intro
\end{code}

Just because one can derive `∅ ⊢ M ↓ ⊥ for some closed term M doesn't mean
that M necessarily diverges. There may be other derivations that
conclude with M producing some more informative value.  However, if
the only thing that a term evaluates to is ⊥, then it indeed it
diverges.

An attentive reader may have noticed a disconnect earlier in the way
we planned to solve the self-application problem and the actual
(↦-elim) rule for application. We said at the beginning that we would
relax the notion of table lookup, allowing an argument to match an
input entry if the argument is equal or greater than the input entry.
Instead, the (↦-elim) rule seems to require an exact match.  However,
because of the (sub) rule, application really does allow larger
arguments.

\begin{code}
↦-elim2 : ∀ {Γ} {γ : Env Γ} {M₁ M₂ v₁ v₂ v₃}
        → γ ⊢ M₁ ↓ (v₁ ↦ v₃)
        → γ ⊢ M₂ ↓ v₂
        → v₁ ⊑ v₂
          ------------------
        → γ ⊢ (M₁ · M₂) ↓ v₃
↦-elim2 d₁ d₂ lt = ↦-elim d₁ (sub d₂ lt)
\end{code}


## Denotations and denotational equality

Next we define a notion of denotational equality based on the above
semantics. Its statement makes use of an if-and-only-if, which we
define as follows.

\begin{code}
_iff_ : Set → Set → Set
P iff Q = (P → Q) × (Q → P)
\end{code}

Another way to view the denotational semantics is as a function that
maps a term to a relation from environments to values.  That is, the
_denotation_ of a term is a relation from environments to values.

\begin{code}
Denotation : Context → Set₁
Denotation Γ = (Env Γ → Value → Set)
\end{code}

The following function ℰ gives this alternative view of the semantics,
which really just amounts to changing the order of the parameters.

\begin{code}
ℰ : ∀{Γ} → (M : Γ ⊢ ★) → Denotation Γ
ℰ M = λ γ v → γ ⊢ M ↓ v
\end{code}

In general, two denotations are equal when they produce the same
values in the same environment.

\begin{code}
infix 3 _≃_

_≃_ : ∀ {Γ} → (Denotation Γ) → (Denotation Γ) → Set
D₁ ≃ D₂ = ∀ {γ} {v} → D₁ γ v iff D₂ γ v
\end{code}

Denotational equality is an equivalence relation.

\begin{code}
≃-refl : ∀ {Γ : Context} → {M : Denotation Γ}
  → M ≃ M
≃-refl = ⟨ (λ x → x) , (λ x → x) ⟩

≃-sym : ∀ {Γ : Context} → {M N : Denotation Γ}
  → M ≃ N
    -----
  → N ≃ M
≃-sym eq = ⟨ proj₂ eq , proj₁ eq ⟩

≃-trans : ∀ {Γ : Context} → {M₁ M₂ M₃ : Denotation Γ}
  → M₁ ≃ M₂
  → M₂ ≃ M₃
    -------
  → M₁ ≃ M₃
≃-trans eq1 eq2 =
  ⟨ (λ z → proj₁ eq2 (proj₁ eq1 z)) , (λ z → proj₂ eq1 (proj₂ eq2 z)) ⟩
\end{code}

Two terms M and N are denotational equal when their denotations are
equal, that is, ℰ M ≃ ℰ N.

The rest of this chapter proves two properties of the denotational
semantics. First, we prove that the semantics is compositional, i.e.,
that the denotation of a term is a function of the denotations of its
subterms. To do this we shall prove equations of the following shape.

    ℰ (ƛ M) ≃ ... ℰ M ...
    ℰ (M · N) ≃ ... ℰ M ... ℰ N ...

The compositionality property is not trivial because the
semantics we have defined includes three rules that are not syntax
directed: ⊥-intro, ⊔-intro, and sub.

The second property we prove about the denotational semantics is that
reduction implies denotational equality.

The proofs of both of these properties relies on some basic results
about renaming, which are quite similar to the renaming lemmas that we
have seen in previous chapters.


## Renaming preserves denotations

We shall prove that renaming variables, and changing the environment
accordingly, preserves the meaning of a term. We generalize the
renaming lemma to allow the values in the new environment to be the
same or larger than the original values. This generalization is useful
in proving that reduction implies denotational equality.

As before, we need an extension lemma to handle the case where we
proceed underneath a lambda abstraction. Here, the nth function
performs lookup in the environment, analogous to Γ ∋ A.  Now suppose
that ρ is a renaming that maps variables in γ into variables with
equal or larger values in δ. This lemmas says that extending the
renaming producing a renaming (ext r) that maps (γ , v) to (δ , v).

\begin{code}
Rename : Context → Context → Set
Rename Γ Δ = ∀{A} → Γ ∋ A → Δ ∋ A
\end{code}


\begin{code}
ext-nth : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ}
  → (ρ : Rename Γ Δ)
  → γ `⊑ (δ ∘ ρ)
    ------------------------------
  → (γ `, v) `⊑ ((δ `, v) ∘ ext ρ)
ext-nth ρ lt Z = Refl⊑
ext-nth ρ lt (S x) = lt x
\end{code}

We proceed by cases on the de Bruijn index n.

* If it is Z, then we just need to show that v ≡ v, which we have by refl.

* If it is S n', then the goal simplifies to nth n' γ ≡ nth (ρ n') δ,
  which is an instance of the premise.

Now for the renaming lemma. Suppose we have a renaming that maps
variables in γ into variables with the same values in δ.  If M
results in v when evaluated in environment γ, then applying the
renaming to M produces a program that results in the same value v when
evaluated in δ.

\begin{code}
rename-pres : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} {M : Γ ⊢ ★}
  → (ρ : Rename Γ Δ)
  → γ `⊑ (δ ∘ ρ)
  → γ ⊢ M ↓ v
    ---------------------
  → δ ⊢ (rename ρ M) ↓ v
rename-pres ρ lt (var {x = x}) = sub var (lt x)
rename-pres ρ lt (↦-elim d d₁) =
   ↦-elim (rename-pres ρ lt d) (rename-pres ρ lt d₁) 
rename-pres ρ lt (↦-intro d) =
   ↦-intro (rename-pres (ext ρ) (ext-nth ρ lt) d)
rename-pres ρ lt ⊥-intro = ⊥-intro
rename-pres ρ lt (⊔-intro d d₁) =
   ⊔-intro (rename-pres ρ lt d) (rename-pres ρ lt d₁)
rename-pres ρ lt (sub d lt′) =
   sub (rename-pres ρ lt d) lt′
\end{code}

The proof is by induction on the semantics of M.  As you can see, all
of the cases are trivial except the cases for variables and lambda.

* For a variable x, we make use of the premise to
  show that nth x γ ≡ nth (ρ x) δ.

* For a lambda abstraction, the induction hypothesis requires us to
  extend the renaming. We do so, and use the ext-nth lemma to show
  that the extended renaming maps variables to ones with equivalent
  values.


## Identity renamings and environment strengthening

We shall need a corollary of the renaming lemma that says that if M
results in v, then we can replace a value in the environment with a
larger one (a stronger one), and M still results in v. In particular,
if γ ⊢ M ↓ v and γ `⊑ δ, then δ ⊢ M ↓ v.  What does this have to do
with renaming?  It's renaming with the identity function.

The next lemma shows that renaming with an identity function is indeed
an identity function on terms. In the case of lambda abstraction, the
identity function gets extended, becoming another identity function,
but not the same one (Agda lacks extensionality).  To work around this
issue, we parameterize the proof over any function that is an
identity.

\begin{code}
is-identity : ∀ {Γ} (id : ∀{A} → Γ ∋ A → Γ ∋ A) → Set
is-identity {Γ} id = (∀ {x : Γ ∋ ★} → id {★} x ≡ x)
\end{code}

\begin{code}
rename-id : ∀ {Γ} {M : Γ ⊢ ★} {id : ∀{A} → Γ ∋ A → Γ ∋ A}
  → is-identity id
    ---------------
  → rename id M ≡ M
rename-id {M = ` x} eq = cong `_ (eq {x})
rename-id {M = ƛ M₁}{id = id} eq = cong ƛ_ (rename-id {M = M₁} ext-id)
  where
  ext-id : is-identity (ext id)
  ext-id {Z} = refl
  ext-id {S x} = cong S_ eq
rename-id {M = M · M₁} eq = cong₂ _·_ (rename-id eq) (rename-id eq)
\end{code}

The identity function on variables, var-id, is an identity function.

\begin{code}
var-id : ∀ {Γ A} → (Γ ∋ A) → (Γ ∋ A)
var-id {A} x = x

var-id-id : ∀ {Γ} → is-identity {Γ} var-id
var-id-id = refl
\end{code}

We can now prove environment strengthening by applying the renaming
lemma with the identity renaming, which gives us δ ⊢ rename var-id M ↓
v, and then we apply the rename-id lemma to obtain δ ⊢ M ↓ v.

\begin{code}
Env⊑ : ∀ {Γ} {γ : Env Γ} {δ : Env Γ} {M v}
  → γ ⊢ M ↓ v
  → γ `⊑ δ
    ----------
  → δ ⊢ M ↓ v
Env⊑{Γ}{γ}{δ}{M}{v} d lt
      with rename-pres var-id lt d
... | d' rewrite rename-id {Γ}{M}{var-id} (var-id-id {Γ}) = d'
\end{code}

In the proof that substitution reflects denotations, in the case for
lambda abstraction, we use a minor variation of Env⊑, in which just
the last element of the environment gets larger.

\begin{code}
up-env : ∀ {Γ} {γ : Env Γ} {M v u₁ u₂}
  → (γ `, u₁) ⊢ M ↓ v
  → u₁ ⊑ u₂
    -----------------
  → (γ `, u₂) ⊢ M ↓ v
up-env d lt = Env⊑ d (nth-le lt)
  where
  nth-le : ∀ {γ u₁ u₂} → u₁ ⊑ u₂ → (γ `, u₁) `⊑ (γ `, u₂)
  nth-le lt Z = lt
  nth-le lt (S n) = Refl⊑
\end{code}


## Compositionality and inversion lemmas 


As mentioned above, we want to fill in the ellipses in the following
equations to show that the semantics is compositional.

    ℰ (ƛ M) ≃ ... ℰ M ...
    ℰ (M · N) ≃ ... ℰ M ... ℰ N ...

Regarding the first equation, we need a function that maps a
Denotation (Γ , ★) to a Denotation Γ. This function, let us name it ℱ,
needs to mimic the non-recursive part of the semantics when applied to
a lambda term.  In particular, we need to consider the rules
(↦-intro), (⊥-intro), and (⊔-intro). So ℱ has three parameters, the
denotation D of the subterm M, an environment γ, and a value v.  If we
define ℱ by recursion on the value v, then it will match up nicely
with the three rules (↦-intro), (⊥-intro), and (⊔-intro).

\begin{code}
ℱ : ∀{Γ} → Denotation (Γ , ★) → Denotation Γ
ℱ D γ (v₁ ↦ v₂) = D (γ `, v₁) v₂
ℱ D γ ⊥ = ⊤
ℱ D γ (v₁ ⊔ v₂) = (ℱ D γ v₁) × (ℱ D γ v₂)
\end{code}

Using this ℱ, we hope to prove that

    ℰ (ƛ M) ≃ ℱ (ℰ M)

The function ℱ is preserved when going from a larger value v to a
smaller value v'. The proof is a straightforward induction on the
derivation of v' ⊑ v, using the up-env lemma in the case for the
(Fun⊑) rule.

\begin{code}
sub-ℱ : ∀{Γ}{M : Γ , ★ ⊢ ★}{γ v v'}
      → ℱ (ℰ M) γ v
      → v' ⊑ v
        ------------
      → ℱ (ℰ M) γ v'
sub-ℱ d Bot⊑ = tt
sub-ℱ d (Fun⊑ lt lt') = sub (up-env d lt) lt'
sub-ℱ d (ConjL⊑ lt lt₁) = ⟨ sub-ℱ d lt , sub-ℱ d lt₁ ⟩
sub-ℱ d (ConjR1⊑ lt) = sub-ℱ (proj₁ d) lt
sub-ℱ d (ConjR2⊑ lt) = sub-ℱ (proj₂ d) lt
sub-ℱ {v = v₁ ↦ v₂ ⊔ v₁ ↦ v₃} {v₁ ↦ (v₂ ⊔ v₃)} ⟨ M2 , M3 ⟩ Dist⊑ =
   ⊔-intro M2 M3
sub-ℱ d (Trans⊑ x₁ x₂) = sub-ℱ (sub-ℱ d x₂) x₁
\end{code}

[PLW:
  If denotations were strengthened to be downward closed,
  we could rewrite the signature replacing (ℰ M) by d : Denotation (Γ , ★)]
  
With this subsumption property in hand, we can prove the forward
direction of the semantic equation for lambda.  The proof is by
induction on the semantics, using sub-ℱ in the case for the (sub)
rule.

\begin{code}
ℰƛ→ℱℰ : ∀{Γ}{γ : Env Γ}{M : Γ , ★ ⊢ ★}{v : Value}
        → ℰ (ƛ M) γ v
          ------------
        → ℱ (ℰ M) γ v
ℰƛ→ℱℰ (↦-intro d) = d
ℰƛ→ℱℰ ⊥-intro = tt
ℰƛ→ℱℰ (⊔-intro d₁ d₂) = ⟨ ℰƛ→ℱℰ d₁ , ℰƛ→ℱℰ d₂ ⟩
ℰƛ→ℱℰ (sub d lt) = sub-ℱ (ℰƛ→ℱℰ d) lt
\end{code}

The "inversion lemma" for lambda abstraction is a special case of the
above. The inversion lemma is useful in proving that denotations are
preserved by reduction.

\begin{code}
lambda-inversion : ∀{Γ}{γ : Env Γ}{M : Γ , ★ ⊢ ★}{v₁ v₂ : Value}
  → γ ⊢ ƛ M ↓ v₁ ↦ v₂
    -----------------
  → (γ `, v₁) ⊢ M ↓ v₂
lambda-inversion{v₁ = v₁}{v₂ = v₂} d = ℰƛ→ℱℰ{v = v₁ ↦ v₂} d
\end{code}

The backward direction of the semantic equation for lambda is even
easier to prove than the forward direction. We proceed by induction on
the value v.

\begin{code}
ℱℰ→ℰƛ : ∀{Γ}{γ : Env Γ}{M : Γ , ★ ⊢ ★}{v : Value}
        → ℱ (ℰ M) γ v
          ------------
        → ℰ (ƛ M) γ v
ℱℰ→ℰƛ {v = ⊥} d = ⊥-intro
ℱℰ→ℰƛ {v = v₁ ↦ v₂} d = ↦-intro d
ℱℰ→ℰƛ {v = v₁ ⊔ v₂} ⟨ d1 , d2 ⟩ = ⊔-intro (ℱℰ→ℰƛ d1) (ℱℰ→ℰƛ d2)
\end{code}

So indeed, the denotational semantics is composititional with respect
to lambda abstraction, as witnessed by the function ℱ.

\begin{code}
lam-equiv : ∀{Γ}{γ : Env Γ}{M : Γ , ★ ⊢ ★}
          → ℰ (ƛ M) ≃ ℱ (ℰ M)
lam-equiv = ⟨ ℰƛ→ℱℰ , ℱℰ→ℰƛ ⟩
\end{code}

Next we consider function application. For this we need to define a
function that takes two denotations, both in context Γ, and produces
another one in context Γ. This function, let us name it ●, needs to
mimic the non-recursive aspects of the semantics of an application (M · N).
We cannot proceed as easily as for ℱ and define the function by
recursion on value v because, for example, the rule (↦-elim) applies
to any value. Instead we shall define ● in a way that directly deals
with the (↦-elim) and (⊥-intro) rules but ignores (⊔-intro). This
makes the forward direction of the proof more difficult, and the case
for (⊔-intro) demonstrates why the (Dist⊑) rule is important.

So we define the application of D₁ to D₂, written D₁ ● D₂, to include
any value v' equivalent to ⊥, for the (⊥-intro) rule, and to include any
value v' that is the output of an entry v ↦ v' in D₁, provided the
input v is in D₂, for the (↦-elim) rule.

\begin{code}
infixl 7 _●_

_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ
(D₁ ● D₂) γ v' = v' ⊑ ⊥ ⊎ Σ[ v ∈ Value ]( D₁ γ (v ↦ v') × D₂ γ v )
\end{code}

Next we consider the inversion lemma for application, which is also
the forward direction of the semantic equation for application.  We
describe the proof below.

\begin{code}
ℰ·→●ℰ : ∀{Γ}{γ : Env Γ}{M N : Γ ⊢ ★}{v : Value}
        → ℰ (M · N) γ v
          ----------------
        → (ℰ M ● ℰ N) γ v
ℰ·→●ℰ (↦-elim{v₁ = v₁} d₁ d₂) = inj₂ ⟨ v₁ , ⟨ d₁ , d₂ ⟩ ⟩
ℰ·→●ℰ {v = ⊥} (⊥-intro) = inj₁ Bot⊑
ℰ·→●ℰ {Γ}{γ}{M}{N}{v} (⊔-intro{v₁ = v₁}{v₂ = v₂} d₁ d₂) 
    with ℰ·→●ℰ d₁ | ℰ·→●ℰ d₂
... | inj₁ lt1 | inj₁ lt2 = inj₁ (ConjL⊑ lt1 lt2)    
... | inj₁ lt1 | inj₂ ⟨ v₁' , ⟨ M↓v12 , N↓v3 ⟩ ⟩ =
      inj₂ ⟨ v₁' , ⟨ sub M↓v12 lt , N↓v3 ⟩ ⟩
      where lt : v₁' ↦ (v₁ ⊔ v₂) ⊑ v₁' ↦ v₂
            lt = (Fun⊑ Refl⊑ (ConjL⊑ (Trans⊑ lt1 Bot⊑) Refl⊑))
... | inj₂ ⟨ v₁' , ⟨ M↓v12 , N↓v3 ⟩ ⟩ | inj₁ lt2 =
      inj₂ ⟨ v₁' , ⟨ sub M↓v12 lt , N↓v3 ⟩ ⟩
      where lt : v₁' ↦ (v₁ ⊔ v₂) ⊑ v₁' ↦ v₁
            lt = (Fun⊑ Refl⊑ (ConjL⊑ Refl⊑ (Trans⊑ lt2 Bot⊑)))
... | inj₂ ⟨ v₁' , ⟨ M↓v12 , N↓v3 ⟩ ⟩ | inj₂ ⟨ v₁'' , ⟨ M↓v12' , N↓v3' ⟩ ⟩ =
      let M↓⊔ = ⊔-intro M↓v12 M↓v12' in
      let N↓⊔ = ⊔-intro N↓v3 N↓v3' in
      let x = inj₂ ⟨ v₁' ⊔ v₁'' , ⟨ sub M↓⊔ Dist⊔↦⊔ , N↓⊔ ⟩ ⟩ in
      x
ℰ·→●ℰ {Γ}{γ}{M}{N}{v} (sub d lt)
    with ℰ·→●ℰ d
... | inj₁ lt2 = inj₁ (Trans⊑ lt lt2)
... | inj₂ ⟨ v₁ , ⟨ M↓v12 , N↓v3 ⟩ ⟩ =
      inj₂ ⟨ v₁ , ⟨ sub M↓v12 (Fun⊑ Refl⊑ lt) , N↓v3 ⟩ ⟩
\end{code}

We proceed by induction on the semantics.

* In case (↦-elim) we have γ ⊢ M₁ ↓ (v₁ ↦ v₂) and γ ⊢ M₂ ↓ v₁,
  which is all we need to show (ℰ M ● ℰ N) γ v₂.

* In case (⊥-intro) we have v = ⊥. We conclude that v ⊑ ⊥.

* In case (⊔-intro) we have ℰ (M · N) γ v₁ and ℰ (M · N) γ v₂
  and need to show (ℰ M ● ℰ N) γ (v₁ ⊔ v₂). By the induction
  hypothesis, we have (ℰ M ● ℰ N) γ v₁ and (ℰ M ● ℰ N) γ v₂.
  We have four subcases to consider.

    * Suppose v₁ ⊑ ⊥ and v₂ ⊑ ⊥. Then v₁ ⊔ v₂ ⊑ ⊥.
    * Suppose v₁ ⊑ ⊥, γ ⊢ M ↓ v₁' ↦ v₂, and γ ⊢ N ↓ v₁'.
      We have γ ⊢ M ↓ v₁' ↦ (v₁ ⊔ v₂) by rule (sub)
      because v₁' ↦ (v₁ ⊔ v₂) ⊑ v₁' ↦ v₂.
    * Suppose γ ⊢ M ↓ v₁' ↦ v₁, γ ⊢ N ↓ v₁', and v₂ ⊑ ⊥.
      We have γ ⊢ M ↓ v₁' ↦ (v₁ ⊔ v₂) by rule (sub)
      because v₁' ↦ (v₁ ⊔ v₂) ⊑ v₁' ↦ v₁.
    * Suppose γ ⊢ M ↓ v₁'' ↦ v₁, γ ⊢ N ↓ v₁'',
      γ ⊢ M ↓ v₁' ↦ v₂, and γ ⊢ N ↓ v₁'.
      This case is the most interesting.
      By two uses of the rule (⊔-intro) we have
      γ ⊢ M ↓ (v₁' ↦ v₂) ⊔ (v₁'' ↦ v₁) and
      γ ⊢ N ↓ (v₁' ⊔ v₁''). But this does not yet match
      what we need for (ℰ M ● ℰ N) because the result of
      M must be an ↦ whose input entry is v₁' ⊔ v₁''.
      So we use the (sub) rule to obtain 
      γ ⊢ M ↓ (v₁' ⊔ v₁'') ↦ (v₁ ⊔ v₂),
      using the Dist⊔→⊔ lemma (thanks to the Dist⊑ rule) to
      show that
   
            (v₁' ⊔ v₁'') ↦ (v₁ ⊔ v₂) ⊑ (v₁' ↦ v₂) ⊔ (v₁'' ↦ v₁)
   
      So we have proved what is needed for this case.

* In case (sub) we have Γ ⊢ M · N ↓ v₁ and v ⊑ v₁.
  By the induction hypothesis, we have (ℰ M ● ℰ N) γ v₁.
  We have two subcases to consider.

    * Suppose v₁ ⊑ ⊥. We conclude that v ⊑ ⊥.
    * Suppose Γ ⊢ M ↓ v' → v₁ and Γ ⊢ N ↓ v'.
      We conclude with Γ ⊢ M ↓ v' → v by rule (sub), because
      v' → v ⊑ v' → v₁. 


The foward direction is proved by cases on the premise (ℰ M ● ℰ N) γ v.
In case v ⊑ ⊥, we obtain Γ ⊢ M · N ↓ ⊥ by rule (⊥-intro).
Otherwise, we conclude immediately by rule (↦-elim).

\begin{code}
●ℰ→ℰ· : ∀{Γ}{γ : Env Γ}{M N : Γ ⊢ ★}{v}
      → (ℰ M ● ℰ N) γ v
        ----------------
      → ℰ (M · N) γ v
●ℰ→ℰ· {γ}{v} (inj₁ lt) = sub ⊥-intro lt
●ℰ→ℰ· {γ}{v} (inj₂ ⟨ v₁ , ⟨ d1 , d2 ⟩ ⟩) = ↦-elim d1 d2
\end{code}

So we have proved that the semantics is compositional with respect to
function application, as witnessed by the ● function.

\begin{code}
app-equiv : ∀{Γ}{γ : Env Γ}{M N : Γ ⊢ ★}
          → ℰ (M · N) ≃ (ℰ M) ● (ℰ N)
app-equiv = ⟨ ℰ·→●ℰ , ●ℰ→ℰ· ⟩
\end{code}

We also need an inversion lemma for variables.
If Γ ⊢ ` x ↓ v, then v ⊑ nth x γ. The proof is a straightforward
induction on the semantics.

\begin{code}
var-inv : ∀ {Γ v x} {γ : Env Γ}
  → ℰ (` x) γ v
    -------------------
  → v ⊑ γ x
var-inv (var) = Refl⊑
var-inv (⊔-intro d₁ d₂) = ConjL⊑ (var-inv d₁) (var-inv d₂)
var-inv (sub d lt) = Trans⊑ lt (var-inv d)
var-inv ⊥-intro = Bot⊑
\end{code}

To round-out the semantic equations, we establish the following one
for variables.

\begin{code}
var-equiv : ∀{Γ}{γ : Env Γ}{x : Γ ∋ ★}
          → ℰ (` x) ≃ (λ γ v → v ⊑ nth x γ)
var-equiv = ⟨ var-inv , (λ lt → sub var lt) ⟩
\end{code}


## Reduction implies denotational equality

We prove that if a term M reduces to N, then M and N are
denotationally equal. We shall prove each direction of the
if-and-only-if separately. One direction will look just like a type
preservation proof. The other direction is like proving type
preservation for reduction going in reverse.

[PLW:
  "type preservation for reduction going in reverse"
  is a well-known property called _subject expansion_.
  It is also well-known that subject expansion is
  false for most typed lambda calculi!]


### Forward reduction preserves denotations

The proof of preservation in this section mixes techniques from
previous chapters. Like the proof of preservation for the STLC, we are
preserving a relation defined separately from the syntax, in contrast
to the inherently typed terms. On the other hand, we are using de
Bruijn indices for variables.

The outline of the proof remains the same in that we must prove lemmas
concerning all of the auxiliary functions used in the reduction
relation: substitution, renaming, and extension.


#### Simultaneous substitution preserves denotations

We introduce the following shorthand for the type of a substitution
from variables in context Γ to terms in context Δ.

\begin{code}
Subst : Context → Context → Set
Subst Γ Δ = ∀{A} → Γ ∋ A → Δ ⊢ A
\end{code}

Our next goal is to prove that simultaneous substitution preserves
meaning.  That is, if M results in v in environment γ, then applying a
substitution σ to M gives us a program that also results in v, but in
an environment δ in which, for every variable x, σ x results in the
same value as the one for x in the original environment γ.
We write δ `⊢ σ ↓ γ for this condition.

\begin{code}
_`⊢_↓_ : ∀{Δ Γ} → Env Δ → Subst Γ Δ → Env Γ → Set
_`⊢_↓_ {Δ}{Γ} δ σ γ = (∀ (x : Γ ∋ ★) → δ ⊢ σ x ↓ γ x)
\end{code}

As usual, to prepare for lambda abstraction, we prove an extension
lemma. It says that applying the exts function to a substitution
produces a new substitution that maps variables to terms that when
evaluated in (δ , v) produce the values in (γ , v).

\begin{code}
subst-ext : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ}
  → (σ : Subst Γ Δ)
  → δ `⊢ σ ↓ γ
   ------------------------------
  → (δ `, v) `⊢ exts σ ↓ (γ `, v)
subst-ext σ d Z = var
subst-ext σ d (S x) = rename-pres S_ (λ _ → Refl⊑) (d x)
\end{code}

The proof is by cases on the de Bruijn index x.

* If it is Z, then we need to show that δ , v ⊢ # 0 ↓ v,
  which we have by rule (var).

* If it is S x',then we need to show that 
  (δ , v) ⊢ rename S_ (σ x') ↓ nth x' γ,
  which we obtain by the renaming lemma.

With the extension lemma in hand, the proof that simultaneous
substitution preserves meaning is straightforward.  Let's dive in!

\begin{code}
subst-pres : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} {M : Γ ⊢ ★}
  → (σ : Subst Γ Δ)
  → δ `⊢ σ ↓ γ
  → γ ⊢ M ↓ v
    ------------------
  → δ ⊢ subst σ M ↓ v
subst-pres σ s (var {x = x}) = (s x)
subst-pres σ s (↦-elim d₁ d₂) =
  ↦-elim (subst-pres σ s d₁) (subst-pres σ s d₂) 
subst-pres σ s (↦-intro d) =
  ↦-intro (subst-pres (λ {A} → exts σ) (subst-ext σ s) d)
subst-pres σ s ⊥-intro = ⊥-intro
subst-pres σ s (⊔-intro d₁ d₂) =
  ⊔-intro (subst-pres σ s d₁) (subst-pres σ s d₂)
subst-pres σ s (sub d lt) = sub (subst-pres σ s d) lt
\end{code}

The proof is by induction on the semantics of M.  The two interesting
cases are for variables and lambda abstractions.

* For a variable x, we have that v ⊑ nth x γ and we need to show that
  δ ⊢ σ x ↓ v.  From the premise applied to x, we have that
  δ ⊢ σ x ↓ nth x γ, so we conclude by the (sub) rule.

* For a lambda abstraction, we must extend the substitution
  for the induction hypothesis. We apply the extension lemma
  to show that the extended substitution maps variables to
  terms that result in the appropriate values.


#### Single substitution preserves denotations

For β reduction, (ƛ M) · N —→ M [ N ], we need to show that the
semantics is preserved when substituting N for de Bruijn index 0 in
term M. By inversion on the rules (↦-elim) and (↦-intro),
we have that γ , v₁ ⊢ M ↓ v₂ and γ ⊢ N ↓ v₁.
So we need to show that γ ⊢ M [ N ] ↓ v₂, or equivalently,
that γ ⊢ subst (subst-zero N) M ↓ v₂.

\begin{code}
substitution : ∀ {Γ} {γ : Env Γ} {M N v₁ v₂}
   → γ `, v₁ ⊢ M ↓ v₂
   → γ ⊢ N ↓ v₁
     -----------------
   → γ ⊢ M [ N ] ↓ v₂   
substitution{Γ}{γ}{M}{N}{v₁}{v₂} dm dn =
  subst-pres (subst-zero N) sub-z-ok dm
  where
  sub-z-ok : γ `⊢ subst-zero N ↓ (γ `, v₁)
  sub-z-ok Z = dn
  sub-z-ok (S x) = var
\end{code}

This result is a corollary of the lemma for simultaneous substitution.
To use the lemma, we just need to show that (subst-zero N) maps
variables to terms that produces the same values as those in γ , v₁.
Let y be an arbitrary variable (de Bruijn index).

* If it is Z, then (subst-zero N) y = N and nth y (γ , v₁) = v₁.
  By the premise we conclude that γ ⊢ N ↓ v₁.

* If it is (S y'), then (subst-zero N) (S y') = y' and
  nth (S y') (γ , v₁) = nth y' γ.  So we conclude that
  γ ⊢ y' ↓ nth y' γ by rule (var).


#### Reduction preserves denotations

With the substitution lemma in hand, it is straightforward to prove
that reduction preserves denotations.

\begin{code}
preserve : ∀ {Γ} {γ : Env Γ} {M N v}
  → γ ⊢ M ↓ v
  → M —→ N
    ----------
  → γ ⊢ N ↓ v
preserve (var) ()
preserve (↦-elim d₁ d₂) (ξ₁ x r) = ↦-elim (preserve d₁ r) d₂ 
preserve (↦-elim d₁ d₂) (ξ₂ x r) = ↦-elim d₁ (preserve d₂ r) 
preserve (↦-elim d₁ d₂) β = substitution (lambda-inversion d₁) d₂
preserve (↦-intro d) (ζ r) = ↦-intro (preserve d r)
preserve ⊥-intro r = ⊥-intro
preserve (⊔-intro d d₁) r = ⊔-intro (preserve d r) (preserve d₁ r)
preserve (sub d lt) r = sub (preserve d r) lt
\end{code}

We proceed by induction on the semantics of M with case analysis on
the reduction.

* If M is a variable, then there is no such reduction.

* If M is an application, then the reduction is either a congruence
  (ξ₁ or ξ₂) or β. For each congruence, we use the induction
  hypothesis. For β reduction we use the substitution lemma and the
  (sub) rule.

* The rest of the cases are straightforward.

### Reduction reflects denotations

This section proves that reduction reflects the denotation of a
term. That is, if N results in v, and if M reduces to N, then M also
results in v. While there are some broad similarities between this
proof and the above proof of semantic preservation, we shall require a
few more technical lemmas to obtain this result.

The main challenge is dealing with the substitution in β reduction:

    (ƛ M₁) · M₂ —→ M₁ [ M₂ ]

We have that γ ⊢ M₁ [ M₂ ] ↓ v and need to show that γ ⊢ (ƛ M₁) · M₂ ↓
v. Now consider the derivation of γ ⊢ M₁ [ M₂ ] ↓ v. The term M₂ may
occur 0, 1, or many times inside M₁ [ M₂ ]. At each of those
occurences, M₂ may result in a different value. But to build a
derivation for (ƛ M₁) · M₂, we need a single value for M₂.  If M₂
occured more than 1 time, then we can join all of the different values
using ⊔. If M₂ occured 0 times, then we can use ⊥ for the value of M₂.


#### Renaming reflects meaning

Previously we showed that renaming variables preserves meaning.  Now
we prove the opposite, that it reflects meaning. That is,
if δ ⊢ rename ρ M ↓ v, then γ ⊢ M ↓ v, where (δ ∘ ρ) `⊑ γ.

First, we need a variant of a lemma given earlier.
\begin{code}
nth-ext : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ}
  → (ρ : Rename Γ Δ)
  → (δ ∘ ρ) `⊑ γ
    ------------------------------
  → ((δ `, v) ∘ ext ρ) `⊑ (γ `, v)
nth-ext ρ lt Z = Refl⊑
nth-ext ρ lt (S x) = lt x
\end{code}

The proof is then as follows.
\begin{code}
rename-reflect : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} { M : Γ ⊢ ★}
  → {ρ : Rename Γ Δ}
  → (δ ∘ ρ) `⊑ γ
  → δ ⊢ rename ρ M ↓ v
    ------------------------------------
  → γ ⊢ M ↓ v
rename-reflect {M = ` x} all-n d with var-inv d
... | lt =  sub var (Trans⊑ lt (all-n x))
rename-reflect {Γ}{Δ}{v₁ ↦ v₂}{γ}{δ}{ƛ M'}{ρ} all-n (↦-intro d) =
   ↦-intro (rename-reflect (nth-ext ρ all-n) d)
rename-reflect {M = ƛ M'} all-n ⊥-intro = ⊥-intro
rename-reflect {M = ƛ M'} all-n (⊔-intro d₁ d₂) =
   ⊔-intro (rename-reflect all-n d₁) (rename-reflect all-n d₂)
rename-reflect {M = ƛ M'} all-n (sub d₁ lt) =   -- [PLW: why is this line in gray?]
   sub (rename-reflect all-n d₁) lt
rename-reflect {M = M₁ · M₂} all-n (↦-elim d₁ d₂) =
   ↦-elim (rename-reflect all-n d₁) (rename-reflect all-n d₂) 
rename-reflect {M = M₁ · M₂} all-n ⊥-intro = ⊥-intro
rename-reflect {M = M₁ · M₂} all-n (⊔-intro d₁ d₂) =
   ⊔-intro (rename-reflect all-n d₁) (rename-reflect all-n d₂)
rename-reflect {M = M₁ · M₂} all-n (sub d₁ lt) =
   sub (rename-reflect all-n d₁) lt
\end{code}

We cannot prove this lemma by induction on the derivation of
δ ⊢ rename ρ M ↓ v, so instead we proceed by induction on M.

* If it is a variable, we apply the inversion lemma to obtain
  that v ⊑ nth (ρ x) δ. Instantiating the premise to x we have
  nth (ρ x) δ = nth x γ, so we conclude by the (var) rule.

* If it is a lambda abstraction ƛ M', we have
  rename ρ (ƛ M') = ƛ (rename (ext ρ) M').
  We proceed by cases on δ ⊢ ƛ (rename (ext ρ) M') ↓ v.

  * Rule (↦-intro): To satisfy the premise of the induction
    hypothesis, we prove that the renaming can be extended to be a
    mapping from γ , v₁ to δ , v₁.

  * Rule (⊥-intro): We simply apply (⊥-intro).

  * Rule (⊔-intro): We apply the induction hypotheses and (⊔-intro).

  * Rule (sub): [PLW: this case is also in the code!]

* If it is an application M₁ · M₂, we have
  rename ρ (M₁ · M₂) = (rename ρ M₁) · (rename ρ M₂).
  We proceed by cases on δ ⊢ (rename ρ M₁) · (rename ρ M₂) ↓ v
  and all the cases are straightforward.

In the upcoming uses of rename-reflect, the renaming will always be
the increment function. So we prove a corollary for that special case.

\begin{code}
rename-inc-reflect : ∀ {Γ v' v} {γ : Env Γ} { M : Γ ⊢ ★}
  → (γ `, v') ⊢ rename S_ M ↓ v
    ----------------------------
  → γ ⊢ M ↓ v
rename-inc-reflect d = rename-reflect `Refl⊑ d
\end{code}


#### Substitution reflects denotations, the variable case

We are almost ready to begin proving that simultaneous substitution
reflects denotations. That is, if γ ⊢ (subst σ M) ↓ v, then γ ⊢ σ k ↓
nth k δ and δ ⊢ M ↓ v for any k and some δ.  We shall start with the
case in which M is a variable x.  So instead the premise is γ ⊢ σ x ↓
v and we need to show that δ ⊢ ` x ↓ v for some δ. The δ that we
choose shall be the environment that maps x to v and every other
variable to ⊥.

The nth element of the `⊥ environment is always ⊥.
[PLW: Probably can omit]
\begin{code}
nth-`⊥ : ∀{Γ} {x : Γ ∋ ★} → `⊥ x ≡ ⊥
nth-`⊥ {x = Z} = refl
nth-`⊥ {Γ , ★} {S x} = nth-`⊥ {Γ} {x}
\end{code}

Next we define the environment that maps x to v and every other
variable to ⊥, that is (const-env x v).

\begin{code}
{-
inv-S : ∀ {Γ A B} {x y : Γ ∋ A}
  → _≡_ {_} {Γ , B ∋ A} (S x) (S y)
  → S x ≡ S y
    -------------------------------
  → x ≡ y
inv-S refl = refl
-}

_var≟_ : ∀ {Γ} → (x y : Γ ∋ ★) → Dec (x ≡ y)
Z var≟ Z  =  yes refl
Z var≟ (S _)  =  no λ()
(S _) var≟ Z  =  no λ()
(S x) var≟ (S y) with  x var≟ y
...                 |  yes refl =  yes refl
...                 |  no neq   =  no λ{refl → neq refl}

var≟-refl : ∀ {Γ} (x : Γ ∋ ★) → (x var≟ x) ≡ yes refl
var≟-refl Z = refl
var≟-refl (S x) rewrite var≟-refl x = refl

const-env : ∀{Γ} → (x : Γ ∋ ★) → Value → Env Γ
const-env x v y with x var≟ y
...             | yes _       = v
...             | no _        = ⊥
\end{code}

Of course, the nth element of (const-env n v) is the value v.

\begin{code}
nth-const-env : ∀{Γ} {x : Γ ∋ ★} {v} → (const-env x v) x ≡ v
nth-const-env {x = x} rewrite var≟-refl x = refl
\end{code}

The nth element of (const-env n' v) is the value ⊥, so long as n ≢ n'.

\begin{code}
diff-nth-const-env : ∀{Γ} {x y : Γ ∋ ★} {v}
  → x ≢ y
    -------------------
  → const-env x v y ≡ ⊥
diff-nth-const-env {Γ} {x} {y} neq with x var≟ y
...  | yes eq  =  ⊥-elim (neq eq)
...  | no _    =  refl
\end{code}

So we choose (const-env x v) for δ and obtain δ ⊢ ` x ↓ v
with the (var) rule.

It remains to prove that γ `⊢ σ ↓ δ and δ ⊢ M ↓ v for any k, given that
we have chosen (const-env x v) for δ .  We shall have two cases to
consider, x ≡ y or x ≢ y.

Now to finish the two cases of the proof.

* In the case where x ≡ y, we need to show
  that γ ⊢ σ y ↓ v, but that's just our premise.
* In the case where x ≢ y, we need to show
  that γ ⊢ σ y ↓ ⊥, which we do via rule (⊥-intro).

Thus, we have completed the variable case of the proof that
simultaneous substitution reflects denotations.  Here is the proof
again, formally.

\begin{code}
subst-reflect-var : ∀ {Γ Δ} {γ : Env Δ} {x : Γ ∋ ★} {v} {σ : Subst Γ Δ}
  → γ ⊢ σ x ↓ v
    ----------------------------------------
  → Σ[ δ ∈ Env Γ ] γ `⊢ σ ↓ δ  ×  δ ⊢ ` x ↓ v
subst-reflect-var {Γ}{Δ}{γ}{x}{v}{σ} xv
  rewrite sym (nth-const-env {Γ}{x}{v}) =
    ⟨ const-env x v , ⟨ const-env-ok , var ⟩ ⟩
  where
  const-env-ok : γ `⊢ σ ↓ const-env x v
  const-env-ok y with x var≟ y
  ... | yes x≡y rewrite sym x≡y | nth-const-env {Γ}{x}{v} = xv
  ... | no x≢y rewrite diff-nth-const-env {Γ}{x}{y}{v} x≢y = ⊥-intro
\end{code}


#### Substitutions and environment construction

Every substitution produces terms that can evaluate to ⊥.

\begin{code}
subst-⊥ : ∀{Γ Δ}{γ : Env Δ}{σ : Subst Γ Δ}
    -----------------
  → γ `⊢ σ ↓ `⊥
subst-⊥ x = ⊥-intro
\end{code}

If a substitution produces terms that evaluate to the values in
both γ₁ and γ₂, then those terms also evaluate to the values in 
γ₁ `⊔ γ₂.

\begin{code}
subst-⊔ : ∀{Γ Δ}{γ : Env Δ}{γ₁ γ₂ : Env Γ}{σ : Subst Γ Δ}
           → γ `⊢ σ ↓ γ₁
           → γ `⊢ σ ↓ γ₂
             -------------------------
           → γ `⊢ σ ↓ (γ₁ `⊔ γ₂)
subst-⊔ γ₁-ok γ₂-ok x = ⊔-intro (γ₁-ok x) (γ₂-ok x)
\end{code}

#### The Lambda constructor is injective

\begin{code}
lambda-inj : ∀ {Γ} {M N : Γ , ★ ⊢ ★ }
  → _≡_ {A = Γ ⊢ ★} (ƛ M) (ƛ N)
    ---------------------------
  → M ≡ N
lambda-inj refl = refl
\end{code}

#### Simultaneous substitution reflects denotations

In this section we prove a central lemma, that
substitution reflects denotations. That is, if γ ⊢ subst σ M ↓ v, then
δ ⊢ M ↓ v and γ `⊢ σ ↓ δ for some δ. We shall proceed by induction on
the derivation of γ ⊢ subst σ M ↓ v. This requires a minor
restatement of the lemma, changing the premise to γ ⊢ L ↓ v and
L ≡ subst σ M.

\begin{code}
split : ∀ {Γ} {M : Γ , ★ ⊢ ★} {δ : Env (Γ , ★)} {v}
  → δ ⊢ M ↓ v
    --------------------------
  → (init δ `, last δ) ⊢ M ↓ v
split {δ = δ} δMv rewrite init-last δ = δMv

subst-reflect : ∀ {Γ Δ} {δ : Env Δ} {M : Γ ⊢ ★} {v} {L : Δ ⊢ ★} {σ : Subst Γ Δ}
  → δ ⊢ L ↓ v
  → subst σ M ≡ L
    ---------------------------------------
  → Σ[ γ ∈ Env Γ ] δ `⊢ σ ↓ γ  ×  γ ⊢ M ↓ v

subst-reflect {M = M}{σ = σ} (var {x = y}) eqL with M 
... | ` x  with var {x = y}
...           | yv  rewrite sym eqL = subst-reflect-var {σ = σ} yv
subst-reflect {M = M} (var {x = y}) () | M₁ · M₂
subst-reflect {M = M} (var {x = y}) () | ƛ M'

subst-reflect {M = M}{σ = σ} (↦-elim d₁ d₂) eqL
         with M 
...    | ` x with ↦-elim d₁ d₂ 
...    | d' rewrite sym eqL = subst-reflect-var {σ = σ} d'
subst-reflect (↦-elim d₁ d₂) () | ƛ M'
subst-reflect{Γ}{Δ}{γ}{σ = σ} (↦-elim d₁ d₂)
   refl | M₁ · M₂
     with subst-reflect {M = M₁} d₁ refl | subst-reflect {M = M₂} d₂ refl
...     | ⟨ δ₁ , ⟨ subst-δ₁ , m1 ⟩ ⟩ | ⟨ δ₂ , ⟨ subst-δ₂ , m2 ⟩ ⟩ =
     ⟨ δ₁ `⊔ δ₂ , ⟨ subst-⊔ {γ₁ = δ₁}{γ₂ = δ₂}{σ = σ} subst-δ₁ subst-δ₂ ,
                    ↦-elim (Env⊑ m1 (EnvConjR1⊑ δ₁ δ₂))
                           (Env⊑ m2 (EnvConjR2⊑ δ₁ δ₂)) ⟩ ⟩

subst-reflect {M = M}{σ = σ} (↦-intro d) eqL with M
...    | ` x with (↦-intro d)
...             | d' rewrite sym eqL = subst-reflect-var {σ = σ} d'
subst-reflect {σ = σ} (↦-intro d) eq | ƛ M'
      with subst-reflect {σ = exts σ} d (lambda-inj eq)
... | ⟨ δ′ , ⟨ exts-σ-δ′ , m′ ⟩ ⟩ = 
    ⟨ init δ′ , ⟨ ((λ x → rename-inc-reflect (exts-σ-δ′ (S x)))) ,
             ↦-intro (up-env (split m′) (var-inv (exts-σ-δ′ Z))) ⟩ ⟩
subst-reflect (↦-intro d) () | M₁ · M₂ 

subst-reflect {σ = σ} ⊥-intro eq =
    ⟨ `⊥ , ⟨ subst-⊥ {σ = σ} , ⊥-intro ⟩ ⟩

subst-reflect {σ = σ} (⊔-intro d₁ d₂) eq
  with subst-reflect {σ = σ} d₁ eq | subst-reflect {σ = σ} d₂ eq
... | ⟨ δ₁ , ⟨ subst-δ₁ , m1 ⟩ ⟩ | ⟨ δ₂ , ⟨ subst-δ₂ , m2 ⟩ ⟩ =
     ⟨ δ₁ `⊔ δ₂ , ⟨ subst-⊔ {γ₁ = δ₁}{γ₂ = δ₂}{σ = σ} subst-δ₁ subst-δ₂ ,
                    ⊔-intro (Env⊑ m1 (EnvConjR1⊑ δ₁ δ₂))
                            (Env⊑ m2 (EnvConjR2⊑ δ₁ δ₂)) ⟩ ⟩
subst-reflect (sub d lt) eq 
    with subst-reflect d eq
... | ⟨ δ , ⟨ subst-δ , m ⟩ ⟩ = ⟨ δ , ⟨ subst-δ , sub m lt ⟩ ⟩
\end{code}

* Case (var): We have subst σ M ≡ ` y, so M must also be a variable, say x.
  We apply the lemma subst-reflect-var to conclude.

* Case (↦-elim): We have subst σ M ≡ L₁ · L₂. We proceed by cases on M.
  * Case M ≡ ` x: We apply the subst-reflect-var lemma again to conclude.

  * Case M ≡ M₁ · M₂: By the induction hypothesis, we have
    some δ₁ and δ₂ such that δ₁ ⊢ M₁ ↓ v₁ ↦ v₃ and γ `⊢ σ ↓ δ₁,
    as well as δ₂ ⊢ M₂ ↓ v₁ and γ `⊢ σ ↓ δ₂.
    By Env⊑ we have  δ₁ ⊔ δ₂ ⊢ M₁ ↓ v₁ ↦ v₃ and δ₁ ⊔ δ₂ ⊢ M₂ ↓ v₁
    (using EnvConjR1⊑ and EnvConjR2⊑), and therefore δ₁ ⊔ δ₂ ⊢ M₁ · M₂ ↓ v₃.
    We conclude this case by obtaining γ `⊢ σ ↓ δ₁ ⊔ δ₂
    by the subst-⊔ lemma.

* Case (↦-intro): We have subst σ M ≡ ƛ L'. We proceed by cases on M.
  * Case M ≡ ` x: We apply the subst-reflect-var lemma.

  * Case M ≡ ƛ M': By the induction hypothesis, we have
    (δ' , v') ⊢ M' ↓ v₂ and (δ , v₁) `⊢ exts σ ↓ (δ' , v').
    From the later we have (δ , v₁) ⊢ # 0 ↓ v'.
    By the lemma var-inv we have v' ⊑ v₁, so by the up-env lemma we
    have (δ' , v₁) ⊢ M' ↓ v₂ and therefore δ' ⊢ ƛ M' ↓ v₁ → v₂.  We
    also need to show that δ `⊢ σ ↓ δ'.  Fix k. We have (δ , v₁) ⊢
    rename S_ σ k ↓ nth k δ'.  We then apply the lemma
    rename-inc-reflect to obtain δ ⊢ σ k ↓ nth k δ', so this case is
    complete.

* Case (⊥-intro): We choose `⊥ for δ.
  We have `⊥ ⊢ M ↓ ⊥ by (⊥-intro).
  We have δ `⊢ σ ↓ `⊥ by the lemma subst-empty.

* Case (⊔-intro): By the induction hypothesis we have
  δ₁ ⊢ M ↓ v₁, δ₂ ⊢ M ↓ v₂, δ `⊢ σ ↓ δ₁, and δ `⊢ σ ↓ δ₂.
  We have δ₁ ⊔ δ₂ ⊢ M ↓ v₁ and δ₁ ⊔ δ₂ ⊢ M ↓ v₂
  by Env⊑ with EnvConjR1⊑ and EnvConjR2⊑.
  So by (⊔-intro) we have δ₁ ⊔ δ₂ ⊢ M ↓ v₁ ⊔ v₂.
  By subst-⊔ we conclude that δ `⊢ σ ↓ δ₁ ⊔ δ₂.
   

#### Single substitution reflects denotations

Most of the work is now behind us. We have proved that simultaneous
substitution reflects denotations. Of course, β reduction uses single
substitution, so we need a corollary that proves that single
substitution reflects denotations. That is,
give terms M : (Γ , ★ ⊢ ★) and N : (Γ ⊢ ★,)
if γ ⊢ M [ N ] ↓ v, then γ ⊢ N ↓ v₂ and (γ , v₂) ⊢ M ↓ v
for some value v₂. We have M [ N ] = subst (subst-zero N) M.
We apply the subst-reflect lemma to obtain
γ `⊢ subst-zero N ↓ (δ' , v') and (δ' , v') ⊢ M ↓ v
for some δ' and v'.

Instantiating γ `⊢ subst-zero N ↓ (δ' , v') at k = 0
gives us γ ⊢ N ↓ v'. We choose v₂ = v', so the first
part of our conclusion is complete.

It remains to prove (γ , v') ⊢ M ↓ v. First, we obtain 
(γ , v') ⊢ rename var-id M ↓ v by the rename-pres lemma
applied to (δ' , v') ⊢ M ↓ v, with the var-id renaming,
γ = (δ' , v'), and δ = (γ , v'). To apply this lemma,
we need to show that 
nth n (δ' , v') ⊑ nth (var-id n) (γ , v') for any n.
This is accomplished by the following lemma, which
makes use of γ `⊢ subst-zero N ↓ (δ' , v').

\begin{code}
nth-id-le : ∀{Γ}{δ'}{v'}{γ}{N}
      → γ `⊢ subst-zero N ↓ (δ' `, v')
        -----------------------------------------------------
      → (x : Γ , ★ ∋ ★) → (δ' `, v') x ⊑ (γ `, v') (var-id x) 
nth-id-le γ-sz-δ'v' Z = Refl⊑
nth-id-le γ-sz-δ'v' (S n') = var-inv (γ-sz-δ'v' (S n'))
\end{code}

The above lemma proceeds by induction on n.

* If it is Z, then we show that v' ⊑ v' by Refl⊑.
* If it is S n,' then from the premise we obtain
  γ ⊢ # n' ↓ nth n' δ'. By var-inv we have
  nth n' δ' ⊑ nth n' γ from which we conclude that
  nth (S n') (δ' , v') ⊑ nth (var-id (S n')) (γ , v').

Returning to the proof that single substitution reflects
denotations, we have just proved that

  (γ `, v') ⊢ rename var-id M ↓ v

but we need to show (γ `, v') ⊢ M ↓ v. 
So we apply the rename-id lemma to obtain
rename var-id M ≡ M.

The following is the formal version of this proof.

\begin{code}
subst-zero-reflect : ∀ {Δ} {δ : Env Δ} {γ : Env (Δ , ★)} {N : Δ ⊢ ★}
  → δ `⊢ subst-zero N ↓ γ
    ----------------------------------------
  → Σ[ w ∈ Value ] γ `⊑ (δ `, w) × δ ⊢ N ↓ w
subst-zero-reflect {δ = δ} {γ = γ} δσγ = ⟨ last γ , ⟨ lemma , δσγ Z ⟩ ⟩   
  where
  lemma : γ `⊑ (δ `, last γ)
  lemma Z  =  Refl⊑
  lemma (S x) = var-inv (δσγ (S x))
  
substitution-reflect : ∀ {Δ} {δ : Env Δ} {M : Δ , ★ ⊢ ★} {N : Δ ⊢ ★} {v}
  → δ ⊢ M [ N ] ↓ v
    ------------------------------------------------
  → Σ[ w ∈ Value ] δ ⊢ N ↓ w  ×  (δ `, w) ⊢ M ↓ v
substitution-reflect d with subst-reflect d refl
...  | ⟨ γ , ⟨ δσγ , γMv ⟩ ⟩ with subst-zero-reflect δσγ
...    | ⟨ w , ⟨ ineq , δNw ⟩ ⟩ = ⟨ w , ⟨ δNw , Env⊑ γMv ineq ⟩ ⟩
\end{code}


#### Reduction reflects denotations

Now that we have proved that substitution reflects denotations, we can
easily prove that reduction does too.

\begin{code}
reflect-beta : ∀{Γ}{γ : Env Γ}{M N}{v}
    → γ ⊢ (N [ M ]) ↓ v
    → γ ⊢ (ƛ N) · M ↓ v
reflect-beta d 
    with substitution-reflect d
... | ⟨ v₂' , ⟨ d₁' , d₂' ⟩ ⟩ = ↦-elim (↦-intro d₂') d₁' 


reflect : ∀ {Γ} {γ : Env Γ} {M M' N v}
  → γ ⊢ N ↓ v  →  M —→ M'  →   M' ≡ N
    ---------------------------------
  → γ ⊢ M ↓ v
reflect (var) (ξ₁ x₁ r) ()
reflect (var) (ξ₂ x₁ r) ()
reflect{γ = γ} (var{x = x}) β mn
    with var{γ = γ}{x = x}
... | d' rewrite sym mn = reflect-beta d' 
reflect (var) (ζ r) ()
reflect (↦-elim d₁ d₂) (ξ₁ x r) refl = ↦-elim (reflect d₁ r refl) d₂ 
reflect (↦-elim d₁ d₂) (ξ₂ x r) refl = ↦-elim d₁ (reflect d₂ r refl) 
reflect (↦-elim d₁ d₂) β mn
    with ↦-elim d₁ d₂
... | d' rewrite sym mn = reflect-beta d'
reflect (↦-elim d₁ d₂) (ζ r) ()
reflect (↦-intro d) (ξ₁ x r) ()
reflect (↦-intro d) (ξ₂ x r) ()
reflect (↦-intro d) β mn
    with ↦-intro d
... | d' rewrite sym mn = reflect-beta d'
reflect (↦-intro d) (ζ r) refl = ↦-intro (reflect d r refl)
reflect ⊥-intro r mn = ⊥-intro
reflect (⊔-intro d₁ d₂) r mn rewrite sym mn =
   ⊔-intro (reflect d₁ r refl) (reflect d₂ r refl)
reflect (sub d lt) r mn = sub (reflect d r mn) lt 
\end{code}

### Finale: reduction implies denotational equality

We have proved that reduction both preserves and reflects
denotations. Thus, reduction implies denotational equality.

\begin{code}
reduce-equal : ∀ {Γ} {M : Γ ⊢ ★} {N : Γ ⊢ ★}
  → M —→ N
    ---------
  → ℰ M ≃ ℰ N
reduce-equal {Γ}{M}{N} r = ⟨ (λ m → preserve m r) , (λ n → reflect n r refl) ⟩
\end{code}


## Notes

The denotational semantics presented in this chapter is an example of
a *filter model* (Barendregt, Coppo, Dezani-Ciancaglini, 1983). Filter
models use type systems with intersection types to precisely
characterize runtime behavior (Coppo, Dezani-Ciancaglini, and Salle,
1979). The notation that we use in this chapter is not that of type
systems and intersection types, but the Value data type is isomorphic
to types (↦ is →, ⊔ is ∧, ⊥ is ⊤), the ⊑ relation is the inverse of
subtyping <:, and the evaluation relation ρ ⊢ M ↓ v is isomorphic to a
type system. Write Γ instead of ρ, A instead of v, and replace ↓ with : and
one has Γ ⊢ M : A.  By varying the definition of subtyping and
using different choices of type atoms, intersection type systems can
provide semantics for many different untyped λ calculi, from full beta
to the lazy and call-by-value calculi (Alessi, Barbanera, and
Dezani-Ciancaglini, 2006) (Rocca and Paolini, 2004).  The denotational
semantics in this chapter corresponds to the BCD system (Barendregt,
Coppo, Dezani-Ciancaglini, 1983).  Part 3 of the book _Lambda Calculus
with Types_ describes a framework for intersection type systems that
enables results similar to the ones in this chapter, but for the
entire family of intersection type systems (Barendregt, Dekkers, and
Statman, 2013).

The two ideas of using finite tables to represent functions and of
relaxing table lookup to enable self application first appeared in a
technical report by Gordon Plotkin (1972) and are later described in
an article in Theoretical Computer Science (Plotkin 1993).  In that
work, the inductive definition of Value is a bit different than the
one we use:
 
    Value = C + ℘f(Value) × ℘f(Value)
 
where C is a set of constants and ℘f means finite powerset.  The pairs
in ℘f(Value) × ℘f(Value) represent input-output mappings, just as in
this chapter. The finite powersets are used to enable a function table
to appear in the input and in the output. These differences amount to
changing where the recursion appears in the definition of Value.
Plotkin's model is an example of a _graph model_ of the untyped lambda
calculus (Barendregt, 1984). In a graph model, the semantics is
presented as a function from programs and environments to (possibly
infinite) sets of values. The semantics in this chapter is instead
defined as a relation, but set-valued functions are isomorphic to
relations. We choose to present the semantics as a relation because
the functional approach requires a kind of existential quantifier that
is not present in Agda.

[PLW: What kind of existential is required?]

Dana Scott's ℘(ω) (1976) and Engeler's B(A) (1981) are two more
examples of graph models. Both use the following inductive definition
of Value.
 
    Value = C + ℘f(Value) × Value
 
The use of Value instead of ℘f(Value) in the output does not restrict
expressiveness compared to Plotkin's model because the semantics use
sets of values and a pair of sets (V, V') can be represented as a set
of pairs { (V, v') | v' ∈ V' }.  In Scott's ℘(ω), the above values are
mapped to and from the natural numbers using a kind of Godel encoding.


## References

* Intersection Types and Lambda Models.  Fabio Alessi, Franco
  Barbanera, and Mariangiola Dezani-Ciancaglini, Theoretical
  Compututer Science, vol. 355, pages 108-126, 2006.

* The Lambda Calculus. H.P. Barendregt, 1984.

* A filter lambda model and the completeness of type assignment.  Henk
  Barendregt, Mario Coppo, and Mariangiola Dezani-Ciancaglini, Journal
  of Symbolic Logic, vol. 48, pages 931-940, 1983.

* Lambda Calculus with Types. Henk Barendregt, Wil Dekkers, and
  Richard Statman, Cambridge University Press, Perspectives in Logic,
  2013.

* Functional characterization of some semantic equalities inside
  λ-calculus. Mario Coppo, Mariangiola Dezani-Ciancaglini, and Patrick
  Salle, in Sixth Colloquium on Automata, Languages and Programming.
  Springer, pages 133--146, 1979.

* Algebras and combinators. Erwin Engeler, Algebra Universalis,
  vol. 13, pages 389-392, 1981.

* A Set-Theoretical Definition of Application. Gordon D. Plotkin,
  University of Edinburgh, Technical Report MIP-R-95, 1972.

* Set-theoretical and other elementary models of the λ-calculus.
  Gordon D. Plotkin, Theoretical Computer Science, vol. 121,
  pages 351-409, 1993.

* The Parametric Lambda Calculus. Simona Ronchi Della Rocca and Luca
  Paolini, Springer, 2004.

* Data Types as Lattices. Dana Scott, SIAM Journal on Computing,
  vol. 5, pages 522-587, 1976.

