---
title     : "Denot: Denotational semantics for the untyped lambda calculus"
layout    : page
prev      : /Untyped/
permalink : /Denot/
next      : /DenotCompositional/
---

\begin{code}
module plfa.Denot where
\end{code}

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
\end{code}


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

If the join v₁ ⊔ v₂ is less than another value v₃,
then both v₁ and v₂ are less than v₃.

\begin{code}
⊔⊑-invL : ∀{v₁ v₂ v₃ : Value}
        → v₁ ⊔ v₂ ⊑ v₃
          ---------
        → v₁ ⊑ v₃
⊔⊑-invL (ConjL⊑ lt1 lt2) = lt1
⊔⊑-invL (ConjR1⊑ lt) = ConjR1⊑ (⊔⊑-invL lt)
⊔⊑-invL (ConjR2⊑ lt) = ConjR2⊑ (⊔⊑-invL lt)
⊔⊑-invL (Trans⊑ lt1 lt2) = Trans⊑ (⊔⊑-invL lt1) lt2

⊔⊑-invR : ∀{v₁ v₂ v₃ : Value}
       → v₁ ⊔ v₂ ⊑ v₃
         ---------
       → v₂ ⊑ v₃
⊔⊑-invR (ConjL⊑ lt lt₁) = lt₁
⊔⊑-invR (ConjR1⊑ lt) = ConjR1⊑ (⊔⊑-invR lt)
⊔⊑-invR (ConjR2⊑ lt) = ConjR2⊑ (⊔⊑-invR lt)
⊔⊑-invR (Trans⊑ lt lt₁) = Trans⊑ (⊔⊑-invR lt) lt₁
\end{code}


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


## Road map for the following chapters

The subsequent chapters prove that the denotational semantics has
several desirable. First, we prove that the semantics is
compositional, i.e., that the denotation of a term is a function of
the denotations of its subterms. To do this we shall prove equations
of the following shape.

    ℰ (ƛ M) ≃ ... ℰ M ...
    ℰ (M · N) ≃ ... ℰ M ... ℰ N ...

The compositionality property is not trivial because the semantics we
have defined includes three rules that are not syntax directed:
(⊥-intro), (⊔-intro), and (sub).

Next we investigate whether the denotational semantics and the
reduction semantics are equivalent. Recall that the job of a language
semantics is to describe the observable behavior of a given program
M. For the lambda calculus there are several choices that one can
make, but they usually boil down to just one bit:

  * divergence: the program M executes forever.
  * termination: the program M halts.

A semantics can be formulated in terms of reduction.

  * divergence: ¬ (M —↠ ƛ N) for any term N.
  * termination: M —↠ ƛ N for some term N.

A semantics can also be formulated using denotations.

  * divergence: ¬ (∅ ⊢ M ↓ v ↦ v') for any v and v'.
  * termination: ∅ ⊢ M ↓ v ↦ v' for some v and v'.

Alternatively, observations can be formulated with the denotation
function ℰ. 

  * divergence: ¬ (ℰ M ≃ ℰ (ƛ N)) for any term N.
  * termination: ℰ M ≃ ℰ (ƛ N) for some term N.

So the question is whether the two semantics are equivalent.

    (∃ N. M —↠ ƛ N)  iff  (∃ N. ℰ M ≃ ℰ (ƛ N))

We address each direction of the equivalence in the second and third
chapters. In the second chapter we prove that reduction to a lambda
abstraction implies denotational equality to a lambda
abstraction. This property is called the _soundness_ in the
literature.

    M —↠ ƛ N  implies  ℰ M ≃ ℰ (ƛ N)

In the third chapter we prove that denotational equality to a lambda
abstraction implies reduction to a lambda abstraction. This property
is called _adequacy_ in the literature.

    ℰ M ≃ ℰ (ƛ N)  implies M —↠ ƛ N' for some N'

The proofs of these properties rely on some basic results about the
denotational semantics, which we establish in the rest of this
chapter.  We start with some lemmas about renaming, which are quite
similar to the renaming lemmas that we have seen in previous chapters.
We conclude with a proof of an important inversion lemma for the
less-than relation regarding function values.


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


## Inversion of the less-than relation for functions

What can we deduce from knowing that a function v₁ ↦ v₁' is less than
some value v₂?  What can we deduce about v₂? The answer to this
question is called the inversion property of less-than for functions.
This question is not easy to answer because of the Dist⊑ rule, which
relates a function on the left to a pair of functions on the right.
So v₂ may include several functions that, as a group, relate to v₁ ↦
v₁'. Furthermore, because of the rules ConjR1⊑ and ConjR2⊑, there may
be other values inside v₂, such as ⊥, that have nothing to do with v₁
↦ v₁'. But in general, we can deduce that v₂ includes a collection of
functions where the join of their domains is less than v₁ and the join
of their codomains is greater than v₁'.

To precisely state and prove this inversion property, we need to
define what it means for a value to _include_ a collection of values.
We also need to define how to compute the join of their domains and
codomains.


### Value membership and inclusion

Recall that we think of a value as a set of entries with the join
operator v₁ ⊔ v₂ acting like set union. The function value v ↦ v' and
bottom value ⊥ constitute the two kinds of elements of the set.  (In
other contexts one can instead think of ⊥ as the empty set, but here
we must think of it as an element.)  We write v ∈ v' to say that v is
an element of v', as defined below.

\begin{code}
infix 5 _∈_

_∈_ : Value → Value → Set
v ∈ ⊥ = v ≡ ⊥
v ∈ v₁ ↦ v₂ = v ≡ v₁ ↦ v₂
v ∈ (v₁ ⊔ v₂) = v ∈ v₁ ⊎ v ∈ v₂
\end{code}

So we can represent a collection of values simply as a value.  We
write v₁ ⊆ v₂ to say that all the elements of v₁ are also in v₂.

\begin{code}
infix 5 _⊆_

_⊆_ : Value → Value → Set
v₁ ⊆ v₂ = ∀{v₃} → v₃ ∈ v₁ → v₃ ∈ v₂
\end{code}

The notions of membership and inclusion for values are closely related
to the less-than relation. They are narrower relations in that they
imply the less-than relation but not the other way around.

\begin{code}
∈→⊑ : ∀{v₁ v₂ : Value}
    → v₁ ∈ v₂
      -----
    → v₁ ⊑ v₂
∈→⊑ {.⊥} {⊥} refl = Bot⊑
∈→⊑ {.(v₂ ↦ v₂₁)} {v₂ ↦ v₂₁} refl = Refl⊑
∈→⊑ {v₁} {v₂ ⊔ v₂₁} (inj₁ x) = ConjR1⊑ (∈→⊑ x)
∈→⊑ {v₁} {v₂ ⊔ v₂₁} (inj₂ y) = ConjR2⊑ (∈→⊑ y)

⊆→⊑ : ∀{v₁ v₂ : Value}
    → v₁ ⊆ v₂
      -----
    → v₁ ⊑ v₂
⊆→⊑ {⊥} {v₂} s with s {⊥} refl
... | x = Bot⊑
⊆→⊑ {v₁ ↦ v₁'} {v₂} s with s {v₁ ↦ v₁'} refl
... | x = ∈→⊑ x
⊆→⊑ {v₁ ⊔ v₁'} {v₂} s =
   ConjL⊑ (⊆→⊑ (λ {C} z → s (inj₁ z))) (⊆→⊑ (λ {C} z → s (inj₂ z)))
\end{code}

We shall also need some inversion principles for value inclusion.  If
the union of v₁ and v₂ is included in v₃, then of course both v₁ and
v₂ are each included in v₃.

\begin{code}
⊔⊆-inv : ∀{v₁ v₂ v₃ : Value}
       → (v₁ ⊔ v₂) ⊆ v₃
         ---------------
       → v₁ ⊆ v₃  ×  v₂ ⊆ v₃
⊔⊆-inv abc = ⟨ (λ {x} x₁ → abc (inj₁ x₁)) , (λ {x} x₁ → abc (inj₂ x₁)) ⟩
\end{code}

In our value representation, the function value v₁ ↦ v₂ is both an
element and also a singleton set. So if v₁ ↦ v₂ is a subset of v₃,
then v₁ ↦ v₂ must be a member of v₃.

\begin{code}
↦⊆→∈ : ∀{v₁ v₂ v₃ : Value}
     → v₁ ↦ v₂ ⊆ v₃
       ---------
     → v₁ ↦ v₂ ∈ v₃
↦⊆→∈{v₁}{v₂}{v₃} incl = incl {v₁ ↦ v₂} refl 
\end{code}


### Function values

To identify collections of functions, we define the following two
predicates. We write Fun v₁ if v₁ is a function value, that is, if v₁
≡ v ↦ v' for some values v and v'. We write Funs v if all the elements
of v are functions.

\begin{code}
data Fun : Value → Set where
  fun : ∀{v₁ v v'} → v₁ ≡ (v ↦ v') → Fun v₁

Funs : Value → Set
Funs v = ∀{v'} → v' ∈ v → Fun v'
\end{code}

Of course, the value ⊥ is not a function.

\begin{code}
¬Fun⊥ : ¬ (Fun ⊥)
¬Fun⊥ (fun ())
\end{code}

In our values-as-sets representation, our sets always include at least
one element. Thus, if all the elements are functions, there is at
least one that is a function.

\begin{code}
Funs∈ : ∀{v₁}
      → Funs v₁
      → Σ[ v ∈ Value ] Σ[ v' ∈ Value ] v ↦ v' ∈ v₁
Funs∈ {⊥} f with f {⊥} refl
... | fun ()
Funs∈ {v ↦ v'} f = ⟨ v , ⟨ v' , refl ⟩ ⟩
Funs∈ {v₁ ⊔ v₂} f
    with Funs∈ {v₁} λ {v'} z → f (inj₁ z)
... | ⟨ v , ⟨ v' , m ⟩ ⟩ = ⟨ v , ⟨ v' , (inj₁ m) ⟩ ⟩
\end{code}


### Domains and codomains

Returning to our goal, the inversion principle for less-than a
function, we want to show that v₁ ↦ v₁' ⊑ v₂ implies that v₂ includes
a set of function values such that the join of their domains is less
than v₁ and the join of their codomains is greater than v₁'.

To this end we define the following dom and cod functions.  Given some
value v (that represents a set of entries), dom v returns the join of
their domains and cod v returns the join of their codomains.

\begin{code}
dom : (v : Value) → Value
dom ⊥  = ⊥
dom (v ↦ v') = v
dom (v ⊔ v') = dom v ⊔ dom v'

cod : (v : Value) → Value
cod ⊥  = ⊥
cod (v ↦ v') = v'
cod (v ⊔ v') = cod v ⊔ cod v'
\end{code}

We need just one property each for dom and cod.  Given a collection of
functions represented by value v, and an entry v₁ ↦ v₂ in v, we know
that v₁ is included in the domain of v.

\begin{code}
↦∈→⊆dom : ∀{v v₁ v₂ : Value}
          → Funs v  →  (v₁ ↦ v₂) ∈ v
            ----------------------
          → v₁ ⊆ dom v
↦∈→⊆dom {⊥} fg ()
↦∈→⊆dom {v ↦ v'} fg refl = λ z → z
↦∈→⊆dom {v ⊔ v'} fg (inj₁ x) =
  let ih = ↦∈→⊆dom {v} (λ {v'} z → fg (inj₁ z)) x in
  λ x₁ → inj₁ (ih x₁)
↦∈→⊆dom {v ⊔ v'} fg (inj₂ y) =
  let ih = ↦∈→⊆dom {v'} (λ {v'} z → fg (inj₂ z)) y in
  λ x₁ → inj₂ (ih x₁)
\end{code}

Regarding cod, suppose we have a collection of functions represented
by v, but all of them are just copies of v₁ ↦ v₂.  Then the cod v is
included in v₂.

\begin{code}
⊆↦→cod⊆ : ∀{v v₁ v₂ : Value}
      → v ⊆ v₁ ↦ v₂
        ---------
      → cod v ⊆ v₂
⊆↦→cod⊆ {⊥} s refl with s {⊥} refl
... | ()
⊆↦→cod⊆ {C ↦ C'} s m with s {C ↦ C'} refl
... | refl = m
⊆↦→cod⊆ {v ⊔ v₁} s (inj₁ x) = ⊆↦→cod⊆ (λ {C} z → s (inj₁ z)) x
⊆↦→cod⊆ {v ⊔ v₁} s (inj₂ y) = ⊆↦→cod⊆ (λ {C} z → s (inj₂ z)) y
\end{code}

With the dom and cod functions in hand, we can make precise the
conclusion of the inversion principle for functions, which we package
into the following predicate named factor. We say that v₁ ↦ v₁'
_factors_ v₂ into v₂'.

\begin{code}
factor : (v₂ : Value) → (v₂' : Value) → (v₁ : Value) → (v₁' : Value) → Set
factor v₂ v₂' v₁ v₁' = Funs v₂' × v₂' ⊆ v₂ × dom v₂' ⊑ v₁ × v₁' ⊑ cod v₂'
\end{code}

We prove the inversion principle for functions by induction on the
derivation of the less-than relation. To make the induction hypothesis
stronger, we broaden the premise to v₁ ⊑ v₂ (instead of v₁ ↦ v₁' ⊑
v₂), and strengthen the conclusion to say that for _every_ function
value w₁ ↦ w₁' ∈ v₁, we have that w₁ ↦ w₁' factors v₂ into v₂'.

### Inversion of less-than for functions, the case for Trans⊑

The crux of the proof is the case for Trans⊑.

    v₁ ⊑ u   u ⊑ v₂
    --------------- (Trans⊑)
        v₁ ⊑ v₂

By the induction hypothesis for v₁ ⊑ u, we know
that w₁ ↦ w₁' factors u into u', for some value u',
so we have Funs u' and u' ⊆ u.
By the induction hypothesis for u ⊑ v₂, we know
that for any u₁ ↦ u₂ ∈ u, u₁ ↦ u₂ factors v₂ into v₂'.
With these facts in hand, we proceed by induction on u'
to prove that (dom u') ↦ (cod u') factors v₂ into v₂'.
We discuss each case of the proof in the text below.

\begin{code}
sub-inv-trans : ∀{u' v₂ u : Value}
    → Funs u'  →  u' ⊆ u
    → (∀{u₁ u₂} → u₁ ↦ u₂ ∈ u → Σ[ v₂' ∈ Value ] factor v₂ v₂' u₁ u₂)
      ---------------------------------------------------------------
    → Σ[ v₂' ∈ Value ] factor v₂ v₂' (dom u') (cod u')
sub-inv-trans {⊥} {v₂} {u} fu' u'⊆u IH =
   ⊥-elim (contradiction (fu'{v' = ⊥} refl) ¬Fun⊥)
sub-inv-trans {u₁' ↦ u₂'} {v₂} {u} fg u'⊆u IH = IH (↦⊆→∈ u'⊆u)
sub-inv-trans {u₁' ⊔ u₂'} {v₂} {u} fg u'⊆u IH
    with ⊔⊆-inv u'⊆u
... | ⟨ u₁'⊆u , u₂'⊆u ⟩
    with sub-inv-trans {u₁'} {v₂} {u} (λ {v'} z → fg (inj₁ z)) u₁'⊆u IH
       | sub-inv-trans {u₂'} {v₂} {u} (λ {v'} z → fg (inj₂ z)) u₂'⊆u IH
... | ⟨ v₂₁' , ⟨ fu21' , ⟨ v₂₁'⊆v₂ , ⟨ dv₂₁'⊑du₁' , cu₁'⊑cv₂₁' ⟩ ⟩ ⟩ ⟩
    | ⟨ v₂₂' , ⟨ fu22' , ⟨ v₂₂'⊆v₂ , ⟨ dv₂₂'⊑du₂' , cu₁'⊑cv₂₂' ⟩ ⟩ ⟩ ⟩ =
      ⟨ (v₂₁' ⊔ v₂₂') , ⟨ fv₂' , ⟨ v₂'⊆v₂ ,
      ⟨ ⊔⊑⊔ dv₂₁'⊑du₁' dv₂₂'⊑du₂' ,
        ⊔⊑⊔ cu₁'⊑cv₂₁' cu₁'⊑cv₂₂' ⟩ ⟩ ⟩ ⟩
    where fv₂' : {v' : Value} → v' ∈ v₂₁' ⊎ v' ∈ v₂₂' → Fun v'
          fv₂' {v'} (inj₁ x) = fu21' x
          fv₂' {v'} (inj₂ y) = fu22' y
          v₂'⊆v₂ : {C : Value} → C ∈ v₂₁' ⊎ C ∈ v₂₂' → C ∈ v₂
          v₂'⊆v₂ {C} (inj₁ x) = v₂₁'⊆v₂ x
          v₂'⊆v₂ {C} (inj₂ y) = v₂₂'⊆v₂ y
\end{code}

* Suppose u' ≡ ⊥. Then we have a contradiction because
  it is not the case that Fun ⊥.

* Suppose u' ≡ u₁' ↦ u₂'. Then u₁' ↦ u₂' ∈ u and we can apply the
  premise (the induction hypothesis from u ⊑ v₂) to obtain that
  u₁' ↦ u₂' factors of v₂ into v₂'. This case is complete because
  dom u' ≡ u₁' and cod u' ≡ u₂'.
  
* Suppose u' ≡ u₁' ⊔ u₂'. Then we have u₁' ⊆ u and u₂' ⊆ u. We also  
  have Funs u₁' and Funs u₂', so we can apply the induction hypothesis
  for both u₁' and u₂'. So there exists values v₂₁' and v₂₂' such that
  (dom u₁') ↦ (cod u₁') factors u into v₂₁' and
  (dom u₂') ↦ (cod u₂') factors u into v₂₂'.
  We will show that (dom u) ↦ (cod u) factors u into (v₂₁' ⊔ v₂₂').
  So we need to show that
  
        dom (v₂₁' ⊔ v₂₂') ⊑ dom (u₁' ⊔ u₂')
        cod (u₁' ⊔ u₂') ⊑ cod (v₂₁' ⊔ v₂₂')
  
  But those both follow directly from the factoring of
  u into v₂₁' and v₂₂', using the monotonicity of ⊔ with respect to ⊑.
  

### Inversion of less-than for functions

We come to the proof of the main lemma concerning the inversion of
less-than for functions. We show that if v₁ ⊑ v₂, then for any w₁ ↦
w₁' ∈ v₁, we can factor v₂ into v₂' according to w₁ ↦ w₁'. We proceed
by induction on the derivation of v₁ ⊑ v₂, and describe each case in
the text after the Agda proof.

\begin{code}
sub-inv : ∀{v₁ v₂ : Value}
        → v₁ ⊑ v₂
        → ∀{w₁ w₁'} → w₁ ↦ w₁' ∈ v₁
          -------------------------------
        → Σ[ v₂' ∈ Value ] factor v₂ v₂' w₁ w₁'
sub-inv {⊥} {v₂} Bot⊑ {w₁} {w₁'} ()
sub-inv {v₁₁ ⊔ v₁₂} {v₂} (ConjL⊑ lt1 lt2) {w₁} {w₁'} (inj₁ x) = sub-inv lt1 x
sub-inv {v₁₁ ⊔ v₁₂} {v₂} (ConjL⊑ lt1 lt2) {w₁} {w₁'} (inj₂ y) = sub-inv lt2 y
sub-inv {v₁} {v₂₁ ⊔ v₂₂} (ConjR1⊑ lt) {w₁} {w₁'} m
    with sub-inv lt m  
... | ⟨ v₂₁' , ⟨ fv₂₁' , ⟨ v₂₁'⊆v₂₁ , ⟨ domv₂₁'⊑w₁ , w₁'⊑codv₂₁' ⟩ ⟩ ⟩ ⟩ =
      ⟨ v₂₁' , ⟨ fv₂₁' , ⟨ (λ {w} z → inj₁ (v₂₁'⊆v₂₁ z)) ,
                                   ⟨ domv₂₁'⊑w₁ , w₁'⊑codv₂₁' ⟩ ⟩ ⟩ ⟩
sub-inv {v₁} {v₂₁ ⊔ v₂₂} (ConjR2⊑ lt) {w₁} {w₁'} m
    with sub-inv lt m  
... | ⟨ v₂₂' , ⟨ fv₂₂' , ⟨ v₂₂'⊆v₂₂ , ⟨ domv₂₂'⊑w₁ , w₁'⊑codv₂₂' ⟩ ⟩ ⟩ ⟩ =
      ⟨ v₂₂' , ⟨ fv₂₂' , ⟨ (λ {C} z → inj₂ (v₂₂'⊆v₂₂ z)) ,
                                   ⟨ domv₂₂'⊑w₁ , w₁'⊑codv₂₂' ⟩ ⟩ ⟩ ⟩
sub-inv {v₁} {v₂} (Trans⊑{v₂ = u} v₁⊑u u⊑v₂) {w₁} {w₁'} w₁↦w₁'∈v₁
    with sub-inv v₁⊑u w₁↦w₁'∈v₁
... | ⟨ u' , ⟨ fu' , ⟨ u'⊆u , ⟨ domu'⊑w₁ , w₁'⊑codu' ⟩ ⟩ ⟩ ⟩ 
    with sub-inv-trans {u'} fu' u'⊆u (sub-inv u⊑v₂) 
... | ⟨ v₂' , ⟨ fv₂' , ⟨ v₂'⊆v₂ , ⟨ domv₂'⊑domu' , codu'⊑codv₂' ⟩ ⟩ ⟩ ⟩ =
      ⟨ v₂' , ⟨ fv₂' , ⟨ v₂'⊆v₂ , ⟨ Trans⊑ domv₂'⊑domu' domu'⊑w₁ ,
                                    Trans⊑ w₁'⊑codu' codu'⊑codv₂' ⟩ ⟩ ⟩ ⟩
sub-inv {v₁₁ ↦ v₁₂} {v₂₁ ↦ v₂₂} (Fun⊑ lt1 lt2) refl =
    ⟨ v₂₁ ↦ v₂₂ , ⟨ (λ {v'} → fun) , ⟨ (λ {C} z → z) , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩
sub-inv {v₂₁ ↦ (v₂₂ ⊔ v₂₃)} {v₂₁ ↦ v₂₂ ⊔ v₂₁ ↦ v₂₃} Dist⊑
    {.v₂₁} {.(v₂₂ ⊔ v₂₃)} refl =
    ⟨ v₂₁ ↦ v₂₂ ⊔ v₂₁ ↦ v₂₃ , ⟨ f , ⟨ g , ⟨ ConjL⊑ Refl⊑ Refl⊑ , Refl⊑ ⟩ ⟩ ⟩ ⟩
  where f : Funs (v₂₁ ↦ v₂₂ ⊔ v₂₁ ↦ v₂₃)
        f (inj₁ x) = fun x
        f (inj₂ y) = fun y
        g : (v₂₁ ↦ v₂₂ ⊔ v₂₁ ↦ v₂₃) ⊆ (v₂₁ ↦ v₂₂ ⊔ v₂₁ ↦ v₂₃)
        g (inj₁ x) = inj₁ x
        g (inj₂ y) = inj₂ y
\end{code}

Let w₁ w₁' be arbitrary values.

* Case (Bot⊑). So v₁ ≡ ⊥. We have w₁ ↦ w₁' ∈ ⊥, but that is impossible.

* Case (ConjL⊑).

        v₁₁ ⊑ v₂   v₁₂ ⊑ v₂
        -------------------
        v₁₁ ⊔ v₁₂ ⊑ v₂

  Given that w₁ ↦ w₁' ∈ v₁₁ ⊔ v₁₂, there are two subcases to consider.

  * Subcase w₁ ↦ w₁' ∈ v₁₁. We conclude by the induction
    hypothesis for v₁₁ ⊑ v₂.
  
  * Subcase w₁ ↦ w₁' ∈ v₁₂. We conclude by the induction hypothesis
    for v₁₂ ⊑ v₂.

* Case (ConjR1⊑).

        v₁ ⊑ v₂₁
        --------------
        v₁ ⊑ v₂₁ ⊔ v₂₂

  Given that w₁ ↦ w₁' ∈ v₁, the induction hypothesis for v₁ ⊑ v₂₁
  gives us that w₁ ↦ w₁' factors v₂₁ into v₂₁' for some v₂₁'.
  To show that w₁ ↦ w₁' also factors (v₂₁ ⊔ v₂₂) into v₂₁',
  we just need to show that v₂₁' ⊆ v₂₁ ⊔ v₂₂, but that follows
  directly from v₂₁' ⊆ v₂₁.

* Case (ConjR2⊑). This case follows by reasoning similar to
  the case for (ConjR1⊑).

* Case (Trans⊑). 

        v₁ ⊑ u   u ⊑ v₂
        ---------------
            v₁ ⊑ v₂
        
  By the induction hypothesis for v₁ ⊑ u, we know
  that w₁ ↦ w₁' factors u into u', for some value u',
  so we have Funs u' and u' ⊆ u.
  By the induction hypothesis for u ⊑ v₂, we know
  that for any u₁ ↦ u₂ ∈ u, u₁ ↦ u₂ factors v₂ into v₂'.
  Now we apply the lemma sub-inv-trans, which gives us
  some v₂' such that (dom u') ↦ (cod u') factors v₂ into v₂'.
  We show that w₁ ↦ w₁' also factors v₂ into v₂'.
  From dom v₂' ⊑ dom u' and dom u' ⊑ w₁, we have dom v₂' ⊑ w₁.
  From w₁' ⊑ cod u' and cod u' ⊑ cod v₂', we have w₁' ⊑ cod v₂',
  and this case is complete.

* Case (Fun⊑).

        v₂₁ ⊑ v₁₁  v₁₂ ⊑ v₂₂
        ---------------------
        v₁₁ ↦ v₁₂ ⊑ v₂₁ ↦ v₂₂

  Given that w₁ ↦ w₁' ∈ v₁₁ ↦ v₁₂, we have w₁ ≡ v₁₁ and w₁' ≡ v₁₂.
  We show that v₁₁ ↦ v₁₂ factors v₂₁ ↦ v₂₂ into itself.
  We need to show that dom (v₂₁ ↦ v₂₂) ⊑ v₁₁ and v₁₂ ⊑ cod (v₂₁ ↦ v₂₂),
  but that is equivalent to our premises v₂₁ ⊑ v₁₁ and v₁₂ ⊑ v₂₂.

* Case (Dist⊑).

        ---------------------------------------------
        v₂₁ ↦ (v₂₂ ⊔ v₂₃) ⊑ (v₂₁ ↦ v₂₂) ⊔ (v₂₁ ↦ v₂₃)

  Given that w₁ ↦ w₁' ∈ v₂₁ ↦ (v₂₂ ⊔ v₂₃), we have w₁ ≡ v₂₁
  and w₁' ≡ v₂₂ ⊔ v₂₃.
  We show that v₂₁ ↦ (v₂₂ ⊔ v₂₃) factors (v₂₁ ↦ v₂₂) ⊔ (v₂₁ ↦ v₂₃) into itself.
  We have v₂₁ ⊔ v₂₁ ⊑ v₂₁, and also
  v₂₂ ⊔ v₂₃ ⊑ v₂₂ ⊔ v₂₃, so the proof is complete.


We conclude this section with two corollaries of the sub-inv lemma.
First, we have the following property that is convenient to use in
later proofs. We specialize the premise to just (v₁ ↦ v₁') ⊑ v₂
and we modify the conclusion to say that for every
w ↦ w' ∈ v₂', we have w ⊑ v₁.

\begin{code}
sub-inv-fun : ∀{v₁ v₁' v₂ : Value}
    → (v₁ ↦ v₁') ⊑ v₂
      -----------------------------------------------------
    → Σ[ v₂' ∈ Value ] Funs v₂' × v₂' ⊆ v₂
        × (∀{w w'} → (w ↦ w') ∈ v₂' → w ⊑ v₁) × v₁' ⊑ cod v₂'
sub-inv-fun{v₁}{v₁'}{v₂} abc
    with sub-inv abc {v₁}{v₁'} refl
... | ⟨ v₂' , ⟨ f , ⟨ v₂'⊆v₂ , ⟨ db , cc ⟩ ⟩ ⟩ ⟩ =
      ⟨ v₂' , ⟨ f , ⟨ v₂'⊆v₂ , ⟨ G , cc ⟩ ⟩ ⟩ ⟩
   where G : ∀{D E} → (D ↦ E) ∈ v₂' → D ⊑ v₁
         G{D}{E} m = Trans⊑ (⊆→⊑ (↦∈→⊆dom f m)) db
\end{code}

The second corollary is the inversion rule that one would expect for
less-than with functions on the left and right-hand sides.

\begin{code}
↦⊑↦-inv : ∀{v₁ v₂ v₃ v₄}
        → v₁ ↦ v₂ ⊑ v₃ ↦ v₄
          -----------------
        → v₃ ⊑ v₁ × v₂ ⊑ v₄
↦⊑↦-inv{v₁}{v₂}{v₃}{v₄} lt
    with sub-inv-fun lt  
... | ⟨ Γ , ⟨ f , ⟨ Γ⊆v34 , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩
    with Funs∈ f
... | ⟨ A , ⟨ A' , A↦A'∈Γ ⟩ ⟩
    with Γ⊆v34 A↦A'∈Γ
... | refl =    
  let codΓ⊆v₄ = ⊆↦→cod⊆ Γ⊆v34 in
  ⟨ lt1 A↦A'∈Γ , Trans⊑ lt2 (⊆→⊑ codΓ⊆v₄) ⟩
\end{code}


## Notes

[JGS: todo: reorganize these notes for the new chapters]

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

