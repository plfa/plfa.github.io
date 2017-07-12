---
title     : "Stlc: The Simply Typed Lambda-Calculus"
layout    : page
permalink : /Stlc
---

This chapter defines the simply-typed lambda calculus.

## Imports

\begin{code}
open import Maps using (Id; id; _≟_; PartialMap; module PartialMap)
open PartialMap using (∅) renaming (_,_↦_ to _,_∶_)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
\end{code}


## Syntax

Syntax of types and terms.

\begin{code}
infixr 20 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  𝔹 : Type

infixl 20 _·_
infix  15 λ[_∶_]_
infix  15 if_then_else_

data Term : Set where
  ` : Id → Term
  λ[_∶_]_ : Id → Type → Term → Term
  _·_ : Term → Term → Term
  true : Term
  false : Term
  if_then_else_ : Term → Term → Term → Term
\end{code}

Example terms.
\begin{code}
f x : Id
f  =  id 0
x  =  id 1

not two : Term 
not =  λ[ x ∶ 𝔹 ] (if ` x then false else true)
two =  λ[ f ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` f · (` f · ` x)
\end{code}

## Values

\begin{code}
data Value : Term → Set where
  value-λ     : ∀ {x A N} → Value (λ[ x ∶ A ] N)
  value-true  : Value true
  value-false : Value false
\end{code}

## Substitution

\begin{code}
_[_:=_] : Term → Id → Term → Term
(` x′) [ x := V ] with x ≟ x′
... | yes _ = V
... | no  _ = ` x′
(λ[ x′ ∶ A′ ] N′) [ x := V ] with x ≟ x′
... | yes _ = λ[ x′ ∶ A′ ] N′
... | no  _ = λ[ x′ ∶ A′ ] (N′ [ x := V ])
(L′ · M′) [ x := V ] =  (L′ [ x := V ]) · (M′ [ x := V ])
(true) [ x := V ] = true
(false) [ x := V ] = false
(if L′ then M′ else N′) [ x := V ] = if (L′ [ x := V ]) then (M′ [ x := V ]) else (N′ [ x := V ])
\end{code}

## Reduction rules

\begin{code}
infix 10 _⟹_ 

data _⟹_ : Term → Term → Set where
  βλ· : ∀ {x A N V} → Value V →
    (λ[ x ∶ A ] N) · V ⟹ N [ x := V ]
  ξ·₁ : ∀ {L L′ M} →
    L ⟹ L′ →
    L · M ⟹ L′ · M
  ξ·₂ : ∀ {V M M′} →
    Value V →
    M ⟹ M′ →
    V · M ⟹ V · M′
  βif-true : ∀ {M N} →
    if true then M else N ⟹ M
  βif-false : ∀ {M N} →
    if false then M else N ⟹ N
  ξif : ∀ {L L′ M N} →
    L ⟹ L′ →    
    if L then M else N ⟹ if L′ then M else N
\end{code}

## Reflexive and transitive closure


\begin{code}
infix 10 _⟹*_ 
infixr 2 _⟹⟨_⟩_
infix  3 _∎

data _⟹*_ : Term → Term → Set where
  _∎ : ∀ M → M ⟹* M
  _⟹⟨_⟩_ : ∀ L {M N} → L ⟹ M → M ⟹* N → L ⟹* N  

reduction₁ : not · true ⟹* false
reduction₁ =
    not · true
  ⟹⟨ βλ· value-true ⟩
    if true then false else true
  ⟹⟨ βif-true ⟩
    false
  ∎

reduction₂ : two · not · true ⟹* true
reduction₂ =
    two · not · true
  ⟹⟨ ξ·₁ (βλ· value-λ) ⟩
    (λ[ x ∶ 𝔹 ] not · (not · ` x)) · true
  ⟹⟨ βλ· value-true ⟩
    not · (not · true)
  ⟹⟨ ξ·₂ value-λ (βλ· value-true) ⟩
    not · (if true then false else true)
  ⟹⟨ ξ·₂ value-λ βif-true  ⟩
    not · false
  ⟹⟨ βλ· value-false ⟩
    if false then false else true
  ⟹⟨ βif-false ⟩
    true
  ∎
\end{code}

Much of the above, though not all, can be filled in using C-c C-r and C-c C-s.



## Type rules

\begin{code}
Context : Set
Context = PartialMap Type

infix 10 _⊢_∶_

data _⊢_∶_ : Context → Term → Type → Set where
  Ax : ∀ {Γ x A} →
    Γ x ≡ just A →
    Γ ⊢ ` x ∶ A
  ⇒-I : ∀ {Γ x N A B} →
    Γ , x ∶ A ⊢ N ∶ B →
    Γ ⊢ λ[ x ∶ A ] N ∶ A ⇒ B
  ⇒-E : ∀ {Γ L M A B} →
    Γ ⊢ L ∶ A ⇒ B →
    Γ ⊢ M ∶ A →
    Γ ⊢ L · M ∶ B
  𝔹-I₁ : ∀ {Γ} →
    Γ ⊢ true ∶ 𝔹
  𝔹-I₂ : ∀ {Γ} →
    Γ ⊢ false ∶ 𝔹
  𝔹-E : ∀ {Γ L M N A} →
    Γ ⊢ L ∶ 𝔹 →
    Γ ⊢ M ∶ A →
    Γ ⊢ N ∶ A →
    Γ ⊢ if L then M else N ∶ A    
\end{code}

## Example type derivations

\begin{code}
typing₁ : ∅ ⊢ not ∶ 𝔹 ⇒ 𝔹
typing₁ = ⇒-I (𝔹-E (Ax refl) 𝔹-I₂ 𝔹-I₁)

typing₂ : ∅ ⊢ two ∶ (𝔹 ⇒ 𝔹) ⇒ 𝔹 ⇒ 𝔹
typing₂ = ⇒-I (⇒-I (⇒-E (Ax refl) (⇒-E (Ax refl) (Ax refl))))
\end{code}

Construction of a type derivation is best done interactively.
We start with the declaration:

    typing₁ : ∅ ⊢ not ∶ 𝔹 ⇒ 𝔹
    typing₁ = ?

Typing C-l causes Agda to create a hole and tell us its expected type.

    typing₁ = { }0
    ?0 : ∅ ⊢ not ∶ 𝔹 ⇒ 𝔹

Now we fill in the hole by typing C-c C-r. Agda observes that
the outermost term in `not` in a `λ`, which is typed using `⇒-I`. The
`⇒-I` rule in turn takes one argument, which Agda leaves as a hole.

    typing₁ = ⇒-I { }0
    ?0 : ∅ , x ∶ 𝔹 ⊢ if ` x then false else true ∶ 𝔹

Again we fill in the hole by typing C-c C-r. Agda observes that the
outermost term is now `if_then_else_`, which is typed using `𝔹-E`. The
`𝔹-E` rule in turn takes three arguments, which Agda leaves as holes.

    typing₁ = ⇒-I (𝔹-E { }0 { }1 { }2)
    ?0 : ∅ , x ∶ 𝔹 ⊢ ` x ∶
    ?1 : ∅ , x ∶ 𝔹 ⊢ false ∶ 𝔹
    ?2 : ∅ , x ∶ 𝔹 ⊢ true ∶ 𝔹

Again we fill in the three holes by typing C-c C-r in each. Agda observes
that `\` x`, `false`, and `true` are typed using `Ax`, `𝔹-I₂`, and
`𝔹-I₁` respectively. The `Ax` rule in turn takes an argument, to show
that `(∅ , x ∶ 𝔹) x = just 𝔹`, which can in turn be specified with a
hole. After filling in all holes, the term is as above.

The entire process can be automated using Agsy, invoked with C-c C-a.


