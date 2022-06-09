---
title     : "SystemF: Inherently typed System F"
permalink : /SystemF/
---

\begin{code}
module plfa.SystemF where
\end{code}

## Fixity declarations

To begin, we get all our infix declarations out of the way.
We list separately operators for judgments, types, and terms.
\begin{code}
infix  4 _∋⋆_
infix  4 _∋_
infix  4 _⊢⋆_
infix  4 _⊢_
infixl 5 _,⋆_
infixl 5 _,_

infix  6 Π_
infixr 7 _⇒_

infix  5 ƛ_
infixl 7 _·_
infix  9 S_
\end{code}

## Kinds

The only kind is `★`, the kind of types.
\begin{code}
data Kind : Set where
  ★ : Kind
\end{code}
Let `J`, `K` range over kinds.

## Type contexts

A type context is either empty or extends a type
context by a type variable of a given kind.
\begin{code}
data Ctx⋆ : Set where
  ∅ : Ctx⋆
  _,⋆_ : Ctx⋆ → Kind → Ctx⋆
\end{code}
Let `Φ`, `Ψ` range over type contexts.

## Type variables

A type variable is indexed by its context and kind.
\begin{code}
data _∋⋆_ : Ctx⋆ → Kind → Set where

  Z : ∀ {Φ J}
      -------------
    → Φ ,⋆ J ∋⋆ J

  S_ : ∀ {Φ J K}
    → Φ ∋⋆ J
      -------------
    → Φ ,⋆ K ∋⋆ J
\end{code}
Let `α`, `β` range over type variables.

## Types

A type is indexed by its context and kind.  A type is either a type
variable, a pi type, or a function type.
\begin{code}
data _⊢⋆_ : Ctx⋆ → Kind → Set where

  `_ : ∀ {Φ J}
    → Φ ∋⋆ J
      --------
    → Φ ⊢⋆ J

  Π_ : ∀ {Φ K}
    → Φ ,⋆ K ⊢⋆ ★
      -----------
    → Φ ⊢⋆ ★

  _⇒_ : ∀ {Φ}
    → Φ ⊢⋆ ★
    → Φ ⊢⋆ ★
      ------
    → Φ ⊢⋆ ★
\end{code}
Let `A`, `B`, `C` range over types.

## Type renaming

A type renaming is a mapping of type variables to type variables.

Extending a type renaming — used when going under a binder.
\begin{code}
ext⋆ : ∀ {Φ Ψ} → (∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
    ------------------------------------------
  → (∀ {J K} → Φ ,⋆ K ∋⋆ J → Ψ ,⋆ K ∋⋆ J)
ext⋆ ρ Z      =  Z
ext⋆ ρ (S α)  =  S (ρ α)
\end{code}

Apply a type renaming to a type.
\begin{code}
rename⋆ : ∀ {Φ Ψ}
  → (∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
    ----------------------------
  → (∀ {J} → Φ ⊢⋆ J → Ψ ⊢⋆ J)
rename⋆ ρ (` α)    =  ` (ρ α)
rename⋆ ρ (Π B)    =  Π (rename⋆ (ext⋆ ρ) B)
rename⋆ ρ (A ⇒ B)  =  rename⋆ ρ A ⇒ rename⋆ ρ B
\end{code}

Weakening is a special case of renaming.
\begin{code}
weaken⋆ : ∀ {Φ J K}
  → Φ ⊢⋆ J
    -------------
  → Φ ,⋆ K ⊢⋆ J
weaken⋆ = rename⋆ S_
\end{code}


## Type substitution

A type substitution is a mapping of type variables to types.

Extending a type substitution — used when going under a binder.
\begin{code}
exts⋆ : ∀ {Φ Ψ} → (∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
    -------------------------------------------
  → (∀ {J K} → Φ ,⋆ K ∋⋆ J → Ψ ,⋆ K ⊢⋆ J)
exts⋆ σ Z      =  ` Z
exts⋆ σ (S α)  =  weaken⋆ (σ α)
\end{code}

Apply a type substitution to a type.
\begin{code}
subst⋆ : ∀ {Φ Ψ}
  → (∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
    -----------------------------
  → (∀ {J} → Φ ⊢⋆ J → Ψ ⊢⋆ J)
subst⋆ σ (` α)     =  σ α
subst⋆ σ (Π B)     =  Π (subst⋆ (exts⋆ σ) B)
subst⋆ σ (A ⇒ B)   =  subst⋆ σ A ⇒ subst⋆ σ B
\end{code}

A special case is substitution a type for the
outermost free variable.
\begin{code}
_[_]⋆ : ∀ {Φ J K}
        → Φ ,⋆ K ⊢⋆ J
        → Φ ⊢⋆ K
          -------------
        → Φ ⊢⋆ J
_[_]⋆ {Φ} {J} {K} B A =  subst⋆ {Φ ,⋆ K} {Φ} σ {J} B
  where
  σ : ∀ {J} → Φ ,⋆ K ∋⋆ J → Φ ⊢⋆ J
  σ Z      =  A
  σ (S α)  =  ` α
\end{code}


## Contexts and erasure

We need to mutually define contexts and their
erasure to type contexts.
\begin{code}
data Ctx : Set
∥_∥ : Ctx → Ctx⋆
\end{code}

A context is either empty, or extends a context by
a type variable of a given kind, or extends a context
by a variable of a given type.
\begin{code}
data Ctx where
  ∅ : Ctx
  _,⋆_ : Ctx → Kind → Ctx
  _,_ : ∀ {J} (Γ : Ctx) → ∥ Γ ∥ ⊢⋆ J → Ctx
\end{code}
Let `Γ` range over contexts.  In the last rule,
the type is indexed by the erasure of the previous
context to a type context and a kind.

The erasure of a context is a type context.
\begin{code}
∥ ∅ ∥       =  ∅
∥ Γ ,⋆ J ∥  =  ∥ Γ ∥ ,⋆ J
∥ Γ , A ∥   =  ∥ Γ ∥
\end{code}

## Variables

A variable is indexed by its context and type.
\begin{code}
data _∋_ : ∀ {J} (Γ : Ctx) → ∥ Γ ∥ ⊢⋆ J → Set where

  Z : ∀ {Γ J} {A : ∥ Γ ∥ ⊢⋆ J}
      ----------
    → Γ , A ∋ A

  S_ : ∀ {Γ J K} {A : ∥ Γ ∥ ⊢⋆ J} {B : ∥ Γ ∥ ⊢⋆ K}
    → Γ ∋ A
      ----------
    → Γ , B ∋ A

  T_ : ∀ {Γ J K} {A : ∥ Γ ∥ ⊢⋆ J}
    → Γ ∋ A
      -------------------
    → Γ ,⋆ K ∋ weaken⋆ A
\end{code}
Let `x`, `y` range over variables.

## Terms

A term is indexed over by its context and type.  A term is a variable,
an abstraction, an application, a type abstraction, or a type
application.
\begin{code}
data _⊢_ : ∀ {J} (Γ : Ctx) → ∥ Γ ∥ ⊢⋆ J → Set where

  `_ : ∀ {Γ J} {A : ∥ Γ ∥ ⊢⋆ J}
    → Γ ∋ A
      ------
    → Γ ⊢ A

  ƛ_ : ∀ {Γ A B}
    → Γ , A ⊢ B
      -----------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      -----------
    → Γ ⊢ B

  Λ_ : ∀ {Γ K} {B : ∥ Γ ∥ ,⋆ K ⊢⋆ ★}
    → Γ ,⋆ K ⊢ B
      ----------
    → Γ ⊢ Π B

  _·⋆_ : ∀ {Γ B}
    → Γ ⊢ Π B
    → (A : ∥ Γ ∥ ⊢⋆ ★)
      ---------------
    → Γ ⊢ B [ A ]⋆
\end{code}

## Remainder

The development continues from here as in
Chapter [DeBruijn][plfa.DeBruijn],
defining renaming and substitution on terms and introducing reduction
rules for terms, proving progress, and applying progress to derive an
evaluator.
