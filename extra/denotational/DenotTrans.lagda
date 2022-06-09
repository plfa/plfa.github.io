---
title     : "DenotTrans: Denotational Transitivity"
permalink : /DenotTrans/
---

An attempt to reformulate the domain order so that transitivity is
admissible.  It doesn't quite work.

\begin{code}
module plfa.DenotTrans where
\end{code}

## Values

\begin{code}
infixr 7 _↦_
infixl 5 _⊔_

data Value : Set where
  ⊥ : Value
  _↦_ : Value → Value → Value
  _⊔_ : Value → Value → Value
\end{code}

## Domain order

\begin{code}
infix 4 _⊑_

data _⊑_ : Value → Value → Set where

  Bot⊑ : ∀ {v} →
    -----
    ⊥ ⊑ v

  ConjL⊑ : ∀ {u v w}
    → u ⊑ w
    → v ⊑ w
      -----------
    → (u ⊔ v) ⊑ w

  ConjR1⊑ : ∀ {u v w}
    → u ⊑ v
      -----------
    → u ⊑ (v ⊔ w)

  ConjR2⊑ : ∀ {u v w}
    → u ⊑ w
      -----------
    → u ⊑ (v ⊔ w)

  Fun⊑ : ∀ {u u′ v v′}
       → u′ ⊑ u
       → v ⊑ v′
         -------------------
       → (u ↦ v) ⊑ (u′ ↦ v′)

  Dist⊑ : ∀{t u v w}
       → t ↦ u ⊑ w
       → t ↦ v ⊑ w
         ---------------
       → t ↦ (u ⊔ v) ⊑ w
\end{code}

This relation is reflexive and transitive.
\begin{code}
refl⊑ : ∀ {v} → v ⊑ v
refl⊑ {⊥} = Bot⊑
refl⊑ {v ↦ w} = Fun⊑ refl⊑ refl⊑
refl⊑ {v ⊔ w} = ConjL⊑ (ConjR1⊑ refl⊑) (ConjR2⊑ refl⊑)

trans⊑ : ∀ {u v w}
     → u ⊑ v
     → v ⊑ w
       --------
     → u ⊑ w
trans⊑ Bot⊑ vw = Bot⊑
trans⊑ (ConjL⊑ tv uv) vw = ConjL⊑ (trans⊑ tv vw) (trans⊑ uv vw)
trans⊑ (ConjR1⊑ tu) (ConjL⊑ uw vw) = trans⊑ tu uw
trans⊑ (ConjR1⊑ tu) (ConjR1⊑ uvw) = ConjR1⊑ (trans⊑ (ConjR1⊑ tu) uvw)
trans⊑ (ConjR1⊑ tu) (ConjR2⊑ uvw) = ConjR2⊑ (trans⊑ (ConjR1⊑ tu) uvw)
trans⊑ (ConjR2⊑ tv) (ConjL⊑ uw vw) = trans⊑ tv vw
trans⊑ (ConjR2⊑ tv) (ConjR1⊑ uvw) = ConjR1⊑ (trans⊑ (ConjR2⊑ tv) uvw)
trans⊑ (ConjR2⊑ tv) (ConjR2⊑ uvw) = ConjR2⊑ (trans⊑ (ConjR2⊑ tv) uvw)
trans⊑ (Fun⊑ u′u vv′) (ConjR1⊑ u′v′w) = ConjR1⊑ (trans⊑ (Fun⊑ u′u vv′) u′v′w)
trans⊑ (Fun⊑ u′u vv′) (ConjR2⊑ u′v′w) = ConjR2⊑ (trans⊑ (Fun⊑ u′u vv′) u′v′w)
trans⊑ (Fun⊑ u′u vv′) (Fun⊑ u″u′ v′v″) = Fun⊑ (trans⊑ u″u′ u′u) (trans⊑ vv′ v′v″)
trans⊑ (Fun⊑ u′u vv′v″) (Dist⊑ u′v′w u′v″w) = {!!}
trans⊑ (Dist⊑ tuw tvw) wx = Dist⊑ (trans⊑ tuw wx) (trans⊑ tvw wx)
\end{code}

There is one hole in the proof that I think it may be impossible to fill.
Here is a diagram of the relevant case.

    u′ ⊑ u                       u′ ↦ v′ ⊑ w
    v ⊑ v′ ⊔ v″                  u′ ↦ v″ ⊑ w
    ---------------------Fun⊑    ----------------Dist⊑
    u ↦ v ⊑ u′ ↦ v′ ⊔ v″         u′ ↦ v′ ⊔ v″ ⊑ w
    ---------------------------------------------Trans⊑
    u ↦ v ⊑ w
