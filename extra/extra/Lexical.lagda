## Lexical order

\begin{code}
Rel : Set → Set₁
Rel A  =  A → A → Set

Reflexive : ∀ {A : Set} → Rel A → Set
Reflexive {A} _≺_  =  ∀ {x : A}
    -----
  → x ≺ x

Trans : ∀ {A : Set} → Rel A → Set
Trans {A} _≺_  =  ∀ {x y z : A}
  → x ≺ y
  → y ≺ z
    -----
  → x ≺ z

Antirefl : ∀ {A : Set} → Rel A → Set
Antirefl {A} _≺_  =  ∀ {x y : A}
  → x ≺ y
    ---------
  → ¬ (x ≡ y)

module Lexical (A : Set) (_≺_ : Rel A) (≺-trans : Trans _≺_) where

  infix 4 _≪_

  data _≪_ : Rel (List A) where

    halt : ∀ {x : A} {xs : List A}
        -------
      → [] ≪ x ∷ xs

    this : ∀ {x y : A} {xs ys : List A}
      → x ≺ y
        ----------------
      → x ∷ xs ≪ y ∷ ys

    next : ∀ {x : A} {xs ys : List A}
      → xs ≪ ys
        ---------------
      → x ∷ xs ≪ x ∷ ys

  ≪-trans : Trans _≪_
  ≪-trans halt         (this _)      =  halt
  ≪-trans halt         (next _)      =  halt
  ≪-trans (this x≺y)   (this y≺z)    =  this (≺-trans x≺y y≺z)
  ≪-trans (this x≺y)   (next ys≪zs)  =  this x≺y
  ≪-trans (next xs≪ys) (this x≺y)    =  this x≺y
  ≪-trans (next xs≪ys) (next ys≪zs)  =  next (≪-trans xs≪ys ys≪zs)

  ≪-antirefl : Antirefl _≺_ → Antirefl _≪_
  ≪-antirefl ≺-antirefl halt ()
  ≪-antirefl ≺-antirefl (this x≺y) refl = ⊥-elim (≺-antirefl x≺y refl)
  ≪-antirefl ≺-antirefl (next xs≪ys) refl = ⊥-elim (≪-antirefl ≺-antirefl xs≪ys refl)

\end{code}
