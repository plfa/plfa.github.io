module experimental.itaiz.Permutation where

open import Data.List using (List; []; _∷_; [_]; _++_)

open import experimental.itaiz.Isomorphism

infix 0 _↭_

data _↭_ {A : Set} : List A → List A → Set where
  Ø : [] ↭ []
  _∷_ : (x : A) → {xs ys : List A} → (xs ↭ ys) → (x ∷ xs) ↭ (x ∷ ys)
  swap : (x y : A) → {xs : List A} → (x ∷ y ∷ xs) ↭ (y ∷ x ∷ xs)
  _⊙_ : {xs ys zs : List A} → xs ↭ ys → ys ↭ zs → xs ↭ zs

variable
  A : Set
  x : A
  xs ys zs : List A

↭-refl : xs ↭ xs
↭-refl {A} {[]} = Ø
↭-refl {A} {x ∷ xs} = x ∷ ↭-refl

↭-sym : xs ↭ ys → ys ↭ xs
↭-sym Ø = Ø
↭-sym (x ∷ xs↭ys) = x ∷ ↭-sym xs↭ys
↭-sym (swap x y) = swap y x
↭-sym (xs↭ys ⊙ ys↭zs) = ↭-sym ys↭zs ⊙ ↭-sym xs↭ys

↭-trans : xs ↭ ys → ys ↭ zs → xs ↭ zs
↭-trans xs↭ys ys↭zs = xs↭ys ⊙ ys↭zs

module ↭-Reasoning {A : Set} where
  open *-Reasoning
    (_↭_ {A})
    (record { *-refl = ↭-refl ; *-trans = ↭-trans })
    renaming (*-begin_ to ↭-begin_ ; _*⟨_⟩_ to _↭⟨_⟩_; _*⟨⟩_ to _↭⟨⟩_;_*-∎ to _↭-∎)
    public

Perm : (List A → List A) → Set
Perm {A} f = (xs : List A) → f xs ↭ xs

swap-ends : (x ∷ xs) ↭ (xs ++ [ x ])
swap-ends {xs = []} = ↭-refl
swap-ends {x = x} {xs = y ∷ xs} =
  ↭-begin
    x ∷ y ∷ xs
  ↭⟨ swap x y ⟩
    y ∷ x ∷ xs
  ↭⟨ y ∷ swap-ends ⟩
    y ∷ xs ++ [ x ]
  ↭-∎
  where open ↭-Reasoning

reverse : List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

reverse-perm : Perm (reverse {A})
reverse-perm [] = Ø
reverse-perm (x ∷ xs) =
  ↭-begin
    reverse (x ∷ xs)
  ↭⟨⟩
    (reverse xs ++ [ x ])
  ↭⟨ ↭-sym swap-ends ⟩
    x ∷ reverse xs
  ↭⟨ x ∷ reverse-perm xs ⟩
    x ∷ xs
  ↭-∎
  where open ↭-Reasoning
