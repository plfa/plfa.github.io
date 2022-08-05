module Rev {A : Set} where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open Eq.≡-Reasoning
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List
  using (List; []; _∷_; _++_; map; foldr; replicate; length; _∷ʳ_)
  -- renaming (reverse to rev)
open import Data.List.Properties
  using (++-assoc; ++-identityʳ)
  -- renaming (unfold-reverse to revʳ;
  --           reverse-++-commute to rev-++;
  --           reverse-involutive to rev-inv)
open import Data.List.All using (All; []; _∷_)
open import Data.List.All.Properties
  renaming (++⁺ to _++All_)

pattern [_]       x        =  x ∷ []
pattern [_,_]     x y      =  x ∷ y ∷ []
pattern [_,_,_]   x y z    =  x ∷ y ∷ z ∷ []
pattern [_,_,_,_] x y z w  =  x ∷ y ∷ z ∷ w ∷ []

rev : List A → List A
rev [] =  []
rev (x ∷ xs) =  rev xs ++ [ x ]

rev-++ : ∀ xs ys → rev (xs ++ ys) ≡ rev ys ++ rev xs
rev-++ [] ys =
  begin
    rev ([] ++ ys)
  ≡⟨ sym (++-identityʳ (rev ys)) ⟩
    rev ys ++ rev []
  ∎
rev-++ (x ∷ xs) ys =
  begin
    rev (x ∷ xs ++ ys)
  ≡⟨⟩
    rev (xs ++ ys) ++ [ x ]
  ≡⟨ cong (_++ [ x ]) (rev-++ xs ys) ⟩
    (rev ys ++ rev xs) ++ [ x ]
  ≡⟨ ++-assoc (rev ys) (rev xs) [ x ] ⟩
    rev ys ++ (rev xs ++ [ x ])
  ≡⟨⟩
    rev ys ++ (rev (x ∷ xs))
  ∎

rev-inv : ∀ xs → rev (rev xs) ≡ xs
rev-inv [] =
  begin
    rev (rev [])
  ≡⟨⟩
    []
  ∎
rev-inv (x ∷ xs) =
  begin
    rev (rev (x ∷ xs))
  ≡⟨⟩
    rev (rev xs ++ [ x ])
  ≡⟨ rev-++ (rev xs) [ x ] ⟩
    rev [ x ] ++ rev (rev xs)
  ≡⟨ cong (rev [ x ] ++_) (rev-inv xs) ⟩
    rev [ x ] ++ xs
  ≡⟨⟩
    x ∷ xs
  ∎

revAll : ∀ (P : A → Set) → ∀ {xs} → All P xs → All P (rev xs)
revAll P [] = []
revAll P (Px ∷ Pxs) =  revAll P Pxs ++All [ Px ]
