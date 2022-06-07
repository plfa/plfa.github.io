---
title     : "FreshIdConor: Generation of fresh names"
permalink : /FreshIdConor
---

\begin{code}
module FreshIdConor where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open Eq.≡-Reasoning
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List
  using (List; []; _∷_; _++_; map; foldr; replicate; length; _∷ʳ_)
  renaming (reverse to rev)
open import Data.List.Properties
  using (++-assoc; ++-identityʳ)
  renaming (unfold-reverse to revʳ;
            reverse-++-commute to rev-++;
            reverse-involutive to rev-inv)
open import Data.List.All using (All; []; _∷_)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Unary using (Decidable)

pattern [_]       x        =  x ∷ []
pattern [_,_]     x y      =  x ∷ y ∷ []
pattern [_,_,_]   x y z    =  x ∷ y ∷ z ∷ []
pattern [_,_,_,_] x y z w  =  x ∷ y ∷ z ∷ w ∷ []
\end{code}

## Conor's Break works left-to-right

\begin{code}
module Break {A : Set} where

  data Break (P : A → Set) : List A → Set where
    none : ∀ {xs} → All P xs → Break P xs
    some : ∀ {xs y zs} → All P xs → ¬ P y → Break P (xs ++ [ y ] ++ zs)

  break : ∀ {P : A → Set} (P? : Decidable P) → (xs : List A) → Break P xs
  break P? []                                           =  none []
  break P? (w ∷ ws) with P? w
  ...                  | no ¬Pw                         =  some [] ¬Pw
  ...                  | yes Pw with break P? ws
  ...                              | none Pws           =  none (Pw ∷ Pws)
  ...                              | some Pws ¬Py       =  some (Pw ∷ Pws) ¬Py
\end{code}

## But we want to break lists right-to-left

\begin{code}
module RevBreak {A : Set} where

  open Break {A}

  data RevBreak (P : A → Set) : List A → Set where
    rnone : ∀ {xs} → All P (rev xs) → RevBreak P xs
    rsome : ∀ {zs y xs} → ¬ P y → All P (rev xs) → RevBreak P (zs ++ [ y ] ++ xs)

-- I'd like to do something along the following lines ...

  revBreak : ∀ {P : A → Set} (P? : Decidable P) → (xs : List A) → RevBreak P xs
  revBreak P? ws with break P? (rev ws)
  ... | none {xs} Pxs = ?
--    rewrite rev-inv ws
--    = rnone {xs = rev xs} Pxs
  ... | some {xs} {y} {zs} Pxs ¬Py = ?
--    rewrite rev-inv ?xs | rev-inv ?zs   -- not clear how to bind ?xs and ?zs
--    = rsome {zs = rev zs} {y = y} {xs = rev xs} ¬Py Pxs

-- ... but even the pattern matching gets into trouble
-- It complains that it cannot be sure that
--   xs ++ [ y ] ++ zs = rev ws
-- Doesn't this property follow immediately from the fact that break typechecks?
\end{code}
