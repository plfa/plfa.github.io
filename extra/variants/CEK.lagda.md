CEK machine

Siek, Thiemann, Wadler, 2 Aug 2022

[Currently not compiling]

```
module variants.CEK where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Relation.Binary.PropositionalEquality
     using (_≡_; _≢_; refl; trans; sym; cong; cong₂; cong-app; subst; inspect)
     renaming ([_] to [[_]])
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
open import variants.Frame
```

Evaluation context as a stack of frames

```
data _==>_ : Type → Type → Set where

  [] : A ==> A

  _∷_ :
      Γ ⊢ A => B
    → B ==> C
      -----------
    → A ==> C

variable
  K : A ==> B
```

Extending a substitution

```
_►_ :
    Γ →ˢ Δ
  → Δ ⊢ A
    ----------
  → Γ ▷ A →ˢ Δ
(σ ► M) Z      =  M
(σ ► M) (S x)  =  σ x
```

CEK configuration
```
record CEK (A : Type) : Set where
  constructor cek
  field
    {Γ′} : Env
    {B′} : Type
    control : Γ′ ⊢ B′
    environment : Γ′ →ˢ ∅
    kontinuation : Γ′ ⊢ B′ ==> A
```

CEK transitions
```
data _~~>_ : CEK A → CEK A → Set where

  CEK-ξ-□· :
      ------------------------------------------------
      cek (L · M) σ K ~~> cek L σ ((□· M) ∷ K)

  CEK-ξ-·□ :
      (v : Value V)
      -----------------------------------------------------
    → cek V σ ((□· M) ∷ K) ~~> cek M σ ((v ·□) ∷ K)

  CEK-β-ƛ :
      (v : Value V)
      --------------------------------------------------------
    → cek V σ (((ƛ N) ·□) ∷ K) ~~> cek N (σ ► V) (▵ K)

  CEK-ξ-`suc□ :
      ------------------------------------------------
      cek (`suc M) σ K ~~> cek M σ (`suc□ ∷ K)

  CEK-κ :
      (v : Value V)
      ------------------------------------------------
    → cek V σ (`suc□ ∷ K) ~~> cek (`suc V) σ K

  CEK-ξ-case□ :
      ----------------------------------------------------------
      cek (case L M N) σ K ~~> cek L σ ((case□ M N) ∷ K)

  CEK-β-zero :
      ---------------------------------------------------
      cek `zero σ ((case□ M N) ∷ K) ~~> cek M σ K

  CEK-β-suc :
      (v : Value V)
      ----------------------------------------------------------------
    → cek (`suc V) σ ((case□ M N) ∷ K) ~~> cek N (σ ► V) (▵ K)

  CEK-μ-· :
     (v : Value V)
     -----------------------------------------------------------------------
   → cek V σ (((μ N) ·□) ∷ K) ~~> cek N (σ ► (μ N)) (▵ ((□· V) ∷ K))

  CEK-μ-case :
     -----------------------------------------------------------------------------
     cek (μ L) σ ((case□ M N) ∷ K) ~~> cek L (σ ► (μ L)) ((case□ M N) ∷ K)
```
