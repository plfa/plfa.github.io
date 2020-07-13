module Issue488 where

open import Data.Product using (∃-syntax; -,_; _×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

module CounterExample where

  data Term : Set where
    A B C D : Term

  data _—→_ : (M N : Term) → Set where
    B—→C : B —→ C
    C—→B : C —→ B
    B—→A : B —→ A
    C—→D : C —→ D

  infix  2 _—↠_
  infix  1 begin_
  infixr 2 _—→⟨_⟩_
  infix  3 _∎

  data _—↠_ : Term → Term → Set where
    _∎ : ∀ M
      ---------
      → M —↠ M

    _—→⟨_⟩_ : ∀ L {M N}
      → L —→ M
      → M —↠ N
        ---------
      → L —↠ N

  begin_ : ∀ {M N}
    → M —↠ N
      ------
    → M —↠ N
  begin M—↠N = M—↠N

  diamond : ∀ {L M N}
    → ((L —→ M) × (L —→ N))
      -----------------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P))
  diamond (B—→A , B—→A) = -, ((A ∎) , (A ∎))
  diamond (C—→B , C—→B) = -, ((B ∎) , (B ∎))
  diamond (B—→C , B—→C) = -, ((C ∎) , (C ∎))
  diamond (C—→D , C—→D) = -, ((D ∎) , (D ∎))
  diamond (B—→C , B—→A) = -, ((begin C —→⟨ C—→B ⟩ B —→⟨ B—→A ⟩ A ∎) , (A ∎))
  diamond (C—→B , C—→D) = -, ((begin B —→⟨ B—→C ⟩ C —→⟨ C—→D ⟩ D ∎) , (D ∎))
  diamond (B—→A , B—→C) = -, ((A ∎) , (begin C —→⟨ C—→B ⟩ B —→⟨ B—→A ⟩ A ∎))
  diamond (C—→D , C—→B) = -, ((D ∎) , (begin B —→⟨ B—→C ⟩ C —→⟨ C—→D ⟩ D ∎))

  A—↠A : ∀ {P} → A —↠ P → P ≡ A
  A—↠A (.A ∎) = refl

  D—↠D : ∀ {P} → D —↠ P → P ≡ D
  D—↠D (.D ∎) = refl

  ¬confluence : ¬ (∀ {L M N}
    → ((L —↠ M) × (L —↠ N))
      -----------------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P)))
  ¬confluence confluence
    with confluence ( (begin B —→⟨ B—→A ⟩ A ∎)
                    , (begin B —→⟨ B—→C ⟩ C —→⟨ C—→D ⟩ D ∎) )
  ... | (P , (A—↠P , D—↠P))
    with trans (sym (A—↠A A—↠P)) (D—↠D D—↠P)
  ... | ()

module DeterministicImpliesDiamondPropertyAndConfluence where

  infix  2 _—↠_
  infix  1 begin_
  infixr 2 _—→⟨_⟩_
  infix  3 _∎

  postulate
    Term : Set
    _—→_ : Term → Term → Set

  postulate
    deterministic : ∀ {L M N}
      → L —→ M
      → L —→ N
      ------
      → M ≡ N

  data _—↠_ : Term → Term → Set where
    _∎ : ∀ M
      ---------
      → M —↠ M

    _—→⟨_⟩_ : ∀ L {M N}
      → L —→ M
      → M —↠ N
        -------
      → L —↠ N

  begin_ : ∀ {M N}
    → M —↠ N
      ------
    → M —↠ N
  begin M—↠N = M—↠N

  diamond : ∀ {L M N}
    → ((L —→ M) × (L —→ N))
      --------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P))
  diamond (L—→M , L—→N)
    rewrite deterministic L—→M L—→N = -, ((_ ∎) , (_ ∎))

  confluence : ∀ {L M N}
    → (L —↠ M)
    → (L —↠ N)
      --------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P))
  confluence {L} {.L} { N} (.L ∎) L—↠N = -, (L—↠N , (N ∎))
  confluence {L} { M} {.L} L—↠M (.L ∎) = -, ((M ∎) , L—↠M)
  confluence {L} { M} { N} (.L —→⟨ L—→M′ ⟩ M′—↠M) (.L —→⟨ L—→N′ ⟩ N′—↠N)
    rewrite deterministic L—→M′ L—→N′ = confluence M′—↠M N′—↠N
