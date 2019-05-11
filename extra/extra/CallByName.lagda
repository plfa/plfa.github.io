\begin{code}
module extra.CallByName where
\end{code}

## Imports

\begin{code}
open import extra.LambdaReduction
  using (_—→_; ξ₁; ξ₂; β; ζ; _—↠_; _—→⟨_⟩_; _[])
open import plfa.Untyped
  using (Context; _⊢_; ★; _∋_; ∅; _,_; Z; S_; `_; ƛ_; _·_; rename; subst;
         ext; exts; _[_]; subst-zero)
open import plfa.Adequacy
open import plfa.Denotational
open import plfa.Soundness
open import extra.Substitution

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum
open import Data.Nat
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Data.Unit
open import Relation.Nullary using (Dec; yes; no)
open import Function using (_∘_)
\end{code}

## Logical Relation between CBN Closures and Terms

\begin{code}
𝔹 : Clos → (∅ ⊢ ★) → Set
ℍ : ∀{Γ} → ClosEnv Γ → Subst Γ ∅ → Set

𝔹 (clos {Γ} M γ) N = Σ[ σ ∈ Subst Γ ∅ ] ℍ γ σ × (N ≡ subst σ M)

ℍ γ σ = ∀{x} → 𝔹 (γ x) (σ x)

ext-subst : ∀{Γ Δ} → Subst Γ Δ → Δ ⊢ ★ → Subst (Γ , ★) Δ
ext-subst{Γ}{Δ} σ N {A} = (subst (subst-zero N)) ∘ (exts σ)

ℍ-ext : ∀ {Γ} {γ : ClosEnv Γ} {σ : Subst Γ ∅} {c} {N : ∅ ⊢ ★}
      → ℍ γ σ  →  𝔹 c N
        --------------------------------
      → ℍ (γ ,' c) ((subst (subst-zero N)) ∘ (exts σ))
ℍ-ext {Γ} {γ} {σ} g e {Z} = e
ℍ-ext {Γ} {γ} {σ}{c}{N} g e {S x} = G g
  where
      eq : ext-subst σ N (S x) ≡ σ x
      eq =
        begin
          (subst (subst-zero N)) (exts σ (S x))
        ≡⟨⟩
          ((subst (subst-zero N)) ∘ (rename S_)) (σ x)
        ≡⟨ rename-subst{M = σ x} ⟩
          (subst ((subst-zero N) ∘ S_)) (σ x)        
        ≡⟨ sub-id ⟩
          σ x
        ∎
      G : 𝔹 (γ x) (σ x) → 𝔹 (γ x) (ext-subst σ N (S x))
      G b rewrite eq = b
\end{code}

\begin{code}
—↠-trans : ∀{Γ}{L M N : Γ ⊢ ★}
         → L —↠ M
         → M —↠ N
         → L —↠ N
—↠-trans (M []) mn = mn
—↠-trans (L —→⟨ r ⟩ lm) mn = L —→⟨ r ⟩ (—↠-trans lm mn)
\end{code}

\begin{code}
—→-app-cong : ∀{Γ}{L L' M : Γ ⊢ ★}
            → L —→ L'
            → L · M —→ L' · M
—→-app-cong (ξ₁ ll') = ξ₁ (—→-app-cong ll')
—→-app-cong (ξ₂ ll') = ξ₁ (ξ₂ ll')
—→-app-cong β = ξ₁ β
—→-app-cong (ζ ll') = ξ₁ (ζ ll')

—↠-app-cong : ∀{Γ}{L L' M : Γ ⊢ ★}
            → L —↠ L'
            → L · M —↠ L' · M
—↠-app-cong {Γ}{L}{L'}{M} (L []) = (L · M) []
—↠-app-cong {Γ}{L}{L'}{M} (L —→⟨ r ⟩ ll') =
    L · M —→⟨ —→-app-cong r ⟩ (—↠-app-cong ll')
\end{code}

\begin{code}
cbn-soundness : ∀{Γ}{γ : ClosEnv Γ}{σ : Subst Γ ∅}{M : Γ ⊢ ★}{c : Clos}
              → γ ⊢ M ⇓ c → ℍ γ σ
              → Σ[ N ∈ ∅ ⊢ ★ ] (subst σ M —↠ N) × 𝔹 c N
cbn-soundness {γ = γ} (⇓-var{x = x} eq d) h
    with γ x | h {x} | eq
... | clos M' γ' | ⟨ σ' , ⟨ h' , r ⟩ ⟩ | refl
    with cbn-soundness{σ = σ'} d h'
... | ⟨ N , ⟨ r' , bn ⟩ ⟩ rewrite r =    
      ⟨ N , ⟨ r' , bn ⟩ ⟩
cbn-soundness {Γ} {γ} {σ} {.(ƛ _)} {.(clos (ƛ _) γ)} (⇓-lam{M = N}) h =
   ⟨ subst σ (ƛ N) , ⟨ subst σ (ƛ N) [] , ⟨ σ , ⟨ h , refl ⟩ ⟩ ⟩ ⟩
cbn-soundness {Γ} {γ} {σ} {.(_ · _)} {c}
    (⇓-app{L = L}{M = M}{Δ = Δ}{δ = δ}{N = N} d₁ d₂) h
    with cbn-soundness{σ = σ} d₁ h
... | ⟨ L' , ⟨ σL—↠L' , ⟨ σ₁ , ⟨ Hδσ₁ , eq ⟩ ⟩ ⟩ ⟩ rewrite eq
    with cbn-soundness{σ = ext-subst σ₁ (subst σ M)} d₂
           (λ {x} → ℍ-ext{Δ}{σ = σ₁} Hδσ₁ (⟨ σ , ⟨ h , refl ⟩ ⟩){x})
       | β{∅}{subst (exts σ₁) N}{subst σ M}
... | ⟨ N' , ⟨ r' , bl ⟩ ⟩ | r 
    rewrite sub-sub{M = N}{σ₁ = exts σ₁}{σ₂ = subst-zero (subst σ M)} =
    let rs = (ƛ subst (exts σ₁) N) · subst σ M —→⟨ r ⟩ r' in
    ⟨ N' , ⟨ —↠-trans (—↠-app-cong σL—↠L') rs , bl ⟩ ⟩
\end{code}
