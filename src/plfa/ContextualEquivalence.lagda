---
title     : "Denotational equality implies contextual equivalence"
layout    : page
prev      : /Adequacy/
permalink : /ContextualEquivalence/
next      : /Acknowledgements/
---

\begin{code}
module plfa.ContextualEquivalence where
\end{code}

## Imports

\begin{code}
open import plfa.Untyped
  using (Context; _⊢_; ★; _∋_; ∅; _,_; Z; S_; `_; ƛ_; _·_; subst; exts)
open import plfa.Substitution using (sub-id; ids)
open import plfa.LambdaReduction using (_—↠_)
open import plfa.Denotational using (ℰ; _≃_; ≃-sym; ≃-trans; _iff_)
open import plfa.Compositional using (Ctx; plug; compositionality)
open import plfa.Soundness using (soundness)
open import plfa.Adequacy using (adequacy)
open import plfa.CallByName using ( ClosEnv; ∅'; clos; _⊢_⇓_; cbn→reduce)

open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
\end{code}


## Denotational equivalence implies contextual equivalence

\begin{code}
terminates : ∀{Γ} → (M : Γ ⊢ ★) → Set
terminates {Γ} M = Σ[ N ∈ (Γ , ★ ⊢ ★) ] (M —↠ ƛ N)
\end{code}

\begin{code}
_≅_ : ∀{Γ} → (M N : Γ ⊢ ★) → Set
(_≅_ {Γ} M N) = ∀ {C : Ctx Γ ∅}
                → (terminates (plug C M)) iff (terminates (plug C N))
\end{code}

\begin{code}
denot-equal-terminates : ∀{Γ} {M N : Γ ⊢ ★} {C : Ctx Γ ∅}
  → ℰ M ≃ ℰ N  →  terminates (plug C M)
    -----------------------------------
  → terminates (plug C N)
denot-equal-terminates {Γ}{M}{N}{C} eq ⟨ N' , CM—↠CƛN' ⟩ =
  let ℰCM≃ℰCƛN' = soundness CM—↠CƛN' in
  let ℰCM≃ℰCN = compositionality{Γ = Γ}{Δ = ∅}{C = C} eq in
  let ℰCN≃ℰCƛN' = ≃-trans (≃-sym ℰCM≃ℰCN) ℰCM≃ℰCƛN' in
    cbn→reduce (proj₂ (proj₂ (proj₂ (adequacy ℰCN≃ℰCƛN'))))
\end{code}

\begin{code}
denot-equal-contex-equal : ∀{Γ} {M N : Γ ⊢ ★}
  → ℰ M ≃ ℰ N
    ---------
  → M ≅ N
denot-equal-contex-equal{Γ}{M}{N} eq {C} =
   ⟨ (λ tm → denot-equal-terminates eq tm) ,
     (λ tn → denot-equal-terminates (≃-sym eq) tn) ⟩
\end{code}
