\begin{code}
module extra.CallByName where
\end{code}

## Imports

\begin{code}
open import plfa.Untyped
  using (Context; _⊢_; ★; _∋_; ∅; _,_; Z; S_; `_; ƛ_; _·_; rename; subst;
         _—↠_; _—→⟨_⟩_; _—→_; ξ₁; ξ₂; β; ζ; ap; ext; exts; _[_]; subst-zero)
  renaming (_∎ to _[])
open import plfa.Denotational
open import plfa.Soundness
open import plfa.Adequacy

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Data.Unit
open import Relation.Nullary using (Dec; yes; no)
open import Function using (_∘_)
\end{code}

## Soundness of call-by-name evaluation with respect to reduction


\begin{code}
compose-exts : ∀{Γ Δ Δ'}{ρ : Rename Γ Δ}{σ : Subst Δ Δ'}
             → (exts σ) ∘ (ext ρ) ≡ exts (σ ∘ ρ)
compose-exts{Γ}{Δ}{Δ'}{ρ}{σ} = extensionality lemma
  where lemma : (x : Γ , ★ ∋ ★)
              → ((exts σ) ∘ (ext ρ)) x ≡ exts (σ ∘ ρ) x
        lemma Z = refl
        lemma (S x) = refl


same-subst : ∀{Γ Δ} → Subst Γ Δ → Subst Γ Δ → Set
same-subst{Γ}{Δ} σ σ' = ∀{x : Γ ∋ ★} → σ x ≡ σ' x

same-subst-ext : ∀{Γ Δ}{σ σ' : Subst Γ Δ}
   → same-subst σ σ'
   → same-subst (exts σ {B = ★}) (exts σ' )
same-subst-ext ss {x = Z} = refl
same-subst-ext ss {x = S x} = cong (rename (λ {A} → S_)) ss

subst-equal : ∀{Γ Δ}{σ σ' : Subst Γ Δ}{M : Γ ⊢ ★}
        → same-subst σ σ' 
         → subst σ M ≡ subst σ' M
subst-equal {Γ} {Δ} {σ} {σ'} {` x} ss = ss
subst-equal {Γ} {Δ} {σ} {σ'} {ƛ M} ss =
   let ih = subst-equal {Γ = Γ , ★} {Δ = Δ , ★}
            {σ = exts σ}{σ' = exts σ'} {M = M}
            (λ {x} → same-subst-ext {Γ}{Δ}{σ}{σ'} ss {x}) in
   cong ƛ_ ih
subst-equal {Γ} {Δ} {σ} {σ'} {L · M} ss =
   let ih1 = subst-equal {Γ} {Δ} {σ} {σ'} {L} ss in
   let ih2 = subst-equal {Γ} {Δ} {σ} {σ'} {M} ss in
   cong₂ _·_ ih1 ih2

rename-subst : ∀{Γ Δ Δ'}{M : Γ ⊢ ★}{ρ : Rename Γ Δ}{σ : Subst Δ Δ'}
             → ((subst σ) ∘ (rename ρ)) M ≡ subst (σ ∘ ρ) M
rename-subst {M = ` x} = refl
rename-subst {Γ}{Δ}{Δ'}{M = ƛ M}{ρ}{σ} =
  let ih : subst (exts σ) (rename (ext ρ) M)
           ≡ subst ((exts σ) ∘ ext ρ) M
      ih = rename-subst {M = M}{ρ = ext ρ}{σ = exts σ} in
  cong ƛ_ g
  where
        e : (exts σ) ∘ (ext ρ) ≡ exts (σ ∘ ρ) {★}{★}
        e = compose-exts{Γ}{Δ}{Δ'}{ρ}{σ}
        ss : same-subst ((exts σ) ∘ (ext ρ)) (exts (σ ∘ ρ))
        ss {Z} = refl
        ss {S x} = refl
        h : subst ((exts σ) ∘ (ext ρ)) M ≡ subst (exts (σ ∘ ρ)) M
        h = subst-equal{Γ , ★}{Δ = Δ' , ★}{σ = ((exts σ) ∘ (ext ρ))}
             {σ' = (exts (σ ∘ ρ))}{M = M} (λ {x} → ss {x})
        g : subst (exts σ) (rename (ext ρ) M)
           ≡ subst (exts (σ ∘ ρ)) M
        g =
           begin
             subst (exts σ) (rename (ext ρ) M)
           ≡⟨ rename-subst {M = M}{ρ = ext ρ}{σ = exts σ} ⟩
             subst ((exts σ) ∘ ext ρ) {★} M
           ≡⟨ h ⟩
             subst (exts (σ ∘ ρ)) {★} M
           ∎
rename-subst {M = L · M} =
   cong₂ _·_ (rename-subst{M = L}) (rename-subst{M = M})


inc-subst-zero-id : ∀{Γ}{M : Γ ⊢ ★}{x : Γ ∋ ★} → ((subst-zero M) ∘ S_) x ≡ ` x
inc-subst-zero-id {.(_ , ★)} {M} {Z} = refl
inc-subst-zero-id {.(_ , _)} {M} {S x} = refl

is-id-subst : ∀{Γ} → Subst Γ Γ → Set
is-id-subst {Γ} σ = ∀{x : Γ ∋ ★} → σ x ≡ ` x

is-id-exts : ∀{Γ} {σ : Subst Γ Γ}
           → is-id-subst σ
           → is-id-subst (exts σ {B = ★})
is-id-exts id {Z} = refl
is-id-exts{Γ}{σ} id {S x} rewrite id {x} = refl

subst-id : ∀{Γ} {M : Γ ⊢ ★} {σ : Subst Γ Γ}
         → is-id-subst σ
         → subst σ M ≡ M
subst-id {M = ` x} {σ} id = id
subst-id {M = ƛ M} {σ} id = cong ƛ_ (subst-id (is-id-exts id))
subst-id {M = L · M} {σ} id = cong₂ _·_ (subst-id id) (subst-id id)
\end{code}


\begin{code}
𝔹 : Clos → (∅ ⊢ ★) → Set
ℍ : ∀{Γ} → ClosEnv Γ → Subst Γ ∅ → Set

𝔹 (clos {Γ} M γ) N = Σ[ σ ∈ Subst Γ ∅ ] ℍ γ σ × (N ≡ subst σ M)

ℍ γ σ = ∀{x} → 𝔹 (γ x) (σ x)

ext-subst : ∀{Γ Δ} → Subst Γ Δ → Δ ⊢ ★ → Subst (Γ , ★) Δ
{-
ext-subst σ N Z = N
ext-subst σ N (S n) = σ n
-}
ext-subst{Γ}{Δ} σ N {A} = (subst (subst-zero N)) ∘ (exts σ)

ℍ-ext : ∀ {Γ} {γ : ClosEnv Γ} {σ : Subst Γ ∅} {c} {N : ∅ ⊢ ★}
      → ℍ γ σ  →  𝔹 c N
        --------------------------------
      → ℍ (γ ,' c) (ext-subst{Γ}{∅} σ N)
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
        ≡⟨ subst-id (λ {x₁} → refl) ⟩
          σ x
        ∎
      G : 𝔹 (γ x) (σ x) → 𝔹 (γ x) (ext-subst σ N (S x))
      G b rewrite eq = b
\end{code}



\begin{code}
cbn-result-clos : ∀{Γ}{γ : ClosEnv Γ}{M : Γ ⊢ ★}{c : Clos}
                → γ ⊢ M ⇓ c
                → Σ[ Δ ∈ Context ] Σ[ δ ∈ ClosEnv Δ ] Σ[ N ∈ Δ , ★ ⊢ ★ ]
                   c ≡ clos (ƛ N) δ
cbn-result-clos (⇓-var x₁ d) = cbn-result-clos d
cbn-result-clos {Γ}{γ}{ƛ N} ⇓-lam = ⟨ Γ , ⟨ γ , ⟨ N , refl ⟩ ⟩ ⟩
cbn-result-clos (⇓-app d₁ d₂) = cbn-result-clos d₂
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
—→-app-cong (ξ₁ ap ll') = ξ₁ ap (—→-app-cong ll')
—→-app-cong (ξ₂ neu ll') = ξ₁ ap (ξ₂ neu ll')
—→-app-cong β = ξ₁ ap β
—→-app-cong (ζ ll') = {!!} {- JGS: problem with ξ₁! -}

—↠-app-cong : ∀{Γ}{L L' M : Γ ⊢ ★}
            → L —↠ L'
            → L · M —↠ L' · M
—↠-app-cong {Γ}{L}{L'}{M} (L []) = (L · M) []
—↠-app-cong {Γ}{L}{L'}{M} (L —→⟨ r ⟩ ll') =
    L · M —→⟨ —→-app-cong r ⟩ (—↠-app-cong ll')
\end{code}


\begin{code}
rename-inc-subst : ∀{Γ}{M : Γ ⊢ ★}{N : Γ ⊢ ★}
                 → (subst (subst-zero M) (rename S_ N)) ≡ N
rename-inc-subst {Γ} {M} {N} rewrite
     rename-subst{M = N}{ρ = S_}{σ = subst-zero M} = subst-id refl


subst-empty : ∀{σ : Subst ∅ ∅}{M : ∅ ⊢ ★}
            → subst σ M ≡ M
subst-empty {σ} {` ()}
subst-empty {σ} {ƛ M} = cong ƛ_ (subst-id G)
  where G : is-id-subst (exts σ {B = ★})
        G {Z} = refl
        G {S ()}
subst-empty {σ} {L · M} = cong₂ _·_ subst-empty subst-empty

commute-exts-subst : ∀{Γ Δ Δ'} {σ : Subst Γ Δ} {σ' : Subst Δ Δ'}
       {A}{B} {x : Γ , B ∋ A} 
     → ((subst (exts σ')) ∘ exts σ) x ≡ (exts ((subst σ') ∘ σ)) x
commute-exts-subst {Γ} {Δ} {Δ'} {σ} {σ'} {x = Z} = refl
commute-exts-subst {∅} {Δ} {Δ'} {σ} {σ'} {x = S ()}
commute-exts-subst {Γ , A} {Δ} {Δ'} {σ} {σ'} {x = S x} =
  let ih = commute-exts-subst {Γ}{{!!}}{{!!}}{λ y → {!!}}{{!!}}{x = x} in
  {!!}
{-
((subst (exts σ')) ∘ exts σ) (S x) 
≡
(subst (exts σ')) ((exts σ) (S x) )
≡
(subst (exts σ')) (rename S_ (σ x))
≡
subst ((exts σ') ∘ S_) (σ x)
≡
subst (S_ ∘ σ') (σ x)


Goal: ((subst (exts σ')) ∘ exts σ) (S x) ≡
      rename S_ (((subst σ') ∘ σ) x)

-}


{-

((subst (exts σ')) ∘ subst (exts σ)) N
≡
subst ((subst (exts σ')) ∘ exts σ) N
≡?
subst (exts ((subst σ') ∘ σ)) N


goal:
((subst (exts σ')) ∘ (subst (exts σ))) N
≡
subst (exts ((subst σ') ∘ σ)) N

-}

subst-subst : ∀{Γ Δ Δ'} {σ : Subst Γ Δ} {σ' : Subst Δ Δ'} {M : Γ ⊢ ★}
            → ((subst σ') ∘ (subst σ)) M ≡  subst (subst σ' ∘ σ) M
subst-subst {Γ} {Δ} {Δ'} {σ} {σ'} {` x} = refl
subst-subst {Γ} {Δ} {Δ'} {σ} {σ'} {ƛ N} =
   let ih = subst-subst{Γ , ★}{Δ , ★}{Δ' , ★}{exts σ}{exts σ'}{M = N} in
   cong ƛ_ {!!}
subst-subst {Γ} {Δ} {Δ'} {σ} {σ'} {L · M} =
   cong₂ _·_ (subst-subst{M = L}) (subst-subst{M = M})

{-

subst (subst-zero (subst σ M)) (subst (exts σ₁) N)
= 
((subst (subst-zero (subst σ M))) ∘ (subst (exts σ))) N

(subst σ) ∘ (subst σ')
= 
subst (subst σ ∘ σ')



subst ( (subst (subst-zero (subst σ M)) ∘ (exts σ₁)) N
=
subst (ext-subst σ₁ (subst σ M)) N

-}

subst-exts-ext-subst : ∀{Γ Δ Δ'}{σ : Subst Γ Δ'}{σ₁ : Subst Δ Δ'}
                        {M : Γ ⊢ ★}{N : Δ , ★ ⊢ ★}
    → subst (subst-zero (subst σ M)) (subst (exts σ₁) N)
      ≡ subst (ext-subst σ₁ (subst σ M)) N
subst-exts-ext-subst {Γ} {Δ} {Δ'} {σ} {σ₁} {M} {` Z} = refl
subst-exts-ext-subst {Γ} {Δ} {Δ'} {σ} {σ₁} {M} {` (S x)} = {!!}
subst-exts-ext-subst {Γ} {Δ} {Δ'} {σ} {σ₁} {M} {ƛ N} =
  let ih : subst(subst-zero(subst (λ x → rename S_ (σ x)) M))(subst(exts σ') N)
           ≡ subst (ext-subst σ' (subst (λ x → rename S_ (σ x)) M)) N
      ih = (subst-exts-ext-subst{Γ}{Δ , ★}{Δ' , ★}
              {λ x → rename S_ (σ x)}{σ'}{M}{N}) in
  let x : subst (exts (subst-zero (subst σ M)))
                (subst (exts (exts σ₁)) N)
          ≡ subst (exts (ext-subst σ₁ (subst σ M))) N
      x = {!!} in      
  cong ƛ_ x
  where σ' : Subst (Δ , ★) (Δ' , ★)
        σ' Z = ` Z
        σ' (S x) = rename S_ (σ₁ x)
        
subst-exts-ext-subst {Γ} {Δ} {Δ'} {σ} {σ₁} {M} {N · N'} =
  cong₂ _·_ (subst-exts-ext-subst{Γ}{Δ}{Δ'}{σ}{σ₁}{M}{N})
            (subst-exts-ext-subst{Γ}{Δ}{Δ'}{σ}{σ₁}{M}{N'})
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
    rewrite subst-exts-ext-subst {Γ}{Δ}{∅}{σ}{σ₁}{M}{N} =
    let rs = (ƛ subst (exts σ₁) N) · subst σ M —→⟨ r ⟩ r' in
   ⟨ N' , ⟨ —↠-trans (—↠-app-cong σL—↠L') rs , bl ⟩ ⟩
\end{code}
