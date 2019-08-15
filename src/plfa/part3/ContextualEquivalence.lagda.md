---
title     : "ContextualEquivalence: Denotational equality implies contextual equivalence 🚧"
layout    : page
prev      : /Adequacy/
permalink : /ContextualEquivalence/
next      : /Substitution/
---

```
module plfa.part3.ContextualEquivalence where
```

## Imports

```
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
     renaming (_,_ to ⟨_,_⟩)
open import plfa.part2.Untyped using (_⊢_; ★; ∅; _,_; ƛ_; _—↠_)
open import plfa.part2.BigStep using (_⊢_⇓_; cbn→reduce)
open import plfa.part3.Denotational using (ℰ; _≃_; ≃-sym; ≃-trans; _iff_)
open import plfa.part3.Compositional using (Ctx; plug; compositionality)
open import plfa.part3.Soundness using (soundness)
open import plfa.part3.Adequacy using (adequacy)
```

## Contextual Equivalence

The notion of _contextual equivalence_ is an important one for
programming languages because it is the sufficient condition for
changing a subterm of a program while maintaining the program's
overall behavior. Two terms `M` and `N` are contextually equivalent
if they can plugged into any context `C` and produce equivalent
results. As discuss in the Denotational chapter, the result of
a program in the lambda calculus is to terminate or not.
We characterize termination with the reduction semantics as follows.

```
terminates : ∀{Γ} → (M : Γ ⊢ ★) → Set
terminates {Γ} M = Σ[ N ∈ (Γ , ★ ⊢ ★) ] (M —↠ ƛ N)
```

So two terms are contextually equivalent if plugging them into the
same context produces two programs that either terminate or diverge
together.

```
_≅_ : ∀{Γ} → (M N : Γ ⊢ ★) → Set
(_≅_ {Γ} M N) = ∀ {C : Ctx Γ ∅}
                → (terminates (plug C M)) iff (terminates (plug C N))
```

The contextual equivalence of two terms is difficult to prove directly
based on the above definition because of the universal quantification
of the context `C`. One of the main motivations for developing
denotational semantics is to have an alternative way to prove
contextual equivalence that instead only requires reasoning about the
two terms.


## Denotational equivalence implies contextual equivalence

Thankfully, the proof that denotational equality implies contextual
equivalence is an easy corollary of the results that we have already
established. Furthermore, the two directions of the if-and-only-if are
symmetric, so we can prove one lemma and then use it twice in the
theorem.

The lemma states that if `M` and `N` are denotationally equal
and if `M` plugged into `C` terminates, then so does
`N` plugged into `C`.

```
denot-equal-terminates : ∀{Γ} {M N : Γ ⊢ ★} {C : Ctx Γ ∅}
  → ℰ M ≃ ℰ N  →  terminates (plug C M)
    -----------------------------------
  → terminates (plug C N)
denot-equal-terminates {Γ}{M}{N}{C} ℰM≃ℰN ⟨ N′ , CM—↠ƛN′ ⟩ =
  let ℰCM≃ℰƛN′ = soundness CM—↠ƛN′ in
  let ℰCM≃ℰCN = compositionality{Γ = Γ}{Δ = ∅}{C = C} ℰM≃ℰN in
  let ℰCN≃ℰƛN′ = ≃-trans (≃-sym ℰCM≃ℰCN) ℰCM≃ℰƛN′ in
    cbn→reduce (proj₂ (proj₂ (proj₂ (adequacy ℰCN≃ℰƛN′))))
```

The proof is direct. Because `plug C —↠ plug C (ƛN′)`,
we can apply soundness to obtain

    ℰ (plug C M) ≃ ℰ (ƛN′)

From `ℰ M ≃ ℰ N`, compositionality gives us

    ℰ (plug C M) ≃ ℰ (plug C N).

Putting these two facts together gives us

    ℰ (plug C N) ≃ ℰ (ƛN′).

We then apply adequacy to deduce

    ∅' ⊢ plug C N ⇓ clos (ƛ N′′) δ).

Call-by-name evaluation implies reduction to a lambda abstraction,
so we conclude that

    terminates (plug C N).


The main theorem follows by two applications of the lemma.

```
denot-equal-contex-equal : ∀{Γ} {M N : Γ ⊢ ★}
  → ℰ M ≃ ℰ N
    ---------
  → M ≅ N
denot-equal-contex-equal{Γ}{M}{N} eq {C} =
   ⟨ (λ tm → denot-equal-terminates eq tm) ,
     (λ tn → denot-equal-terminates (≃-sym eq) tn) ⟩
```


## Unicode

This chapter uses the following unicode:

    ≅  U+2245  APPROXIMATELY EQUAL TO (\~= or \cong)
