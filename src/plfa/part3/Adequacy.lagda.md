---
title     : "Adequacy: Adequacy of denotational semantics with respect to operational semantics"
permalink : /Adequacy/
---

```agda
module plfa.part3.Adequacy where
```

## Introduction

Having proved a preservation property in the last chapter, a natural
next step would be to prove progress. That is, to prove a property
of the form

    If γ ⊢ M ↓ v, then either M is a lambda abstraction or M —→ N for some N.

Such a property would tell us that having a denotation implies either
reduction to normal form or divergence. This is indeed true, but we
can prove a much stronger property! In fact, having a denotation that
is a function value (not `⊥`) implies reduction to a lambda
abstraction.

This stronger property, reformulated a bit, is known as _adequacy_.
That is, if a term `M` is denotationally equal to a lambda abstraction,
then `M` reduces to a lambda abstraction.

    ℰ M ≃ ℰ (ƛ N)  implies M —↠ ƛ N' for some N'

Recall that `ℰ M ≃ ℰ (ƛ N)` is equivalent to saying that `γ ⊢ M ↓ (v ↦
w)` for some `v` and `w`. We will show that `γ ⊢ M ↓ (v ↦ w)` implies
multi-step reduction a lambda abstraction.  The recursive structure of
the derivations for `γ ⊢ M ↓ (v ↦ w)` are completely different from
the structure of multi-step reductions, so a direct proof would be
challenging. However, The structure of `γ ⊢ M ↓ (v ↦ w)` closer to
that of [BigStep](/BigStep/) call-by-name
evaluation. Further, we already proved that big-step evaluation
implies multi-step reduction to a lambda (`cbn→reduce`). So we shall
prove that `γ ⊢ M ↓ (v ↦ w)` implies that `γ' ⊢ M ⇓ c`, where `c` is a
closure (a term paired with an environment), `γ'` is an environment
that maps variables to closures, and `γ` and `γ'` are appropriate
related.  The proof will be an induction on the derivation of
`γ ⊢ M ↓ v`, and to strengthen the induction hypothesis, we will relate
semantic values to closures using a _logical relation_ `𝕍`.

The rest of this chapter is organized as follows.

* To make the `𝕍` relation down-closed with respect to `⊑`,
  we must loosen the requirement that `M` result in a function value and
  instead require that `M` result in a value that is greater than or
  equal to a function value. We establish several properties about
  being ``greater than a function''.

* We define the logical relation `𝕍` that relates values and closures,
  and extend it to a relation on terms `𝔼` and environments `𝔾`.
  We prove several lemmas that culminate in the property that
  if `𝕍 v c` and `v′ ⊑ v`, then `𝕍 v′ c`.

* We prove the main lemma,
  that if `𝔾 γ γ'` and `γ ⊢ M ↓ v`, then `𝔼 v (clos M γ')`.

* We prove adequacy as a corollary to the main lemma.


## Imports

```agda
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product.Base using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Data.Empty using () renaming (⊥ to Bot)
open import Data.Unit.Base using (tt; ⊤)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Function.Base using (_∘_)
open import plfa.part2.Untyped
     using (Context; _⊢_; ★; _∋_; ∅; _,_; Z; S_; `_; ƛ_; _·_;
            rename; subst; ext; exts; _[_]; subst-zero;
            _—↠_; _—→⟨_⟩_; _∎; _—→_; ξ₁; ξ₂; β; ζ)
open import plfa.part2.Substitution using (ids; sub-id)
open import plfa.part2.BigStep
     using (Clos; clos; ClosEnv; ∅'; _,'_; _⊢_⇓_; ⇓-var; ⇓-lam; ⇓-app;
            ⇓-determ; cbn→reduce)
open import plfa.part3.Denotational
     using (Value; Env; `∅; _`,_; _↦_; _⊑_; _⊢_↓_; ⊥; all-funs∈; _⊔_; ∈→⊑;
            var; ↦-elim; ↦-intro; ⊔-intro; ⊥-intro; sub; ℰ; _≃_; _iff_;
            ⊑-trans; ⊑-conj-R1; ⊑-conj-R2; ⊑-conj-L; ⊑-refl; ⊑-fun; ⊑-bot;
            ⊑-dist; sub-inv-fun)
open import plfa.part3.Soundness using (soundness)

```


## The property of being greater or equal to a function

We define the following short-hand for saying that a value is
greater-than or equal to a function value.

```agda
above-fun : Value → Set
above-fun u = Σ[ v ∈ Value ] Σ[ w ∈ Value ] v ↦ w ⊑ u
```

If a value `u` is greater than a function, then an even greater value `u'`
is too.

```agda
above-fun-⊑ : ∀{u u' : Value}
      → above-fun u → u ⊑ u'
        -------------------
      → above-fun u'
above-fun-⊑ ⟨ v , ⟨ w , lt' ⟩ ⟩ lt = ⟨ v , ⟨ w , ⊑-trans lt' lt ⟩ ⟩
```

The bottom value `⊥` is not greater than a function.

```agda
above-fun⊥ : ¬ above-fun ⊥
above-fun⊥ ⟨ v , ⟨ w , lt ⟩ ⟩
    with sub-inv-fun lt
... | ⟨ Γ , ⟨ f , ⟨ Γ⊆⊥ , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩
    with all-funs∈ f
... | ⟨ A , ⟨ B , m ⟩ ⟩
    with Γ⊆⊥ m
... | ()
```

If the join of two values `u` and `u'` is greater than a function, then
at least one of them is too.

```agda
above-fun-⊔ : ∀{u u'}
           → above-fun (u ⊔ u')
           → above-fun u ⊎ above-fun u'
above-fun-⊔{u}{u'} ⟨ v , ⟨ w , v↦w⊑u⊔u' ⟩ ⟩
    with sub-inv-fun v↦w⊑u⊔u'
... | ⟨ Γ , ⟨ f , ⟨ Γ⊆u⊔u' , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩
    with all-funs∈ f
... | ⟨ A , ⟨ B , m ⟩ ⟩
    with Γ⊆u⊔u' m
... | inj₁ x = inj₁ ⟨ A , ⟨ B , (∈→⊑ x) ⟩ ⟩
... | inj₂ x = inj₂ ⟨ A , ⟨ B , (∈→⊑ x) ⟩ ⟩
```

On the other hand, if neither of `u` and `u'` is greater than a function,
then their join is also not greater than a function.

```agda
not-above-fun-⊔ : ∀{u u' : Value}
               → ¬ above-fun u → ¬ above-fun u'
               → ¬ above-fun (u ⊔ u')
not-above-fun-⊔ naf1 naf2 af12
    with above-fun-⊔ af12
... | inj₁ af1 = contradiction af1 naf1
... | inj₂ af2 = contradiction af2 naf2
```

The converse is also true. If the join of two values is not above a
function, then neither of them is individually.

```agda
not-above-fun-⊔-inv : ∀{u u' : Value} → ¬ above-fun (u ⊔ u')
              → ¬ above-fun u × ¬ above-fun u'
not-above-fun-⊔-inv af = ⟨ f af , g af ⟩
  where
    f : ∀{u u' : Value} → ¬ above-fun (u ⊔ u') → ¬ above-fun u
    f{u}{u'} af12 ⟨ v , ⟨ w , lt ⟩ ⟩ =
        contradiction ⟨ v , ⟨ w , ⊑-conj-R1 lt ⟩ ⟩ af12
    g : ∀{u u' : Value} → ¬ above-fun (u ⊔ u') → ¬ above-fun u'
    g{u}{u'} af12 ⟨ v , ⟨ w , lt ⟩ ⟩ =
        contradiction ⟨ v , ⟨ w , ⊑-conj-R2 lt ⟩ ⟩ af12
```

The property of being greater than a function value is decidable, as
exhibited by the following function.

```agda
above-fun? : (v : Value) → Dec (above-fun v)
above-fun? ⊥ = no above-fun⊥
above-fun? (v ↦ w) = yes ⟨ v , ⟨ w , ⊑-refl ⟩ ⟩
above-fun? (u ⊔ u')
    with above-fun? u | above-fun? u'
... | yes ⟨ v , ⟨ w , lt ⟩ ⟩ | _ = yes ⟨ v , ⟨ w , (⊑-conj-R1 lt) ⟩ ⟩
... | no _ | yes ⟨ v , ⟨ w , lt ⟩ ⟩ = yes ⟨ v , ⟨ w , (⊑-conj-R2 lt) ⟩ ⟩
... | no x | no y = no (not-above-fun-⊔ x y)
```


## Relating values to closures

Next we relate semantic values to closures.  The relation `𝕍` is for
closures whose term is a lambda abstraction, i.e., in weak-head normal
form (WHNF). The relation 𝔼 is for any closure. Roughly speaking,
`𝔼 v c` will hold if, when `v` is greater than a function value, `c` evaluates
to a closure `c'` in WHNF and `𝕍 v c'`. Regarding `𝕍 v c`, it will hold when
`c` is in WHNF, and if `v` is a function, the body of `c` evaluates
according to `v`.

```agda
𝕍 : Value → Clos → Set
𝔼 : Value → Clos → Set
```

We define `𝕍` as a function from values and closures to `Set` and not as a
data type because it is mutually recursive with `𝔼` in a negative
position (to the left of an implication).  We first perform case
analysis on the term in the closure. If the term is a variable or
application, then `𝕍` is false (`Bot`). If the term is a lambda
abstraction, we define `𝕍` by recursion on the value, which we
describe below.

```agda
𝕍 v (clos (` x₁) γ) = Bot
𝕍 v (clos (M · M₁) γ) = Bot
𝕍 ⊥ (clos (ƛ M) γ) = ⊤
𝕍 (v ↦ w) (clos (ƛ N) γ) =
    (∀{c : Clos} → 𝔼 v c → above-fun w → Σ[ c' ∈ Clos ]
        (γ ,' c) ⊢ N ⇓ c'  ×  𝕍 w c')
𝕍 (u ⊔ v) (clos (ƛ N) γ) = 𝕍 u (clos (ƛ N) γ) × 𝕍 v (clos (ƛ N) γ)
```

* If the value is `⊥`, then the result is true (`⊤`).

* If the value is a join (u ⊔ v), then the result is the pair
  (conjunction) of 𝕍 is true for both u and v.

* The important case is for a function value `v ↦ w` and closure
  `clos (ƛ N) γ`. Given any closure `c` such that `𝔼 v c`, if `w` is
  greater than a function, then `N` evaluates (with `γ` extended with `c`)
  to some closure `c'` and we have `𝕍 w c'`.


The definition of `𝔼` is straightforward. If `v` is a greater than a
function, then `M` evaluates to a closure related to `v`.

```agda
𝔼 v (clos M γ') = above-fun v → Σ[ c ∈ Clos ] γ' ⊢ M ⇓ c × 𝕍 v c
```

The proof of the main lemma is by induction on `γ ⊢ M ↓ v`, so it goes
underneath lambda abstractions and must therefore reason about open
terms (terms with variables). So we must relate environments of
semantic values to environments of closures.  In the following, `𝔾`
relates `γ` to `γ'` if the corresponding values and closures are related
by `𝔼`.

```agda
𝔾 : ∀{Γ} → Env Γ → ClosEnv Γ → Set
𝔾 {Γ} γ γ' = ∀{x : Γ ∋ ★} → 𝔼 (γ x) (γ' x)

𝔾-∅ : 𝔾 `∅ ∅'
𝔾-∅ {()}

𝔾-ext : ∀{Γ}{γ : Env Γ}{γ' : ClosEnv Γ}{v c}
      → 𝔾 γ γ' → 𝔼 v c → 𝔾 (γ `, v) (γ' ,' c)
𝔾-ext {Γ} {γ} {γ'} g e {Z} = e
𝔾-ext {Γ} {γ} {γ'} g e {S x} = g
```

We need a few properties of the `𝕍` and `𝔼` relations.  The first is that
a closure in the `𝕍` relation must be in weak-head normal form.  We
define WHNF has follows.

```agda
data WHNF : ∀ {Γ A} → Γ ⊢ A → Set where
  ƛ_ : ∀ {Γ} {N : Γ , ★ ⊢ ★}
     → WHNF (ƛ N)
```

The proof goes by cases on the term in the closure.

```agda
𝕍→WHNF : ∀{Γ}{γ : ClosEnv Γ}{M : Γ ⊢ ★}{v}
       → 𝕍 v (clos M γ) → WHNF M
𝕍→WHNF {M = ` x} {v} ()
𝕍→WHNF {M = ƛ N} {v} vc = ƛ_
𝕍→WHNF {M = L · M} {v} ()
```

Next we have an introduction rule for `𝕍` that mimics the `⊔-intro`
rule. If both `u` and `v` are related to a closure `c`, then their join is
too.

```agda
𝕍⊔-intro : ∀{c u v}
         → 𝕍 u c → 𝕍 v c
           ---------------
         → 𝕍 (u ⊔ v) c
𝕍⊔-intro {clos (` x) γ} () vc
𝕍⊔-intro {clos (ƛ N) γ} uc vc = ⟨ uc , vc ⟩
𝕍⊔-intro {clos (L · M) γ} () vc
```

In a moment we prove that `𝕍` is preserved when going from a greater
value to a lesser value: if `𝕍 v c` and `v' ⊑ v`, then `𝕍 v' c`.
This property, named `sub-𝕍`, is needed by the main lemma in
the case for the `sub` rule.

To prove `sub-𝕍`, we in turn need the following property concerning
values that are not greater than a function, that is, values that are
equivalent to `⊥`. In such cases, `𝕍 v (clos (ƛ N) γ')` is trivially true.

```agda
not-above-fun-𝕍 : ∀{v : Value}{Γ}{γ' : ClosEnv Γ}{N : Γ , ★ ⊢ ★ }
    → ¬ above-fun v
      -------------------
    → 𝕍 v (clos (ƛ N) γ')
not-above-fun-𝕍 {⊥} af = tt
not-above-fun-𝕍 {v ↦ v'} af = contradiction ⟨ v , ⟨ v' , ⊑-refl ⟩ ⟩ af
not-above-fun-𝕍 {v₁ ⊔ v₂} af
    with not-above-fun-⊔-inv af
... | ⟨ af1 , af2 ⟩ = ⟨ not-above-fun-𝕍 af1 , not-above-fun-𝕍 af2 ⟩
```

The proofs of `sub-𝕍` and `sub-𝔼` are intertwined.

```agda
sub-𝕍 : ∀{c : Clos}{v v'} → 𝕍 v c → v' ⊑ v → 𝕍 v' c
sub-𝔼 : ∀{c : Clos}{v v'} → 𝔼 v c → v' ⊑ v → 𝔼 v' c
```

We prove `sub-𝕍` by case analysis on the closure's term, to dispatch the
cases for variables and application. We then proceed by induction on
`v' ⊑ v`. We describe each case below.

```agda
sub-𝕍 {clos (` x) γ} {v} () lt
sub-𝕍 {clos (L · M) γ} () lt
sub-𝕍 {clos (ƛ N) γ} vc ⊑-bot = tt
sub-𝕍 {clos (ƛ N) γ} vc (⊑-conj-L lt1 lt2) = ⟨ (sub-𝕍 vc lt1) , sub-𝕍 vc lt2 ⟩
sub-𝕍 {clos (ƛ N) γ} ⟨ vv1 , vv2 ⟩ (⊑-conj-R1 lt) = sub-𝕍 vv1 lt
sub-𝕍 {clos (ƛ N) γ} ⟨ vv1 , vv2 ⟩ (⊑-conj-R2 lt) = sub-𝕍 vv2 lt
sub-𝕍 {clos (ƛ N) γ} vc (⊑-trans{v = v₂} lt1 lt2) = sub-𝕍 (sub-𝕍 vc lt2) lt1
sub-𝕍 {clos (ƛ N) γ} vc (⊑-fun lt1 lt2) ev1 sf
    with vc (sub-𝔼 ev1 lt1) (above-fun-⊑ sf lt2)
... | ⟨ c , ⟨ Nc , v4 ⟩ ⟩ = ⟨ c , ⟨ Nc , sub-𝕍 v4 lt2 ⟩ ⟩
sub-𝕍 {clos (ƛ N) γ} {v ↦ w ⊔ v ↦ w'} ⟨ vcw , vcw' ⟩ ⊑-dist ev1c sf
    with above-fun? w | above-fun? w'
... | yes af2 | yes af3
    with vcw ev1c af2 | vcw' ev1c af3
... | ⟨ clos L δ , ⟨ L⇓c₂ , 𝕍w ⟩ ⟩
    | ⟨ c₃ , ⟨ L⇓c₃ , 𝕍w' ⟩ ⟩ rewrite ⇓-determ L⇓c₃ L⇓c₂ with 𝕍→WHNF 𝕍w
... | ƛ_ =
      ⟨ clos L δ , ⟨ L⇓c₂ , ⟨ 𝕍w , 𝕍w' ⟩ ⟩ ⟩
sub-𝕍 {c} {v ↦ w ⊔ v ↦ w'} ⟨ vcw , vcw' ⟩  ⊑-dist ev1c sf
    | yes af2 | no naf3
    with vcw ev1c af2
... | ⟨ clos {Γ'} L γ₁ , ⟨ L⇓c2 , 𝕍w ⟩ ⟩
    with 𝕍→WHNF 𝕍w
... | ƛ_ {N = N'} =
      let 𝕍w' = not-above-fun-𝕍{w'}{Γ'}{γ₁}{N'} naf3 in
      ⟨ clos (ƛ N') γ₁ , ⟨ L⇓c2 , 𝕍⊔-intro 𝕍w 𝕍w' ⟩ ⟩
sub-𝕍 {c} {v ↦ w ⊔ v ↦ w'} ⟨ vcw , vcw' ⟩ ⊑-dist ev1c sf
    | no naf2 | yes af3
    with vcw' ev1c af3
... | ⟨ clos {Γ'} L γ₁ , ⟨ L⇓c3 , 𝕍w'c ⟩ ⟩
    with 𝕍→WHNF 𝕍w'c
... | ƛ_ {N = N'} =
      let 𝕍wc = not-above-fun-𝕍{w}{Γ'}{γ₁}{N'} naf2 in
      ⟨ clos (ƛ N') γ₁ , ⟨ L⇓c3 , 𝕍⊔-intro 𝕍wc 𝕍w'c ⟩ ⟩
sub-𝕍 {c} {v ↦ w ⊔ v ↦ w'} ⟨ vcw , vcw' ⟩ ⊑-dist ev1c ⟨ v' , ⟨ w'' , lt ⟩ ⟩
    | no naf2 | no naf3
    with above-fun-⊔ ⟨ v' , ⟨ w'' , lt ⟩ ⟩
... | inj₁ af2 = contradiction af2 naf2
... | inj₂ af3 = contradiction af3 naf3
```

* Case `⊑-bot`. We immediately have `𝕍 ⊥ (clos (ƛ N) γ)`.

* Case `⊑-conj-L`.

        v₁' ⊑ v     v₂' ⊑ v
        -------------------
        (v₁' ⊔ v₂') ⊑ v

  The induction hypotheses gives us `𝕍 v₁' (clos (ƛ N) γ)`
  and `𝕍 v₂' (clos (ƛ N) γ)`, which is all we need for this case.

* Case `⊑-conj-R1`.

        v' ⊑ v₁
        -------------
        v' ⊑ (v₁ ⊔ v₂)

  The induction hypothesis gives us `𝕍 v' (clos (ƛ N) γ)`.

* Case `⊑-conj-R2`.

        v' ⊑ v₂
        -------------
        v' ⊑ (v₁ ⊔ v₂)

  Again, the induction hypothesis gives us `𝕍 v' (clos (ƛ N) γ)`.

* Case `⊑-trans`.

        v' ⊑ v₂   v₂ ⊑ v
        -----------------
             v' ⊑ v

  The induction hypothesis for `v₂ ⊑ v` gives us
  `𝕍 v₂ (clos (ƛ N) γ)`. We apply the induction hypothesis
  for `v' ⊑ v₂` to conclude that `𝕍 v' (clos (ƛ N) γ)`.

* Case `⊑-dist`. This case  is the most difficult. We have

        𝕍 (v ↦ w) (clos (ƛ N) γ)
        𝕍 (v ↦ w') (clos (ƛ N) γ)

  and need to show that

        𝕍 (v ↦ (w ⊔ w')) (clos (ƛ N) γ)

  Let `c` be an arbitrary closure such that `𝔼 v c`.
  Assume `w ⊔ w'` is greater than a function.
  Unfortunately, this does not mean that both `w` and `w'`
  are above functions. But thanks to the lemma `above-fun-⊔`,
  we know that at least one of them is greater than a function.

  * Suppose both of them are greater than a function.  Then we have
    `γ ⊢ N ⇓ clos L δ` and `𝕍 w (clos L δ)`.  We also have `γ ⊢ N ⇓ c₃` and
    `𝕍 w' c₃`.  Because the big-step semantics is deterministic, we have
    `c₃ ≡ clos L δ`. Also, from `𝕍 w (clos L δ)` we know that `L ≡ ƛ N'`
    for some `N'`. We conclude that `𝕍 (w ⊔ w') (clos (ƛ N') δ)`.

  * Suppose one of them is greater than a function and the other is
    not: say `above-fun w` and `¬ above-fun w'`. Then from
    `𝕍 (v ↦ w) (clos (ƛ N) γ)`
    we have `γ ⊢ N ⇓ clos L γ₁` and `𝕍 w (clos L γ₁)`. From this we have
    `L ≡ ƛ N'` for some `N'`. Meanwhile, from `¬ above-fun w'` we have
    `𝕍 w' (clos L γ₁)`. We conclude that
    `𝕍 (w ⊔ w') (clos (ƛ N') γ₁)`.


The proof of `sub-𝔼` is direct and explained below.

```agda
sub-𝔼 {clos M γ} {v} {v'} 𝔼v v'⊑v fv'
    with 𝔼v (above-fun-⊑ fv' v'⊑v)
... | ⟨ c , ⟨ M⇓c , 𝕍v ⟩ ⟩ =
      ⟨ c , ⟨ M⇓c , sub-𝕍 𝕍v v'⊑v ⟩ ⟩
```

From `above-fun v'` and `v' ⊑ v` we have `above-fun v`.  Then with `𝔼 v c` we
obtain a closure `c` such that `γ ⊢ M ⇓ c` and `𝕍 v c`. We conclude with an
application of `sub-𝕍` with `v' ⊑ v` to show `𝕍 v' c`.


## Programs with function denotation terminate via call-by-name

The main lemma proves that if a term has a denotation that is above a
function, then it terminates via call-by-name. More formally, if
`γ ⊢ M ↓ v` and `𝔾 γ γ'`, then `𝔼 v (clos M γ')`. The proof is by
induction on the derivation of `γ ⊢ M ↓ v` we discuss each case below.

The following lemma, kth-x, is used in the case for the `var` rule.

```agda
kth-x : ∀{Γ}{γ' : ClosEnv Γ}{x : Γ ∋ ★}
     → Σ[ Δ ∈ Context ] Σ[ δ ∈ ClosEnv Δ ] Σ[ M ∈ Δ ⊢ ★ ]
                 γ' x ≡ clos M δ
kth-x{γ' = γ'}{x = x} with γ' x
... | clos{Γ = Δ} M δ = ⟨ Δ , ⟨ δ , ⟨ M , refl ⟩ ⟩ ⟩
```

```agda
↓→𝔼 : ∀{Γ}{γ : Env Γ}{γ' : ClosEnv Γ}{M : Γ ⊢ ★ }{v}
            → 𝔾 γ γ' → γ ⊢ M ↓ v → 𝔼 v (clos M γ')
↓→𝔼 {Γ} {γ} {γ'} 𝔾γγ' (var{x = x}) fγx
    with kth-x{Γ}{γ'}{x} | 𝔾γγ'{x = x}
... | ⟨ Δ , ⟨ δ , ⟨ M' , eq ⟩ ⟩ ⟩ | 𝔾γγ'x rewrite eq
    with 𝔾γγ'x fγx
... | ⟨ c , ⟨ M'⇓c , 𝕍γx ⟩ ⟩ =
      ⟨ c , ⟨ (⇓-var eq M'⇓c) , 𝕍γx ⟩ ⟩
↓→𝔼 {Γ} {γ} {γ'} 𝔾γγ' (↦-elim{L = L}{M = M}{v = v₁}{w = v} d₁ d₂) fv
    with ↓→𝔼 𝔾γγ' d₁ ⟨ v₁ , ⟨ v , ⊑-refl ⟩ ⟩
... | ⟨ clos L' δ , ⟨ L⇓L' , 𝕍v₁↦v ⟩ ⟩
    with 𝕍→WHNF 𝕍v₁↦v
... | ƛ_ {N = N}
    with 𝕍v₁↦v {clos M γ'} (↓→𝔼 𝔾γγ' d₂) fv
... | ⟨ c' , ⟨ N⇓c' , 𝕍v ⟩ ⟩ =
    ⟨ c' , ⟨ ⇓-app L⇓L' N⇓c' , 𝕍v ⟩ ⟩
↓→𝔼 {Γ} {γ} {γ'} 𝔾γγ' (↦-intro{N = N}{v = v}{w = w} d) fv↦w =
    ⟨ clos (ƛ N) γ' , ⟨ ⇓-lam , E ⟩ ⟩
    where E : {c : Clos} → 𝔼 v c → above-fun w
            → Σ[ c' ∈ Clos ] (γ' ,' c) ⊢ N ⇓ c'  ×  𝕍 w c'
          E {c} 𝔼vc fw = ↓→𝔼 (λ {x} → 𝔾-ext{Γ}{γ}{γ'} 𝔾γγ' 𝔼vc {x}) d fw
↓→𝔼 𝔾γγ' ⊥-intro f⊥ = contradiction f⊥ above-fun⊥
↓→𝔼 𝔾γγ' (⊔-intro{v = v₁}{w = v₂} d₁ d₂) fv12
    with above-fun? v₁ | above-fun? v₂
... | yes fv1 | yes fv2
    with ↓→𝔼 𝔾γγ' d₁ fv1 | ↓→𝔼 𝔾γγ' d₂ fv2
... | ⟨ c₁ , ⟨ M⇓c₁ , 𝕍v₁ ⟩ ⟩ | ⟨ c₂ , ⟨ M⇓c₂ , 𝕍v₂ ⟩ ⟩
    rewrite ⇓-determ M⇓c₂ M⇓c₁ =
    ⟨ c₁ , ⟨ M⇓c₁ , 𝕍⊔-intro 𝕍v₁ 𝕍v₂ ⟩ ⟩
↓→𝔼 𝔾γγ' (⊔-intro{v = v₁}{w = v₂} d₁ d₂) fv12 | yes fv1 | no nfv2
    with ↓→𝔼 𝔾γγ' d₁ fv1
... | ⟨ clos {Γ'} M' γ₁ , ⟨ M⇓c₁ , 𝕍v₁ ⟩ ⟩
    with 𝕍→WHNF 𝕍v₁
... | ƛ_ {N = N} =
    let 𝕍v₂ = not-above-fun-𝕍{v₂}{Γ'}{γ₁}{N} nfv2 in
    ⟨ clos (ƛ N) γ₁ , ⟨ M⇓c₁ , 𝕍⊔-intro 𝕍v₁ 𝕍v₂ ⟩ ⟩
↓→𝔼 𝔾γγ' (⊔-intro{v = v₁}{w = v₂} d₁ d₂) fv12 | no nfv1  | yes fv2
    with ↓→𝔼 𝔾γγ' d₂ fv2
... | ⟨ clos {Γ'} M' γ₁ , ⟨ M'⇓c₂ , 𝕍2c ⟩ ⟩
    with 𝕍→WHNF 𝕍2c
... | ƛ_ {N = N} =
    let 𝕍1c = not-above-fun-𝕍{v₁}{Γ'}{γ₁}{N} nfv1 in
    ⟨ clos (ƛ N) γ₁ , ⟨ M'⇓c₂ , 𝕍⊔-intro 𝕍1c 𝕍2c ⟩ ⟩
↓→𝔼 𝔾γγ' (⊔-intro d₁ d₂) fv12 | no nfv1  | no nfv2
    with above-fun-⊔ fv12
... | inj₁ fv1 = contradiction fv1 nfv1
... | inj₂ fv2 = contradiction fv2 nfv2
↓→𝔼 {Γ} {γ} {γ'} {M} {v'} 𝔾γγ' (sub{v = v} d v'⊑v) fv'
    with ↓→𝔼 {Γ} {γ} {γ'} {M} 𝔾γγ' d (above-fun-⊑ fv' v'⊑v)
... | ⟨ c , ⟨ M⇓c , 𝕍v ⟩ ⟩ =
      ⟨ c , ⟨ M⇓c , sub-𝕍 𝕍v v'⊑v ⟩ ⟩
```

* Case `var`. Looking up `x` in `γ'` yields some closure, `clos M' δ`,
  and from `𝔾 γ γ'` we have `𝔼 (γ x) (clos M' δ)`. With the premise
  `above-fun (γ x)`, we obtain a closure `c` such that `δ ⊢ M' ⇓ c`
  and `𝕍 (γ x) c`. To conclude `γ' ⊢ x ⇓ c` via `⇓-var`, we
  need `γ' x ≡ clos M' δ`, which is obvious, but it requires some
  Agda shananigans via the `kth-x` lemma to get our hands on it.

* Case `↦-elim`. We have `γ ⊢ L · M ↓ v`.
  The induction hypothesis for `γ ⊢ L ↓ v₁ ↦ v`
  gives us `γ' ⊢ L ⇓ clos L' δ` and `𝕍 v (clos L' δ)`.
  Of course, `L' ≡ ƛ N` for some `N`.
  By the induction hypothesis for `γ ⊢ M ↓ v₁`,
  we have `𝔼 v₁ (clos M γ')`.
  Together with the premise `above-fun v` and `𝕍 v (clos L' δ)`,
  we obtain a closure `c'` such that `δ ⊢ N ⇓ c'` and `𝕍 v c'`.
  We conclude that `γ' ⊢ L · M ⇓ c'` by rule `⇓-app`.

* Case `↦-intro`. We have `γ ⊢ ƛ N ↓ v ↦ w`.
  We immediately have `γ' ⊢ ƛ M ⇓ clos (ƛ M) γ'` by rule `⇓-lam`.
  But we also need to prove `𝕍 (v ↦ w) (clos (ƛ N) γ')`.
  Let `c` by an arbitrary closure such that `𝔼 v c`.
  Suppose `v'` is greater than a function value.
  We need to show that `γ' , c ⊢ N ⇓ c'` and `𝕍 v' c'` for some `c'`.
  We prove this by the induction hypothesis for `γ , v ⊢ N ↓ v'`
  but we must first show that `𝔾 (γ , v) (γ' , c)`. We prove
  that by the lemma `𝔾-ext`, using facts `𝔾 γ γ'` and `𝔼 v c`.

* Case `⊥-intro`. We have the premise `above-fun ⊥`, but that's impossible.

* Case `⊔-intro`. We have `γ ⊢ M ↓ (v₁ ⊔ v₂)` and `above-fun (v₁ ⊔ v₂)`
  and need to show `γ' ⊢ M ↓ c` and `𝕍 (v₁ ⊔ v₂) c` for some `c`.
  Again, by `above-fun-⊔`, at least one of `v₁` or `v₂` is greater than
  a function.

  * Suppose both `v₁` and `v₂` are greater than a function value.
    By the induction hypotheses for `γ ⊢ M ↓ v₁` and `γ ⊢ M ↓ v₂`
    we have `γ' ⊢ M ⇓ c₁`, `𝕍 v₁ c₁`, `γ' ⊢ M ⇓ c₂`, and `𝕍 v₂ c₂`
    for some `c₁` and `c₂`. Because `⇓` is deterministic, we have `c₂ ≡ c₁`.
    Then by `𝕍⊔-intro` we conclude that `𝕍 (v₁ ⊔ v₂) c₁`.

  * Without loss of generality, suppose `v₁` is greater than a function
    value but `v₂` is not.  By the induction hypotheses for `γ ⊢ M ↓ v₁`,
    and using `𝕍→WHNF`, we have `γ' ⊢ M ⇓ clos (ƛ N) γ₁`
    and `𝕍 v₁ (clos (ƛ N) γ₁)`.
    Then because `v₂` is not greater than a function, we also have
    `𝕍 v₂ (clos (ƛ N) γ₁)`. We conclude that `𝕍 (v₁ ⊔ v₂) (clos (ƛ N) γ₁)`.

* Case `sub`. We have `γ ⊢ M ↓ v`, `v' ⊑ v`, and `above-fun v'`.
  We need to show that `γ' ⊢ M ⇓ c` and `𝕍 v' c` for some `c`.
  We have `above-fun v` by `above-fun-⊑`,
  so the induction hypothesis for `γ ⊢ M ↓ v` gives us a closure `c`
  such that `γ' ⊢ M ⇓ c` and `𝕍 v c`. We conclude that `𝕍 v' c` by `sub-𝕍`.


## Proof of denotational adequacy

From the main lemma we can directly show that `ℰ M ≃ ℰ (ƛ N)` implies
that `M` big-steps to a lambda, i.e., `∅ ⊢ M ⇓ clos (ƛ N′) γ`.

```agda
↓→⇓ : ∀{M : ∅ ⊢ ★}{N : ∅ , ★ ⊢ ★}  →  ℰ M ≃ ℰ (ƛ N)
         →  Σ[ Γ ∈ Context ] Σ[ N′ ∈ (Γ , ★ ⊢ ★) ] Σ[ γ ∈ ClosEnv Γ ]
            ∅' ⊢ M ⇓ clos (ƛ N′) γ
↓→⇓{M}{N} eq
    with ↓→𝔼 𝔾-∅ ((proj₂ (eq `∅ (⊥ ↦ ⊥))) (↦-intro ⊥-intro))
                 ⟨ ⊥ , ⟨ ⊥ , ⊑-refl ⟩ ⟩
... | ⟨ clos {Γ} M′ γ , ⟨ M⇓c , Vc ⟩ ⟩
    with 𝕍→WHNF Vc
... | ƛ_ {N = N′} =
    ⟨ Γ , ⟨ N′ , ⟨ γ , M⇓c ⟩  ⟩ ⟩
```

The proof goes as follows. We derive `∅ ⊢ ƛ N ↓ ⊥ ↦ ⊥` and
then `ℰ M ≃ ℰ (ƛ N)` gives us `∅ ⊢ M ↓ ⊥ ↦ ⊥`. We conclude
by applying the main lemma to obtain `∅ ⊢ M ⇓ clos (ƛ N′) γ`
for some `N′` and `γ`.

Now to prove the adequacy property. We apply the above
lemma to obtain `∅ ⊢ M ⇓ clos (ƛ N′) γ` and then
apply `cbn→reduce` to conclude.

```agda
adequacy : ∀{M : ∅ ⊢ ★}{N : ∅ , ★ ⊢ ★}
   →  ℰ M ≃ ℰ (ƛ N)
   → Σ[ N′ ∈ (∅ , ★ ⊢ ★) ]
     (M —↠ ƛ N′)
adequacy{M}{N} eq
    with ↓→⇓ eq
... | ⟨ Γ , ⟨ N′ , ⟨ γ , M⇓ ⟩ ⟩ ⟩ =
    cbn→reduce M⇓
```

## Call-by-name is equivalent to beta reduction

As promised, we return to the question of whether call-by-name
evaluation is equivalent to beta reduction. In chapter
[BigStep](/BigStep/) we established the forward
direction: that if call-by-name produces a result, then the program
beta reduces to a lambda abstraction (`cbn→reduce`).  We now prove the backward
direction of the if-and-only-if, leveraging our results about the
denotational semantics.

```agda
reduce→cbn : ∀ {M : ∅ ⊢ ★} {N : ∅ , ★ ⊢ ★}
           → M —↠ ƛ N
           → Σ[ Δ ∈ Context ] Σ[ N′ ∈ Δ , ★ ⊢ ★ ] Σ[ δ ∈ ClosEnv Δ ]
             ∅' ⊢ M ⇓ clos (ƛ N′) δ
reduce→cbn M—↠ƛN = ↓→⇓ (soundness M—↠ƛN)
```

Suppose `M —↠ ƛ N`. Soundness of the denotational semantics gives us
`ℰ M ≃ ℰ (ƛ N)`. Then by `↓→⇓` we conclude that
`∅' ⊢ M ⇓ clos (ƛ N′) δ` for some `N′` and `δ`.

Putting the two directions of the if-and-only-if together, we
establish that call-by-name evaluation is equivalent to beta reduction
in the following sense.

```agda
cbn↔reduce : ∀ {M : ∅ ⊢ ★}
           → (Σ[ N ∈ ∅ , ★ ⊢ ★ ] (M —↠ ƛ N))
             iff
             (Σ[ Δ ∈ Context ] Σ[ N′ ∈ Δ , ★ ⊢ ★ ] Σ[ δ ∈ ClosEnv Δ ]
               ∅' ⊢ M ⇓ clos (ƛ N′) δ)
cbn↔reduce {M} = ⟨ (λ x → reduce→cbn (proj₂ x)) ,
                   (λ x → cbn→reduce (proj₂ (proj₂ (proj₂ x)))) ⟩
```


## Unicode

This chapter uses the following unicode:

    𝔼  U+1D53C  MATHEMATICAL DOUBLE-STRUCK CAPITAL E (\bE)
    𝔾  U+1D53E  MATHEMATICAL DOUBLE-STRUCK CAPITAL G (\bG)
    𝕍  U+1D53E  MATHEMATICAL DOUBLE-STRUCK CAPITAL V (\bV)
