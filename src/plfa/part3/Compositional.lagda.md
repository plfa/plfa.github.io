---
title     : "Compositional: The denotational semantics is compositional"
layout    : page
prev      : /Denotational/
permalink : /Compositional/
next      : /Soundness/
---

```
module plfa.part3.Compositional where
```

## Introduction

In this chapter we prove that the denotational semantics is compositional,
which means we fill in the ellipses in the following equations.

    ℰ (` x) ≃ ...
    ℰ (ƛ M) ≃ ... ℰ M ...
    ℰ (M · N) ≃ ... ℰ M ... ℰ N ...

Such equations would imply that the denotational semantics could be
instead defined as a recursive function. Indeed, we end this chapter
with such a definition and prove that it is equivalent to ℰ.


## Imports

```
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import plfa.part2.Untyped
  using (Context; _,_; ★; _∋_; _⊢_; `_; ƛ_; _·_)
open import plfa.part3.Denotational
  using (Value; _↦_; _`,_; _⊔_; ⊥; _⊑_; _⊢_↓_;
         ⊑-bot; ⊑-fun; ⊑-conj-L; ⊑-conj-R1; ⊑-conj-R2;
         ⊑-dist; ⊑-refl; ⊑-trans; ⊔↦⊔-dist;
         var; ↦-intro; ↦-elim; ⊔-intro; ⊥-intro; sub;
         up-env; ℰ; _≃_; ≃-sym; Denotation; Env)
open plfa.part3.Denotational.≃-Reasoning
```

## Equation for lambda abstraction

Regarding the first equation

    ℰ (ƛ M) ≃ ... ℰ M ...

we need to define a function that maps a `Denotation (Γ , ★)` to a
`Denotation Γ`. This function, let us name it `ℱ`, should mimic the
non-recursive part of the semantics when applied to a lambda term.  In
particular, we need to consider the rules `↦-intro`, `⊥-intro`, and
`⊔-intro`. So `ℱ` has three parameters, the denotation `D` of the
subterm `M`, an environment `γ`, and a value `v`.  If we define `ℱ` by
recursion on the value `v`, then it matches up nicely with the three
rules `↦-intro`, `⊥-intro`, and `⊔-intro`.

```
ℱ : ∀{Γ} → Denotation (Γ , ★) → Denotation Γ
ℱ D γ (v ↦ w) = D (γ `, v) w
ℱ D γ ⊥ = ⊤
ℱ D γ (u ⊔ v) = (ℱ D γ u) × (ℱ D γ v)
```

If one squints hard enough, the `ℱ` function starts to look like the
`curry` operation familiar to functional programmers. It turns a
function that expects a tuple of length `n + 1` (the environment `Γ , ★`)
into a function that expects a tuple of length `n` and returns a
function of one parameter.

Using this `ℱ`, we hope to prove that

    ℰ (ƛ N) ≃ ℱ (ℰ N)

The function `ℱ` is preserved when going from a larger value `v` to a
smaller value `u`. The proof is a straightforward induction on the
derivation of `u ⊑ v`, using the `up-env` lemma in the case for the
`⊑-fun` rule.

```
sub-ℱ : ∀{Γ}{N : Γ , ★ ⊢ ★}{γ v u}
  → ℱ (ℰ N) γ v
  → u ⊑ v
    ------------
  → ℱ (ℰ N) γ u
sub-ℱ d ⊑-bot = tt
sub-ℱ d (⊑-fun lt lt′) = sub (up-env d lt) lt′
sub-ℱ d (⊑-conj-L lt lt₁) = ⟨ sub-ℱ d lt , sub-ℱ d lt₁ ⟩
sub-ℱ d (⊑-conj-R1 lt) = sub-ℱ (proj₁ d) lt
sub-ℱ d (⊑-conj-R2 lt) = sub-ℱ (proj₂ d) lt
sub-ℱ {v = v₁ ↦ v₂ ⊔ v₁ ↦ v₃} {v₁ ↦ (v₂ ⊔ v₃)} ⟨ N2 , N3 ⟩ ⊑-dist =
   ⊔-intro N2 N3
sub-ℱ d (⊑-trans x₁ x₂) = sub-ℱ (sub-ℱ d x₂) x₁
```

<!--
[PLW:
  If denotations were strengthened to be downward closed,
  we could rewrite the signature replacing (ℰ N) by d : Denotation (Γ , ★)]
[JGS: I'll look into this.]
-->

With this subsumption property in hand, we can prove the forward
direction of the semantic equation for lambda.  The proof is by
induction on the semantics, using `sub-ℱ` in the case for the `sub`
rule.

```
ℰƛ→ℱℰ : ∀{Γ}{γ : Env Γ}{N : Γ , ★ ⊢ ★}{v : Value}
  → ℰ (ƛ N) γ v
    ------------
  → ℱ (ℰ N) γ v
ℰƛ→ℱℰ (↦-intro d) = d
ℰƛ→ℱℰ ⊥-intro = tt
ℰƛ→ℱℰ (⊔-intro d₁ d₂) = ⟨ ℰƛ→ℱℰ d₁ , ℰƛ→ℱℰ d₂ ⟩
ℰƛ→ℱℰ (sub d lt) = sub-ℱ (ℰƛ→ℱℰ d) lt
```

The "inversion lemma" for lambda abstraction is a special case of the
above. The inversion lemma is useful in proving that denotations are
preserved by reduction.

```
lambda-inversion : ∀{Γ}{γ : Env Γ}{N : Γ , ★ ⊢ ★}{v₁ v₂ : Value}
  → γ ⊢ ƛ N ↓ v₁ ↦ v₂
    -----------------
  → (γ `, v₁) ⊢ N ↓ v₂
lambda-inversion{v₁ = v₁}{v₂ = v₂} d = ℰƛ→ℱℰ{v = v₁ ↦ v₂} d
```

The backward direction of the semantic equation for lambda is even
easier to prove than the forward direction. We proceed by induction on
the value v.

```
ℱℰ→ℰƛ : ∀{Γ}{γ : Env Γ}{N : Γ , ★ ⊢ ★}{v : Value}
  → ℱ (ℰ N) γ v
    ------------
  → ℰ (ƛ N) γ v
ℱℰ→ℰƛ {v = ⊥} d = ⊥-intro
ℱℰ→ℰƛ {v = v₁ ↦ v₂} d = ↦-intro d
ℱℰ→ℰƛ {v = v₁ ⊔ v₂} ⟨ d1 , d2 ⟩ = ⊔-intro (ℱℰ→ℰƛ d1) (ℱℰ→ℰƛ d2)
```

So indeed, the denotational semantics is compositional with respect
to lambda abstraction, as witnessed by the function `ℱ`.

```
lam-equiv : ∀{Γ}{N : Γ , ★ ⊢ ★}
  → ℰ (ƛ N) ≃ ℱ (ℰ N)
lam-equiv γ v = ⟨ ℰƛ→ℱℰ , ℱℰ→ℰƛ ⟩
```


## Equation for function application

Next we fill in the ellipses for the equation concerning function
application.

    ℰ (M · N) ≃ ... ℰ M ... ℰ N ...

For this we need to define a function that takes two denotations, both
in context `Γ`, and produces another one in context `Γ`. This
function, let us name it `●`, needs to mimic the non-recursive aspects
of the semantics of an application `L · M`.  We cannot proceed as
easily as for `ℱ` and define the function by recursion on value `v`
because, for example, the rule `↦-elim` applies to any value. Instead
we shall define `●` in a way that directly deals with the `↦-elim` and
`⊥-intro` rules but ignores `⊔-intro`. This makes the forward
direction of the proof more difficult, and the case for `⊔-intro`
demonstrates why the `⊑-dist` rule is important.

So we define the application of `D₁` to `D₂`, written `D₁ ● D₂`, to include
any value `w` equivalent to `⊥`, for the `⊥-intro` rule, and to include any
value `w` that is the output of an entry `v ↦ w` in `D₁`, provided the
input `v` is in `D₂`, for the `↦-elim` rule.

```
infixl 7 _●_

_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ
(D₁ ● D₂) γ w = w ⊑ ⊥ ⊎ Σ[ v ∈ Value ]( D₁ γ (v ↦ w) × D₂ γ v )
```

If one squints hard enough, the `_●_` operator starts to look
like the `apply` operation familiar to functional programmers.
It takes two parameters and applies the first to the second.

Next we consider the inversion lemma for application, which is also
the forward direction of the semantic equation for application.  We
describe the proof below.

```
ℰ·→●ℰ : ∀{Γ}{γ : Env Γ}{L M : Γ ⊢ ★}{v : Value}
  → ℰ (L · M) γ v
    ----------------
  → (ℰ L ● ℰ M) γ v
ℰ·→●ℰ (↦-elim{v = v′} d₁ d₂) = inj₂ ⟨ v′ , ⟨ d₁ , d₂ ⟩ ⟩
ℰ·→●ℰ {v = ⊥} ⊥-intro = inj₁ ⊑-bot
ℰ·→●ℰ {Γ}{γ}{L}{M}{v} (⊔-intro{v = v₁}{w = v₂} d₁ d₂)
    with ℰ·→●ℰ d₁ | ℰ·→●ℰ d₂
... | inj₁ lt1 | inj₁ lt2 = inj₁ (⊑-conj-L lt1 lt2)
... | inj₁ lt1 | inj₂ ⟨ v₁′ , ⟨ L↓v12 , M↓v3 ⟩ ⟩ =
      inj₂ ⟨ v₁′ , ⟨ sub L↓v12 lt , M↓v3 ⟩ ⟩
      where lt : v₁′ ↦ (v₁ ⊔ v₂) ⊑ v₁′ ↦ v₂
            lt = (⊑-fun ⊑-refl (⊑-conj-L (⊑-trans lt1 ⊑-bot) ⊑-refl))
... | inj₂ ⟨ v₁′ , ⟨ L↓v12 , M↓v3 ⟩ ⟩ | inj₁ lt2 =
      inj₂ ⟨ v₁′ , ⟨ sub L↓v12 lt , M↓v3 ⟩ ⟩
      where lt : v₁′ ↦ (v₁ ⊔ v₂) ⊑ v₁′ ↦ v₁
            lt = (⊑-fun ⊑-refl (⊑-conj-L ⊑-refl (⊑-trans lt2 ⊑-bot)))
... | inj₂ ⟨ v₁′ , ⟨ L↓v12 , M↓v3 ⟩ ⟩ | inj₂ ⟨ v₁′′ , ⟨ L↓v12′ , M↓v3′ ⟩ ⟩ =
      let L↓⊔ = ⊔-intro L↓v12 L↓v12′ in
      let M↓⊔ = ⊔-intro M↓v3 M↓v3′ in
      inj₂ ⟨ v₁′ ⊔ v₁′′ , ⟨ sub L↓⊔ ⊔↦⊔-dist , M↓⊔ ⟩ ⟩
ℰ·→●ℰ {Γ}{γ}{L}{M}{v} (sub d lt)
    with ℰ·→●ℰ d
... | inj₁ lt2 = inj₁ (⊑-trans lt lt2)
... | inj₂ ⟨ v₁ , ⟨ L↓v12 , M↓v3 ⟩ ⟩ =
      inj₂ ⟨ v₁ , ⟨ sub L↓v12 (⊑-fun ⊑-refl lt) , M↓v3 ⟩ ⟩
```

We proceed by induction on the semantics.

* In case `↦-elim` we have `γ ⊢ L ↓ (v′ ↦ v)` and `γ ⊢ M ↓ v′`,
  which is all we need to show `(ℰ L ● ℰ M) γ v`.

* In case `⊥-intro` we have `v = ⊥`. We conclude that `v ⊑ ⊥`.

* In case `⊔-intro` we have `ℰ (L · M) γ v₁` and `ℰ (L · M) γ v₂`
  and need to show `(ℰ L ● ℰ M) γ (v₁ ⊔ v₂)`. By the induction
  hypothesis, we have `(ℰ L ● ℰ M) γ v₁` and `(ℰ L ● ℰ M) γ v₂`.
  We have four subcases to consider.

    * Suppose `v₁ ⊑ ⊥` and `v₂ ⊑ ⊥`. Then `v₁ ⊔ v₂ ⊑ ⊥`.
    * Suppose `v₁ ⊑ ⊥`, `γ ⊢ L ↓ v₁′ ↦ v₂`, and `γ ⊢ M ↓ v₁′`.
      We have `γ ⊢ L ↓ v₁′ ↦ (v₁ ⊔ v₂)` by rule `sub`
      because `v₁′ ↦ (v₁ ⊔ v₂) ⊑ v₁′ ↦ v₂`.
    * Suppose `γ ⊢ L ↓ v₁′ ↦ v₁`, `γ ⊢ M ↓ v₁′`, and `v₂ ⊑ ⊥`.
      We have `γ ⊢ L ↓ v₁′ ↦ (v₁ ⊔ v₂)` by rule `sub`
      because `v₁′ ↦ (v₁ ⊔ v₂) ⊑ v₁′ ↦ v₁`.
    * Suppose `γ ⊢ L ↓ v₁′′ ↦ v₁, γ ⊢ M ↓ v₁′′`,
      `γ ⊢ L ↓ v₁′ ↦ v₂`, and `γ ⊢ M ↓ v₁′`.
      This case is the most interesting.
      By two uses of the rule `⊔-intro` we have
      `γ ⊢ L ↓ (v₁′ ↦ v₂) ⊔ (v₁′′ ↦ v₁)` and
      `γ ⊢ M ↓ (v₁′ ⊔ v₁′′)`. But this does not yet match
      what we need for `ℰ L ● ℰ M` because the result of
      `L` must be an `↦` whose input entry is `v₁′ ⊔ v₁′′`.
      So we use the `sub` rule to obtain
      `γ ⊢ L ↓ (v₁′ ⊔ v₁′′) ↦ (v₁ ⊔ v₂)`,
      using the `⊔↦⊔-dist` lemma (thanks to the `⊑-dist` rule) to
      show that

            (v₁′ ⊔ v₁′′) ↦ (v₁ ⊔ v₂) ⊑ (v₁′ ↦ v₂) ⊔ (v₁′′ ↦ v₁)

      So we have proved what is needed for this case.

* In case `sub` we have `Γ ⊢ L · M ↓ v₁` and `v ⊑ v₁`.
  By the induction hypothesis, we have `(ℰ L ● ℰ M) γ v₁`.
  We have two subcases to consider.

    * Suppose `v₁ ⊑ ⊥`. We conclude that `v ⊑ ⊥`.
    * Suppose `Γ ⊢ L ↓ v′ → v₁` and `Γ ⊢ M ↓ v′`.
      We conclude with `Γ ⊢ L ↓ v′ → v` by rule `sub`, because
      `v′ → v ⊑ v′ → v₁`.


The forward direction is proved by cases on the premise `(ℰ L ● ℰ M) γ v`.
In case `v ⊑ ⊥`, we obtain `Γ ⊢ L · M ↓ ⊥` by rule `⊥-intro`.
Otherwise, we conclude immediately by rule `↦-elim`.

```
●ℰ→ℰ· : ∀{Γ}{γ : Env Γ}{L M : Γ ⊢ ★}{v}
  → (ℰ L ● ℰ M) γ v
    ----------------
  → ℰ (L · M) γ v
●ℰ→ℰ· {γ}{v} (inj₁ lt) = sub ⊥-intro lt
●ℰ→ℰ· {γ}{v} (inj₂ ⟨ v₁ , ⟨ d1 , d2 ⟩ ⟩) = ↦-elim d1 d2
```

So we have proved that the semantics is compositional with respect to
function application, as witnessed by the `●` function.

```
app-equiv : ∀{Γ}{L M : Γ ⊢ ★}
  → ℰ (L · M) ≃ (ℰ L) ● (ℰ M)
app-equiv γ v = ⟨ ℰ·→●ℰ , ●ℰ→ℰ· ⟩
```

We also need an inversion lemma for variables.
If `Γ ⊢ x ↓ v`, then `v ⊑ γ x`. The proof is a straightforward
induction on the semantics.

```
var-inv : ∀ {Γ v x} {γ : Env Γ}
  → ℰ (` x) γ v
    -------------------
  → v ⊑ γ x
var-inv (var) = ⊑-refl
var-inv (⊔-intro d₁ d₂) = ⊑-conj-L (var-inv d₁) (var-inv d₂)
var-inv (sub d lt) = ⊑-trans lt (var-inv d)
var-inv ⊥-intro = ⊑-bot
```

To round-out the semantic equations, we establish the following one
for variables.

```
var-equiv : ∀{Γ}{x : Γ ∋ ★} → ℰ (` x) ≃ (λ γ v → v ⊑ γ x)
var-equiv γ v = ⟨ var-inv , (λ lt → sub var lt) ⟩
```



## Congruence

The main work of this chapter is complete: we have established
semantic equations that show how the denotational semantics is
compositional. In this section and the next we make use of these
equations to prove some corollaries: that denotational equality is a
_congruence_ and to prove the _compositionality property_, which states
that surrounding two denotationally-equal terms in the same context
produces two programs that are denotationally equal.

We begin by showing that denotational equality is a congruence with
respect to lambda abstraction: that `ℰ N ≃ ℰ N′` implies `ℰ (ƛ N) ≃ ℰ
(ƛ N′)`. We shall use the `lam-equiv` equation to reduce this question to
whether `ℱ` is a congruence.

```
ℱ-cong : ∀{Γ}{D D′ : Denotation (Γ , ★)}
  → D ≃ D′
    -----------
  → ℱ D ≃ ℱ D′
ℱ-cong{Γ} D≃D′ γ v =
  ⟨ (λ x → ℱ≃{γ}{v} x D≃D′) , (λ x → ℱ≃{γ}{v} x (≃-sym D≃D′)) ⟩
  where
  ℱ≃ : ∀{γ : Env Γ}{v}{D D′ : Denotation (Γ , ★)}
    → ℱ D γ v  →  D ≃ D′ → ℱ D′ γ v
  ℱ≃ {v = ⊥} fd dd′ = tt
  ℱ≃ {γ}{v ↦ w} fd dd′ = proj₁ (dd′ (γ `, v) w) fd
  ℱ≃ {γ}{u ⊔ w} fd dd′ = ⟨ ℱ≃{γ}{u} (proj₁ fd) dd′ , ℱ≃{γ}{w} (proj₂ fd) dd′ ⟩
```

The proof of `ℱ-cong` uses the lemma `ℱ≃` to handle both directions of
the if-and-only-if. That lemma is proved by a straightforward
induction on the value `v`.

We now prove that lambda abstraction is a congruence by direct
equational reasoning.

```
lam-cong : ∀{Γ}{N N′ : Γ , ★ ⊢ ★}
  → ℰ N ≃ ℰ N′
    -----------------
  → ℰ (ƛ N) ≃ ℰ (ƛ N′)
lam-cong {Γ}{N}{N′} N≃N′ =
  start
    ℰ (ƛ N)
  ≃⟨ lam-equiv ⟩
    ℱ (ℰ N)
  ≃⟨ ℱ-cong N≃N′ ⟩
    ℱ (ℰ N′)
  ≃⟨ ≃-sym lam-equiv ⟩
    ℰ (ƛ N′)
  ☐
```

Next we prove that denotational equality is a congruence for
application: that `ℰ L ≃ ℰ L′` and `ℰ M ≃ ℰ M′` imply
`ℰ (L · M) ≃ ℰ (L′ · M′)`. The `app-equiv` equation
reduces this to the question of whether the `●` operator
is a congruence.

```
●-cong : ∀{Γ}{D₁ D₁′ D₂ D₂′ : Denotation Γ}
  → D₁ ≃ D₁′ → D₂ ≃ D₂′
  → (D₁ ● D₂) ≃ (D₁′ ● D₂′)
●-cong {Γ} d1 d2 γ v = ⟨ (λ x → ●≃ x d1 d2) ,
                         (λ x → ●≃ x (≃-sym d1) (≃-sym d2)) ⟩
  where
  ●≃ : ∀{γ : Env Γ}{v}{D₁ D₁′ D₂ D₂′ : Denotation Γ}
    → (D₁ ● D₂) γ v  →  D₁ ≃ D₁′  →  D₂ ≃ D₂′
    → (D₁′ ● D₂′) γ v
  ●≃ (inj₁ v⊑⊥) eq₁ eq₂ = inj₁ v⊑⊥
  ●≃ {γ} {w} (inj₂ ⟨ v , ⟨ Dv↦w , Dv ⟩ ⟩) eq₁ eq₂ =
    inj₂ ⟨ v , ⟨ proj₁ (eq₁ γ (v ↦ w)) Dv↦w , proj₁ (eq₂ γ v) Dv ⟩ ⟩
```

Again, both directions of the if-and-only-if are proved via a lemma.
This time the lemma is proved by cases on `(D₁ ● D₂) γ v`.

With the congruence of `●`, we can prove that application is a
congruence by direct equational reasoning.

```
app-cong : ∀{Γ}{L L′ M M′ : Γ ⊢ ★}
  → ℰ L ≃ ℰ L′
  → ℰ M ≃ ℰ M′
    -------------------------
  → ℰ (L · M) ≃ ℰ (L′ · M′)
app-cong {Γ}{L}{L′}{M}{M′} L≅L′ M≅M′ =
  start
    ℰ (L · M)
  ≃⟨ app-equiv ⟩
    ℰ L ● ℰ M
  ≃⟨ ●-cong L≅L′ M≅M′ ⟩
    ℰ L′ ● ℰ M′
  ≃⟨ ≃-sym app-equiv ⟩
    ℰ (L′ · M′)
  ☐
```


## Compositionality

The _compositionality property_ states that surrounding two terms that
are denotationally equal in the same context produces two programs
that are denotationally equal. To make this precise, we define what we
mean by "context" and "surround".

A _context_ is a program with one hole in it. The following data
definition `Ctx` makes this idea explicit. We index the `Ctx` data
type with two contexts for variables: one for the hole and one for
terms that result from filling the hole.

```
data Ctx : Context → Context → Set where
  ctx-hole : ∀{Γ} → Ctx Γ Γ
  ctx-lam :  ∀{Γ Δ} → Ctx (Γ , ★) (Δ , ★) → Ctx (Γ , ★) Δ
  ctx-app-L : ∀{Γ Δ} → Ctx Γ Δ → Δ ⊢ ★ → Ctx Γ Δ
  ctx-app-R : ∀{Γ Δ} → Δ ⊢ ★ → Ctx Γ Δ → Ctx Γ Δ
```

* The constructor `ctx-hole` represents the hole, and in this case the
  variable context for the hole is the same as the variable context
  for the term that results from filling the hole.

* The constructor `ctx-lam` takes a `Ctx` and produces a larger one that
  adds a lambda abstraction at the top. The variable context of the
  hole stays the same, whereas we remove one variable from the context
  of the resulting term because it is bound by this lambda
  abstraction.

* There are two constructions for application, `ctx-app-L` and
  `ctx-app-R`. The `ctx-app-L` is for when the hole is inside the left-hand
  term (the operator) and the later is when the hole is inside the
  right-hand term (the operand).

The action of surrounding a term with a context is defined by the
following `plug` function. It is defined by recursion on the context.

```
plug : ∀{Γ}{Δ} → Ctx Γ Δ → Γ ⊢ ★ → Δ ⊢ ★
plug ctx-hole M = M
plug (ctx-lam C) N = ƛ plug C N
plug (ctx-app-L C N) L = (plug C L) · N
plug (ctx-app-R L C) M = L · (plug C M)
```

We are ready to state and prove the compositionality principle.  Given
two terms `M` and `N` that are denotationally equal, plugging them both
into an arbitrary context `C` produces two programs that are
denotationally equal.

```
compositionality : ∀{Γ Δ}{C : Ctx Γ Δ} {M N : Γ ⊢ ★}
  → ℰ M ≃ ℰ N
    ---------------------------
  → ℰ (plug C M) ≃ ℰ (plug C N)
compositionality {C = ctx-hole} M≃N =
  M≃N
compositionality {C = ctx-lam C′} M≃N =
  lam-cong (compositionality {C = C′} M≃N)
compositionality {C = ctx-app-L C′ L} M≃N =
  app-cong (compositionality {C = C′} M≃N) λ γ v → ⟨ (λ x → x) , (λ x → x) ⟩
compositionality {C = ctx-app-R L C′} M≃N =
  app-cong (λ γ v → ⟨ (λ x → x) , (λ x → x) ⟩) (compositionality {C = C′} M≃N)
```

The proof is a straightforward induction on the context `C`, using the
congruence properties `lam-cong` and `app-cong` that we established
above.

## The denotational semantics defined as a function

Having established the three equations `var-equiv`, `lam-equiv`, and
`app-equiv`, one should be able to define the denotational semantics
as a recursive function over the input term `M`. Indeed, we define the
following function `⟦ M ⟧` that maps terms to denotations, using the
auxiliary curry `ℱ` and apply `●` functions in the cases for lambda
and application, respectively.

```
⟦_⟧ : ∀{Γ} → (M : Γ ⊢ ★) → Denotation Γ
⟦ ` x ⟧ γ v = v ⊑ γ x
⟦ ƛ N ⟧ = ℱ ⟦ N ⟧
⟦ L · M ⟧ = ⟦ L ⟧ ● ⟦ M ⟧
```

The proof that `ℰ M` is denotationally equal to `⟦ M ⟧` is a
straightforward induction, using the three equations
`var-equiv`, `lam-equiv`, and `app-equiv` together
with the congruence lemmas for `ℱ` and `●`.

```
ℰ≃⟦⟧ : ∀ {Γ} {M : Γ ⊢ ★} → ℰ M ≃ ⟦ M ⟧
ℰ≃⟦⟧ {Γ} {` x} = var-equiv
ℰ≃⟦⟧ {Γ} {ƛ N} =
  let ih = ℰ≃⟦⟧ {M = N} in
    ℰ (ƛ N)
  ≃⟨ lam-equiv ⟩
    ℱ (ℰ N)
  ≃⟨ ℱ-cong (ℰ≃⟦⟧ {M = N}) ⟩
    ℱ ⟦ N ⟧
  ≃⟨⟩
    ⟦ ƛ N ⟧
  ☐
ℰ≃⟦⟧ {Γ} {L · M} =
   ℰ (L · M)
  ≃⟨ app-equiv ⟩
   ℰ L ● ℰ M
  ≃⟨ ●-cong (ℰ≃⟦⟧ {M = L}) (ℰ≃⟦⟧ {M = M}) ⟩
   ⟦ L ⟧ ● ⟦ M ⟧
  ≃⟨⟩
    ⟦ L · M ⟧
  ☐
```


## Unicode

This chapter uses the following unicode:

    ℱ  U+2131  SCRIPT CAPITAL F (\McF)
    ●  U+2131  BLACK CIRCLE (\cib)
