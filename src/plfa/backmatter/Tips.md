---
title     : "Tips"
permalink : /Tips/
---

# Interactive development 

## Equational reasoning skeleton

When starting to work on an equational reasoning problem, you can begin like this:
```agda
begin
    ?
  ≡⟨ ? ⟩
    ?
  ≡⟨ ? ⟩
    ?
  ≡⟨ ? ⟩
    ?
∎
```

This sets up a series of reasoning steps with holes for both the expressions at each step, and the step itself. 
Since the reasoning steps are holes, Agda will always accept this, so you can make incremental progress while keeping your file compiling.

Now call "solve" (`C-c C-s` in Emacs).
This will solve the expression holes at the beginning and the end so you don't have to fill them in.
You can do this again if you fix a step, so if you fill in the reasoning you want to do for a step, you can use "solve" and Agda will fill in the next term.

## Goal information will show computed terms

Suppose you have a partial equational reasoning proof:
```agda
begin
    2 + (x + y)
  ≡⟨ ?2 ⟩
    ?
  ≡⟨ ? ⟩
    ?
  ≡⟨ ? ⟩
    ?
∎
```

The first term can be computed more.
To see this, you can ask for the goal context for `?2` and it will show something like this:
```
?2 = suc (suc (x + y)) = y_5244
```
i.e. your LHS and an unknown RHS (because it's a hole), but it will show the LHS fully computed, which you can copy into your file directly.

## Quickly setting up `with` clauses

If you have a function like this:
```agda
foo a = ?
```
and you want to introduce a `with`-clause, there is no direct hotkey for this. 
The fastest thing to do is to write
```agda
foo a with my-thing
... | x = ?
```
and then ask to case-split on `x`.

## Quickly setting up record skeletons

"Refine" (`C-c C-r` in Emacs) will set up a skeleton for a record constructor if Agda knows a hole must be a record type.
This is useful for e.g. isomorphisms, products, sigmas, or existentials.

# General tips

## Try and make your definitions compute as much as possible

For example, compare:
```agda
2 * foo b
```
vs
```agda
foo b * 2 
```

The definition of `*` does case analysis on its first argument.
This means that if the first argument to `*` is a constructor application, Agda can do some computation for you. 
The first example computes to `foo b + (foo b + zero)`, but the second one does not compute at all: Agda can't pattern match on `foo b`, it could be anything!

Doing this lets Agda do more definitional simplification, which means you have to do less work.
Unfortunately it does require you to know _which_ arguments are the one that Agda can evaluate, which requires looking at the definitions of the functions.

## `x + x` is better than `2 * x`

An expression like `2 * x` will compute to `x + (x + zero)`.
You now need to get rid of the `x + zero` with a rewrite or similar.
You don't have this problem if you just write `x + x`.

This is probably less true for larger constants: writing out `8 * x` would be tedious.

## The three styles of proof all tend to use the same assumptions

Consider these three proofs of the same theorem:
```agda
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p =
  begin
    (suc m + n) * p
  ≡⟨⟩
    suc (m + n) * p
  ≡⟨⟩
    p + (m + n) * p
  ≡⟨ cong (p +_) (*-distrib-+ m n p) ⟩
    p + (m * p + n * p)
  ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
    (p + m * p) + n * p
  ≡⟨⟩
    (suc m * p) + n * p
  ∎

*-distrib-+‵ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+‵ zero n p = refl
*-distrib-+‵ (suc m) n p = trans ( cong (p +_) (*-distrib-+‵ m n p)) ( sym ( +-assoc p (m * p) (n * p)))

*-distrib-+‶ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+‶ zero n p = refl
*-distrib-+‶ (suc m) n p rewrite +-assoc p (m * p) (n * p) | *-distrib-+‶ m n p = refl
```

They use three approaches for doing "multiple steps":
1. Equational reasoning
2. `trans`
3. `rewrite`

However, notably they all use the same supporting proofs!
That means you can often write the overall proof however you find easiest and then rewrite it into another form if you want.
For example, do the proof slowly with equational reasoning, and then turn it into a compact proof with `rewrite`.

## Avoid mutual recursion in proofs by recursing outside the lemma

Look at the second part of the proof of commutativity of `+`:
```agda
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎
```
We use two equalities: the `+-suc` lemma, and a recursive use of `+-comm`.

If you were doing this for the first time, you might be tempted to make _one_ lemma for both those steps.
It wouldn't look that different, it would just have `n` and `m` swapped.
But then you would find that you needed to call `+-comm` from the lemma, which needs mutual recursion.

Instead, you can do what's done here and use the recursive call before/after your lemma.

## When to use implicit parameters

Roughly: if it can be inferred easily from the result, e.g.
```
≤-refl : ∀ { n : ℕ } → n ≤ n
```
Agda will be able to infer the `n` from the `n ≤ n` in the result.

Note that the situation is different for constructors and functions.
Generally, Agda can infer `x` from `f x` if `f` is a constructor (like `≤`) but _not_ if it is a function (like `_+_`).

## Avoiding "green slime"

"Green slime" is when you use a function in the index of a returned data type value.
For example:
```agda
data Tree (A : Set) : ℕ → Set where
  leaf : A → Tree A 1
  node : ∀ {s : ℕ} → Tree A s → Tree A s → Tree A (s + s)
```
Here we end up with a `Tree (s + s)` as the result of `node`.
This means that if we pattern match on a value of type `Tree A n`, Agda may get confused about making `n` and `s + s` the same.

There are a few ways to avoid green slime, but one way that often works is to use a variable and also include a proof that it has the value that you want. So:

```agda
data Tree (A : Set) : ℕ → Set where
  leaf : A → Tree A 1
  node : 
    ∀ {s : ℕ} {s‵ : ℕ}
    → Tree A s 
    → Tree A s 
    → s‵ ≡ s + s
    → Tree A s‵
```

Now you can still get the information about the sum by matching on the proof, but Agda has an easier time.
