---
layout : post
title  : "Migration to Agda 2.6.1"
short  : false
---

We upgraded to [Agda 2.6.1](https://github.com/agda/agda/releases/tag/v2.6.1) and [version 1.3 of the standard library](https://github.com/agda/agda-stdlib/releases/tag/v1.3). If you want to continue working with the latest version of the book, you'll have to update your versions locally. Please follow the instructions in [Getting Started]({{ site.baseurl }}/GettingStarted/) to reinstall Agda and the standard library.

<!--more-->

### Changes to the termination checker

Agda 2.6.1 made several [changes to the termination checker][termination-checking]. As a result of these changes, Agda is no longer able to see that our evaluation functions, e.g., in [Properties][properties-eval], are terminating. In response, we changed the definition of `Gas` to be a record type, rather than a data type:

```diff
- data Gas : Set where
-   gas : ℕ → Gas
+ record Gas : Set where
+   constructor gas
+   field
+     amount : ℕ
```

The reason this works is that η-equality holds *by definition* for records. Agda uses this to see that unwrapping and rewrapping numbers as `Gas` is the identity, and hence the amount of gas is decreasing if that number is decreasing.

[termination-checking]: https://github.com/agda/agda/blob/master/doc/release-notes/2.6.1.md#termination-checking
[properties-eval]: https://plfa.github.io/Properties/#31408

### Changes to equational reasoning

The function `_≡⟨_⟩_`, part of the equational reasoning syntax, was renamed to `step-≡`, for [various reasons][step-≡]. The new function has the same semantics, but flips the order of the arguments. This does not mean you have to change your equational reasoning proofs, as the module also defines a syntax macro, which recovers the original argument order:

```
infixr -2 step-≡

step-≡ : ∀ x {y z : A} → y ≡ z → x ≡ y → x ≡ z
step-≡ y≡z x≡y = trans x≡y y≡z

syntax step-≡ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z
```

Syntax macros aren’t quite definitions in Agda, so you cannot import them by “name”. Instead, they’re imported together with the function for which they’re defined, i.e., as `step-≡`:

```diff
- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
+ open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
```

If you’d like more details, there’s a lot of discussion of why this change was made in the [CHANGELOG][step-≡]. For PLFA, we make a note of the incongruence in the chapter on [Equality][equality-stdlib], but leave our definitions of equational reasoning unchanged.

[step-≡]: https://github.com/agda/agda-stdlib/blob/master/CHANGELOG/v1.3.md#changes-to-how-equational-reasoning-is-implemented
[equality-stdlib]: https://plfa.github.io/Equality/#standard-library

### Deprecation of `Data.List.{All,Any}`

The modules `Data.List.{All,Any}` were deprecated in v1.0,
and were moved to `Data.List.Relation.Unary.{All,Any}`:

```diff
- import Data.List.All using (All; []; _∷_)
- import Data.List.Any using (Any; here; there)
+ import Data.List.Relation.Unary.All using (All; []; _∷_)
+ import Data.List.Relation.Unary.Any using (Any; here; there)
```
