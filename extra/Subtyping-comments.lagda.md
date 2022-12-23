Comments on Subtyping
Philip Wadler

```agda
module plfa.part2.Subtyping-comments where
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _<_; _+_)
open import Data.Nat.Properties
    using (m+n≤o⇒m≤o; m+n≤o⇒n≤o; n≤0⇒n≡0; ≤-pred; ≤-refl; ≤-trans; m≤m+n;
           m≤n+m; ≤-step; m≤n⇒m<n∨m≡n)
open import Data.Product using (_×_; _,_) -- using (proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
```

Nice work. We should discuss!

Bits of the chapter are quite a slog, which makes me wonder about
whether to include it or not. I'm also concerned about the way in
which the extrinsic formulation is mixed with de Bruijn indices,
which strikes me as odd.

In several places (e.g. C-rcd, field-pres) a row of dashes has been
omitted where the convention in Parts 1 and 2 of the book would
include one.  Also, in several places more than one hypothesis appears
on a line (e.g., ⊆-tran, ren-vec-pres). Please stick to the
conventions of Parts 1 and 2.

I suggest more mnemonic names for the subtyping rules.

   <:-nat  -->  <:-ℕ
   <:-fun  -->  <:-⇒
   <:-rcd  -->  <:-⦗⦘

"The proof does not go by induction on the type `A` because of the
`<:-rcd` rule." Please say more about why this prohibits induction.
It took me a while before I could see why this was the case.

"suc (ty-size A + ty-size B)" --> 1 + (ty-size A + ty-size B),
and similarly.

Omit {n} in two clauses defining vec-ty-size, it is not needed.

The definition of <:-refl-aux uses a trick similar to Peter's for
turning strong recursion into ordinary recursion.

In most places, strong induction is avoided in favour of mutual
recursion with one definition on values and the other on a vector of
values. I wonder if the same might be done here, using a vector of
subtyping relations.  (The length of this vector, and the order of
subtyping entries, would correspond to the types of the fields in the
shorter vector.)

Here is my attempt to distill the essence of Peter and Jeremy's trick.
It captures something useful, but I'm not sure it is the same as the
trick.

```agda
weak-ind : ∀ {P : ℕ → Set}
  → P zero
  → (∀ (m : ℕ)
      → P m
        ---------
      → P (suc m))
    ---------------
  → ∀ (n : ℕ) → P n
weak-ind {P} base step = h
  where
  h : ∀ (n : ℕ) → P n
  h zero    = base
  h (suc n) = step n (h n)

choose : ∀ (m n : ℕ) → m < suc n → m < n ⊎ m ≡ n
choose m n (s≤s m≤n)  =  m≤n⇒m<n∨m≡n m≤n

strong-id : ∀ {P : ℕ → Set}
  → (∀ (n : ℕ)
      → (∀ (m : ℕ) → m < n → P m)
        -------------------------
      → P n)
    ---------------
  → ∀ (n : ℕ) → P n
strong-id {P} ih n  =  ih n (cov n)
  where

  base : ∀ (m : ℕ) → m < zero → P m
  base m ()

  step : ∀ (n : ℕ)
    → (∀ (m : ℕ) → m < n → P m)
      -----------------------------
    → (∀ (m : ℕ) → m < suc n → P m)
  step n cov m m<sn with choose m n m<sn
  ... | inj₁ m<n   =  cov m m<n
  ... | inj₂ refl  =  ih n cov

  cov : ∀ (n : ℕ) (m : ℕ) → m < n → P m
  cov = weak-ind base step
```

Choosing variables to be de Bruijn indices but using an extrinsic
formulation of types strikes me as an odd choice. Better all in
or all out. In particular, the extrinsic formulation may make it
easier to get the indices wrong. I'd much prefer a development that
is completely intrinsic.

Field initialisers. This term is slightly misleading, as it suggests
that we might update fields, but we never do so. I would call it the
field term or the field value.

Similarly, I find it annoying that some definitions with vectors
are based on nil and cons, and others on lookup. Again, I wonder
whether there is a development that only uses lookup.

"Here we instead treat records in a lazy fashion, declaring any record
to be a value, to save on some extra bookkeeping." Surely it is better
to give the usual definition, even at the cost of some extra
bookkeeping?  The bookkeeping saved is the ξ rule that reduces a
record to a value.  Far better to make this explicit, as it may not be
easy for some students to fill in.

Canonical forms. I'm not sure why you include canonical forms, as
in Properties they are not needed (appearing only as an exercise).

"The presence of the subsumption rule impacts its definition because
we must allow the type of the value `V` to be a subtype of `A`."
If you keep canonical forms, please justify this sentence. It is not
obvious.

"like the one in the [Properties](/Properties/)"
-->
"like the one in Chapter [Properties](/Properties/)"

You are working off an old proof of progress. The current proof does not
reference canonical forms.

"in the [DeBruijn](/DeBruijn/) chapter"
-->
"in Chapter [DeBruijn](/DeBruijn/)"

"_⦂ᵣ_⇒_" and "_⦂_⇒_"
a notation closer to the one in our formalisation for
simply-typed blame calculus would be
"_⦂_→ᴿ_" and "_⦂_→ˢ_"

I'm surprised to see Canonical pop up in the proof of preservation,
even in clauses that previously didn't require it. The text should
point this out and explain why it is needed. (Is it needed? My
experience getting rid of canonical in the proof of preservation
suggests that it might be worth looking for alternatives.)

"Case `⊢#` and `ξ-#`: So `∅ ⊢ M ⦂ ⦗ ls ⦂ As ⦘`, `lookup ls i ≡ l`,
`lookup As i ≡ A`, and `M —→ M′`." Replase "So" by "We have" to match
phrasing used elsewhere. (I haven't seen "So used in this way before.)

"Exercise `intrinsic-records`" Why does the intrinsic formulation
have to be algorithmic?

"Exercise `variants`" I try to limit (recommended) to exercises that I
expect to assign to the students. This exercise seems on the hard side
for that purpose. Perhaps make it a stretch exercise instead? Note
also that the last part of the question ("Come up with an algorithmic
subtyping rule for variant types") isn't appropriate for a recommended
question, as the terms in it are only defined in an earlier stretch
question. That could be fixed by turning the last sentence into a
separate stretch exercise.
