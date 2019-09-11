Style guide for PLFA
============================

This is based on [the style guide for the Agda standard library](https://github.com/agda/agda-stdlib/blob/master/notes/style-guide.md).
Like it, this is very much a work-in-progress and is not exhaustive. 

## File structure

#### Module imports

* All module imports should be placed at the top of the file immediately
  after the module declaration.

* If the module takes parameters that require imports from other files
  then those imports only may be placed above the module declaration.

* If it is important that certain names only come into scope later in
  the file then the module should still be imported at the top of the
  file but it can be given a shorter name using `as` and then opened
  later on in the file when needed, e.g.
  ```agda
  import Data.List.Relation.Binary.Equality.Setoid as SetoidEquality
  ...
  ...
  open SetoidEquality S
  ```

* The list of module imports should be in alphabetical order.

* When using only a few items from a module, the items should be
  enumerated in the import with `using` in order to make dependencies
  clearer.

#### Indentation

* The contents of a top-level module should have zero indentation.

* Every subsequent nested scope should then be indented by an additional
  two spaces.

* `where` blocks should be indented by two spaces and their contents
  should be aligned with the `where`.

* If the type of a term does not fit on one line then the subsequent
  lines of the type should all be indented by two spaces, e.g.
  ```agda
  map-cong₂ : ∀ {a b} {A : Set a} {B : Set b} 
    → ∀ {f g : A → B} {xs} 
    → All (λ x → f x ≡ g x) xs → map f xs ≡ map g xs
  ```

* As can be seen in the example above, function arrows at line breaks
  should always go at the beginning of the next line rather than the 
  end of the line. 

#### Module parameters

* Module parameters should be put on a single line if they fit.

* If they don't fit on a single line, then they should be spread out
  over multiple lines, each indented by two spaces. If they can be
  grouped logically by line then it is fine to do so, otherwise a line
  each is probably clearest.

* The `where` should go on it's own line at the end.

* For example:
  ```agda
  module Relation.Binary.Reasoning.Base.Single
    {a ℓ} {A : Set a} (_∼_ : Rel A ℓ)
    (refl : Reflexive _∼_) (trans : Transitive _∼_)
    where
  ```

#### Reasoning layout

* The `begin` clause should go on a new line.

* Every subsequent combinator `_≡⟨_⟩_` should go on its own line,
  with the intermediate terms on their own line, indented by two spaces.

* The relation sign (e.g. `≡`) for each line should be aligned if possible.

* For example:
  ```agda
  +-comm : Commutative _+_
  +-comm zero    n = sym (+-identityʳ n)
  +-comm (suc m) n = 
    begin
      suc m + n
    ≡⟨⟩
      suc (m + n)
    ≡⟨ cong suc (+-comm m n) ⟩
      suc (n + m)
    ≡⟨ sym (+-suc n m) ⟩
      n + suc m
    ∎
  ```

* When multiple reasoning frameworks need to be used in the same file, the
  `open` statement should always come in a where clause local to the
  definition. This way users can easily see which reasoning toolkit is
  being used. For instance:
  ```agda
  foo m n p = begin
    (...) ∎
    where open ≤-Reasoning
  ```

#### Record layout

* The `record` declaration should go on the same line as the rest of the proof.

* The next line with the first record item should start with a single `{`.

* Every subsequent item of the record should go on its own line starting with
  a `;`.

* The final line should end with `}` on its own.

* For example:
  ```agda
  ≤-isPreorder : IsPreorder _≡_ _≤_
  ≤-isPreorder = record
    { isEquivalence = isEquivalence
    ; reflexive     = ≤-reflexive
    ; trans         = ≤-trans
    }
  ```

#### `where` blocks

* `where` blocks are preferred rather than the `let` construction.

* The `where` should be placed on the line below the main proof,
  indented by two spaces.

* If the contents of the block is non-trivial then types should be
  provided alongside the terms, and all terms should be on lines after
  the `where`, e.g.
  ```agda
  statement : Statement
  statement = proof
    where
        proof : Proof
        proof = some-very-long-proof
  ```

* If the contents of the block is trivial or is an `open` statement then
  it can provided on the same line as the `where` and a type can be
  omitted, e.g.
  ```agda
  statement : Statement
  statement = proof
    where proof = x
  ```

#### Other

* Non-trivial proofs in `private` blocks are generally discouraged. If its
  non-trivial then the chances are someone will want to reuse it as some
  point!

* The `with` syntax is preferred over the use of `case` from the `Function`
  module.

## Types

#### Implicit and explicit arguments

* Functions arguments should be implicit if they can "almost always"
  be inferred. If there are common cases where they cannot be inferred
  then they should be left explicit.

* If there are lots of implicit arguments that are common to a collection
  of proofs they should be extracted by using an anonymous module.

* Implicit of type `Level` and `Set` can be generalised using `variable`.
  At the moment the policy is *not* to generalise over any other types in
  order to minimise the amount of information that users have to keep in
  their head concurrently.

## Naming conventions

* Names should be descriptive - i.e. given the name of a proof and the
  module it lives in then users should be able to make a reasonable
  guess at what it contains.

* Terms from other modules should only be renamed to avoid name clashes,
  otherwise all names should be used as defined.

* Datatype names should be capitalised and function names should be
  lowercase.

#### Variables

* Natural variables are named `m`, `n`, `o`, ... (default `n`)

* Integer variables are named `i`, `j`, `k`, ... (default `i`)

* Rational variables are named `p`, `q`, `r`, ... (default `p`)

* When naming proofs, the variables should occur in order, e.g.
  `m≤n+m` rather than `n≤m+n`.

* Collections of elements are usually indicated by appending an `s`
  (e.g. if you are naming your variables `x` and `y` then lists
  should be named `xs` and `ys`).


#### Preconditions and postconditions

* Preconditions should only be included in names of results if
  "important" (mostly judgement call).

* Preconditions of results should be prepended to a description
  of the result by using the symbol `⇒` in names (e.g. `asym⇒antisym`)

* Preconditions and postconditions should be combined using the symbols
  `∨` and `∧` (e.g. `m*n≡0⇒m≡0∨n≡0`)

* Try to avoid the need for bracketing but if necessary use square
  brackets (e.g. `[m∸n]⊓[n∸m]≡0`)

#### Operators and relations

* Operators and relations should be defined using mixfix notation where
  applicable (e.g. `_+_`, `_<_`)

* Common properties such as those in rings/orders/equivalences etc.
  have defined abbreviations (e.g. commutativity is shortened to `comm`).
  `Data.Nat.Properties` is a good place to look for examples.

* Properties should be by prefixed by the relevant operator/relation
  (e.g. commutativity of `_+_` is named `+-comm`)

* If the relevant unicode characters are available, negated forms of
  relations should be used over the `¬` symbol (e.g. `m+n≮n` should be
  used instead of `¬m+n<n`).

#### Functions and relations over specific datatypes

* When defining a new relation over a datatype
  (e.g. `Data.List.Relation.Binary.Pointwise`)
  it is often common to define how to introduce and eliminate that
  relation over various simple functions (e.g. `map`) over that datatype:
  ```agda
  map⁺ : Pointwise (λ a b → R (f a) (g b)) as bs →
                 Pointwise R (map f as) (map g bs)

  map⁻ : Pointwise R (map f as) (map g bs) →
                 Pointwise (λ a b → R (f a) (g b)) as bs
  ```
  Such elimination and introduction proofs are called the name of the
  function superscripted with either a `+` or `-` accordingly.
