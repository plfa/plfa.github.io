Outline of
Programming Languages Theory in Agda (PLTA)
  [can I think of a wadlerian name?]


Naturals
  definition of naturals and why it makes sense
    Nat; zero; suc
Recursion
  recursive definitions and why they make sense
    _+_; _*_; _∸_
  Exercises
    _^_; _⊔_; _⊓_
Induction
  proof by induction and its relation to recursion
    +-assoc; +-suc; +-identity; +-comm
    *-distributes-+
  classifying operations
    associative; identity; commutative; distributive; idempotent
    monoid; Abelian monoid; ring
  Exercises
    *-assoc; *-comm; ∸-+-assoc
    ^-distributes-*; +-distributes-⊔; +-distributes-⊓
    counterexamples to show that _^_ is not associative or commutative
Relations
  specifying relations by an inductive datatype
  classifying relations
    reflexive; symmetric; antisymmetric; transitive; total
    preorder; partial order; total order
    [do I also want irreflexive (requires negation)?]
    [should I include a bit of lattice theory?]
  proof by induction over evidence
    ≤-refl; ≤-trans; ≤-antisym; ≤-total
    [define ≤-total using ⊎ or a custom datatype? Probably custom is better]    
  decidable relations
    total order corresponds to a decidable relation
Lists
  definition
    data List : Set → Set where
      [] : ∀ {A : Set} → List A
      _::_ : ∀ {A : Set} → A → List A → List A
  equivalent way to write:
    data List (A : Set) : Set where
      [] : List A
      _::_ : A → List A → List A
  length
  append _++_
    infixr 5 _++_
    ++-monoid
  and or any all sum product
  reverse
    reverse and append
    double reverse
    fast and slow reverse and their equivalence
    exercise : length xs ≡ length (reverse xs)
  function composition
  map
    composition of two maps
  foldr
    composition of foldr with map
  foldl
    relation of foldr, foldl, and reverse
  lexicographic order
    define using a nested module
    data Lex {a ℓ₁ ℓ₂} {A : Set a} (P : Set)
             (_≈_ : Rel A ℓ₁) (_≺_ : Rel A ℓ₂) : Rel (List A) (ℓ₁ ⊔ ℓ₂) where
      base : P                             → Lex P _≈_ _≺_ []       []
      halt : ∀ {y ys}                      → Lex P _≈_ _≺_ []       (y ∷ ys)
      this : ∀ {x xs y ys} (x≺y : x ≺ y)   → Lex P _≈_ _≺_ (x ∷ xs) (y ∷ ys)
      next : ∀ {x xs y ys} (x≈y : x ≈ y)
             (xs<ys : Lex P _≈_ _≺_ xs ys) → Lex P _≈_ _≺_ (x ∷ xs) (y ∷ ys)

Logic
  isomorphism
    use two different definitions of ≤ as an example
  projection
    will get an example later, with ⊎-distributes-×
  conjunction and top
    ×-assoc; ×-comm; ×-ident (as isomorphisms)
  disjunction and bottom
    ⊥-elim
    ⊎-assoc; ⊎-comm; ⊎-ident (as isomorphisms)
  distributive laws
    ×-distributes-⊎ (as isomorphism)
      [The proof is straightforward but lengthy. Is there a way to shorten it?]
    ⊎-distributes-× (as projection)
  implication
    reflexive and transitive
  negation
    contrapositive: (A → B) → (¬ B → ¬ A)
    double negation introduction: A → ¬ ¬ A
    triple negation elimination: ¬ ¬ ¬ A → ¬ A
    excluded middle irrefutable: ¬ ¬ (A ⊎ ¬ A)
  for all
  there exists
    example: even n → ∃(λ m → n = 2 * m)
    exercise: odd n → ∃(λ m → n = 2 * m + 1)
    example: 
      ∀ (A : Set) (B : A → Set) → 
        (∀ (x : A) → B x) → ¬ ∃ (λ (x : A) → ¬ B x)
    exercise:
      ∀ (A : Set) (B : A → Set) →
        ∃ (λ (x : A) → B x) → ¬ (∀ (x : A) → ¬ B x)
  intuitionistic and classical logic
    following are all equivalent
      excluded middle: A ⊎ ¬ A
      double negation elimination: ¬ ¬ A → A
      Peirce's law: ∀ (A B : Set) → ((A → B) → A) → A
      de Morgan's law: ¬ (¬ A × ¬ B) → A ⊎ B
      implication implies disjunction: (A → B) → ¬ A ⊎ B
    show classical implies
      ∀ (A : Set) (B : A → Set) → 
        ¬ (∃(λ (x : A) → ¬ B x) → ∀ (x : A) → B x
      ∀ (A : Set) (B : A → Set) →
        ¬ (∀ (x : A) → ¬ B x) → ∃(λ (x : A) → B x)
    [demonstrate Kolmogorov's or Gödel's embedding]
  equivalence
    how it is defined
    biimplication with Leibniz equality

Equivalence [not sure where this goes]
  how it is defined
  library for reasoning about it
Lambda notation [don't know where to put this]
  [Best if it comes *before* existentials]
Currying [don't know where to put this]
Structures [not sure where this goes]
  [distribute as they are introduced, or centralise in one chapter?]
  mathematical structures as records
    equivalence
    monoid; Abelian monoid; ring
    preorder; partial order; total order
    lattice
    isomorphism; projection;
    relation inclusion; biinclusion
  other properties of relations
    irreflexive
    complement of a relation




