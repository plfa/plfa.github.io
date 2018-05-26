### Identifier maps

\begin{code}
_∈?_ : ∀ (x : Id) → (xs : List Id) → Dec (x ∈ xs)
x ∈? xs = {!!}

data IdMap : Set where
  make : ∀ (xs : List Id) → (φ : ∀ {x} → x ∈ xs → Term) → IdMap

default : List Id → IdMap
default xs = make xs φ
  where
  φ : ∀ {x : Id} (x∈ : x ∈ xs) → Term
  φ {x} x∈  =  ` x

∅ : IdMap
∅ = make [] (λ())

infixl 5 _,_↦_

_,_↦_ : IdMap → Id → Term → IdMap
make xs φ , x ↦ M  = make xs′ φ′
  where
  xs′ = x ∷ xs
  φ′ : ∀ {x} → x ∈ xs′ → Term
  φ′ here        =  M
  φ′ (there x∈)  =  φ x∈
\end{code}
