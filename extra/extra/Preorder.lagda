## Formalising preorder

\begin{code}
record IsPreorder {A : Set} (_≤_ : A → A → Set) : Set where
  field
    reflexive : ∀ {x : A} → x ≤ x
    trans : ∀ {x y z : A} → x ≤ y → y ≤ z → x ≤ z

IsPreorder-≤ : IsPreorder _≤_
IsPreorder-≤ =
  record
    { reflexive = ≤-refl
    ; trans = ≤-trans
    }

record Preorder : Set₁ where
  field
    A : Set
    _≺_ : A → A → Set
    isPre : IsPreorder _≺_
\end{code}
