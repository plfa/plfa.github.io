Extensionality of a function of two arguments

\begin{code}
extensionality2 : ∀ {A B C : Set} → {f g : A → B → C} → (∀ (x : A) (y : B) → f x y ≡ g x y) → f ≡ g
extensionality2 fxy≡gxy = extensionality (λ x → extensionality (λ y → fxy≡gxy x y))
\end{code}

Isomorphism of all and exists.
\begin{code}
¬∃∀ : ∀ {A : Set} {B : A → Set} → (¬ ∃ (λ (x : A) → B x)) ≃ ∀ (x : A) → ¬ B x
¬∃∀ =
  record
    { to   =  λ { ¬∃bx x bx → ¬∃bx (x , bx) }
    ; fro  =  λ { ∀¬bx (x , bx) → ∀¬bx x bx }
    ; invˡ =  λ { ¬∃bx → extensionality (λ { (x , bx) → refl }) } 
    ; invʳ =  λ { ∀¬bx → refl } 
    }
\end{code}
