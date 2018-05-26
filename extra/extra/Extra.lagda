## Disjunction

In order to state totality, we need a way to formalise disjunction,
the notion that given two propositions either one or the other holds.
In Agda, we do so by declaring a suitable inductive type.
\begin{code}
data _⊎_ : Set → Set → Set where
  inj₁ : ∀ {A B : Set} → A → A ⊎ B
  inj₂ : ∀ {A B : Set} → B → A ⊎ B
\end{code}
This tells us that if `A` and `B` are propositions then `A ⊎ B` is
also a proposition.  Evidence that `A ⊎ B` holds is either of the form
`inj₁ x`, where `x` is evidence that `A` holds, or `inj₂ y`, where
`y` is evidence that `B` holds.

We set the precedence of disjunction so that it binds less tightly than
inequality.
\begin{code}
infixr 1 _⊎_
\end{code}
Thus, `m ≤ n ⊎ n ≤ m` parses as `(m ≤ n) ⊎ (n ≤ m)`.

------------------------------------------------------------------------

I, along with many others, am a fan of Peirce's [Types and Programming
Languages][tapl], known by the acronym TAPL. One of my best students
started writing his own systems with no help from me, trained by that
book.

------------------------------------------------------------------------

\begin{code}
postulate
  extensionality : ∀ {A B : Set} → {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g

extensionality2 : ∀ {A B C : Set} → {f g : A → B → C} → (∀ (x : A) (y : B) → f x y ≡ g x y) → f ≡ g
extensionality2 fxy≡gxy = extensionality (λ x → extensionality (λ y → fxy≡gxy x y))
\end{code}



