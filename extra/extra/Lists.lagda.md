#### Exercise `Any-∃` (practice)

Show that `Any P xs` is isomorphic to `∃[ x ] (x ∈ xs × P x)`.

```
Any-∃ : ∀ {A : Set} {P : A → Set} {xs : List A} → Any P xs ≃ ∃[ x ] (x ∈ xs × P x)
Any-∃ {A} {P} {xs} = record
  { to = to
  ; from = {!!}
  ; from∘to = {!!}
  ; to∘from = {!!} }
  where
  to : ∀ {A : Set} {P : A → Set} {xs : List A} → Any P xs → ∃[ x ] (x ∈ xs × P x)
  to (here {x = x} px) = ⟨ x , ⟨ here refl , px ⟩ ⟩
  to (there anyp) with to anyp
  ...                | ⟨ x , ⟨ x∈xs , px ⟩ ⟩ = ⟨ x , ⟨ there x∈xs , px ⟩ ⟩

```
