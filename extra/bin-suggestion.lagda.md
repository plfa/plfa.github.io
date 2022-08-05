Michel Levy has a suggestion for improving Bin in Quantifiers.

In the Quantifiers chapter, I found the Bin-isomorphism exercise
difficult. I suggest the following variation. A canonical element is an
element (to n). Hence the alternative definition of Can.

```
data Can': Bin -> Set where
  tocan : {b : Bin } -> ∃[ n ] (b ≡ to n) -> Can' b
```

With this definition the proof of the property, "if b is canonical, then
`to (from b) = b`" becomes much simpler.
```
tofrom: (b: Bin) -> Can' b -> to (from b) ≡ b
tofrom b (tocan ⟨ n , btn ⟩) =
  Eq.trans (Eq.cong (to ∘ from) btn) (Eq.trans (Eq.cong to (fromto n)) (Eq.sym btn))

ℕ≃Can : ℕ ≃ ∃[ b ] (Can' b)
ℕ≃Can =
  record  {
  to = \ { n -> ⟨ to n , tocan ⟨ n , refl ⟩ ⟩}
  ; from = \ { ⟨ _ , tocan ⟨ n , _ ⟩ ⟩ -> n }
  ; from∘to = \ { n -> refl}
  ; to∘from = \ { ⟨ _ , tocan ⟨ n , refl ⟩ ⟩ -> refl }
  }
```
