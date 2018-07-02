infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _                      =  V
... | no  _                      =  ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _                      =  ƛ x ⇒ N
... | no  _                      =  ƛ x ⇒ (N [ y := V ])
(L · M) [ y := V ]               =  (L [ y := V ]) · (M [ y := V ])
(`zero) [ y := V ]               =  `zero
(`suc M) [ y := V ]              =  `suc (M [ y := V ])
(`case L
  [zero⇒ M
  |suc x ⇒ N ])
  [ y := V ] with x ≟ y
... | yes _                      =  `case L [ y := V ]
                                       [zero⇒ M [ y := V ]
                                       |suc x ⇒ N ]
... | no  _                      =  `case L [ y := V ]
                                       [zero⇒ M [ y := V ]
                                       |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _                      =  μ x ⇒ N
... | no  _                      =  μ x ⇒ (N [ y := V ])

subst : ∀ {Γ x N V A B}
  → ∅ ⊢ V ⦂ A
  → Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
  → Γ ⊢ N [ x := V ] ⦂ B
subst {x = y} ⊢V (⊢` {x = x} Z) with x ≟ y
... | yes refl     =  weaken ⊢V
... | no  x≢y      =  ⊥-elim (x≢y refl)
subst {x = y} ⊢V (⊢` {x = x} (S x≢y ∋x)) with x ≟ y
... | yes refl     =  ⊥-elim (x≢y refl)
... | no  _        =  ⊢` ∋x
subst {x = y} ⊢V (⊢ƛ {x = x} ⊢N) with x ≟ y
... | yes refl     =  ⊢ƛ (drop ⊢N)
... | no  x≢y      =  ⊢ƛ (subst ⊢V (swap x≢y ⊢N))
subst ⊢V (⊢L · ⊢M) = subst ⊢V ⊢L · subst ⊢V ⊢M
subst ⊢V ⊢zero     =  ⊢zero
subst ⊢V (⊢suc ⊢M) =  ⊢suc (subst ⊢V ⊢M)
subst {x = y} ⊢V (⊢case {x = x} ⊢L ⊢M ⊢N) with x ≟ y
... | yes refl     =  ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (drop ⊢N)
... | no  x≢y      =  ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (subst ⊢V (swap x≢y ⊢N))
subst {x = y} ⊢V (⊢μ {x = x} ⊢M) with x ≟ y
... | yes refl     =  ⊢μ (drop ⊢M)
... | no  x≢y      =  ⊢μ (subst ⊢V (swap x≢y ⊢M))
