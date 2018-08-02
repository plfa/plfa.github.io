-- Factored definition of substitution



infix 9 _[_:=_]
infix 9 _⟨_⟩[_:=_]

_[_:=_]   : Term → Id → Term → Term

_⟨_⟩[_:=_] : Term → Id → Id → Term → Term
N ⟨ x ⟩[ y := V ] with x ≟ y
... | yes _                  =  N
... | no  _                  =  N [ y := V ]

(` x) [ y := V ] with x ≟ y
... | yes _                  =  V
... | no  _                  =  ` x
(ƛ x ⇒ N) [ y := V ]         =  ƛ x ⇒ N ⟨ x ⟩[ y := V ]
(L · M) [ y := V ]           =  (L [ y := V ]) · (M [ y := V ])
(`zero) [ y := V ]           =  `zero
(`suc M) [ y := V ]          =  `suc (M [ y := V ])
(case L
  [zero⇒ M
  |suc x ⇒ N ]) [ y := V ]   =  case L [ y := V ]
                                   [zero⇒ M [ y := V ]
                                   |suc x ⇒ N ⟨ x ⟩[ y := V ] ]
(μ x ⇒ N) [ y := V ]         =  μ x ⇒ (N ⟨ x ⟩[ y := V ])



subst : ∀ {Γ y N V A B}
  → ∅ ⊢ V ⦂ B
  → Γ , y ⦂ B ⊢ N ⦂ A
    --------------------
  → Γ ⊢ N [ y := V ] ⦂ A

substvar : ∀ {Γ x y V A B}
  → ∅ ⊢ V ⦂ B
  → Γ , y ⦂ B ∋ x ⦂ A
    ------------------------
  → Γ ⊢ (` x) [ y := V ] ⦂ A 

substbind : ∀ {Γ x y N V A B C}
  → ∅ ⊢ V ⦂ B
  → Γ , y ⦂ B , x ⦂ A ⊢ N ⦂ C
    ---------------------------------
  → Γ , x ⦂ A ⊢ N ⟨ x ⟩[ y := V ] ⦂ C

subst ⊢V (⊢` ∋x)           =  substvar ⊢V ∋x
subst ⊢V (⊢ƛ ⊢N)           =  ⊢ƛ (substbind ⊢V ⊢N)
subst ⊢V (⊢L · ⊢M)         =  subst ⊢V ⊢L · subst ⊢V ⊢M
subst ⊢V ⊢zero             =  ⊢zero
subst ⊢V (⊢suc ⊢M)         =  ⊢suc (subst ⊢V ⊢M)
subst ⊢V (⊢case ⊢L ⊢M ⊢N)  =  ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (substbind ⊢V ⊢N)
subst ⊢V (⊢μ ⊢N)           =  ⊢μ (substbind ⊢V ⊢N)

substvar {x = x} {y = y} ⊢V Z with x ≟ y
... | yes refl             =  weaken ⊢V
... | no  x≢y              =  ⊥-elim (x≢y refl)
substvar {x = x} {y = y} ⊢V (S x≢y ∋x) with x ≟ y
... | yes refl             =  ⊥-elim (x≢y refl)
... | no  _                =  ⊢` ∋x

substbind {x = x} {y = y} ⊢V ⊢N with x ≟ y
... | yes refl             =  drop ⊢N
... | no  x≢y              =  subst ⊢V (swap x≢y ⊢N)
