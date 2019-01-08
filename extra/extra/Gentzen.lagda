## A brief history of logic

Formulations of logic go back to Aristotle in the third century BCE,
but the modern approach to symbolic logic did not get started until
the 18th century with the work of Boole.  Universal and existential
quantification were introduced by Frege and Pierce, and Peano
introduced the notations `(x)A` and `(∃x)A` to stand for them.
Peano's notation was adopted by Russell and Whitehead for use in
*Principia Mathematica*.

The formulation of logic most widely used today is *Natural
Deduction*, introduced by Gerhard Gentzen in 1935, in what was in
effect his doctoral dissertation.  Gentzen's major insight was to
write the rules of logic in *introduction* and *elimination* pairs.

By the way, that same work of Gentzen also introduced Sequent
Calculus, the second most widely used formulation of logic, and the
symbol ∀ to mean *for all*---so there is a goal for you if you are
about to write your doctoral dissertation!

## Natural Deduction

Here are the inference rules for Natural Deduction annotated with Agda terms.


    M : A    N : B
    ---------------- ×-I
    (M , N) : A × B

    L : A × B
    --------- ×-E₁
    fst L : A

    L : A × B
    --------- ×-E₂
    snd L : B

    M : A
    -------------- ⊎-I₁
    inj₁ M : A ⊎ B

    N : B
    -------------- ⊎-I₂
    inj₂ N : A ⊎ B

                (x : A)  (y : B)
    L : A ⊎ B   Px : C   Qy : C
    ---------------------------------------- ⊎-E
    (λ { inj₁ x → Px ; inj₂ y → Qy }) L : C

    (x : A)
    Nx : B
    ------------------- →-I
    (λ x → Nx) : A → B

    L : A → B    M : A
    ------------------- →-E
    L M : B

    (x : A)
    Nx : Bx
    ----------------------------- ∀-I
    (λ x → Nx) : ∀ (x : A) → Bx

    L : ∀ (x : A) → Bx    M : A
    ---------------------------- ∀-E
    L M : Bx [ x := M ]

             
    M : A    Nx [ x := M ] : Bx [ x := M ]
    -------------------------------------- ∃-I
    (M , Nx) : ∃ A (λ x → Bx)

                         (x : A, y : Bx)
    L : ∃ A (λ x → Bx)      Pxy : C
    ------------------------------------ ∃-E
    (λ { (x , y) → Pxy }) L : C

[These rules---especially toward the end---are rather complicated.
Is this really the best way to explain this material?  Maybe it
is better to give a less formal explanation for now, and introduce
the more formal rules when giving a model of Barendregt's generalised
lambda calculus toward the end of the book, if I get that far.]

These rules differ only slightly from Gentzen's original.  We
have written `A × B` where Gentzen wrote `A & B`, for reasons
that will become clear later.


## Natural deduction as a logic (no terms)

We adopt an idea from Gentzen's sequent calculus, writing `Γ ⊢ A` to
make explicit the set of assumptions `Γ` from which proposition `A`
follows.

    Γ ⊢ A
    Γ ⊢ B
    --------- ×-I
    Γ ⊢ A × B

    Γ ⊢ A × B
    --------- ×-E₁
    Γ ⊢ A

    Γ ⊢ A × B
    --------- ×-E₁₂
    Γ ⊢ B

    ----- ⊤-I
    Γ ⊢ ⊤

    Γ ⊢ A
    --------- +-I₁
    Γ ⊢ A ⊎ B

    Γ ⊢ B
    --------- +-I₂
    Γ ⊢ A ⊎ B

    Γ ⊢ A ⊎ B
    Γ , A ⊢ C
    Γ , B ⊢ C
    ----------- +-E
    Γ ⊢ C

    Γ ⊢ ⊥
    ----- ⊥-E
    Γ ⊢ C

    Γ , A ⊢ B
    --------- →-I
    Γ ⊢ A → B

    Γ ⊢ A → B
    Γ ⊢ A
    --------- →-E
    Γ ⊢ B

    Γ , A ⊢ ⊥
    --------- ¬-I
    Γ ⊢ ¬ A

    Γ ⊢ ¬ A
    Γ ⊢ A
    -------- ¬-E
    Γ ⊢ ⊥

    Γ , x : A ⊢ B
    ------------------ ∀-I  (x does not appear free in Γ)
    Γ ⊢ ∀ (x : A) → B

    Γ ⊢ ∀ (x : A) → B
    Γ ⊢ M : A
    ----------------- ∀-E
    Γ ⊢ B [ x := M ]

    Γ ⊢ M : A
    Γ ⊢ B [ x := M ]
    ----------------- ∃-I
    Γ ⊢ ∃ [ x : A ] B

    Γ ⊢ ∃ [ x : A ] B
    Γ , x : A ⊢ C
    ----------------- ∃-E  (x does not appear free in Γ or C)
    Γ ⊢ C
