Three possible formulations of `μ`

    μ N  —→  N [ μ N ]

    (μ N) · V  —→  N [ μ N , V ]

    (μ (ƛ N)) · V  —→  N [ μ (ƛ N) , V ]

The first is odd in that we substitute for `f` a term that is not a value.

One advantage of the first is that it also works perfectly well on other types.
For instance,

    case (μ x → suc x) [zero→ zero | suc x → x]

returns (μ x → suc x).

The second has two values of function type, both lambda abstractions and fixpoints.

What if the body of μ must first reduce to a value? Two cases.

    Value is a lambda.

    (μ f → N) · V
      —→  (μ f → ƛ x → N′) · V
      —→  (ƛ x → N′) [ f := μ f → ƛ x → N ] · V
      —→  (ƛ x → N′ [ f := μ f → ƛ x → N ]) · V
      —→  N′ [ f := μ f → ƛ x → N , x := V ]

    Value is itself a mu.

    (μ f → μ g → N) · V
      —→ (μ f → μ g → N′) · V
      —→ (μ f → μ g → λ x → N″) · V
      —→ (μ g → λ x → N″) [ f := μ f → μ g → λ x → N″ ] · V
      —→ (μ g → λ x → N″ [ f := μ f → μ g → λ x → N″ ]) · V
      —→ (λ x → N″ [ f := μ f → μ g → λ x → N″ ])
            [ g := μ g → λ x → N″ [ f := μ f → μ g → λ x → N″ ] · V
      —→ (λ x → N″ [ f := μ f → μ g → λ x → N″ ]
            [ g := μ g → λ x → N″ [ f := μ f → μ g → λ x → N″ ]) · V
      —→ N″ [ f := μ f → μ g → λ x → N″ ]
             [ g := μ g → λ x → N″ [ f := μ f → μ g → λ x → N″ ]
             [ x := V ]

    This is something you would *never* want to do, because f and g are
    bound to the same function. Better to avoid it by building functions
    into the syntax, I expect.
