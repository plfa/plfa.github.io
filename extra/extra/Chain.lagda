The reflexive and transitive closure `↠` of an arbitrary relation `↦`
is the smallest relation that includes `↦` and is also reflexive
and transitive.  We could define this directly, as follows.
\begin{code}
module Closure (A : Set) (_↦_ : A → A → Set) where

  data _↠_ : A → A → Set where

    refl : ∀ {M}
        --------
      → M ↠ M

    trans : ∀ {L M N}
      → L ↠ M
      → M ↠ N
        --------
      → L ↠ N

    inc : ∀ {M N}
      → M ↦ N
        --------
      → M ↠ N
\end{code}
Here we use a module to define the reflexive and transitive
closure of an arbitrary relation.
The three clauses specify that `↠` is reflexive and transitive,
and that `↦` implies `↠`.

However, it will prove more convenient to define the transitive
closure as a sequence of zero or more steps of the underlying
relation, along lines similar to that for reasoning about
chains of equalities
Chapter [Equality]({{ site.baseurl }}{% link out/plta/Equality.md %}).
\begin{code}
module Chain (A : Set) (_↦_ : A → A → Set) where

  infix  2 _↠_
  infix  1 begin_
  infixr 2 _↦⟨_⟩_
  infix  3 _∎

  data _↠_ : A → A → Set where
    _∎ : ∀ M
        ---------
      → M ↠ M

    _↦⟨_⟩_ : ∀ L {M N}
      → L ↦ M
      → M ↠ N
        ---------
      → L ↠ N

  begin_ : ∀ {M N} → (M ↠ N) → (M ↠ N)
  begin M↠N = M↠N
\end{code}
We can read this as follows.

* From term `M`, we can take no steps,
  giving a step of type `M ↠ M`.
  It is written `M ∎`.

* From term `L` we can take a single of type `L ↦ M`
  followed by zero or more steps of type `M ↠ N`,
  giving a step of type `L ↠ N`,
  It is written `L ⟨ L↦M ⟩ M↠N`,
  where `L↦M` and `M↠N` are steps of the appropriate type.

The notation is chosen to allow us to lay
out example reductions in an appealing way,
as we will see in the next section.

We then instantiate the second module to our specific notion
of reduction step.
\begin{code}
open Chain (Term) (_↦_)
\end{code}
