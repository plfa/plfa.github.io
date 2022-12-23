Look at the following when revising the paper.

On 2018-07-07 00:45, Philip Wadler wrote:
Indeed, I considered using Delay for the evaluator in the textbook,
but decided that supplying a step count was simpler, and avoided the
need to explain coinduction.

In "Operational Semantics Using the Partiality Monad"
(https://doi.org/10.1145/2364527.2364546) I defined the semantics of an
untyped language by giving a definitional interpreter, using the delay
monad. Then I proved type soundness for this language as a negative
statement (using a more positive lemma):

  [] ⊢ t ∈ σ → ¬ (⟦ t ⟧ [] ≈ fail)

Thus, instead of starting with type soundness and deriving an evaluator,
I started with an evaluator and proved type soundness.

This kind of exercise has also been performed using fuel, see Siek's
"Type Safety in Three Easy Lemmas"
(https://siek.blogspot.com/2013/05/type-safety-in-three-easy-lemmas.html)
and "Functional Big-Step Semantics" by Owens et al.
(https://doi.org/10.1007/978-3-662-49498-1_23).
