Everyone on this list will be familiar with Progress and Preservation
for terms in a typed calculus.  Write ∅ ⊢ M : A to indicate that term
M has type A for closed M.

  Progress.  If ∅ ⊢ M : A then either M is a value or M —→ N,
  for some term N.

  Preservation.  If ∅ ⊢ M : A and M —→ N then ∅ ⊢ N : A.

It is easy to combine these two proofs into an evaluator.
Write —↠ for the transitive and reflexive closure of —→.

  Evaluation.  If ∅ ⊢ M : A, then for every natural number n,
  either M —↠ V, where V is a value and the reduction sequence
  has no more than n steps, or M —↠ N, where N is not a value
  and the reduction sequence has n steps.

Evaluation implies that either M —↠ V or there is an infinite
sequence M —→ M₁ —→ M₂ —→ ... that never reduces to a value;
but this last result is not constructive, as deciding which of
the two results holds is not decidable.

An Agda implementation of Evaluation provides an evaluator for terms:
given a number n it will perform up to n steps of evaluation, stopping
early if a value is reached. This is entirely obvious (at least in
retrospect), but I have not seen it written down anywhere. For
instance, this approach is not exploited in Software Foundations to
evaluate terms (other methods are used instead).  I have used it
in my draft textbook:

  https:plfa.inf.ed.ac.uk

Questions: What sources in the literature should one cite for this
technique?  How well-known is it as folklore?
