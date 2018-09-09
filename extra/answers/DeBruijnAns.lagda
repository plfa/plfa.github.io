---
title     : "DeBruijn Answers"
layout    : page
permalink : /DeBruijnAns
---


#### Exercise `V¬—→`

Adapt the reesults of the previous section to show values do
not reduce, and its corollary, terms that reduce are not
values.

\begin{code}
V¬—→ : ∀ {Γ A} {M N : Γ ⊢ A} → Value M → ¬ (M —→ N)
V¬—→ V-ƛ        ()
V¬—→ V-zero     ()
V¬—→ (V-suc VM) (ξ-suc M—→N) = V¬—→ VM M—→N

—→¬V : ∀ {Γ A} {M N : Γ ⊢ A} → (M —→ N) → ¬ Value M
—→¬V M—→N VM  =  V¬—→ VM M—→N
\end{code}
