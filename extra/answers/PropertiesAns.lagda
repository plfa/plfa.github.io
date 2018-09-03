---
title     : "Properties Answers"
layout    : page
permalink : /PropertiesAns
---


#### Exercise `unstuck`

No well-typed term is stuck.
\begin{code}
unstuck′ : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    -----------
  → ¬ (Stuck M)
unstuck′ ⊢M ⟨ ¬M—→N , ¬VM ⟩ with progress ⊢M 
... | step M—→N  =  ¬M—→N M—→N
... | done VM   =  ¬VM VM
\end{code}

Any descendant of a well-typed term is well-typed.
\begin{code}
preserves′ : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —↠ N
    ---------
  → ∅ ⊢ N ⦂ A
preserves′ ⊢M (M ∎)             =  ⊢M
preserves′ ⊢L (L —→⟨ L—→M ⟩ M—↠N)  =  preserves′ (preserve ⊢L L—→M) M—↠N
\end{code}

Combining the above gives us the desired result.
\begin{code}
wttdgs′ : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —↠ N
    -----------
  → ¬ (Stuck N)
wttdgs′ ⊢M M—↠N  =  unstuck′ (preserves′ ⊢M M—↠N)
\end{code}
