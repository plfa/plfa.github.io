\documentclass{article}
\usepackage{bbm}
\usepackage[greek,english]{babel}
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{autofe}
\usepackage{agda}
\begin{document}

\begin{code}
data αβγδεζθικλμνξρστυφχψω : Set₁ where

postulate
  →⇒⇛⇉⇄↦⇨↠⇀⇁ : Set
\end{code}

\[
∀X [ ∅ ∉ X ⇒ ∃f:X ⟶  ⋃ X\ ∀A ∈ X (f(A) ∈ A) ]
\]
\end{document}
