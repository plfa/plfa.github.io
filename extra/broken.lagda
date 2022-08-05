## Our first corollary: rearranging

We can apply associativity to rearrange parentheses however we like.
Here is an example.

\begin{code}
+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + ((n + p) + q)
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ∎
\end{code}
