\begin{code}
open import Data.Nat (ℕ; zero; suc)

data Env : Set where
  ε : Env
  _,* : Env → Env

data _∋* : Env → Set where
  Z : ∀ {Γ : Env} → Var (Γ ,*)
  S : ∀ {Γ : Env} → Var Γ → Var (Γ ,*)

data _⊢* : Env → Set where
  var : ∀ {Γ : Env} → Var Γ → Tm Γ
  ƛ   : Var (Γ ,*) → Var Γ
  _·_ : Var Γ → Var Γ → Var Γ

\end{code}
