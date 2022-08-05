infix  6  ƛ`_⇒_

ƛ`_⇒_ : Term → Term → Term
ƛ`_⇒_ (` x) N =  ƛ x ⇒ N
ƛ`_⇒_ _ _ = ⊥-elim impossible
  where postulate impossible : ⊥

plusᶜ′ : Term
plusᶜ′ =  ƛ` m ⇒ ƛ` n ⇒ ƛ` s ⇒ ƛ` z ⇒ (m · s · (n · s · z))
  where
  m = ` "m"
  n = ` "n"
  s = ` "s"
  z = ` "z"

_ : plusᶜ ≡ plusᶜ′
_ = refl
