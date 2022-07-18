import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_; s≤s)
open import Data.Nat.Properties using (+-identityʳ; +-suc; m≤n+m; ≤-pred; +-assoc)

-- Modulus

-- nat-eq = λ n m a b → if (n == m) then a else b
nat-eq : {a : Set} → ℕ → ℕ → a → a → a
nat-eq zero zero f g = f
nat-eq zero (suc n) f g = g
nat-eq (suc m) zero f g = g
nat-eq (suc m) (suc n) f g = nat-eq m n f g

mod'-help : ℕ → ℕ → ℕ → ℕ
mod'-help zero md r = r
mod'-help (suc n) md r = nat-eq md r (mod'-help n md zero) (mod'-help n md (suc r))

mod' : ℕ → ℕ → ℕ
mod' n zero = zero
mod' n (suc m) = mod'-help n m zero

-- mod-help n md c r
-- invariants
--   c + r ≡ md
--   n0 mod (suc md) ≡ (n + r) mod (suc md)
mod-help : ℕ → ℕ → ℕ → ℕ → ℕ
mod-help zero md c r = r
mod-help (suc n) md zero r = mod-help n md md zero
mod-help (suc n) md (suc c) r = mod-help n md c (suc r)

_mod_ : ℕ → ℕ → ℕ
_mod_ n zero = zero
_mod_ n (suc m) = mod-help n m m zero

infix 7 _mod_

_ : mod' 0 3 ≡ 0
_ = refl
_ : mod' 1 3 ≡ 1
_ = refl
_ : mod' 2 3 ≡ 2
_ = refl
_ : mod' 3 3 ≡ 0
_ = refl
_ : mod' 4 3 ≡ 1
_ = refl

_ : 0 mod 3 ≡ 0
_ = refl
_ : 1 mod 3 ≡ 1
_ = refl
_ : 2 mod 3 ≡ 2
_ = refl
_ : 3 mod 3 ≡ 0
_ = refl
_ : 4 mod 3 ≡ 1
_ = refl

+≡⇒≤-r : (a b c : ℕ) → a + b ≡ c → b ≤ c
+≡⇒≤-r a b c ab=c rewrite sym ab=c = m≤n+m b a

+-suc-≡ : (c r md : ℕ) → suc (c + r) ≡ md → c + suc r ≡ md
+-suc-≡ c r md eq rewrite +-suc c r = eq

≤-mod-help : (n md c r : ℕ) → (c + r ≡ md) → mod-help n md c r ≤ md
≤-mod-help zero md c r eq = +≡⇒≤-r c r md eq
≤-mod-help (suc n) md zero r eq = ≤-mod-help n md md zero (+-identityʳ md)
≤-mod-help (suc n) md (suc c) r eq = ≤-mod-help n md c (suc r) (+-suc-≡ c r md eq)


-- mod-help n m m zero ≤ m
≤-mod : (n m : ℕ) → n mod (suc m) ≤ m
≤-mod n m = ≤-mod-help n m m zero (+-identityʳ m)

zero-mod : (m : ℕ) → zero mod m ≡ zero
zero-mod zero = refl
zero-mod (suc m) = refl

m+a-mod-m-help : (n md c r : ℕ) → mod-help (c + n) md c r ≡ mod-help n md zero (c + r)
m+a-mod-m-help n md zero r = refl
m+a-mod-m-help n md (suc c) r rewrite sym (+-suc c r)= m+a-mod-m-help n md c (suc r)

m+a-mod-m : (a m : ℕ) → (m + a) mod m ≡ a mod m
m+a-mod-m a zero = refl
m+a-mod-m a (suc m) =
  begin
    mod-help (suc (m + a)) m m zero
  ≡⟨ cong (λ x → mod-help x m m zero) (sym (+-suc m a)) ⟩
    mod-help (m + suc a) m m zero
  ≡⟨ m+a-mod-m-help (suc a) m m zero ⟩
    mod-help (suc a) m zero (m + zero)
  ≡⟨ cong (mod-help (suc a) m zero) (+-identityʳ m) ⟩
    mod-help (suc a) m zero m
  ≡⟨⟩
    mod-help a m m zero
  ∎

m-mod-m : (m : ℕ) → m mod m ≡ zero
m-mod-m m =
  begin
    m mod m
  ≡⟨ cong (_mod m) (sym (+-identityʳ m)) ⟩
    (m + zero) mod m
  ≡⟨ m+a-mod-m zero m ⟩
    zero mod m
  ≡⟨ zero-mod m ⟩
    zero
  ∎

s*-mod : (s a m : ℕ) → (s * m + a) mod m ≡ a mod m
s*-mod zero a m = refl
s*-mod (suc s) a m =
  begin
    (m + s * m + a) mod m
  ≡⟨ cong (_mod m) (+-assoc m (s * m) a) ⟩
    (m + (s * m + a)) mod m
  ≡⟨ m+a-mod-m (s * m + a) m ⟩
    (s * m + a) mod m
  ≡⟨ s*-mod s a m ⟩
    a mod m
  ∎

st*-mod : (s t a m : ℕ) → (s * m + a) mod m ≡ (t * m + a) mod m
st*-mod s t a m =
  begin
    (s * m + a) mod m
  ≡⟨ s*-mod s a m ⟩
    a mod m
  ≡⟨ sym (s*-mod t a m) ⟩
    (t * m + a) mod m
  ∎

<-m-mod-help-help : (n md c r : ℕ) → n ≤ c → mod-help n md c r ≡ n + r
<-m-mod-help-help zero md c r n≤c = refl
<-m-mod-help-help (suc n) md (suc c) r sn≤sc rewrite sym (+-suc n r) = <-m-mod-help-help n md c (suc r) (≤-pred sn≤sc)

<-m-mod-help : (n m : ℕ) → n < suc m → mod-help n m m zero ≡ n
<-m-mod-help n m n<sm =
  begin
    mod-help n m m zero
  ≡⟨ <-m-mod-help-help n m m zero (≤-pred n<sm) ⟩
    n + zero
  ≡⟨ +-identityʳ n ⟩
    n
  ∎

<-m-mod : (n m : ℕ) → n < m → n mod m ≡ n
<-m-mod n (suc m) n<m = <-m-mod-help n m n<m

mod-idempotent : (a m : ℕ) → (a mod m) mod m ≡ a mod m
mod-idempotent a zero = refl
mod-idempotent a (suc m) = <-m-mod (a mod suc m) (suc m) (s≤s (≤-mod a m))

suc-mod : (a m : ℕ) → (suc a) mod m ≡ (suc (a mod m)) mod m
suc-mod-help : (n md c r : ℕ) → c + r ≡ md → mod-help (suc n) md c r ≡ mod-help (suc (mod-help n md c r)) md md zero
-- r ≡ md → zero ≡ mod-help (suc r) md md zero
suc-mod-help zero md zero r c+r≡md rewrite c+r≡md = sym (m-mod-m (suc md))
-- r ≡ md → mod-help (suc n) md md zero ≡ mod-help (suc (mod-help n md md zero)) md md zero
suc-mod-help (suc n) md zero r c+r≡md = suc-mod n (suc md)
-- suc (c + r) ≡ md → suc r ≡ mod-help (suc r) md md zero
suc-mod-help zero md (suc c) r c+r≡md = -- <-m-mod
  begin
    suc r
  ≡⟨ sym (<-m-mod (suc r) (suc md) sr<smd) ⟩
    (suc r) mod (suc md)
  ≡⟨⟩
    mod-help (suc r) md md zero
  ∎
  where
    sr≤sc+r : suc r ≤ suc (c + r)
    sr≤sc+r = s≤s (m≤n+m r c)
    sr≤md : suc r ≤ md
    sr≤md rewrite sym c+r≡md = sr≤sc+r
    sr<smd : suc r < suc md
    sr<smd = s≤s sr≤md
-- mod-help (suc n) md c (suc r) ≡ mod-help (suc (mod-help n md c (suc r))) md md zero
suc-mod-help (suc n) md (suc c) r c+r≡md = suc-mod-help n md c (suc r) c+sr≡md
  where
    c+sr≡md : c + suc r ≡ md
    c+sr≡md rewrite +-suc c r = c+r≡md
suc-mod a zero = refl
suc-mod a (suc m) = suc-mod-help a m m zero (+-identityʳ m)

+-mod-l : (a b m : ℕ) → (a + b) mod m ≡ (a mod m + b) mod m
-- b mod m ≡ (zero mod m + b) mod m
+-mod-l zero b m = {!!}
-- suc (a + b) mod m ≡ (suc a mod m + b) mod m
+-mod-l (suc a) b m =
  begin
    suc (a + b) mod m
  ≡⟨ {!!} ⟩
    suc ((a + b) mod m) mod m
  ≡⟨ {!!} ⟩
    suc ((a mod m + b) mod m) mod m
  ≡⟨ {!!} ⟩
    suc (a mod m + b) mod m
  ≡⟨ {!!} ⟩
    ((suc (a mod m)) + b) mod m
  ≡⟨ {!!} ⟩ -- This is missing. Doesn't seem to work. !!!!!!!!!!!!!!!!!!
    ((suc (a mod m)) mod m + b) mod m
  ≡⟨ {!!} ⟩
    (suc a mod m + b) mod m
  ∎

+-mod : (a b m : ℕ) → (a + b) mod m ≡ (a mod m + b mod m) mod m
-- b mod m ≡ (zero mod m + b mod m) mod m
+-mod zero b m = {!!}
-- suc (a + b) mod m ≡ (suc a mod m + b mod m) mod m
+-mod (suc a) b m =
  begin
    (suc (a + b)) mod m
  ≡⟨ {!!} ⟩
    (suc ((a + b) mod m)) mod m
  ≡⟨ {!!} ⟩
    (suc ((a mod m + b mod m) mod m)) mod m
  ≡⟨ {!!} ⟩
    (suc (a mod m + b mod m)) mod m
  ≡⟨ {!!} ⟩
    (suc (a mod m) + b mod m) mod m
  ≡⟨ {!!} ⟩ -- something missing
    ((suc (a mod m)) + b) mod m
  ≡⟨ {!!} ⟩
    ((suc (a mod m)) mod m + b mod m) mod m
  ≡⟨ {!!} ⟩
    ((suc a) mod m + b mod m) mod m
  ∎

*-mod : {a b m : ℕ} → (a * b) mod m ≡ ((a mod m) * (b mod m)) mod m
*-mod = {!!}
