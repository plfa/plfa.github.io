open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Bool using (Bool; false; true; not)
open import Data.Empty
open import Data.Fin using (Fin; toℕ; fromℕ<)
open import Data.Fin.Properties using (toℕ<n; toℕ-fromℕ<)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Function
open import Relation.Nullary -- When restricting import, make sure C-c C-c (false because proof) to (no p) works.
open import plfa.part1.Isomorphism using (_≃_; _⇔_; _≲_; extensionality; ∀-extensionality; ≃-trans; ≃-sym)
open plfa.part1.Isomorphism.≃-Reasoning

---------------- Util ----------------

get-≤ : (m n : ℕ) → m ≤ n → ∃[ o ] (n ≡ o + m)
get-≤ 0 n z≤n = n , sym (+-identityʳ n)
get-≤ (suc m) (suc n) (s≤s m≤n) with get-≤ m n m≤n
... | o , refl = o , sym (+-suc o m)

<-trans-+1 : {m n o : ℕ} → m < n → n < o → suc m < o
<-trans-+1 {m} {n} {o} m<n n<o = ≤-trans (s≤s m<n) n<o

≮→≤ : {m n : ℕ} → ¬ (m < n) → n ≤ m
≮→≤ {zero} {zero} ¬m<n = z≤n
≮→≤ {zero} {suc n} ¬m<n = ⊥-elim (¬m<n (s≤s z≤n))
≮→≤ {suc m} {zero} ¬m<n = z≤n
≮→≤ {suc m} {suc n} ¬m<n = s≤s (≮→≤ (λ z → ¬m<n (s≤s z)))

≤→≮ : {m n : ℕ} → m ≤ n → ¬ (n < m)
≤→≮ {zero} {zero} z≤n ()
≤→≮ {suc m} {zero} ()
≤→≮ {suc m} {suc n} (s≤s m≤n) (s≤s n<m) = ≤→≮ m≤n n<m

≤-+-balanced : {m n : ℕ} → (o : ℕ) → m ≤ n → m + o ≤ n + o
≤-+-balanced {m} {n} o m≤n = +-mono-≤ m≤n (≤-refl {o})

<→≤ : {m n : ℕ} → m < n → m ≤ n
<→≤ {m} {n} m<n = ≤-trans (m≤n+m m 1) m<n

m∸o≤n : {m n o : ℕ} → m ≤ n + o → m ∸ o ≤ n
m∸o≤n {m} {n} {o} m≤n =
  ≤-Reasoning.begin
    m ∸ o
  ≤-Reasoning.≤⟨ ∸-monoˡ-≤ o m≤n ⟩
    n + o ∸ o
  ≤-Reasoning.≡⟨ m+n∸n≡m n o ⟩
    n
  ≤-Reasoning.∎

≤-uniq : {m n : ℕ} → (p p' : m ≤ n) → p ≡ p'
≤-uniq {zero} {zero} z≤n z≤n = refl
≤-uniq {zero} {suc n} z≤n z≤n = refl
≤-uniq {suc m} {suc n} (s≤s p) (s≤s p') = cong s≤s (≤-uniq p p')

---------------- Strictly Monotonic Basics ----------------

Strict-mon : (f : ℕ → ℕ) → Set
Strict-mon f = (i d : ℕ) → f i < f (suc d + i)

-- An SMZ is a function that is strictly monotonic and starts at 0.
record SMZ : Set where
  field
    f : ℕ → ℕ
    strict : Strict-mon f
    f0≡0 : f 0 ≡ 0

strict-mon-from-suc : (f : ℕ → ℕ) → ((i : ℕ) → f i < f (suc i)) → Strict-mon f
strict-mon-from-suc f pre i zero = pre i
strict-mon-from-suc f pre i (suc d) rewrite sym (+-suc d i) =
  <-trans (pre i) (strict-mon-from-suc f pre (suc i) d)

strict-mon-suc : (f : ℕ → ℕ) → Strict-mon f → (i : ℕ) → f i < f (suc i)
strict-mon-suc f strict i = strict i zero

strict-mon-≤ : (f : ℕ → ℕ) → Strict-mon f → (i j : ℕ) → i ≤ j → f i ≤ f j
strict-mon-≤ f strict i j i≤j with (get-≤ i j i≤j)
... | zero , refl = ≤-refl
... | suc d , refl =
  ≤-Reasoning.begin
    f i
  ≤-Reasoning.<⟨ strict i d ⟩
    f (suc d + i)
  ≤-Reasoning.∎

strict-mon-<-m : (f : ℕ → ℕ) → Strict-mon f → (i j m : ℕ) → i < j → m < f (suc i) → m < f j
strict-mon-<-m f strict i j m i<j m<fsi =
  ≤-Reasoning.begin
    suc m
  ≤-Reasoning.≤⟨ m<fsi ⟩
    f (suc i)
  ≤-Reasoning.≤⟨ strict-mon-≤ f strict (suc i) j i<j ⟩
    f j
  ≤-Reasoning.∎

strict-mon-< : (f : ℕ → ℕ) → Strict-mon f → (i j : ℕ) → i < j → f i < f j
strict-mon-< f strict i j i<j = strict-mon-<-m f strict i j (f i) i<j (strict-mon-suc f strict i)

id-≤-sm : (f : ℕ → ℕ) → Strict-mon f → (i : ℕ) → i ≤ f i
id-≤-sm _ _ zero = z≤n
id-≤-sm f strict (suc i) = ≤-trans (s≤s (id-≤-sm f strict i)) (strict i 0)

sm<fsi : (f : ℕ → ℕ) → Strict-mon f → (m i : ℕ) → m < f i → suc m < f (suc i)
sm<fsi f strict m i m<fi = <-trans-+1 m<fi (strict-mon-suc f strict i)

delta-≤-sm : (f : ℕ → ℕ) → Strict-mon f → (i d : ℕ) → d + f i ≤ f (d + i)
delta-≤-sm f strict i zero = ≤-refl
delta-≤-sm f strict i (suc d) =
  ≤-Reasoning.begin
    suc (d + f i)
  ≤-Reasoning.≤⟨ s≤s (delta-≤-sm f strict i d) ⟩
    suc (f (d + i))
  ≤-Reasoning.≤⟨ strict (d + i) zero ⟩
    f (suc (d + i))
  ≤-Reasoning.∎

find-idx-help : (f : SMZ) → (m i : ℕ) → Dec (suc m < SMZ.f f (suc i)) → ℕ
find-idx-help f m i (no _) = suc i
find-idx-help f m i (yes _) = i

-- find-idx-ind-m recurses on m, so it does not need gas. It's probably harder to prove properties about.
find-idx : SMZ → ℕ → ℕ
find-idx _ zero = 0
find-idx f (suc m) = find-idx-help f m i (suc m <? SMZ.f f (suc i))
  where
    i = find-idx f m

find-idx-≤ : (f : SMZ) → (m : ℕ) → SMZ.f f (find-idx f m) ≤ m
find-idx-≤ f zero rewrite SMZ.f0≡0 f = ≤-refl
find-idx-≤ f (suc m) with (suc m <? SMZ.f f (suc (find-idx f m)))
... | no ¬p = ≮→≤ ¬p
... | yes _ = ≤-trans (find-idx-≤ f m) (m≤n+m m 1)

find-idx-< : (f : SMZ) → (m : ℕ) → m < SMZ.f f (suc (find-idx f m))
find-idx-< f zero =
  ≤-Reasoning.begin
    suc zero
  ≤-Reasoning.≤⟨ id-≤-sm (SMZ.f f) (SMZ.strict f) (suc zero) ⟩
    SMZ.f f (suc zero)
  ≤-Reasoning.≤⟨ strict-mon-≤ (SMZ.f f) (SMZ.strict f)
                  (suc zero) (suc (find-idx f zero)) (s≤s z≤n) ⟩
    SMZ.f f (suc (find-idx f zero))
  ≤-Reasoning.∎
{-
m < f (suc i) -- induction
suc m < f (suc (suc i)) -- apply sm<fsi
suc m < f (suc (find-idx (suc m)))
  -- suc i ≡ find-idx (suc m) by normalization when ¬(suc m < f (suc i))
-}
find-idx-< f (suc m) with (suc m <? SMZ.f f (suc (find-idx f m)))
... | no _ = sm<fsi (SMZ.f f) (SMZ.strict f) m (suc i) ind
  where
    i = find-idx f m
    ind : m < SMZ.f f (suc i)
    ind = find-idx-< f m
... | yes p = p

-- This proof depends on find-idx-≤ and find-idx-<,
-- and does not directly depend on the implementation of find-idx.
find∘f-range : (f : SMZ) → (i m : ℕ) → SMZ.f f i ≤ m → m < SMZ.f f (suc i) → find-idx f m ≡ i
find∘f-range f i m fi≤m m<fsi with find-idx f m <? i
-- case: i' < i
...        | yes si'≤i = ⊥-elim ((≤→≮ m'≤m m<m'))
  where
    i' = find-idx f m
    m' = SMZ.f f (suc i')
    m<m' : m < m'
    m<m' = find-idx-< f m
    m'≤fi : m' ≤ SMZ.f f i
    m'≤fi = strict-mon-≤ (SMZ.f f) (SMZ.strict f) (suc i') i si'≤i
    m'≤m : m' ≤ m
    m'≤m = ≤-trans m'≤fi fi≤m
find∘f-range f i m fi≤m m<fsi | no i'<i with i <? find-idx f m
-- case: i < i'
... | yes i<i' = ⊥-elim (≤→≮ m'≤m m<m')
  where
    i' = find-idx f m
    m' = SMZ.f f i'
    m'≤m : m' ≤ m
    m'≤m = find-idx-≤ f m
    m<m' : m < m'
    m<m' = strict-mon-<-m (SMZ.f f) (SMZ.strict f) i i' m i<i' m<fsi
-- case: i ≡ i'
... | no i<i' = ≤-antisym (≮→≤ i<i') (≮→≤ i'<i)

find∘f : (f : SMZ) → (i : ℕ) → find-idx f (SMZ.f f i) ≡ i
find∘f f i = find∘f-range f i (SMZ.f f i) ≤-refl
                (strict-mon-< (SMZ.f f) (SMZ.strict f) i (suc i) ≤-refl)

find∘f+ : (f : SMZ) → (i rem : ℕ) → (rem < SMZ.f f (suc i) ∸ SMZ.f f i) → find-idx f (rem + SMZ.f f i) ≡ i
find∘f+ f i rem rem< = find∘f-range f i m fi≤m m<fsi
  where
    m = rem + SMZ.f f i
    fi≤m : SMZ.f f i ≤ rem + SMZ.f f i
    fi≤m = m≤n+m (SMZ.f f i) rem
    rem<+ : rem + SMZ.f f i < (SMZ.f f (suc i) ∸ SMZ.f f i) + SMZ.f f i
    rem<+ = ≤-+-balanced (SMZ.f f i) rem<
    fsi-cancel : (SMZ.f f (suc i) ∸ SMZ.f f i) + SMZ.f f i ≡ SMZ.f f (suc i)
    fsi-cancel = m∸n+n≡m (<→≤ (strict-mon-< (SMZ.f f) (SMZ.strict f) i (suc i) ≤-refl))
    m<fsi : rem + SMZ.f f i < SMZ.f f (suc i)
    m<fsi rewrite sym fsi-cancel = rem<+

{- Alternative definition.
   Since I can prove find-idx-< and find-idx-≤ with the above defintion, this is not necessary -}

find-idx-gassed-help : SMZ → ℕ → ℕ → ℕ → ℕ
find-idx-gassed-help _ m zero i = 0 -- do not care
find-idx-gassed-help f m (suc gas) i with m <? SMZ.f f (suc i)
... | no _ = find-idx-gassed-help f m gas (suc i)
... | yes _ = i

find-idx-gassed : SMZ → ℕ → ℕ
find-idx-gassed f m = find-idx-gassed-help f m (suc m) 0

---------------- Strictly Monotonic ≃ ----------------

-- The relation here is basically the identity: (m : ℕ) <-> (m : ℕ).
-- Except that the right side is partitioned into ranges,
-- so the right m carries info about which range it's in.
-- ∃[ m ](f (find m) ≤ m × (m < f (suc (find m))))

SMZ-Part : SMZ → Set
SMZ-Part f = ∃[ m ]((SMZ.f f (find-idx f m) ≤ m) × (m < SMZ.f f (suc (find-idx f m))))

ℕ≃SMZ : (f : SMZ) → ℕ ≃ SMZ-Part f
ℕ≃SMZ f = record { to = to ; from = from ; from∘to = from∘to ; to∘from = to∘from }
  where
    find = find-idx f
    to : ℕ → SMZ-Part f
    to m = m , find-idx-≤ f m , find-idx-< f m
    from : SMZ-Part f → ℕ
    from (m , _ , _) = m
    from∘to : (m : ℕ) → from (to m) ≡ m
    from∘to m = refl
    to∘from : (t : SMZ-Part f) → to (from t) ≡ t
    to∘from (m , fi≤m , m<fsi) =
      begin
        to (from (m , fi≤m , m<fsi))
      ≡⟨⟩
        (m , find-idx-≤ f m , find-idx-< f m)
      ≡⟨ cong (λ z → (m , z , find-idx-< f m)) (≤-uniq (find-idx-≤ f m) fi≤m) ⟩
        (m , fi≤m , find-idx-< f m)
      ≡⟨ cong (λ z → (m , fi≤m , z)) (≤-uniq (find-idx-< f m) m<fsi) ⟩
        (m , fi≤m , m<fsi)
      ∎

SMZ-Part-≡ : (f : SMZ) → (m m' : ℕ) → (m ≡ m')
           → (fi≤m : SMZ.f f (find-idx f m) ≤ m) → (fi≤m' : SMZ.f f (find-idx f m') ≤ m')
           → (m<fsi : m < SMZ.f f (suc (find-idx f m))) → (m<fsi' : m' < SMZ.f f (suc (find-idx f m')))
           → (m , fi≤m , m<fsi) ≡ (m' , fi≤m' , m<fsi')
SMZ-Part-≡ f m _ refl fi≤m fi≤m' m<fsi m<fsi'
  rewrite ≤-uniq fi≤m' fi≤m | ≤-uniq m<fsi' m<fsi
  = refl

---------------- ℕ ≃ ℕ × ℕ ----------------

{-
from (x , y) =
y
↑
|
|
6
37
148
0259---→ x
-}

sum-triangle : ℕ → ℕ
sum-triangle zero = zero
sum-triangle (suc i) = suc i + sum-triangle i

triangle-SMZ : SMZ
triangle-SMZ = record
  { f = sum-triangle
  ; strict = strict-mon-from-suc sum-triangle
                (λ i → (s≤s (m≤n+m (sum-triangle i) i)))
  ; f0≡0 = refl }

triangle≃ℕ×ℕ : SMZ-Part triangle-SMZ ≃ ℕ × ℕ
triangle≃ℕ×ℕ = record { to = to ; from = from ; from∘to = from∘to ; to∘from = to∘from }
  where
    f = SMZ.f triangle-SMZ
    strict = SMZ.strict triangle-SMZ
    f0≡0 = SMZ.f0≡0 triangle-SMZ
    find = find-idx triangle-SMZ
    to : SMZ-Part triangle-SMZ → ℕ × ℕ
    to (m , _ , _) = rem , i ∸ rem
      where
        i = find m
        rem = m ∸ f i
    from : ℕ × ℕ → SMZ-Part triangle-SMZ
    from (x , y) = m , fi≤m , m<fsi
      where
        i = y + x
        rem = x
        m = rem + f i
        fi≤m : f (find m) ≤ m
        fi≤m = find-idx-≤ triangle-SMZ m
        m<fsi : m < f (suc (find m))
        m<fsi = find-idx-< triangle-SMZ m
    from∘to : (t : SMZ-Part triangle-SMZ) → from (to t) ≡ t
    from∘to (m , fi≤m , m<fsi) =
      begin
        from (to (m , fi≤m , m<fsi))
      ≡⟨⟩
        from (rem , y)
      ≡⟨⟩
        (m' , fi≤m' , m<fsi')
      ≡⟨ SMZ-Part-≡ triangle-SMZ m' m m'≡m fi≤m' fi≤m m<fsi' m<fsi ⟩
        (m , fi≤m , m<fsi)
      ∎
      where
        i = find m
        rem = m ∸ f i
        y = i ∸ rem
        i' = y + rem
        m' = rem + f i'
        fi≤m' : f (find m') ≤ m'
        fi≤m' = find-idx-≤ triangle-SMZ m'
        m<fsi' : m' < f (suc (find m'))
        m<fsi' = find-idx-< triangle-SMZ m'
        rem≤i : m ∸ sum-triangle i ≤ i
        rem≤i = m∸o≤n (≤-pred m<fsi)
        i'≡i : (i ∸ rem) + rem ≡ i
        i'≡i = m∸n+n≡m {i} {rem} rem≤i
        m'≡m : m ∸ f i + f i' ≡ m
        m'≡m rewrite i'≡i = m∸n+n≡m {m} {f i} fi≤m
    to∘from : (xy : ℕ × ℕ) → to (from xy) ≡ xy
    to∘from (x , y) =
      begin
        to (from (x , y))
      ≡⟨⟩
        to (m , fi≤m , m<fsi)
      ≡⟨⟩
        (rem' , i' ∸ rem')
      ≡⟨ cong (_, i' ∸ rem') rem'≡rem ⟩
        (x , i' ∸ rem')
      ≡⟨ cong (x ,_) i'∸rem'≡y ⟩
        (x , y)
      ∎
      where
        i = y + x
        rem = x
        m = rem + f i
        fi≤m : f (find m) ≤ m
        fi≤m = find-idx-≤ triangle-SMZ m
        m<fsi : m < f (suc (find m))
        m<fsi = find-idx-< triangle-SMZ m
        i' = find m
        rem' = m ∸ f i'
        rem< : x < suc (y + x) + sum-triangle i ∸ sum-triangle i
        rem< rewrite m+n∸n≡m (suc (y + x)) (sum-triangle i) = s≤s (m≤n+m x y)
        i'≡i : i' ≡ i
        i'≡i =
          begin
            find (rem + f i)
          ≡⟨ find∘f+ triangle-SMZ i rem rem< ⟩
            i
          ∎
        rem'≡rem : rem' ≡ rem
        rem'≡rem =
          begin
            m ∸ f i'
          ≡⟨⟩
            (rem + f i) ∸ f (find (rem + f i))
          ≡⟨ cong (λ z → (rem + f i) ∸ f z) i'≡i ⟩
            (rem + f i) ∸ f i
          ≡⟨ m+n∸n≡m rem (f i) ⟩
            rem
          ∎
        i'∸rem'≡y : i' ∸ rem' ≡ y
        i'∸rem'≡y rewrite rem'≡rem | i'≡i = m+n∸n≡m y x

ℕ≃ℕ×ℕ : ℕ ≃ ℕ × ℕ
ℕ≃ℕ×ℕ = ≃-trans (ℕ≃SMZ triangle-SMZ) triangle≃ℕ×ℕ
