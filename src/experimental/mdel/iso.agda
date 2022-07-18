import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app; sym; _≢_)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; s≤s; _<_; _∸_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; +-mono-≤; +-suc; ≤-trans; suc-injective; ≤-refl;
  ≤-pred; ≤-antisym; +-∸-comm; m+n∸n≡m; m∸n≤m; m≤n+m; ≤-stepsˡ; m+n≤o⇒n≤o; +-assoc; m∸n+n≡m)
open import Function using (_∘_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃; map₁; map₂) -- https://agda.github.io/agda-stdlib/Data.Product.html
open import Data.Bool using (Bool; false; true; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import plfa.part1.Isomorphism using (_≃_; ≃-refl; ≃-sym; ≃-trans;
                                          _≲_; ≲-refl; ≲-trans; ≲-antisym; ≃-implies-≲;
                                          extensionality; ∀-extensionality)
open _≃_
open plfa.part1.Isomorphism.≃-Reasoning
open _≲_
open plfa.part1.Isomorphism.≲-Reasoning

≢-sym : {A : Set} → {x y : A} → x ≢ y → y ≢ x
≢-sym xy yx = xy (sym yx)

---------------- ≃ connectives ----------------

≃-_→C : {A B C : Set} → A ≃ B → (A → C) ≃ (B → C)
≃-_→C {A} {B} {C} record { to = to ; from = from ; from∘to = from∘to ; to∘from = to∘from } =
  record
  { to = to'
  ; from = from'
  ; from∘to = from∘to'
  ; to∘from = to∘from' }
  where
    to' : (A → C) → (B → C)
    to' na b = na (from b)
    from' : (B → C) → (A → C)
    from' nb a = nb (to a)
    from∘to-help : (na : (A → C)) → (a : A) → na (from (to a)) ≡ na a
    from∘to-help na a rewrite from∘to a = refl
    from∘to' : (na : (A → C)) → from' (to' na) ≡ na
    from∘to' na =
      begin
        from' (to' na)
      ≡⟨⟩
        (λ a → na (from (to a)))
      ≡⟨ extensionality (from∘to-help na) ⟩
        na
      ∎
    to∘from-help : (nb : (B → C)) → (b : B) → nb (to (from b)) ≡ nb b
    to∘from-help nb b rewrite to∘from b = refl
    to∘from' : (nb : (B → C)) → to' (from' nb) ≡ nb
    to∘from' nb =
      begin
        to' (from' nb)
      ≡⟨⟩
        (λ b → nb (to (from b)))
      ≡⟨ extensionality (to∘from-help nb) ⟩
        nb
      ∎

≃-¬_ : {A B : Set} → A ≃ B → ¬ A ≃ ¬ B
≃-¬_ = ≃-_→C

≃-C→_ : {A B C : Set} → A ≃ B → (C → A) ≃ (C → B)
≃-C→_ {A} {B} {C} record { to = to ; from = from ; from∘to = from∘to ; to∘from = to∘from } =
  record
  { to = to'
  ; from = from'
  ; from∘to = from∘to'
  ; to∘from = to∘from' }
  where
    to' : (C → A) → (C → B)
    to' = to ∘_
    from' : (C → B) → (C → A)
    from' = from ∘_
    from∘to-help : (ca : (C → A)) → (c : C) → from (to (ca c)) ≡ ca c
    from∘to-help ca c rewrite from∘to (ca c) = refl
    from∘to' : (ca : C → A) → from' (to' ca) ≡ ca
    from∘to' ca =
      begin
        from' (to' ca)
      ≡⟨⟩
        (λ c → from (to (ca c)))
      ≡⟨ extensionality (from∘to-help ca) ⟩
        ca
      ∎
    to∘from-help : (cb : (C → B)) → (c : C) → to (from (cb c)) ≡ cb c
    to∘from-help cb c rewrite to∘from (cb c) = refl
    to∘from' : (cb : C → B) → to' (from' cb) ≡ cb
    to∘from' cb =
      begin
        to' (from' cb)
      ≡⟨⟩
        (λ c → to (from (cb c)))
      ≡⟨ extensionality (to∘from-help cb) ⟩
        cb
      ∎

≃-A×_ : {A B1 B2 : Set} → B1 ≃ B2 → A × B1 ≃ A × B2
≃-A×_ record { to = to ; from = from ; from∘to = from∘to ; to∘from = to∘from } = record
  { to = λ { (a , b) → (a , to b) }
  ; from = λ { (a , b) → (a , from b) }
  ; from∘to = λ { (a , b) → cong (λ b → (a , b)) (from∘to b) }
  ; to∘from = λ { (a , b) → cong (λ b → (a , b)) (to∘from b) } }

≃-_×A : {A B1 B2 : Set} → B1 ≃ B2 → B1 × A ≃ B2 × A
≃-_×A record { to = to ; from = from ; from∘to = from∘to ; to∘from = to∘from } = record
  { to = λ { (b , a) → (to b , a) }
  ; from = λ { (b , a) → (from b , a) }
  ; from∘to = λ { (b , a) → cong (λ b → (b , a)) (from∘to b) }
  ; to∘from = λ { (b , a) → cong (λ b → (b , a)) (to∘from b) } }

≃-A⊎_ : {A B1 B2 : Set} → B1 ≃ B2 → A ⊎ B1 ≃ A ⊎ B2
≃-A⊎_ record { to = to ; from = from ; from∘to = from∘to ; to∘from = to∘from } = record
  { to = λ { (inj₁ a) → inj₁ a ; (inj₂ b) → inj₂ (to b) }
  ; from = λ { (inj₁ a) → inj₁ a ; (inj₂ b) → inj₂ (from b) }
  ; from∘to = λ { (inj₁ a) → refl ; (inj₂ b) → cong inj₂ (from∘to b) }
  ; to∘from = λ { (inj₁ a) → refl ; (inj₂ b) → cong inj₂ (to∘from b) } }

≃-_⊎A : {A B1 B2 : Set} → B1 ≃ B2 → B1 ⊎ A ≃ B2 ⊎ A
≃-_⊎A record { to = to ; from = from ; from∘to = from∘to ; to∘from = to∘from } = record
  { to = λ { (inj₁ b) → inj₁ (to b) ; (inj₂ a) → inj₂ a }
  ; from = λ { (inj₁ b) → inj₁ (from b) ; (inj₂ a) → inj₂ a }
  ; from∘to = λ { (inj₁ b) → cong inj₁ (from∘to b) ; (inj₂ a) → refl }
  ; to∘from = λ { (inj₁ b) → cong inj₁ (to∘from b) ; (inj₂ a) → refl } }

×-comm : {A B : Set} → A × B ≃ B × A
×-comm = record
  { to = λ { (a , b) → b , a }
  ; from = λ { (b , a) → a , b }
  ; from∘to = λ { (a , b) → refl }
  ; to∘from = λ { (b , a) → refl } }

×-assoc : {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc = record
  { to = λ { ((a , b) , c) → a , (b , c) }
  ; from = λ { (a , (b , c)) → (a , b) , c }
  ; from∘to = λ { ((a , b) , c) → refl }
  ; to∘from = λ { (a , (b , c)) → refl } }

⊎-comm : {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm = record
  { to = λ { (inj₁ a) → inj₂ a ; (inj₂ b) → inj₁ b }
  ; from = λ { (inj₁ b) → inj₂ b ; (inj₂ a) → inj₁ a }
  ; from∘to = λ { (inj₁ a) → refl ; (inj₂ b) → refl }
  ; to∘from = λ { (inj₁ b) → refl ; (inj₂ a) → refl } }

⊎-assoc : {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc = record
  { to = λ { (inj₁ (inj₁ a)) → inj₁ a ; (inj₁ (inj₂ b)) → inj₂ (inj₁ b) ; (inj₂ c) → inj₂ (inj₂ c) }
  ; from = λ { (inj₁ a) → inj₁ (inj₁ a) ; (inj₂ (inj₁ b)) → inj₁ (inj₂ b) ; (inj₂ (inj₂ c)) → inj₂ c }
  ; from∘to = λ { (inj₁ (inj₁ a)) → refl ; (inj₁ (inj₂ b)) → refl ; (inj₂ c) → refl }
  ; to∘from = λ { (inj₁ a) → refl ; (inj₂ (inj₁ b)) → refl ; (inj₂ (inj₂ c)) → refl } }

Bool×A≃A⊎A : {A : Set} → Bool × A ≃ A ⊎ A
Bool×A≃A⊎A {A} = record { to = r-to ; from = r-from ; from∘to = r-from∘to ; to∘from = r-to∘from }
  where
    r-to : Bool × A → A ⊎ A
    r-to (false , a) = inj₁ a
    r-to (true , a) = inj₂ a
    r-from : A ⊎ A → Bool × A
    r-from (inj₁ a) = false , a
    r-from (inj₂ a) = true , a
    r-from∘to : (ba : Bool × A) → r-from (r-to ba) ≡ ba
    r-from∘to (false , a) = refl
    r-from∘to (true , a) = refl
    r-to∘from : (aa : A ⊎ A) → r-to (r-from aa) ≡ aa
    r-to∘from (inj₁ a) = refl
    r-to∘from (inj₂ a) = refl

---------------- ≃ ⊤ ⊥ ----------------

-- ¬ A → A has no elements, expressed as an isomorphism.
≃⊥ : {A : Set} → ¬ A → A ≃ ⊥
≃⊥ {A} ¬a = record
  { to = λ a → ¬a a
  ; from = λ ()
  ; from∘to = λ a → ⊥-elim (¬a a)
  ; to∘from = λ bot → ⊥-elim bot }

-- ¬ A → ¬ A has 1 element, expressed as an isomorphism.
¬≃⊤ : {A : Set} → ¬ A → (¬ A) ≃ ⊤
¬≃⊤ {A} ¬a = record
  { to = λ _ → tt
  ; from = λ _ → ¬a
  ; from∘to = λ f → extensionality (⊥-elim ∘ ¬a)
  ; to∘from = λ { tt → refl } }

uniq-¬ : {A : Set} → (¬a ¬b : ¬ A) → ¬a ≡ ¬b
uniq-¬ {A} ¬a ¬b =
  begin
    ¬a
  ≡⟨ from∘to iso ¬a ⟩
    from iso (to iso ¬a)
  ≡⟨⟩
    from iso tt
  ≡⟨⟩
    from iso (to iso ¬b)
  ≡⟨ from∘to iso ¬b ⟩
    ¬b
  ∎
  where
    open _≃_
    iso : ¬ A ≃ ⊤
    iso = ¬≃⊤ {A} ¬a



---------------- Fin-≲-card ----------------

-- HERE 1
data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin n
  suc : {n : ℕ} → Fin n → Fin (suc n)

_∉_ : {m : ℕ} → (x : Fin m) → (f : Fin m → Bool) → Set
x ∉ f = f x ≡ false
infix 1 _∉_

Bool→ℕ : Bool → ℕ
Bool→ℕ false = 0
Bool→ℕ true = 1

Bool→ℕ≤1 : (b : Bool) → Bool→ℕ b ≤ 1
Bool→ℕ≤1 false = _≤_.z≤n
Bool→ℕ≤1 true = _≤_.s≤s _≤_.z≤n

count : {m : ℕ} → (Fin m → Bool) → ℕ
count {zero} f = Bool→ℕ (f zero)
count {suc m} f = Bool→ℕ (f zero) + count (f ∘ suc)

subset-≤ : {n : ℕ} → (ys : Fin n → Bool) → count ys ≤ suc n
subset-≤ {zero} f = Bool→ℕ≤1 (f zero)
subset-≤ {suc n} f = +-mono-≤ z-≤ rec-≤
  where
    rec-≤ : count (λ z → f (suc z)) ≤ suc n
    rec-≤ = subset-≤ {n} (f ∘ suc)
    z-≤ : Bool→ℕ (f zero) ≤ 1
    z-≤ = Bool→ℕ≤1 (f zero)

inj : {A B : Set} → (A → B) → Set
inj {A} to = (x y : A) → to x ≡ to y → x ≡ y

Fin-suc-injective : {m : ℕ} → {x y : Fin m} → Fin.suc x ≡ Fin.suc y → x ≡ y
Fin-suc-injective refl = refl

Fin-suc-≢ : {m : ℕ} → {x y : Fin m} → Fin.suc x ≢ Fin.suc y → x ≢ y
Fin-suc-≢ {m} {x} {y} neq eq = neq (cong suc eq)

_∘suc-inj : {A : Set} → {m : ℕ} → (f : Fin (suc m) → A) → inj f → inj (f ∘ suc)
_∘suc-inj f inj-f x y eq = Fin-suc-injective (inj-f (suc x) (suc y) eq)

-- set-insert : {A : Set} → {Eq A} → A → (A → Bool) → (A → Bool)
-- set-insert x f y = x == y or f y
set-insert : {m : ℕ} → Fin m → (Fin m → Bool) → (Fin m → Bool)
set-insert zero f zero = true
set-insert zero f (suc y) = f (suc y)
set-insert (suc x) f zero = f zero
set-insert (suc x) f (suc y) = set-insert x (f ∘ suc) y

set-insert-count : {m : ℕ} → (x : Fin m) → (f : Fin m → Bool) → x ∉ f → count (set-insert x f) ≡ suc (count f)
set-insert-count {zero} zero f notin rewrite notin = refl
set-insert-count {suc m} zero f notin rewrite notin = refl
set-insert-count (suc x) f notin =
  begin
    Bool→ℕ (f zero) + count (set-insert x (f ∘ suc))
  ≡⟨ cong (Bool→ℕ (f zero) +_) (set-insert-count x (f ∘ suc) notin) ⟩
    Bool→ℕ (f zero) + suc (count (f ∘ suc))
  ≡⟨ +-suc (Bool→ℕ (f zero)) (count (f ∘ suc)) ⟩
    suc (Bool→ℕ (f zero) + count (f ∘ suc))
  ∎

set-insert-∉ : {m : ℕ} → (y : Fin m) → (f : Fin m → Bool) → (x : Fin m) → x ∉ f → x ≢ y → x ∉ (set-insert y f)
set-insert-∉ zero f zero xf neq = ⊥-elim (neq refl)
set-insert-∉ zero f (suc x) xf neq = xf
set-insert-∉ (suc y) f zero xf neq = xf
set-insert-∉ (suc y) f (suc x) xf neq = set-insert-∉ y (f ∘ suc) x xf (Fin-suc-≢ neq)

-- Unused (due to C-c C-a)
not-in-empty : {m : ℕ} → (x : Fin m) → x ∉ (λ _ → false)
not-in-empty x = refl

-- HERE 3
image : {m n : ℕ} → (to : Fin m → Fin n) → (Fin n → Bool)
image {zero} to = set-insert (to zero) (λ _ → false)
image {suc m} to = set-insert (to zero) (image {m} (to ∘ suc))

not-in-image : {m n : ℕ} → (f : Fin m → Fin n) → (x : Fin n) → ((y : Fin m) → f y ≢ x) → x ∉ image f
not-in-image {zero} {n} f x fy≢x = set-insert-∉ (f zero) (λ _ → false) x refl (≢-sym (fy≢x zero))
not-in-image {suc m} {n} f x fy≢x =
  set-insert-∉ (f zero)
               (image (f ∘ suc))
               x
               (not-in-image (f ∘ suc) x (fy≢x ∘ suc))
               (≢-sym (fy≢x zero))

-- (A ∋ x) is (x : A)
_∋_ : (A : Set) → A → A
_∋_ _ x = x
infix 0 _∋_

z-≢-s : {m : ℕ} → {x : Fin m} → suc x ≢ (Fin (suc m) ∋ zero)
z-≢-s ()

-- A ≢ B = A ≡ B → ⊥
tz-≢-ts : {m n : ℕ} → (to : Fin (suc m) → Fin n) → inj to → (x : Fin m) → to (suc x) ≢ to zero
tz-≢-ts {m} to inj-to x eq = z-≢-s (inj-to (suc x) zero eq)

-- HERE 5
image-suc-zero : {m n : ℕ} → (to : Fin (suc m) → Fin n) → inj to
               → image (to ∘ suc) (to zero) ≡ false
image-suc-zero {m} to inj-to = not-in-image (to ∘ suc) (to zero) (tz-≢-ts to inj-to)

count-empty : {m : ℕ} → count {m} (λ _ → false) ≡ zero
count-empty {zero} = refl
count-empty {suc m} = count-empty {m}

-- HERE 4
image-count : {m n : ℕ} → (to : Fin m → Fin n) → inj to → count (image to) ≡ suc m
image-count {zero} {n} to _ =
  begin
    count (set-insert (to zero) (λ _ → false))
  ≡⟨ set-insert-count (to zero) (λ _ → false) refl ⟩
    suc (count {n} (λ _ → false))
  ≡⟨ cong suc (count-empty {n}) ⟩
    1
  ∎
image-count {suc m} to inj-to =
  begin
    count (set-insert (to zero) (image (to ∘ suc)))
  ≡⟨ set-insert-count (to zero) (image (to ∘ suc)) (image-suc-zero to inj-to) ⟩
    suc (count (image (to ∘ suc)))
  ≡⟨ cong suc (image-count (to ∘ suc) (_∘suc-inj to inj-to)) ⟩
    suc (suc m)
  ∎

-- HERE 2
-- suc m ≡ |image to| ≤ suc n
inj→sm≤sn : {m n : ℕ} → (to : Fin m → Fin n) → inj to → suc m ≤ suc n
inj→sm≤sn {m} {n} to inj-to rewrite sym (image-count to inj-to) = subset-≤ (image to)

≲→inj : {A B : Set} → (A≲B : A ≲ B) → inj (to A≲B)
≲→inj {A} {B} A≲B x y tx≡ty =
  begin
    x
  ≡⟨ sym (from∘to A≲B x) ⟩
    from A≲B (to A≲B x)
  ≡⟨ cong (from A≲B) tx≡ty ⟩
    from A≲B (to A≲B y)
  ≡⟨ (from∘to A≲B y) ⟩
    y
  ∎

-- HERE 0
Fin-≲-card : {m n : ℕ} → Fin m ≲ Fin n → m ≤ n
Fin-≲-card {m} {n} fm≲fn = ≤-pred (inj→sm≤sn (to fm≲fn) (≲→inj fm≲fn))

---------------- Fin-≃-card ----------------

mn-to : {m n : ℕ} → m ≤ n → Fin m → Fin n
mn-to mn zero = zero
mn-to (_≤_.s≤s mn) (suc fm) = suc (mn-to mn fm)

mn-from : {m n : ℕ} → m ≤ n → Fin n → Fin m
mn-from _≤_.z≤n fn = zero
mn-from (_≤_.s≤s mn) zero = zero
mn-from (_≤_.s≤s mn) (suc fn) = suc (mn-from mn fn)

mn-from∘to : {m n : ℕ} → (mn : m ≤ n) → (fm : Fin m) → mn-from mn (mn-to mn fm) ≡ fm
mn-from∘to _≤_.z≤n zero = refl
mn-from∘to (_≤_.s≤s mn) zero = refl
mn-from∘to (_≤_.s≤s mn) (suc fm) = cong suc (mn-from∘to mn fm)

Fin-≲-card-inv : {m n : ℕ} → m ≤ n → Fin m ≲ Fin n
Fin-≲-card-inv {m} {n} mn = record { to = mn-to mn ; from = mn-from mn ; from∘to = mn-from∘to mn }

Fin-≃-card : {m n : ℕ} → Fin m ≃ Fin n → m ≡ n
Fin-≃-card {m} {n} record { to = to ; from = from ; from∘to = from∘to ; to∘from = to∘from } = ≤-antisym l g
  where
    l : m ≤ n
    l = Fin-≲-card (record { to = to ; from = from ; from∘to = from∘to })
    g : n ≤ m
    g = Fin-≲-card (record { to = from ; from = to ; from∘to = to∘from })

---------------- ℕ≄2^ℕ : ℕ ≄ (ℕ → Bool) ----------------

-- This uses Cantor's diagonalization argument.

_≄_ : (A B : Set) → Set
A ≄ B = ¬ (A ≃ B)
infix 0 _≄_

b≢nb : (b : Bool) → b ≢ not b
b≢nb false ()
b≢nb true ()

ℕ≄2^ℕ : ℕ ≄ (ℕ → Bool)
ℕ≄2^ℕ record { to = to ; from = from ; from∘to = from∘to ; to∘from = to∘from } =
  isnt-diag (from diag) is-diag
  where
    diag : ℕ → Bool
    diag m = not (to m m)
    isnt-diag : (m : ℕ) → to m ≢ diag
    isnt-diag m tm≡diag = b≢nb (to m m) (cong (λ f → f m) tm≡diag)
    is-diag : to (from diag) ≡ diag
    is-diag = to∘from diag

---------------- ℕ ≃ ℕ ⊎ ℕ ----------------

{-
First I tried to mirror to and from, where each induction step decrements (m : ℕ) by 1:
    to : ℕ → ℕ ⊎ ℕ
    to zero = inj₁ zero
    to (suc m) with to m
    ... | inj₁ n = inj₂ n
    ... | inj₂ n = inj₁ (suc n)
    from : ℕ ⊎ ℕ → ℕ
    from (inj₁ zero) = zero
    from (inj₁ (suc n)) = suc (from (inj₂ n))
    from (inj₂ n) = suc (from (inj₁ n))
This did not work due to `from` failing a termination check.
I also tried the same induction on (Bool × ℕ) instead of (ℕ ⊎ ℕ), but this failed the termination check too.

A solution that worked to decrement (n : ℕ) in (Bool × ℕ) by 1 each induction step,
which corresponds to decrementing (m : ℕ) by 2 each step.
This proof is about as straight-forward as possible.
-}

-- even <-> (false, _) ; odd <-> (true, _)
ℕ≃Bool×ℕ : ℕ ≃ Bool × ℕ
ℕ≃Bool×ℕ = record { to = r-to ; from = r-from ; from∘to = r-from∘to ; to∘from = r-to∘from }
  where
    r-to : ℕ → Bool × ℕ
    r-to zero = false , zero
    r-to (suc zero) = true , zero
    r-to (suc (suc m)) = map₂ suc (r-to m)
    r-from : Bool × ℕ → ℕ
    r-from (false , zero) = zero
    r-from (true , zero) = suc zero
    -- A single case with (o , suc n) causes a grey highlight. Is this a problem?
    r-from (false , suc n) = suc (suc (r-from (false , n)))
    r-from (true , suc n) = suc (suc (r-from (true , n)))
    r-from-suc : (on : Bool × ℕ) → r-from (map₂ suc on) ≡ suc (suc (r-from on))
    r-from-suc (false , zero) = refl
    r-from-suc (true , zero) = refl
    r-from-suc (false , suc n) = refl
    r-from-suc (true , suc n) = refl
    r-from∘to : (m : ℕ) → r-from (r-to m) ≡ m
    r-from∘to zero = refl
    r-from∘to (suc zero) = refl
    r-from∘to (suc (suc m)) =
      begin
        r-from (r-to (suc (suc m)))
      ≡⟨⟩
        r-from (map₂ suc (r-to m))
      ≡⟨ r-from-suc (r-to m) ⟩
        suc (suc (r-from (r-to m)))
      ≡⟨ cong suc (cong suc (r-from∘to m)) ⟩ -- Why does not this work: cong (suc ∘ suc) (r-from∘to m)
        suc (suc m)
      ∎
    r-to∘from : (on : Bool × ℕ) → r-to (r-from on) ≡ on
    r-to∘from (false , zero) = refl
    r-to∘from (true , zero) = refl
    r-to∘from (false , suc n) rewrite r-to∘from (false , n) = refl
    r-to∘from (true , suc n) rewrite r-to∘from (true , n) = refl

ℕ≃ℕ⊎ℕ : ℕ ≃ ℕ ⊎ ℕ
ℕ≃ℕ⊎ℕ = ≃-trans ℕ≃Bool×ℕ Bool×A≃A⊎A

---------------- ℕ ≃ ℕ × ℕ ----------------

-- See nxn.agda
