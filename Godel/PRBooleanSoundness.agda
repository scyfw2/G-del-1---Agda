{-# OPTIONS --safe #-}

module Godel.PRBooleanSoundness where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.PRArithmeticSemantics using (mulNat)

absurd : {A : Set} → ⊥ → A
absurd ()

suc-injective :
  {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl

plus-suc-not-zero :
  (m n : ℕ) → m + suc n ≡ zero → ⊥
plus-suc-not-zero zero n ()
plus-suc-not-zero (suc m) n ()

zero≠suc : {n : ℕ} → zero ≡ suc n → ⊥
zero≠suc ()

suc-plus-suc-not-one :
  (m n : ℕ) → suc m + suc n ≡ suc zero → ⊥
suc-plus-suc-not-one m n eq =
  plus-suc-not-zero m n (suc-injective eq)

mulNat-zeroʳ :
  (m : ℕ) → mulNat m zero ≡ zero
mulNat-zeroʳ zero = refl
mulNat-zeroʳ (suc m)
  rewrite mulNat-zeroʳ m = refl

mulNat-suc-suc-positive :
  (m n : ℕ) →
  Σ ℕ (λ k → mulNat (suc m) (suc n) ≡ suc k)
mulNat-suc-suc-positive zero n =
  n ,Σ refl
mulNat-suc-suc-positive (suc m) n
  with mulNat-suc-suc-positive m n
... | k ,Σ eq
  rewrite eq =
  (k + suc n) ,Σ refl

abstract
  mulNat-one-sound :
    (left right : ℕ) →
    mulNat left right ≡ suc zero →
    (left ≡ suc zero) × (right ≡ suc zero)
  mulNat-one-sound zero right ()
  mulNat-one-sound (suc zero) right eq =
    refl ,× eq
  mulNat-one-sound (suc (suc left)) zero eq
    rewrite mulNat-zeroʳ (suc (suc left)) =
    absurd (zero≠suc eq)
  mulNat-one-sound (suc (suc left)) (suc right) eq
    with mulNat-suc-suc-positive left right
  ... | k ,Σ inner-eq
    rewrite inner-eq =
    absurd (suc-plus-suc-not-one k right eq)

  mulNat-nonzero-sound :
    (left right : ℕ) →
    Σ ℕ (λ k → mulNat left right ≡ suc k) →
    (Σ ℕ (λ k → left ≡ suc k)) ×
    (Σ ℕ (λ k → right ≡ suc k))
  mulNat-nonzero-sound zero right (k ,Σ ())
  mulNat-nonzero-sound (suc left) zero (k ,Σ eq)
    rewrite mulNat-zeroʳ left =
    absurd (zero≠suc eq)
  mulNat-nonzero-sound (suc left) (suc right) nonzero =
    (left ,Σ refl) ,× (right ,Σ refl)

  and-output-sound :
    (left right output : ℕ) →
    output ≡ mulNat left right →
    output ≡ suc zero →
    (left ≡ suc zero) × (right ≡ suc zero)
  and-output-sound left right output output-eq output-one =
    mulNat-one-sound
      left
      right
      (trans (sym output-eq) output-one)

  and-output-nonzero-sound :
    (left right output : ℕ) →
    output ≡ mulNat left right →
    Σ ℕ (λ k → output ≡ suc k) →
    (Σ ℕ (λ k → left ≡ suc k)) ×
    (Σ ℕ (λ k → right ≡ suc k))
  and-output-nonzero-sound left right output output-eq (k ,Σ output-nz) =
    mulNat-nonzero-sound
      left
      right
      (k ,Σ trans (sym output-eq) output-nz)

  and3-output-sound :
    (first second third output : ℕ) →
    output ≡ mulNat first (mulNat second third) →
    output ≡ suc zero →
    (first ≡ suc zero) ×
    ((second ≡ suc zero) × (third ≡ suc zero))
  and3-output-sound first second third output output-eq output-one
    with and-output-sound
          first
          (mulNat second third)
          output
          output-eq
          output-one
  ... | first-one ,× rest-one
    with mulNat-one-sound second third rest-one
  ... | second-one ,× third-one =
    first-one ,× (second-one ,× third-one)

  and4-output-sound :
    (first second third fourth output : ℕ) →
    output ≡ mulNat first (mulNat second (mulNat third fourth)) →
    output ≡ suc zero →
    (first ≡ suc zero) ×
    ((second ≡ suc zero) ×
     ((third ≡ suc zero) × (fourth ≡ suc zero)))
  and4-output-sound first second third fourth output output-eq output-one
    with and-output-sound
          first
          (mulNat second (mulNat third fourth))
          output
          output-eq
          output-one
  ... | first-one ,× rest-one
    with and3-output-sound
          second
          third
          fourth
          (mulNat second (mulNat third fourth))
          refl
          rest-one
  ... | second-one ,× (third-one ,× fourth-one) =
    first-one ,× (second-one ,× (third-one ,× fourth-one))
