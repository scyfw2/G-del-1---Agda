{-# OPTIONS --safe #-}

module Godel.PRArithmeticSemantics where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.PRBooleanHelpers
open import Godel.PRBoundedSearch

isZeroNat : ℕ → ℕ
isZeroNat zero = suc zero
isZeroNat (suc n) = zero

predNat : ℕ → ℕ
predNat zero = zero
predNat (suc n) = n

mulNat : ℕ → ℕ → ℕ
mulNat zero n = zero
mulNat (suc m) n = mulNat m n + n

minusNat : ℕ → ℕ → ℕ
minusNat m zero = m
minusNat zero (suc n) = zero
minusNat (suc m) (suc n) = minusNat m n

minus-zeroˡ :
  (m : ℕ) → minusNat zero m ≡ zero
minus-zeroˡ zero = refl
minus-zeroˡ (suc m) = refl

pred-minus-suc :
  (n m : ℕ) → predNat (minusNat (suc n) m) ≡ minusNat n m
pred-minus-suc n zero = refl
pred-minus-suc zero (suc m) rewrite minus-zeroˡ m = refl
pred-minus-suc (suc n) (suc m) = pred-minus-suc n m

lessEqNat : ℕ → ℕ → ℕ
lessEqNat m n = isZeroNat (minusNat m n)

eqNatNat : ℕ → ℕ → ℕ
eqNatNat m n = mulNat (lessEqNat m n) (lessEqNat n m)

ifZeroNat : ℕ → ℕ → ℕ → ℕ
ifZeroNat zero t e = t
ifZeroNat (suc c) t e = e

+-zeroʳ : (n : ℕ) → n + zero ≡ n
+-zeroʳ zero = refl
+-zeroʳ (suc n) = cong suc (+-zeroʳ n)

constF-correct :
  {n : ℕ} → (c : ℕ) → (xs : Vec ℕ n) →
  evalPRF (constF c) xs ≡ c
constF-correct zero xs = refl
constF-correct (suc c) xs rewrite constF-correct c xs = refl

addF-correct :
  (m n : ℕ) → evalPRF addF (m ∷ n ∷ []) ≡ m + n
addF-correct zero n = refl
addF-correct (suc m) n rewrite addF-correct m n = refl

mulF-correct :
  (m n : ℕ) → evalPRF mulF (m ∷ n ∷ []) ≡ mulNat m n
mulF-correct zero n = refl
mulF-correct (suc m) n
  rewrite mulF-correct m n
        | addF-correct (mulNat m n) n = refl

predF-correct :
  (n : ℕ) → evalPRF predF (n ∷ []) ≡ predNat n
predF-correct zero = refl
predF-correct (suc n) = refl

subFromFirstF-correct :
  (m n : ℕ) → evalPRF subFromFirstF (m ∷ n ∷ []) ≡ minusNat n m
subFromFirstF-correct zero n = refl
subFromFirstF-correct (suc m) zero
  rewrite subFromFirstF-correct m zero
        | predF-correct (minusNat zero m)
        | minus-zeroˡ m = refl
subFromFirstF-correct (suc m) (suc n)
  rewrite subFromFirstF-correct m (suc n)
        | predF-correct (minusNat (suc n) m)
        | pred-minus-suc n m = refl

minusF-correct :
  (m n : ℕ) → evalPRF minusF (m ∷ n ∷ []) ≡ minusNat m n
minusF-correct m n = subFromFirstF-correct n m

isZeroF-correct :
  (n : ℕ) → evalPRF isZeroF (n ∷ []) ≡ isZeroNat n
isZeroF-correct zero = refl
isZeroF-correct (suc n) = refl

notF-correct :
  (n : ℕ) → evalPRF notF (n ∷ []) ≡ isZeroNat n
notF-correct = isZeroF-correct

andF-correct :
  (m n : ℕ) → evalPRF andF (m ∷ n ∷ []) ≡ mulNat m n
andF-correct = mulF-correct

lessEqF-correct :
  (m n : ℕ) → evalPRF lessEqF (m ∷ n ∷ []) ≡ lessEqNat m n
lessEqF-correct m n
  rewrite minusF-correct m n
        | isZeroF-correct (minusNat m n) = refl

lessEqNat-zeroʳ : (n : ℕ) → lessEqNat (suc n) zero ≡ zero
lessEqNat-zeroʳ n = refl

lessEqNat-refl : (n : ℕ) → lessEqNat n n ≡ suc zero
lessEqNat-refl zero = refl
lessEqNat-refl (suc n) = lessEqNat-refl n

eqNatF-correct :
  (m n : ℕ) → evalPRF eqNatF (m ∷ n ∷ []) ≡ eqNatNat m n
eqNatF-correct m n
  rewrite lessEqF-correct m n
        | lessEqF-correct n m
        | andF-correct (lessEqNat m n) (lessEqNat n m) = refl

ifZeroF-correct :
  (c t e : ℕ) → evalPRF ifZeroF (c ∷ t ∷ e ∷ []) ≡ ifZeroNat c t e
ifZeroF-correct zero t e
  rewrite addF-correct t zero
        | +-zeroʳ t = refl
ifZeroF-correct (suc c) t e
  rewrite addF-correct zero e = refl
