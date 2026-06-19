{-# OPTIONS --safe #-}

module Godel.PRDigitSemantics where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.PRBooleanHelpers
open import Godel.PRBoundedSearch
open import Godel.PRArithmeticSemantics
open import Godel.PRDigitCoding
open import Godel.CanonicalCoding
  using (Digit; d0; d1; d2; d3; appendDigit)

mod4Nat : ℕ → ℕ
mod4Nat zero = zero
mod4Nat (suc zero) = suc zero
mod4Nat (suc (suc zero)) = suc (suc zero)
mod4Nat (suc (suc (suc zero))) = suc (suc (suc zero))
mod4Nat (suc (suc (suc (suc n)))) = mod4Nat n

div4Nat : ℕ → ℕ
div4Nat zero = zero
div4Nat (suc zero) = zero
div4Nat (suc (suc zero)) = zero
div4Nat (suc (suc (suc zero))) = zero
div4Nat (suc (suc (suc (suc n)))) = suc (div4Nat n)

iterDiv4Nat : ℕ → ℕ → ℕ
iterDiv4Nat zero input = input
iterDiv4Nat (suc k) input = div4Nat (iterDiv4Nat k input)

digitAtNat : ℕ → ℕ → ℕ
digitAtNat position input = mod4Nat (iterDiv4Nat position input)

digitEqualsAtNat : ℕ → ℕ → ℕ → ℕ
digitEqualsAtNat position input digit =
  eqNatNat (digitAtNat position input) digit

mod4StepNat : ℕ → ℕ
mod4StepNat r =
  ifZeroNat
    (eqNatNat r (suc (suc (suc zero))))
    (suc r)
    zero

div4StepNat : ℕ → ℕ → ℕ
div4StepNat n q =
  ifZeroNat (mod4Nat (suc n)) (suc q) q

suc-ifZeroNat :
  (c t e : ℕ) →
  suc (ifZeroNat c t e) ≡ ifZeroNat c (suc t) (suc e)
suc-ifZeroNat zero t e = refl
suc-ifZeroNat (suc c) t e = refl

mod4StepF-correct :
  (n r : ℕ) →
  evalPRF mod4StepF (n ∷ r ∷ []) ≡ mod4StepNat r
mod4StepF-correct n r
  rewrite eqNatF-correct r (suc (suc (suc zero)))
        | constF-correct (suc (suc (suc zero))) (n ∷ r ∷ [])
        | ifZeroF-correct
            (eqNatNat r (suc (suc (suc zero))))
            (suc r)
            zero = refl

mod4Nat-suc :
  (n : ℕ) → mod4Nat (suc n) ≡ mod4StepNat (mod4Nat n)
mod4Nat-suc zero = refl
mod4Nat-suc (suc zero) = refl
mod4Nat-suc (suc (suc zero)) = refl
mod4Nat-suc (suc (suc (suc zero))) = refl
mod4Nat-suc (suc (suc (suc (suc n)))) = mod4Nat-suc n

mod4F-correct :
  (n : ℕ) → evalPRF mod4F (n ∷ []) ≡ mod4Nat n
mod4F-correct zero = refl
mod4F-correct (suc n)
  rewrite mod4F-correct n
        | mod4StepF-correct n (mod4Nat n)
        | mod4Nat-suc n = refl

div4StepF-correct :
  (n q : ℕ) →
  evalPRF div4StepF (n ∷ q ∷ []) ≡ div4StepNat n q
div4StepF-correct n q
  rewrite mod4F-correct (suc n)
        | ifZeroF-correct (mod4Nat (suc n)) (suc q) q = refl

div4Nat-suc :
  (n : ℕ) → div4Nat (suc n) ≡ div4StepNat n (div4Nat n)
div4Nat-suc zero = refl
div4Nat-suc (suc zero) = refl
div4Nat-suc (suc (suc zero)) = refl
div4Nat-suc (suc (suc (suc zero))) = refl
div4Nat-suc (suc (suc (suc (suc n))))
  rewrite div4Nat-suc n
        | suc-ifZeroNat (mod4Nat (suc n)) (suc (div4Nat n)) (div4Nat n) =
  refl

div4F-correct :
  (n : ℕ) → evalPRF div4F (n ∷ []) ≡ div4Nat n
div4F-correct zero = refl
div4F-correct (suc n)
  rewrite div4F-correct n
        | div4StepF-correct n (div4Nat n)
        | div4Nat-suc n = refl

iterDiv4F-correct :
  (position input : ℕ) →
  evalPRF iterDiv4F (position ∷ input ∷ []) ≡
  iterDiv4Nat position input
iterDiv4F-correct zero input = refl
iterDiv4F-correct (suc position) input
  rewrite iterDiv4F-correct position input
        | div4F-correct (iterDiv4Nat position input) = refl

digitAtF-correct :
  (position input : ℕ) →
  evalPRF digitAtF (position ∷ input ∷ []) ≡
  digitAtNat position input
digitAtF-correct position input
  rewrite iterDiv4F-correct position input
        | mod4F-correct (iterDiv4Nat position input) = refl

mod4Nat-appendDigit :
  (d : Digit) → (rest : ℕ) →
  mod4Nat (appendDigit d rest) ≡ digitToNat d
mod4Nat-appendDigit d0 zero = refl
mod4Nat-appendDigit d1 zero = refl
mod4Nat-appendDigit d2 zero = refl
mod4Nat-appendDigit d3 zero = refl
mod4Nat-appendDigit d0 (suc rest) = mod4Nat-appendDigit d0 rest
mod4Nat-appendDigit d1 (suc rest) = mod4Nat-appendDigit d1 rest
mod4Nat-appendDigit d2 (suc rest) = mod4Nat-appendDigit d2 rest
mod4Nat-appendDigit d3 (suc rest) = mod4Nat-appendDigit d3 rest

div4Nat-appendDigit :
  (d : Digit) → (rest : ℕ) →
  div4Nat (appendDigit d rest) ≡ rest
div4Nat-appendDigit d0 zero = refl
div4Nat-appendDigit d1 zero = refl
div4Nat-appendDigit d2 zero = refl
div4Nat-appendDigit d3 zero = refl
div4Nat-appendDigit d0 (suc rest)
  rewrite div4Nat-appendDigit d0 rest = refl
div4Nat-appendDigit d1 (suc rest)
  rewrite div4Nat-appendDigit d1 rest = refl
div4Nat-appendDigit d2 (suc rest)
  rewrite div4Nat-appendDigit d2 rest = refl
div4Nat-appendDigit d3 (suc rest)
  rewrite div4Nat-appendDigit d3 rest = refl

digitAt-appendDigit-head :
  (d : Digit) → (rest : ℕ) →
  digitAtNat zero (appendDigit d rest) ≡ digitToNat d
digitAt-appendDigit-head = mod4Nat-appendDigit

iterDiv4Nat-appendDigit-tail :
  (position : ℕ) → (d : Digit) → (rest : ℕ) →
  iterDiv4Nat (suc position) (appendDigit d rest) ≡
  iterDiv4Nat position rest
iterDiv4Nat-appendDigit-tail zero d rest =
  div4Nat-appendDigit d rest
iterDiv4Nat-appendDigit-tail (suc position) d rest
  rewrite iterDiv4Nat-appendDigit-tail position d rest = refl

digitAt-appendDigit-tail :
  (position : ℕ) → (d : Digit) → (rest : ℕ) →
  digitAtNat (suc position) (appendDigit d rest) ≡
  digitAtNat position rest
digitAt-appendDigit-tail position d rest
  rewrite iterDiv4Nat-appendDigit-tail position d rest = refl
