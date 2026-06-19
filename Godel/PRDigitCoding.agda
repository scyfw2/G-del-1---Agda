{-# OPTIONS --safe #-}

module Godel.PRDigitCoding where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.PRBooleanHelpers
open import Godel.PRBoundedSearch
open import Godel.CanonicalCoding
  using (Digit; d0; d1; d2; d3)

mod4StepF : PRF (suc (suc zero))
mod4StepF =
  compF ifZeroF
    (compF eqNatF (projF fin1 ∷ threeF ∷ []) ∷
     compF sucF (projF fin1 ∷ []) ∷
     zeroF ∷ [])

mod4F : PRF (suc zero)
mod4F = precF zeroF mod4StepF

div4StepF : PRF (suc (suc zero))
div4StepF =
  compF ifZeroF
    (compF mod4F (compF sucF (projF fin0 ∷ []) ∷ []) ∷
     compF sucF (projF fin1 ∷ []) ∷
     projF fin1 ∷ [])

div4F : PRF (suc zero)
div4F = precF zeroF div4StepF

iterDiv4F : PRF (suc (suc zero))
iterDiv4F =
  precF
    (projF fin0)
    (compF div4F (projF fin1 ∷ []))

digitAtF : PRF (suc (suc zero))
digitAtF =
  compF mod4F (iterDiv4F ∷ [])

isDigitF : ℕ → PRF (suc zero)
isDigitF d =
  compF eqNatF (mod4F ∷ constF d ∷ [])

isDigit0F : PRF (suc zero)
isDigit0F = isDigitF zero

isDigit1F : PRF (suc zero)
isDigit1F = isDigitF (suc zero)

isDigit2F : PRF (suc zero)
isDigit2F = isDigitF (suc (suc zero))

isDigit3F : PRF (suc zero)
isDigit3F = isDigitF (suc (suc (suc zero)))

digitToNat : Digit → ℕ
digitToNat d0 = zero
digitToNat d1 = suc zero
digitToNat d2 = suc (suc zero)
digitToNat d3 = suc (suc (suc zero))
