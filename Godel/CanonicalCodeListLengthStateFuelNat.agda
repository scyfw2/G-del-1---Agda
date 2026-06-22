{-# OPTIONS --safe #-}

module Godel.CanonicalCodeListLengthStateFuelNat where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List renaming (_∷_ to _∷ˡ_)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.CanonicalCoding using (Digit; d2; d3)
open import Godel.PRNatListDigitStream
  using (_++ᵈ_; appendDigitsWithRest; digitsLength; natDigits)
import Godel.CanonicalCodeListLengthStackMachine as SM
import Godel.CanonicalCodeListLengthNumericState as NS
import Godel.CanonicalCodeListLengthStatePR as StatePR
import Godel.CanonicalCodeListLengthStateStepBranches as Branches
open import Godel.CanonicalCodeListLengthStateFuel

-- First small fuel-induction layer: unary natural prefixes.
--
-- This module mirrors the Lean theorem `runStateStepEval_nat_prefix_complete`.
-- It only uses the nat-frame branch equations (`d2` keeps the nat frame,
-- `d3` pops it), so it stays independent from code/list recursion.

stateStep-nat-d2-stateCodeTrue :
  (suffix : List Digit) → (stack-code len : ℕ) →
  evalPRF StatePR.stateStepF
    (stateCodeConsFrameEncTrue d2 suffix SM.natFrame stack-code len ∷ []) ≡
  stateCodeFrameEncTrue suffix SM.natFrame stack-code len
stateStep-nat-d2-stateCodeTrue suffix stack-code len =
  Branches.stateStepF-nat-d2-opaque
    (appendDigitsWithRest suffix zero)
    stack-code
    len

stateStep-nat-d3-stateCodeTrue :
  (suffix : List Digit) → (stack-code len : ℕ) →
  evalPRF StatePR.stateStepF
    (stateCodeConsFrameEncTrue d3 suffix SM.natFrame stack-code len ∷ []) ≡
  stateCodeTrueEnc suffix stack-code len
stateStep-nat-d3-stateCodeTrue suffix stack-code len =
  Branches.stateStepF-nat-d3-opaque
    (appendDigitsWithRest suffix zero)
    stack-code
    len

runStateStep-nat-prefix-complete-enc :
  (n : ℕ) → (suffix : List Digit) → (stack-code len : ℕ) →
  runStateStepFuel
    (digitsLength (natDigits n))
    (stateCodeFrameEncTrue
      (natDigits n ++ᵈ suffix)
      SM.natFrame
      stack-code
      len)
  ≡
  stateCodeTrueEnc suffix stack-code len
runStateStep-nat-prefix-complete-enc zero suffix stack-code len
  rewrite stateStep-nat-d3-stateCodeTrue suffix stack-code len =
  refl
runStateStep-nat-prefix-complete-enc (suc n) suffix stack-code len
  rewrite stateStep-nat-d2-stateCodeTrue (natDigits n ++ᵈ suffix) stack-code len =
  runStateStep-nat-prefix-complete-enc n suffix stack-code len

runStateStep-nat-prefix-complete :
  (n : ℕ) → (suffix : List Digit) →
  (stack : List SM.Frame) → (len : ℕ) →
  runStateStepFuel
    (digitsLength (natDigits n))
    (stateCodeFrameTrue
      (natDigits n ++ᵈ suffix)
      SM.natFrame
      stack
      len)
  ≡
  stateCodeTrue suffix stack len
runStateStep-nat-prefix-complete n suffix stack len =
  runStateStep-nat-prefix-complete-enc n suffix (NS.encodeStack stack) len
