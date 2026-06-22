{-# OPTIONS --safe #-}

module Godel.CanonicalCodeListLengthStateFuelCode where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List renaming ([] to []ˡ; _∷_ to _∷ˡ_)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.CanonicalCoding using (Code; atom; Digit; d0; d1)
open import Godel.PRNatListDigitStream
  using (_++ᵈ_; appendDigitsWithRest; digitsLength; natDigits)
import Godel.CanonicalCodeListLengthStackMachine as SM
import Godel.CanonicalCodeListLengthNumericState as NS
import Godel.CanonicalCodeListLengthStatePR as StatePR
import Godel.CanonicalCodeListLengthStateStepBranches as Branches
open import Godel.CanonicalCodeListLengthStateFuel
open import Godel.CanonicalCodeListLengthStateFuelNat

-- Second small layer: code-frame one-step equations.
--
-- Full code prefixes are mutually recursive with code-list prefixes, so the
-- complete theorem lives in `CanonicalCodeListLengthStateFuelCodeList`.  This
-- module keeps the local code-frame facts isolated and also proves the atom
-- case, which only needs the nat-prefix theorem.

stateStep-code-d0-stateCodeTrue :
  (suffix : List Digit) → (stack-code len : ℕ) →
  evalPRF StatePR.stateStepF
    (stateCodeConsFrameEncTrue d0 suffix SM.codeFrame stack-code len ∷ []) ≡
  stateCodeFrameEncTrue suffix SM.natFrame stack-code len
stateStep-code-d0-stateCodeTrue suffix stack-code len =
  Branches.stateStepF-code-d0-opaque
    (appendDigitsWithRest suffix zero)
    stack-code
    len

stateStep-code-d1-stateCodeTrue :
  (suffix : List Digit) → (stack-code len : ℕ) →
  evalPRF StatePR.stateStepF
    (stateCodeConsFrameEncTrue d1 suffix SM.codeFrame stack-code len ∷ []) ≡
  stateCodeTwoFramesEncTrue suffix SM.natFrame SM.nestedList stack-code len
stateStep-code-d1-stateCodeTrue suffix stack-code len =
  Branches.stateStepF-code-d1-opaque
    (appendDigitsWithRest suffix zero)
    stack-code
    len

runStateStep-atom-prefix-complete-enc :
  (n : ℕ) → (suffix : List Digit) → (stack-code len : ℕ) →
  runStateStepFuel
    (digitsLength (SM.codeDigitsWithRest (atom n) []ˡ))
    (stateCodeFrameEncTrue
      (SM.codeDigitsWithRest (atom n) suffix)
      SM.codeFrame
      stack-code
      len)
  ≡
  stateCodeTrueEnc suffix stack-code len
runStateStep-atom-prefix-complete-enc n suffix stack-code len
  rewrite stateStep-code-d0-stateCodeTrue
            (natDigits n ++ᵈ suffix)
            stack-code
            len
        | NS.digitsLength-++-zeroʳ (natDigits n) =
  runStateStep-nat-prefix-complete-enc n suffix stack-code len

