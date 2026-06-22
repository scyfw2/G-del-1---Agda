{-# OPTIONS --safe #-}

module Godel.CanonicalCodeListLengthStateFuelCodeList where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List renaming ([] to []ˡ; _∷_ to _∷ˡ_)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.CanonicalCoding
  using (Code; atom; node; Digit; d0; d1; +-zeroʳ; +-sucʳ; +-assoc)
open import Godel.CanonicalCodeParserTargets using (codeListLength)
open import Godel.PRNatListDigitStream
  using
    ( _++ᵈ_
    ; appendDigitsWithRest
    ; digitsLength
    ; digitsLength-++
    ; natDigits
    )
import Godel.CanonicalCodeListLengthStackMachine as SM
import Godel.CanonicalCodeListLengthNumericState as NS
import Godel.CanonicalCodeListLengthStatePR as StatePR
import Godel.CanonicalCodeListLengthStateStepBranches as Branches
open import Godel.CanonicalCodeListLengthStateFuel
open import Godel.CanonicalCodeListLengthStateFuelNat
open import Godel.CanonicalCodeListLengthStateFuelCode

-- Final prefix-induction layer for the PRF scanner state.
--
-- The code and code-list cases are mutually recursive, exactly as in the
-- explicit digit-stream and numeric-state mirrors.  All stack manipulation is
-- kept in encoded form (`stack-code`) so Agda does not normalize whole stack
-- encodings while rewriting a single branch equation.

stateStep-root-d0-stateCodeTrue :
  (suffix : List Digit) → (stack-code len : ℕ) →
  evalPRF StatePR.stateStepF
    (stateCodeConsFrameEncTrue d0 suffix SM.rootList stack-code len ∷ []) ≡
  stateCodeTrueEnc suffix stack-code len
stateStep-root-d0-stateCodeTrue suffix stack-code len =
  Branches.stateStepF-root-d0-opaque
    (appendDigitsWithRest suffix zero)
    stack-code
    len

stateStep-root-d1-stateCodeTrue :
  (suffix : List Digit) → (stack-code len : ℕ) →
  evalPRF StatePR.stateStepF
    (stateCodeConsFrameEncTrue d1 suffix SM.rootList stack-code len ∷ []) ≡
  stateCodeTwoFramesEncTrue
    suffix
    SM.codeFrame
    SM.rootList
    stack-code
    (suc len)
stateStep-root-d1-stateCodeTrue suffix stack-code len =
  Branches.stateStepF-root-d1-opaque
    (appendDigitsWithRest suffix zero)
    stack-code
    len

stateStep-nested-d0-stateCodeTrue :
  (suffix : List Digit) → (stack-code len : ℕ) →
  evalPRF StatePR.stateStepF
    (stateCodeConsFrameEncTrue d0 suffix SM.nestedList stack-code len ∷ []) ≡
  stateCodeTrueEnc suffix stack-code len
stateStep-nested-d0-stateCodeTrue suffix stack-code len =
  Branches.stateStepF-nested-d0-opaque
    (appendDigitsWithRest suffix zero)
    stack-code
    len

stateStep-nested-d1-stateCodeTrue :
  (suffix : List Digit) → (stack-code len : ℕ) →
  evalPRF StatePR.stateStepF
    (stateCodeConsFrameEncTrue d1 suffix SM.nestedList stack-code len ∷ []) ≡
  stateCodeTwoFramesEncTrue
    suffix
    SM.codeFrame
    SM.nestedList
    stack-code
    len
stateStep-nested-d1-stateCodeTrue suffix stack-code len =
  Branches.stateStepF-nested-d1-opaque
    (appendDigitsWithRest suffix zero)
    stack-code
    len

mutual
  runStateStep-code-prefix-complete-enc :
    (c : Code) → (suffix : List Digit) → (stack-code len : ℕ) →
    runStateStepFuel
      (digitsLength (SM.codeDigitsWithRest c []ˡ))
      (stateCodeFrameEncTrue
        (SM.codeDigitsWithRest c suffix)
        SM.codeFrame
        stack-code
        len)
    ≡
    stateCodeTrueEnc suffix stack-code len
  runStateStep-code-prefix-complete-enc (atom n) suffix stack-code len =
    runStateStep-atom-prefix-complete-enc n suffix stack-code len
  runStateStep-code-prefix-complete-enc (node tag children) suffix stack-code len
    rewrite stateStep-code-d1-stateCodeTrue
              (natDigits tag ++ᵈ
                SM.codeListDigitsWithRest children suffix)
              stack-code
              len
          | digitsLength-++
              (natDigits tag)
              (SM.codeListDigitsWithRest children []ˡ)
          | runStateStepFuel-add
              (digitsLength (natDigits tag))
              (digitsLength (SM.codeListDigitsWithRest children []ˡ))
              (stateCodeTwoFramesEncTrue
                (natDigits tag ++ᵈ
                  SM.codeListDigitsWithRest children suffix)
                SM.natFrame
                SM.nestedList
                stack-code
                len)
          | runStateStep-nat-prefix-complete-enc
              tag
              (SM.codeListDigitsWithRest children suffix)
              (NS.pushFrame SM.nestedList stack-code)
              len =
    runStateStep-nestedList-prefix-complete-enc children suffix stack-code len

  runStateStep-rootList-prefix-complete-enc :
    (codes : List Code) → (suffix : List Digit) →
    (stack-code len : ℕ) →
    runStateStepFuel
      (digitsLength (SM.codeListDigitsWithRest codes []ˡ))
      (stateCodeFrameEncTrue
        (SM.codeListDigitsWithRest codes suffix)
        SM.rootList
        stack-code
        len)
    ≡
    stateCodeTrueEnc suffix stack-code (len + codeListLength codes)
  runStateStep-rootList-prefix-complete-enc []ˡ suffix stack-code len
    rewrite stateStep-root-d0-stateCodeTrue suffix stack-code len
          | +-zeroʳ len =
    refl
  runStateStep-rootList-prefix-complete-enc (head ∷ˡ tail) suffix stack-code len
    rewrite stateStep-root-d1-stateCodeTrue
              (SM.codeDigitsWithRest
                head
                (SM.codeListDigitsWithRest tail suffix))
              stack-code
              len
          | NS.codeDigitsWithRest-length
              head
              (SM.codeListDigitsWithRest tail []ˡ)
          | runStateStepFuel-add
              (digitsLength (SM.codeDigitsWithRest head []ˡ))
              (digitsLength (SM.codeListDigitsWithRest tail []ˡ))
              (stateCodeTwoFramesEncTrue
                (SM.codeDigitsWithRest
                  head
                  (SM.codeListDigitsWithRest tail suffix))
                SM.codeFrame
                SM.rootList
                stack-code
                (suc len))
          | runStateStep-code-prefix-complete-enc
              head
              (SM.codeListDigitsWithRest tail suffix)
              (NS.pushFrame SM.rootList stack-code)
              (suc len)
          | runStateStep-rootList-prefix-complete-enc
              tail
              suffix
              stack-code
              (suc len)
          | +-sucʳ len (codeListLength tail) =
    refl

  runStateStep-nestedList-prefix-complete-enc :
    (codes : List Code) → (suffix : List Digit) →
    (stack-code len : ℕ) →
    runStateStepFuel
      (digitsLength (SM.codeListDigitsWithRest codes []ˡ))
      (stateCodeFrameEncTrue
        (SM.codeListDigitsWithRest codes suffix)
        SM.nestedList
        stack-code
        len)
    ≡
    stateCodeTrueEnc suffix stack-code len
  runStateStep-nestedList-prefix-complete-enc []ˡ suffix stack-code len
    rewrite stateStep-nested-d0-stateCodeTrue suffix stack-code len =
    refl
  runStateStep-nestedList-prefix-complete-enc
    (head ∷ˡ tail)
    suffix
    stack-code
    len
    rewrite stateStep-nested-d1-stateCodeTrue
              (SM.codeDigitsWithRest
                head
                (SM.codeListDigitsWithRest tail suffix))
              stack-code
              len
          | NS.codeDigitsWithRest-length
              head
              (SM.codeListDigitsWithRest tail []ˡ)
          | runStateStepFuel-add
              (digitsLength (SM.codeDigitsWithRest head []ˡ))
              (digitsLength (SM.codeListDigitsWithRest tail []ˡ))
              (stateCodeTwoFramesEncTrue
                (SM.codeDigitsWithRest
                  head
                  (SM.codeListDigitsWithRest tail suffix))
                SM.codeFrame
                SM.nestedList
                stack-code
                len)
          | runStateStep-code-prefix-complete-enc
              head
              (SM.codeListDigitsWithRest tail suffix)
              (NS.pushFrame SM.nestedList stack-code)
              len =
    runStateStep-nestedList-prefix-complete-enc tail suffix stack-code len

runStateStep-codeList-closed-complete-enc :
  (codes : List Code) →
  runStateStepFuel
    (digitsLength (SM.codeListDigitsWithRest codes []ˡ))
    (stateCodeFrameEncTrue
      (SM.codeListDigitsWithRest codes []ˡ)
      SM.rootList
      zero
      zero)
  ≡
  stateCodeTrueEnc []ˡ zero (codeListLength codes)
runStateStep-codeList-closed-complete-enc codes =
  runStateStep-rootList-prefix-complete-enc codes []ˡ zero zero

