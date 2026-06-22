{-# OPTIONS --safe #-}

module Godel.CanonicalCodeListLengthStatePRCompleteness where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List using (List) renaming ([] to []ˡ; _∷_ to _∷ˡ_)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.PRBooleanHelpers using (andF; eqNatF)
open import Godel.PRBoundedSearch using (constF)
import Godel.PRArithmeticSemantics as Arith
open import Godel.CanonicalCoding
  using
    ( Code
    ; atom
    ; node
    ; Digit
    ; d0
    ; d1
    ; d2
    ; d3
    ; _≤_
    ; ≤-refl
    ; ≤-zero
    ; ≤-step
    ; ≤-suc
    ; ≤-trans
    ; appendDigit
    ; n≤appendDigit
    ; suc≤appendDigit₁
    ; codeSize
    ; codeListSize
    ; codeSize+base≤encodeCodeWithRest
    ; codeListSize+base≤encodeCodeListWithRest
    ; encodeCodeWithRest
    ; encodeCodeListWithRest
    ; +-zeroʳ
    ; +-sucʳ
    ; +-assoc
    ; +-comm
    ; +-swap-mid
    )
open import Godel.CanonicalCodeParserTargets using (codeListLength)
open import Godel.PRNatListDigitStream
  using
    ( _++ᵈ_
    ; appendDigitsWithRest
    ; appendDigitsWithRest-++
    ; digitsLength
    ; digitsLength-++
    ; natDigits
    ; encodeNatWithRest-as-digits
    )
import Godel.CanonicalCodeListLengthStackMachine as SM
import Godel.CanonicalCodeListLengthNumericState as NS
import Godel.CanonicalCodeListLengthStateStepBranches as Branches
import Godel.CanonicalCodeListLengthStatePR as StatePR
import Godel.CanonicalCodeListLengthStateFuel as Fuel

-- PRF-level bridge for the canonical scanner.
--
-- Lean's numeric mini-prototype shows that the clean route is:
--
--   explicit fuel runner
--     → canonical prefix theorem
--     → completed-state stability
--     → final-state checker
--
-- This module ports that route to Agda.  It deliberately proves the
-- explicit-fuel canonical theorem first; the remaining all-input theorem for
-- `lengthScannerF` still needs an arbitrary-input parser/state correspondence.

scannerStartStateCode : ℕ → ℕ
scannerStartStateCode input =
  StatePR.stateInput input (suc zero) zero (suc zero)

scannerStartStateCode-branches :
  (input : ℕ) →
  scannerStartStateCode input ≡
  Branches.stateInput input (suc zero) zero (suc zero)
scannerStartStateCode-branches input =
  StatePR.stateCodeF-correct input (suc zero) zero (suc zero)

scannerStartStateCode-codeList :
  (codes : List Code) →
  scannerStartStateCode
    (appendDigitsWithRest (SM.codeListDigitsWithRest codes []ˡ) zero) ≡
  Fuel.stateCodeFrameEncTrue
    (SM.codeListDigitsWithRest codes []ˡ)
    SM.rootList
    zero
    zero
scannerStartStateCode-codeList codes
  rewrite scannerStartStateCode-branches
            (appendDigitsWithRest
              (SM.codeListDigitsWithRest codes []ˡ)
              zero) =
  refl

startStateF-correct :
  (input : ℕ) →
  evalPRF StatePR.startStateF (input ∷ []) ≡
  scannerStartStateCode input
startStateF-correct input
  rewrite StatePR.mkStateF-correct
            (projF fzero)
            (constF (suc zero))
            zeroF
            oneF
            (input ∷ [])
        | sym (StatePR.stateCodeF-correct
            input
            (suc zero)
            zero
            (suc zero)) =
  refl

-- The next lemma should relate `StatePR.runScannerStateFuelF` to
-- `Fuel.runStateStepFuel`.  The important engineering trick is to keep the
-- concrete state step opaque while proving iteration laws; otherwise Agda
-- repeatedly expands the full branch tree for `StatePR.stateStepF`.

abstract
  stateStepCode : ℕ → ℕ
  stateStepCode state-code =
    evalPRF StatePR.stateStepF (state-code ∷ [])

  stateStepCode-correct :
    (state-code : ℕ) →
    stateStepCode state-code ≡
    evalPRF StatePR.stateStepF (state-code ∷ [])
  stateStepCode-correct state-code = refl

runStateStepFuelOpaque : ℕ → ℕ → ℕ
runStateStepFuelOpaque zero state-code = state-code
runStateStepFuelOpaque (suc fuel) state-code =
  runStateStepFuelOpaque fuel (stateStepCode state-code)

runStateStepFuelOpaque-snoc :
  (fuel state-code : ℕ) →
  runStateStepFuelOpaque (suc fuel) state-code ≡
  stateStepCode (runStateStepFuelOpaque fuel state-code)
runStateStepFuelOpaque-snoc zero state-code = refl
runStateStepFuelOpaque-snoc (suc fuel) state-code
  rewrite runStateStepFuelOpaque-snoc
            fuel
            (stateStepCode state-code) =
  refl

runStateStepFuelOpaque-add :
  (a b state-code : ℕ) →
  runStateStepFuelOpaque (a + b) state-code ≡
  runStateStepFuelOpaque b (runStateStepFuelOpaque a state-code)
runStateStepFuelOpaque-add zero b state-code = refl
runStateStepFuelOpaque-add (suc a) b state-code =
  runStateStepFuelOpaque-add a b (stateStepCode state-code)

-- Avoid a generic theorem equating this opaque runner with
-- `Fuel.runStateStepFuel`: it forces the full `stateStepF` tree to unfold at
-- arbitrary states.  The canonical/failure paths should instead be reproved
-- directly for the opaque runner using branch-specific opaque lemmas.

abstract
  stateStepCode-root-d0 :
    (suffix : List Digit) → (stack-code len : ℕ) →
    stateStepCode
      (Fuel.stateCodeConsFrameEncTrue
        d0
        suffix
        SM.rootList
        stack-code
        len) ≡
    Fuel.stateCodeTrueEnc suffix stack-code len
  stateStepCode-root-d0 suffix stack-code len =
    Branches.stateStepF-root-d0-opaque
      (appendDigitsWithRest suffix zero)
      stack-code
      len

  stateStepCode-root-d1 :
    (suffix : List Digit) → (stack-code len : ℕ) →
    stateStepCode
      (Fuel.stateCodeConsFrameEncTrue
        d1
        suffix
        SM.rootList
        stack-code
        len) ≡
    Fuel.stateCodeTwoFramesEncTrue
      suffix
      SM.codeFrame
      SM.rootList
      stack-code
      (suc len)
  stateStepCode-root-d1 suffix stack-code len =
    Branches.stateStepF-root-d1-opaque
      (appendDigitsWithRest suffix zero)
      stack-code
      len

  stateStepCode-nested-d0 :
    (suffix : List Digit) → (stack-code len : ℕ) →
    stateStepCode
      (Fuel.stateCodeConsFrameEncTrue
        d0
        suffix
        SM.nestedList
        stack-code
        len) ≡
    Fuel.stateCodeTrueEnc suffix stack-code len
  stateStepCode-nested-d0 suffix stack-code len =
    Branches.stateStepF-nested-d0-opaque
      (appendDigitsWithRest suffix zero)
      stack-code
      len

  stateStepCode-nested-d1 :
    (suffix : List Digit) → (stack-code len : ℕ) →
    stateStepCode
      (Fuel.stateCodeConsFrameEncTrue
        d1
        suffix
        SM.nestedList
        stack-code
        len) ≡
    Fuel.stateCodeTwoFramesEncTrue
      suffix
      SM.codeFrame
      SM.nestedList
      stack-code
      len
  stateStepCode-nested-d1 suffix stack-code len =
    Branches.stateStepF-nested-d1-opaque
      (appendDigitsWithRest suffix zero)
      stack-code
      len

  stateStepCode-code-d0 :
    (suffix : List Digit) → (stack-code len : ℕ) →
    stateStepCode
      (Fuel.stateCodeConsFrameEncTrue
        d0
        suffix
        SM.codeFrame
        stack-code
        len) ≡
    Fuel.stateCodeFrameEncTrue suffix SM.natFrame stack-code len
  stateStepCode-code-d0 suffix stack-code len =
    Branches.stateStepF-code-d0-opaque
      (appendDigitsWithRest suffix zero)
      stack-code
      len

  stateStepCode-code-d1 :
    (suffix : List Digit) → (stack-code len : ℕ) →
    stateStepCode
      (Fuel.stateCodeConsFrameEncTrue
        d1
        suffix
        SM.codeFrame
        stack-code
        len) ≡
    Fuel.stateCodeTwoFramesEncTrue
      suffix
      SM.natFrame
      SM.nestedList
      stack-code
      len
  stateStepCode-code-d1 suffix stack-code len =
    Branches.stateStepF-code-d1-opaque
      (appendDigitsWithRest suffix zero)
      stack-code
      len

  stateStepCode-nat-d2 :
    (suffix : List Digit) → (stack-code len : ℕ) →
    stateStepCode
      (Fuel.stateCodeConsFrameEncTrue
        d2
        suffix
        SM.natFrame
        stack-code
        len) ≡
    Fuel.stateCodeFrameEncTrue suffix SM.natFrame stack-code len
  stateStepCode-nat-d2 suffix stack-code len =
    Branches.stateStepF-nat-d2-opaque
      (appendDigitsWithRest suffix zero)
      stack-code
      len

  stateStepCode-nat-d3 :
    (suffix : List Digit) → (stack-code len : ℕ) →
    stateStepCode
      (Fuel.stateCodeConsFrameEncTrue
        d3
        suffix
        SM.natFrame
        stack-code
        len) ≡
    Fuel.stateCodeTrueEnc suffix stack-code len
  stateStepCode-nat-d3 suffix stack-code len =
    Branches.stateStepF-nat-d3-opaque
      (appendDigitsWithRest suffix zero)
      stack-code
      len

  stateStepCode-failed :
    (rest stack len : ℕ) →
    stateStepCode (Branches.stateInput rest stack len zero) ≡
    Branches.stateInput rest stack len zero
  stateStepCode-failed rest stack len =
    Branches.stateStepF-failed-opaque rest stack len

  stateStepCode-done :
    (len : ℕ) →
    stateStepCode (Branches.stateInput zero zero len (suc zero)) ≡
    Branches.stateInput zero zero len (suc zero)
  stateStepCode-done len =
    Branches.stateStepF-done-opaque len

  stateStepCode-empty-nonzero :
    (rest len : ℕ) →
    stateStepCode
      (Branches.stateInput (suc rest) zero len (suc zero)) ≡
    Branches.stateInput (suc rest) zero len zero
  stateStepCode-empty-nonzero rest len =
    Branches.stateStepF-empty-nonzero-opaque rest len

runOpaque-nat-prefix-complete-enc :
  (n : ℕ) → (suffix : List Digit) → (stack-code len : ℕ) →
  runStateStepFuelOpaque
    (digitsLength (natDigits n))
    (Fuel.stateCodeFrameEncTrue
      (natDigits n ++ᵈ suffix)
      SM.natFrame
      stack-code
      len)
  ≡
  Fuel.stateCodeTrueEnc suffix stack-code len
runOpaque-nat-prefix-complete-enc zero suffix stack-code len
  rewrite stateStepCode-nat-d3 suffix stack-code len =
  refl
runOpaque-nat-prefix-complete-enc (suc n) suffix stack-code len
  rewrite stateStepCode-nat-d2 (natDigits n ++ᵈ suffix) stack-code len =
  runOpaque-nat-prefix-complete-enc n suffix stack-code len

runOpaque-atom-prefix-complete-enc :
  (n : ℕ) → (suffix : List Digit) → (stack-code len : ℕ) →
  runStateStepFuelOpaque
    (digitsLength (SM.codeDigitsWithRest (atom n) []ˡ))
    (Fuel.stateCodeFrameEncTrue
      (SM.codeDigitsWithRest (atom n) suffix)
      SM.codeFrame
      stack-code
      len)
  ≡
  Fuel.stateCodeTrueEnc suffix stack-code len
runOpaque-atom-prefix-complete-enc n suffix stack-code len
  rewrite stateStepCode-code-d0 (natDigits n ++ᵈ suffix) stack-code len
        | NS.digitsLength-++-zeroʳ (natDigits n) =
  runOpaque-nat-prefix-complete-enc n suffix stack-code len

mutual
  runOpaque-code-prefix-complete-enc :
    (c : Code) → (suffix : List Digit) → (stack-code len : ℕ) →
    runStateStepFuelOpaque
      (digitsLength (SM.codeDigitsWithRest c []ˡ))
      (Fuel.stateCodeFrameEncTrue
        (SM.codeDigitsWithRest c suffix)
        SM.codeFrame
        stack-code
        len)
    ≡
    Fuel.stateCodeTrueEnc suffix stack-code len
  runOpaque-code-prefix-complete-enc (atom n) suffix stack-code len =
    runOpaque-atom-prefix-complete-enc n suffix stack-code len
  runOpaque-code-prefix-complete-enc (node tag children) suffix stack-code len
    rewrite stateStepCode-code-d1
              (natDigits tag ++ᵈ
                SM.codeListDigitsWithRest children suffix)
              stack-code
              len
          | digitsLength-++
              (natDigits tag)
              (SM.codeListDigitsWithRest children []ˡ)
          | runStateStepFuelOpaque-add
              (digitsLength (natDigits tag))
              (digitsLength (SM.codeListDigitsWithRest children []ˡ))
              (Fuel.stateCodeTwoFramesEncTrue
                (natDigits tag ++ᵈ
                  SM.codeListDigitsWithRest children suffix)
                SM.natFrame
                SM.nestedList
                stack-code
                len)
          | runOpaque-nat-prefix-complete-enc
              tag
              (SM.codeListDigitsWithRest children suffix)
              (NS.pushFrame SM.nestedList stack-code)
              len =
    runOpaque-nestedList-prefix-complete-enc children suffix stack-code len

  runOpaque-rootList-prefix-complete-enc :
    (codes : List Code) → (suffix : List Digit) →
    (stack-code len : ℕ) →
    runStateStepFuelOpaque
      (digitsLength (SM.codeListDigitsWithRest codes []ˡ))
      (Fuel.stateCodeFrameEncTrue
        (SM.codeListDigitsWithRest codes suffix)
        SM.rootList
        stack-code
        len)
    ≡
    Fuel.stateCodeTrueEnc suffix stack-code (len + codeListLength codes)
  runOpaque-rootList-prefix-complete-enc []ˡ suffix stack-code len
    rewrite stateStepCode-root-d0 suffix stack-code len
          | +-zeroʳ len =
    refl
  runOpaque-rootList-prefix-complete-enc (head ∷ˡ tail) suffix stack-code len
    rewrite stateStepCode-root-d1
              (SM.codeDigitsWithRest
                head
                (SM.codeListDigitsWithRest tail suffix))
              stack-code
              len
          | NS.codeDigitsWithRest-length
              head
              (SM.codeListDigitsWithRest tail []ˡ)
          | runStateStepFuelOpaque-add
              (digitsLength (SM.codeDigitsWithRest head []ˡ))
              (digitsLength (SM.codeListDigitsWithRest tail []ˡ))
              (Fuel.stateCodeTwoFramesEncTrue
                (SM.codeDigitsWithRest
                  head
                  (SM.codeListDigitsWithRest tail suffix))
                SM.codeFrame
                SM.rootList
                stack-code
                (suc len))
          | runOpaque-code-prefix-complete-enc
              head
              (SM.codeListDigitsWithRest tail suffix)
              (NS.pushFrame SM.rootList stack-code)
              (suc len)
          | runOpaque-rootList-prefix-complete-enc
              tail
              suffix
              stack-code
              (suc len)
          | +-sucʳ len (codeListLength tail) =
    refl

  runOpaque-nestedList-prefix-complete-enc :
    (codes : List Code) → (suffix : List Digit) →
    (stack-code len : ℕ) →
    runStateStepFuelOpaque
      (digitsLength (SM.codeListDigitsWithRest codes []ˡ))
      (Fuel.stateCodeFrameEncTrue
        (SM.codeListDigitsWithRest codes suffix)
        SM.nestedList
        stack-code
        len)
    ≡
    Fuel.stateCodeTrueEnc suffix stack-code len
  runOpaque-nestedList-prefix-complete-enc []ˡ suffix stack-code len
    rewrite stateStepCode-nested-d0 suffix stack-code len =
    refl
  runOpaque-nestedList-prefix-complete-enc
    (head ∷ˡ tail)
    suffix
    stack-code
    len
    rewrite stateStepCode-nested-d1
              (SM.codeDigitsWithRest
                head
                (SM.codeListDigitsWithRest tail suffix))
              stack-code
              len
          | NS.codeDigitsWithRest-length
              head
              (SM.codeListDigitsWithRest tail []ˡ)
          | runStateStepFuelOpaque-add
              (digitsLength (SM.codeDigitsWithRest head []ˡ))
              (digitsLength (SM.codeListDigitsWithRest tail []ˡ))
              (Fuel.stateCodeTwoFramesEncTrue
                (SM.codeDigitsWithRest
                  head
                  (SM.codeListDigitsWithRest tail suffix))
                SM.codeFrame
                SM.nestedList
                stack-code
                len)
          | runOpaque-code-prefix-complete-enc
              head
              (SM.codeListDigitsWithRest tail suffix)
              (NS.pushFrame SM.nestedList stack-code)
              len =
    runOpaque-nestedList-prefix-complete-enc tail suffix stack-code len

runOpaque-codeList-closed-complete-enc :
  (codes : List Code) →
  runStateStepFuelOpaque
    (digitsLength (SM.codeListDigitsWithRest codes []ˡ))
    (Fuel.stateCodeFrameEncTrue
      (SM.codeListDigitsWithRest codes []ˡ)
      SM.rootList
      zero
      zero)
  ≡
  Fuel.stateCodeTrueEnc []ˡ zero (codeListLength codes)
runOpaque-codeList-closed-complete-enc codes =
  runOpaque-rootList-prefix-complete-enc codes []ˡ zero zero

stateCodeFailedEnc : ℕ → ℕ → ℕ → ℕ
stateCodeFailedEnc rest stack len =
  Branches.stateInput rest stack len zero

stateCodeDoneEnc : ℕ → ℕ
stateCodeDoneEnc len =
  Branches.stateInput zero zero len (suc zero)

runStateStepFuelOpaque-failed :
  (fuel rest stack len : ℕ) →
  runStateStepFuelOpaque fuel (stateCodeFailedEnc rest stack len) ≡
  stateCodeFailedEnc rest stack len
runStateStepFuelOpaque-failed zero rest stack len = refl
runStateStepFuelOpaque-failed (suc fuel) rest stack len
  rewrite stateStepCode-failed rest stack len =
  runStateStepFuelOpaque-failed fuel rest stack len

runStateStepFuelOpaque-done :
  (fuel len : ℕ) →
  runStateStepFuelOpaque fuel (stateCodeDoneEnc len) ≡
  stateCodeDoneEnc len
runStateStepFuelOpaque-done zero len = refl
runStateStepFuelOpaque-done (suc fuel) len
  rewrite stateStepCode-done len =
  runStateStepFuelOpaque-done fuel len

runStateStepFuelOpaque-empty-nonzero :
  (fuel rest len : ℕ) →
  runStateStepFuelOpaque
    (suc fuel)
    (Branches.stateInput (suc rest) zero len (suc zero))
  ≡
  stateCodeFailedEnc (suc rest) zero len
runStateStepFuelOpaque-empty-nonzero fuel rest len
  rewrite stateStepCode-empty-nonzero rest len =
  runStateStepFuelOpaque-failed fuel (suc rest) zero len

runOpaque-codeList-closed-complete-extra :
  (codes : List Code) → (extra : ℕ) →
  runStateStepFuelOpaque
    (digitsLength (SM.codeListDigitsWithRest codes []ˡ) + extra)
    (Fuel.stateCodeFrameEncTrue
      (SM.codeListDigitsWithRest codes []ˡ)
      SM.rootList
      zero
      zero)
  ≡
  stateCodeDoneEnc (codeListLength codes)
runOpaque-codeList-closed-complete-extra codes extra
  rewrite runStateStepFuelOpaque-add
            (digitsLength (SM.codeListDigitsWithRest codes []ˡ))
            extra
            (Fuel.stateCodeFrameEncTrue
              (SM.codeListDigitsWithRest codes []ˡ)
              SM.rootList
              zero
              zero)
        | runOpaque-codeList-closed-complete-enc codes
        | runStateStepFuelOpaque-done extra (codeListLength codes) =
  refl

abstract
  stateStepForPrecOpaqueF : PRF (suc (suc (suc zero)))
  stateStepForPrecOpaqueF =
    compF StatePR.stateStepF (projF (fsuc fzero) ∷ [])

  stateStepForPrecOpaqueF-correct :
    (fuel state-code input : ℕ) →
    evalPRF stateStepForPrecOpaqueF
      (fuel ∷ state-code ∷ input ∷ []) ≡
    stateStepCode state-code
  stateStepForPrecOpaqueF-correct fuel state-code input =
    sym (stateStepCode-correct state-code)

runScannerStateFuelOpaqueF : PRF (suc (suc zero))
runScannerStateFuelOpaqueF =
  precF StatePR.startStateF stateStepForPrecOpaqueF

runScannerStateFuelOpaqueF-correct :
  (fuel input : ℕ) →
  evalPRF runScannerStateFuelOpaqueF (fuel ∷ input ∷ []) ≡
  runStateStepFuelOpaque fuel (scannerStartStateCode input)
runScannerStateFuelOpaqueF-correct zero input =
  startStateF-correct input
runScannerStateFuelOpaqueF-correct (suc fuel) input
  rewrite runScannerStateFuelOpaqueF-correct fuel input
        | stateStepForPrecOpaqueF-correct
            fuel
            (runStateStepFuelOpaque
              fuel
              (scannerStartStateCode input))
            input
        | sym
            (runStateStepFuelOpaque-snoc
              fuel
              (scannerStartStateCode input)) =
  refl

runScannerStateFuelOpaqueF-codeList-complete-extra :
  (codes : List Code) → (extra : ℕ) →
  evalPRF runScannerStateFuelOpaqueF
    ( (digitsLength (SM.codeListDigitsWithRest codes []ˡ) + extra)
    ∷ appendDigitsWithRest (SM.codeListDigitsWithRest codes []ˡ) zero
    ∷ []) ≡
  stateCodeDoneEnc (codeListLength codes)
runScannerStateFuelOpaqueF-codeList-complete-extra codes extra =
  trans
    (runScannerStateFuelOpaqueF-correct
      (digitsLength (SM.codeListDigitsWithRest codes []ˡ) + extra)
      (appendDigitsWithRest (SM.codeListDigitsWithRest codes []ˡ) zero))
    (trans
      (cong
        (runStateStepFuelOpaque
          (digitsLength (SM.codeListDigitsWithRest codes []ˡ) + extra))
        (scannerStartStateCode-codeList codes))
      (runOpaque-codeList-closed-complete-extra codes extra))

runScannerStateWithFuelOpaqueF : PRF (suc (suc (suc zero)))
runScannerStateWithFuelOpaqueF =
  compF runScannerStateFuelOpaqueF
    (projF fzero ∷ projF (fsuc fzero) ∷ [])

finalRestWithFuelOpaqueF : PRF (suc (suc (suc zero)))
finalRestWithFuelOpaqueF =
  compF StatePR.stateRestF (runScannerStateWithFuelOpaqueF ∷ [])

finalStackWithFuelOpaqueF : PRF (suc (suc (suc zero)))
finalStackWithFuelOpaqueF =
  compF StatePR.stateStackF (runScannerStateWithFuelOpaqueF ∷ [])

finalLenWithFuelOpaqueF : PRF (suc (suc (suc zero)))
finalLenWithFuelOpaqueF =
  compF StatePR.stateLenF (runScannerStateWithFuelOpaqueF ∷ [])

finalOkWithFuelOpaqueF : PRF (suc (suc (suc zero)))
finalOkWithFuelOpaqueF =
  compF StatePR.stateOkF (runScannerStateWithFuelOpaqueF ∷ [])

lengthScannerWithFuelOpaqueF : PRF (suc (suc (suc zero)))
lengthScannerWithFuelOpaqueF =
  compF andF
    ( finalOkWithFuelOpaqueF ∷
      compF andF
        ( compF eqNatF (finalRestWithFuelOpaqueF ∷ zeroF ∷ []) ∷
          compF andF
            ( compF eqNatF (finalStackWithFuelOpaqueF ∷ zeroF ∷ []) ∷
              compF eqNatF
                (finalLenWithFuelOpaqueF ∷
                 projF (fsuc (fsuc fzero)) ∷ []) ∷ []) ∷ []) ∷ [])

eqNatNat-refl :
  (n : ℕ) → Arith.eqNatNat n n ≡ suc zero
eqNatNat-refl n
  rewrite Arith.lessEqNat-refl n =
  refl

x≤x+y : (x y : ℕ) → x ≤ x + y
x≤x+y x y = y ,Σ refl

y≤x+y : (x y : ℕ) → y ≤ x + y
y≤x+y x y = x ,Σ +-comm x y

+-interchange :
  (a b c d : ℕ) →
  (a + b) + (c + d) ≡ (a + c) + (b + d)
+-interchange a b c d
  rewrite +-assoc a b (c + d)
        | +-swap-mid b c d
        | sym (+-assoc a c (b + d)) =
  refl

≤-+-mono :
  {a b c d : ℕ} →
  a ≤ b → c ≤ d → a + c ≤ b + d
≤-+-mono {a} {c = c} (extra₁ ,Σ eq₁) (extra₂ ,Σ eq₂) =
  extra₁ + extra₂ ,Σ
  trans
    (cong (λ x → x + _) eq₁)
    (trans
      (cong (λ x → (a + extra₁) + x) eq₂)
      (+-interchange a extra₁ c extra₂))

≤-+-right :
  {a b : ℕ} → (c : ℕ) → a ≤ b → a + c ≤ b + c
≤-+-right c p = ≤-+-mono p (≤-refl c)

≤-double :
  {a b : ℕ} → a ≤ b → a + a ≤ b + b
≤-double p = ≤-+-mono p p

natDigits-length :
  (n : ℕ) → digitsLength (natDigits n) ≡ suc n
natDigits-length zero = refl
natDigits-length (suc n) =
  cong suc (natDigits-length n)

atom-length-bound-eq :
  (n suffix-len : ℕ) →
  ((suc n + suc n) + suffix-len) + suc zero ≡
  suc (suc n + suffix-len) + suc n
atom-length-bound-eq n suffix-len
  rewrite +-assoc (suc n + suc n) suffix-len (suc zero)
        | +-assoc (suc n) (suc n) (suffix-len + suc zero)
        | +-swap-mid (suc n) suffix-len (suc zero)
        | sym (+-assoc (suc n) suffix-len (suc (suc n)))
        | +-sucʳ (suc n + suffix-len) (suc n)
        | +-sucʳ n zero
        | +-zeroʳ n
        | +-sucʳ suffix-len (suc n)
        | +-sucʳ n (suffix-len + suc n)
        | sym (+-assoc n suffix-len (suc n)) =
  refl

atom-length≤size :
  (n suffix-len : ℕ) →
  suc (suc n + suffix-len) ≤
  ((suc n + suc n) + suffix-len) + suc zero
atom-length≤size n suffix-len =
  suc n ,Σ atom-length-bound-eq n suffix-len

node-size-step-eq :
  (tag child-size suffix-len : ℕ) →
  ((suc (tag + child-size) + suc (tag + child-size)) + suffix-len) + suc zero
  ≡
  suc (suc tag + (((child-size + child-size) + suffix-len) + suc zero))
    + tag
node-size-step-eq zero child-size suffix-len
  rewrite +-sucʳ child-size child-size
        | +-sucʳ ((child-size + child-size) + suffix-len) zero
        | +-zeroʳ ((child-size + child-size) + suffix-len)
        | +-zeroʳ (child-size + child-size + suffix-len) =
  refl
node-size-step-eq (suc tag) child-size suffix-len
  rewrite +-sucʳ (tag + child-size) (suc tag + child-size)
        | +-sucʳ
            (tag + (child-size + child-size + suffix-len + suc zero))
            tag =
  cong suc (cong suc (node-size-step-eq tag child-size suffix-len))

node-size-step≤ :
  (tag child-size suffix-len : ℕ) →
  suc (suc tag + (((child-size + child-size) + suffix-len) + suc zero))
  ≤
  ((suc (tag + child-size) + suc (tag + child-size)) + suffix-len) + suc zero
node-size-step≤ tag child-size suffix-len =
  tag ,Σ node-size-step-eq tag child-size suffix-len

double-sum-eq :
  (x y : ℕ) →
  (x + y) + (x + y) ≡ (x + x) + (y + y)
double-sum-eq zero y = refl
double-sum-eq (suc x) y
  rewrite +-sucʳ (x + y) (x + y)
        | +-sucʳ x x =
  cong suc (cong suc (double-sum-eq x y))

list-cons-size-step-eq :
  (head-size tail-size suffix-len : ℕ) →
  ((suc (head-size + tail-size) + suc (head-size + tail-size))
    + suffix-len) + suc zero
  ≡
  suc
    (((head-size + head-size) +
      (((tail-size + tail-size) + suffix-len) + suc zero))
     + suc zero)
list-cons-size-step-eq head-size tail-size suffix-len
  rewrite +-sucʳ (head-size + tail-size) (head-size + tail-size)
        | double-sum-eq head-size tail-size
        | +-assoc (head-size + head-size) (tail-size + tail-size) suffix-len
        | +-sucʳ ((tail-size + tail-size) + suffix-len) zero
        | +-zeroʳ ((tail-size + tail-size) + suffix-len)
        | +-sucʳ
            (head-size + head-size)
            ((tail-size + tail-size) + suffix-len)
        | +-sucʳ
            ((head-size + head-size) +
             ((tail-size + tail-size) + suffix-len))
            zero
        | +-zeroʳ
            ((head-size + head-size) +
             ((tail-size + tail-size) + suffix-len)) =
  refl

list-cons-size-step≤ :
  (head-size tail-size suffix-len : ℕ) →
  suc
    (((head-size + head-size) +
      (((tail-size + tail-size) + suffix-len) + suc zero))
     + suc zero)
  ≤
  ((suc (head-size + tail-size) + suc (head-size + tail-size))
    + suffix-len) + suc zero
list-cons-size-step≤ head-size tail-size suffix-len =
  zero ,Σ
  trans
    (list-cons-size-step-eq head-size tail-size suffix-len)
    (sym
      (+-zeroʳ
        (suc
          (((head-size + head-size) +
            (((tail-size + tail-size) + suffix-len) + suc zero))
           + suc zero))))

mutual
  codeDigitsWithRest-length≤size :
    (c : Code) → (suffix : List Digit) →
    digitsLength (SM.codeDigitsWithRest c suffix) ≤
    (codeSize c + codeSize c) + digitsLength suffix + suc zero
  codeDigitsWithRest-length≤size (atom n) suffix
    rewrite digitsLength-++ (natDigits n) suffix
          | natDigits-length n =
    atom-length≤size n (digitsLength suffix)
  codeDigitsWithRest-length≤size (node tag children) suffix
    rewrite digitsLength-++ (natDigits tag)
              (SM.codeListDigitsWithRest children suffix)
          | natDigits-length tag =
    ≤-trans
      (≤-suc
        (≤-+-mono
          (≤-refl (suc tag))
          (codeListDigitsWithRest-length≤size children suffix)))
      (node-size-step≤
        tag
        (codeListSize children)
        (digitsLength suffix))

  codeListDigitsWithRest-length≤size :
    (codes : List Code) → (suffix : List Digit) →
    digitsLength (SM.codeListDigitsWithRest codes suffix) ≤
    (codeListSize codes + codeListSize codes) + digitsLength suffix + suc zero
  codeListDigitsWithRest-length≤size []ˡ suffix
    rewrite +-sucʳ (digitsLength suffix) zero
          | +-zeroʳ (digitsLength suffix) =
    ≤-refl (suc (digitsLength suffix))
  codeListDigitsWithRest-length≤size (head ∷ˡ tail) suffix =
    ≤-trans
      (≤-suc
        (codeDigitsWithRest-length≤size
          head
          (SM.codeListDigitsWithRest tail suffix)))
      (≤-trans
        (≤-suc
          (≤-+-right
            (suc zero)
            (≤-+-mono
              (≤-refl (codeSize head + codeSize head))
              (codeListDigitsWithRest-length≤size tail suffix))))
        (list-cons-size-step≤
          (codeSize head)
          (codeListSize tail)
          (digitsLength suffix)))

mutual
  codeDigitsWithRest-append :
    (c : Code) → (suffix : List Digit) → (rest : ℕ) →
    appendDigitsWithRest (SM.codeDigitsWithRest c suffix) rest ≡
    encodeCodeWithRest c (appendDigitsWithRest suffix rest)
  codeDigitsWithRest-append (atom n) suffix rest
    rewrite appendDigitsWithRest-++ (natDigits n) suffix rest
          | sym
              (encodeNatWithRest-as-digits
                n
                (appendDigitsWithRest suffix rest)) =
    refl
  codeDigitsWithRest-append (node tag children) suffix rest
    rewrite appendDigitsWithRest-++ 
              (natDigits tag)
              (SM.codeListDigitsWithRest children suffix)
              rest
          | codeListDigitsWithRest-append children suffix rest
          | sym
              (encodeNatWithRest-as-digits
                tag
                (encodeCodeListWithRest
                  children
                  (appendDigitsWithRest suffix rest))) =
    refl

  codeListDigitsWithRest-append :
    (codes : List Code) → (suffix : List Digit) → (rest : ℕ) →
    appendDigitsWithRest (SM.codeListDigitsWithRest codes suffix) rest ≡
    encodeCodeListWithRest codes (appendDigitsWithRest suffix rest)
  codeListDigitsWithRest-append []ˡ suffix rest = refl
  codeListDigitsWithRest-append (head ∷ˡ tail) suffix rest
    rewrite codeDigitsWithRest-append
              head
              (SM.codeListDigitsWithRest tail suffix)
              rest
          | codeListDigitsWithRest-append tail suffix rest =
    refl

codeListClosed-append≡encode :
  (codes : List Code) →
  appendDigitsWithRest (SM.codeListDigitsWithRest codes []ˡ) zero ≡
  encodeCodeListWithRest codes zero
codeListClosed-append≡encode codes =
  codeListDigitsWithRest-append codes []ˡ zero

codeSize-positive :
  (c : Code) → suc zero ≤ codeSize c
codeSize-positive (atom n) =
  ≤-suc (≤-zero n)
codeSize-positive (node tag children) =
  ≤-suc (≤-zero (tag + codeListSize children))

sum-positive-left :
  (x y : ℕ) → suc zero ≤ x → suc zero ≤ x + y
sum-positive-left x y p =
  ≤-trans p (x≤x+y x y)

codeListSize≤encodeClosed :
  (codes : List Code) →
  codeListSize codes ≤ encodeCodeListWithRest codes zero
codeListSize≤encodeClosed codes =
  subst
    (λ size → size ≤ encodeCodeListWithRest codes zero)
    (+-zeroʳ (codeListSize codes))
    (codeListSize+base≤encodeCodeListWithRest
      codes
      zero
      zero
      (≤-refl zero))

double+2≤appendDigit₁-suc :
  (n : ℕ) →
  suc (suc (suc n + suc n)) ≤ appendDigit d1 (suc n)
double+2≤appendDigit₁-suc zero =
  ≤-step (≤-refl (suc (suc (suc (suc zero)))))
double+2≤appendDigit₁-suc (suc n)
  rewrite +-sucʳ n n
        | +-sucʳ n (suc n) =
  ≤-step
    (≤-step
      (≤-suc
        (≤-suc
          (double+2≤appendDigit₁-suc n))))

double+2≤appendDigit₁ :
  (n : ℕ) →
  suc zero ≤ n →
  suc (suc (n + n)) ≤ appendDigit d1 n
double+2≤appendDigit₁ zero (extra ,Σ ())
double+2≤appendDigit₁ (suc n) positive =
  double+2≤appendDigit₁-suc n

double-suc≤appendDigit₁ :
  {sum code : ℕ} →
  suc zero ≤ sum →
  sum ≤ code →
  suc sum + suc sum ≤ appendDigit d1 code
double-suc≤appendDigit₁ {sum} {code} sum-positive sum≤code
  rewrite +-sucʳ sum sum =
  ≤-trans
    (≤-suc (≤-suc (≤-double sum≤code)))
    (double+2≤appendDigit₁
      code
      (≤-trans sum-positive sum≤code))

codeListDouble≤encodeClosed :
  (codes : List Code) →
  codeListSize codes + codeListSize codes ≤
  encodeCodeListWithRest codes zero
codeListDouble≤encodeClosed []ˡ =
  ≤-zero (encodeCodeListWithRest []ˡ zero)
codeListDouble≤encodeClosed (head ∷ˡ tail) =
  double-suc≤appendDigit₁
    (sum-positive-left
      (codeSize head)
      (codeListSize tail)
      (codeSize-positive head))
    (codeSize+base≤encodeCodeWithRest
      head
      (codeListSize tail)
      (encodeCodeListWithRest tail zero)
      (codeListSize≤encodeClosed tail))

closed-list-size-bound-eq :
  (size : ℕ) →
  (size + size) + digitsLength []ˡ + suc zero ≡
  suc (size + size)
closed-list-size-bound-eq zero = refl
closed-list-size-bound-eq (suc size)
  rewrite +-sucʳ size size =
  cong suc (cong suc (closed-list-size-bound-eq size))

codeListClosed-length≤size :
  (codes : List Code) →
  digitsLength (SM.codeListDigitsWithRest codes []ˡ) ≤
  suc (codeListSize codes + codeListSize codes)
codeListClosed-length≤size codes =
  subst
    (λ bound → digitsLength (SM.codeListDigitsWithRest codes []ˡ) ≤ bound)
    (closed-list-size-bound-eq (codeListSize codes))
    (codeListDigitsWithRest-length≤size codes []ˡ)

codeListClosed-length≤fixedFuel :
  (codes : List Code) →
  digitsLength (SM.codeListDigitsWithRest codes []ˡ) ≤
    suc (appendDigitsWithRest (SM.codeListDigitsWithRest codes []ˡ) zero)
codeListClosed-length≤fixedFuel codes =
  ≤-trans
    (codeListClosed-length≤size codes)
    (subst
      (λ input →
        suc (codeListSize codes + codeListSize codes) ≤ suc input)
      (sym (codeListClosed-append≡encode codes))
      (≤-suc (codeListDouble≤encodeClosed codes)))

lengthScannerWithFuelOpaqueF-codeList-complete-extra :
  (codes : List Code) → (extra : ℕ) →
  evalPRF lengthScannerWithFuelOpaqueF
    ( (digitsLength (SM.codeListDigitsWithRest codes []ˡ) + extra)
    ∷ appendDigitsWithRest (SM.codeListDigitsWithRest codes []ˡ) zero
    ∷ codeListLength codes
    ∷ []) ≡
  suc zero
lengthScannerWithFuelOpaqueF-codeList-complete-extra codes extra
  rewrite runScannerStateFuelOpaqueF-codeList-complete-extra codes extra
        | StatePR.stateOkF-correct-code
            zero zero (codeListLength codes) (suc zero)
        | StatePR.stateRestF-correct-code
            zero zero (codeListLength codes) (suc zero)
        | StatePR.stateStackF-correct-code
            zero zero (codeListLength codes) (suc zero)
        | StatePR.stateLenF-correct-code
            zero zero (codeListLength codes) (suc zero)
        | Arith.eqNatF-correct zero zero
        | Arith.eqNatF-correct zero zero
        | Arith.eqNatF-correct
            (codeListLength codes)
            (codeListLength codes)
        | eqNatNat-refl zero
        | eqNatNat-refl (codeListLength codes)
        | Arith.andF-correct (suc zero) (suc zero)
        | Arith.andF-correct (suc zero) (suc zero)
        | Arith.andF-correct (suc zero) (suc zero) =
  refl

lengthScannerWithFuelOpaqueF-codeList-complete-fixed-from-bound :
  (codes : List Code) →
  digitsLength (SM.codeListDigitsWithRest codes []ˡ) ≤
    suc (appendDigitsWithRest (SM.codeListDigitsWithRest codes []ˡ) zero) →
  evalPRF lengthScannerWithFuelOpaqueF
    ( suc (appendDigitsWithRest (SM.codeListDigitsWithRest codes []ˡ) zero)
    ∷ appendDigitsWithRest (SM.codeListDigitsWithRest codes []ˡ) zero
    ∷ codeListLength codes
    ∷ []) ≡
  suc zero
lengthScannerWithFuelOpaqueF-codeList-complete-fixed-from-bound
  codes
  (extra ,Σ fuel-eq) =
  subst
    (λ fuel →
      evalPRF lengthScannerWithFuelOpaqueF
        ( fuel
        ∷ appendDigitsWithRest (SM.codeListDigitsWithRest codes []ˡ) zero
        ∷ codeListLength codes
        ∷ []) ≡
      suc zero)
    (sym fuel-eq)
    (lengthScannerWithFuelOpaqueF-codeList-complete-extra codes extra)

lengthScannerWithFuelOpaqueF-codeList-complete-fixed :
  (codes : List Code) →
  evalPRF lengthScannerWithFuelOpaqueF
    ( suc (appendDigitsWithRest (SM.codeListDigitsWithRest codes []ˡ) zero)
    ∷ appendDigitsWithRest (SM.codeListDigitsWithRest codes []ˡ) zero
    ∷ codeListLength codes
    ∷ []) ≡
  suc zero
lengthScannerWithFuelOpaqueF-codeList-complete-fixed codes =
  lengthScannerWithFuelOpaqueF-codeList-complete-fixed-from-bound
    codes
    (codeListClosed-length≤fixedFuel codes)

-- The canonical prefix theorem is intentionally kept for the next layer.  It
-- combines `runScannerStateFuelF-correct` with
-- `CanonicalCodeListLengthStateFuelCodeList.runStateStep-codeList-closed-complete-enc`
-- and completed-state stability.

-- The Lean module also packages this state theorem with a final-state
-- `rest = 0 ∧ stack = 0 ∧ len = expected` checker.  In Agda that final
-- checker should be added as a separate opaque layer; expanding the whole
-- `lengthScannerF`-shaped conjunction in one proof causes the same large
-- normalization pressure that this scanner route is meant to avoid.
