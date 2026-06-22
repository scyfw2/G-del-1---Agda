{-# OPTIONS --safe #-}

module Godel.CanonicalCodeListLengthStateFuel where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List using (List)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.CanonicalCoding using (Digit; appendDigit)
open import Godel.PRNatListDigitStream
  using (appendDigitsWithRest)
import Godel.CanonicalCodeListLengthStackMachine as SM
import Godel.CanonicalCodeListLengthNumericState as NS
import Godel.CanonicalCodeListLengthStatePR as StatePR
import Godel.CanonicalCodeListLengthStateStepBranches as Branches

-- Lightweight landing point for the next fuel-induction stage.
--
-- `CanonicalCodeListLengthStateStepBranches` proves one-step equations for
-- `stateStepF`.  The next theorem will iterate those equations over canonical
-- nat/code/list prefixes.  This module fixes the runner and state-code shape
-- that the induction should use; the full prefix theorem is intentionally kept
-- out until it is split into smaller nat/code/list lemmas, mirroring the Lean
-- shadow proof.

runStateStepFuel : ℕ → ℕ → ℕ
runStateStepFuel zero state-code = state-code
runStateStepFuel (suc fuel) state-code =
  runStateStepFuel fuel (evalPRF StatePR.stateStepF (state-code ∷ []))

runStateStepFuel-add :
  (a b state-code : ℕ) →
  runStateStepFuel (a + b) state-code ≡
  runStateStepFuel b (runStateStepFuel a state-code)
runStateStepFuel-add zero b state-code = refl
runStateStepFuel-add (suc a) b state-code =
  runStateStepFuel-add
    a
    b
    (evalPRF StatePR.stateStepF (state-code ∷ []))

stateCodeTrueEnc : List Digit → ℕ → ℕ → ℕ
stateCodeTrueEnc digits stack-code len =
  Branches.stateInput
    (appendDigitsWithRest digits zero)
    stack-code
    len
    (suc zero)

stateCodeTrue : List Digit → List SM.Frame → ℕ → ℕ
stateCodeTrue digits stack len =
  stateCodeTrueEnc digits (NS.encodeStack stack) len

stateCodeFrameEncTrue : List Digit → SM.Frame → ℕ → ℕ → ℕ
stateCodeFrameEncTrue digits frame stack-code len =
  Branches.stateInput
    (appendDigitsWithRest digits zero)
    (NS.pushFrame frame stack-code)
    len
    (suc zero)

stateCodeFrameTrue : List Digit → SM.Frame → List SM.Frame → ℕ → ℕ
stateCodeFrameTrue digits frame stack len =
  stateCodeFrameEncTrue digits frame (NS.encodeStack stack) len

stateCodeConsFrameEncTrue :
  Digit → List Digit → SM.Frame → ℕ → ℕ → ℕ
stateCodeConsFrameEncTrue d suffix frame stack-code len =
  Branches.stateInput
    (appendDigit d (appendDigitsWithRest suffix zero))
    (NS.pushFrame frame stack-code)
    len
    (suc zero)

stateCodeConsFrameTrue :
  Digit → List Digit → SM.Frame → List SM.Frame → ℕ → ℕ
stateCodeConsFrameTrue d suffix frame stack len =
  stateCodeConsFrameEncTrue d suffix frame (NS.encodeStack stack) len

stateCodeTwoFramesEncTrue :
  List Digit → SM.Frame → SM.Frame → ℕ → ℕ → ℕ
stateCodeTwoFramesEncTrue digits top next stack-code len =
  Branches.stateInput
    (appendDigitsWithRest digits zero)
    (NS.pushFrame top (NS.pushFrame next stack-code))
    len
    (suc zero)
