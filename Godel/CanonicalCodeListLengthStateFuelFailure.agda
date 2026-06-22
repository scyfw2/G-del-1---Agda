{-# OPTIONS --safe #-}

module Godel.CanonicalCodeListLengthStateFuelFailure where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
import Godel.CanonicalCodeListLengthStateStepBranches as Branches
open import Godel.CanonicalCodeListLengthStateFuel

-- Failure-side fuel induction for the PRF-level scanner state.
--
-- `CanonicalCodeListLengthStateFuelNat/Code/CodeList` cover canonical
-- prefixes.  These lemmas cover the other operational boundary: failed states
-- and completed states remain stable, and an empty stack with remaining input
-- steps into failure.

stateCodeEnc : ℕ → ℕ → ℕ → ℕ → ℕ
stateCodeEnc = Branches.stateInput

stateCodeFailedEnc : ℕ → ℕ → ℕ → ℕ
stateCodeFailedEnc rest stack len =
  stateCodeEnc rest stack len zero

stateCodeDoneEnc : ℕ → ℕ
stateCodeDoneEnc len =
  stateCodeEnc zero zero len (suc zero)

runStateStepFuel-failed :
  (fuel rest stack len : ℕ) →
  runStateStepFuel fuel (stateCodeFailedEnc rest stack len) ≡
  stateCodeFailedEnc rest stack len
runStateStepFuel-failed zero rest stack len = refl
runStateStepFuel-failed (suc fuel) rest stack len
  rewrite Branches.stateStepF-failed-opaque rest stack len =
  runStateStepFuel-failed fuel rest stack len

runStateStepFuel-done :
  (fuel len : ℕ) →
  runStateStepFuel fuel (stateCodeDoneEnc len) ≡
  stateCodeDoneEnc len
runStateStepFuel-done zero len = refl
runStateStepFuel-done (suc fuel) len
  rewrite Branches.stateStepF-done-opaque len =
  runStateStepFuel-done fuel len

runStateStepFuel-empty-nonzero :
  (fuel rest len : ℕ) →
  runStateStepFuel
    (suc fuel)
    (stateCodeEnc (suc rest) zero len (suc zero))
  ≡
  stateCodeFailedEnc (suc rest) zero len
runStateStepFuel-empty-nonzero fuel rest len
  rewrite Branches.stateStepF-empty-nonzero-opaque rest len =
  runStateStepFuel-failed fuel (suc rest) zero len

