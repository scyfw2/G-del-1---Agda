{-# OPTIONS --safe #-}

module Godel.ProofRuleFixedPairTarget where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.PrimitiveRecursive
open import Godel.PRRepresentabilityFinal using (PARepresentsRelation)
open import Godel.ProofCheckingPR using (proofCodeArgs)
open import Godel.ProofRuleFixedPair

-- Rule-level adapter for branches whose checker is exactly a fixed pair of
-- proof-code and formula-code values.

record ProofRuleFixedPairPR
  (expected-proof-code expected-formula-code : ℕ) : Set₁ where
  field
    fixed-pair-pr :
      PRRel (suc (suc zero))

    fixed-pair-complete :
      {proof-code formula-code : ℕ} →
      FixedPairNat
        expected-proof-code
        expected-formula-code
        proof-code
        formula-code →
      PRRel-holds
        fixed-pair-pr
        (proofCodeArgs proof-code formula-code)

    fixed-pair-sound :
      {proof-code formula-code : ℕ} →
      PRRel-holds
        fixed-pair-pr
        (proofCodeArgs proof-code formula-code) →
      FixedPairNat
        expected-proof-code
        expected-formula-code
        proof-code
        formula-code

proofRuleFixedPairPR :
  (expected-proof-code expected-formula-code : ℕ) →
  ProofRuleFixedPairPR expected-proof-code expected-formula-code
proofRuleFixedPairPR expected-proof-code expected-formula-code = record
  { fixed-pair-pr =
      fixedPairPR expected-proof-code expected-formula-code
  ; fixed-pair-complete = λ {proof-code} {formula-code} fixed-pair →
      fixedPairF-complete
        {expected-proof-code}
        {expected-formula-code}
        {proof-code}
        {formula-code}
        fixed-pair
  ; fixed-pair-sound = λ {proof-code} {formula-code} holds →
      fixedPairF-sound
        {expected-proof-code}
        {expected-formula-code}
        {proof-code}
        {formula-code}
        holds
  }

record ProofRuleFixedPairPARepresentability
  (expected-proof-code expected-formula-code : ℕ) :
  Set₁ where
  field
    fixed-pair-represented :
      PARepresentsRelation
        (fixedPairPR expected-proof-code expected-formula-code)

proofRuleFixedPairPR-represented :
  (expected-proof-code expected-formula-code : ℕ) →
  ProofRuleFixedPairPARepresentability
    expected-proof-code
    expected-formula-code
proofRuleFixedPairPR-represented
  expected-proof-code
  expected-formula-code = record
  { fixed-pair-represented =
      fixedPairPR-represented
        expected-proof-code
        expected-formula-code
  }

proofRuleFixedPairPARepresentability :
  (expected-proof-code expected-formula-code : ℕ) →
  ProofRuleFixedPairPARepresentability
    expected-proof-code
    expected-formula-code
proofRuleFixedPairPARepresentability
  expected-proof-code
  expected-formula-code =
  proofRuleFixedPairPR-represented
    expected-proof-code
    expected-formula-code
