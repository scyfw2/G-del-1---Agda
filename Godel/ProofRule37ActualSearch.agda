{-# OPTIONS --safe #-}

module Godel.ProofRule37ActualSearch where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.PrimitiveRecursive using (evalPRF)
open import Godel.ProofCheckingPR using (proofCodeArgs)
open import Godel.ProofRule37ActualHit
  using
    ( Rule37ActualHitData
    ; rule37Search-complete-closedRule37-actual
    )
open import Godel.ProofRule37Search
  using
    ( rule37SearchF
    ; rule37SearchPR
    )
open import Godel.ProofRule37SearchHit
  using
    ( Rule37WitnessHitSoundBridge
    ; rule37Search-sound-from-hit-bridge
    ; rule37Search-nonzero-sound-from-hit-bridge
    )
open import Godel.ProofRuleFixedProofOr using (NonzeroNat)
open import Godel.ProofCheckingRule37Branch
  using (ProofRule37CheckingBranchData)
open import Godel.ProofRuleTargets
  using
    ( ClosedNumeralNeqRuleNat
    ; ProofRule37PR
    )

-- Once the actual witness hit predicate has both directions, the concrete
-- bounded search relation becomes a full rule-37 PR relation.

record Rule37ActualSearchData : Set₁ where
  field
    actual-hit-complete :
      Rule37ActualHitData

    actual-hit-sound :
      Rule37WitnessHitSoundBridge ClosedNumeralNeqRuleNat

rule37Search-complete-actual :
  Rule37ActualSearchData →
  {proof-code formula-code : ℕ} →
  ClosedNumeralNeqRuleNat proof-code formula-code →
  evalPRF rule37SearchF (proofCodeArgs proof-code formula-code) ≡
  suc zero
rule37Search-complete-actual D =
  rule37Search-complete-closedRule37-actual
    (Rule37ActualSearchData.actual-hit-complete D)

rule37Search-sound-actual :
  Rule37ActualSearchData →
  {proof-code formula-code : ℕ} →
  evalPRF rule37SearchF (proofCodeArgs proof-code formula-code) ≡
  suc zero →
  ClosedNumeralNeqRuleNat proof-code formula-code
rule37Search-sound-actual D =
  rule37Search-sound-from-hit-bridge
    (Rule37ActualSearchData.actual-hit-sound D)

rule37Search-nonzero-sound-actual :
  Rule37ActualSearchData →
  {proof-code formula-code : ℕ} →
  NonzeroNat (evalPRF rule37SearchF (proofCodeArgs proof-code formula-code)) →
  ClosedNumeralNeqRuleNat proof-code formula-code
rule37Search-nonzero-sound-actual D =
  rule37Search-nonzero-sound-from-hit-bridge
    (Rule37ActualSearchData.actual-hit-sound D)

proofRule37PR-from-actual-search :
  Rule37ActualSearchData →
  ProofRule37PR
proofRule37PR-from-actual-search D = record
  { rule37-pr =
      rule37SearchPR
  ; rule37-complete = λ {proof-code} {formula-code} rule37 →
      rule37Search-complete-actual
        D
        {proof-code}
        {formula-code}
        rule37
  ; rule37-sound = λ {proof-code} {formula-code} holds →
      rule37Search-sound-actual
        D
        {proof-code}
        {formula-code}
        holds
  }

proofRule37CheckingBranchData-from-actual-search :
  Rule37ActualSearchData →
  ProofRule37CheckingBranchData
proofRule37CheckingBranchData-from-actual-search D = record
  { rule37-pr-data =
      proofRule37PR-from-actual-search D
  ; rule37-nonzero-sound =
      rule37Search-nonzero-sound-actual D
  }
