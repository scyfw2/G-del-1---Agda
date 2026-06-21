{-# OPTIONS --safe #-}

module Godel.ProofRule37ArgsHit where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.PrimitiveRecursive using (evalPRF)
open import Godel.ProofCheckingPR using (proofCodeArgs)
open import Godel.ProofRule37Search
  using
    ( rule37SearchF
    ; rule37SearchMMeta
    ; rule37SearchPR
    )
open import Godel.ProofRule37SearchCorrectness
  using
    ( NonzeroNat
    ; search2UpTo
    )
open import Godel.ProofCheckingRule37Branch
  using (ProofRule37CheckingBranchData)
open import Godel.ProofRuleTargets
  using
    ( ClosedNumeralNeqRuleNat
    ; ProofRule37PR
    ; rule37WitnessArgs
    ; rule37WitnessF
    )

-- Boundary for an args-based rule-37 hit route.  This route uses
-- rule37WitnessArgs directly, so the existing branch theorems in
-- ProofRuleTargets are the right eventual tools.  We keep the remaining facts
-- as explicit fields because placing the proof terms here currently causes
-- Agda to normalize the large witness checker too aggressively.

rule37ArgsHitValue : ℕ → ℕ → ℕ → ℕ → ℕ
rule37ArgsHitValue m n proof-code formula-code =
  evalPRF
    rule37WitnessF
    (rule37WitnessArgs m n proof-code formula-code)

record Rule37ArgsSearchData : Set₁ where
  field
    search-meta-as-args-hit-search2 :
      (proof-code formula-code : ℕ) →
      rule37SearchMMeta proof-code proof-code formula-code ≡
      search2UpTo
        (λ m n → rule37ArgsHitValue m n proof-code formula-code)
        proof-code
        proof-code

    args-search-complete :
      {proof-code formula-code : ℕ} →
      ClosedNumeralNeqRuleNat proof-code formula-code →
      evalPRF rule37SearchF (proofCodeArgs proof-code formula-code) ≡
      suc zero

    args-search-sound :
      {proof-code formula-code : ℕ} →
      evalPRF rule37SearchF (proofCodeArgs proof-code formula-code) ≡
      suc zero →
      ClosedNumeralNeqRuleNat proof-code formula-code

proofRule37PR-from-args-search :
  Rule37ArgsSearchData →
  ProofRule37PR
proofRule37PR-from-args-search D = record
  { rule37-pr =
      rule37SearchPR
  ; rule37-complete = λ {proof-code} {formula-code} rule37 →
      Rule37ArgsSearchData.args-search-complete
        D
        {proof-code}
        {formula-code}
        rule37
  ; rule37-sound = λ {proof-code} {formula-code} holds →
      Rule37ArgsSearchData.args-search-sound
        D
        {proof-code}
        {formula-code}
        holds
  }

record Rule37ArgsCheckingBranchData : Set₁ where
  field
    args-search-data :
      Rule37ArgsSearchData

    args-search-nonzero-sound :
      {proof-code formula-code : ℕ} →
      NonzeroNat
        (evalPRF rule37SearchF (proofCodeArgs proof-code formula-code)) →
      ClosedNumeralNeqRuleNat proof-code formula-code

proofRule37CheckingBranchData-from-args-search :
  Rule37ArgsCheckingBranchData →
  ProofRule37CheckingBranchData
proofRule37CheckingBranchData-from-args-search D = record
  { rule37-pr-data =
      proofRule37PR-from-args-search
        (Rule37ArgsCheckingBranchData.args-search-data D)
  ; rule37-nonzero-sound =
      Rule37ArgsCheckingBranchData.args-search-nonzero-sound D
  }
