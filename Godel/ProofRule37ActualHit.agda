{-# OPTIONS --safe #-}

module Godel.ProofRule37ActualHit where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.PrimitiveRecursive using (evalPRF)
open import Godel.ProofCheckingPR using (proofCodeArgs)
open import Godel.ProofRule37Search
  using
    ( rule37SearchF
    ; rule37SearchMMeta
    ; rule37WitnessValue
    )
open import Godel.ProofRule37SearchHit
  using (Rule37SearchHitInterface)
open import Godel.ProofRule37SemanticHit
  using
    ( Rule37SemanticHitComplete
    ; rule37Search-complete-closedRule37
    )
open import Godel.ProofRuleTargets
  using (ClosedNumeralNeqRuleNat)

-- The concrete hit predicate is exactly the witness checker value already used
-- by rule37SearchMMeta.  Keeping this in a small module localizes any heavy
-- witness-checker reasoning away from the generic bounded-search modules.

rule37ActualHitInterface : Rule37SearchHitInterface
rule37ActualHitInterface = record
  { witness-hit-value =
      rule37WitnessValue
  ; search-meta-as-hit-search2 = λ proof-code formula-code →
      refl
  }

record Rule37ActualHitData : Set₁ where
  field
    actual-semantic-hit-complete :
      Rule37SemanticHitComplete rule37ActualHitInterface

rule37Search-complete-closedRule37-actual :
  Rule37ActualHitData →
  {proof-code formula-code : ℕ} →
  ClosedNumeralNeqRuleNat proof-code formula-code →
  evalPRF rule37SearchF (proofCodeArgs proof-code formula-code)
  ≡ suc zero
rule37Search-complete-closedRule37-actual D =
  rule37Search-complete-closedRule37
    rule37ActualHitInterface
    (Rule37ActualHitData.actual-semantic-hit-complete D)
