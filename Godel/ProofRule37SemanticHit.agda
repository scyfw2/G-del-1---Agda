{-# OPTIONS --safe #-}

module Godel.ProofRule37SemanticHit where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.PrimitiveRecursive using (evalPRF)
open import Godel.ProofCheckingPR using (proofCodeArgs)
open import Godel.ProofRule37Bounds
  using
    ( rule37-left-witness≤proofCode
    ; rule37-right-witness≤proofCode
    )
open import Godel.ProofRule37SearchHit
  using
    ( Rule37SearchHitInterface
    ; Rule37WitnessBoundedHit
    ; rule37Search-complete-bounded-hit
    )
open import Godel.ProofRule37Search using (rule37SearchF)
open import Godel.ProofRuleTargets
  using
    ( ClosedNumeralNeqRuleNat
    ; Rule37WitnessNat
    )

-- This is the rule-37-specific bridge from the semantic rule target to the
-- bounded-hit shape required by the search theorem.  It uses only the code
-- bounds proved in ProofRule37Bounds.  The actual hit predicate remains
-- abstract, so this module still avoids expanding rule37WitnessF.

record Rule37SemanticHitComplete
    (I : Rule37SearchHitInterface) : Set₁ where
  field
    witness-nat-to-hit :
      {m n proof-code formula-code : ℕ} →
      Rule37WitnessNat m n proof-code formula-code →
      Rule37SearchHitInterface.witness-hit-value
        I
        m
        n
        proof-code
        formula-code
      ≡ suc zero

closedRule37-to-bounded-hit :
  (I : Rule37SearchHitInterface) →
  Rule37SemanticHitComplete I →
  {proof-code formula-code : ℕ} →
  ClosedNumeralNeqRuleNat proof-code formula-code →
  Rule37WitnessBoundedHit I proof-code formula-code
closedRule37-to-bounded-hit
  I
  complete
  {proof-code}
  {formula-code}
  (m ,Σ (n ,Σ (neq ,× (proof-eq ,× formula-eq)))) =
  m ,Σ
    (n ,Σ
      ((rule37-left-witness≤proofCode
          {m}
          {n}
          {proof-code}
          proof-eq
        ,×
        rule37-right-witness≤proofCode
          {m}
          {n}
          {proof-code}
          proof-eq)
       ,×
       Rule37SemanticHitComplete.witness-nat-to-hit
        complete
        {m}
        {n}
        {proof-code}
        {formula-code}
        (neq ,× (proof-eq ,× formula-eq))))

rule37Search-complete-closedRule37 :
  (I : Rule37SearchHitInterface) →
  Rule37SemanticHitComplete I →
  {proof-code formula-code : ℕ} →
  ClosedNumeralNeqRuleNat proof-code formula-code →
  evalPRF rule37SearchF (proofCodeArgs proof-code formula-code)
  ≡ suc zero
rule37Search-complete-closedRule37 I complete rule37 =
  rule37Search-complete-bounded-hit
    I
    (closedRule37-to-bounded-hit I complete rule37)
