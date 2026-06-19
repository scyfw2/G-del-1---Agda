{-# OPTIONS --safe #-}

module Godel.PRConcreteHistoryValid where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.PA
open import Godel.PrimitiveRecursive
open import Godel.PRRepresentability
open import Godel.PRSequenceCoding
open import Godel.PRConcreteSequenceCoding
import Godel.PRHistoryCoding as History

-- Candidate PR checker for a coded primitive-recursion computation history.
-- This remains a minimal-basis PRF placeholder until the bounded traversal
-- over History.historyCode is implemented.
history-validF-candidate :
  {n : ℕ} →
  PRF n →
  PRF (suc (suc n)) →
  PRF (suc (suc n))
history-validF-candidate g h = zeroF

record PRConcreteHistoryValidObligations
    (sequence-obligations : PRConcreteSequenceCodingObligations) : Set₁ where
  field
    history-valid-correct :
      {n : ℕ} →
      (g : PRF n) →
      (h : PRF (suc (suc n))) →
      (x : ℕ) →
      (xs : Vec ℕ n) →
      evalPRF
        (history-validF-candidate g h)
        (x ∷ History.historyCode (History.evalHistory g h x xs) ∷ xs)
      ≡ suc zero

    history-body-subst0 :
      {n : ℕ} →
      (g : PRF n) →
      (h : PRF (suc (suc n))) →
      (xs : Vec Term (suc n)) →
      (y sequence-code : Term) →
      subst0 sequence-code
        (historyBodyFormulaFor
          (concretePRSequenceCoding-fromObligations sequence-obligations)
          (prf-represented (history-validF-candidate g h))
          (wkVec xs)
          (wkTerm y)
          (var zero))
      ≡
      historyBodyFormulaFor
        (concretePRSequenceCoding-fromObligations sequence-obligations)
        (prf-represented (history-validF-candidate g h))
        xs
        y
        sequence-code

concretePRPrimitiveRecursionInfrastructure-fromObligations :
  (sequence-obligations : PRConcreteSequenceCodingObligations) →
  PRConcreteHistoryValidObligations sequence-obligations →
  PRPrimitiveRecursionInfrastructure
concretePRPrimitiveRecursionInfrastructure-fromObligations
  sequence-obligations
  history-obligations = record
  { sequence-coding =
      concretePRSequenceCoding-fromObligations sequence-obligations
  ; history-validF = history-validF-candidate
  ; history-valid-represented = λ g h →
      prf-represented (history-validF-candidate g h)
  ; history-body-subst0 =
      PRConcreteHistoryValidObligations.history-body-subst0
        history-obligations
  ; history-valid-correct =
      PRConcreteHistoryValidObligations.history-valid-correct
        history-obligations
  }
