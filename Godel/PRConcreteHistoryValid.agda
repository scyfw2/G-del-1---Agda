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
open import Godel.PRHistoryValidCheckers public
open import Godel.PRHistoryValidSemantics
import Godel.PRHistoryCoding as History

-- The checker itself is concrete and verified in PRHistoryValidSemantics.
-- The remaining obligation is only the syntactic substitution stability needed
-- by PRHistoryFormula when the history code is introduced as an existential
-- witness.
record PRConcreteHistoryValidObligations : Set₁ where
  field
    history-body-subst0 :
      {n : ℕ} →
      (g : PRF n) →
      (h : PRF (suc (suc n))) →
      (xs : Vec Term (suc n)) →
      (y sequence-code : Term) →
      subst0 sequence-code
        (historyBodyFormulaFor
          concretePRSequenceCoding
          (prf-represented (history-validF-candidate g h))
          (wkVec xs)
          (wkTerm y)
          (var zero))
      ≡
      historyBodyFormulaFor
        concretePRSequenceCoding
        (prf-represented (history-validF-candidate g h))
        xs
        y
        sequence-code

concretePRPrimitiveRecursionInfrastructure-fromObligations :
  PRConcreteHistoryValidObligations →
  PRPrimitiveRecursionInfrastructure
concretePRPrimitiveRecursionInfrastructure-fromObligations
  history-obligations = record
  { sequence-coding = concretePRSequenceCoding
  ; history-validF = history-validF-candidate
  ; history-valid-represented = λ g h →
      prf-represented (history-validF-candidate g h)
  ; history-body-subst0 =
      PRConcreteHistoryValidObligations.history-body-subst0
        history-obligations
  ; history-valid-correct =
      history-valid-correct-concrete
  }
