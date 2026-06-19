{-# OPTIONS --safe #-}

module Godel.PRConcreteSequenceCoding where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List using (List)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.PRRepresentability
open import Godel.PRSequenceCoding
import Godel.PRHistoryCoding as History

-- These are intentionally ordinary PRF definitions, not new PRF
-- constructors.  The next implementation step is to replace the placeholders
-- with minimal-basis PRF programs that decode History.historyCode.
seqLengthF-candidate : PRF (suc zero)
seqLengthF-candidate = zeroF

seqNthF-candidate : PRF (suc (suc zero))
seqNthF-candidate = zeroF

seqAppendF-candidate : PRF (suc (suc zero))
seqAppendF-candidate = zeroF

seqUpdateF-candidate : PRF (suc (suc (suc zero)))
seqUpdateF-candidate = zeroF

seqAllF-candidate : PRF (suc (suc zero))
seqAllF-candidate = zeroF

record PRConcreteSequenceCodingObligations : Set₁ where
  field
    seqLength-correct :
      (history : List ℕ) →
      evalPRF seqLengthF-candidate (History.historyCode history ∷ []) ≡
      History.historyLength history

    seqNth-correct :
      (history : List ℕ) → (index : ℕ) →
      evalPRF seqNthF-candidate (History.historyCode history ∷ index ∷ []) ≡
      History.historyNthDefault history index zero

concretePRSequenceCoding-fromObligations :
  PRConcreteSequenceCodingObligations →
  PRSequenceCoding
concretePRSequenceCoding-fromObligations obligations = record
  { seqLengthF = seqLengthF-candidate
  ; seqNthF = seqNthF-candidate
  ; seqAppendF = seqAppendF-candidate
  ; seqUpdateF = seqUpdateF-candidate
  ; seqAllF = seqAllF-candidate
  ; seqLength-represented = prf-represented seqLengthF-candidate
  ; seqNth-represented = prf-represented seqNthF-candidate
  ; seqAppend-represented = prf-represented seqAppendF-candidate
  ; seqUpdate-represented = prf-represented seqUpdateF-candidate
  ; seqAll-represented = prf-represented seqAllF-candidate
  ; seqLength-correct =
      PRConcreteSequenceCodingObligations.seqLength-correct obligations
  ; seqNth-correct =
      PRConcreteSequenceCodingObligations.seqNth-correct obligations
  }
