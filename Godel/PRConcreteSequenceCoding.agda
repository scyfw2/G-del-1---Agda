{-# OPTIONS --safe #-}

module Godel.PRConcreteSequenceCoding where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List using (List; []; _∷_)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.PRRepresentability
open import Godel.PRSequenceCoding
open import Godel.PRNatListDecoder
open import Godel.PRNatListDecoderSemantics
open import Godel.PRNatListDigitStream
import Godel.PRHistoryCoding as History

seqLengthF-candidate : PRF (suc zero)
seqLengthF-candidate = seqLengthF

seqNthF-candidate : PRF (suc (suc zero))
seqNthF-candidate = seqNthF

seqAppendF-candidate : PRF (suc (suc zero))
seqAppendF-candidate = zeroF

seqUpdateF-candidate : PRF (suc (suc (suc zero)))
seqUpdateF-candidate = zeroF

seqAllF-candidate : PRF (suc (suc zero))
seqAllF-candidate = zeroF

seqLength-empty-example :
  evalPRF seqLengthF-candidate (History.historyCode [] ∷ []) ≡ zero
seqLength-empty-example = refl

seqLength-single-zero-example :
  evalPRF seqLengthF-candidate (History.historyCode (zero ∷ []) ∷ []) ≡
  suc zero
seqLength-single-zero-example = refl

seqNth-single-zero-example :
  evalPRF seqNthF-candidate (History.historyCode (zero ∷ []) ∷ zero ∷ []) ≡
  zero
seqNth-single-zero-example = refl

seqNth-single-one-example :
  evalPRF seqNthF-candidate
    (History.historyCode (suc zero ∷ []) ∷ zero ∷ []) ≡
  suc zero
seqNth-single-one-example = refl

seqNth-out-of-bounds-example :
  evalPRF seqNthF-candidate
    (History.historyCode (suc zero ∷ []) ∷ suc zero ∷ []) ≡
  zero
seqNth-out-of-bounds-example = refl

seqLength-correct-concrete :
  (history : List ℕ) →
  evalPRF seqLengthF-candidate (History.historyCode history ∷ []) ≡
  History.historyLength history
seqLength-correct-concrete history
  rewrite seqLengthF-correct-to-meta (History.historyCode history) =
  seqLengthNat-historyCode history

seqNth-correct-to-digit-stream :
  (history : List ℕ) → (index : ℕ) →
  evalPRF seqNthF-candidate (History.historyCode history ∷ index ∷ []) ≡
  seqNthDigitsUpTo
    (scanBound (natListDigits history))
    (natListDigits history)
    index
seqNth-correct-to-digit-stream history index
  rewrite seqNthF-correct-to-meta (History.historyCode history) index =
  seqNthNat-historyCode-as-digits history index

seqNth-correct-concrete :
  (history : List ℕ) → (index : ℕ) →
  evalPRF seqNthF-candidate (History.historyCode history ∷ index ∷ []) ≡
  History.historyNthDefault history index zero
seqNth-correct-concrete history index =
  trans
    (seqNth-correct-to-digit-stream history index)
    (seqNthDigitsUpTo-natListDigits history index)

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

concretePRSequenceCoding-obligations :
  PRConcreteSequenceCodingObligations
concretePRSequenceCoding-obligations = record
  { seqLength-correct = seqLength-correct-concrete
  ; seqNth-correct = seqNth-correct-concrete
  }

concretePRSequenceCoding : PRSequenceCoding
concretePRSequenceCoding =
  concretePRSequenceCoding-fromObligations
    concretePRSequenceCoding-obligations
