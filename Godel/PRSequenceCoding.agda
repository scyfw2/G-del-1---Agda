{-# OPTIONS --safe #-}

module Godel.PRSequenceCoding where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List using (List)
open import Godel.Core
open import Godel.Syntax
open import Godel.PrimitiveRecursive
import Godel.PRHistoryCoding as History
open import Godel.PRRepresentability

wkTermN : ℕ → Term → Term
wkTermN zero t = t
wkTermN (suc n) t = wkTermN n (wkTerm t)

wkVecN : {n : ℕ} → ℕ → Vec Term n → Vec Term n
wkVecN k [] = []
wkVecN k (x ∷ xs) = wkTermN k x ∷ wkVecN k xs

wkVec : {n : ℕ} → Vec Term n → Vec Term n
wkVec = wkVecN (suc zero)

-- Primitive recursion representability eventually needs PA to reason about a
-- coded finite computation history.  This record names the exact sequence
-- coding substrate required by that proof.
record PRSequenceCoding : Set₁ where
  field
    seqLengthF : PRF (suc zero)
    seqNthF    : PRF (suc (suc zero))
    seqAppendF : PRF (suc (suc zero))
    seqUpdateF : PRF (suc (suc (suc zero)))
    seqAllF    : PRF (suc (suc zero))

    seqLength-represented : PARepresentsFunction seqLengthF
    seqNth-represented    : PARepresentsFunction seqNthF
    seqAppend-represented : PARepresentsFunction seqAppendF
    seqUpdate-represented : PARepresentsFunction seqUpdateF
    seqAll-represented    : PARepresentsFunction seqAllF

    seqLength-correct :
      (history : List ℕ) →
      evalPRF seqLengthF (History.historyCode history ∷ []) ≡
      History.historyLength history

    seqNth-correct :
      (history : List ℕ) → (index : ℕ) →
      evalPRF seqNthF (History.historyCode history ∷ index ∷ []) ≡
      History.historyNthDefault history index zero

seqLengthFormulaFor :
  PRSequenceCoding →
  Term →
  Term →
  Formula
seqLengthFormulaFor seq sequence-code length-value =
  PARepresentsFunction.graphFormula
    (PRSequenceCoding.seqLength-represented seq)
    (sequence-code ∷ [])
    length-value

seqNthFormulaFor :
  PRSequenceCoding →
  Term →
  Term →
  Term →
  Formula
seqNthFormulaFor seq sequence-code index value =
  PARepresentsFunction.graphFormula
    (PRSequenceCoding.seqNth-represented seq)
    (sequence-code ∷ index ∷ [])
    value

historyValidFormulaFor :
  {n : ℕ} →
  {history-valid : PRF (suc (suc n))} →
  PARepresentsFunction history-valid →
  Term →
  Term →
  Vec Term n →
  Formula
historyValidFormulaFor history-valid-rep x sequence-code xs =
  PARepresentsFunction.graphFormula
    history-valid-rep
    (x ∷ sequence-code ∷ xs)
    (numeral (suc zero))

historyBodyFormulaFor :
  {n : ℕ} →
  PRSequenceCoding →
  {history-valid : PRF (suc (suc n))} →
  PARepresentsFunction history-valid →
  Vec Term (suc n) →
  Term →
  Term →
  Formula
historyBodyFormulaFor seq history-valid-rep (x ∷ xs) y sequence-code =
  seqLengthFormulaFor seq sequence-code (sucᵗ x) ∧
  (historyValidFormulaFor history-valid-rep x sequence-code xs ∧
   seqNthFormulaFor seq sequence-code x y)

record PRPrimitiveRecursionInfrastructure : Set₁ where
  field
    sequence-coding : PRSequenceCoding

    history-validF :
      {n : ℕ} →
      PRF n →
      PRF (suc (suc n)) →
      PRF (suc (suc n))

    history-valid-represented :
      {n : ℕ} →
      (g : PRF n) →
      (h : PRF (suc (suc n))) →
      PARepresentsFunction (history-validF g h)

    history-body-subst0 :
      {n : ℕ} →
      (g : PRF n) →
      (h : PRF (suc (suc n))) →
      (xs : Vec Term (suc n)) →
      (y sequence-code : Term) →
      subst0 sequence-code
        (historyBodyFormulaFor
          sequence-coding
          (history-valid-represented g h)
          (wkVec xs)
          (wkTerm y)
          (var zero))
      ≡
      historyBodyFormulaFor
        sequence-coding
        (history-valid-represented g h)
        xs
        y
        sequence-code

    history-valid-correct :
      {n : ℕ} →
      (g : PRF n) →
      (h : PRF (suc (suc n))) →
      (x : ℕ) →
      (xs : Vec ℕ n) →
      evalPRF
        (history-validF g h)
        (x ∷ History.historyCode (History.evalHistory g h x xs) ∷ xs)
      ≡ suc zero
