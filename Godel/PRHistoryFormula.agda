{-# OPTIONS --safe #-}

module Godel.PRHistoryFormula where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List using (List)
open import Godel.Core
open import Godel.Syntax
open import Godel.PA
open import Godel.ProofSystem
open import Godel.PAProofCombinators
open import Godel.PrimitiveRecursive
open import Godel.PRRepresentability
import Godel.PRSequenceCoding as Seq
open import Godel.PRSequenceCoding hiding (wkTermN; wkVecN; wkVec)
import Godel.PRHistoryCoding as History

pa-provable-cong : {A B : Formula} → A ≡ B → PA-provable A → PA-provable B
pa-provable-cong eq p = subst PA-provable eq p

wkTermN : ℕ → Term → Term
wkTermN = Seq.wkTermN

wkVecN : {n : ℕ} → ℕ → Vec Term n → Vec Term n
wkVecN = Seq.wkVecN

wkVec : {n : ℕ} → Vec Term n → Vec Term n
wkVec = Seq.wkVec

seqLengthFormula :
  PRPrimitiveRecursionInfrastructure →
  Term →
  Term →
  Formula
seqLengthFormula I sequence-code length-value =
  seqLengthFormulaFor
    (PRPrimitiveRecursionInfrastructure.sequence-coding I)
    sequence-code
    length-value

seqNthFormula :
  PRPrimitiveRecursionInfrastructure →
  Term →
  Term →
  Term →
  Formula
seqNthFormula I sequence-code index value =
  seqNthFormulaFor
    (PRPrimitiveRecursionInfrastructure.sequence-coding I)
    sequence-code
    index
    value

historyValidFormula :
  {n : ℕ} →
  PRPrimitiveRecursionInfrastructure →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  Term →
  Term →
  Vec Term n →
  Formula
historyValidFormula I g h x sequence-code xs =
  historyValidFormulaFor
    (PRPrimitiveRecursionInfrastructure.history-valid-represented I g h)
    x
    sequence-code
    xs

historyBodyFormula :
  {n : ℕ} →
  PRPrimitiveRecursionInfrastructure →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  Vec Term (suc n) →
  Term →
  Term →
  Formula
historyBodyFormula I g h xs y sequence-code =
  historyBodyFormulaFor
    (PRPrimitiveRecursionInfrastructure.sequence-coding I)
    (PRPrimitiveRecursionInfrastructure.history-valid-represented I g h)
    xs
    y
    sequence-code

historyResultFormula :
  {n : ℕ} →
  PRPrimitiveRecursionInfrastructure →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  Vec Term (suc n) →
  Term →
  Formula
historyResultFormula I g h xs y =
  ∃ᶠ (historyBodyFormula I g h (wkVec xs) (wkTerm y) (var zero))

seqLengthFormula-value :
  (I : PRPrimitiveRecursionInfrastructure) →
  (history : List ℕ) →
  PA-provable
    (seqLengthFormula
      I
      (numeral (History.historyCode history))
      (numeral (History.historyLength history)))
seqLengthFormula-value I history
  with PRSequenceCoding.seqLength-represented
         (PRPrimitiveRecursionInfrastructure.sequence-coding I)
... | rep =
  pa-provable-cong
    (cong
      (λ k →
        PARepresentsFunction.graphFormula
          rep
          (numeral (History.historyCode history) ∷ [])
          (numeral k))
      (PRSequenceCoding.seqLength-correct
        (PRPrimitiveRecursionInfrastructure.sequence-coding I)
        history))
    (PARepresentsFunction.represents-value
      rep
      (History.historyCode history ∷ []))

seqNthFormula-value :
  (I : PRPrimitiveRecursionInfrastructure) →
  (history : List ℕ) →
  (index : ℕ) →
  PA-provable
    (seqNthFormula
      I
      (numeral (History.historyCode history))
      (numeral index)
      (numeral (History.historyNthDefault history index zero)))
seqNthFormula-value I history index
  with PRSequenceCoding.seqNth-represented
         (PRPrimitiveRecursionInfrastructure.sequence-coding I)
... | rep =
  pa-provable-cong
    (cong
      (λ k →
        PARepresentsFunction.graphFormula
          rep
          (numeral (History.historyCode history) ∷ numeral index ∷ [])
          (numeral k))
      (PRSequenceCoding.seqNth-correct
        (PRPrimitiveRecursionInfrastructure.sequence-coding I)
        history
        index))
    (PARepresentsFunction.represents-value
      rep
      (History.historyCode history ∷ index ∷ []))

historyValidFormula-value :
  {n : ℕ} →
  (I : PRPrimitiveRecursionInfrastructure) →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (x : ℕ) →
  (xs : Vec ℕ n) →
  PA-provable
    (historyValidFormula
      I g h
      (numeral x)
      (numeral (History.historyCode (History.evalHistory g h x xs)))
      (numeralVec xs))
historyValidFormula-value I g h x xs
  with PRPrimitiveRecursionInfrastructure.history-valid-represented I g h
... | rep =
  pa-provable-cong
    (cong
      (λ k →
        PARepresentsFunction.graphFormula
          rep
          (numeral x ∷
           numeral (History.historyCode (History.evalHistory g h x xs)) ∷
           numeralVec xs)
          (numeral k))
      (PRPrimitiveRecursionInfrastructure.history-valid-correct I g h x xs))
    (PARepresentsFunction.represents-value
      rep
      (x ∷ History.historyCode (History.evalHistory g h x xs) ∷ xs))

historyResultFormula-value :
  {n : ℕ} →
  (I : PRPrimitiveRecursionInfrastructure) →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (xs : Vec ℕ (suc n)) →
  PA-provable
    (historyResultFormula
      I g h
      (numeralVec xs)
      (numeral (evalPRF (precF g h) xs)))
historyResultFormula-value I g h (x ∷ xs) =
  exists-intro-use
    {A =
      historyBodyFormula
        I g h
        (wkVec (numeralVec (x ∷ xs)))
        (wkTerm (numeral (evalPRF (precF g h) (x ∷ xs))))
        (var zero)}
    (numeral (History.historyCode (History.evalHistory g h x xs)))
    (pa-provable-cong
      (sym
        (PRPrimitiveRecursionInfrastructure.history-body-subst0
          I
          g
          h
          (numeralVec (x ∷ xs))
          (numeral (evalPRF (precF g h) (x ∷ xs)))
          (numeral (History.historyCode (History.evalHistory g h x xs)))))
      (and-intro-use
        lengthPart
        (and-intro-use
          (historyValidFormula-value I g h x xs)
          nthPart)))
  where
    hist : List ℕ
    hist = History.evalHistory g h x xs

    code : ℕ
    code = History.historyCode hist

    lengthPart :
      PA-provable
        (seqLengthFormula I (numeral code) (sucᵗ (numeral x)))
    lengthPart =
      pa-provable-cong
        (cong
          (λ t → seqLengthFormula I (numeral code) t)
          (cong numeral (History.historyLength-evalHistory g h x xs)))
        (seqLengthFormula-value I hist)

    nthValue-eq :
      History.historyNthDefault hist x zero ≡
      evalPRF (precF g h) (x ∷ xs)
    nthValue-eq =
      trans
        (History.historyNth-evalHistory-last g h x xs)
        (History.lastHistory-evalPrec g h x xs)

    nthPart :
      PA-provable
        (seqNthFormula
          I
          (numeral code)
          (numeral x)
          (numeral (evalPRF (precF g h) (x ∷ xs))))
    nthPart =
      pa-provable-cong
        (cong
          (λ t → seqNthFormula I (numeral code) (numeral x) t)
          (cong numeral nthValue-eq))
        (seqNthFormula-value I hist x)

historyBackedGraphFormula :
  {n : ℕ} →
  PRPrimitiveRecursionInfrastructure →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  Vec Term (suc n) →
  Term →
  Formula
historyBackedGraphFormula I g h xs y =
  evaluatedGraphFormula (precF g h) xs y ∧
  historyResultFormula I g h xs y

historyBackedGraphFormula-value :
  {n : ℕ} →
  (I : PRPrimitiveRecursionInfrastructure) →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (xs : Vec ℕ (suc n)) →
  PA-provable
    (historyBackedGraphFormula
      I g h
      (numeralVec xs)
      (numeral (evalPRF (precF g h) xs)))
historyBackedGraphFormula-value I g h xs =
  and-intro-use
    (evaluatedGraphFormula-value (precF g h) xs)
    (historyResultFormula-value I g h xs)

historyBackedGraphFormula-unique :
  {n : ℕ} →
  (I : PRPrimitiveRecursionInfrastructure) →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (xs : Vec ℕ (suc n)) →
  (y z : Term) →
  PA-provable
    (historyBackedGraphFormula I g h (numeralVec xs) y ⇒
     (historyBackedGraphFormula I g h (numeralVec xs) z ⇒ y ≈ z))
historyBackedGraphFormula-unique I g h xs y z
  rewrite termValues-numeralVec xs =
  and-left-imp-use
    (eq-unique-value
      {y = y}
      {z = z}
      {c = numeral (evalPRF (precF g h) xs)})

primitive-recursion-closes-with-history :
  {n : ℕ} →
  PRPrimitiveRecursionInfrastructure →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  PARepresentsFunction g →
  PARepresentsFunction h →
  PARepresentsFunction (precF g h)
primitive-recursion-closes-with-history I g h g-rep h-rep = record
  { graphFormula = historyBackedGraphFormula I g h
  ; represents-value = historyBackedGraphFormula-value I g h
  ; represents-unique = historyBackedGraphFormula-unique I g h
  ; represents-exists = λ xs →
      numeral (evalPRF (precF g h) xs) ,Σ
      historyBackedGraphFormula-value I g h xs
  }

record PRHistoryResultUniqueness
    (I : PRPrimitiveRecursionInfrastructure) : Set₁ where
  field
    historyResultFormula-unique :
      {n : ℕ} →
      (g : PRF n) →
      (h : PRF (suc (suc n))) →
      PARepresentsFunction g →
      PARepresentsFunction h →
      (xs : Vec ℕ (suc n)) →
      (y z : Term) →
      PA-provable
        (historyResultFormula I g h (numeralVec xs) y ⇒
         (historyResultFormula I g h (numeralVec xs) z ⇒ y ≈ z))

primitive-recursion-closes-with-concrete-history :
  {n : ℕ} →
  (I : PRPrimitiveRecursionInfrastructure) →
  PRHistoryResultUniqueness I →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  PARepresentsFunction g →
  PARepresentsFunction h →
  PARepresentsFunction (precF g h)
primitive-recursion-closes-with-concrete-history I uniqueness g h g-rep h-rep =
  record
    { graphFormula = historyResultFormula I g h
    ; represents-value = historyResultFormula-value I g h
    ; represents-unique =
        PRHistoryResultUniqueness.historyResultFormula-unique
          uniqueness
          g
          h
          g-rep
          h-rep
    ; represents-exists = λ xs →
        numeral (evalPRF (precF g h) xs) ,Σ
        historyResultFormula-value I g h xs
    }
