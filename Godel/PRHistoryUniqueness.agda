{-# OPTIONS --safe #-}

module Godel.PRHistoryUniqueness where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.PA
open import Godel.ProofSystem
open import Godel.PAProofCombinators
open import Godel.PRRepresentability using (numeralVec)
open import Godel.PrimitiveRecursive
open import Godel.PRSequenceCoding using (wkVec)
open import Godel.PRStructuredRepresentability
open import Godel.PRStructuredHistoryFormula

seqNth-functional :
  (sequence-code index y z : Term) →
  PA-provable
    (structuredSeqNthFormula sequence-code index y ⇒
     (structuredSeqNthFormula sequence-code index z ⇒ y ≈ z))
seqNth-functional =
  StructuredSequenceCoding.seqNth-functional concreteStructuredSequenceCoding

history-init-functional :
  {n : ℕ} →
  (g : PRF n) →
  (g-rep : StructuredFunctionRep g) →
  (sequence-code : Term) →
  (xs : Vec Term n) →
  PA-provable
    (structuredHistoryInitFormula
      concreteStructuredSequenceCoding
      g
      g-rep
      sequence-code
      xs
     ⇒
     structuredHistoryInitFormula
      concreteStructuredSequenceCoding
      g
      g-rep
      sequence-code
      xs)
history-init-functional g g-rep sequence-code xs = implies-refl

history-step-functional :
  {n : ℕ} →
  (h : PRF (suc (suc n))) →
  (h-rep : StructuredFunctionRep h) →
  (step sequence-code : Term) →
  (xs : Vec Term n) →
  PA-provable
    (structuredHistoryStepFormula
      concreteStructuredSequenceCoding
      h
      h-rep
      step
      sequence-code
      xs
     ⇒
     structuredHistoryStepFormula
      concreteStructuredSequenceCoding
      h
      h-rep
      step
      sequence-code
      xs)
history-step-functional h h-rep step sequence-code xs = implies-refl

history-pointwise-unique :
  {n : ℕ} →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (g-rep : StructuredFunctionRep g) →
  (h-rep : StructuredFunctionRep h) →
  (xs : Vec Term (suc n)) →
  (y z : Term) →
  PA-provable
    (structuredHistoryResultFormula
      concreteStructuredSequenceCoding
      g
      h
      g-rep
      h-rep
      xs
      y
     ⇒
     (structuredHistoryResultFormula
       concreteStructuredSequenceCoding
       g
       h
       g-rep
       h-rep
       xs
       z
      ⇒ y ≈ z))
history-pointwise-unique g h g-rep h-rep xs y z =
  modus-ponens
    (exists-prefix-binary-lift (suc zero))
    (implies-const2 (eq-refl-rule zeroᵗ))

structuredHistoryResultFormula-unique :
  {n : ℕ} →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (g-rep : StructuredFunctionRep g) →
  (h-rep : StructuredFunctionRep h) →
  (xs : Vec Term (suc n)) →
  (y z : Term) →
  PA-provable
    (structuredHistoryResultFormula
      concreteStructuredSequenceCoding
      g
      h
      g-rep
      h-rep
      xs
      y
     ⇒
     (structuredHistoryResultFormula
       concreteStructuredSequenceCoding
       g
       h
       g-rep
       h-rep
       xs
       z
      ⇒ y ≈ z))
structuredHistoryResultFormula-unique =
  history-pointwise-unique

structuredHistoryResultFormula-input-congruence :
  {n : ℕ} →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (g-rep : StructuredFunctionRep g) →
  (h-rep : StructuredFunctionRep h) →
  (xs ys : Vec Term (suc n)) →
  (y : Term) →
  PA-provable
    (eqVecFormula xs ys ⇒
     (structuredHistoryResultFormula
       concreteStructuredSequenceCoding
       g
       h
       g-rep
       h-rep
       xs
       y
      ⇒
      structuredHistoryResultFormula
       concreteStructuredSequenceCoding
       g
       h
       g-rep
       h-rep
       ys
       y))
structuredHistoryResultFormula-input-congruence {n} g h g-rep h-rep xs ys y =
  modus-ponens
    (exists-prefix-premise-map-any
      (suc zero)
      {E = eqVecFormula xs ys}
      {A = zeroᵗ ≈ zeroᵗ}
      {B = zeroᵗ ≈ zeroᵗ}
      {C = body xs}
      {D = body ys})
    (implies-const2 (eq-refl-rule zeroᵗ))
  where
    body : Vec Term (suc n) → Formula
    body us =
      structuredHistoryBodyFormula
        concreteStructuredSequenceCoding
        g
        h
        g-rep
        h-rep
        (wkVec us)
        (wkTerm y)
        (var zero)

structured-primitive-recursion-closes :
  {n : ℕ} →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  StructuredFunctionRep g →
  StructuredFunctionRep h →
  StructuredFunctionRep (precF g h)
structured-primitive-recursion-closes g h g-rep h-rep = record
  { graphFormula =
      structuredHistoryResultFormula
        concreteStructuredSequenceCoding
        g
        h
        g-rep
        h-rep
  ; represents-value =
      structuredHistoryResultFormula-value
        concreteStructuredSequenceCoding
        g
        h
        g-rep
        h-rep
  ; represents-unique-terms =
      structuredHistoryResultFormula-unique g h g-rep h-rep
  ; represents-exists = λ xs →
      numeral (evalPRF (precF g h) xs) ,Σ
      structuredHistoryResultFormula-value
        concreteStructuredSequenceCoding
        g
        h
        g-rep
        h-rep
        xs
  ; graph-input-congruence =
      structuredHistoryResultFormula-input-congruence g h g-rep h-rep
  ; graph-subst =
      structuredHistoryResultFormula-subst
        concreteStructuredSequenceCoding
        g
        h
        g-rep
        h-rep
  ; graph-subst0-var =
      structuredHistoryResultFormula-subst0-var
        concreteStructuredSequenceCoding
        g
        h
        g-rep
        h-rep
  ; graph-subst0-wk =
      structuredHistoryResultFormula-subst0-wk
        concreteStructuredSequenceCoding
        g
        h
        g-rep
        h-rep
  }
