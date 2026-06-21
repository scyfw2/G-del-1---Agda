{-# OPTIONS --safe #-}

module Godel.ProofRule37ParserWitness where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.CanonicalCodePR using (nodeChildrenF)
open import Godel.PrimitiveRecursive
open import Godel.PRBooleanHelpers using (fin0; fin1; fin2; fin3)
open import Godel.PRRepresentabilityFinal
  using
    ( PARepresentsRelation
    ; prrel-represented
    )
open import Godel.ProofRule37DecomposedWitness
  using
    ( Rule37DecomposedWitnessNat
    ; rule37DecomposedWitnessF
    ; rule37DecomposedWitnessPR
    ; rule37DecomposedWitness-complete
    ; rule37DecomposedWitness-sound
    ; rule37DecomposedWitness-nonzero-sound
    )
open import Godel.ProofRuleTargets
  using
    ( rule37WitnessArgs )

-- A parser-backed four-argument witness checker for rule 37.
--
-- This keeps the search-facing argument shape `(m,n,proof-code,formula-code)`,
-- but the proof-code branch now runs through nodeChildrenF and the decomposed
-- node/payload checker rather than comparing proof-code with a fully-built
-- canonical proof-code in one step.

rule37ParserWitnessF : PRF (suc (suc (suc (suc zero))))
rule37ParserWitnessF =
  compF rule37DecomposedWitnessF
    ( projF fin0 ∷
      projF fin1 ∷
      projF fin2 ∷
      compF nodeChildrenF (projF fin2 ∷ []) ∷
      projF fin3 ∷ [])

rule37ParserWitnessPR : PRRel (suc (suc (suc (suc zero))))
rule37ParserWitnessPR =
  rel rule37ParserWitnessF

Rule37ParserWitnessNat : ℕ → ℕ → ℕ → ℕ → Set
Rule37ParserWitnessNat m n proof-code formula-code =
  Rule37DecomposedWitnessNat
    m
    n
    proof-code
    (evalPRF nodeChildrenF (proof-code ∷ []))
    formula-code

rule37ParserWitnessF-correct :
  (m n proof-code formula-code : ℕ) →
  evalPRF
    rule37ParserWitnessF
    (rule37WitnessArgs m n proof-code formula-code)
  ≡
  evalPRF
    rule37DecomposedWitnessF
    (m ∷ n ∷ proof-code ∷
     evalPRF nodeChildrenF (proof-code ∷ []) ∷
     formula-code ∷ [])
rule37ParserWitnessF-correct m n proof-code formula-code =
  refl

rule37ParserWitness-complete :
  {m n proof-code formula-code : ℕ} →
  Rule37ParserWitnessNat m n proof-code formula-code →
  PRRel-holds
    rule37ParserWitnessPR
    (rule37WitnessArgs m n proof-code formula-code)
rule37ParserWitness-complete
    {m} {n} {proof-code} {formula-code} witness =
  rule37DecomposedWitness-complete
    {m = m}
    {n = n}
    {proof-code = proof-code}
    {children-code = evalPRF nodeChildrenF (proof-code ∷ [])}
    {formula-code = formula-code}
    witness

rule37ParserWitness-sound :
  {m n proof-code formula-code : ℕ} →
  PRRel-holds
    rule37ParserWitnessPR
    (rule37WitnessArgs m n proof-code formula-code) →
  Rule37ParserWitnessNat m n proof-code formula-code
rule37ParserWitness-sound {m} {n} {proof-code} {formula-code} holds =
  rule37DecomposedWitness-sound
    {m = m}
    {n = n}
    {proof-code = proof-code}
    {children-code = evalPRF nodeChildrenF (proof-code ∷ [])}
    {formula-code = formula-code}
    holds

abstract
  rule37ParserWitness-nonzero-sound :
    {m n proof-code formula-code : ℕ} →
    Σ ℕ
      (λ k →
        evalPRF
          rule37ParserWitnessF
          (rule37WitnessArgs m n proof-code formula-code)
        ≡ suc k) →
    Rule37ParserWitnessNat m n proof-code formula-code
  rule37ParserWitness-nonzero-sound
      {m} {n} {proof-code} {formula-code} nonzero =
    rule37DecomposedWitness-nonzero-sound
      {m = m}
      {n = n}
      {proof-code = proof-code}
      {children-code = evalPRF nodeChildrenF (proof-code ∷ [])}
      {formula-code = formula-code}
      nonzero

rule37ParserWitnessPR-represented :
  PARepresentsRelation rule37ParserWitnessPR
rule37ParserWitnessPR-represented =
  prrel-represented rule37ParserWitnessPR
