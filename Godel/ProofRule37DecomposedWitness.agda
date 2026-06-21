{-# OPTIONS --safe #-}

module Godel.ProofRule37DecomposedWitness where

open import Agda.Builtin.List renaming ([] to []ˡ; _∷_ to _∷ˡ_)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.CanonicalCoding using (atom; encodeCodeListWithRest; canonicalNatFormula)
open import Godel.PrimitiveRecursive
open import Godel.PRBooleanHelpers using (andF; fin0; fin1; fin2; fin3)
open import Godel.PRArithmeticSemantics using (andF-correct; mulNat)
open import Godel.PRBooleanSoundness
  using (and-output-nonzero-sound; and3-output-sound)
open import Godel.PRRepresentabilityFinal
  using
    ( PARepresentsRelation
    ; prrel-represented
    )
open import Godel.ProofRule37NodeChildren
  using
    ( Rule37NodeChildrenNat
    ; args₄
    ; rule37NodeChildrenF
    ; rule37NodeChildrenPR
    ; rule37NodeChildren-complete
    ; rule37NodeChildren-sound
    ; rule37NodeChildren-nonzero-sound
    ; rule37NodeChildrenNat-canonical
    )
open import Godel.ProofRuleTargets
  using
    ( NatNeqNat
    ; closedNumeralNeqCode
    ; closedNumeralNeqFormula
    ; rule37WitnessArgs
    ; rule37FormulaCodeEqF
    ; rule37FormulaCodeEqF-complete
    ; rule37FormulaCodeEqF-nonzero-sound
    ; rule37FormulaCodeEqF-sound
    ; rule37NeqBranchF
    ; rule37NeqBranchF-complete
    ; rule37NeqBranchF-nonzero-sound
    ; rule37NeqBranchF-sound
    )

-- A decomposed rule-37 witness checker.
--
-- The older witness checker compares proof-code directly with the fully
-- constructed canonical proof-code.  This version carries children-code as an
-- explicit witness and checks the proof-code branch through raw node parsing
-- plus the two-atom children payload checker.

fin4 : {n : ℕ} → Fin (suc (suc (suc (suc (suc n)))))
fin4 = fsuc fin3

args₅ :
  ℕ → ℕ → ℕ → ℕ → ℕ →
  Vec ℕ (suc (suc (suc (suc (suc zero)))))
args₅ a b c d e = a ∷ b ∷ c ∷ d ∷ e ∷ []

rule37DecomposedWitnessArgs :
  ℕ → ℕ → ℕ → ℕ → ℕ →
  Vec ℕ (suc (suc (suc (suc (suc zero)))))
rule37DecomposedWitnessArgs m n proof-code children-code formula-code =
  args₅ m n proof-code children-code formula-code

rule37NodeChildrenBranchF : PRF (suc (suc (suc (suc (suc zero)))))
rule37NodeChildrenBranchF =
  compF rule37NodeChildrenF
    ( projF fin2 ∷
      projF fin3 ∷
      projF fin0 ∷
      projF fin1 ∷ [])

rule37FormulaBranchF : PRF (suc (suc (suc (suc (suc zero)))))
rule37FormulaBranchF =
  compF rule37FormulaCodeEqF
    ( projF fin0 ∷
      projF fin1 ∷
      projF fin2 ∷
      projF fin4 ∷ [])

rule37NeqBranch5F : PRF (suc (suc (suc (suc (suc zero)))))
rule37NeqBranch5F =
  compF rule37NeqBranchF
    ( projF fin0 ∷
      projF fin1 ∷
      projF fin2 ∷
      projF fin4 ∷ [])

rule37DecomposedInnerF : PRF (suc (suc (suc (suc (suc zero)))))
rule37DecomposedInnerF =
  compF andF
    (rule37FormulaBranchF ∷
     rule37NeqBranch5F ∷ [])

rule37DecomposedWitnessF : PRF (suc (suc (suc (suc (suc zero)))))
rule37DecomposedWitnessF =
  compF andF
    (rule37NodeChildrenBranchF ∷
     rule37DecomposedInnerF ∷ [])

rule37DecomposedWitnessPR : PRRel (suc (suc (suc (suc (suc zero)))))
rule37DecomposedWitnessPR =
  rel rule37DecomposedWitnessF

Rule37DecomposedWitnessNat : ℕ → ℕ → ℕ → ℕ → ℕ → Set
Rule37DecomposedWitnessNat m n proof-code children-code formula-code =
  NatNeqNat m n ×
  (Rule37NodeChildrenNat proof-code children-code m n ×
   (formula-code ≡ canonicalNatFormula (closedNumeralNeqFormula m n)))

rule37NodeChildrenBranchF-correct :
  (m n proof-code children-code formula-code : ℕ) →
  evalPRF
    rule37NodeChildrenBranchF
    (rule37DecomposedWitnessArgs
      m n proof-code children-code formula-code)
  ≡
  evalPRF
    rule37NodeChildrenF
    (args₄ proof-code children-code m n)
rule37NodeChildrenBranchF-correct m n proof-code children-code formula-code =
  refl

rule37FormulaBranchF-correct :
  (m n proof-code children-code formula-code : ℕ) →
  evalPRF
    rule37FormulaBranchF
    (rule37DecomposedWitnessArgs
      m n proof-code children-code formula-code)
  ≡
  evalPRF
    rule37FormulaCodeEqF
    (rule37WitnessArgs m n proof-code formula-code)
rule37FormulaBranchF-correct m n proof-code children-code formula-code =
  refl

rule37NeqBranch5F-correct :
  (m n proof-code children-code formula-code : ℕ) →
  evalPRF
    rule37NeqBranch5F
    (rule37DecomposedWitnessArgs
      m n proof-code children-code formula-code)
  ≡
  evalPRF
    rule37NeqBranchF
    (rule37WitnessArgs m n proof-code formula-code)
rule37NeqBranch5F-correct m n proof-code children-code formula-code =
  refl

rule37DecomposedWitnessF-correct-flat :
  (m n proof-code children-code formula-code : ℕ) →
  evalPRF
    rule37DecomposedWitnessF
    (rule37DecomposedWitnessArgs
      m n proof-code children-code formula-code)
  ≡
  mulNat
    (evalPRF
      rule37NodeChildrenF
      (args₄ proof-code children-code m n))
    (mulNat
      (evalPRF
        rule37FormulaCodeEqF
        (rule37WitnessArgs m n proof-code formula-code))
      (evalPRF
        rule37NeqBranchF
        (rule37WitnessArgs m n proof-code formula-code)))
rule37DecomposedWitnessF-correct-flat
    m n proof-code children-code formula-code
  rewrite andF-correct
            (evalPRF
              rule37NodeChildrenBranchF
              (rule37DecomposedWitnessArgs
                m n proof-code children-code formula-code))
            (evalPRF
              rule37DecomposedInnerF
              (rule37DecomposedWitnessArgs
                m n proof-code children-code formula-code))
        | andF-correct
            (evalPRF
              rule37FormulaBranchF
              (rule37DecomposedWitnessArgs
                m n proof-code children-code formula-code))
            (evalPRF
              rule37NeqBranch5F
              (rule37DecomposedWitnessArgs
                m n proof-code children-code formula-code))
        | rule37NodeChildrenBranchF-correct
            m n proof-code children-code formula-code
        | rule37FormulaBranchF-correct
            m n proof-code children-code formula-code
        | rule37NeqBranch5F-correct
            m n proof-code children-code formula-code =
  refl

rule37DecomposedWitness-complete :
  {m n proof-code children-code formula-code : ℕ} →
  Rule37DecomposedWitnessNat
    m n proof-code children-code formula-code →
  PRRel-holds
    rule37DecomposedWitnessPR
    (rule37DecomposedWitnessArgs
      m n proof-code children-code formula-code)
rule37DecomposedWitness-complete
    {m} {n} {proof-code} {children-code} {formula-code}
    (neq ,× (node-children ,× formula-eq))
  rewrite rule37DecomposedWitnessF-correct-flat
            m n proof-code children-code formula-code
        | rule37NodeChildren-complete
            {proof-code = proof-code}
            {children-code = children-code}
            {m = m}
            {n = n}
            node-children
        | rule37FormulaCodeEqF-complete
            {m = m}
            {n = n}
            {proof-code = proof-code}
            {formula-code = formula-code}
            formula-eq
        | rule37NeqBranchF-complete
            {m = m}
            {n = n}
            {proof-code = proof-code}
            {formula-code = formula-code}
            neq =
  refl

rule37DecomposedWitness-sound :
  {m n proof-code children-code formula-code : ℕ} →
  PRRel-holds
    rule37DecomposedWitnessPR
    (rule37DecomposedWitnessArgs
      m n proof-code children-code formula-code) →
  Rule37DecomposedWitnessNat
    m n proof-code children-code formula-code
rule37DecomposedWitness-sound
    {m} {n} {proof-code} {children-code} {formula-code} holds
  with and3-output-sound
        (evalPRF
          rule37NodeChildrenF
          (args₄ proof-code children-code m n))
        (evalPRF
          rule37FormulaCodeEqF
          (rule37WitnessArgs m n proof-code formula-code))
        (evalPRF
          rule37NeqBranchF
          (rule37WitnessArgs m n proof-code formula-code))
        (evalPRF
          rule37DecomposedWitnessF
          (rule37DecomposedWitnessArgs
            m n proof-code children-code formula-code))
        (rule37DecomposedWitnessF-correct-flat
          m n proof-code children-code formula-code)
        holds
... | node-children-one ,× (formula-one ,× neq-one) =
  rule37NeqBranchF-sound
    {m = m}
    {n = n}
    {proof-code = proof-code}
    {formula-code = formula-code}
    neq-one
  ,×
  ( rule37NodeChildren-sound
      {proof-code = proof-code}
      {children-code = children-code}
      {m = m}
      {n = n}
      node-children-one
  ,×
    rule37FormulaCodeEqF-sound
      {m = m}
      {n = n}
      {proof-code = proof-code}
      {formula-code = formula-code}
      formula-one
  )

rule37DecomposedWitness-nonzero-sound :
  {m n proof-code children-code formula-code : ℕ} →
  Σ ℕ
    (λ k →
      evalPRF
        rule37DecomposedWitnessF
        (rule37DecomposedWitnessArgs
          m n proof-code children-code formula-code)
      ≡ suc k) →
  Rule37DecomposedWitnessNat
    m n proof-code children-code formula-code
rule37DecomposedWitness-nonzero-sound
    {m} {n} {proof-code} {children-code} {formula-code} nonzero
  with and-output-nonzero-sound
        (evalPRF
          rule37NodeChildrenF
          (args₄ proof-code children-code m n))
        (mulNat
          (evalPRF
            rule37FormulaCodeEqF
            (rule37WitnessArgs m n proof-code formula-code))
          (evalPRF
            rule37NeqBranchF
            (rule37WitnessArgs m n proof-code formula-code)))
        (evalPRF
          rule37DecomposedWitnessF
          (rule37DecomposedWitnessArgs
            m n proof-code children-code formula-code))
        (rule37DecomposedWitnessF-correct-flat
          m n proof-code children-code formula-code)
        nonzero
... | node-children-nz ,× inner-nz
  with and-output-nonzero-sound
        (evalPRF
          rule37FormulaCodeEqF
          (rule37WitnessArgs m n proof-code formula-code))
        (evalPRF
          rule37NeqBranchF
          (rule37WitnessArgs m n proof-code formula-code))
        (mulNat
          (evalPRF
            rule37FormulaCodeEqF
            (rule37WitnessArgs m n proof-code formula-code))
          (evalPRF
            rule37NeqBranchF
            (rule37WitnessArgs m n proof-code formula-code)))
        refl
        inner-nz
... | formula-nz ,× neq-nz =
  rule37NeqBranchF-nonzero-sound
    {m = m}
    {n = n}
    {proof-code = proof-code}
    {formula-code = formula-code}
    neq-nz
  ,×
  ( rule37NodeChildren-nonzero-sound
      {proof-code = proof-code}
      {children-code = children-code}
      {m = m}
      {n = n}
      node-children-nz
  ,×
    rule37FormulaCodeEqF-nonzero-sound
      {m = m}
      {n = n}
      {proof-code = proof-code}
      {formula-code = formula-code}
      formula-nz
  )

rule37DecomposedWitness-canonical :
  {m n formula-code : ℕ} →
  NatNeqNat m n →
  formula-code ≡ canonicalNatFormula (closedNumeralNeqFormula m n) →
  Rule37DecomposedWitnessNat
    m
    n
    (closedNumeralNeqCode m n)
    (encodeCodeListWithRest (atom m ∷ˡ atom n ∷ˡ []ˡ) zero)
    formula-code
rule37DecomposedWitness-canonical {m} {n} neq formula-eq =
  neq
  ,×
  ( rule37NodeChildrenNat-canonical m n
  ,×
    formula-eq
  )

rule37DecomposedWitnessPR-represented :
  PARepresentsRelation rule37DecomposedWitnessPR
rule37DecomposedWitnessPR-represented =
  prrel-represented rule37DecomposedWitnessPR
