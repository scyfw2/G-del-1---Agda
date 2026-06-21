{-# OPTIONS --safe #-}

module Godel.ProofRuleFixedPair where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.PRBooleanHelpers using (fin0; fin1; andF; eqNatF)
open import Godel.PRBoundedSearch using (constF)
open import Godel.PRArithmeticSemantics
  using
    ( constF-correct
    ; andF-correct
    ; eqNatF-correct
    ; eqNatNat
    ; mulNat
    )
open import Godel.PRBooleanSoundness using (and-output-sound)
open import Godel.CanonicalCodePR
  using
    ( eqNatNat-refl-code
    ; eqNatNat-sound-code
    )
open import Godel.PRRepresentabilityFinal
  using (PARepresentsRelation; prrel-represented)
open import Godel.ProofCheckingPR using (proofCodeArgs)

-- Reusable PR component for proof-checker branches whose successful output is
-- exactly a fixed pair of numeric codes:
--
--   input proof-code   = expected-proof-code
--   input formula-code = expected-formula-code
--
-- This is useful for fixed axiom/proof-rule leaves and keeps those branches on
-- the final PRRepresentability route.

fixedProofCodeEqF : ℕ → PRF (suc (suc zero))
fixedProofCodeEqF expected-proof-code =
  compF eqNatF
    (projF fin0 ∷
     constF expected-proof-code ∷ [])

fixedFormulaCodeEqF : ℕ → PRF (suc (suc zero))
fixedFormulaCodeEqF expected-formula-code =
  compF eqNatF
    (projF fin1 ∷
     constF expected-formula-code ∷ [])

fixedPairF : ℕ → ℕ → PRF (suc (suc zero))
fixedPairF expected-proof-code expected-formula-code =
  compF andF
    (fixedProofCodeEqF expected-proof-code ∷
     fixedFormulaCodeEqF expected-formula-code ∷ [])

fixedPairPR : ℕ → ℕ → PRRel (suc (suc zero))
fixedPairPR expected-proof-code expected-formula-code =
  rel (fixedPairF expected-proof-code expected-formula-code)

FixedPairNat : ℕ → ℕ → ℕ → ℕ → Set
FixedPairNat expected-proof-code expected-formula-code proof-code formula-code =
  (proof-code ≡ expected-proof-code) ×
  (formula-code ≡ expected-formula-code)

fixedProofCodeEqF-correct :
  (expected-proof-code proof-code formula-code : ℕ) →
  evalPRF
    (fixedProofCodeEqF expected-proof-code)
    (proofCodeArgs proof-code formula-code)
  ≡
  eqNatNat proof-code expected-proof-code
fixedProofCodeEqF-correct expected-proof-code proof-code formula-code
  rewrite constF-correct expected-proof-code
            (proofCodeArgs proof-code formula-code)
        | eqNatF-correct proof-code expected-proof-code =
  refl

fixedFormulaCodeEqF-correct :
  (expected-formula-code proof-code formula-code : ℕ) →
  evalPRF
    (fixedFormulaCodeEqF expected-formula-code)
    (proofCodeArgs proof-code formula-code)
  ≡
  eqNatNat formula-code expected-formula-code
fixedFormulaCodeEqF-correct expected-formula-code proof-code formula-code
  rewrite constF-correct expected-formula-code
            (proofCodeArgs proof-code formula-code)
        | eqNatF-correct formula-code expected-formula-code =
  refl

fixedPairF-correct :
  (expected-proof-code expected-formula-code proof-code formula-code : ℕ) →
  evalPRF
    (fixedPairF expected-proof-code expected-formula-code)
    (proofCodeArgs proof-code formula-code)
  ≡
  mulNat
    (eqNatNat proof-code expected-proof-code)
    (eqNatNat formula-code expected-formula-code)
fixedPairF-correct expected-proof-code expected-formula-code proof-code formula-code
  rewrite fixedProofCodeEqF-correct
            expected-proof-code
            proof-code
            formula-code
        | fixedFormulaCodeEqF-correct
            expected-formula-code
            proof-code
            formula-code
        | andF-correct
            (eqNatNat proof-code expected-proof-code)
            (eqNatNat formula-code expected-formula-code) =
  refl

fixedPairF-complete :
  {expected-proof-code expected-formula-code proof-code formula-code : ℕ} →
  FixedPairNat
    expected-proof-code
    expected-formula-code
    proof-code
    formula-code →
  evalPRF
    (fixedPairF expected-proof-code expected-formula-code)
    (proofCodeArgs proof-code formula-code)
  ≡ suc zero
fixedPairF-complete
  {expected-proof-code}
  {expected-formula-code}
  {proof-code}
  {formula-code}
  (proof-eq ,× formula-eq)
  rewrite fixedPairF-correct
            expected-proof-code
            expected-formula-code
            proof-code
            formula-code
        | proof-eq
        | formula-eq
        | eqNatNat-refl-code expected-proof-code
        | eqNatNat-refl-code expected-formula-code =
  refl

fixedPairF-sound :
  {expected-proof-code expected-formula-code proof-code formula-code : ℕ} →
  evalPRF
    (fixedPairF expected-proof-code expected-formula-code)
    (proofCodeArgs proof-code formula-code)
  ≡ suc zero →
  FixedPairNat
    expected-proof-code
    expected-formula-code
    proof-code
    formula-code
fixedPairF-sound
  {expected-proof-code}
  {expected-formula-code}
  {proof-code}
  {formula-code}
  holds
  with and-output-sound
        (eqNatNat proof-code expected-proof-code)
        (eqNatNat formula-code expected-formula-code)
        (evalPRF
          (fixedPairF expected-proof-code expected-formula-code)
          (proofCodeArgs proof-code formula-code))
        (fixedPairF-correct
          expected-proof-code
          expected-formula-code
          proof-code
          formula-code)
        holds
... | proof-one ,× formula-one =
  eqNatNat-sound-code proof-code expected-proof-code proof-one ,×
  eqNatNat-sound-code formula-code expected-formula-code formula-one

fixedPairPR-represented :
  (expected-proof-code expected-formula-code : ℕ) →
  PARepresentsRelation (fixedPairPR expected-proof-code expected-formula-code)
fixedPairPR-represented expected-proof-code expected-formula-code =
  prrel-represented (fixedPairPR expected-proof-code expected-formula-code)
