{-# OPTIONS --safe #-}

module Godel.ProofRulePRDisjunction where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.PRBooleanHelpers using (orF)
open import Godel.PRArithmeticSemantics using (orF-correct)
open import Godel.PRRepresentabilityFinal
  using (PARepresentsRelation; prrel-represented)
open import Godel.ProofCheckingPR using (proofCodeArgs)
open import Godel.ProofRuleFixedProofOr
  using
    ( NonzeroNat
    ; or-output-complete-left
    ; or-output-complete-right
    ; or-output-nonzero-sound
    )

-- Generic binary disjunction for proof-rule PR relations over
-- (proof-code, formula-code).  This is the relation-level glue used to combine
-- independently represented proof-checker branches without specializing their
-- decoded soundness proofs.

orProofRuleF :
  PRRel (suc (suc zero)) →
  PRRel (suc (suc zero)) →
  PRF (suc (suc zero))
orProofRuleF left right =
  compF orF
    (PRRel.characteristic left ∷
     PRRel.characteristic right ∷ [])

orProofRulePR :
  PRRel (suc (suc zero)) →
  PRRel (suc (suc zero)) →
  PRRel (suc (suc zero))
orProofRulePR left right =
  rel (orProofRuleF left right)

orProofRule-complete-left :
  (left right : PRRel (suc (suc zero))) →
  {proof-code formula-code : ℕ} →
  PRRel-holds left (proofCodeArgs proof-code formula-code) →
  PRRel-holds
    (orProofRulePR left right)
    (proofCodeArgs proof-code formula-code)
orProofRule-complete-left left right {proof-code} {formula-code} left-holds
  rewrite orF-correct
            (evalPRF
              (PRRel.characteristic left)
              (proofCodeArgs proof-code formula-code))
            (evalPRF
              (PRRel.characteristic right)
              (proofCodeArgs proof-code formula-code)) =
  or-output-complete-left
    (evalPRF
      (PRRel.characteristic left)
      (proofCodeArgs proof-code formula-code))
    (evalPRF
      (PRRel.characteristic right)
      (proofCodeArgs proof-code formula-code))
    (zero ,Σ left-holds)

orProofRule-complete-right :
  (left right : PRRel (suc (suc zero))) →
  {proof-code formula-code : ℕ} →
  PRRel-holds right (proofCodeArgs proof-code formula-code) →
  PRRel-holds
    (orProofRulePR left right)
    (proofCodeArgs proof-code formula-code)
orProofRule-complete-right left right {proof-code} {formula-code} right-holds
  rewrite orF-correct
            (evalPRF
              (PRRel.characteristic left)
              (proofCodeArgs proof-code formula-code))
            (evalPRF
              (PRRel.characteristic right)
              (proofCodeArgs proof-code formula-code)) =
  or-output-complete-right
    (evalPRF
      (PRRel.characteristic left)
      (proofCodeArgs proof-code formula-code))
    (evalPRF
      (PRRel.characteristic right)
      (proofCodeArgs proof-code formula-code))
    (zero ,Σ right-holds)

orProofRule-nonzero-sound :
  (left right : PRRel (suc (suc zero))) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (orProofRulePR left right)
    (proofCodeArgs proof-code formula-code) →
  NonzeroNat
    (evalPRF
      (PRRel.characteristic left)
      (proofCodeArgs proof-code formula-code))
  ⊎
  NonzeroNat
    (evalPRF
      (PRRel.characteristic right)
      (proofCodeArgs proof-code formula-code))
orProofRule-nonzero-sound left right {proof-code} {formula-code} holds
  rewrite orF-correct
            (evalPRF
              (PRRel.characteristic left)
              (proofCodeArgs proof-code formula-code))
            (evalPRF
              (PRRel.characteristic right)
              (proofCodeArgs proof-code formula-code)) =
  or-output-nonzero-sound
    (evalPRF
      (PRRel.characteristic left)
      (proofCodeArgs proof-code formula-code))
    (evalPRF
      (PRRel.characteristic right)
      (proofCodeArgs proof-code formula-code))
    (zero ,Σ holds)

orProofRule-nonzero-output-sound :
  (left right : PRRel (suc (suc zero))) →
  {proof-code formula-code : ℕ} →
  NonzeroNat
    (evalPRF
      (PRRel.characteristic (orProofRulePR left right))
      (proofCodeArgs proof-code formula-code)) →
  NonzeroNat
    (evalPRF
      (PRRel.characteristic left)
      (proofCodeArgs proof-code formula-code))
  ⊎
  NonzeroNat
    (evalPRF
      (PRRel.characteristic right)
      (proofCodeArgs proof-code formula-code))
orProofRule-nonzero-output-sound left right {proof-code} {formula-code} nonzero
  rewrite orF-correct
            (evalPRF
              (PRRel.characteristic left)
              (proofCodeArgs proof-code formula-code))
            (evalPRF
              (PRRel.characteristic right)
              (proofCodeArgs proof-code formula-code)) =
  or-output-nonzero-sound
    (evalPRF
      (PRRel.characteristic left)
      (proofCodeArgs proof-code formula-code))
    (evalPRF
      (PRRel.characteristic right)
      (proofCodeArgs proof-code formula-code))
    nonzero

orProofRulePR-represented :
  (left right : PRRel (suc (suc zero))) →
  PARepresentsRelation (orProofRulePR left right)
orProofRulePR-represented left right =
  prrel-represented (orProofRulePR left right)
