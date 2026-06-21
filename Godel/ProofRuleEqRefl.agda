{-# OPTIONS --safe #-}

module Godel.ProofRuleEqRefl where

open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.CanonicalCoding
  using
    ( canonicalCodeTerm
    ; canonicalNatFormula
    ; encodeCode
    ; node
    )
open import Godel.PrimitiveRecursive
open import Godel.PRRepresentabilityFinal
  using (PARepresentsRelation; prrel-represented)
open import Godel.ProofCanonicalChecker
  using
    ( checkPAProofCode
    ; decodeCanonicalTerm-roundTrip
    )
open import Godel.ProofCheckingBranch
open import Godel.ProofCheckingPR
  using (proofCodeArgs)
open import Godel.ProofCheckingPRTargets
  using (DecodedExecutableProofCodeNat)
open import Godel.ProofRuleFixedProofOr
  using (NonzeroNat)

-- Semantic target for proof-rule tag 8:
--
--   eq-refl-rule : t = t

EqReflRuleNat : ℕ → ℕ → Set
EqReflRuleNat proof-code formula-code =
  Σ Term
    (λ t →
      (proof-code ≡
       encodeCode
        (node 8
          (canonicalCodeTerm t ∷
           []))) ×
      (formula-code ≡ canonicalNatFormula (t ≈ t)))

eqReflRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  EqReflRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
eqReflRuleNat-to-decoded
  (t ,Σ (proof-eq ,× formula-eq)) =
  node 8
    (canonicalCodeTerm t ∷
     [])
  ,Σ
  ((t ≈ t) ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 8
          (canonicalCodeTerm t ∷
           []))
      ≡
      just (t ≈ t)
    check-eq
      rewrite decodeCanonicalTerm-roundTrip t =
      refl

record ProofRuleEqReflPR : Set₁ where
  field
    eqRefl-pr :
      PRRel (suc (suc zero))

    eqRefl-complete :
      {proof-code formula-code : ℕ} →
      EqReflRuleNat proof-code formula-code →
      PRRel-holds eqRefl-pr (proofCodeArgs proof-code formula-code)

    eqRefl-sound :
      {proof-code formula-code : ℕ} →
      PRRel-holds eqRefl-pr (proofCodeArgs proof-code formula-code) →
      EqReflRuleNat proof-code formula-code

proofRuleEqReflPR-to-decoded :
  (D : ProofRuleEqReflPR) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (ProofRuleEqReflPR.eqRefl-pr D)
    (proofCodeArgs proof-code formula-code) →
  DecodedExecutableProofCodeNat proof-code formula-code
proofRuleEqReflPR-to-decoded D holds =
  eqReflRuleNat-to-decoded
    (ProofRuleEqReflPR.eqRefl-sound D holds)

proofRuleEqReflPR-represented :
  (D : ProofRuleEqReflPR) →
  PARepresentsRelation (ProofRuleEqReflPR.eqRefl-pr D)
proofRuleEqReflPR-represented D =
  prrel-represented (ProofRuleEqReflPR.eqRefl-pr D)

record ProofRuleEqReflCheckingBranchData : Set₁ where
  field
    eqRefl-pr-data :
      ProofRuleEqReflPR

    eqRefl-nonzero-sound :
      {proof-code formula-code : ℕ} →
      NonzeroNat
        (evalPRF
          (PRRel.characteristic
            (ProofRuleEqReflPR.eqRefl-pr eqRefl-pr-data))
          (proofCodeArgs proof-code formula-code)) →
      EqReflRuleNat proof-code formula-code

proofRuleEqReflCheckingBranch :
  ProofRuleEqReflCheckingBranchData →
  ProofCheckingBranchPR
proofRuleEqReflCheckingBranch D = record
  { branch-pr =
      ProofRuleEqReflPR.eqRefl-pr
        (ProofRuleEqReflCheckingBranchData.eqRefl-pr-data D)
  ; branch-sound-decoded =
      proofRuleEqReflPR-to-decoded
        (ProofRuleEqReflCheckingBranchData.eqRefl-pr-data D)
  ; branch-nonzero-sound-decoded =
      λ nonzero →
        eqReflRuleNat-to-decoded
          (ProofRuleEqReflCheckingBranchData.eqRefl-nonzero-sound
            D
            nonzero)
  }

proofRuleEqReflTargetedBranch :
  ProofRuleEqReflCheckingBranchData →
  TargetedProofCheckingBranchPR EqReflRuleNat
proofRuleEqReflTargetedBranch D = record
  { branch =
      proofRuleEqReflCheckingBranch D
  ; branch-complete-target =
      ProofRuleEqReflPR.eqRefl-complete
        (ProofRuleEqReflCheckingBranchData.eqRefl-pr-data D)
  }
