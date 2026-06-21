{-# OPTIONS --safe #-}

module Godel.ProofRuleExcludedMiddle where

open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.CanonicalCoding
  using
    ( canonicalCodeFormula
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
    ; decodeCanonicalFormula-roundTrip
    )
open import Godel.ProofCheckingPR
  using (proofCodeArgs)
open import Godel.ProofCheckingPRTargets
  using (DecodedExecutableProofCodeNat)
open import Godel.ProofCheckingBranch
open import Godel.ProofRuleFixedProofOr
  using (NonzeroNat)

-- Semantic target for proof-rule tag 3:
--
--   excluded-middle : A \/ not A

ExcludedMiddleRuleNat : ℕ → ℕ → Set
ExcludedMiddleRuleNat proof-code formula-code =
  Σ Formula
    (λ A →
      (proof-code ≡
       encodeCode
        (node 3
          (canonicalCodeFormula A ∷
           []))) ×
      (formula-code ≡ canonicalNatFormula (A ∨ (¬ᶠ A))))

excludedMiddleRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  ExcludedMiddleRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
excludedMiddleRuleNat-to-decoded
  (A ,Σ (proof-eq ,× formula-eq)) =
  node 3
    (canonicalCodeFormula A ∷
     [])
  ,Σ
  ((A ∨ (¬ᶠ A)) ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 3
          (canonicalCodeFormula A ∷
           []))
      ≡
      just (A ∨ (¬ᶠ A))
    check-eq
      rewrite decodeCanonicalFormula-roundTrip A =
      refl

record ProofRuleExcludedMiddlePR : Set₁ where
  field
    excludedMiddle-pr :
      PRRel (suc (suc zero))

    excludedMiddle-complete :
      {proof-code formula-code : ℕ} →
      ExcludedMiddleRuleNat proof-code formula-code →
      PRRel-holds excludedMiddle-pr (proofCodeArgs proof-code formula-code)

    excludedMiddle-sound :
      {proof-code formula-code : ℕ} →
      PRRel-holds excludedMiddle-pr (proofCodeArgs proof-code formula-code) →
      ExcludedMiddleRuleNat proof-code formula-code

proofRuleExcludedMiddlePR-to-decoded :
  (D : ProofRuleExcludedMiddlePR) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (ProofRuleExcludedMiddlePR.excludedMiddle-pr D)
    (proofCodeArgs proof-code formula-code) →
  DecodedExecutableProofCodeNat proof-code formula-code
proofRuleExcludedMiddlePR-to-decoded D holds =
  excludedMiddleRuleNat-to-decoded
    (ProofRuleExcludedMiddlePR.excludedMiddle-sound D holds)

proofRuleExcludedMiddlePR-represented :
  (D : ProofRuleExcludedMiddlePR) →
  PARepresentsRelation (ProofRuleExcludedMiddlePR.excludedMiddle-pr D)
proofRuleExcludedMiddlePR-represented D =
  prrel-represented (ProofRuleExcludedMiddlePR.excludedMiddle-pr D)

record ProofRuleExcludedMiddleCheckingBranchData : Set₁ where
  field
    excludedMiddle-pr-data :
      ProofRuleExcludedMiddlePR

    excludedMiddle-nonzero-sound :
      {proof-code formula-code : ℕ} →
      NonzeroNat
        (evalPRF
          (PRRel.characteristic
            (ProofRuleExcludedMiddlePR.excludedMiddle-pr
              excludedMiddle-pr-data))
          (proofCodeArgs proof-code formula-code)) →
      ExcludedMiddleRuleNat proof-code formula-code

proofRuleExcludedMiddleCheckingBranch :
  ProofRuleExcludedMiddleCheckingBranchData →
  ProofCheckingBranchPR
proofRuleExcludedMiddleCheckingBranch D = record
  { branch-pr =
      ProofRuleExcludedMiddlePR.excludedMiddle-pr
        (ProofRuleExcludedMiddleCheckingBranchData.excludedMiddle-pr-data D)
  ; branch-sound-decoded =
      proofRuleExcludedMiddlePR-to-decoded
        (ProofRuleExcludedMiddleCheckingBranchData.excludedMiddle-pr-data D)
  ; branch-nonzero-sound-decoded =
      λ nonzero →
        excludedMiddleRuleNat-to-decoded
          (ProofRuleExcludedMiddleCheckingBranchData.excludedMiddle-nonzero-sound
            D
            nonzero)
  }

proofRuleExcludedMiddleTargetedBranch :
  ProofRuleExcludedMiddleCheckingBranchData →
  TargetedProofCheckingBranchPR ExcludedMiddleRuleNat
proofRuleExcludedMiddleTargetedBranch D = record
  { branch =
      proofRuleExcludedMiddleCheckingBranch D
  ; branch-complete-target =
      ProofRuleExcludedMiddlePR.excludedMiddle-complete
        (ProofRuleExcludedMiddleCheckingBranchData.excludedMiddle-pr-data D)
  }
