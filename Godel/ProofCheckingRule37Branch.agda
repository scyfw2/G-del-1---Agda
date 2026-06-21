{-# OPTIONS --safe #-}

module Godel.ProofCheckingRule37Branch where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.ProofCheckingPR using (proofCodeArgs)
open import Godel.ProofCheckingBranch
open import Godel.ProofRuleFixedProofOr using (NonzeroNat)
open import Godel.ProofRuleTargets
  using
    ( ClosedNumeralNeqRuleNat
    ; ProofRule37PR
    ; proofRule37PR-to-decoded
    )

-- Rule 37 already has a rule-level PR target.  To use it inside the final
-- proofCodePAPR OR tree we need one additional fact: nonzero hits are sound.
-- This is exactly the shape exposed by the bounded-search branches, and it is
-- stronger than the base ProofRule37PR record's eval=1 soundness.

record ProofRule37CheckingBranchData : Set₁ where
  field
    rule37-pr-data :
      ProofRule37PR

    rule37-nonzero-sound :
      {proof-code formula-code : ℕ} →
      NonzeroNat
        (evalPRF
          (PRRel.characteristic
            (ProofRule37PR.rule37-pr rule37-pr-data))
          (proofCodeArgs proof-code formula-code)) →
      ClosedNumeralNeqRuleNat proof-code formula-code

proofRule37CheckingBranch :
  ProofRule37CheckingBranchData →
  ProofCheckingBranchPR
proofRule37CheckingBranch D = record
  { branch-pr =
      ProofRule37PR.rule37-pr
        (ProofRule37CheckingBranchData.rule37-pr-data D)
  ; branch-sound-decoded =
      proofRule37PR-to-decoded
        (ProofRule37CheckingBranchData.rule37-pr-data D)
  ; branch-nonzero-sound-decoded =
      λ {proof-code} {formula-code} nonzero →
        proofRule37PR-to-decoded
          (ProofRule37CheckingBranchData.rule37-pr-data D)
          (nonzero-to-rule37-holds nonzero)
  }
  where
    nonzero-to-rule37-holds :
      {proof-code formula-code : ℕ} →
      NonzeroNat
        (evalPRF
          (PRRel.characteristic
            (ProofRule37PR.rule37-pr
              (ProofRule37CheckingBranchData.rule37-pr-data D)))
          (proofCodeArgs proof-code formula-code)) →
      PRRel-holds
        (ProofRule37PR.rule37-pr
          (ProofRule37CheckingBranchData.rule37-pr-data D))
        (proofCodeArgs proof-code formula-code)
    nonzero-to-rule37-holds {proof-code} {formula-code} nonzero =
      ProofRule37PR.rule37-complete
        (ProofRule37CheckingBranchData.rule37-pr-data D)
        (ProofRule37CheckingBranchData.rule37-nonzero-sound D nonzero)

proofRule37TargetedBranch :
  ProofRule37CheckingBranchData →
  TargetedProofCheckingBranchPR ClosedNumeralNeqRuleNat
proofRule37TargetedBranch D = record
  { branch =
      proofRule37CheckingBranch D
  ; branch-complete-target =
      ProofRule37PR.rule37-complete
        (ProofRule37CheckingBranchData.rule37-pr-data D)
  }
