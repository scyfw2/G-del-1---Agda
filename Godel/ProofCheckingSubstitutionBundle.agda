{-# OPTIONS --safe #-}

module Godel.ProofCheckingSubstitutionBundle where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.ProofCheckingBranch
open import Godel.ProofRuleSubstitutionSchemas
  using
    ( ForallEliminateRuleNat
    ; ExistsIntroduceRuleNat
    ; ProofRuleForallEliminateCheckingBranchData
    ; ProofRuleExistsIntroduceCheckingBranchData
    ; proofRuleForallEliminateTargetedBranch
    ; proofRuleExistsIntroduceTargetedBranch
    )

-- Parameterized OR bundle for substitution-style proof-rule targets:
--
--   tag 6 forall-eliminate
--   tag 7 exists-introduce

SubstitutionTarget₂ : ℕ → ℕ → Set
SubstitutionTarget₂ =
  OrProofCheckingTarget
    ForallEliminateRuleNat
    ExistsIntroduceRuleNat

record ProofCheckingSubstitutionBranchesData : Set₁ where
  field
    forall-eliminate :
      ProofRuleForallEliminateCheckingBranchData

    exists-introduce :
      ProofRuleExistsIntroduceCheckingBranchData

proofCheckingSubstitutionBranch₂ :
  ProofCheckingSubstitutionBranchesData →
  TargetedProofCheckingBranchPR SubstitutionTarget₂
proofCheckingSubstitutionBranch₂ D =
  orTargetedProofCheckingBranchPR
    (proofRuleForallEliminateTargetedBranch
      (ProofCheckingSubstitutionBranchesData.forall-eliminate D))
    (proofRuleExistsIntroduceTargetedBranch
      (ProofCheckingSubstitutionBranchesData.exists-introduce D))
