{-# OPTIONS --safe #-}

module Godel.ProofCheckingLogicalBundle where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.ProofCheckingBranch
open import Godel.ProofRuleLogicalConnectives
  using
    ( AndIntroRuleNat
    ; AndElimLeftRuleNat
    ; AndElimRightRuleNat
    ; OrIntroLeftRuleNat
    ; OrIntroRightRuleNat
    ; ProofRuleAndIntroCheckingBranchData
    ; ProofRuleAndElimLeftCheckingBranchData
    ; ProofRuleAndElimRightCheckingBranchData
    ; ProofRuleOrIntroLeftCheckingBranchData
    ; ProofRuleOrIntroRightCheckingBranchData
    ; proofRuleAndIntroTargetedBranch
    ; proofRuleAndElimLeftTargetedBranch
    ; proofRuleAndElimRightTargetedBranch
    ; proofRuleOrIntroLeftTargetedBranch
    ; proofRuleOrIntroRightTargetedBranch
    )

-- Parameterized OR bundle for logical connective proof-rule targets:
--
--   tag 19 and-introduce
--   tag 20 and-elim-left
--   tag 21 and-elim-right
--   tag 22 or-intro-left
--   tag 23 or-intro-right

LogicalTarget₂ :
  (Left Right : ℕ → ℕ → Set) →
  ℕ →
  ℕ →
  Set
LogicalTarget₂ Left Right =
  OrProofCheckingTarget Left Right

LogicalTarget₄ :
  (A B C D : ℕ → ℕ → Set) →
  ℕ →
  ℕ →
  Set
LogicalTarget₄ A B C D =
  OrProofCheckingTarget
    (LogicalTarget₂ A B)
    (LogicalTarget₂ C D)

LogicalTarget₅ : ℕ → ℕ → Set
LogicalTarget₅ =
  OrProofCheckingTarget
    (LogicalTarget₄
      AndIntroRuleNat
      AndElimLeftRuleNat
      AndElimRightRuleNat
      OrIntroLeftRuleNat)
    OrIntroRightRuleNat

record ProofCheckingLogicalBranchesData : Set₁ where
  field
    and-intro :
      ProofRuleAndIntroCheckingBranchData

    and-elim-left :
      ProofRuleAndElimLeftCheckingBranchData

    and-elim-right :
      ProofRuleAndElimRightCheckingBranchData

    or-intro-left :
      ProofRuleOrIntroLeftCheckingBranchData

    or-intro-right :
      ProofRuleOrIntroRightCheckingBranchData

proofCheckingLogicalBranch₄ :
  ProofCheckingLogicalBranchesData →
  TargetedProofCheckingBranchPR
    (LogicalTarget₄
      AndIntroRuleNat
      AndElimLeftRuleNat
      AndElimRightRuleNat
      OrIntroLeftRuleNat)
proofCheckingLogicalBranch₄ D =
  orTargetedProofCheckingBranchPR
    (orTargetedProofCheckingBranchPR
      (proofRuleAndIntroTargetedBranch
        (ProofCheckingLogicalBranchesData.and-intro D))
      (proofRuleAndElimLeftTargetedBranch
        (ProofCheckingLogicalBranchesData.and-elim-left D)))
    (orTargetedProofCheckingBranchPR
      (proofRuleAndElimRightTargetedBranch
        (ProofCheckingLogicalBranchesData.and-elim-right D))
      (proofRuleOrIntroLeftTargetedBranch
        (ProofCheckingLogicalBranchesData.or-intro-left D)))

proofCheckingLogicalBranch₅ :
  ProofCheckingLogicalBranchesData →
  TargetedProofCheckingBranchPR LogicalTarget₅
proofCheckingLogicalBranch₅ D =
  orTargetedProofCheckingBranchPR
    (proofCheckingLogicalBranch₄ D)
    (proofRuleOrIntroRightTargetedBranch
      (ProofCheckingLogicalBranchesData.or-intro-right D))
