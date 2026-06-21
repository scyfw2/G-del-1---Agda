{-# OPTIONS --safe #-}

module Godel.ProofCheckingEqualitySubstitutionBundle where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.ProofCheckingBranch
open import Godel.ProofRuleEqualitySubstitution
  using
    ( EqUniqueValueRuleNat
    ; EqSubstRightRuleNat
    ; EqSubstSucRightRuleNat
    ; ProofRuleEqUniqueValueCheckingBranchData
    ; ProofRuleEqSubstRightCheckingBranchData
    ; ProofRuleEqSubstSucRightCheckingBranchData
    ; proofRuleEqUniqueValueTargetedBranch
    ; proofRuleEqSubstRightTargetedBranch
    ; proofRuleEqSubstSucRightTargetedBranch
    )

-- Parameterized OR bundle for equality substitution proof-rule targets:
--
--   tag 24 eq-unique-value
--   tag 35 eq-subst-right
--   tag 36 eq-subst-suc-right

EqualitySubstitutionTarget₃ : ℕ → ℕ → Set
EqualitySubstitutionTarget₃ =
  OrProofCheckingTarget
    EqUniqueValueRuleNat
    (OrProofCheckingTarget
      EqSubstRightRuleNat
      EqSubstSucRightRuleNat)

record ProofCheckingEqualitySubstitutionBranchesData : Set₁ where
  field
    eq-unique-value :
      ProofRuleEqUniqueValueCheckingBranchData

    eq-subst-right :
      ProofRuleEqSubstRightCheckingBranchData

    eq-subst-suc-right :
      ProofRuleEqSubstSucRightCheckingBranchData

proofCheckingEqualitySubstitutionBranch₃ :
  ProofCheckingEqualitySubstitutionBranchesData →
  TargetedProofCheckingBranchPR EqualitySubstitutionTarget₃
proofCheckingEqualitySubstitutionBranch₃ D =
  orTargetedProofCheckingBranchPR
    (proofRuleEqUniqueValueTargetedBranch
      (ProofCheckingEqualitySubstitutionBranchesData.eq-unique-value D))
    (orTargetedProofCheckingBranchPR
      (proofRuleEqSubstRightTargetedBranch
        (ProofCheckingEqualitySubstitutionBranchesData.eq-subst-right D))
      (proofRuleEqSubstSucRightTargetedBranch
        (ProofCheckingEqualitySubstitutionBranchesData.eq-subst-suc-right D)))
