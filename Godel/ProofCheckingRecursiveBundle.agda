{-# OPTIONS --safe #-}

module Godel.ProofCheckingRecursiveBundle where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.ProofCheckingBranch
open import Godel.ProofRuleRecursiveSchemas
  using
    ( ModusPonensRuleNat
    ; ForallGeneralizeRuleNat
    ; ProofRuleModusPonensCheckingBranchData
    ; ProofRuleForallGeneralizeCheckingBranchData
    ; proofRuleModusPonensTargetedBranch
    ; proofRuleForallGeneralizeTargetedBranch
    )

-- Parameterized OR bundle for proof-rule targets whose executable checker
-- calls the proof checker recursively:
--
--   tag 4 modus-ponens
--   tag 5 forall-generalize

RecursiveTarget₂ : ℕ → ℕ → Set
RecursiveTarget₂ =
  OrProofCheckingTarget
    ModusPonensRuleNat
    ForallGeneralizeRuleNat

record ProofCheckingRecursiveBranchesData : Set₁ where
  field
    modus-ponens :
      ProofRuleModusPonensCheckingBranchData

    forall-generalize :
      ProofRuleForallGeneralizeCheckingBranchData

proofCheckingRecursiveBranch₂ :
  ProofCheckingRecursiveBranchesData →
  TargetedProofCheckingBranchPR RecursiveTarget₂
proofCheckingRecursiveBranch₂ D =
  orTargetedProofCheckingBranchPR
    (proofRuleModusPonensTargetedBranch
      (ProofCheckingRecursiveBranchesData.modus-ponens D))
    (proofRuleForallGeneralizeTargetedBranch
      (ProofCheckingRecursiveBranchesData.forall-generalize D))
