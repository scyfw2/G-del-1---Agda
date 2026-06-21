{-# OPTIONS --safe #-}

module Godel.ProofCheckingQuantifierBundle where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.ProofCheckingBranch
open import Godel.ProofRuleQuantifierSchemas
  using
    ( ExistsElimRuleNat
    ; ExistsPrefixIntroduceRuleNat
    ; ExistsPrefixBinaryLiftRuleNat
    ; ExistsPrefixPremiseMapRuleNat
    ; PremiseChangeRuleNat
    ; ProofRuleExistsElimCheckingBranchData
    ; ProofRuleExistsPrefixIntroduceCheckingBranchData
    ; ProofRuleExistsPrefixBinaryLiftCheckingBranchData
    ; ProofRuleExistsPrefixPremiseMapCheckingBranchData
    ; ProofRulePremiseChangeCheckingBranchData
    ; proofRuleExistsElimTargetedBranch
    ; proofRuleExistsPrefixIntroduceTargetedBranch
    ; proofRuleExistsPrefixBinaryLiftTargetedBranch
    ; proofRuleExistsPrefixPremiseMapTargetedBranch
    ; proofRulePremiseChangeTargetedBranch
    )

-- Parameterized OR bundle for tags 14-18:
--
--   tag 14 exists-eliminate
--   tag 15 exists-prefix-introduce-any
--   tag 16 exists-prefix-binary-lift
--   tag 17 exists-prefix-premise-map-any
--   tag 18 premise-change-any

QuantifierTarget₂ :
  (Left Right : ℕ → ℕ → Set) →
  ℕ →
  ℕ →
  Set
QuantifierTarget₂ Left Right =
  OrProofCheckingTarget Left Right

QuantifierTarget₄ :
  (A B C D : ℕ → ℕ → Set) →
  ℕ →
  ℕ →
  Set
QuantifierTarget₄ A B C D =
  OrProofCheckingTarget
    (QuantifierTarget₂ A B)
    (QuantifierTarget₂ C D)

QuantifierTarget₅ : ℕ → ℕ → Set
QuantifierTarget₅ =
  OrProofCheckingTarget
    (QuantifierTarget₄
      ExistsElimRuleNat
      ExistsPrefixIntroduceRuleNat
      ExistsPrefixBinaryLiftRuleNat
      ExistsPrefixPremiseMapRuleNat)
    PremiseChangeRuleNat

record ProofCheckingQuantifierBranchesData : Set₁ where
  field
    exists-elim :
      ProofRuleExistsElimCheckingBranchData

    exists-prefix-intro :
      ProofRuleExistsPrefixIntroduceCheckingBranchData

    exists-prefix-binary-lift :
      ProofRuleExistsPrefixBinaryLiftCheckingBranchData

    exists-prefix-premise-map :
      ProofRuleExistsPrefixPremiseMapCheckingBranchData

    premise-change :
      ProofRulePremiseChangeCheckingBranchData

proofCheckingQuantifierBranch₄ :
  ProofCheckingQuantifierBranchesData →
  TargetedProofCheckingBranchPR
    (QuantifierTarget₄
      ExistsElimRuleNat
      ExistsPrefixIntroduceRuleNat
      ExistsPrefixBinaryLiftRuleNat
      ExistsPrefixPremiseMapRuleNat)
proofCheckingQuantifierBranch₄ D =
  orTargetedProofCheckingBranchPR
    (orTargetedProofCheckingBranchPR
      (proofRuleExistsElimTargetedBranch
        (ProofCheckingQuantifierBranchesData.exists-elim D))
      (proofRuleExistsPrefixIntroduceTargetedBranch
        (ProofCheckingQuantifierBranchesData.exists-prefix-intro D)))
    (orTargetedProofCheckingBranchPR
      (proofRuleExistsPrefixBinaryLiftTargetedBranch
        (ProofCheckingQuantifierBranchesData.exists-prefix-binary-lift D))
      (proofRuleExistsPrefixPremiseMapTargetedBranch
        (ProofCheckingQuantifierBranchesData.exists-prefix-premise-map D)))

proofCheckingQuantifierBranch₅ :
  ProofCheckingQuantifierBranchesData →
  TargetedProofCheckingBranchPR QuantifierTarget₅
proofCheckingQuantifierBranch₅ D =
  orTargetedProofCheckingBranchPR
    (proofCheckingQuantifierBranch₄ D)
    (proofRulePremiseChangeTargetedBranch
      (ProofCheckingQuantifierBranchesData.premise-change D))
