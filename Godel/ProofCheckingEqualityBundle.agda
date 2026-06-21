{-# OPTIONS --safe #-}

module Godel.ProofCheckingEqualityBundle where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.ProofCheckingBranch
open import Godel.ProofRuleEqRefl
  using
    ( EqReflRuleNat
    ; ProofRuleEqReflCheckingBranchData
    ; proofRuleEqReflTargetedBranch
    )
open import Godel.ProofRuleEqualitySchemas
  using
    ( EqSymRuleNat
    ; EqTransRuleNat
    ; SucCongRuleNat
    ; AddCongRuleNat
    ; MulCongRuleNat
    ; ProofRuleEqSymCheckingBranchData
    ; ProofRuleEqTransCheckingBranchData
    ; ProofRuleSucCongCheckingBranchData
    ; ProofRuleAddCongCheckingBranchData
    ; ProofRuleMulCongCheckingBranchData
    ; proofRuleEqSymTargetedBranch
    ; proofRuleEqTransTargetedBranch
    ; proofRuleSucCongTargetedBranch
    ; proofRuleAddCongTargetedBranch
    ; proofRuleMulCongTargetedBranch
    )

-- Parameterized OR bundle for equality-related proof-rule targets:
--
--   tag 8  eq-refl
--   tag 9  eq-sym
--   tag 10 eq-trans
--   tag 11 suc-cong
--   tag 12 add-cong
--   tag 13 mul-cong
--
-- The bundle only composes already-supplied targeted branches.  It does not
-- construct the concrete numeric PR checkers for those tags.

EqualityTarget₂ :
  (Left Right : ℕ → ℕ → Set) →
  ℕ →
  ℕ →
  Set
EqualityTarget₂ Left Right =
  OrProofCheckingTarget Left Right

EqualityTarget₄ :
  (A B C D : ℕ → ℕ → Set) →
  ℕ →
  ℕ →
  Set
EqualityTarget₄ A B C D =
  OrProofCheckingTarget
    (EqualityTarget₂ A B)
    (EqualityTarget₂ C D)

EqualityTarget₆ : ℕ → ℕ → Set
EqualityTarget₆ =
  OrProofCheckingTarget
    (EqualityTarget₄
      EqReflRuleNat
      EqSymRuleNat
      EqTransRuleNat
      SucCongRuleNat)
    (EqualityTarget₂
      AddCongRuleNat
      MulCongRuleNat)

record ProofCheckingEqualityBranchesData : Set₁ where
  field
    eq-refl :
      ProofRuleEqReflCheckingBranchData

    eq-sym :
      ProofRuleEqSymCheckingBranchData

    eq-trans :
      ProofRuleEqTransCheckingBranchData

    suc-cong :
      ProofRuleSucCongCheckingBranchData

    add-cong :
      ProofRuleAddCongCheckingBranchData

    mul-cong :
      ProofRuleMulCongCheckingBranchData

proofCheckingEqualityBranch₄ :
  ProofCheckingEqualityBranchesData →
  TargetedProofCheckingBranchPR
    (EqualityTarget₄
      EqReflRuleNat
      EqSymRuleNat
      EqTransRuleNat
      SucCongRuleNat)
proofCheckingEqualityBranch₄ D =
  orTargetedProofCheckingBranchPR
    (orTargetedProofCheckingBranchPR
      (proofRuleEqReflTargetedBranch
        (ProofCheckingEqualityBranchesData.eq-refl D))
      (proofRuleEqSymTargetedBranch
        (ProofCheckingEqualityBranchesData.eq-sym D)))
    (orTargetedProofCheckingBranchPR
      (proofRuleEqTransTargetedBranch
        (ProofCheckingEqualityBranchesData.eq-trans D))
      (proofRuleSucCongTargetedBranch
        (ProofCheckingEqualityBranchesData.suc-cong D)))

proofCheckingEqualityBranch₂ :
  ProofCheckingEqualityBranchesData →
  TargetedProofCheckingBranchPR
    (EqualityTarget₂ AddCongRuleNat MulCongRuleNat)
proofCheckingEqualityBranch₂ D =
  orTargetedProofCheckingBranchPR
    (proofRuleAddCongTargetedBranch
      (ProofCheckingEqualityBranchesData.add-cong D))
    (proofRuleMulCongTargetedBranch
      (ProofCheckingEqualityBranchesData.mul-cong D))

proofCheckingEqualityBranch₆ :
  ProofCheckingEqualityBranchesData →
  TargetedProofCheckingBranchPR EqualityTarget₆
proofCheckingEqualityBranch₆ D =
  orTargetedProofCheckingBranchPR
    (proofCheckingEqualityBranch₄ D)
    (proofCheckingEqualityBranch₂ D)
