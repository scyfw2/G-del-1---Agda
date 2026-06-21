{-# OPTIONS --safe #-}

module Godel.ProofCheckingDerivedLogicalBundle where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.ProofCheckingBranch
open import Godel.ProofRuleDerivedLogicalSchemas
  using
    ( AndLeftImpRuleNat
    ; AndRightImpRuleNat
    ; AndLeftImp1RuleNat
    ; AndRightImp1RuleNat
    ; ImpAndIntro2RuleNat
    ; AndBothMapRuleNat
    ; AndLeftMapRuleNat
    ; PremiseAndBothMapRuleNat
    ; PremiseAndLeftMapRuleNat
    ; BodyUniqueComposeRuleNat
    ; ContradictionToNegRuleNat
    ; ProofRuleAndLeftImpCheckingBranchData
    ; ProofRuleAndRightImpCheckingBranchData
    ; ProofRuleAndLeftImp1CheckingBranchData
    ; ProofRuleAndRightImp1CheckingBranchData
    ; ProofRuleImpAndIntro2CheckingBranchData
    ; ProofRuleAndBothMapCheckingBranchData
    ; ProofRuleAndLeftMapCheckingBranchData
    ; ProofRulePremiseAndBothMapCheckingBranchData
    ; ProofRulePremiseAndLeftMapCheckingBranchData
    ; ProofRuleBodyUniqueComposeCheckingBranchData
    ; ProofRuleContradictionToNegCheckingBranchData
    ; proofRuleAndLeftImpTargetedBranch
    ; proofRuleAndRightImpTargetedBranch
    ; proofRuleAndLeftImp1TargetedBranch
    ; proofRuleAndRightImp1TargetedBranch
    ; proofRuleImpAndIntro2TargetedBranch
    ; proofRuleAndBothMapTargetedBranch
    ; proofRuleAndLeftMapTargetedBranch
    ; proofRulePremiseAndBothMapTargetedBranch
    ; proofRulePremiseAndLeftMapTargetedBranch
    ; proofRuleBodyUniqueComposeTargetedBranch
    ; proofRuleContradictionToNegTargetedBranch
    )

-- Parameterized OR bundle for derived logical helper proof-rule targets:
--
--   tags 25-34 and tag 38

DerivedLogicalTarget₂ :
  (Left Right : ℕ → ℕ → Set) →
  ℕ →
  ℕ →
  Set
DerivedLogicalTarget₂ Left Right =
  OrProofCheckingTarget Left Right

DerivedLogicalTarget₃ :
  (A B C : ℕ → ℕ → Set) →
  ℕ →
  ℕ →
  Set
DerivedLogicalTarget₃ A B C =
  OrProofCheckingTarget
    A
    (OrProofCheckingTarget B C)

DerivedLogicalTarget₅ : ℕ → ℕ → Set
DerivedLogicalTarget₅ =
  OrProofCheckingTarget
    (DerivedLogicalTarget₂
      AndLeftImpRuleNat
      AndRightImpRuleNat)
    (DerivedLogicalTarget₃
      AndLeftImp1RuleNat
      AndRightImp1RuleNat
      ImpAndIntro2RuleNat)

DerivedLogicalTarget₆ : ℕ → ℕ → Set
DerivedLogicalTarget₆ =
  OrProofCheckingTarget
    (DerivedLogicalTarget₃
      AndBothMapRuleNat
      AndLeftMapRuleNat
      PremiseAndBothMapRuleNat)
    (DerivedLogicalTarget₃
      PremiseAndLeftMapRuleNat
      BodyUniqueComposeRuleNat
      ContradictionToNegRuleNat)

DerivedLogicalTarget₁₁ : ℕ → ℕ → Set
DerivedLogicalTarget₁₁ =
  OrProofCheckingTarget
    DerivedLogicalTarget₅
    DerivedLogicalTarget₆

record ProofCheckingDerivedLogicalBranchesData : Set₁ where
  field
    and-left-imp :
      ProofRuleAndLeftImpCheckingBranchData

    and-right-imp :
      ProofRuleAndRightImpCheckingBranchData

    and-left-imp1 :
      ProofRuleAndLeftImp1CheckingBranchData

    and-right-imp1 :
      ProofRuleAndRightImp1CheckingBranchData

    imp-and-intro2 :
      ProofRuleImpAndIntro2CheckingBranchData

    and-both-map :
      ProofRuleAndBothMapCheckingBranchData

    and-left-map :
      ProofRuleAndLeftMapCheckingBranchData

    premise-and-both-map :
      ProofRulePremiseAndBothMapCheckingBranchData

    premise-and-left-map :
      ProofRulePremiseAndLeftMapCheckingBranchData

    body-unique-compose :
      ProofRuleBodyUniqueComposeCheckingBranchData

    contradiction-to-neg :
      ProofRuleContradictionToNegCheckingBranchData

proofCheckingDerivedLogicalBranch₂a :
  ProofCheckingDerivedLogicalBranchesData →
  TargetedProofCheckingBranchPR
    (DerivedLogicalTarget₂
      AndLeftImpRuleNat
      AndRightImpRuleNat)
proofCheckingDerivedLogicalBranch₂a D =
  orTargetedProofCheckingBranchPR
    (proofRuleAndLeftImpTargetedBranch
      (ProofCheckingDerivedLogicalBranchesData.and-left-imp D))
    (proofRuleAndRightImpTargetedBranch
      (ProofCheckingDerivedLogicalBranchesData.and-right-imp D))

proofCheckingDerivedLogicalBranch₃a :
  ProofCheckingDerivedLogicalBranchesData →
  TargetedProofCheckingBranchPR
    (DerivedLogicalTarget₃
      AndLeftImp1RuleNat
      AndRightImp1RuleNat
      ImpAndIntro2RuleNat)
proofCheckingDerivedLogicalBranch₃a D =
  orTargetedProofCheckingBranchPR
    (proofRuleAndLeftImp1TargetedBranch
      (ProofCheckingDerivedLogicalBranchesData.and-left-imp1 D))
    (orTargetedProofCheckingBranchPR
      (proofRuleAndRightImp1TargetedBranch
        (ProofCheckingDerivedLogicalBranchesData.and-right-imp1 D))
      (proofRuleImpAndIntro2TargetedBranch
        (ProofCheckingDerivedLogicalBranchesData.imp-and-intro2 D)))

proofCheckingDerivedLogicalBranch₅ :
  ProofCheckingDerivedLogicalBranchesData →
  TargetedProofCheckingBranchPR DerivedLogicalTarget₅
proofCheckingDerivedLogicalBranch₅ D =
  orTargetedProofCheckingBranchPR
    (proofCheckingDerivedLogicalBranch₂a D)
    (proofCheckingDerivedLogicalBranch₃a D)

proofCheckingDerivedLogicalBranch₃b :
  ProofCheckingDerivedLogicalBranchesData →
  TargetedProofCheckingBranchPR
    (DerivedLogicalTarget₃
      AndBothMapRuleNat
      AndLeftMapRuleNat
      PremiseAndBothMapRuleNat)
proofCheckingDerivedLogicalBranch₃b D =
  orTargetedProofCheckingBranchPR
    (proofRuleAndBothMapTargetedBranch
      (ProofCheckingDerivedLogicalBranchesData.and-both-map D))
    (orTargetedProofCheckingBranchPR
      (proofRuleAndLeftMapTargetedBranch
        (ProofCheckingDerivedLogicalBranchesData.and-left-map D))
      (proofRulePremiseAndBothMapTargetedBranch
        (ProofCheckingDerivedLogicalBranchesData.premise-and-both-map D)))

proofCheckingDerivedLogicalBranch₃c :
  ProofCheckingDerivedLogicalBranchesData →
  TargetedProofCheckingBranchPR
    (DerivedLogicalTarget₃
      PremiseAndLeftMapRuleNat
      BodyUniqueComposeRuleNat
      ContradictionToNegRuleNat)
proofCheckingDerivedLogicalBranch₃c D =
  orTargetedProofCheckingBranchPR
    (proofRulePremiseAndLeftMapTargetedBranch
      (ProofCheckingDerivedLogicalBranchesData.premise-and-left-map D))
    (orTargetedProofCheckingBranchPR
      (proofRuleBodyUniqueComposeTargetedBranch
        (ProofCheckingDerivedLogicalBranchesData.body-unique-compose D))
      (proofRuleContradictionToNegTargetedBranch
        (ProofCheckingDerivedLogicalBranchesData.contradiction-to-neg D)))

proofCheckingDerivedLogicalBranch₆ :
  ProofCheckingDerivedLogicalBranchesData →
  TargetedProofCheckingBranchPR DerivedLogicalTarget₆
proofCheckingDerivedLogicalBranch₆ D =
  orTargetedProofCheckingBranchPR
    (proofCheckingDerivedLogicalBranch₃b D)
    (proofCheckingDerivedLogicalBranch₃c D)

proofCheckingDerivedLogicalBranch₁₁ :
  ProofCheckingDerivedLogicalBranchesData →
  TargetedProofCheckingBranchPR DerivedLogicalTarget₁₁
proofCheckingDerivedLogicalBranch₁₁ D =
  orTargetedProofCheckingBranchPR
    (proofCheckingDerivedLogicalBranch₅ D)
    (proofCheckingDerivedLogicalBranch₆ D)
