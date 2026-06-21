{-# OPTIONS --safe #-}

module Godel.ProofCheckingTargetOverview where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.ProofCheckingBranch
open import Godel.ProofCheckingBranchBundle
  using
    ( ProofCheckingFixedAndRule37Data
    ; ProofCheckingFixedRule37HilbertKExcludedSTarget
    ; proofCheckingFixedRule37HilbertKExcludedSBranchFromParts
    )
open import Godel.ProofCheckingEqualityBundle
  using
    ( EqualityTarget₆
    ; ProofCheckingEqualityBranchesData
    ; proofCheckingEqualityBranch₆
    )
open import Godel.ProofCheckingEqualitySubstitutionBundle
  using
    ( EqualitySubstitutionTarget₃
    ; ProofCheckingEqualitySubstitutionBranchesData
    ; proofCheckingEqualitySubstitutionBranch₃
    )
open import Godel.ProofCheckingDerivedLogicalBundle
  using
    ( DerivedLogicalTarget₁₁
    ; ProofCheckingDerivedLogicalBranchesData
    ; proofCheckingDerivedLogicalBranch₁₁
    )
open import Godel.ProofCheckingLogicalBundle
  using
    ( LogicalTarget₅
    ; ProofCheckingLogicalBranchesData
    ; proofCheckingLogicalBranch₅
    )
open import Godel.ProofCheckingRecursiveBundle
  using
    ( RecursiveTarget₂
    ; ProofCheckingRecursiveBranchesData
    ; proofCheckingRecursiveBranch₂
    )
open import Godel.ProofCheckingPR using (ProofCheckingPR)
open import Godel.ProofCheckingPRTargets
  using
    ( DecodedExecutableProofCodeNat
    ; ProofCheckingPRDecodedNat
    ; proofCheckingPRDecodedNat-to-ProofCheckingPR
    )
open import Godel.ProofCheckingQuantifierBundle
  using
    ( QuantifierTarget₅
    ; ProofCheckingQuantifierBranchesData
    ; proofCheckingQuantifierBranch₅
    )
open import Godel.ProofCheckingSubstitutionBundle
  using
    ( SubstitutionTarget₂
    ; ProofCheckingSubstitutionBranchesData
    ; proofCheckingSubstitutionBranch₂
    )
open import Godel.ProofRuleExcludedMiddle
  using (ProofRuleExcludedMiddleCheckingBranchData)
open import Godel.ProofRuleHilbertK
  using (ProofRuleHilbertKCheckingBranchData)
open import Godel.ProofRuleHilbertS
  using (ProofRuleHilbertSCheckingBranchData)
open import Godel.ProofRuleFixedCodeLeaf
  using (FixedCodeLeafData)
open import Godel.ProofRulePAAxiomInduction
  using
    ( InductionAxiomRuleNat
    ; ProofRuleInductionAxiomCheckingBranchData
    ; proofRuleInductionAxiomTargetedBranch
    )

-- Current named target slice for the future proofCodePAPR checker.  This is
-- not the final checker yet; it records the branch families that have been
-- split out of checkPAProofCode so far:
--
--   fixed PA axiom leaves + rule 37
--   parameterized PA induction axiom
--   Hilbert K/S and excluded middle
--   recursive proof-tree rules
--   forall/exists substitution rules
--   equality/congruence rules
--   equality substitution/value rules
--   derived logical helper rules
--   quantifier/existential-prefix rules
--   logical connective rules

CurrentProofCheckingTarget :
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  ℕ →
  ℕ →
  Set
CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 =
  OrProofCheckingTarget
    (ProofCheckingFixedRule37HilbertKExcludedSTarget d0 d1 d2 d3 d4 d5)
    (OrProofCheckingTarget
      InductionAxiomRuleNat
      (OrProofCheckingTarget
        RecursiveTarget₂
        (OrProofCheckingTarget
          SubstitutionTarget₂
          (OrProofCheckingTarget
            EqualityTarget₆
            (OrProofCheckingTarget
              EqualitySubstitutionTarget₃
              (OrProofCheckingTarget
                DerivedLogicalTarget₁₁
                (OrProofCheckingTarget QuantifierTarget₅ LogicalTarget₅)))))))

record CurrentProofCheckingBranchesData : Set₁ where
  field
    fixed-rule37 :
      ProofCheckingFixedAndRule37Data

    hilbertK :
      ProofRuleHilbertKCheckingBranchData

    excluded-middle :
      ProofRuleExcludedMiddleCheckingBranchData

    hilbertS :
      ProofRuleHilbertSCheckingBranchData

    induction-axiom :
      ProofRuleInductionAxiomCheckingBranchData

    recursive :
      ProofCheckingRecursiveBranchesData

    substitution :
      ProofCheckingSubstitutionBranchesData

    equality :
      ProofCheckingEqualityBranchesData

    equality-substitution :
      ProofCheckingEqualitySubstitutionBranchesData

    derived-logical :
      ProofCheckingDerivedLogicalBranchesData

    quantifier :
      ProofCheckingQuantifierBranchesData

    logical :
      ProofCheckingLogicalBranchesData

currentProofCheckingBranch :
  (D : CurrentProofCheckingBranchesData) →
  TargetedProofCheckingBranchPR
    (CurrentProofCheckingTarget
      (ProofCheckingFixedAndRule37Data.leaf₀
        (CurrentProofCheckingBranchesData.fixed-rule37 D))
      (ProofCheckingFixedAndRule37Data.leaf₁
        (CurrentProofCheckingBranchesData.fixed-rule37 D))
      (ProofCheckingFixedAndRule37Data.leaf₂
        (CurrentProofCheckingBranchesData.fixed-rule37 D))
      (ProofCheckingFixedAndRule37Data.leaf₃
        (CurrentProofCheckingBranchesData.fixed-rule37 D))
      (ProofCheckingFixedAndRule37Data.leaf₄
        (CurrentProofCheckingBranchesData.fixed-rule37 D))
      (ProofCheckingFixedAndRule37Data.leaf₅
        (CurrentProofCheckingBranchesData.fixed-rule37 D)))
currentProofCheckingBranch D =
  orTargetedProofCheckingBranchPR
    (proofCheckingFixedRule37HilbertKExcludedSBranchFromParts
      (CurrentProofCheckingBranchesData.fixed-rule37 D)
      (CurrentProofCheckingBranchesData.hilbertK D)
      (CurrentProofCheckingBranchesData.excluded-middle D)
      (CurrentProofCheckingBranchesData.hilbertS D))
    (orTargetedProofCheckingBranchPR
      (proofRuleInductionAxiomTargetedBranch
        (CurrentProofCheckingBranchesData.induction-axiom D))
      (orTargetedProofCheckingBranchPR
        (proofCheckingRecursiveBranch₂
          (CurrentProofCheckingBranchesData.recursive D))
        (orTargetedProofCheckingBranchPR
          (proofCheckingSubstitutionBranch₂
            (CurrentProofCheckingBranchesData.substitution D))
          (orTargetedProofCheckingBranchPR
            (proofCheckingEqualityBranch₆
              (CurrentProofCheckingBranchesData.equality D))
            (orTargetedProofCheckingBranchPR
              (proofCheckingEqualitySubstitutionBranch₃
                (CurrentProofCheckingBranchesData.equality-substitution D))
              (orTargetedProofCheckingBranchPR
                (proofCheckingDerivedLogicalBranch₁₁
                  (CurrentProofCheckingBranchesData.derived-logical D))
                (orTargetedProofCheckingBranchPR
                  (proofCheckingQuantifierBranch₅
                    (CurrentProofCheckingBranchesData.quantifier D))
                  (proofCheckingLogicalBranch₅
                    (CurrentProofCheckingBranchesData.logical D)))))))))

currentProofCheckingDecodedPR :
  (D : CurrentProofCheckingBranchesData) →
  ({proof-code formula-code : ℕ} →
   DecodedExecutableProofCodeNat proof-code formula-code →
   CurrentProofCheckingTarget
      (ProofCheckingFixedAndRule37Data.leaf₀
        (CurrentProofCheckingBranchesData.fixed-rule37 D))
      (ProofCheckingFixedAndRule37Data.leaf₁
        (CurrentProofCheckingBranchesData.fixed-rule37 D))
      (ProofCheckingFixedAndRule37Data.leaf₂
        (CurrentProofCheckingBranchesData.fixed-rule37 D))
      (ProofCheckingFixedAndRule37Data.leaf₃
        (CurrentProofCheckingBranchesData.fixed-rule37 D))
      (ProofCheckingFixedAndRule37Data.leaf₄
        (CurrentProofCheckingBranchesData.fixed-rule37 D))
      (ProofCheckingFixedAndRule37Data.leaf₅
        (CurrentProofCheckingBranchesData.fixed-rule37 D))
      proof-code
      formula-code) →
  ProofCheckingPRDecodedNat
currentProofCheckingDecodedPR D decoded-coverage =
  targetedProofCheckingBranch-covered-decodedPR
    (currentProofCheckingBranch D)
    decoded-coverage

currentProofCheckingPR :
  (D : CurrentProofCheckingBranchesData) →
  ({proof-code formula-code : ℕ} →
   DecodedExecutableProofCodeNat proof-code formula-code →
   CurrentProofCheckingTarget
      (ProofCheckingFixedAndRule37Data.leaf₀
        (CurrentProofCheckingBranchesData.fixed-rule37 D))
      (ProofCheckingFixedAndRule37Data.leaf₁
        (CurrentProofCheckingBranchesData.fixed-rule37 D))
      (ProofCheckingFixedAndRule37Data.leaf₂
        (CurrentProofCheckingBranchesData.fixed-rule37 D))
      (ProofCheckingFixedAndRule37Data.leaf₃
        (CurrentProofCheckingBranchesData.fixed-rule37 D))
      (ProofCheckingFixedAndRule37Data.leaf₄
        (CurrentProofCheckingBranchesData.fixed-rule37 D))
      (ProofCheckingFixedAndRule37Data.leaf₅
        (CurrentProofCheckingBranchesData.fixed-rule37 D))
      proof-code
      formula-code) →
  ProofCheckingPR
currentProofCheckingPR D decoded-coverage =
  proofCheckingPRDecodedNat-to-ProofCheckingPR
    (currentProofCheckingDecodedPR D decoded-coverage)
