{-# OPTIONS --safe #-}

module Godel.ProofCheckingBranchBundle where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.ProofCheckingBranch
open import Godel.ProofCheckingFixedLeafBranches
  using
    ( FixedLeafTarget₆
    ; fixedLeafTargetedBranch₆
    )
open import Godel.ProofCheckingPR using (ProofCheckingPR)
open import Godel.ProofCheckingPRTargets
  using
    ( DecodedExecutableProofCodeNat
    ; ProofCheckingPRDecodedNat
    ; proofCheckingPRDecodedNat-to-ProofCheckingPR
    )
open import Godel.ProofCheckingRule37Branch
  using
    ( ProofRule37CheckingBranchData
    ; proofRule37TargetedBranch
    )
open import Godel.ProofRuleFixedCodeLeaf
  using (FixedCodeLeafData)
open import Godel.ProofRuleExcludedMiddle
  using
    ( ExcludedMiddleRuleNat
    ; ProofRuleExcludedMiddleCheckingBranchData
    ; proofRuleExcludedMiddleTargetedBranch
    )
open import Godel.ProofRuleHilbertK
  using
    ( HilbertKRuleNat
    ; ProofRuleHilbertKCheckingBranchData
    ; proofRuleHilbertKTargetedBranch
    )
open import Godel.ProofRuleHilbertS
  using
    ( HilbertSRuleNat
    ; ProofRuleHilbertSCheckingBranchData
    ; proofRuleHilbertSTargetedBranch
    )
open import Godel.ProofRuleTargets
  using (ClosedNumeralNeqRuleNat)

-- A lightweight proof-checker bundle for the first concrete pieces of the
-- final proofCodePAPR OR tree.  The six fixed leaves are supplied as opaque
-- FixedCodeLeafData values, so this module does not normalize their concrete
-- PA proof/formula codes while composing the branch.

ProofCheckingFixedAndRule37Target :
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  ℕ →
  ℕ →
  Set
ProofCheckingFixedAndRule37Target d0 d1 d2 d3 d4 d5 =
  OrProofCheckingTarget
    (FixedLeafTarget₆ d0 d1 d2 d3 d4 d5)
    ClosedNumeralNeqRuleNat

proofCheckingFixedAndRule37Branch :
  (d0 d1 d2 d3 d4 d5 : FixedCodeLeafData) →
  ProofRule37CheckingBranchData →
  TargetedProofCheckingBranchPR
    (ProofCheckingFixedAndRule37Target d0 d1 d2 d3 d4 d5)
proofCheckingFixedAndRule37Branch d0 d1 d2 d3 d4 d5 rule37 =
  orTargetedProofCheckingBranchPR
    (fixedLeafTargetedBranch₆ d0 d1 d2 d3 d4 d5)
    (proofRule37TargetedBranch rule37)

proofCheckingFixedAndRule37DecodedPR :
  (d0 d1 d2 d3 d4 d5 : FixedCodeLeafData) →
  (rule37 : ProofRule37CheckingBranchData) →
  ({proof-code formula-code : ℕ} →
   DecodedExecutableProofCodeNat proof-code formula-code →
   ProofCheckingFixedAndRule37Target
     d0 d1 d2 d3 d4 d5
     proof-code
     formula-code) →
  ProofCheckingPRDecodedNat
proofCheckingFixedAndRule37DecodedPR d0 d1 d2 d3 d4 d5 rule37 decoded-to-target =
  targetedProofCheckingBranch-covered-decodedPR
    (proofCheckingFixedAndRule37Branch d0 d1 d2 d3 d4 d5 rule37)
    decoded-to-target

proofCheckingFixedAndRule37PR :
  (d0 d1 d2 d3 d4 d5 : FixedCodeLeafData) →
  (rule37 : ProofRule37CheckingBranchData) →
  ({proof-code formula-code : ℕ} →
   DecodedExecutableProofCodeNat proof-code formula-code →
   ProofCheckingFixedAndRule37Target
     d0 d1 d2 d3 d4 d5
     proof-code
     formula-code) →
  ProofCheckingPR
proofCheckingFixedAndRule37PR d0 d1 d2 d3 d4 d5 rule37 decoded-to-target =
  proofCheckingPRDecodedNat-to-ProofCheckingPR
    (proofCheckingFixedAndRule37DecodedPR
      d0 d1 d2 d3 d4 d5
      rule37
      decoded-to-target)

record ProofCheckingFixedAndRule37Data : Set₁ where
  field
    leaf₀ :
      FixedCodeLeafData

    leaf₁ :
      FixedCodeLeafData

    leaf₂ :
      FixedCodeLeafData

    leaf₃ :
      FixedCodeLeafData

    leaf₄ :
      FixedCodeLeafData

    leaf₅ :
      FixedCodeLeafData

    rule37 :
      ProofRule37CheckingBranchData

    decoded-coverage :
      {proof-code formula-code : ℕ} →
      DecodedExecutableProofCodeNat proof-code formula-code →
      ProofCheckingFixedAndRule37Target
        leaf₀
        leaf₁
        leaf₂
        leaf₃
        leaf₄
        leaf₅
        proof-code
        formula-code

proofCheckingFixedAndRule37DataBranch :
  (D : ProofCheckingFixedAndRule37Data) →
  TargetedProofCheckingBranchPR
    (ProofCheckingFixedAndRule37Target
      (ProofCheckingFixedAndRule37Data.leaf₀ D)
      (ProofCheckingFixedAndRule37Data.leaf₁ D)
      (ProofCheckingFixedAndRule37Data.leaf₂ D)
      (ProofCheckingFixedAndRule37Data.leaf₃ D)
      (ProofCheckingFixedAndRule37Data.leaf₄ D)
      (ProofCheckingFixedAndRule37Data.leaf₅ D))
proofCheckingFixedAndRule37DataBranch D =
  proofCheckingFixedAndRule37Branch
    (ProofCheckingFixedAndRule37Data.leaf₀ D)
    (ProofCheckingFixedAndRule37Data.leaf₁ D)
    (ProofCheckingFixedAndRule37Data.leaf₂ D)
    (ProofCheckingFixedAndRule37Data.leaf₃ D)
    (ProofCheckingFixedAndRule37Data.leaf₄ D)
    (ProofCheckingFixedAndRule37Data.leaf₅ D)
    (ProofCheckingFixedAndRule37Data.rule37 D)

proofCheckingFixedAndRule37DataDecodedPR :
  ProofCheckingFixedAndRule37Data →
  ProofCheckingPRDecodedNat
proofCheckingFixedAndRule37DataDecodedPR D =
  targetedProofCheckingBranch-covered-decodedPR
    (proofCheckingFixedAndRule37DataBranch D)
    (ProofCheckingFixedAndRule37Data.decoded-coverage D)

proofCheckingFixedAndRule37DataPR :
  ProofCheckingFixedAndRule37Data →
  ProofCheckingPR
proofCheckingFixedAndRule37DataPR D =
  proofCheckingPRDecodedNat-to-ProofCheckingPR
    (proofCheckingFixedAndRule37DataDecodedPR D)

ProofCheckingFixedRule37PlusTarget :
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  (Extra : ℕ → ℕ → Set) →
  ℕ →
  ℕ →
  Set
ProofCheckingFixedRule37PlusTarget d0 d1 d2 d3 d4 d5 Extra =
  OrProofCheckingTarget
    (ProofCheckingFixedAndRule37Target d0 d1 d2 d3 d4 d5)
    Extra

proofCheckingFixedRule37PlusBranch :
  (d0 d1 d2 d3 d4 d5 : FixedCodeLeafData) →
  ProofRule37CheckingBranchData →
  {Extra : ℕ → ℕ → Set} →
  TargetedProofCheckingBranchPR Extra →
  TargetedProofCheckingBranchPR
    (ProofCheckingFixedRule37PlusTarget d0 d1 d2 d3 d4 d5 Extra)
proofCheckingFixedRule37PlusBranch d0 d1 d2 d3 d4 d5 rule37 extra =
  orTargetedProofCheckingBranchPR
    (proofCheckingFixedAndRule37Branch d0 d1 d2 d3 d4 d5 rule37)
    extra

record ProofCheckingFixedRule37PlusData
    (Extra : ℕ → ℕ → Set) :
    Set₁ where
  field
    base :
      ProofCheckingFixedAndRule37Data

    extra-branch :
      TargetedProofCheckingBranchPR Extra

    decoded-coverage-plus :
      {proof-code formula-code : ℕ} →
      DecodedExecutableProofCodeNat proof-code formula-code →
      ProofCheckingFixedRule37PlusTarget
        (ProofCheckingFixedAndRule37Data.leaf₀ base)
        (ProofCheckingFixedAndRule37Data.leaf₁ base)
        (ProofCheckingFixedAndRule37Data.leaf₂ base)
        (ProofCheckingFixedAndRule37Data.leaf₃ base)
        (ProofCheckingFixedAndRule37Data.leaf₄ base)
        (ProofCheckingFixedAndRule37Data.leaf₅ base)
        Extra
        proof-code
        formula-code

proofCheckingFixedRule37PlusDataAsExtension :
  {Extra : ℕ → ℕ → Set} →
  (D : ProofCheckingFixedRule37PlusData Extra) →
  ProofCheckingBranchExtensionData
    (ProofCheckingFixedAndRule37Target
      (ProofCheckingFixedAndRule37Data.leaf₀
        (ProofCheckingFixedRule37PlusData.base D))
      (ProofCheckingFixedAndRule37Data.leaf₁
        (ProofCheckingFixedRule37PlusData.base D))
      (ProofCheckingFixedAndRule37Data.leaf₂
        (ProofCheckingFixedRule37PlusData.base D))
      (ProofCheckingFixedAndRule37Data.leaf₃
        (ProofCheckingFixedRule37PlusData.base D))
      (ProofCheckingFixedAndRule37Data.leaf₄
        (ProofCheckingFixedRule37PlusData.base D))
      (ProofCheckingFixedAndRule37Data.leaf₅
        (ProofCheckingFixedRule37PlusData.base D)))
    Extra
proofCheckingFixedRule37PlusDataAsExtension D = record
  { base-branch =
      proofCheckingFixedAndRule37DataBranch
        (ProofCheckingFixedRule37PlusData.base D)
  ; extra-branch =
      ProofCheckingFixedRule37PlusData.extra-branch D
  ; decoded-coverage =
      ProofCheckingFixedRule37PlusData.decoded-coverage-plus D
  }

proofCheckingFixedRule37PlusDataBranch :
  {Extra : ℕ → ℕ → Set} →
  (D : ProofCheckingFixedRule37PlusData Extra) →
  TargetedProofCheckingBranchPR
    (ProofCheckingFixedRule37PlusTarget
      (ProofCheckingFixedAndRule37Data.leaf₀
        (ProofCheckingFixedRule37PlusData.base D))
      (ProofCheckingFixedAndRule37Data.leaf₁
        (ProofCheckingFixedRule37PlusData.base D))
      (ProofCheckingFixedAndRule37Data.leaf₂
        (ProofCheckingFixedRule37PlusData.base D))
      (ProofCheckingFixedAndRule37Data.leaf₃
        (ProofCheckingFixedRule37PlusData.base D))
      (ProofCheckingFixedAndRule37Data.leaf₄
        (ProofCheckingFixedRule37PlusData.base D))
      (ProofCheckingFixedAndRule37Data.leaf₅
        (ProofCheckingFixedRule37PlusData.base D))
      Extra)
proofCheckingFixedRule37PlusDataBranch D =
  proofCheckingBranchExtension
    (proofCheckingFixedRule37PlusDataAsExtension D)

proofCheckingFixedRule37PlusDataDecodedPR :
  {Extra : ℕ → ℕ → Set} →
  ProofCheckingFixedRule37PlusData Extra →
  ProofCheckingPRDecodedNat
proofCheckingFixedRule37PlusDataDecodedPR D =
  proofCheckingBranchExtensionDecodedPR
    (proofCheckingFixedRule37PlusDataAsExtension D)

proofCheckingFixedRule37PlusDataPR :
  {Extra : ℕ → ℕ → Set} →
  ProofCheckingFixedRule37PlusData Extra →
  ProofCheckingPR
proofCheckingFixedRule37PlusDataPR D =
  proofCheckingPRDecodedNat-to-ProofCheckingPR
    (proofCheckingFixedRule37PlusDataDecodedPR D)

ProofCheckingFixedRule37HilbertKTarget :
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  ℕ →
  ℕ →
  Set
ProofCheckingFixedRule37HilbertKTarget d0 d1 d2 d3 d4 d5 =
  ProofCheckingFixedRule37PlusTarget
    d0 d1 d2 d3 d4 d5
    HilbertKRuleNat

record ProofCheckingFixedRule37HilbertKData : Set₁ where
  field
    base :
      ProofCheckingFixedAndRule37Data

    hilbertK :
      ProofRuleHilbertKCheckingBranchData

    decoded-coverage-hilbertK :
      {proof-code formula-code : ℕ} →
      DecodedExecutableProofCodeNat proof-code formula-code →
      ProofCheckingFixedRule37HilbertKTarget
        (ProofCheckingFixedAndRule37Data.leaf₀ base)
        (ProofCheckingFixedAndRule37Data.leaf₁ base)
        (ProofCheckingFixedAndRule37Data.leaf₂ base)
        (ProofCheckingFixedAndRule37Data.leaf₃ base)
        (ProofCheckingFixedAndRule37Data.leaf₄ base)
        (ProofCheckingFixedAndRule37Data.leaf₅ base)
        proof-code
        formula-code

proofCheckingFixedRule37HilbertKAsPlus :
  ProofCheckingFixedRule37HilbertKData →
  ProofCheckingFixedRule37PlusData HilbertKRuleNat
proofCheckingFixedRule37HilbertKAsPlus D = record
  { base =
      ProofCheckingFixedRule37HilbertKData.base D
  ; extra-branch =
      proofRuleHilbertKTargetedBranch
        (ProofCheckingFixedRule37HilbertKData.hilbertK D)
  ; decoded-coverage-plus =
      ProofCheckingFixedRule37HilbertKData.decoded-coverage-hilbertK D
  }

proofCheckingFixedRule37HilbertKDecodedPR :
  ProofCheckingFixedRule37HilbertKData →
  ProofCheckingPRDecodedNat
proofCheckingFixedRule37HilbertKDecodedPR D =
  proofCheckingFixedRule37PlusDataDecodedPR
    (proofCheckingFixedRule37HilbertKAsPlus D)

proofCheckingFixedRule37HilbertKPR :
  ProofCheckingFixedRule37HilbertKData →
  ProofCheckingPR
proofCheckingFixedRule37HilbertKPR D =
  proofCheckingFixedRule37PlusDataPR
    (proofCheckingFixedRule37HilbertKAsPlus D)

proofCheckingFixedRule37HilbertKBranch :
  (D : ProofCheckingFixedAndRule37Data) →
  ProofRuleHilbertKCheckingBranchData →
  TargetedProofCheckingBranchPR
    (ProofCheckingFixedRule37HilbertKTarget
      (ProofCheckingFixedAndRule37Data.leaf₀ D)
      (ProofCheckingFixedAndRule37Data.leaf₁ D)
      (ProofCheckingFixedAndRule37Data.leaf₂ D)
      (ProofCheckingFixedAndRule37Data.leaf₃ D)
      (ProofCheckingFixedAndRule37Data.leaf₄ D)
      (ProofCheckingFixedAndRule37Data.leaf₅ D))
proofCheckingFixedRule37HilbertKBranch D hilbertK =
  proofCheckingFixedRule37PlusBranch
    (ProofCheckingFixedAndRule37Data.leaf₀ D)
    (ProofCheckingFixedAndRule37Data.leaf₁ D)
    (ProofCheckingFixedAndRule37Data.leaf₂ D)
    (ProofCheckingFixedAndRule37Data.leaf₃ D)
    (ProofCheckingFixedAndRule37Data.leaf₄ D)
    (ProofCheckingFixedAndRule37Data.leaf₅ D)
    (ProofCheckingFixedAndRule37Data.rule37 D)
    (proofRuleHilbertKTargetedBranch hilbertK)

ProofCheckingFixedRule37HilbertKExcludedTarget :
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  ℕ →
  ℕ →
  Set
ProofCheckingFixedRule37HilbertKExcludedTarget d0 d1 d2 d3 d4 d5 =
  OrProofCheckingTarget
    (ProofCheckingFixedRule37HilbertKTarget d0 d1 d2 d3 d4 d5)
    ExcludedMiddleRuleNat

record ProofCheckingFixedRule37HilbertKExcludedData : Set₁ where
  field
    base :
      ProofCheckingFixedAndRule37Data

    hilbertK :
      ProofRuleHilbertKCheckingBranchData

    excluded-middle :
      ProofRuleExcludedMiddleCheckingBranchData

    decoded-coverage-excluded :
      {proof-code formula-code : ℕ} →
      DecodedExecutableProofCodeNat proof-code formula-code →
      ProofCheckingFixedRule37HilbertKExcludedTarget
        (ProofCheckingFixedAndRule37Data.leaf₀ base)
        (ProofCheckingFixedAndRule37Data.leaf₁ base)
        (ProofCheckingFixedAndRule37Data.leaf₂ base)
        (ProofCheckingFixedAndRule37Data.leaf₃ base)
        (ProofCheckingFixedAndRule37Data.leaf₄ base)
        (ProofCheckingFixedAndRule37Data.leaf₅ base)
        proof-code
        formula-code

proofCheckingFixedRule37HilbertKExcludedBranch :
  (D : ProofCheckingFixedRule37HilbertKExcludedData) →
  TargetedProofCheckingBranchPR
    (ProofCheckingFixedRule37HilbertKExcludedTarget
      (ProofCheckingFixedAndRule37Data.leaf₀
        (ProofCheckingFixedRule37HilbertKExcludedData.base D))
      (ProofCheckingFixedAndRule37Data.leaf₁
        (ProofCheckingFixedRule37HilbertKExcludedData.base D))
      (ProofCheckingFixedAndRule37Data.leaf₂
        (ProofCheckingFixedRule37HilbertKExcludedData.base D))
      (ProofCheckingFixedAndRule37Data.leaf₃
        (ProofCheckingFixedRule37HilbertKExcludedData.base D))
      (ProofCheckingFixedAndRule37Data.leaf₄
        (ProofCheckingFixedRule37HilbertKExcludedData.base D))
      (ProofCheckingFixedAndRule37Data.leaf₅
        (ProofCheckingFixedRule37HilbertKExcludedData.base D)))
proofCheckingFixedRule37HilbertKExcludedBranch D =
  orTargetedProofCheckingBranchPR
    (proofCheckingFixedRule37HilbertKBranch
      (ProofCheckingFixedRule37HilbertKExcludedData.base D)
      (ProofCheckingFixedRule37HilbertKExcludedData.hilbertK D))
    (proofRuleExcludedMiddleTargetedBranch
      (ProofCheckingFixedRule37HilbertKExcludedData.excluded-middle D))

proofCheckingFixedRule37HilbertKExcludedBranchFromParts :
  (D : ProofCheckingFixedAndRule37Data) →
  ProofRuleHilbertKCheckingBranchData →
  ProofRuleExcludedMiddleCheckingBranchData →
  TargetedProofCheckingBranchPR
    (ProofCheckingFixedRule37HilbertKExcludedTarget
      (ProofCheckingFixedAndRule37Data.leaf₀ D)
      (ProofCheckingFixedAndRule37Data.leaf₁ D)
      (ProofCheckingFixedAndRule37Data.leaf₂ D)
      (ProofCheckingFixedAndRule37Data.leaf₃ D)
      (ProofCheckingFixedAndRule37Data.leaf₄ D)
      (ProofCheckingFixedAndRule37Data.leaf₅ D))
proofCheckingFixedRule37HilbertKExcludedBranchFromParts D hilbertK excluded-middle =
  orTargetedProofCheckingBranchPR
    (proofCheckingFixedRule37HilbertKBranch D hilbertK)
    (proofRuleExcludedMiddleTargetedBranch excluded-middle)

proofCheckingFixedRule37HilbertKExcludedDecodedPR :
  ProofCheckingFixedRule37HilbertKExcludedData →
  ProofCheckingPRDecodedNat
proofCheckingFixedRule37HilbertKExcludedDecodedPR D =
  targetedProofCheckingBranch-covered-decodedPR
    (proofCheckingFixedRule37HilbertKExcludedBranch D)
    (ProofCheckingFixedRule37HilbertKExcludedData.decoded-coverage-excluded D)

proofCheckingFixedRule37HilbertKExcludedPR :
  ProofCheckingFixedRule37HilbertKExcludedData →
  ProofCheckingPR
proofCheckingFixedRule37HilbertKExcludedPR D =
  proofCheckingPRDecodedNat-to-ProofCheckingPR
    (proofCheckingFixedRule37HilbertKExcludedDecodedPR D)

ProofCheckingFixedRule37HilbertKExcludedSTarget :
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  ℕ →
  ℕ →
  Set
ProofCheckingFixedRule37HilbertKExcludedSTarget d0 d1 d2 d3 d4 d5 =
  OrProofCheckingTarget
    (ProofCheckingFixedRule37HilbertKExcludedTarget d0 d1 d2 d3 d4 d5)
    HilbertSRuleNat

record ProofCheckingFixedRule37HilbertKExcludedSData : Set₁ where
  field
    base :
      ProofCheckingFixedAndRule37Data

    hilbertK :
      ProofRuleHilbertKCheckingBranchData

    excluded-middle :
      ProofRuleExcludedMiddleCheckingBranchData

    hilbertS :
      ProofRuleHilbertSCheckingBranchData

    decoded-coverage-hilbertS :
      {proof-code formula-code : ℕ} →
      DecodedExecutableProofCodeNat proof-code formula-code →
      ProofCheckingFixedRule37HilbertKExcludedSTarget
        (ProofCheckingFixedAndRule37Data.leaf₀ base)
        (ProofCheckingFixedAndRule37Data.leaf₁ base)
        (ProofCheckingFixedAndRule37Data.leaf₂ base)
        (ProofCheckingFixedAndRule37Data.leaf₃ base)
        (ProofCheckingFixedAndRule37Data.leaf₄ base)
        (ProofCheckingFixedAndRule37Data.leaf₅ base)
        proof-code
        formula-code

proofCheckingFixedRule37HilbertKExcludedSBranch :
  (D : ProofCheckingFixedRule37HilbertKExcludedSData) →
  TargetedProofCheckingBranchPR
    (ProofCheckingFixedRule37HilbertKExcludedSTarget
      (ProofCheckingFixedAndRule37Data.leaf₀
        (ProofCheckingFixedRule37HilbertKExcludedSData.base D))
      (ProofCheckingFixedAndRule37Data.leaf₁
        (ProofCheckingFixedRule37HilbertKExcludedSData.base D))
      (ProofCheckingFixedAndRule37Data.leaf₂
        (ProofCheckingFixedRule37HilbertKExcludedSData.base D))
      (ProofCheckingFixedAndRule37Data.leaf₃
        (ProofCheckingFixedRule37HilbertKExcludedSData.base D))
      (ProofCheckingFixedAndRule37Data.leaf₄
        (ProofCheckingFixedRule37HilbertKExcludedSData.base D))
      (ProofCheckingFixedAndRule37Data.leaf₅
        (ProofCheckingFixedRule37HilbertKExcludedSData.base D)))
proofCheckingFixedRule37HilbertKExcludedSBranch D =
  orTargetedProofCheckingBranchPR
    (proofCheckingFixedRule37HilbertKExcludedBranchFromParts
      (ProofCheckingFixedRule37HilbertKExcludedSData.base D)
      (ProofCheckingFixedRule37HilbertKExcludedSData.hilbertK D)
      (ProofCheckingFixedRule37HilbertKExcludedSData.excluded-middle D))
    (proofRuleHilbertSTargetedBranch
      (ProofCheckingFixedRule37HilbertKExcludedSData.hilbertS D))

proofCheckingFixedRule37HilbertKExcludedSBranchFromParts :
  (D : ProofCheckingFixedAndRule37Data) →
  ProofRuleHilbertKCheckingBranchData →
  ProofRuleExcludedMiddleCheckingBranchData →
  ProofRuleHilbertSCheckingBranchData →
  TargetedProofCheckingBranchPR
    (ProofCheckingFixedRule37HilbertKExcludedSTarget
      (ProofCheckingFixedAndRule37Data.leaf₀ D)
      (ProofCheckingFixedAndRule37Data.leaf₁ D)
      (ProofCheckingFixedAndRule37Data.leaf₂ D)
      (ProofCheckingFixedAndRule37Data.leaf₃ D)
      (ProofCheckingFixedAndRule37Data.leaf₄ D)
      (ProofCheckingFixedAndRule37Data.leaf₅ D))
proofCheckingFixedRule37HilbertKExcludedSBranchFromParts D hilbertK excluded-middle hilbertS =
  orTargetedProofCheckingBranchPR
    (proofCheckingFixedRule37HilbertKExcludedBranchFromParts
      D
      hilbertK
      excluded-middle)
    (proofRuleHilbertSTargetedBranch hilbertS)

proofCheckingFixedRule37HilbertKExcludedSDecodedPR :
  ProofCheckingFixedRule37HilbertKExcludedSData →
  ProofCheckingPRDecodedNat
proofCheckingFixedRule37HilbertKExcludedSDecodedPR D =
  targetedProofCheckingBranch-covered-decodedPR
    (proofCheckingFixedRule37HilbertKExcludedSBranch D)
    (ProofCheckingFixedRule37HilbertKExcludedSData.decoded-coverage-hilbertS D)

proofCheckingFixedRule37HilbertKExcludedSPR :
  ProofCheckingFixedRule37HilbertKExcludedSData →
  ProofCheckingPR
proofCheckingFixedRule37HilbertKExcludedSPR D =
  proofCheckingPRDecodedNat-to-ProofCheckingPR
    (proofCheckingFixedRule37HilbertKExcludedSDecodedPR D)
