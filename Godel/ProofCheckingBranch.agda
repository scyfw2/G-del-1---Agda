{-# OPTIONS --safe #-}

module Godel.ProofCheckingBranch where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.PRRepresentabilityFinal
  using (PARepresentsRelation; prrel-represented)
open import Godel.ProofCheckingPR using (proofCodeArgs; ProofCheckingPR)
open import Godel.ProofCheckingPRTargets
  using
    ( DecodedExecutableProofCodeNat
    ; ProofCheckingPRDecodedNat
    ; proofCheckingPRDecodedNat-to-ProofCheckingPR
    )
open import Godel.ProofRuleFixedPair
  using (fixedPairF)
open import Godel.ProofRuleFixedProofOr
  using
    ( NonzeroNat
    ; fixedPairF-nonzero-sound
    )
open import Godel.ProofRuleFixedCodeLeaf
  using
    ( FixedCodeLeafData
    ; FixedCodeLeafNat
    ; fixedCodeLeafF
    ; fixedCodeLeafPR
    ; fixedCodeLeaf-complete
    ; fixedCodeLeafNat-to-decoded
    ; fixedCodeLeafPR-to-decoded
    )
open import Godel.ProofRulePRDisjunction
  using
    ( orProofRulePR
    ; orProofRule-complete-left
    ; orProofRule-complete-right
    ; orProofRule-nonzero-sound
    ; orProofRule-nonzero-output-sound
    )

-- A proof-checker branch is any binary PR relation over
-- (proof-code, formula-code) whose successful hits decode to the executable
-- proof-checker target.  The nonzero sound field is what makes OR-composition
-- usable: orF only tells us that one branch was nonzero, not definitionally
-- equal to one.
record ProofCheckingBranchPR : Set₁ where
  field
    branch-pr :
      PRRel (suc (suc zero))

    branch-sound-decoded :
      {proof-code formula-code : ℕ} →
      PRRel-holds branch-pr (proofCodeArgs proof-code formula-code) →
      DecodedExecutableProofCodeNat proof-code formula-code

    branch-nonzero-sound-decoded :
      {proof-code formula-code : ℕ} →
      NonzeroNat
        (evalPRF
          (PRRel.characteristic branch-pr)
          (proofCodeArgs proof-code formula-code)) →
      DecodedExecutableProofCodeNat proof-code formula-code

proofCheckingBranchPR-represented :
  (D : ProofCheckingBranchPR) →
  PARepresentsRelation (ProofCheckingBranchPR.branch-pr D)
proofCheckingBranchPR-represented D =
  prrel-represented (ProofCheckingBranchPR.branch-pr D)

fixedCodeLeafBranch :
  FixedCodeLeafData →
  ProofCheckingBranchPR
fixedCodeLeafBranch D = record
  { branch-pr =
      fixedCodeLeafPR D
  ; branch-sound-decoded =
      fixedCodeLeafPR-to-decoded D
  ; branch-nonzero-sound-decoded =
      λ {proof-code} {formula-code} nonzero →
        fixedCodeLeafNat-to-decoded D
          (fixedPairF-nonzero-sound nonzero)
  }

orProofCheckingBranchPR :
  ProofCheckingBranchPR →
  ProofCheckingBranchPR →
  ProofCheckingBranchPR
orProofCheckingBranchPR left right = record
  { branch-pr =
      orProofRulePR
        (ProofCheckingBranchPR.branch-pr left)
        (ProofCheckingBranchPR.branch-pr right)
  ; branch-sound-decoded =
      λ {proof-code} {formula-code} holds →
        or-nonzero-to-decoded {proof-code} {formula-code}
          (orProofRule-nonzero-sound
            (ProofCheckingBranchPR.branch-pr left)
            (ProofCheckingBranchPR.branch-pr right)
            holds)
  ; branch-nonzero-sound-decoded =
      λ {proof-code} {formula-code} nonzero →
        or-nonzero-to-decoded {proof-code} {formula-code}
          (orProofRule-nonzero-output-sound
            (ProofCheckingBranchPR.branch-pr left)
            (ProofCheckingBranchPR.branch-pr right)
            nonzero)
  }
  where
    or-nonzero-to-decoded :
      {proof-code formula-code : ℕ} →
      NonzeroNat
        (evalPRF
          (PRRel.characteristic (ProofCheckingBranchPR.branch-pr left))
          (proofCodeArgs proof-code formula-code))
      ⊎
      NonzeroNat
        (evalPRF
          (PRRel.characteristic (ProofCheckingBranchPR.branch-pr right))
          (proofCodeArgs proof-code formula-code)) →
      DecodedExecutableProofCodeNat proof-code formula-code
    or-nonzero-to-decoded (inj₁ left-hit) =
      ProofCheckingBranchPR.branch-nonzero-sound-decoded left left-hit
    or-nonzero-to-decoded (inj₂ right-hit) =
      ProofCheckingBranchPR.branch-nonzero-sound-decoded right right-hit

orProofCheckingBranch-complete-left :
  (left right : ProofCheckingBranchPR) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (ProofCheckingBranchPR.branch-pr left)
    (proofCodeArgs proof-code formula-code) →
  PRRel-holds
    (ProofCheckingBranchPR.branch-pr
      (orProofCheckingBranchPR left right))
    (proofCodeArgs proof-code formula-code)
orProofCheckingBranch-complete-left left right =
  orProofRule-complete-left
    (ProofCheckingBranchPR.branch-pr left)
    (ProofCheckingBranchPR.branch-pr right)

orProofCheckingBranch-complete-right :
  (left right : ProofCheckingBranchPR) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (ProofCheckingBranchPR.branch-pr right)
    (proofCodeArgs proof-code formula-code) →
  PRRel-holds
    (ProofCheckingBranchPR.branch-pr
      (orProofCheckingBranchPR left right))
    (proofCodeArgs proof-code formula-code)
orProofCheckingBranch-complete-right left right =
  orProofRule-complete-right
    (ProofCheckingBranchPR.branch-pr left)
    (ProofCheckingBranchPR.branch-pr right)

-- A targeted branch is complete only for the semantic slice it implements.
-- This is the shape needed for the final checker: each proof-rule branch owns
-- one target, and the targets are then OR-combined until they cover all decoded
-- executable proof-code facts.
record TargetedProofCheckingBranchPR
    (Target : ℕ → ℕ → Set) :
    Set₁ where
  field
    branch :
      ProofCheckingBranchPR

    branch-complete-target :
      {proof-code formula-code : ℕ} →
      Target proof-code formula-code →
      PRRel-holds
        (ProofCheckingBranchPR.branch-pr branch)
        (proofCodeArgs proof-code formula-code)

fixedCodeLeafTargetedBranch :
  (D : FixedCodeLeafData) →
  TargetedProofCheckingBranchPR (FixedCodeLeafNat D)
fixedCodeLeafTargetedBranch D = record
  { branch =
      fixedCodeLeafBranch D
  ; branch-complete-target =
      fixedCodeLeaf-complete D
  }

targetedProofCheckingBranch-map :
  {Target Source : ℕ → ℕ → Set} →
  ({proof-code formula-code : ℕ} →
   Source proof-code formula-code →
   Target proof-code formula-code) →
  TargetedProofCheckingBranchPR Target →
  TargetedProofCheckingBranchPR Source
targetedProofCheckingBranch-map source-to-target D = record
  { branch =
      TargetedProofCheckingBranchPR.branch D
  ; branch-complete-target =
      λ source →
        TargetedProofCheckingBranchPR.branch-complete-target D
          (source-to-target source)
  }

data OrProofCheckingTarget
    (Left Right : ℕ → ℕ → Set)
    (proof-code formula-code : ℕ) :
    Set where
  branch-left :
    Left proof-code formula-code →
    OrProofCheckingTarget Left Right proof-code formula-code

  branch-right :
    Right proof-code formula-code →
    OrProofCheckingTarget Left Right proof-code formula-code

orTargetedProofCheckingBranchPR :
  {Left Right : ℕ → ℕ → Set} →
  TargetedProofCheckingBranchPR Left →
  TargetedProofCheckingBranchPR Right →
  TargetedProofCheckingBranchPR (OrProofCheckingTarget Left Right)
orTargetedProofCheckingBranchPR left right = record
  { branch =
      orProofCheckingBranchPR
        (TargetedProofCheckingBranchPR.branch left)
        (TargetedProofCheckingBranchPR.branch right)
  ; branch-complete-target =
      λ where
        (branch-left left-target) →
          orProofCheckingBranch-complete-left
            (TargetedProofCheckingBranchPR.branch left)
            (TargetedProofCheckingBranchPR.branch right)
            (TargetedProofCheckingBranchPR.branch-complete-target
              left
              left-target)
        (branch-right right-target) →
          orProofCheckingBranch-complete-right
            (TargetedProofCheckingBranchPR.branch left)
            (TargetedProofCheckingBranchPR.branch right)
            (TargetedProofCheckingBranchPR.branch-complete-target
              right
              right-target)
  }

targetedProofCheckingBranch-to-decodedPR :
  TargetedProofCheckingBranchPR DecodedExecutableProofCodeNat →
  ProofCheckingPRDecodedNat
targetedProofCheckingBranch-to-decodedPR D = record
  { proofCodePAPR =
      ProofCheckingBranchPR.branch-pr
        (TargetedProofCheckingBranchPR.branch D)
  ; proofCodePAPR-complete-decoded-nat =
      TargetedProofCheckingBranchPR.branch-complete-target D
  ; proofCodePAPR-sound-decoded-nat =
      ProofCheckingBranchPR.branch-sound-decoded
        (TargetedProofCheckingBranchPR.branch D)
  }

targetedProofCheckingBranch-covered-decodedPR :
  {Target : ℕ → ℕ → Set} →
  TargetedProofCheckingBranchPR Target →
  ({proof-code formula-code : ℕ} →
   DecodedExecutableProofCodeNat proof-code formula-code →
   Target proof-code formula-code) →
  ProofCheckingPRDecodedNat
targetedProofCheckingBranch-covered-decodedPR D decoded-to-target =
  targetedProofCheckingBranch-to-decodedPR
    (targetedProofCheckingBranch-map decoded-to-target D)

targetedProofCheckingBranch-covered-proofCheckingPR :
  {Target : ℕ → ℕ → Set} →
  TargetedProofCheckingBranchPR Target →
  ({proof-code formula-code : ℕ} →
   DecodedExecutableProofCodeNat proof-code formula-code →
   Target proof-code formula-code) →
  ProofCheckingPR
targetedProofCheckingBranch-covered-proofCheckingPR D decoded-to-target =
  proofCheckingPRDecodedNat-to-ProofCheckingPR
    (targetedProofCheckingBranch-covered-decodedPR D decoded-to-target)

-- Generic extension data for growing the final proofCodePAPR branch tree in
-- stages.  A caller supplies an already-built base branch, one more targeted
-- branch family, and a coverage proof saying that the combined target covers
-- every decoded executable proof-code fact.
record ProofCheckingBranchExtensionData
    (Base Extra : ℕ → ℕ → Set) :
    Set₁ where
  field
    base-branch :
      TargetedProofCheckingBranchPR Base

    extra-branch :
      TargetedProofCheckingBranchPR Extra

    decoded-coverage :
      {proof-code formula-code : ℕ} →
      DecodedExecutableProofCodeNat proof-code formula-code →
      OrProofCheckingTarget Base Extra proof-code formula-code

proofCheckingBranchExtension :
  {Base Extra : ℕ → ℕ → Set} →
  ProofCheckingBranchExtensionData Base Extra →
  TargetedProofCheckingBranchPR (OrProofCheckingTarget Base Extra)
proofCheckingBranchExtension D =
  orTargetedProofCheckingBranchPR
    (ProofCheckingBranchExtensionData.base-branch D)
    (ProofCheckingBranchExtensionData.extra-branch D)

proofCheckingBranchExtensionDecodedPR :
  {Base Extra : ℕ → ℕ → Set} →
  ProofCheckingBranchExtensionData Base Extra →
  ProofCheckingPRDecodedNat
proofCheckingBranchExtensionDecodedPR D =
  targetedProofCheckingBranch-covered-decodedPR
    (proofCheckingBranchExtension D)
    (ProofCheckingBranchExtensionData.decoded-coverage D)

proofCheckingBranchExtensionPR :
  {Base Extra : ℕ → ℕ → Set} →
  ProofCheckingBranchExtensionData Base Extra →
  ProofCheckingPR
proofCheckingBranchExtensionPR D =
  proofCheckingPRDecodedNat-to-ProofCheckingPR
    (proofCheckingBranchExtensionDecodedPR D)
