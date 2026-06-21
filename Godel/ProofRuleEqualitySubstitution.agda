{-# OPTIONS --safe #-}

module Godel.ProofRuleEqualitySubstitution where

open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.CanonicalCoding
  using
    ( canonicalCodeTerm
    ; canonicalNatFormula
    ; encodeCode
    ; node
    )
open import Godel.PrimitiveRecursive
open import Godel.PRRepresentabilityFinal
  using (PARepresentsRelation; prrel-represented)
open import Godel.ProofCanonicalChecker
  using
    ( checkPAProofCode
    ; decodeCanonicalTerm-roundTrip
    )
open import Godel.ProofCheckingBranch
open import Godel.ProofCheckingPR
  using (proofCodeArgs)
open import Godel.ProofCheckingPRTargets
  using (DecodedExecutableProofCodeNat)
open import Godel.ProofRuleFixedProofOr
  using (NonzeroNat)

-- Targets for equality-value and right-substitution proof rules:
--
--   tag 24 eq-unique-value
--   tag 35 eq-subst-right
--   tag 36 eq-subst-suc-right

record ProofRuleEqualitySubstitutionPR
    (Target : ℕ → ℕ → Set) :
    Set₁ where
  field
    equality-substitution-pr :
      PRRel (suc (suc zero))

    equality-substitution-complete :
      {proof-code formula-code : ℕ} →
      Target proof-code formula-code →
      PRRel-holds
        equality-substitution-pr
        (proofCodeArgs proof-code formula-code)

    equality-substitution-sound :
      {proof-code formula-code : ℕ} →
      PRRel-holds
        equality-substitution-pr
        (proofCodeArgs proof-code formula-code) →
      Target proof-code formula-code

proofRuleEqualitySubstitutionPR-represented :
  {Target : ℕ → ℕ → Set} →
  (D : ProofRuleEqualitySubstitutionPR Target) →
  PARepresentsRelation
    (ProofRuleEqualitySubstitutionPR.equality-substitution-pr D)
proofRuleEqualitySubstitutionPR-represented D =
  prrel-represented
    (ProofRuleEqualitySubstitutionPR.equality-substitution-pr D)

record ProofRuleEqualitySubstitutionCheckingBranchData
    (Target : ℕ → ℕ → Set) :
    Set₁ where
  field
    equality-substitution-pr-data :
      ProofRuleEqualitySubstitutionPR Target

    equality-substitution-nonzero-sound :
      {proof-code formula-code : ℕ} →
      NonzeroNat
        (evalPRF
          (PRRel.characteristic
            (ProofRuleEqualitySubstitutionPR.equality-substitution-pr
              equality-substitution-pr-data))
          (proofCodeArgs proof-code formula-code)) →
      Target proof-code formula-code

proofRuleEqualitySubstitutionCheckingBranch :
  {Target : ℕ → ℕ → Set} →
  ({proof-code formula-code : ℕ} →
   Target proof-code formula-code →
   DecodedExecutableProofCodeNat proof-code formula-code) →
  ProofRuleEqualitySubstitutionCheckingBranchData Target →
  ProofCheckingBranchPR
proofRuleEqualitySubstitutionCheckingBranch target-to-decoded D = record
  { branch-pr =
      ProofRuleEqualitySubstitutionPR.equality-substitution-pr
        (ProofRuleEqualitySubstitutionCheckingBranchData.equality-substitution-pr-data
          D)
  ; branch-sound-decoded =
      λ holds →
        target-to-decoded
          (ProofRuleEqualitySubstitutionPR.equality-substitution-sound
            (ProofRuleEqualitySubstitutionCheckingBranchData.equality-substitution-pr-data
              D)
            holds)
  ; branch-nonzero-sound-decoded =
      λ nonzero →
        target-to-decoded
          (ProofRuleEqualitySubstitutionCheckingBranchData.equality-substitution-nonzero-sound
            D
            nonzero)
  }

proofRuleEqualitySubstitutionTargetedBranch :
  {Target : ℕ → ℕ → Set} →
  ({proof-code formula-code : ℕ} →
   Target proof-code formula-code →
   DecodedExecutableProofCodeNat proof-code formula-code) →
  ProofRuleEqualitySubstitutionCheckingBranchData Target →
  TargetedProofCheckingBranchPR Target
proofRuleEqualitySubstitutionTargetedBranch target-to-decoded D = record
  { branch =
      proofRuleEqualitySubstitutionCheckingBranch target-to-decoded D
  ; branch-complete-target =
      ProofRuleEqualitySubstitutionPR.equality-substitution-complete
        (ProofRuleEqualitySubstitutionCheckingBranchData.equality-substitution-pr-data
          D)
  }

EqUniqueValueFormula : Term → Term → Term → Formula
EqUniqueValueFormula y z c =
  y ≈ c ⇒ (z ≈ c ⇒ y ≈ z)

EqUniqueValueProofCode : Term → Term → Term → ℕ
EqUniqueValueProofCode y z c =
  encodeCode
    (node 24
      (canonicalCodeTerm y ∷
       canonicalCodeTerm z ∷
       canonicalCodeTerm c ∷
       []))

EqUniqueValueRuleNat : ℕ → ℕ → Set
EqUniqueValueRuleNat proof-code formula-code =
  Σ Term
    (λ y →
      Σ Term
        (λ z →
          Σ Term
            (λ c →
              (proof-code ≡ EqUniqueValueProofCode y z c) ×
              (formula-code ≡
               canonicalNatFormula (EqUniqueValueFormula y z c)))))

eqUniqueValueRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  EqUniqueValueRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
eqUniqueValueRuleNat-to-decoded
  (y ,Σ (z ,Σ (c ,Σ (proof-eq ,× formula-eq)))) =
  node 24
    (canonicalCodeTerm y ∷
     canonicalCodeTerm z ∷
     canonicalCodeTerm c ∷
     [])
  ,Σ
  (EqUniqueValueFormula y z c ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 24
          (canonicalCodeTerm y ∷
           canonicalCodeTerm z ∷
           canonicalCodeTerm c ∷
           []))
      ≡
      just (EqUniqueValueFormula y z c)
    check-eq
      rewrite decodeCanonicalTerm-roundTrip y
            | decodeCanonicalTerm-roundTrip z
            | decodeCanonicalTerm-roundTrip c =
      refl

ProofRuleEqUniqueValuePR : Set₁
ProofRuleEqUniqueValuePR =
  ProofRuleEqualitySubstitutionPR EqUniqueValueRuleNat

ProofRuleEqUniqueValueCheckingBranchData : Set₁
ProofRuleEqUniqueValueCheckingBranchData =
  ProofRuleEqualitySubstitutionCheckingBranchData EqUniqueValueRuleNat

proofRuleEqUniqueValueTargetedBranch :
  ProofRuleEqUniqueValueCheckingBranchData →
  TargetedProofCheckingBranchPR EqUniqueValueRuleNat
proofRuleEqUniqueValueTargetedBranch =
  proofRuleEqualitySubstitutionTargetedBranch
    eqUniqueValueRuleNat-to-decoded

EqSubstRightFormula : Term → Term → Term → Formula
EqSubstRightFormula a b y =
  a ≈ b ⇒ (y ≈ a ⇒ y ≈ b)

EqSubstRightProofCode : Term → Term → Term → ℕ
EqSubstRightProofCode a b y =
  encodeCode
    (node 35
      (canonicalCodeTerm a ∷
       canonicalCodeTerm b ∷
       canonicalCodeTerm y ∷
       []))

EqSubstRightRuleNat : ℕ → ℕ → Set
EqSubstRightRuleNat proof-code formula-code =
  Σ Term
    (λ a →
      Σ Term
        (λ b →
          Σ Term
            (λ y →
              (proof-code ≡ EqSubstRightProofCode a b y) ×
              (formula-code ≡
               canonicalNatFormula (EqSubstRightFormula a b y)))))

eqSubstRightRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  EqSubstRightRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
eqSubstRightRuleNat-to-decoded
  (a ,Σ (b ,Σ (y ,Σ (proof-eq ,× formula-eq)))) =
  node 35
    (canonicalCodeTerm a ∷
     canonicalCodeTerm b ∷
     canonicalCodeTerm y ∷
     [])
  ,Σ
  (EqSubstRightFormula a b y ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 35
          (canonicalCodeTerm a ∷
           canonicalCodeTerm b ∷
           canonicalCodeTerm y ∷
           []))
      ≡
      just (EqSubstRightFormula a b y)
    check-eq
      rewrite decodeCanonicalTerm-roundTrip a
            | decodeCanonicalTerm-roundTrip b
            | decodeCanonicalTerm-roundTrip y =
      refl

ProofRuleEqSubstRightPR : Set₁
ProofRuleEqSubstRightPR =
  ProofRuleEqualitySubstitutionPR EqSubstRightRuleNat

ProofRuleEqSubstRightCheckingBranchData : Set₁
ProofRuleEqSubstRightCheckingBranchData =
  ProofRuleEqualitySubstitutionCheckingBranchData EqSubstRightRuleNat

proofRuleEqSubstRightTargetedBranch :
  ProofRuleEqSubstRightCheckingBranchData →
  TargetedProofCheckingBranchPR EqSubstRightRuleNat
proofRuleEqSubstRightTargetedBranch =
  proofRuleEqualitySubstitutionTargetedBranch
    eqSubstRightRuleNat-to-decoded

EqSubstSucRightFormula : Term → Term → Term → Formula
EqSubstSucRightFormula a b y =
  a ≈ b ⇒ (y ≈ sucᵗ a ⇒ y ≈ sucᵗ b)

EqSubstSucRightProofCode : Term → Term → Term → ℕ
EqSubstSucRightProofCode a b y =
  encodeCode
    (node 36
      (canonicalCodeTerm a ∷
       canonicalCodeTerm b ∷
       canonicalCodeTerm y ∷
       []))

EqSubstSucRightRuleNat : ℕ → ℕ → Set
EqSubstSucRightRuleNat proof-code formula-code =
  Σ Term
    (λ a →
      Σ Term
        (λ b →
          Σ Term
            (λ y →
              (proof-code ≡ EqSubstSucRightProofCode a b y) ×
              (formula-code ≡
               canonicalNatFormula (EqSubstSucRightFormula a b y)))))

eqSubstSucRightRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  EqSubstSucRightRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
eqSubstSucRightRuleNat-to-decoded
  (a ,Σ (b ,Σ (y ,Σ (proof-eq ,× formula-eq)))) =
  node 36
    (canonicalCodeTerm a ∷
     canonicalCodeTerm b ∷
     canonicalCodeTerm y ∷
     [])
  ,Σ
  (EqSubstSucRightFormula a b y ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 36
          (canonicalCodeTerm a ∷
           canonicalCodeTerm b ∷
           canonicalCodeTerm y ∷
           []))
      ≡
      just (EqSubstSucRightFormula a b y)
    check-eq
      rewrite decodeCanonicalTerm-roundTrip a
            | decodeCanonicalTerm-roundTrip b
            | decodeCanonicalTerm-roundTrip y =
      refl

ProofRuleEqSubstSucRightPR : Set₁
ProofRuleEqSubstSucRightPR =
  ProofRuleEqualitySubstitutionPR EqSubstSucRightRuleNat

ProofRuleEqSubstSucRightCheckingBranchData : Set₁
ProofRuleEqSubstSucRightCheckingBranchData =
  ProofRuleEqualitySubstitutionCheckingBranchData EqSubstSucRightRuleNat

proofRuleEqSubstSucRightTargetedBranch :
  ProofRuleEqSubstSucRightCheckingBranchData →
  TargetedProofCheckingBranchPR EqSubstSucRightRuleNat
proofRuleEqSubstSucRightTargetedBranch =
  proofRuleEqualitySubstitutionTargetedBranch
    eqSubstSucRightRuleNat-to-decoded
