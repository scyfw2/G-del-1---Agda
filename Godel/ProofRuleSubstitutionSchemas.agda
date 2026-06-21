{-# OPTIONS --safe #-}

module Godel.ProofRuleSubstitutionSchemas where

open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.CanonicalCoding
  using
    ( canonicalCodeFormula
    ; canonicalCodeTerm
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
    ; decodeCanonicalFormula-roundTrip
    ; decodeCanonicalTerm-roundTrip
    )
open import Godel.ProofCheckingBranch
open import Godel.ProofCheckingPR
  using (proofCodeArgs)
open import Godel.ProofCheckingPRTargets
  using (DecodedExecutableProofCodeNat)
open import Godel.ProofRuleFixedProofOr
  using (NonzeroNat)

-- Targets for formula/term substitution schema rules:
--
--   tag 6 forall-eliminate
--   tag 7 exists-introduce

record ProofRuleSubstitutionPR
    (Target : ℕ → ℕ → Set) :
    Set₁ where
  field
    substitution-pr :
      PRRel (suc (suc zero))

    substitution-complete :
      {proof-code formula-code : ℕ} →
      Target proof-code formula-code →
      PRRel-holds substitution-pr (proofCodeArgs proof-code formula-code)

    substitution-sound :
      {proof-code formula-code : ℕ} →
      PRRel-holds substitution-pr (proofCodeArgs proof-code formula-code) →
      Target proof-code formula-code

proofRuleSubstitutionPR-represented :
  {Target : ℕ → ℕ → Set} →
  (D : ProofRuleSubstitutionPR Target) →
  PARepresentsRelation (ProofRuleSubstitutionPR.substitution-pr D)
proofRuleSubstitutionPR-represented D =
  prrel-represented (ProofRuleSubstitutionPR.substitution-pr D)

record ProofRuleSubstitutionCheckingBranchData
    (Target : ℕ → ℕ → Set) :
    Set₁ where
  field
    substitution-pr-data :
      ProofRuleSubstitutionPR Target

    substitution-nonzero-sound :
      {proof-code formula-code : ℕ} →
      NonzeroNat
        (evalPRF
          (PRRel.characteristic
            (ProofRuleSubstitutionPR.substitution-pr substitution-pr-data))
          (proofCodeArgs proof-code formula-code)) →
      Target proof-code formula-code

proofRuleSubstitutionCheckingBranch :
  {Target : ℕ → ℕ → Set} →
  ({proof-code formula-code : ℕ} →
   Target proof-code formula-code →
   DecodedExecutableProofCodeNat proof-code formula-code) →
  ProofRuleSubstitutionCheckingBranchData Target →
  ProofCheckingBranchPR
proofRuleSubstitutionCheckingBranch target-to-decoded D = record
  { branch-pr =
      ProofRuleSubstitutionPR.substitution-pr
        (ProofRuleSubstitutionCheckingBranchData.substitution-pr-data D)
  ; branch-sound-decoded =
      λ holds →
        target-to-decoded
          (ProofRuleSubstitutionPR.substitution-sound
            (ProofRuleSubstitutionCheckingBranchData.substitution-pr-data D)
            holds)
  ; branch-nonzero-sound-decoded =
      λ nonzero →
        target-to-decoded
          (ProofRuleSubstitutionCheckingBranchData.substitution-nonzero-sound
            D
            nonzero)
  }

proofRuleSubstitutionTargetedBranch :
  {Target : ℕ → ℕ → Set} →
  ({proof-code formula-code : ℕ} →
   Target proof-code formula-code →
   DecodedExecutableProofCodeNat proof-code formula-code) →
  ProofRuleSubstitutionCheckingBranchData Target →
  TargetedProofCheckingBranchPR Target
proofRuleSubstitutionTargetedBranch target-to-decoded D = record
  { branch =
      proofRuleSubstitutionCheckingBranch target-to-decoded D
  ; branch-complete-target =
      ProofRuleSubstitutionPR.substitution-complete
        (ProofRuleSubstitutionCheckingBranchData.substitution-pr-data D)
  }

forallEliminateProofCode : Formula → Term → ℕ
forallEliminateProofCode A t =
  encodeCode
    (node 6
      (canonicalCodeFormula A ∷
       canonicalCodeTerm t ∷
       []))

ForallEliminateFormula : Formula → Term → Formula
ForallEliminateFormula A t =
  (∀ᶠ A) ⇒ subst0 t A

ForallEliminateRuleNat : ℕ → ℕ → Set
ForallEliminateRuleNat proof-code formula-code =
  Σ Formula
    (λ A →
      Σ Term
        (λ t →
          (proof-code ≡ forallEliminateProofCode A t) ×
          (formula-code ≡ canonicalNatFormula (ForallEliminateFormula A t))))

forallEliminateRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  ForallEliminateRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
forallEliminateRuleNat-to-decoded
  (A ,Σ (t ,Σ (proof-eq ,× formula-eq))) =
  node 6
    (canonicalCodeFormula A ∷
     canonicalCodeTerm t ∷
     [])
  ,Σ
  (ForallEliminateFormula A t ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 6
          (canonicalCodeFormula A ∷
           canonicalCodeTerm t ∷
           []))
      ≡
      just (ForallEliminateFormula A t)
    check-eq
      rewrite decodeCanonicalFormula-roundTrip A
            | decodeCanonicalTerm-roundTrip t =
      refl

ProofRuleForallEliminatePR : Set₁
ProofRuleForallEliminatePR =
  ProofRuleSubstitutionPR ForallEliminateRuleNat

ProofRuleForallEliminateCheckingBranchData : Set₁
ProofRuleForallEliminateCheckingBranchData =
  ProofRuleSubstitutionCheckingBranchData ForallEliminateRuleNat

proofRuleForallEliminateTargetedBranch :
  ProofRuleForallEliminateCheckingBranchData →
  TargetedProofCheckingBranchPR ForallEliminateRuleNat
proofRuleForallEliminateTargetedBranch =
  proofRuleSubstitutionTargetedBranch forallEliminateRuleNat-to-decoded

existsIntroduceProofCode : Formula → Term → ℕ
existsIntroduceProofCode A t =
  encodeCode
    (node 7
      (canonicalCodeFormula A ∷
       canonicalCodeTerm t ∷
       []))

ExistsIntroduceFormula : Formula → Term → Formula
ExistsIntroduceFormula A t =
  subst0 t A ⇒ ∃ᶠ A

ExistsIntroduceRuleNat : ℕ → ℕ → Set
ExistsIntroduceRuleNat proof-code formula-code =
  Σ Formula
    (λ A →
      Σ Term
        (λ t →
          (proof-code ≡ existsIntroduceProofCode A t) ×
          (formula-code ≡ canonicalNatFormula (ExistsIntroduceFormula A t))))

existsIntroduceRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  ExistsIntroduceRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
existsIntroduceRuleNat-to-decoded
  (A ,Σ (t ,Σ (proof-eq ,× formula-eq))) =
  node 7
    (canonicalCodeFormula A ∷
     canonicalCodeTerm t ∷
     [])
  ,Σ
  (ExistsIntroduceFormula A t ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 7
          (canonicalCodeFormula A ∷
           canonicalCodeTerm t ∷
           []))
      ≡
      just (ExistsIntroduceFormula A t)
    check-eq
      rewrite decodeCanonicalFormula-roundTrip A
            | decodeCanonicalTerm-roundTrip t =
      refl

ProofRuleExistsIntroducePR : Set₁
ProofRuleExistsIntroducePR =
  ProofRuleSubstitutionPR ExistsIntroduceRuleNat

ProofRuleExistsIntroduceCheckingBranchData : Set₁
ProofRuleExistsIntroduceCheckingBranchData =
  ProofRuleSubstitutionCheckingBranchData ExistsIntroduceRuleNat

proofRuleExistsIntroduceTargetedBranch :
  ProofRuleExistsIntroduceCheckingBranchData →
  TargetedProofCheckingBranchPR ExistsIntroduceRuleNat
proofRuleExistsIntroduceTargetedBranch =
  proofRuleSubstitutionTargetedBranch existsIntroduceRuleNat-to-decoded
