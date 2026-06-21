{-# OPTIONS --safe #-}

module Godel.ProofRuleRecursiveSchemas where

open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.CanonicalCoding
  using
    ( Code
    ; canonicalNatFormula
    ; encodeCode
    ; node
    )
open import Godel.DecidableCoding
  using (formulaEq-refl)
open import Godel.PrimitiveRecursive
open import Godel.PRRepresentabilityFinal
  using (PARepresentsRelation; prrel-represented)
open import Godel.ProofCanonicalChecker
  using (checkPAProofCode)
open import Godel.ProofCheckingBranch
open import Godel.ProofCheckingPR
  using (proofCodeArgs)
open import Godel.ProofCheckingPRTargets
  using (DecodedExecutableProofCodeNat)
open import Godel.ProofRuleFixedProofOr
  using (NonzeroNat)

-- Recursive proof-rule targets:
--
--   tag 4 modus-ponens
--   tag 5 forall-generalize
--
-- These targets still mention checkPAProofCode for child proof codes.  They
-- are the semantic bridge that the eventual recursive numeric PR checker must
-- implement.

record ProofRuleRecursivePR
    (Target : ℕ → ℕ → Set) :
    Set₁ where
  field
    recursive-pr :
      PRRel (suc (suc zero))

    recursive-complete :
      {proof-code formula-code : ℕ} →
      Target proof-code formula-code →
      PRRel-holds recursive-pr (proofCodeArgs proof-code formula-code)

    recursive-sound :
      {proof-code formula-code : ℕ} →
      PRRel-holds recursive-pr (proofCodeArgs proof-code formula-code) →
      Target proof-code formula-code

proofRuleRecursivePR-represented :
  {Target : ℕ → ℕ → Set} →
  (D : ProofRuleRecursivePR Target) →
  PARepresentsRelation (ProofRuleRecursivePR.recursive-pr D)
proofRuleRecursivePR-represented D =
  prrel-represented (ProofRuleRecursivePR.recursive-pr D)

record ProofRuleRecursiveCheckingBranchData
    (Target : ℕ → ℕ → Set) :
    Set₁ where
  field
    recursive-pr-data :
      ProofRuleRecursivePR Target

    recursive-nonzero-sound :
      {proof-code formula-code : ℕ} →
      NonzeroNat
        (evalPRF
          (PRRel.characteristic
            (ProofRuleRecursivePR.recursive-pr recursive-pr-data))
          (proofCodeArgs proof-code formula-code)) →
      Target proof-code formula-code

proofRuleRecursiveCheckingBranch :
  {Target : ℕ → ℕ → Set} →
  ({proof-code formula-code : ℕ} →
   Target proof-code formula-code →
   DecodedExecutableProofCodeNat proof-code formula-code) →
  ProofRuleRecursiveCheckingBranchData Target →
  ProofCheckingBranchPR
proofRuleRecursiveCheckingBranch target-to-decoded D = record
  { branch-pr =
      ProofRuleRecursivePR.recursive-pr
        (ProofRuleRecursiveCheckingBranchData.recursive-pr-data D)
  ; branch-sound-decoded =
      λ holds →
        target-to-decoded
          (ProofRuleRecursivePR.recursive-sound
            (ProofRuleRecursiveCheckingBranchData.recursive-pr-data D)
            holds)
  ; branch-nonzero-sound-decoded =
      λ nonzero →
        target-to-decoded
          (ProofRuleRecursiveCheckingBranchData.recursive-nonzero-sound
            D
            nonzero)
  }

proofRuleRecursiveTargetedBranch :
  {Target : ℕ → ℕ → Set} →
  ({proof-code formula-code : ℕ} →
   Target proof-code formula-code →
   DecodedExecutableProofCodeNat proof-code formula-code) →
  ProofRuleRecursiveCheckingBranchData Target →
  TargetedProofCheckingBranchPR Target
proofRuleRecursiveTargetedBranch target-to-decoded D = record
  { branch =
      proofRuleRecursiveCheckingBranch target-to-decoded D
  ; branch-complete-target =
      ProofRuleRecursivePR.recursive-complete
        (ProofRuleRecursiveCheckingBranchData.recursive-pr-data D)
  }

ModusPonensRuleNat : ℕ → ℕ → Set
ModusPonensRuleNat proof-code formula-code =
  Σ Code
    (λ p →
      Σ Code
        (λ q →
          Σ Formula
            (λ A →
              Σ Formula
                (λ B →
                  (proof-code ≡ encodeCode (node 4 (p ∷ q ∷ []))) ×
                  ((formula-code ≡ canonicalNatFormula B) ×
                   ((checkPAProofCode p ≡ just (A ⇒ B)) ×
                    (checkPAProofCode q ≡ just A)))))))

modusPonensRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  ModusPonensRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
modusPonensRuleNat-to-decoded
  (p ,Σ (q ,Σ (A ,Σ (B ,Σ
    (proof-eq ,× (formula-eq ,× (p-check ,× q-check))))))) =
  node 4 (p ∷ q ∷ [])
  ,Σ
  (B ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode (node 4 (p ∷ q ∷ [])) ≡ just B
    check-eq
      rewrite p-check
            | q-check
            | formulaEq-refl A =
      refl

ForallGeneralizeRuleNat : ℕ → ℕ → Set
ForallGeneralizeRuleNat proof-code formula-code =
  Σ Code
    (λ p →
      Σ Formula
        (λ A →
          (proof-code ≡ encodeCode (node 5 (p ∷ []))) ×
          ((formula-code ≡ canonicalNatFormula (∀ᶠ A)) ×
           (checkPAProofCode p ≡ just A))))

forallGeneralizeRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  ForallGeneralizeRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
forallGeneralizeRuleNat-to-decoded
  (p ,Σ (A ,Σ (proof-eq ,× (formula-eq ,× p-check)))) =
  node 5 (p ∷ [])
  ,Σ
  (∀ᶠ A ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode (node 5 (p ∷ [])) ≡ just (∀ᶠ A)
    check-eq rewrite p-check = refl

ProofRuleModusPonensPR : Set₁
ProofRuleModusPonensPR =
  ProofRuleRecursivePR ModusPonensRuleNat

ProofRuleForallGeneralizePR : Set₁
ProofRuleForallGeneralizePR =
  ProofRuleRecursivePR ForallGeneralizeRuleNat

ProofRuleModusPonensCheckingBranchData : Set₁
ProofRuleModusPonensCheckingBranchData =
  ProofRuleRecursiveCheckingBranchData ModusPonensRuleNat

ProofRuleForallGeneralizeCheckingBranchData : Set₁
ProofRuleForallGeneralizeCheckingBranchData =
  ProofRuleRecursiveCheckingBranchData ForallGeneralizeRuleNat

proofRuleModusPonensTargetedBranch :
  ProofRuleModusPonensCheckingBranchData →
  TargetedProofCheckingBranchPR ModusPonensRuleNat
proofRuleModusPonensTargetedBranch =
  proofRuleRecursiveTargetedBranch modusPonensRuleNat-to-decoded

proofRuleForallGeneralizeTargetedBranch :
  ProofRuleForallGeneralizeCheckingBranchData →
  TargetedProofCheckingBranchPR ForallGeneralizeRuleNat
proofRuleForallGeneralizeTargetedBranch =
  proofRuleRecursiveTargetedBranch forallGeneralizeRuleNat-to-decoded
