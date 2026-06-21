{-# OPTIONS --safe #-}

module Godel.ProofRuleHilbertK where

open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.CanonicalCoding
  using
    ( Code
    ; canonicalCodeFormula
    ; canonicalNatFormula
    ; encodeCode
    ; node
    )
open import Godel.PrimitiveRecursive
open import Godel.PRRepresentabilityFinal
  using (PARepresentsRelation; prrel-represented)
open import Godel.ProofCanonicalChecker
  using
    ( DecodedExecutableProofCodePA
    ; checkPAProofCode
    ; decodeCanonicalFormula-roundTrip
    )
open import Godel.ProofCheckingPR
  using (proofCodeArgs)
open import Godel.ProofCheckingPRTargets
  using (DecodedExecutableProofCodeNat)
open import Godel.ProofCheckingBranch
open import Godel.ProofRuleFixedProofOr
  using (NonzeroNat)

-- Semantic target for proof-rule tag 1:
--
--   hilbert-K : A => B => A
--
-- This is the theorem-facing target for the future PR branch.  The target is
-- intentionally stated with canonical formula children; a decoded proof-code
-- coverage proof can later use decoder no-junk lemmas to reduce arbitrary
-- successful children to this canonical shape.

HilbertKRuleNat : ℕ → ℕ → Set
HilbertKRuleNat proof-code formula-code =
  Σ Formula
    (λ A →
      Σ Formula
        (λ B →
          (proof-code ≡
           encodeCode
            (node 1
              (canonicalCodeFormula A ∷
               canonicalCodeFormula B ∷
               []))) ×
          (formula-code ≡ canonicalNatFormula (A ⇒ (B ⇒ A)))))

hilbertKRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  HilbertKRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
hilbertKRuleNat-to-decoded
  (A ,Σ (B ,Σ (proof-eq ,× formula-eq))) =
  node 1
    (canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     [])
  ,Σ
  (A ⇒ (B ⇒ A) ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 1
          (canonicalCodeFormula A ∷
           canonicalCodeFormula B ∷
           []))
      ≡
      just (A ⇒ (B ⇒ A))
    check-eq
      rewrite decodeCanonicalFormula-roundTrip A
            | decodeCanonicalFormula-roundTrip B =
      refl

record ProofRuleHilbertKPR : Set₁ where
  field
    hilbertK-pr :
      PRRel (suc (suc zero))

    hilbertK-complete :
      {proof-code formula-code : ℕ} →
      HilbertKRuleNat proof-code formula-code →
      PRRel-holds hilbertK-pr (proofCodeArgs proof-code formula-code)

    hilbertK-sound :
      {proof-code formula-code : ℕ} →
      PRRel-holds hilbertK-pr (proofCodeArgs proof-code formula-code) →
      HilbertKRuleNat proof-code formula-code

proofRuleHilbertKPR-to-decoded :
  (D : ProofRuleHilbertKPR) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (ProofRuleHilbertKPR.hilbertK-pr D)
    (proofCodeArgs proof-code formula-code) →
  DecodedExecutableProofCodeNat proof-code formula-code
proofRuleHilbertKPR-to-decoded D holds =
  hilbertKRuleNat-to-decoded
    (ProofRuleHilbertKPR.hilbertK-sound D holds)

proofRuleHilbertKPR-represented :
  (D : ProofRuleHilbertKPR) →
  PARepresentsRelation (ProofRuleHilbertKPR.hilbertK-pr D)
proofRuleHilbertKPR-represented D =
  prrel-represented (ProofRuleHilbertKPR.hilbertK-pr D)

record ProofRuleHilbertKCheckingBranchData : Set₁ where
  field
    hilbertK-pr-data :
      ProofRuleHilbertKPR

    hilbertK-nonzero-sound :
      {proof-code formula-code : ℕ} →
      NonzeroNat
        (evalPRF
          (PRRel.characteristic
            (ProofRuleHilbertKPR.hilbertK-pr hilbertK-pr-data))
          (proofCodeArgs proof-code formula-code)) →
      HilbertKRuleNat proof-code formula-code

proofRuleHilbertKCheckingBranch :
  ProofRuleHilbertKCheckingBranchData →
  ProofCheckingBranchPR
proofRuleHilbertKCheckingBranch D = record
  { branch-pr =
      ProofRuleHilbertKPR.hilbertK-pr
        (ProofRuleHilbertKCheckingBranchData.hilbertK-pr-data D)
  ; branch-sound-decoded =
      proofRuleHilbertKPR-to-decoded
        (ProofRuleHilbertKCheckingBranchData.hilbertK-pr-data D)
  ; branch-nonzero-sound-decoded =
      λ nonzero →
        hilbertKRuleNat-to-decoded
          (ProofRuleHilbertKCheckingBranchData.hilbertK-nonzero-sound
            D
            nonzero)
  }

proofRuleHilbertKTargetedBranch :
  ProofRuleHilbertKCheckingBranchData →
  TargetedProofCheckingBranchPR HilbertKRuleNat
proofRuleHilbertKTargetedBranch D = record
  { branch =
      proofRuleHilbertKCheckingBranch D
  ; branch-complete-target =
      ProofRuleHilbertKPR.hilbertK-complete
        (ProofRuleHilbertKCheckingBranchData.hilbertK-pr-data D)
  }
