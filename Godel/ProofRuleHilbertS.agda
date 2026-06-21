{-# OPTIONS --safe #-}

module Godel.ProofRuleHilbertS where

open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.CanonicalCoding
  using
    ( canonicalCodeFormula
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
    )
open import Godel.ProofCheckingBranch
open import Godel.ProofCheckingPR
  using (proofCodeArgs)
open import Godel.ProofCheckingPRTargets
  using (DecodedExecutableProofCodeNat)
open import Godel.ProofRuleFixedProofOr
  using (NonzeroNat)

-- Semantic target for proof-rule tag 2:
--
--   hilbert-S : (A => B => C) => (A => B) => A => C

HilbertSFormula : Formula → Formula → Formula → Formula
HilbertSFormula A B C =
  (A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C))

HilbertSRuleNat : ℕ → ℕ → Set
HilbertSRuleNat proof-code formula-code =
  Σ Formula
    (λ A →
      Σ Formula
        (λ B →
          Σ Formula
            (λ C →
              (proof-code ≡
               encodeCode
                (node 2
                  (canonicalCodeFormula A ∷
                   canonicalCodeFormula B ∷
                   canonicalCodeFormula C ∷
                   []))) ×
              (formula-code ≡ canonicalNatFormula (HilbertSFormula A B C)))))

hilbertSRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  HilbertSRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
hilbertSRuleNat-to-decoded
  (A ,Σ (B ,Σ (C ,Σ (proof-eq ,× formula-eq)))) =
  node 2
    (canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     canonicalCodeFormula C ∷
     [])
  ,Σ
  (HilbertSFormula A B C ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 2
          (canonicalCodeFormula A ∷
           canonicalCodeFormula B ∷
           canonicalCodeFormula C ∷
           []))
      ≡
      just (HilbertSFormula A B C)
    check-eq
      rewrite decodeCanonicalFormula-roundTrip A
            | decodeCanonicalFormula-roundTrip B
            | decodeCanonicalFormula-roundTrip C =
      refl

record ProofRuleHilbertSPR : Set₁ where
  field
    hilbertS-pr :
      PRRel (suc (suc zero))

    hilbertS-complete :
      {proof-code formula-code : ℕ} →
      HilbertSRuleNat proof-code formula-code →
      PRRel-holds hilbertS-pr (proofCodeArgs proof-code formula-code)

    hilbertS-sound :
      {proof-code formula-code : ℕ} →
      PRRel-holds hilbertS-pr (proofCodeArgs proof-code formula-code) →
      HilbertSRuleNat proof-code formula-code

proofRuleHilbertSPR-to-decoded :
  (D : ProofRuleHilbertSPR) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (ProofRuleHilbertSPR.hilbertS-pr D)
    (proofCodeArgs proof-code formula-code) →
  DecodedExecutableProofCodeNat proof-code formula-code
proofRuleHilbertSPR-to-decoded D holds =
  hilbertSRuleNat-to-decoded
    (ProofRuleHilbertSPR.hilbertS-sound D holds)

proofRuleHilbertSPR-represented :
  (D : ProofRuleHilbertSPR) →
  PARepresentsRelation (ProofRuleHilbertSPR.hilbertS-pr D)
proofRuleHilbertSPR-represented D =
  prrel-represented (ProofRuleHilbertSPR.hilbertS-pr D)

record ProofRuleHilbertSCheckingBranchData : Set₁ where
  field
    hilbertS-pr-data :
      ProofRuleHilbertSPR

    hilbertS-nonzero-sound :
      {proof-code formula-code : ℕ} →
      NonzeroNat
        (evalPRF
          (PRRel.characteristic
            (ProofRuleHilbertSPR.hilbertS-pr hilbertS-pr-data))
          (proofCodeArgs proof-code formula-code)) →
      HilbertSRuleNat proof-code formula-code

proofRuleHilbertSCheckingBranch :
  ProofRuleHilbertSCheckingBranchData →
  ProofCheckingBranchPR
proofRuleHilbertSCheckingBranch D = record
  { branch-pr =
      ProofRuleHilbertSPR.hilbertS-pr
        (ProofRuleHilbertSCheckingBranchData.hilbertS-pr-data D)
  ; branch-sound-decoded =
      proofRuleHilbertSPR-to-decoded
        (ProofRuleHilbertSCheckingBranchData.hilbertS-pr-data D)
  ; branch-nonzero-sound-decoded =
      λ nonzero →
        hilbertSRuleNat-to-decoded
          (ProofRuleHilbertSCheckingBranchData.hilbertS-nonzero-sound
            D
            nonzero)
  }

proofRuleHilbertSTargetedBranch :
  ProofRuleHilbertSCheckingBranchData →
  TargetedProofCheckingBranchPR HilbertSRuleNat
proofRuleHilbertSTargetedBranch D = record
  { branch =
      proofRuleHilbertSCheckingBranch D
  ; branch-complete-target =
      ProofRuleHilbertSPR.hilbertS-complete
        (ProofRuleHilbertSCheckingBranchData.hilbertS-pr-data D)
  }
