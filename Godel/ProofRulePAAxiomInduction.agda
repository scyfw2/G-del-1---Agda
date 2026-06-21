{-# OPTIONS --safe #-}

module Godel.ProofRulePAAxiomInduction where

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
open import Godel.PA
  using (induction)
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

-- Semantic target for the parameterized PA induction axiom branch:
--
--   proof-code = node 0 (node 6 (formula-code) :: [])
--   formula    = induction A
--
-- The six non-parameterized PA axioms remain represented by fixed code leaves.

InductionAxiomProofCode : Formula → ℕ
InductionAxiomProofCode A =
  encodeCode
    (node 0
      (node 6
        (canonicalCodeFormula A ∷
         [])
       ∷ []))

InductionAxiomRuleNat : ℕ → ℕ → Set
InductionAxiomRuleNat proof-code formula-code =
  Σ Formula
    (λ A →
      (proof-code ≡ InductionAxiomProofCode A) ×
      (formula-code ≡ canonicalNatFormula (induction A)))

inductionAxiomRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  InductionAxiomRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
inductionAxiomRuleNat-to-decoded
  (A ,Σ (proof-eq ,× formula-eq)) =
  node 0
    (node 6
      (canonicalCodeFormula A ∷
       [])
     ∷ [])
  ,Σ
  (induction A ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 0
          (node 6
            (canonicalCodeFormula A ∷
             [])
           ∷ []))
      ≡
      just (induction A)
    check-eq
      rewrite decodeCanonicalFormula-roundTrip A =
      refl

record ProofRuleInductionAxiomPR : Set₁ where
  field
    induction-axiom-pr :
      PRRel (suc (suc zero))

    induction-axiom-complete :
      {proof-code formula-code : ℕ} →
      InductionAxiomRuleNat proof-code formula-code →
      PRRel-holds induction-axiom-pr (proofCodeArgs proof-code formula-code)

    induction-axiom-sound :
      {proof-code formula-code : ℕ} →
      PRRel-holds induction-axiom-pr (proofCodeArgs proof-code formula-code) →
      InductionAxiomRuleNat proof-code formula-code

proofRuleInductionAxiomPR-represented :
  (D : ProofRuleInductionAxiomPR) →
  PARepresentsRelation (ProofRuleInductionAxiomPR.induction-axiom-pr D)
proofRuleInductionAxiomPR-represented D =
  prrel-represented (ProofRuleInductionAxiomPR.induction-axiom-pr D)

record ProofRuleInductionAxiomCheckingBranchData : Set₁ where
  field
    induction-axiom-pr-data :
      ProofRuleInductionAxiomPR

    induction-axiom-nonzero-sound :
      {proof-code formula-code : ℕ} →
      NonzeroNat
        (evalPRF
          (PRRel.characteristic
            (ProofRuleInductionAxiomPR.induction-axiom-pr
              induction-axiom-pr-data))
          (proofCodeArgs proof-code formula-code)) →
      InductionAxiomRuleNat proof-code formula-code

proofRuleInductionAxiomCheckingBranch :
  ProofRuleInductionAxiomCheckingBranchData →
  ProofCheckingBranchPR
proofRuleInductionAxiomCheckingBranch D = record
  { branch-pr =
      ProofRuleInductionAxiomPR.induction-axiom-pr
        (ProofRuleInductionAxiomCheckingBranchData.induction-axiom-pr-data D)
  ; branch-sound-decoded =
      λ holds →
        inductionAxiomRuleNat-to-decoded
          (ProofRuleInductionAxiomPR.induction-axiom-sound
            (ProofRuleInductionAxiomCheckingBranchData.induction-axiom-pr-data D)
            holds)
  ; branch-nonzero-sound-decoded =
      λ nonzero →
        inductionAxiomRuleNat-to-decoded
          (ProofRuleInductionAxiomCheckingBranchData.induction-axiom-nonzero-sound
            D
            nonzero)
  }

proofRuleInductionAxiomTargetedBranch :
  ProofRuleInductionAxiomCheckingBranchData →
  TargetedProofCheckingBranchPR InductionAxiomRuleNat
proofRuleInductionAxiomTargetedBranch D = record
  { branch =
      proofRuleInductionAxiomCheckingBranch D
  ; branch-complete-target =
      ProofRuleInductionAxiomPR.induction-axiom-complete
        (ProofRuleInductionAxiomCheckingBranchData.induction-axiom-pr-data D)
  }
