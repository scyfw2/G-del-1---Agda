{-# OPTIONS --safe #-}

module Godel.ProofRuleLogicalConnectives where

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

-- Targets for the simple logical connective proof rules.

binaryFormulaProofCode : ℕ → Formula → Formula → ℕ
binaryFormulaProofCode tag A B =
  encodeCode
    (node tag
      (canonicalCodeFormula A ∷
       canonicalCodeFormula B ∷
       []))

AndIntroFormula : Formula → Formula → Formula
AndIntroFormula A B =
  A ⇒ (B ⇒ (A ∧ B))

AndIntroRuleNat : ℕ → ℕ → Set
AndIntroRuleNat proof-code formula-code =
  Σ Formula
    (λ A →
      Σ Formula
        (λ B →
          (proof-code ≡ binaryFormulaProofCode 19 A B) ×
          (formula-code ≡ canonicalNatFormula (AndIntroFormula A B))))

andIntroRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  AndIntroRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
andIntroRuleNat-to-decoded
  (A ,Σ (B ,Σ (proof-eq ,× formula-eq))) =
  node 19
    (canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     [])
  ,Σ
  (AndIntroFormula A B ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 19
          (canonicalCodeFormula A ∷
           canonicalCodeFormula B ∷
           []))
      ≡
      just (AndIntroFormula A B)
    check-eq
      rewrite decodeCanonicalFormula-roundTrip A
            | decodeCanonicalFormula-roundTrip B =
      refl

record ProofRuleAndIntroPR : Set₁ where
  field
    andIntro-pr :
      PRRel (suc (suc zero))

    andIntro-complete :
      {proof-code formula-code : ℕ} →
      AndIntroRuleNat proof-code formula-code →
      PRRel-holds andIntro-pr (proofCodeArgs proof-code formula-code)

    andIntro-sound :
      {proof-code formula-code : ℕ} →
      PRRel-holds andIntro-pr (proofCodeArgs proof-code formula-code) →
      AndIntroRuleNat proof-code formula-code

proofRuleAndIntroPR-to-decoded :
  (D : ProofRuleAndIntroPR) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (ProofRuleAndIntroPR.andIntro-pr D)
    (proofCodeArgs proof-code formula-code) →
  DecodedExecutableProofCodeNat proof-code formula-code
proofRuleAndIntroPR-to-decoded D holds =
  andIntroRuleNat-to-decoded
    (ProofRuleAndIntroPR.andIntro-sound D holds)

proofRuleAndIntroPR-represented :
  (D : ProofRuleAndIntroPR) →
  PARepresentsRelation (ProofRuleAndIntroPR.andIntro-pr D)
proofRuleAndIntroPR-represented D =
  prrel-represented (ProofRuleAndIntroPR.andIntro-pr D)

record ProofRuleAndIntroCheckingBranchData : Set₁ where
  field
    andIntro-pr-data :
      ProofRuleAndIntroPR

    andIntro-nonzero-sound :
      {proof-code formula-code : ℕ} →
      NonzeroNat
        (evalPRF
          (PRRel.characteristic
            (ProofRuleAndIntroPR.andIntro-pr andIntro-pr-data))
          (proofCodeArgs proof-code formula-code)) →
      AndIntroRuleNat proof-code formula-code

proofRuleAndIntroCheckingBranch :
  ProofRuleAndIntroCheckingBranchData →
  ProofCheckingBranchPR
proofRuleAndIntroCheckingBranch D = record
  { branch-pr =
      ProofRuleAndIntroPR.andIntro-pr
        (ProofRuleAndIntroCheckingBranchData.andIntro-pr-data D)
  ; branch-sound-decoded =
      proofRuleAndIntroPR-to-decoded
        (ProofRuleAndIntroCheckingBranchData.andIntro-pr-data D)
  ; branch-nonzero-sound-decoded =
      λ nonzero →
        andIntroRuleNat-to-decoded
          (ProofRuleAndIntroCheckingBranchData.andIntro-nonzero-sound
            D
            nonzero)
  }

proofRuleAndIntroTargetedBranch :
  ProofRuleAndIntroCheckingBranchData →
  TargetedProofCheckingBranchPR AndIntroRuleNat
proofRuleAndIntroTargetedBranch D = record
  { branch =
      proofRuleAndIntroCheckingBranch D
  ; branch-complete-target =
      ProofRuleAndIntroPR.andIntro-complete
        (ProofRuleAndIntroCheckingBranchData.andIntro-pr-data D)
  }

AndElimLeftFormula : Formula → Formula → Formula
AndElimLeftFormula A B =
  (A ∧ B) ⇒ A

AndElimLeftRuleNat : ℕ → ℕ → Set
AndElimLeftRuleNat proof-code formula-code =
  Σ Formula
    (λ A →
      Σ Formula
        (λ B →
          (proof-code ≡ binaryFormulaProofCode 20 A B) ×
          (formula-code ≡ canonicalNatFormula (AndElimLeftFormula A B))))

andElimLeftRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  AndElimLeftRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
andElimLeftRuleNat-to-decoded
  (A ,Σ (B ,Σ (proof-eq ,× formula-eq))) =
  node 20
    (canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     [])
  ,Σ
  (AndElimLeftFormula A B ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 20
          (canonicalCodeFormula A ∷
           canonicalCodeFormula B ∷
           []))
      ≡
      just (AndElimLeftFormula A B)
    check-eq
      rewrite decodeCanonicalFormula-roundTrip A
            | decodeCanonicalFormula-roundTrip B =
      refl

record ProofRuleAndElimLeftPR : Set₁ where
  field
    andElimLeft-pr :
      PRRel (suc (suc zero))

    andElimLeft-complete :
      {proof-code formula-code : ℕ} →
      AndElimLeftRuleNat proof-code formula-code →
      PRRel-holds andElimLeft-pr (proofCodeArgs proof-code formula-code)

    andElimLeft-sound :
      {proof-code formula-code : ℕ} →
      PRRel-holds andElimLeft-pr (proofCodeArgs proof-code formula-code) →
      AndElimLeftRuleNat proof-code formula-code

proofRuleAndElimLeftPR-to-decoded :
  (D : ProofRuleAndElimLeftPR) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (ProofRuleAndElimLeftPR.andElimLeft-pr D)
    (proofCodeArgs proof-code formula-code) →
  DecodedExecutableProofCodeNat proof-code formula-code
proofRuleAndElimLeftPR-to-decoded D holds =
  andElimLeftRuleNat-to-decoded
    (ProofRuleAndElimLeftPR.andElimLeft-sound D holds)

proofRuleAndElimLeftPR-represented :
  (D : ProofRuleAndElimLeftPR) →
  PARepresentsRelation (ProofRuleAndElimLeftPR.andElimLeft-pr D)
proofRuleAndElimLeftPR-represented D =
  prrel-represented (ProofRuleAndElimLeftPR.andElimLeft-pr D)

record ProofRuleAndElimLeftCheckingBranchData : Set₁ where
  field
    andElimLeft-pr-data :
      ProofRuleAndElimLeftPR

    andElimLeft-nonzero-sound :
      {proof-code formula-code : ℕ} →
      NonzeroNat
        (evalPRF
          (PRRel.characteristic
            (ProofRuleAndElimLeftPR.andElimLeft-pr andElimLeft-pr-data))
          (proofCodeArgs proof-code formula-code)) →
      AndElimLeftRuleNat proof-code formula-code

proofRuleAndElimLeftCheckingBranch :
  ProofRuleAndElimLeftCheckingBranchData →
  ProofCheckingBranchPR
proofRuleAndElimLeftCheckingBranch D = record
  { branch-pr =
      ProofRuleAndElimLeftPR.andElimLeft-pr
        (ProofRuleAndElimLeftCheckingBranchData.andElimLeft-pr-data D)
  ; branch-sound-decoded =
      proofRuleAndElimLeftPR-to-decoded
        (ProofRuleAndElimLeftCheckingBranchData.andElimLeft-pr-data D)
  ; branch-nonzero-sound-decoded =
      λ nonzero →
        andElimLeftRuleNat-to-decoded
          (ProofRuleAndElimLeftCheckingBranchData.andElimLeft-nonzero-sound
            D
            nonzero)
  }

proofRuleAndElimLeftTargetedBranch :
  ProofRuleAndElimLeftCheckingBranchData →
  TargetedProofCheckingBranchPR AndElimLeftRuleNat
proofRuleAndElimLeftTargetedBranch D = record
  { branch =
      proofRuleAndElimLeftCheckingBranch D
  ; branch-complete-target =
      ProofRuleAndElimLeftPR.andElimLeft-complete
        (ProofRuleAndElimLeftCheckingBranchData.andElimLeft-pr-data D)
  }

AndElimRightFormula : Formula → Formula → Formula
AndElimRightFormula A B =
  (A ∧ B) ⇒ B

AndElimRightRuleNat : ℕ → ℕ → Set
AndElimRightRuleNat proof-code formula-code =
  Σ Formula
    (λ A →
      Σ Formula
        (λ B →
          (proof-code ≡ binaryFormulaProofCode 21 A B) ×
          (formula-code ≡ canonicalNatFormula (AndElimRightFormula A B))))

andElimRightRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  AndElimRightRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
andElimRightRuleNat-to-decoded
  (A ,Σ (B ,Σ (proof-eq ,× formula-eq))) =
  node 21
    (canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     [])
  ,Σ
  (AndElimRightFormula A B ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 21
          (canonicalCodeFormula A ∷
           canonicalCodeFormula B ∷
           []))
      ≡
      just (AndElimRightFormula A B)
    check-eq
      rewrite decodeCanonicalFormula-roundTrip A
            | decodeCanonicalFormula-roundTrip B =
      refl

record ProofRuleAndElimRightPR : Set₁ where
  field
    andElimRight-pr :
      PRRel (suc (suc zero))

    andElimRight-complete :
      {proof-code formula-code : ℕ} →
      AndElimRightRuleNat proof-code formula-code →
      PRRel-holds andElimRight-pr (proofCodeArgs proof-code formula-code)

    andElimRight-sound :
      {proof-code formula-code : ℕ} →
      PRRel-holds andElimRight-pr (proofCodeArgs proof-code formula-code) →
      AndElimRightRuleNat proof-code formula-code

proofRuleAndElimRightPR-to-decoded :
  (D : ProofRuleAndElimRightPR) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (ProofRuleAndElimRightPR.andElimRight-pr D)
    (proofCodeArgs proof-code formula-code) →
  DecodedExecutableProofCodeNat proof-code formula-code
proofRuleAndElimRightPR-to-decoded D holds =
  andElimRightRuleNat-to-decoded
    (ProofRuleAndElimRightPR.andElimRight-sound D holds)

proofRuleAndElimRightPR-represented :
  (D : ProofRuleAndElimRightPR) →
  PARepresentsRelation (ProofRuleAndElimRightPR.andElimRight-pr D)
proofRuleAndElimRightPR-represented D =
  prrel-represented (ProofRuleAndElimRightPR.andElimRight-pr D)

record ProofRuleAndElimRightCheckingBranchData : Set₁ where
  field
    andElimRight-pr-data :
      ProofRuleAndElimRightPR

    andElimRight-nonzero-sound :
      {proof-code formula-code : ℕ} →
      NonzeroNat
        (evalPRF
          (PRRel.characteristic
            (ProofRuleAndElimRightPR.andElimRight-pr andElimRight-pr-data))
          (proofCodeArgs proof-code formula-code)) →
      AndElimRightRuleNat proof-code formula-code

proofRuleAndElimRightCheckingBranch :
  ProofRuleAndElimRightCheckingBranchData →
  ProofCheckingBranchPR
proofRuleAndElimRightCheckingBranch D = record
  { branch-pr =
      ProofRuleAndElimRightPR.andElimRight-pr
        (ProofRuleAndElimRightCheckingBranchData.andElimRight-pr-data D)
  ; branch-sound-decoded =
      proofRuleAndElimRightPR-to-decoded
        (ProofRuleAndElimRightCheckingBranchData.andElimRight-pr-data D)
  ; branch-nonzero-sound-decoded =
      λ nonzero →
        andElimRightRuleNat-to-decoded
          (ProofRuleAndElimRightCheckingBranchData.andElimRight-nonzero-sound
            D
            nonzero)
  }

proofRuleAndElimRightTargetedBranch :
  ProofRuleAndElimRightCheckingBranchData →
  TargetedProofCheckingBranchPR AndElimRightRuleNat
proofRuleAndElimRightTargetedBranch D = record
  { branch =
      proofRuleAndElimRightCheckingBranch D
  ; branch-complete-target =
      ProofRuleAndElimRightPR.andElimRight-complete
        (ProofRuleAndElimRightCheckingBranchData.andElimRight-pr-data D)
  }

OrIntroLeftFormula : Formula → Formula → Formula
OrIntroLeftFormula A B =
  A ⇒ (A ∨ B)

OrIntroLeftRuleNat : ℕ → ℕ → Set
OrIntroLeftRuleNat proof-code formula-code =
  Σ Formula
    (λ A →
      Σ Formula
        (λ B →
          (proof-code ≡ binaryFormulaProofCode 22 A B) ×
          (formula-code ≡ canonicalNatFormula (OrIntroLeftFormula A B))))

orIntroLeftRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  OrIntroLeftRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
orIntroLeftRuleNat-to-decoded
  (A ,Σ (B ,Σ (proof-eq ,× formula-eq))) =
  node 22
    (canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     [])
  ,Σ
  (OrIntroLeftFormula A B ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 22
          (canonicalCodeFormula A ∷
           canonicalCodeFormula B ∷
           []))
      ≡
      just (OrIntroLeftFormula A B)
    check-eq
      rewrite decodeCanonicalFormula-roundTrip A
            | decodeCanonicalFormula-roundTrip B =
      refl

record ProofRuleOrIntroLeftPR : Set₁ where
  field
    orIntroLeft-pr :
      PRRel (suc (suc zero))

    orIntroLeft-complete :
      {proof-code formula-code : ℕ} →
      OrIntroLeftRuleNat proof-code formula-code →
      PRRel-holds orIntroLeft-pr (proofCodeArgs proof-code formula-code)

    orIntroLeft-sound :
      {proof-code formula-code : ℕ} →
      PRRel-holds orIntroLeft-pr (proofCodeArgs proof-code formula-code) →
      OrIntroLeftRuleNat proof-code formula-code

proofRuleOrIntroLeftPR-to-decoded :
  (D : ProofRuleOrIntroLeftPR) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (ProofRuleOrIntroLeftPR.orIntroLeft-pr D)
    (proofCodeArgs proof-code formula-code) →
  DecodedExecutableProofCodeNat proof-code formula-code
proofRuleOrIntroLeftPR-to-decoded D holds =
  orIntroLeftRuleNat-to-decoded
    (ProofRuleOrIntroLeftPR.orIntroLeft-sound D holds)

proofRuleOrIntroLeftPR-represented :
  (D : ProofRuleOrIntroLeftPR) →
  PARepresentsRelation (ProofRuleOrIntroLeftPR.orIntroLeft-pr D)
proofRuleOrIntroLeftPR-represented D =
  prrel-represented (ProofRuleOrIntroLeftPR.orIntroLeft-pr D)

record ProofRuleOrIntroLeftCheckingBranchData : Set₁ where
  field
    orIntroLeft-pr-data :
      ProofRuleOrIntroLeftPR

    orIntroLeft-nonzero-sound :
      {proof-code formula-code : ℕ} →
      NonzeroNat
        (evalPRF
          (PRRel.characteristic
            (ProofRuleOrIntroLeftPR.orIntroLeft-pr orIntroLeft-pr-data))
          (proofCodeArgs proof-code formula-code)) →
      OrIntroLeftRuleNat proof-code formula-code

proofRuleOrIntroLeftCheckingBranch :
  ProofRuleOrIntroLeftCheckingBranchData →
  ProofCheckingBranchPR
proofRuleOrIntroLeftCheckingBranch D = record
  { branch-pr =
      ProofRuleOrIntroLeftPR.orIntroLeft-pr
        (ProofRuleOrIntroLeftCheckingBranchData.orIntroLeft-pr-data D)
  ; branch-sound-decoded =
      proofRuleOrIntroLeftPR-to-decoded
        (ProofRuleOrIntroLeftCheckingBranchData.orIntroLeft-pr-data D)
  ; branch-nonzero-sound-decoded =
      λ nonzero →
        orIntroLeftRuleNat-to-decoded
          (ProofRuleOrIntroLeftCheckingBranchData.orIntroLeft-nonzero-sound
            D
            nonzero)
  }

proofRuleOrIntroLeftTargetedBranch :
  ProofRuleOrIntroLeftCheckingBranchData →
  TargetedProofCheckingBranchPR OrIntroLeftRuleNat
proofRuleOrIntroLeftTargetedBranch D = record
  { branch =
      proofRuleOrIntroLeftCheckingBranch D
  ; branch-complete-target =
      ProofRuleOrIntroLeftPR.orIntroLeft-complete
        (ProofRuleOrIntroLeftCheckingBranchData.orIntroLeft-pr-data D)
  }

OrIntroRightFormula : Formula → Formula → Formula
OrIntroRightFormula A B =
  B ⇒ (A ∨ B)

OrIntroRightRuleNat : ℕ → ℕ → Set
OrIntroRightRuleNat proof-code formula-code =
  Σ Formula
    (λ A →
      Σ Formula
        (λ B →
          (proof-code ≡ binaryFormulaProofCode 23 A B) ×
          (formula-code ≡ canonicalNatFormula (OrIntroRightFormula A B))))

orIntroRightRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  OrIntroRightRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
orIntroRightRuleNat-to-decoded
  (A ,Σ (B ,Σ (proof-eq ,× formula-eq))) =
  node 23
    (canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     [])
  ,Σ
  (OrIntroRightFormula A B ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 23
          (canonicalCodeFormula A ∷
           canonicalCodeFormula B ∷
           []))
      ≡
      just (OrIntroRightFormula A B)
    check-eq
      rewrite decodeCanonicalFormula-roundTrip A
            | decodeCanonicalFormula-roundTrip B =
      refl

record ProofRuleOrIntroRightPR : Set₁ where
  field
    orIntroRight-pr :
      PRRel (suc (suc zero))

    orIntroRight-complete :
      {proof-code formula-code : ℕ} →
      OrIntroRightRuleNat proof-code formula-code →
      PRRel-holds orIntroRight-pr (proofCodeArgs proof-code formula-code)

    orIntroRight-sound :
      {proof-code formula-code : ℕ} →
      PRRel-holds orIntroRight-pr (proofCodeArgs proof-code formula-code) →
      OrIntroRightRuleNat proof-code formula-code

proofRuleOrIntroRightPR-to-decoded :
  (D : ProofRuleOrIntroRightPR) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (ProofRuleOrIntroRightPR.orIntroRight-pr D)
    (proofCodeArgs proof-code formula-code) →
  DecodedExecutableProofCodeNat proof-code formula-code
proofRuleOrIntroRightPR-to-decoded D holds =
  orIntroRightRuleNat-to-decoded
    (ProofRuleOrIntroRightPR.orIntroRight-sound D holds)

proofRuleOrIntroRightPR-represented :
  (D : ProofRuleOrIntroRightPR) →
  PARepresentsRelation (ProofRuleOrIntroRightPR.orIntroRight-pr D)
proofRuleOrIntroRightPR-represented D =
  prrel-represented (ProofRuleOrIntroRightPR.orIntroRight-pr D)

record ProofRuleOrIntroRightCheckingBranchData : Set₁ where
  field
    orIntroRight-pr-data :
      ProofRuleOrIntroRightPR

    orIntroRight-nonzero-sound :
      {proof-code formula-code : ℕ} →
      NonzeroNat
        (evalPRF
          (PRRel.characteristic
            (ProofRuleOrIntroRightPR.orIntroRight-pr orIntroRight-pr-data))
          (proofCodeArgs proof-code formula-code)) →
      OrIntroRightRuleNat proof-code formula-code

proofRuleOrIntroRightCheckingBranch :
  ProofRuleOrIntroRightCheckingBranchData →
  ProofCheckingBranchPR
proofRuleOrIntroRightCheckingBranch D = record
  { branch-pr =
      ProofRuleOrIntroRightPR.orIntroRight-pr
        (ProofRuleOrIntroRightCheckingBranchData.orIntroRight-pr-data D)
  ; branch-sound-decoded =
      proofRuleOrIntroRightPR-to-decoded
        (ProofRuleOrIntroRightCheckingBranchData.orIntroRight-pr-data D)
  ; branch-nonzero-sound-decoded =
      λ nonzero →
        orIntroRightRuleNat-to-decoded
          (ProofRuleOrIntroRightCheckingBranchData.orIntroRight-nonzero-sound
            D
            nonzero)
  }

proofRuleOrIntroRightTargetedBranch :
  ProofRuleOrIntroRightCheckingBranchData →
  TargetedProofCheckingBranchPR OrIntroRightRuleNat
proofRuleOrIntroRightTargetedBranch D = record
  { branch =
      proofRuleOrIntroRightCheckingBranch D
  ; branch-complete-target =
      ProofRuleOrIntroRightPR.orIntroRight-complete
        (ProofRuleOrIntroRightCheckingBranchData.orIntroRight-pr-data D)
  }
