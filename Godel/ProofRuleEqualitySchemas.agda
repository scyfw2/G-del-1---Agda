{-# OPTIONS --safe #-}

module Godel.ProofRuleEqualitySchemas where

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

-- Semantic targets for the non-recursive equality schema proof rules.

EqSymFormula : Term → Term → Formula
EqSymFormula s t =
  s ≈ t ⇒ t ≈ s

EqSymRuleNat : ℕ → ℕ → Set
EqSymRuleNat proof-code formula-code =
  Σ Term
    (λ s →
      Σ Term
        (λ t →
          (proof-code ≡
           encodeCode
            (node 9
              (canonicalCodeTerm s ∷
               canonicalCodeTerm t ∷
               []))) ×
          (formula-code ≡ canonicalNatFormula (EqSymFormula s t))))

eqSymRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  EqSymRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
eqSymRuleNat-to-decoded
  (s ,Σ (t ,Σ (proof-eq ,× formula-eq))) =
  node 9
    (canonicalCodeTerm s ∷
     canonicalCodeTerm t ∷
     [])
  ,Σ
  (EqSymFormula s t ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 9
          (canonicalCodeTerm s ∷
           canonicalCodeTerm t ∷
           []))
      ≡
      just (EqSymFormula s t)
    check-eq
      rewrite decodeCanonicalTerm-roundTrip s
            | decodeCanonicalTerm-roundTrip t =
      refl

record ProofRuleEqSymPR : Set₁ where
  field
    eqSym-pr :
      PRRel (suc (suc zero))

    eqSym-complete :
      {proof-code formula-code : ℕ} →
      EqSymRuleNat proof-code formula-code →
      PRRel-holds eqSym-pr (proofCodeArgs proof-code formula-code)

    eqSym-sound :
      {proof-code formula-code : ℕ} →
      PRRel-holds eqSym-pr (proofCodeArgs proof-code formula-code) →
      EqSymRuleNat proof-code formula-code

proofRuleEqSymPR-to-decoded :
  (D : ProofRuleEqSymPR) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (ProofRuleEqSymPR.eqSym-pr D)
    (proofCodeArgs proof-code formula-code) →
  DecodedExecutableProofCodeNat proof-code formula-code
proofRuleEqSymPR-to-decoded D holds =
  eqSymRuleNat-to-decoded
    (ProofRuleEqSymPR.eqSym-sound D holds)

proofRuleEqSymPR-represented :
  (D : ProofRuleEqSymPR) →
  PARepresentsRelation (ProofRuleEqSymPR.eqSym-pr D)
proofRuleEqSymPR-represented D =
  prrel-represented (ProofRuleEqSymPR.eqSym-pr D)

record ProofRuleEqSymCheckingBranchData : Set₁ where
  field
    eqSym-pr-data :
      ProofRuleEqSymPR

    eqSym-nonzero-sound :
      {proof-code formula-code : ℕ} →
      NonzeroNat
        (evalPRF
          (PRRel.characteristic
            (ProofRuleEqSymPR.eqSym-pr eqSym-pr-data))
          (proofCodeArgs proof-code formula-code)) →
      EqSymRuleNat proof-code formula-code

proofRuleEqSymCheckingBranch :
  ProofRuleEqSymCheckingBranchData →
  ProofCheckingBranchPR
proofRuleEqSymCheckingBranch D = record
  { branch-pr =
      ProofRuleEqSymPR.eqSym-pr
        (ProofRuleEqSymCheckingBranchData.eqSym-pr-data D)
  ; branch-sound-decoded =
      proofRuleEqSymPR-to-decoded
        (ProofRuleEqSymCheckingBranchData.eqSym-pr-data D)
  ; branch-nonzero-sound-decoded =
      λ nonzero →
        eqSymRuleNat-to-decoded
          (ProofRuleEqSymCheckingBranchData.eqSym-nonzero-sound
            D
            nonzero)
  }

proofRuleEqSymTargetedBranch :
  ProofRuleEqSymCheckingBranchData →
  TargetedProofCheckingBranchPR EqSymRuleNat
proofRuleEqSymTargetedBranch D = record
  { branch =
      proofRuleEqSymCheckingBranch D
  ; branch-complete-target =
      ProofRuleEqSymPR.eqSym-complete
        (ProofRuleEqSymCheckingBranchData.eqSym-pr-data D)
  }

EqTransFormula : Term → Term → Term → Formula
EqTransFormula r s t =
  r ≈ s ⇒ (s ≈ t ⇒ r ≈ t)

EqTransRuleNat : ℕ → ℕ → Set
EqTransRuleNat proof-code formula-code =
  Σ Term
    (λ r →
      Σ Term
        (λ s →
          Σ Term
            (λ t →
              (proof-code ≡
               encodeCode
                (node 10
                  (canonicalCodeTerm r ∷
                   canonicalCodeTerm s ∷
                   canonicalCodeTerm t ∷
                   []))) ×
              (formula-code ≡ canonicalNatFormula (EqTransFormula r s t)))))

eqTransRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  EqTransRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
eqTransRuleNat-to-decoded
  (r ,Σ (s ,Σ (t ,Σ (proof-eq ,× formula-eq)))) =
  node 10
    (canonicalCodeTerm r ∷
     canonicalCodeTerm s ∷
     canonicalCodeTerm t ∷
     [])
  ,Σ
  (EqTransFormula r s t ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 10
          (canonicalCodeTerm r ∷
           canonicalCodeTerm s ∷
           canonicalCodeTerm t ∷
           []))
      ≡
      just (EqTransFormula r s t)
    check-eq
      rewrite decodeCanonicalTerm-roundTrip r
            | decodeCanonicalTerm-roundTrip s
            | decodeCanonicalTerm-roundTrip t =
      refl

record ProofRuleEqTransPR : Set₁ where
  field
    eqTrans-pr :
      PRRel (suc (suc zero))

    eqTrans-complete :
      {proof-code formula-code : ℕ} →
      EqTransRuleNat proof-code formula-code →
      PRRel-holds eqTrans-pr (proofCodeArgs proof-code formula-code)

    eqTrans-sound :
      {proof-code formula-code : ℕ} →
      PRRel-holds eqTrans-pr (proofCodeArgs proof-code formula-code) →
      EqTransRuleNat proof-code formula-code

proofRuleEqTransPR-to-decoded :
  (D : ProofRuleEqTransPR) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (ProofRuleEqTransPR.eqTrans-pr D)
    (proofCodeArgs proof-code formula-code) →
  DecodedExecutableProofCodeNat proof-code formula-code
proofRuleEqTransPR-to-decoded D holds =
  eqTransRuleNat-to-decoded
    (ProofRuleEqTransPR.eqTrans-sound D holds)

proofRuleEqTransPR-represented :
  (D : ProofRuleEqTransPR) →
  PARepresentsRelation (ProofRuleEqTransPR.eqTrans-pr D)
proofRuleEqTransPR-represented D =
  prrel-represented (ProofRuleEqTransPR.eqTrans-pr D)

record ProofRuleEqTransCheckingBranchData : Set₁ where
  field
    eqTrans-pr-data :
      ProofRuleEqTransPR

    eqTrans-nonzero-sound :
      {proof-code formula-code : ℕ} →
      NonzeroNat
        (evalPRF
          (PRRel.characteristic
            (ProofRuleEqTransPR.eqTrans-pr eqTrans-pr-data))
          (proofCodeArgs proof-code formula-code)) →
      EqTransRuleNat proof-code formula-code

proofRuleEqTransCheckingBranch :
  ProofRuleEqTransCheckingBranchData →
  ProofCheckingBranchPR
proofRuleEqTransCheckingBranch D = record
  { branch-pr =
      ProofRuleEqTransPR.eqTrans-pr
        (ProofRuleEqTransCheckingBranchData.eqTrans-pr-data D)
  ; branch-sound-decoded =
      proofRuleEqTransPR-to-decoded
        (ProofRuleEqTransCheckingBranchData.eqTrans-pr-data D)
  ; branch-nonzero-sound-decoded =
      λ nonzero →
        eqTransRuleNat-to-decoded
          (ProofRuleEqTransCheckingBranchData.eqTrans-nonzero-sound
            D
            nonzero)
  }

proofRuleEqTransTargetedBranch :
  ProofRuleEqTransCheckingBranchData →
  TargetedProofCheckingBranchPR EqTransRuleNat
proofRuleEqTransTargetedBranch D = record
  { branch =
      proofRuleEqTransCheckingBranch D
  ; branch-complete-target =
      ProofRuleEqTransPR.eqTrans-complete
        (ProofRuleEqTransCheckingBranchData.eqTrans-pr-data D)
  }

SucCongFormula : Term → Term → Formula
SucCongFormula s t =
  s ≈ t ⇒ sucᵗ s ≈ sucᵗ t

SucCongRuleNat : ℕ → ℕ → Set
SucCongRuleNat proof-code formula-code =
  Σ Term
    (λ s →
      Σ Term
        (λ t →
          (proof-code ≡
           encodeCode
            (node 11
              (canonicalCodeTerm s ∷
               canonicalCodeTerm t ∷
               []))) ×
          (formula-code ≡ canonicalNatFormula (SucCongFormula s t))))

sucCongRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  SucCongRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
sucCongRuleNat-to-decoded
  (s ,Σ (t ,Σ (proof-eq ,× formula-eq))) =
  node 11
    (canonicalCodeTerm s ∷
     canonicalCodeTerm t ∷
     [])
  ,Σ
  (SucCongFormula s t ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 11
          (canonicalCodeTerm s ∷
           canonicalCodeTerm t ∷
           []))
      ≡
      just (SucCongFormula s t)
    check-eq
      rewrite decodeCanonicalTerm-roundTrip s
            | decodeCanonicalTerm-roundTrip t =
      refl

record ProofRuleSucCongPR : Set₁ where
  field
    sucCong-pr :
      PRRel (suc (suc zero))

    sucCong-complete :
      {proof-code formula-code : ℕ} →
      SucCongRuleNat proof-code formula-code →
      PRRel-holds sucCong-pr (proofCodeArgs proof-code formula-code)

    sucCong-sound :
      {proof-code formula-code : ℕ} →
      PRRel-holds sucCong-pr (proofCodeArgs proof-code formula-code) →
      SucCongRuleNat proof-code formula-code

proofRuleSucCongPR-to-decoded :
  (D : ProofRuleSucCongPR) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (ProofRuleSucCongPR.sucCong-pr D)
    (proofCodeArgs proof-code formula-code) →
  DecodedExecutableProofCodeNat proof-code formula-code
proofRuleSucCongPR-to-decoded D holds =
  sucCongRuleNat-to-decoded
    (ProofRuleSucCongPR.sucCong-sound D holds)

proofRuleSucCongPR-represented :
  (D : ProofRuleSucCongPR) →
  PARepresentsRelation (ProofRuleSucCongPR.sucCong-pr D)
proofRuleSucCongPR-represented D =
  prrel-represented (ProofRuleSucCongPR.sucCong-pr D)

record ProofRuleSucCongCheckingBranchData : Set₁ where
  field
    sucCong-pr-data :
      ProofRuleSucCongPR

    sucCong-nonzero-sound :
      {proof-code formula-code : ℕ} →
      NonzeroNat
        (evalPRF
          (PRRel.characteristic
            (ProofRuleSucCongPR.sucCong-pr sucCong-pr-data))
          (proofCodeArgs proof-code formula-code)) →
      SucCongRuleNat proof-code formula-code

proofRuleSucCongCheckingBranch :
  ProofRuleSucCongCheckingBranchData →
  ProofCheckingBranchPR
proofRuleSucCongCheckingBranch D = record
  { branch-pr =
      ProofRuleSucCongPR.sucCong-pr
        (ProofRuleSucCongCheckingBranchData.sucCong-pr-data D)
  ; branch-sound-decoded =
      proofRuleSucCongPR-to-decoded
        (ProofRuleSucCongCheckingBranchData.sucCong-pr-data D)
  ; branch-nonzero-sound-decoded =
      λ nonzero →
        sucCongRuleNat-to-decoded
          (ProofRuleSucCongCheckingBranchData.sucCong-nonzero-sound
            D
            nonzero)
  }

proofRuleSucCongTargetedBranch :
  ProofRuleSucCongCheckingBranchData →
  TargetedProofCheckingBranchPR SucCongRuleNat
proofRuleSucCongTargetedBranch D = record
  { branch =
      proofRuleSucCongCheckingBranch D
  ; branch-complete-target =
      ProofRuleSucCongPR.sucCong-complete
        (ProofRuleSucCongCheckingBranchData.sucCong-pr-data D)
  }

AddCongFormula : Term → Term → Term → Term → Formula
AddCongFormula a b c d =
  a ≈ b ⇒ (c ≈ d ⇒ (a +ᵗ c) ≈ (b +ᵗ d))

AddCongRuleNat : ℕ → ℕ → Set
AddCongRuleNat proof-code formula-code =
  Σ Term
    (λ a →
      Σ Term
        (λ b →
          Σ Term
            (λ c →
              Σ Term
                (λ d →
                  (proof-code ≡
                   encodeCode
                    (node 12
                      (canonicalCodeTerm a ∷
                       canonicalCodeTerm b ∷
                       canonicalCodeTerm c ∷
                       canonicalCodeTerm d ∷
                       []))) ×
                  (formula-code ≡ canonicalNatFormula (AddCongFormula a b c d))))))

addCongRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  AddCongRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
addCongRuleNat-to-decoded
  (a ,Σ (b ,Σ (c ,Σ (d ,Σ (proof-eq ,× formula-eq))))) =
  node 12
    (canonicalCodeTerm a ∷
     canonicalCodeTerm b ∷
     canonicalCodeTerm c ∷
     canonicalCodeTerm d ∷
     [])
  ,Σ
  (AddCongFormula a b c d ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 12
          (canonicalCodeTerm a ∷
           canonicalCodeTerm b ∷
           canonicalCodeTerm c ∷
           canonicalCodeTerm d ∷
           []))
      ≡
      just (AddCongFormula a b c d)
    check-eq
      rewrite decodeCanonicalTerm-roundTrip a
            | decodeCanonicalTerm-roundTrip b
            | decodeCanonicalTerm-roundTrip c
            | decodeCanonicalTerm-roundTrip d =
      refl

record ProofRuleAddCongPR : Set₁ where
  field
    addCong-pr :
      PRRel (suc (suc zero))

    addCong-complete :
      {proof-code formula-code : ℕ} →
      AddCongRuleNat proof-code formula-code →
      PRRel-holds addCong-pr (proofCodeArgs proof-code formula-code)

    addCong-sound :
      {proof-code formula-code : ℕ} →
      PRRel-holds addCong-pr (proofCodeArgs proof-code formula-code) →
      AddCongRuleNat proof-code formula-code

proofRuleAddCongPR-to-decoded :
  (D : ProofRuleAddCongPR) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (ProofRuleAddCongPR.addCong-pr D)
    (proofCodeArgs proof-code formula-code) →
  DecodedExecutableProofCodeNat proof-code formula-code
proofRuleAddCongPR-to-decoded D holds =
  addCongRuleNat-to-decoded
    (ProofRuleAddCongPR.addCong-sound D holds)

proofRuleAddCongPR-represented :
  (D : ProofRuleAddCongPR) →
  PARepresentsRelation (ProofRuleAddCongPR.addCong-pr D)
proofRuleAddCongPR-represented D =
  prrel-represented (ProofRuleAddCongPR.addCong-pr D)

record ProofRuleAddCongCheckingBranchData : Set₁ where
  field
    addCong-pr-data :
      ProofRuleAddCongPR

    addCong-nonzero-sound :
      {proof-code formula-code : ℕ} →
      NonzeroNat
        (evalPRF
          (PRRel.characteristic
            (ProofRuleAddCongPR.addCong-pr addCong-pr-data))
          (proofCodeArgs proof-code formula-code)) →
      AddCongRuleNat proof-code formula-code

proofRuleAddCongCheckingBranch :
  ProofRuleAddCongCheckingBranchData →
  ProofCheckingBranchPR
proofRuleAddCongCheckingBranch D = record
  { branch-pr =
      ProofRuleAddCongPR.addCong-pr
        (ProofRuleAddCongCheckingBranchData.addCong-pr-data D)
  ; branch-sound-decoded =
      proofRuleAddCongPR-to-decoded
        (ProofRuleAddCongCheckingBranchData.addCong-pr-data D)
  ; branch-nonzero-sound-decoded =
      λ nonzero →
        addCongRuleNat-to-decoded
          (ProofRuleAddCongCheckingBranchData.addCong-nonzero-sound
            D
            nonzero)
  }

proofRuleAddCongTargetedBranch :
  ProofRuleAddCongCheckingBranchData →
  TargetedProofCheckingBranchPR AddCongRuleNat
proofRuleAddCongTargetedBranch D = record
  { branch =
      proofRuleAddCongCheckingBranch D
  ; branch-complete-target =
      ProofRuleAddCongPR.addCong-complete
        (ProofRuleAddCongCheckingBranchData.addCong-pr-data D)
  }

MulCongFormula : Term → Term → Term → Term → Formula
MulCongFormula a b c d =
  a ≈ b ⇒ (c ≈ d ⇒ (a *ᵗ c) ≈ (b *ᵗ d))

MulCongRuleNat : ℕ → ℕ → Set
MulCongRuleNat proof-code formula-code =
  Σ Term
    (λ a →
      Σ Term
        (λ b →
          Σ Term
            (λ c →
              Σ Term
                (λ d →
                  (proof-code ≡
                   encodeCode
                    (node 13
                      (canonicalCodeTerm a ∷
                       canonicalCodeTerm b ∷
                       canonicalCodeTerm c ∷
                       canonicalCodeTerm d ∷
                       []))) ×
                  (formula-code ≡ canonicalNatFormula (MulCongFormula a b c d))))))

mulCongRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  MulCongRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
mulCongRuleNat-to-decoded
  (a ,Σ (b ,Σ (c ,Σ (d ,Σ (proof-eq ,× formula-eq))))) =
  node 13
    (canonicalCodeTerm a ∷
     canonicalCodeTerm b ∷
     canonicalCodeTerm c ∷
     canonicalCodeTerm d ∷
     [])
  ,Σ
  (MulCongFormula a b c d ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 13
          (canonicalCodeTerm a ∷
           canonicalCodeTerm b ∷
           canonicalCodeTerm c ∷
           canonicalCodeTerm d ∷
           []))
      ≡
      just (MulCongFormula a b c d)
    check-eq
      rewrite decodeCanonicalTerm-roundTrip a
            | decodeCanonicalTerm-roundTrip b
            | decodeCanonicalTerm-roundTrip c
            | decodeCanonicalTerm-roundTrip d =
      refl

record ProofRuleMulCongPR : Set₁ where
  field
    mulCong-pr :
      PRRel (suc (suc zero))

    mulCong-complete :
      {proof-code formula-code : ℕ} →
      MulCongRuleNat proof-code formula-code →
      PRRel-holds mulCong-pr (proofCodeArgs proof-code formula-code)

    mulCong-sound :
      {proof-code formula-code : ℕ} →
      PRRel-holds mulCong-pr (proofCodeArgs proof-code formula-code) →
      MulCongRuleNat proof-code formula-code

proofRuleMulCongPR-to-decoded :
  (D : ProofRuleMulCongPR) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (ProofRuleMulCongPR.mulCong-pr D)
    (proofCodeArgs proof-code formula-code) →
  DecodedExecutableProofCodeNat proof-code formula-code
proofRuleMulCongPR-to-decoded D holds =
  mulCongRuleNat-to-decoded
    (ProofRuleMulCongPR.mulCong-sound D holds)

proofRuleMulCongPR-represented :
  (D : ProofRuleMulCongPR) →
  PARepresentsRelation (ProofRuleMulCongPR.mulCong-pr D)
proofRuleMulCongPR-represented D =
  prrel-represented (ProofRuleMulCongPR.mulCong-pr D)

record ProofRuleMulCongCheckingBranchData : Set₁ where
  field
    mulCong-pr-data :
      ProofRuleMulCongPR

    mulCong-nonzero-sound :
      {proof-code formula-code : ℕ} →
      NonzeroNat
        (evalPRF
          (PRRel.characteristic
            (ProofRuleMulCongPR.mulCong-pr mulCong-pr-data))
          (proofCodeArgs proof-code formula-code)) →
      MulCongRuleNat proof-code formula-code

proofRuleMulCongCheckingBranch :
  ProofRuleMulCongCheckingBranchData →
  ProofCheckingBranchPR
proofRuleMulCongCheckingBranch D = record
  { branch-pr =
      ProofRuleMulCongPR.mulCong-pr
        (ProofRuleMulCongCheckingBranchData.mulCong-pr-data D)
  ; branch-sound-decoded =
      proofRuleMulCongPR-to-decoded
        (ProofRuleMulCongCheckingBranchData.mulCong-pr-data D)
  ; branch-nonzero-sound-decoded =
      λ nonzero →
        mulCongRuleNat-to-decoded
          (ProofRuleMulCongCheckingBranchData.mulCong-nonzero-sound
            D
            nonzero)
  }

proofRuleMulCongTargetedBranch :
  ProofRuleMulCongCheckingBranchData →
  TargetedProofCheckingBranchPR MulCongRuleNat
proofRuleMulCongTargetedBranch D = record
  { branch =
      proofRuleMulCongCheckingBranch D
  ; branch-complete-target =
      ProofRuleMulCongPR.mulCong-complete
        (ProofRuleMulCongCheckingBranchData.mulCong-pr-data D)
  }
