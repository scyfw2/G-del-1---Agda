{-# OPTIONS --safe #-}

module Godel.ProofRuleQuantifierSchemas where

open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.ProofSystem using (exists-prefix)
open import Godel.CanonicalCoding
  using
    ( atom
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

-- Shared branch wrapper for the quantifier/existential-prefix proof-rule
-- targets.  Each target below supplies its own decoded-checker adapter.

record ProofRuleQuantifierPR
    (Target : ℕ → ℕ → Set) :
    Set₁ where
  field
    quantifier-pr :
      PRRel (suc (suc zero))

    quantifier-complete :
      {proof-code formula-code : ℕ} →
      Target proof-code formula-code →
      PRRel-holds quantifier-pr (proofCodeArgs proof-code formula-code)

    quantifier-sound :
      {proof-code formula-code : ℕ} →
      PRRel-holds quantifier-pr (proofCodeArgs proof-code formula-code) →
      Target proof-code formula-code

proofRuleQuantifierPR-represented :
  {Target : ℕ → ℕ → Set} →
  (D : ProofRuleQuantifierPR Target) →
  PARepresentsRelation (ProofRuleQuantifierPR.quantifier-pr D)
proofRuleQuantifierPR-represented D =
  prrel-represented (ProofRuleQuantifierPR.quantifier-pr D)

record ProofRuleQuantifierCheckingBranchData
    (Target : ℕ → ℕ → Set) :
    Set₁ where
  field
    quantifier-pr-data :
      ProofRuleQuantifierPR Target

    quantifier-nonzero-sound :
      {proof-code formula-code : ℕ} →
      NonzeroNat
        (evalPRF
          (PRRel.characteristic
            (ProofRuleQuantifierPR.quantifier-pr quantifier-pr-data))
          (proofCodeArgs proof-code formula-code)) →
      Target proof-code formula-code

proofRuleQuantifierCheckingBranch :
  {Target : ℕ → ℕ → Set} →
  ({proof-code formula-code : ℕ} →
   Target proof-code formula-code →
   DecodedExecutableProofCodeNat proof-code formula-code) →
  ProofRuleQuantifierCheckingBranchData Target →
  ProofCheckingBranchPR
proofRuleQuantifierCheckingBranch target-to-decoded D = record
  { branch-pr =
      ProofRuleQuantifierPR.quantifier-pr
        (ProofRuleQuantifierCheckingBranchData.quantifier-pr-data D)
  ; branch-sound-decoded =
      λ holds →
        target-to-decoded
          (ProofRuleQuantifierPR.quantifier-sound
            (ProofRuleQuantifierCheckingBranchData.quantifier-pr-data D)
            holds)
  ; branch-nonzero-sound-decoded =
      λ nonzero →
        target-to-decoded
          (ProofRuleQuantifierCheckingBranchData.quantifier-nonzero-sound
            D
            nonzero)
  }

proofRuleQuantifierTargetedBranch :
  {Target : ℕ → ℕ → Set} →
  ({proof-code formula-code : ℕ} →
   Target proof-code formula-code →
   DecodedExecutableProofCodeNat proof-code formula-code) →
  ProofRuleQuantifierCheckingBranchData Target →
  TargetedProofCheckingBranchPR Target
proofRuleQuantifierTargetedBranch target-to-decoded D = record
  { branch =
      proofRuleQuantifierCheckingBranch target-to-decoded D
  ; branch-complete-target =
      ProofRuleQuantifierPR.quantifier-complete
        (ProofRuleQuantifierCheckingBranchData.quantifier-pr-data D)
  }

ExistsElimFormula : Formula → Formula → Formula
ExistsElimFormula A B =
  (∀ᶠ (A ⇒ wkFormula B)) ⇒ (∃ᶠ A ⇒ B)

ExistsElimRuleNat : ℕ → ℕ → Set
ExistsElimRuleNat proof-code formula-code =
  Σ Formula
    (λ A →
      Σ Formula
        (λ B →
          (proof-code ≡
           encodeCode
            (node 14
              (canonicalCodeFormula A ∷
               canonicalCodeFormula B ∷
               []))) ×
          (formula-code ≡ canonicalNatFormula (ExistsElimFormula A B))))

existsElimRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  ExistsElimRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
existsElimRuleNat-to-decoded
  (A ,Σ (B ,Σ (proof-eq ,× formula-eq))) =
  node 14
    (canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     [])
  ,Σ
  (ExistsElimFormula A B ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 14
          (canonicalCodeFormula A ∷
           canonicalCodeFormula B ∷
           []))
      ≡
      just (ExistsElimFormula A B)
    check-eq
      rewrite decodeCanonicalFormula-roundTrip A
            | decodeCanonicalFormula-roundTrip B =
      refl

ProofRuleExistsElimPR : Set₁
ProofRuleExistsElimPR =
  ProofRuleQuantifierPR ExistsElimRuleNat

ProofRuleExistsElimCheckingBranchData : Set₁
ProofRuleExistsElimCheckingBranchData =
  ProofRuleQuantifierCheckingBranchData ExistsElimRuleNat

proofRuleExistsElimTargetedBranch :
  ProofRuleExistsElimCheckingBranchData →
  TargetedProofCheckingBranchPR ExistsElimRuleNat
proofRuleExistsElimTargetedBranch =
  proofRuleQuantifierTargetedBranch existsElimRuleNat-to-decoded

ExistsPrefixIntroduceFormula : ℕ → Formula → Formula → Formula
ExistsPrefixIntroduceFormula k I A =
  I ⇒ exists-prefix k A

ExistsPrefixIntroduceRuleNat : ℕ → ℕ → Set
ExistsPrefixIntroduceRuleNat proof-code formula-code =
  Σ ℕ
    (λ k →
      Σ Formula
        (λ I →
          Σ Formula
            (λ A →
              (proof-code ≡
               encodeCode
                (node 15
                  (atom k ∷
                   canonicalCodeFormula I ∷
                   canonicalCodeFormula A ∷
                   []))) ×
              (formula-code ≡
               canonicalNatFormula (ExistsPrefixIntroduceFormula k I A)))))

existsPrefixIntroduceRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  ExistsPrefixIntroduceRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
existsPrefixIntroduceRuleNat-to-decoded
  (k ,Σ (I ,Σ (A ,Σ (proof-eq ,× formula-eq)))) =
  node 15
    (atom k ∷
     canonicalCodeFormula I ∷
     canonicalCodeFormula A ∷
     [])
  ,Σ
  (ExistsPrefixIntroduceFormula k I A ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 15
          (atom k ∷
           canonicalCodeFormula I ∷
           canonicalCodeFormula A ∷
           []))
      ≡
      just (ExistsPrefixIntroduceFormula k I A)
    check-eq
      rewrite decodeCanonicalFormula-roundTrip I
            | decodeCanonicalFormula-roundTrip A =
      refl

ProofRuleExistsPrefixIntroducePR : Set₁
ProofRuleExistsPrefixIntroducePR =
  ProofRuleQuantifierPR ExistsPrefixIntroduceRuleNat

ProofRuleExistsPrefixIntroduceCheckingBranchData : Set₁
ProofRuleExistsPrefixIntroduceCheckingBranchData =
  ProofRuleQuantifierCheckingBranchData ExistsPrefixIntroduceRuleNat

proofRuleExistsPrefixIntroduceTargetedBranch :
  ProofRuleExistsPrefixIntroduceCheckingBranchData →
  TargetedProofCheckingBranchPR ExistsPrefixIntroduceRuleNat
proofRuleExistsPrefixIntroduceTargetedBranch =
  proofRuleQuantifierTargetedBranch existsPrefixIntroduceRuleNat-to-decoded

ExistsPrefixBinaryLiftFormula :
  ℕ → Formula → Formula → Formula → Formula → Formula
ExistsPrefixBinaryLiftFormula k A B C D =
  (A ⇒ (B ⇒ D)) ⇒ (exists-prefix k A ⇒ (exists-prefix k B ⇒ C))

ExistsPrefixBinaryLiftRuleNat : ℕ → ℕ → Set
ExistsPrefixBinaryLiftRuleNat proof-code formula-code =
  Σ ℕ
    (λ k →
      Σ Formula
        (λ A →
          Σ Formula
            (λ B →
              Σ Formula
                (λ C →
                  Σ Formula
                    (λ D →
                      (proof-code ≡
                       encodeCode
                        (node 16
                          (atom k ∷
                           canonicalCodeFormula A ∷
                           canonicalCodeFormula B ∷
                           canonicalCodeFormula C ∷
                           canonicalCodeFormula D ∷
                           []))) ×
                      (formula-code ≡
                       canonicalNatFormula
                         (ExistsPrefixBinaryLiftFormula k A B C D)))))))

existsPrefixBinaryLiftRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  ExistsPrefixBinaryLiftRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
existsPrefixBinaryLiftRuleNat-to-decoded
  (k ,Σ (A ,Σ (B ,Σ (C ,Σ (D ,Σ (proof-eq ,× formula-eq)))))) =
  node 16
    (atom k ∷
     canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     canonicalCodeFormula C ∷
     canonicalCodeFormula D ∷
     [])
  ,Σ
  (ExistsPrefixBinaryLiftFormula k A B C D ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 16
          (atom k ∷
           canonicalCodeFormula A ∷
           canonicalCodeFormula B ∷
           canonicalCodeFormula C ∷
           canonicalCodeFormula D ∷
           []))
      ≡
      just (ExistsPrefixBinaryLiftFormula k A B C D)
    check-eq
      rewrite decodeCanonicalFormula-roundTrip A
            | decodeCanonicalFormula-roundTrip B
            | decodeCanonicalFormula-roundTrip C
            | decodeCanonicalFormula-roundTrip D =
      refl

ProofRuleExistsPrefixBinaryLiftPR : Set₁
ProofRuleExistsPrefixBinaryLiftPR =
  ProofRuleQuantifierPR ExistsPrefixBinaryLiftRuleNat

ProofRuleExistsPrefixBinaryLiftCheckingBranchData : Set₁
ProofRuleExistsPrefixBinaryLiftCheckingBranchData =
  ProofRuleQuantifierCheckingBranchData ExistsPrefixBinaryLiftRuleNat

proofRuleExistsPrefixBinaryLiftTargetedBranch :
  ProofRuleExistsPrefixBinaryLiftCheckingBranchData →
  TargetedProofCheckingBranchPR ExistsPrefixBinaryLiftRuleNat
proofRuleExistsPrefixBinaryLiftTargetedBranch =
  proofRuleQuantifierTargetedBranch existsPrefixBinaryLiftRuleNat-to-decoded

ExistsPrefixPremiseMapFormula :
  ℕ → Formula → Formula → Formula → Formula → Formula → Formula
ExistsPrefixPremiseMapFormula k E A B C D =
  (E ⇒ (A ⇒ B)) ⇒ (E ⇒ (exists-prefix k C ⇒ exists-prefix k D))

ExistsPrefixPremiseMapRuleNat : ℕ → ℕ → Set
ExistsPrefixPremiseMapRuleNat proof-code formula-code =
  Σ ℕ
    (λ k →
      Σ Formula
        (λ E →
          Σ Formula
            (λ A →
              Σ Formula
                (λ B →
                  Σ Formula
                    (λ C →
                      Σ Formula
                        (λ D →
                          (proof-code ≡
                           encodeCode
                            (node 17
                              (atom k ∷
                               canonicalCodeFormula E ∷
                               canonicalCodeFormula A ∷
                               canonicalCodeFormula B ∷
                               canonicalCodeFormula C ∷
                               canonicalCodeFormula D ∷
                               []))) ×
                          (formula-code ≡
                           canonicalNatFormula
                             (ExistsPrefixPremiseMapFormula k E A B C D))))))))

existsPrefixPremiseMapRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  ExistsPrefixPremiseMapRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
existsPrefixPremiseMapRuleNat-to-decoded
  (k ,Σ (E ,Σ (A ,Σ (B ,Σ (C ,Σ (D ,Σ (proof-eq ,× formula-eq))))))) =
  node 17
    (atom k ∷
     canonicalCodeFormula E ∷
     canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     canonicalCodeFormula C ∷
     canonicalCodeFormula D ∷
     [])
  ,Σ
  (ExistsPrefixPremiseMapFormula k E A B C D ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 17
          (atom k ∷
           canonicalCodeFormula E ∷
           canonicalCodeFormula A ∷
           canonicalCodeFormula B ∷
           canonicalCodeFormula C ∷
           canonicalCodeFormula D ∷
           []))
      ≡
      just (ExistsPrefixPremiseMapFormula k E A B C D)
    check-eq
      rewrite decodeCanonicalFormula-roundTrip E
            | decodeCanonicalFormula-roundTrip A
            | decodeCanonicalFormula-roundTrip B
            | decodeCanonicalFormula-roundTrip C
            | decodeCanonicalFormula-roundTrip D =
      refl

ProofRuleExistsPrefixPremiseMapPR : Set₁
ProofRuleExistsPrefixPremiseMapPR =
  ProofRuleQuantifierPR ExistsPrefixPremiseMapRuleNat

ProofRuleExistsPrefixPremiseMapCheckingBranchData : Set₁
ProofRuleExistsPrefixPremiseMapCheckingBranchData =
  ProofRuleQuantifierCheckingBranchData ExistsPrefixPremiseMapRuleNat

proofRuleExistsPrefixPremiseMapTargetedBranch :
  ProofRuleExistsPrefixPremiseMapCheckingBranchData →
  TargetedProofCheckingBranchPR ExistsPrefixPremiseMapRuleNat
proofRuleExistsPrefixPremiseMapTargetedBranch =
  proofRuleQuantifierTargetedBranch existsPrefixPremiseMapRuleNat-to-decoded

PremiseChangeFormula : Formula → Formula → Formula → Formula → Formula
PremiseChangeFormula E E' A B =
  (E' ⇒ (A ⇒ B)) ⇒ (E ⇒ (A ⇒ B))

PremiseChangeRuleNat : ℕ → ℕ → Set
PremiseChangeRuleNat proof-code formula-code =
  Σ Formula
    (λ E →
      Σ Formula
        (λ E' →
          Σ Formula
            (λ A →
              Σ Formula
                (λ B →
                  (proof-code ≡
                   encodeCode
                    (node 18
                      (canonicalCodeFormula E ∷
                       canonicalCodeFormula E' ∷
                       canonicalCodeFormula A ∷
                       canonicalCodeFormula B ∷
                       []))) ×
                  (formula-code ≡
                   canonicalNatFormula (PremiseChangeFormula E E' A B))))))

premiseChangeRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  PremiseChangeRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
premiseChangeRuleNat-to-decoded
  (E ,Σ (E' ,Σ (A ,Σ (B ,Σ (proof-eq ,× formula-eq))))) =
  node 18
    (canonicalCodeFormula E ∷
     canonicalCodeFormula E' ∷
     canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     [])
  ,Σ
  (PremiseChangeFormula E E' A B ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 18
          (canonicalCodeFormula E ∷
           canonicalCodeFormula E' ∷
           canonicalCodeFormula A ∷
           canonicalCodeFormula B ∷
           []))
      ≡
      just (PremiseChangeFormula E E' A B)
    check-eq
      rewrite decodeCanonicalFormula-roundTrip E
            | decodeCanonicalFormula-roundTrip E'
            | decodeCanonicalFormula-roundTrip A
            | decodeCanonicalFormula-roundTrip B =
      refl

ProofRulePremiseChangePR : Set₁
ProofRulePremiseChangePR =
  ProofRuleQuantifierPR PremiseChangeRuleNat

ProofRulePremiseChangeCheckingBranchData : Set₁
ProofRulePremiseChangeCheckingBranchData =
  ProofRuleQuantifierCheckingBranchData PremiseChangeRuleNat

proofRulePremiseChangeTargetedBranch :
  ProofRulePremiseChangeCheckingBranchData →
  TargetedProofCheckingBranchPR PremiseChangeRuleNat
proofRulePremiseChangeTargetedBranch =
  proofRuleQuantifierTargetedBranch premiseChangeRuleNat-to-decoded
