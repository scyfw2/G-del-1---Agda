{-# OPTIONS --safe #-}

module Godel.ProofRuleDerivedLogicalSchemas where

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

-- Targets for derived logical helper proof rules:
--
--   tag 25 and-left-imp
--   tag 26 and-right-imp
--   tag 27 and-left-imp1
--   tag 28 and-right-imp1
--   tag 29 imp-and-intro2
--   tag 30 and-both-map
--   tag 31 and-left-map
--   tag 32 premise-and-both-map
--   tag 33 premise-and-left-map
--   tag 34 body-unique-compose
--   tag 38 contradiction-to-neg

record ProofRuleDerivedLogicalPR
    (Target : ℕ → ℕ → Set) :
    Set₁ where
  field
    derived-logical-pr :
      PRRel (suc (suc zero))

    derived-logical-complete :
      {proof-code formula-code : ℕ} →
      Target proof-code formula-code →
      PRRel-holds derived-logical-pr (proofCodeArgs proof-code formula-code)

    derived-logical-sound :
      {proof-code formula-code : ℕ} →
      PRRel-holds derived-logical-pr (proofCodeArgs proof-code formula-code) →
      Target proof-code formula-code

proofRuleDerivedLogicalPR-represented :
  {Target : ℕ → ℕ → Set} →
  (D : ProofRuleDerivedLogicalPR Target) →
  PARepresentsRelation (ProofRuleDerivedLogicalPR.derived-logical-pr D)
proofRuleDerivedLogicalPR-represented D =
  prrel-represented (ProofRuleDerivedLogicalPR.derived-logical-pr D)

record ProofRuleDerivedLogicalCheckingBranchData
    (Target : ℕ → ℕ → Set) :
    Set₁ where
  field
    derived-logical-pr-data :
      ProofRuleDerivedLogicalPR Target

    derived-logical-nonzero-sound :
      {proof-code formula-code : ℕ} →
      NonzeroNat
        (evalPRF
          (PRRel.characteristic
            (ProofRuleDerivedLogicalPR.derived-logical-pr
              derived-logical-pr-data))
          (proofCodeArgs proof-code formula-code)) →
      Target proof-code formula-code

proofRuleDerivedLogicalCheckingBranch :
  {Target : ℕ → ℕ → Set} →
  ({proof-code formula-code : ℕ} →
   Target proof-code formula-code →
   DecodedExecutableProofCodeNat proof-code formula-code) →
  ProofRuleDerivedLogicalCheckingBranchData Target →
  ProofCheckingBranchPR
proofRuleDerivedLogicalCheckingBranch target-to-decoded D = record
  { branch-pr =
      ProofRuleDerivedLogicalPR.derived-logical-pr
        (ProofRuleDerivedLogicalCheckingBranchData.derived-logical-pr-data D)
  ; branch-sound-decoded =
      λ holds →
        target-to-decoded
          (ProofRuleDerivedLogicalPR.derived-logical-sound
            (ProofRuleDerivedLogicalCheckingBranchData.derived-logical-pr-data D)
            holds)
  ; branch-nonzero-sound-decoded =
      λ nonzero →
        target-to-decoded
          (ProofRuleDerivedLogicalCheckingBranchData.derived-logical-nonzero-sound
            D
            nonzero)
  }

proofRuleDerivedLogicalTargetedBranch :
  {Target : ℕ → ℕ → Set} →
  ({proof-code formula-code : ℕ} →
   Target proof-code formula-code →
   DecodedExecutableProofCodeNat proof-code formula-code) →
  ProofRuleDerivedLogicalCheckingBranchData Target →
  TargetedProofCheckingBranchPR Target
proofRuleDerivedLogicalTargetedBranch target-to-decoded D = record
  { branch =
      proofRuleDerivedLogicalCheckingBranch target-to-decoded D
  ; branch-complete-target =
      ProofRuleDerivedLogicalPR.derived-logical-complete
        (ProofRuleDerivedLogicalCheckingBranchData.derived-logical-pr-data D)
  }

AndLeftImpFormula :
  Formula → Formula → Formula → Formula → Formula → Formula
AndLeftImpFormula A B C D E =
  (A ⇒ (C ⇒ E)) ⇒ ((A ∧ B) ⇒ ((C ∧ D) ⇒ E))

AndLeftImpProofCode :
  Formula → Formula → Formula → Formula → Formula → ℕ
AndLeftImpProofCode A B C D E =
  encodeCode
    (node 25
      (canonicalCodeFormula A ∷
       canonicalCodeFormula B ∷
       canonicalCodeFormula C ∷
       canonicalCodeFormula D ∷
       canonicalCodeFormula E ∷
       []))

AndLeftImpRuleNat : ℕ → ℕ → Set
AndLeftImpRuleNat proof-code formula-code =
  Σ Formula
    (λ A →
      Σ Formula
        (λ B →
          Σ Formula
            (λ C →
              Σ Formula
                (λ D →
                  Σ Formula
                    (λ E →
                      (proof-code ≡ AndLeftImpProofCode A B C D E) ×
                      (formula-code ≡
                       canonicalNatFormula
                        (AndLeftImpFormula A B C D E)))))))

andLeftImpRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  AndLeftImpRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
andLeftImpRuleNat-to-decoded
  (A ,Σ (B ,Σ (C ,Σ (D ,Σ (E ,Σ (proof-eq ,× formula-eq)))))) =
  node 25
    (canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     canonicalCodeFormula C ∷
     canonicalCodeFormula D ∷
     canonicalCodeFormula E ∷
     [])
  ,Σ
  (AndLeftImpFormula A B C D E ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 25
          (canonicalCodeFormula A ∷
           canonicalCodeFormula B ∷
           canonicalCodeFormula C ∷
           canonicalCodeFormula D ∷
           canonicalCodeFormula E ∷
           []))
      ≡
      just (AndLeftImpFormula A B C D E)
    check-eq
      rewrite decodeCanonicalFormula-roundTrip A
            | decodeCanonicalFormula-roundTrip B
            | decodeCanonicalFormula-roundTrip C
            | decodeCanonicalFormula-roundTrip D
            | decodeCanonicalFormula-roundTrip E =
      refl

AndRightImpFormula :
  Formula → Formula → Formula → Formula → Formula → Formula
AndRightImpFormula A B C D E =
  (B ⇒ (D ⇒ E)) ⇒ ((A ∧ B) ⇒ ((C ∧ D) ⇒ E))

AndRightImpProofCode :
  Formula → Formula → Formula → Formula → Formula → ℕ
AndRightImpProofCode A B C D E =
  encodeCode
    (node 26
      (canonicalCodeFormula A ∷
       canonicalCodeFormula B ∷
       canonicalCodeFormula C ∷
       canonicalCodeFormula D ∷
       canonicalCodeFormula E ∷
       []))

AndRightImpRuleNat : ℕ → ℕ → Set
AndRightImpRuleNat proof-code formula-code =
  Σ Formula
    (λ A →
      Σ Formula
        (λ B →
          Σ Formula
            (λ C →
              Σ Formula
                (λ D →
                  Σ Formula
                    (λ E →
                      (proof-code ≡ AndRightImpProofCode A B C D E) ×
                      (formula-code ≡
                       canonicalNatFormula
                        (AndRightImpFormula A B C D E)))))))

andRightImpRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  AndRightImpRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
andRightImpRuleNat-to-decoded
  (A ,Σ (B ,Σ (C ,Σ (D ,Σ (E ,Σ (proof-eq ,× formula-eq)))))) =
  node 26
    (canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     canonicalCodeFormula C ∷
     canonicalCodeFormula D ∷
     canonicalCodeFormula E ∷
     [])
  ,Σ
  (AndRightImpFormula A B C D E ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 26
          (canonicalCodeFormula A ∷
           canonicalCodeFormula B ∷
           canonicalCodeFormula C ∷
           canonicalCodeFormula D ∷
           canonicalCodeFormula E ∷
           []))
      ≡
      just (AndRightImpFormula A B C D E)
    check-eq
      rewrite decodeCanonicalFormula-roundTrip A
            | decodeCanonicalFormula-roundTrip B
            | decodeCanonicalFormula-roundTrip C
            | decodeCanonicalFormula-roundTrip D
            | decodeCanonicalFormula-roundTrip E =
      refl

AndLeftImp1Formula : Formula → Formula → Formula → Formula → Formula
AndLeftImp1Formula A B C E =
  (A ⇒ (C ⇒ E)) ⇒ ((A ∧ B) ⇒ (C ⇒ E))

AndLeftImp1ProofCode : Formula → Formula → Formula → Formula → ℕ
AndLeftImp1ProofCode A B C E =
  encodeCode
    (node 27
      (canonicalCodeFormula A ∷
       canonicalCodeFormula B ∷
       canonicalCodeFormula C ∷
       canonicalCodeFormula E ∷
       []))

AndLeftImp1RuleNat : ℕ → ℕ → Set
AndLeftImp1RuleNat proof-code formula-code =
  Σ Formula
    (λ A →
      Σ Formula
        (λ B →
          Σ Formula
            (λ C →
              Σ Formula
                (λ E →
                  (proof-code ≡ AndLeftImp1ProofCode A B C E) ×
                  (formula-code ≡
                   canonicalNatFormula (AndLeftImp1Formula A B C E))))))

andLeftImp1RuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  AndLeftImp1RuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
andLeftImp1RuleNat-to-decoded
  (A ,Σ (B ,Σ (C ,Σ (E ,Σ (proof-eq ,× formula-eq))))) =
  node 27
    (canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     canonicalCodeFormula C ∷
     canonicalCodeFormula E ∷
     [])
  ,Σ
  (AndLeftImp1Formula A B C E ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 27
          (canonicalCodeFormula A ∷
           canonicalCodeFormula B ∷
           canonicalCodeFormula C ∷
           canonicalCodeFormula E ∷
           []))
      ≡
      just (AndLeftImp1Formula A B C E)
    check-eq
      rewrite decodeCanonicalFormula-roundTrip A
            | decodeCanonicalFormula-roundTrip B
            | decodeCanonicalFormula-roundTrip C
            | decodeCanonicalFormula-roundTrip E =
      refl

AndRightImp1Formula : Formula → Formula → Formula → Formula → Formula
AndRightImp1Formula A B C E =
  (B ⇒ (C ⇒ E)) ⇒ ((A ∧ B) ⇒ (C ⇒ E))

AndRightImp1ProofCode : Formula → Formula → Formula → Formula → ℕ
AndRightImp1ProofCode A B C E =
  encodeCode
    (node 28
      (canonicalCodeFormula A ∷
       canonicalCodeFormula B ∷
       canonicalCodeFormula C ∷
       canonicalCodeFormula E ∷
       []))

AndRightImp1RuleNat : ℕ → ℕ → Set
AndRightImp1RuleNat proof-code formula-code =
  Σ Formula
    (λ A →
      Σ Formula
        (λ B →
          Σ Formula
            (λ C →
              Σ Formula
                (λ E →
                  (proof-code ≡ AndRightImp1ProofCode A B C E) ×
                  (formula-code ≡
                   canonicalNatFormula (AndRightImp1Formula A B C E))))))

andRightImp1RuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  AndRightImp1RuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
andRightImp1RuleNat-to-decoded
  (A ,Σ (B ,Σ (C ,Σ (E ,Σ (proof-eq ,× formula-eq))))) =
  node 28
    (canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     canonicalCodeFormula C ∷
     canonicalCodeFormula E ∷
     [])
  ,Σ
  (AndRightImp1Formula A B C E ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 28
          (canonicalCodeFormula A ∷
           canonicalCodeFormula B ∷
           canonicalCodeFormula C ∷
           canonicalCodeFormula E ∷
           []))
      ≡
      just (AndRightImp1Formula A B C E)
    check-eq
      rewrite decodeCanonicalFormula-roundTrip A
            | decodeCanonicalFormula-roundTrip B
            | decodeCanonicalFormula-roundTrip C
            | decodeCanonicalFormula-roundTrip E =
      refl

ImpAndIntro2Formula : Formula → Formula → Formula → Formula → Formula
ImpAndIntro2Formula A B C D =
  (A ⇒ (B ⇒ C)) ⇒
  ((A ⇒ (B ⇒ D)) ⇒
   (A ⇒ (B ⇒ (C ∧ D))))

ImpAndIntro2ProofCode : Formula → Formula → Formula → Formula → ℕ
ImpAndIntro2ProofCode A B C D =
  encodeCode
    (node 29
      (canonicalCodeFormula A ∷
       canonicalCodeFormula B ∷
       canonicalCodeFormula C ∷
       canonicalCodeFormula D ∷
       []))

ImpAndIntro2RuleNat : ℕ → ℕ → Set
ImpAndIntro2RuleNat proof-code formula-code =
  Σ Formula
    (λ A →
      Σ Formula
        (λ B →
          Σ Formula
            (λ C →
              Σ Formula
                (λ D →
                  (proof-code ≡ ImpAndIntro2ProofCode A B C D) ×
                  (formula-code ≡
                   canonicalNatFormula (ImpAndIntro2Formula A B C D))))))

impAndIntro2RuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  ImpAndIntro2RuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
impAndIntro2RuleNat-to-decoded
  (A ,Σ (B ,Σ (C ,Σ (D ,Σ (proof-eq ,× formula-eq))))) =
  node 29
    (canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     canonicalCodeFormula C ∷
     canonicalCodeFormula D ∷
     [])
  ,Σ
  (ImpAndIntro2Formula A B C D ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 29
          (canonicalCodeFormula A ∷
           canonicalCodeFormula B ∷
           canonicalCodeFormula C ∷
           canonicalCodeFormula D ∷
           []))
      ≡
      just (ImpAndIntro2Formula A B C D)
    check-eq
      rewrite decodeCanonicalFormula-roundTrip A
            | decodeCanonicalFormula-roundTrip B
            | decodeCanonicalFormula-roundTrip C
            | decodeCanonicalFormula-roundTrip D =
      refl

AndBothMapFormula : Formula → Formula → Formula → Formula → Formula
AndBothMapFormula A B C D =
  (A ⇒ C) ⇒ ((B ⇒ D) ⇒ ((A ∧ B) ⇒ (C ∧ D)))

AndBothMapProofCode : Formula → Formula → Formula → Formula → ℕ
AndBothMapProofCode A B C D =
  encodeCode
    (node 30
      (canonicalCodeFormula A ∷
       canonicalCodeFormula B ∷
       canonicalCodeFormula C ∷
       canonicalCodeFormula D ∷
       []))

AndBothMapRuleNat : ℕ → ℕ → Set
AndBothMapRuleNat proof-code formula-code =
  Σ Formula
    (λ A →
      Σ Formula
        (λ B →
          Σ Formula
            (λ C →
              Σ Formula
                (λ D →
                  (proof-code ≡ AndBothMapProofCode A B C D) ×
                  (formula-code ≡
                   canonicalNatFormula (AndBothMapFormula A B C D))))))

andBothMapRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  AndBothMapRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
andBothMapRuleNat-to-decoded
  (A ,Σ (B ,Σ (C ,Σ (D ,Σ (proof-eq ,× formula-eq))))) =
  node 30
    (canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     canonicalCodeFormula C ∷
     canonicalCodeFormula D ∷
     [])
  ,Σ
  (AndBothMapFormula A B C D ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 30
          (canonicalCodeFormula A ∷
           canonicalCodeFormula B ∷
           canonicalCodeFormula C ∷
           canonicalCodeFormula D ∷
           []))
      ≡
      just (AndBothMapFormula A B C D)
    check-eq
      rewrite decodeCanonicalFormula-roundTrip A
            | decodeCanonicalFormula-roundTrip B
            | decodeCanonicalFormula-roundTrip C
            | decodeCanonicalFormula-roundTrip D =
      refl

AndLeftMapFormula : Formula → Formula → Formula → Formula
AndLeftMapFormula A B C =
  (A ⇒ C) ⇒ ((A ∧ B) ⇒ (C ∧ B))

AndLeftMapProofCode : Formula → Formula → Formula → ℕ
AndLeftMapProofCode A B C =
  encodeCode
    (node 31
      (canonicalCodeFormula A ∷
       canonicalCodeFormula B ∷
       canonicalCodeFormula C ∷
       []))

AndLeftMapRuleNat : ℕ → ℕ → Set
AndLeftMapRuleNat proof-code formula-code =
  Σ Formula
    (λ A →
      Σ Formula
        (λ B →
          Σ Formula
            (λ C →
              (proof-code ≡ AndLeftMapProofCode A B C) ×
              (formula-code ≡
               canonicalNatFormula (AndLeftMapFormula A B C)))))

andLeftMapRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  AndLeftMapRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
andLeftMapRuleNat-to-decoded
  (A ,Σ (B ,Σ (C ,Σ (proof-eq ,× formula-eq)))) =
  node 31
    (canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     canonicalCodeFormula C ∷
     [])
  ,Σ
  (AndLeftMapFormula A B C ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 31
          (canonicalCodeFormula A ∷
           canonicalCodeFormula B ∷
           canonicalCodeFormula C ∷
           []))
      ≡
      just (AndLeftMapFormula A B C)
    check-eq
      rewrite decodeCanonicalFormula-roundTrip A
            | decodeCanonicalFormula-roundTrip B
            | decodeCanonicalFormula-roundTrip C =
      refl

PremiseAndBothMapFormula :
  Formula → Formula → Formula → Formula → Formula → Formula
PremiseAndBothMapFormula E A B C D =
  (E ⇒ (A ⇒ C)) ⇒
  ((E ⇒ (B ⇒ D)) ⇒
   (E ⇒ ((A ∧ B) ⇒ (C ∧ D))))

PremiseAndBothMapProofCode :
  Formula → Formula → Formula → Formula → Formula → ℕ
PremiseAndBothMapProofCode E A B C D =
  encodeCode
    (node 32
      (canonicalCodeFormula E ∷
       canonicalCodeFormula A ∷
       canonicalCodeFormula B ∷
       canonicalCodeFormula C ∷
       canonicalCodeFormula D ∷
       []))

PremiseAndBothMapRuleNat : ℕ → ℕ → Set
PremiseAndBothMapRuleNat proof-code formula-code =
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
                       PremiseAndBothMapProofCode E A B C D) ×
                      (formula-code ≡
                       canonicalNatFormula
                        (PremiseAndBothMapFormula E A B C D)))))))

premiseAndBothMapRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  PremiseAndBothMapRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
premiseAndBothMapRuleNat-to-decoded
  (E ,Σ (A ,Σ (B ,Σ (C ,Σ (D ,Σ (proof-eq ,× formula-eq)))))) =
  node 32
    (canonicalCodeFormula E ∷
     canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     canonicalCodeFormula C ∷
     canonicalCodeFormula D ∷
     [])
  ,Σ
  (PremiseAndBothMapFormula E A B C D ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 32
          (canonicalCodeFormula E ∷
           canonicalCodeFormula A ∷
           canonicalCodeFormula B ∷
           canonicalCodeFormula C ∷
           canonicalCodeFormula D ∷
           []))
      ≡
      just (PremiseAndBothMapFormula E A B C D)
    check-eq
      rewrite decodeCanonicalFormula-roundTrip E
            | decodeCanonicalFormula-roundTrip A
            | decodeCanonicalFormula-roundTrip B
            | decodeCanonicalFormula-roundTrip C
            | decodeCanonicalFormula-roundTrip D =
      refl

PremiseAndLeftMapFormula : Formula → Formula → Formula → Formula → Formula
PremiseAndLeftMapFormula E A B C =
  (E ⇒ (A ⇒ C)) ⇒
  (E ⇒ ((A ∧ B) ⇒ (C ∧ B)))

PremiseAndLeftMapProofCode : Formula → Formula → Formula → Formula → ℕ
PremiseAndLeftMapProofCode E A B C =
  encodeCode
    (node 33
      (canonicalCodeFormula E ∷
       canonicalCodeFormula A ∷
       canonicalCodeFormula B ∷
       canonicalCodeFormula C ∷
       []))

PremiseAndLeftMapRuleNat : ℕ → ℕ → Set
PremiseAndLeftMapRuleNat proof-code formula-code =
  Σ Formula
    (λ E →
      Σ Formula
        (λ A →
          Σ Formula
            (λ B →
              Σ Formula
                (λ C →
                  (proof-code ≡ PremiseAndLeftMapProofCode E A B C) ×
                  (formula-code ≡
                   canonicalNatFormula
                    (PremiseAndLeftMapFormula E A B C))))))

premiseAndLeftMapRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  PremiseAndLeftMapRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
premiseAndLeftMapRuleNat-to-decoded
  (E ,Σ (A ,Σ (B ,Σ (C ,Σ (proof-eq ,× formula-eq))))) =
  node 33
    (canonicalCodeFormula E ∷
     canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     canonicalCodeFormula C ∷
     [])
  ,Σ
  (PremiseAndLeftMapFormula E A B C ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 33
          (canonicalCodeFormula E ∷
           canonicalCodeFormula A ∷
           canonicalCodeFormula B ∷
           canonicalCodeFormula C ∷
           []))
      ≡
      just (PremiseAndLeftMapFormula E A B C)
    check-eq
      rewrite decodeCanonicalFormula-roundTrip E
            | decodeCanonicalFormula-roundTrip A
            | decodeCanonicalFormula-roundTrip B
            | decodeCanonicalFormula-roundTrip C =
      refl

BodyUniqueComposeFormula :
  Formula → Formula → Formula → Formula → Formula → Formula → Formula → Formula
BodyUniqueComposeFormula A B C D E F G =
  (A ⇒ (C ⇒ E)) ⇒
  ((E ⇒ (B ⇒ F)) ⇒
   ((F ⇒ (D ⇒ G)) ⇒
    ((A ∧ B) ⇒ ((C ∧ D) ⇒ G))))

BodyUniqueComposeProofCode :
  Formula → Formula → Formula → Formula → Formula → Formula → Formula → ℕ
BodyUniqueComposeProofCode A B C D E F G =
  encodeCode
    (node 34
      (canonicalCodeFormula A ∷
       canonicalCodeFormula B ∷
       canonicalCodeFormula C ∷
       canonicalCodeFormula D ∷
       canonicalCodeFormula E ∷
       canonicalCodeFormula F ∷
       canonicalCodeFormula G ∷
       []))

BodyUniqueComposeRuleNat : ℕ → ℕ → Set
BodyUniqueComposeRuleNat proof-code formula-code =
  Σ Formula
    (λ A →
      Σ Formula
        (λ B →
          Σ Formula
            (λ C →
              Σ Formula
                (λ D →
                  Σ Formula
                    (λ E →
                      Σ Formula
                        (λ F →
                          Σ Formula
                            (λ G →
                              (proof-code ≡
                               BodyUniqueComposeProofCode A B C D E F G) ×
                              (formula-code ≡
                               canonicalNatFormula
                                (BodyUniqueComposeFormula
                                  A B C D E F G)))))))))

bodyUniqueComposeRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  BodyUniqueComposeRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
bodyUniqueComposeRuleNat-to-decoded
  (A ,Σ
    (B ,Σ
      (C ,Σ
        (D ,Σ
          (E ,Σ
            (F ,Σ
              (G ,Σ (proof-eq ,× formula-eq)))))))) =
  node 34
    (canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     canonicalCodeFormula C ∷
     canonicalCodeFormula D ∷
     canonicalCodeFormula E ∷
     canonicalCodeFormula F ∷
     canonicalCodeFormula G ∷
     [])
  ,Σ
  (BodyUniqueComposeFormula A B C D E F G ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 34
          (canonicalCodeFormula A ∷
           canonicalCodeFormula B ∷
           canonicalCodeFormula C ∷
           canonicalCodeFormula D ∷
           canonicalCodeFormula E ∷
           canonicalCodeFormula F ∷
           canonicalCodeFormula G ∷
           []))
      ≡
      just (BodyUniqueComposeFormula A B C D E F G)
    check-eq
      rewrite decodeCanonicalFormula-roundTrip A
            | decodeCanonicalFormula-roundTrip B
            | decodeCanonicalFormula-roundTrip C
            | decodeCanonicalFormula-roundTrip D
            | decodeCanonicalFormula-roundTrip E
            | decodeCanonicalFormula-roundTrip F
            | decodeCanonicalFormula-roundTrip G =
      refl

ContradictionToNegFormula : Formula → Formula → Formula
ContradictionToNegFormula A B =
  (A ⇒ B) ⇒ (¬ᶠ B ⇒ ¬ᶠ A)

ContradictionToNegProofCode : Formula → Formula → ℕ
ContradictionToNegProofCode A B =
  encodeCode
    (node 38
      (canonicalCodeFormula A ∷
       canonicalCodeFormula B ∷
       []))

ContradictionToNegRuleNat : ℕ → ℕ → Set
ContradictionToNegRuleNat proof-code formula-code =
  Σ Formula
    (λ A →
      Σ Formula
        (λ B →
          (proof-code ≡ ContradictionToNegProofCode A B) ×
          (formula-code ≡
           canonicalNatFormula (ContradictionToNegFormula A B))))

contradictionToNegRuleNat-to-decoded :
  {proof-code formula-code : ℕ} →
  ContradictionToNegRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
contradictionToNegRuleNat-to-decoded
  (A ,Σ (B ,Σ (proof-eq ,× formula-eq))) =
  node 38
    (canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     [])
  ,Σ
  (ContradictionToNegFormula A B ,Σ
    (proof-eq ,×
     (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode
        (node 38
          (canonicalCodeFormula A ∷
           canonicalCodeFormula B ∷
           []))
      ≡
      just (ContradictionToNegFormula A B)
    check-eq
      rewrite decodeCanonicalFormula-roundTrip A
            | decodeCanonicalFormula-roundTrip B =
      refl

ProofRuleAndLeftImpPR : Set₁
ProofRuleAndLeftImpPR =
  ProofRuleDerivedLogicalPR AndLeftImpRuleNat

ProofRuleAndRightImpPR : Set₁
ProofRuleAndRightImpPR =
  ProofRuleDerivedLogicalPR AndRightImpRuleNat

ProofRuleAndLeftImp1PR : Set₁
ProofRuleAndLeftImp1PR =
  ProofRuleDerivedLogicalPR AndLeftImp1RuleNat

ProofRuleAndRightImp1PR : Set₁
ProofRuleAndRightImp1PR =
  ProofRuleDerivedLogicalPR AndRightImp1RuleNat

ProofRuleImpAndIntro2PR : Set₁
ProofRuleImpAndIntro2PR =
  ProofRuleDerivedLogicalPR ImpAndIntro2RuleNat

ProofRuleAndBothMapPR : Set₁
ProofRuleAndBothMapPR =
  ProofRuleDerivedLogicalPR AndBothMapRuleNat

ProofRuleAndLeftMapPR : Set₁
ProofRuleAndLeftMapPR =
  ProofRuleDerivedLogicalPR AndLeftMapRuleNat

ProofRulePremiseAndBothMapPR : Set₁
ProofRulePremiseAndBothMapPR =
  ProofRuleDerivedLogicalPR PremiseAndBothMapRuleNat

ProofRulePremiseAndLeftMapPR : Set₁
ProofRulePremiseAndLeftMapPR =
  ProofRuleDerivedLogicalPR PremiseAndLeftMapRuleNat

ProofRuleBodyUniqueComposePR : Set₁
ProofRuleBodyUniqueComposePR =
  ProofRuleDerivedLogicalPR BodyUniqueComposeRuleNat

ProofRuleContradictionToNegPR : Set₁
ProofRuleContradictionToNegPR =
  ProofRuleDerivedLogicalPR ContradictionToNegRuleNat

ProofRuleAndLeftImpCheckingBranchData : Set₁
ProofRuleAndLeftImpCheckingBranchData =
  ProofRuleDerivedLogicalCheckingBranchData AndLeftImpRuleNat

ProofRuleAndRightImpCheckingBranchData : Set₁
ProofRuleAndRightImpCheckingBranchData =
  ProofRuleDerivedLogicalCheckingBranchData AndRightImpRuleNat

ProofRuleAndLeftImp1CheckingBranchData : Set₁
ProofRuleAndLeftImp1CheckingBranchData =
  ProofRuleDerivedLogicalCheckingBranchData AndLeftImp1RuleNat

ProofRuleAndRightImp1CheckingBranchData : Set₁
ProofRuleAndRightImp1CheckingBranchData =
  ProofRuleDerivedLogicalCheckingBranchData AndRightImp1RuleNat

ProofRuleImpAndIntro2CheckingBranchData : Set₁
ProofRuleImpAndIntro2CheckingBranchData =
  ProofRuleDerivedLogicalCheckingBranchData ImpAndIntro2RuleNat

ProofRuleAndBothMapCheckingBranchData : Set₁
ProofRuleAndBothMapCheckingBranchData =
  ProofRuleDerivedLogicalCheckingBranchData AndBothMapRuleNat

ProofRuleAndLeftMapCheckingBranchData : Set₁
ProofRuleAndLeftMapCheckingBranchData =
  ProofRuleDerivedLogicalCheckingBranchData AndLeftMapRuleNat

ProofRulePremiseAndBothMapCheckingBranchData : Set₁
ProofRulePremiseAndBothMapCheckingBranchData =
  ProofRuleDerivedLogicalCheckingBranchData PremiseAndBothMapRuleNat

ProofRulePremiseAndLeftMapCheckingBranchData : Set₁
ProofRulePremiseAndLeftMapCheckingBranchData =
  ProofRuleDerivedLogicalCheckingBranchData PremiseAndLeftMapRuleNat

ProofRuleBodyUniqueComposeCheckingBranchData : Set₁
ProofRuleBodyUniqueComposeCheckingBranchData =
  ProofRuleDerivedLogicalCheckingBranchData BodyUniqueComposeRuleNat

ProofRuleContradictionToNegCheckingBranchData : Set₁
ProofRuleContradictionToNegCheckingBranchData =
  ProofRuleDerivedLogicalCheckingBranchData ContradictionToNegRuleNat

proofRuleAndLeftImpTargetedBranch :
  ProofRuleAndLeftImpCheckingBranchData →
  TargetedProofCheckingBranchPR AndLeftImpRuleNat
proofRuleAndLeftImpTargetedBranch =
  proofRuleDerivedLogicalTargetedBranch andLeftImpRuleNat-to-decoded

proofRuleAndRightImpTargetedBranch :
  ProofRuleAndRightImpCheckingBranchData →
  TargetedProofCheckingBranchPR AndRightImpRuleNat
proofRuleAndRightImpTargetedBranch =
  proofRuleDerivedLogicalTargetedBranch andRightImpRuleNat-to-decoded

proofRuleAndLeftImp1TargetedBranch :
  ProofRuleAndLeftImp1CheckingBranchData →
  TargetedProofCheckingBranchPR AndLeftImp1RuleNat
proofRuleAndLeftImp1TargetedBranch =
  proofRuleDerivedLogicalTargetedBranch andLeftImp1RuleNat-to-decoded

proofRuleAndRightImp1TargetedBranch :
  ProofRuleAndRightImp1CheckingBranchData →
  TargetedProofCheckingBranchPR AndRightImp1RuleNat
proofRuleAndRightImp1TargetedBranch =
  proofRuleDerivedLogicalTargetedBranch andRightImp1RuleNat-to-decoded

proofRuleImpAndIntro2TargetedBranch :
  ProofRuleImpAndIntro2CheckingBranchData →
  TargetedProofCheckingBranchPR ImpAndIntro2RuleNat
proofRuleImpAndIntro2TargetedBranch =
  proofRuleDerivedLogicalTargetedBranch impAndIntro2RuleNat-to-decoded

proofRuleAndBothMapTargetedBranch :
  ProofRuleAndBothMapCheckingBranchData →
  TargetedProofCheckingBranchPR AndBothMapRuleNat
proofRuleAndBothMapTargetedBranch =
  proofRuleDerivedLogicalTargetedBranch andBothMapRuleNat-to-decoded

proofRuleAndLeftMapTargetedBranch :
  ProofRuleAndLeftMapCheckingBranchData →
  TargetedProofCheckingBranchPR AndLeftMapRuleNat
proofRuleAndLeftMapTargetedBranch =
  proofRuleDerivedLogicalTargetedBranch andLeftMapRuleNat-to-decoded

proofRulePremiseAndBothMapTargetedBranch :
  ProofRulePremiseAndBothMapCheckingBranchData →
  TargetedProofCheckingBranchPR PremiseAndBothMapRuleNat
proofRulePremiseAndBothMapTargetedBranch =
  proofRuleDerivedLogicalTargetedBranch premiseAndBothMapRuleNat-to-decoded

proofRulePremiseAndLeftMapTargetedBranch :
  ProofRulePremiseAndLeftMapCheckingBranchData →
  TargetedProofCheckingBranchPR PremiseAndLeftMapRuleNat
proofRulePremiseAndLeftMapTargetedBranch =
  proofRuleDerivedLogicalTargetedBranch premiseAndLeftMapRuleNat-to-decoded

proofRuleBodyUniqueComposeTargetedBranch :
  ProofRuleBodyUniqueComposeCheckingBranchData →
  TargetedProofCheckingBranchPR BodyUniqueComposeRuleNat
proofRuleBodyUniqueComposeTargetedBranch =
  proofRuleDerivedLogicalTargetedBranch bodyUniqueComposeRuleNat-to-decoded

proofRuleContradictionToNegTargetedBranch :
  ProofRuleContradictionToNegCheckingBranchData →
  TargetedProofCheckingBranchPR ContradictionToNegRuleNat
proofRuleContradictionToNegTargetedBranch =
  proofRuleDerivedLogicalTargetedBranch contradictionToNegRuleNat-to-decoded
