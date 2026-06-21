{-# OPTIONS --safe #-}

module Godel.ProofCheckingTargetCoverage where

open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.PA
  using (induction)
open import Godel.CanonicalCoding
  using
    ( Code
    ; atom
    ; canonicalCodeFormula
    ; canonicalCodeTerm
    ; canonicalNatFormula
    ; encodeCode
    ; node
    )
open import Godel.ProofCanonicalChecker
  using
    ( decodeCanonicalFormula
    ; decodeCanonicalFormula-sound
    ; decodeCanonicalTerm
    ; decodeCanonicalTerm-sound
    )
open import Godel.ProofCheckingBranch
open import Godel.ProofCheckingBranchBundle
  using
    ( ProofCheckingFixedRule37HilbertKExcludedSTarget
    ; ProofCheckingFixedRule37HilbertKExcludedTarget
    ; ProofCheckingFixedRule37HilbertKTarget
    ; ProofCheckingFixedAndRule37Target
    )
open import Godel.ProofCheckingRecursiveBundle
  using (RecursiveTarget₂)
open import Godel.ProofCheckingSubstitutionBundle
  using (SubstitutionTarget₂)
open import Godel.ProofCheckingEqualityBundle
  using (EqualityTarget₆)
open import Godel.ProofCheckingEqualitySubstitutionBundle
  using (EqualitySubstitutionTarget₃)
open import Godel.ProofCheckingDerivedLogicalBundle
  using (DerivedLogicalTarget₁₁)
open import Godel.ProofCheckingQuantifierBundle
  using (QuantifierTarget₅)
open import Godel.ProofCheckingLogicalBundle
  using (LogicalTarget₅)
open import Godel.ProofCheckingFixedLeafBranches
  using (FixedLeafTarget₆)
open import Godel.ProofCheckingTargetOverview
  using (CurrentProofCheckingTarget)
open import Godel.ProofRuleFixedCodeLeaf
  using (FixedCodeLeafData)
open import Godel.ProofRulePAAxiomInduction
  using (InductionAxiomRuleNat)
open import Godel.ProofRuleHilbertK
  using (HilbertKRuleNat)
open import Godel.ProofRuleHilbertS
  using (HilbertSRuleNat)
open import Godel.ProofRuleExcludedMiddle
  using (ExcludedMiddleRuleNat)
open import Godel.ProofRuleSubstitutionSchemas
  using
    ( ForallEliminateRuleNat
    ; ExistsIntroduceRuleNat
    )
open import Godel.ProofRuleLogicalConnectives
  using
    ( AndIntroRuleNat
    ; AndElimLeftRuleNat
    ; AndElimRightRuleNat
    ; OrIntroLeftRuleNat
    ; OrIntroRightRuleNat
    )
open import Godel.ProofRuleEqRefl
  using (EqReflRuleNat)
open import Godel.ProofRuleEqualitySchemas
  using
    ( EqSymRuleNat
    ; EqTransRuleNat
    ; SucCongRuleNat
    ; AddCongRuleNat
    ; MulCongRuleNat
    )
open import Godel.ProofRuleEqualitySubstitution
  using
    ( EqUniqueValueRuleNat
    ; EqSubstRightRuleNat
    ; EqSubstSucRightRuleNat
    )
open import Godel.ProofRuleDerivedLogicalSchemas
  using
    ( AndLeftImpRuleNat
    ; AndRightImpRuleNat
    ; AndLeftImp1RuleNat
    ; AndRightImp1RuleNat
    ; ImpAndIntro2RuleNat
    ; AndBothMapRuleNat
    ; AndLeftMapRuleNat
    ; PremiseAndBothMapRuleNat
    ; PremiseAndLeftMapRuleNat
    ; BodyUniqueComposeRuleNat
    ; ContradictionToNegRuleNat
    )
open import Godel.ProofRuleQuantifierSchemas
  using
    ( ExistsElimRuleNat
    ; ExistsPrefixIntroduceRuleNat
    ; ExistsPrefixBinaryLiftRuleNat
    ; ExistsPrefixPremiseMapRuleNat
    ; PremiseChangeRuleNat
    )
open import Godel.ProofSystem
  using (exists-prefix)

inject-base :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  ProofCheckingFixedRule37HilbertKExcludedSTarget
    d0 d1 d2 d3 d4 d5
    proof-code
    formula-code →
  CurrentProofCheckingTarget
    d0 d1 d2 d3 d4 d5
    proof-code
    formula-code
inject-base =
  branch-left

inject-induction :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  InductionAxiomRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-induction target =
  branch-right (branch-left target)

inject-recursive :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  RecursiveTarget₂ proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-recursive target =
  branch-right (branch-right (branch-left target))

inject-substitution :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  SubstitutionTarget₂ proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-substitution target =
  branch-right (branch-right (branch-right (branch-left target)))

inject-equality :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  EqualityTarget₆ proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-equality target =
  branch-right (branch-right (branch-right (branch-right (branch-left target))))

inject-equality-substitution :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  EqualitySubstitutionTarget₃ proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-equality-substitution target =
  branch-right
    (branch-right
      (branch-right
        (branch-right
          (branch-right (branch-left target)))))

inject-derived-logical :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  DerivedLogicalTarget₁₁ proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-derived-logical target =
  branch-right
    (branch-right
      (branch-right
        (branch-right
          (branch-right
            (branch-right (branch-left target))))))

inject-and-left-imp :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  AndLeftImpRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-and-left-imp target =
  inject-derived-logical
    (branch-left (branch-left (branch-left target)))

inject-and-right-imp :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  AndRightImpRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-and-right-imp target =
  inject-derived-logical
    (branch-left (branch-left (branch-right target)))

inject-and-left-imp1 :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  AndLeftImp1RuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-and-left-imp1 target =
  inject-derived-logical
    (branch-left (branch-right (branch-left target)))

inject-and-right-imp1 :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  AndRightImp1RuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-and-right-imp1 target =
  inject-derived-logical
    (branch-left (branch-right (branch-right (branch-left target))))

inject-imp-and-intro2 :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  ImpAndIntro2RuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-imp-and-intro2 target =
  inject-derived-logical
    (branch-left (branch-right (branch-right (branch-right target))))

inject-and-both-map :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  AndBothMapRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-and-both-map target =
  inject-derived-logical
    (branch-right (branch-left (branch-left target)))

inject-and-left-map :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  AndLeftMapRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-and-left-map target =
  inject-derived-logical
    (branch-right (branch-left (branch-right (branch-left target))))

inject-premise-and-both-map :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  PremiseAndBothMapRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-premise-and-both-map target =
  inject-derived-logical
    (branch-right (branch-left (branch-right (branch-right target))))

inject-premise-and-left-map :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  PremiseAndLeftMapRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-premise-and-left-map target =
  inject-derived-logical
    (branch-right (branch-right (branch-left target)))

inject-body-unique-compose :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  BodyUniqueComposeRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-body-unique-compose target =
  inject-derived-logical
    (branch-right (branch-right (branch-right (branch-left target))))

inject-contradiction-to-neg :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  ContradictionToNegRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-contradiction-to-neg target =
  inject-derived-logical
    (branch-right (branch-right (branch-right (branch-right target))))

inject-quantifier :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  QuantifierTarget₅ proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-quantifier target =
  branch-right
    (branch-right
      (branch-right
        (branch-right
          (branch-right
            (branch-right (branch-right (branch-left target)))))))

inject-logical :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  LogicalTarget₅ proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-logical target =
  branch-right
    (branch-right
      (branch-right
        (branch-right
          (branch-right
            (branch-right (branch-right (branch-right target)))))))

inject-fixed-rule37 :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  ProofCheckingFixedAndRule37Target
    d0 d1 d2 d3 d4 d5
    proof-code
    formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-fixed-rule37 target =
  inject-base
    (branch-left (branch-left (branch-left target)))

inject-hilbertK :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  HilbertKRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-hilbertK target =
  inject-base
    (branch-left (branch-left (branch-right target)))

inject-excluded-middle :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  ExcludedMiddleRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-excluded-middle target =
  inject-base
    (branch-left (branch-right target))

inject-hilbertS :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  HilbertSRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-hilbertS target =
  inject-base
    (branch-right target)

inject-forall-eliminate :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  ForallEliminateRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-forall-eliminate target =
  inject-substitution (branch-left target)

inject-exists-introduce :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  ExistsIntroduceRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-exists-introduce target =
  inject-substitution (branch-right target)

inject-and-intro :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  AndIntroRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-and-intro target =
  inject-logical (branch-left (branch-left (branch-left target)))

inject-and-elim-left :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  AndElimLeftRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-and-elim-left target =
  inject-logical (branch-left (branch-left (branch-right target)))

inject-and-elim-right :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  AndElimRightRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-and-elim-right target =
  inject-logical (branch-left (branch-right (branch-left target)))

inject-or-intro-left :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  OrIntroLeftRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-or-intro-left target =
  inject-logical (branch-left (branch-right (branch-right target)))

inject-or-intro-right :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  OrIntroRightRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-or-intro-right target =
  inject-logical (branch-right target)

inject-eq-refl :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  EqReflRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-eq-refl target =
  inject-equality (branch-left (branch-left (branch-left target)))

inject-eq-sym :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  EqSymRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-eq-sym target =
  inject-equality (branch-left (branch-left (branch-right target)))

inject-eq-trans :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  EqTransRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-eq-trans target =
  inject-equality (branch-left (branch-right (branch-left target)))

inject-suc-cong :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  SucCongRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-suc-cong target =
  inject-equality (branch-left (branch-right (branch-right target)))

inject-add-cong :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  AddCongRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-add-cong target =
  inject-equality (branch-right (branch-left target))

inject-mul-cong :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  MulCongRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-mul-cong target =
  inject-equality (branch-right (branch-right target))

inject-eq-unique-value :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  EqUniqueValueRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-eq-unique-value target =
  inject-equality-substitution (branch-left target)

inject-eq-subst-right :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  EqSubstRightRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-eq-subst-right target =
  inject-equality-substitution (branch-right (branch-left target))

inject-eq-subst-suc-right :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  EqSubstSucRightRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-eq-subst-suc-right target =
  inject-equality-substitution (branch-right (branch-right target))

inject-exists-elim :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  ExistsElimRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-exists-elim target =
  inject-quantifier (branch-left (branch-left (branch-left target)))

inject-exists-prefix-introduce :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  ExistsPrefixIntroduceRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-exists-prefix-introduce target =
  inject-quantifier (branch-left (branch-left (branch-right target)))

inject-exists-prefix-binary-lift :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  ExistsPrefixBinaryLiftRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-exists-prefix-binary-lift target =
  inject-quantifier (branch-left (branch-right (branch-left target)))

inject-exists-prefix-premise-map :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  ExistsPrefixPremiseMapRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-exists-prefix-premise-map target =
  inject-quantifier (branch-left (branch-right (branch-right target)))

inject-premise-change :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  PremiseChangeRuleNat proof-code formula-code →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inject-premise-change target =
  inject-quantifier (branch-right target)

hilbertKDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (a b : Code) →
  (A B : Formula) →
  proof-code ≡ encodeCode (node 1 (a ∷ b ∷ [])) →
  formula-code ≡ canonicalNatFormula (A ⇒ (B ⇒ A)) →
  decodeCanonicalFormula a ≡ just A →
  decodeCanonicalFormula b ≡ just B →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
hilbertKDecodedCoverage a b A B proof-eq formula-eq a-eq b-eq
  rewrite decodeCanonicalFormula-sound a A a-eq
        | decodeCanonicalFormula-sound b B b-eq =
  inject-hilbertK
    (A ,Σ (B ,Σ (proof-eq ,× formula-eq)))

hilbertSDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (a b c : Code) →
  (A B C : Formula) →
  proof-code ≡ encodeCode (node 2 (a ∷ b ∷ c ∷ [])) →
  formula-code ≡
    canonicalNatFormula
      ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C))) →
  decodeCanonicalFormula a ≡ just A →
  decodeCanonicalFormula b ≡ just B →
  decodeCanonicalFormula c ≡ just C →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
hilbertSDecodedCoverage a b c A B C proof-eq formula-eq a-eq b-eq c-eq
  rewrite decodeCanonicalFormula-sound a A a-eq
        | decodeCanonicalFormula-sound b B b-eq
        | decodeCanonicalFormula-sound c C c-eq =
  inject-hilbertS
    (A ,Σ (B ,Σ (C ,Σ (proof-eq ,× formula-eq))))

excludedMiddleDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (a : Code) →
  (A : Formula) →
  proof-code ≡ encodeCode (node 3 (a ∷ [])) →
  formula-code ≡ canonicalNatFormula (A ∨ ¬ᶠ A) →
  decodeCanonicalFormula a ≡ just A →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
excludedMiddleDecodedCoverage a A proof-eq formula-eq a-eq
  rewrite decodeCanonicalFormula-sound a A a-eq =
  inject-excluded-middle
    (A ,Σ (proof-eq ,× formula-eq))

inductionAxiomDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (a : Code) →
  (A : Formula) →
  proof-code ≡ encodeCode (node 0 (node 6 (a ∷ []) ∷ [])) →
  formula-code ≡ canonicalNatFormula (induction A) →
  decodeCanonicalFormula a ≡ just A →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
inductionAxiomDecodedCoverage a A proof-eq formula-eq a-eq
  rewrite decodeCanonicalFormula-sound a A a-eq =
  inject-induction
    (A ,Σ (proof-eq ,× formula-eq))

forallEliminateDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (a t : Code) →
  (A : Formula) →
  (u : Term) →
  proof-code ≡ encodeCode (node 6 (a ∷ t ∷ [])) →
  formula-code ≡ canonicalNatFormula ((∀ᶠ A) ⇒ subst0 u A) →
  decodeCanonicalFormula a ≡ just A →
  decodeCanonicalTerm t ≡ just u →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
forallEliminateDecodedCoverage a t A u proof-eq formula-eq a-eq t-eq
  rewrite decodeCanonicalFormula-sound a A a-eq
        | decodeCanonicalTerm-sound t u t-eq =
  inject-forall-eliminate
    (A ,Σ (u ,Σ (proof-eq ,× formula-eq)))

existsIntroduceDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (a t : Code) →
  (A : Formula) →
  (u : Term) →
  proof-code ≡ encodeCode (node 7 (a ∷ t ∷ [])) →
  formula-code ≡ canonicalNatFormula (subst0 u A ⇒ ∃ᶠ A) →
  decodeCanonicalFormula a ≡ just A →
  decodeCanonicalTerm t ≡ just u →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
existsIntroduceDecodedCoverage a t A u proof-eq formula-eq a-eq t-eq
  rewrite decodeCanonicalFormula-sound a A a-eq
        | decodeCanonicalTerm-sound t u t-eq =
  inject-exists-introduce
    (A ,Σ (u ,Σ (proof-eq ,× formula-eq)))

andIntroDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (a b : Code) →
  (A B : Formula) →
  proof-code ≡ encodeCode (node 19 (a ∷ b ∷ [])) →
  formula-code ≡ canonicalNatFormula (A ⇒ (B ⇒ (A ∧ B))) →
  decodeCanonicalFormula a ≡ just A →
  decodeCanonicalFormula b ≡ just B →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
andIntroDecodedCoverage a b A B proof-eq formula-eq a-eq b-eq
  rewrite decodeCanonicalFormula-sound a A a-eq
        | decodeCanonicalFormula-sound b B b-eq =
  inject-and-intro
    (A ,Σ (B ,Σ (proof-eq ,× formula-eq)))

andElimLeftDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (a b : Code) →
  (A B : Formula) →
  proof-code ≡ encodeCode (node 20 (a ∷ b ∷ [])) →
  formula-code ≡ canonicalNatFormula ((A ∧ B) ⇒ A) →
  decodeCanonicalFormula a ≡ just A →
  decodeCanonicalFormula b ≡ just B →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
andElimLeftDecodedCoverage a b A B proof-eq formula-eq a-eq b-eq
  rewrite decodeCanonicalFormula-sound a A a-eq
        | decodeCanonicalFormula-sound b B b-eq =
  inject-and-elim-left
    (A ,Σ (B ,Σ (proof-eq ,× formula-eq)))

andElimRightDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (a b : Code) →
  (A B : Formula) →
  proof-code ≡ encodeCode (node 21 (a ∷ b ∷ [])) →
  formula-code ≡ canonicalNatFormula ((A ∧ B) ⇒ B) →
  decodeCanonicalFormula a ≡ just A →
  decodeCanonicalFormula b ≡ just B →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
andElimRightDecodedCoverage a b A B proof-eq formula-eq a-eq b-eq
  rewrite decodeCanonicalFormula-sound a A a-eq
        | decodeCanonicalFormula-sound b B b-eq =
  inject-and-elim-right
    (A ,Σ (B ,Σ (proof-eq ,× formula-eq)))

orIntroLeftDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (a b : Code) →
  (A B : Formula) →
  proof-code ≡ encodeCode (node 22 (a ∷ b ∷ [])) →
  formula-code ≡ canonicalNatFormula (A ⇒ (A ∨ B)) →
  decodeCanonicalFormula a ≡ just A →
  decodeCanonicalFormula b ≡ just B →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
orIntroLeftDecodedCoverage a b A B proof-eq formula-eq a-eq b-eq
  rewrite decodeCanonicalFormula-sound a A a-eq
        | decodeCanonicalFormula-sound b B b-eq =
  inject-or-intro-left
    (A ,Σ (B ,Σ (proof-eq ,× formula-eq)))

orIntroRightDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (a b : Code) →
  (A B : Formula) →
  proof-code ≡ encodeCode (node 23 (a ∷ b ∷ [])) →
  formula-code ≡ canonicalNatFormula (B ⇒ (A ∨ B)) →
  decodeCanonicalFormula a ≡ just A →
  decodeCanonicalFormula b ≡ just B →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
orIntroRightDecodedCoverage a b A B proof-eq formula-eq a-eq b-eq
  rewrite decodeCanonicalFormula-sound a A a-eq
        | decodeCanonicalFormula-sound b B b-eq =
  inject-or-intro-right
    (A ,Σ (B ,Σ (proof-eq ,× formula-eq)))

andLeftImpDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (a b c d e : Code) →
  (A B C D E : Formula) →
  proof-code ≡ encodeCode (node 25 (a ∷ b ∷ c ∷ d ∷ e ∷ [])) →
  formula-code ≡
    canonicalNatFormula
      ((A ⇒ (C ⇒ E)) ⇒ ((A ∧ B) ⇒ ((C ∧ D) ⇒ E))) →
  decodeCanonicalFormula a ≡ just A →
  decodeCanonicalFormula b ≡ just B →
  decodeCanonicalFormula c ≡ just C →
  decodeCanonicalFormula d ≡ just D →
  decodeCanonicalFormula e ≡ just E →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
andLeftImpDecodedCoverage
  a b c d e A B C D E proof-eq formula-eq a-eq b-eq c-eq d-eq e-eq
  rewrite decodeCanonicalFormula-sound a A a-eq
        | decodeCanonicalFormula-sound b B b-eq
        | decodeCanonicalFormula-sound c C c-eq
        | decodeCanonicalFormula-sound d D d-eq
        | decodeCanonicalFormula-sound e E e-eq =
  inject-and-left-imp
    (A ,Σ (B ,Σ (C ,Σ (D ,Σ (E ,Σ (proof-eq ,× formula-eq))))))

andRightImpDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (a b c d e : Code) →
  (A B C D E : Formula) →
  proof-code ≡ encodeCode (node 26 (a ∷ b ∷ c ∷ d ∷ e ∷ [])) →
  formula-code ≡
    canonicalNatFormula
      ((B ⇒ (D ⇒ E)) ⇒ ((A ∧ B) ⇒ ((C ∧ D) ⇒ E))) →
  decodeCanonicalFormula a ≡ just A →
  decodeCanonicalFormula b ≡ just B →
  decodeCanonicalFormula c ≡ just C →
  decodeCanonicalFormula d ≡ just D →
  decodeCanonicalFormula e ≡ just E →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
andRightImpDecodedCoverage
  a b c d e A B C D E proof-eq formula-eq a-eq b-eq c-eq d-eq e-eq
  rewrite decodeCanonicalFormula-sound a A a-eq
        | decodeCanonicalFormula-sound b B b-eq
        | decodeCanonicalFormula-sound c C c-eq
        | decodeCanonicalFormula-sound d D d-eq
        | decodeCanonicalFormula-sound e E e-eq =
  inject-and-right-imp
    (A ,Σ (B ,Σ (C ,Σ (D ,Σ (E ,Σ (proof-eq ,× formula-eq))))))

andLeftImp1DecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (a b c e : Code) →
  (A B C E : Formula) →
  proof-code ≡ encodeCode (node 27 (a ∷ b ∷ c ∷ e ∷ [])) →
  formula-code ≡
    canonicalNatFormula
      ((A ⇒ (C ⇒ E)) ⇒ ((A ∧ B) ⇒ (C ⇒ E))) →
  decodeCanonicalFormula a ≡ just A →
  decodeCanonicalFormula b ≡ just B →
  decodeCanonicalFormula c ≡ just C →
  decodeCanonicalFormula e ≡ just E →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
andLeftImp1DecodedCoverage
  a b c e A B C E proof-eq formula-eq a-eq b-eq c-eq e-eq
  rewrite decodeCanonicalFormula-sound a A a-eq
        | decodeCanonicalFormula-sound b B b-eq
        | decodeCanonicalFormula-sound c C c-eq
        | decodeCanonicalFormula-sound e E e-eq =
  inject-and-left-imp1
    (A ,Σ (B ,Σ (C ,Σ (E ,Σ (proof-eq ,× formula-eq)))))

andRightImp1DecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (a b c e : Code) →
  (A B C E : Formula) →
  proof-code ≡ encodeCode (node 28 (a ∷ b ∷ c ∷ e ∷ [])) →
  formula-code ≡
    canonicalNatFormula
      ((B ⇒ (C ⇒ E)) ⇒ ((A ∧ B) ⇒ (C ⇒ E))) →
  decodeCanonicalFormula a ≡ just A →
  decodeCanonicalFormula b ≡ just B →
  decodeCanonicalFormula c ≡ just C →
  decodeCanonicalFormula e ≡ just E →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
andRightImp1DecodedCoverage
  a b c e A B C E proof-eq formula-eq a-eq b-eq c-eq e-eq
  rewrite decodeCanonicalFormula-sound a A a-eq
        | decodeCanonicalFormula-sound b B b-eq
        | decodeCanonicalFormula-sound c C c-eq
        | decodeCanonicalFormula-sound e E e-eq =
  inject-and-right-imp1
    (A ,Σ (B ,Σ (C ,Σ (E ,Σ (proof-eq ,× formula-eq)))))

impAndIntro2DecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (a b c d : Code) →
  (A B C D : Formula) →
  proof-code ≡ encodeCode (node 29 (a ∷ b ∷ c ∷ d ∷ [])) →
  formula-code ≡
    canonicalNatFormula
      ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ (B ⇒ D)) ⇒ (A ⇒ (B ⇒ (C ∧ D))))) →
  decodeCanonicalFormula a ≡ just A →
  decodeCanonicalFormula b ≡ just B →
  decodeCanonicalFormula c ≡ just C →
  decodeCanonicalFormula d ≡ just D →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
impAndIntro2DecodedCoverage
  a b c d A B C D proof-eq formula-eq a-eq b-eq c-eq d-eq
  rewrite decodeCanonicalFormula-sound a A a-eq
        | decodeCanonicalFormula-sound b B b-eq
        | decodeCanonicalFormula-sound c C c-eq
        | decodeCanonicalFormula-sound d D d-eq =
  inject-imp-and-intro2
    (A ,Σ (B ,Σ (C ,Σ (D ,Σ (proof-eq ,× formula-eq)))))

andBothMapDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (a b c d : Code) →
  (A B C D : Formula) →
  proof-code ≡ encodeCode (node 30 (a ∷ b ∷ c ∷ d ∷ [])) →
  formula-code ≡
    canonicalNatFormula
      ((A ⇒ C) ⇒ ((B ⇒ D) ⇒ ((A ∧ B) ⇒ (C ∧ D)))) →
  decodeCanonicalFormula a ≡ just A →
  decodeCanonicalFormula b ≡ just B →
  decodeCanonicalFormula c ≡ just C →
  decodeCanonicalFormula d ≡ just D →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
andBothMapDecodedCoverage
  a b c d A B C D proof-eq formula-eq a-eq b-eq c-eq d-eq
  rewrite decodeCanonicalFormula-sound a A a-eq
        | decodeCanonicalFormula-sound b B b-eq
        | decodeCanonicalFormula-sound c C c-eq
        | decodeCanonicalFormula-sound d D d-eq =
  inject-and-both-map
    (A ,Σ (B ,Σ (C ,Σ (D ,Σ (proof-eq ,× formula-eq)))))

andLeftMapDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (a b c : Code) →
  (A B C : Formula) →
  proof-code ≡ encodeCode (node 31 (a ∷ b ∷ c ∷ [])) →
  formula-code ≡ canonicalNatFormula ((A ⇒ C) ⇒ ((A ∧ B) ⇒ (C ∧ B))) →
  decodeCanonicalFormula a ≡ just A →
  decodeCanonicalFormula b ≡ just B →
  decodeCanonicalFormula c ≡ just C →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
andLeftMapDecodedCoverage a b c A B C proof-eq formula-eq a-eq b-eq c-eq
  rewrite decodeCanonicalFormula-sound a A a-eq
        | decodeCanonicalFormula-sound b B b-eq
        | decodeCanonicalFormula-sound c C c-eq =
  inject-and-left-map
    (A ,Σ (B ,Σ (C ,Σ (proof-eq ,× formula-eq))))

premiseAndBothMapDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (e a b c d : Code) →
  (E A B C D : Formula) →
  proof-code ≡ encodeCode (node 32 (e ∷ a ∷ b ∷ c ∷ d ∷ [])) →
  formula-code ≡
    canonicalNatFormula
      ((E ⇒ (A ⇒ C)) ⇒ ((E ⇒ (B ⇒ D)) ⇒ (E ⇒ ((A ∧ B) ⇒ (C ∧ D))))) →
  decodeCanonicalFormula e ≡ just E →
  decodeCanonicalFormula a ≡ just A →
  decodeCanonicalFormula b ≡ just B →
  decodeCanonicalFormula c ≡ just C →
  decodeCanonicalFormula d ≡ just D →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
premiseAndBothMapDecodedCoverage
  e a b c d E A B C D proof-eq formula-eq e-eq a-eq b-eq c-eq d-eq
  rewrite decodeCanonicalFormula-sound e E e-eq
        | decodeCanonicalFormula-sound a A a-eq
        | decodeCanonicalFormula-sound b B b-eq
        | decodeCanonicalFormula-sound c C c-eq
        | decodeCanonicalFormula-sound d D d-eq =
  inject-premise-and-both-map
    (E ,Σ (A ,Σ (B ,Σ (C ,Σ (D ,Σ (proof-eq ,× formula-eq))))))

premiseAndLeftMapDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (e a b c : Code) →
  (E A B C : Formula) →
  proof-code ≡ encodeCode (node 33 (e ∷ a ∷ b ∷ c ∷ [])) →
  formula-code ≡
    canonicalNatFormula
      ((E ⇒ (A ⇒ C)) ⇒ (E ⇒ ((A ∧ B) ⇒ (C ∧ B)))) →
  decodeCanonicalFormula e ≡ just E →
  decodeCanonicalFormula a ≡ just A →
  decodeCanonicalFormula b ≡ just B →
  decodeCanonicalFormula c ≡ just C →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
premiseAndLeftMapDecodedCoverage
  e a b c E A B C proof-eq formula-eq e-eq a-eq b-eq c-eq
  rewrite decodeCanonicalFormula-sound e E e-eq
        | decodeCanonicalFormula-sound a A a-eq
        | decodeCanonicalFormula-sound b B b-eq
        | decodeCanonicalFormula-sound c C c-eq =
  inject-premise-and-left-map
    (E ,Σ (A ,Σ (B ,Σ (C ,Σ (proof-eq ,× formula-eq)))))

bodyUniqueComposeDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (a b c d e f g : Code) →
  (A B C D E F G : Formula) →
  proof-code ≡ encodeCode (node 34 (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ [])) →
  formula-code ≡
    canonicalNatFormula
      ((A ⇒ (C ⇒ E)) ⇒
       ((E ⇒ (B ⇒ F)) ⇒
        ((F ⇒ (D ⇒ G)) ⇒ ((A ∧ B) ⇒ ((C ∧ D) ⇒ G))))) →
  decodeCanonicalFormula a ≡ just A →
  decodeCanonicalFormula b ≡ just B →
  decodeCanonicalFormula c ≡ just C →
  decodeCanonicalFormula d ≡ just D →
  decodeCanonicalFormula e ≡ just E →
  decodeCanonicalFormula f ≡ just F →
  decodeCanonicalFormula g ≡ just G →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
bodyUniqueComposeDecodedCoverage
  a b c d e f g A B C D E F G
  proof-eq formula-eq a-eq b-eq c-eq d-eq e-eq f-eq g-eq
  rewrite decodeCanonicalFormula-sound a A a-eq
        | decodeCanonicalFormula-sound b B b-eq
        | decodeCanonicalFormula-sound c C c-eq
        | decodeCanonicalFormula-sound d D d-eq
        | decodeCanonicalFormula-sound e E e-eq
        | decodeCanonicalFormula-sound f F f-eq
        | decodeCanonicalFormula-sound g G g-eq =
  inject-body-unique-compose
    (A ,Σ
      (B ,Σ
        (C ,Σ
          (D ,Σ
            (E ,Σ
              (F ,Σ
                (G ,Σ (proof-eq ,× formula-eq))))))))

contradictionToNegDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (a b : Code) →
  (A B : Formula) →
  proof-code ≡ encodeCode (node 38 (a ∷ b ∷ [])) →
  formula-code ≡ canonicalNatFormula ((A ⇒ B) ⇒ (¬ᶠ B ⇒ ¬ᶠ A)) →
  decodeCanonicalFormula a ≡ just A →
  decodeCanonicalFormula b ≡ just B →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
contradictionToNegDecodedCoverage a b A B proof-eq formula-eq a-eq b-eq
  rewrite decodeCanonicalFormula-sound a A a-eq
        | decodeCanonicalFormula-sound b B b-eq =
  inject-contradiction-to-neg
    (A ,Σ (B ,Σ (proof-eq ,× formula-eq)))

eqReflDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (t-code : Code) →
  (t : Term) →
  proof-code ≡ encodeCode (node 8 (t-code ∷ [])) →
  formula-code ≡ canonicalNatFormula (t ≈ t) →
  decodeCanonicalTerm t-code ≡ just t →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
eqReflDecodedCoverage t-code t proof-eq formula-eq t-eq
  rewrite decodeCanonicalTerm-sound t-code t t-eq =
  inject-eq-refl
    (t ,Σ (proof-eq ,× formula-eq))

eqSymDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (s-code t-code : Code) →
  (s t : Term) →
  proof-code ≡ encodeCode (node 9 (s-code ∷ t-code ∷ [])) →
  formula-code ≡ canonicalNatFormula (s ≈ t ⇒ t ≈ s) →
  decodeCanonicalTerm s-code ≡ just s →
  decodeCanonicalTerm t-code ≡ just t →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
eqSymDecodedCoverage s-code t-code s t proof-eq formula-eq s-eq t-eq
  rewrite decodeCanonicalTerm-sound s-code s s-eq
        | decodeCanonicalTerm-sound t-code t t-eq =
  inject-eq-sym
    (s ,Σ (t ,Σ (proof-eq ,× formula-eq)))

eqTransDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (r-code s-code t-code : Code) →
  (r s t : Term) →
  proof-code ≡ encodeCode (node 10 (r-code ∷ s-code ∷ t-code ∷ [])) →
  formula-code ≡ canonicalNatFormula (r ≈ s ⇒ (s ≈ t ⇒ r ≈ t)) →
  decodeCanonicalTerm r-code ≡ just r →
  decodeCanonicalTerm s-code ≡ just s →
  decodeCanonicalTerm t-code ≡ just t →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
eqTransDecodedCoverage r-code s-code t-code r s t proof-eq formula-eq r-eq s-eq t-eq
  rewrite decodeCanonicalTerm-sound r-code r r-eq
        | decodeCanonicalTerm-sound s-code s s-eq
        | decodeCanonicalTerm-sound t-code t t-eq =
  inject-eq-trans
    (r ,Σ (s ,Σ (t ,Σ (proof-eq ,× formula-eq))))

sucCongDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (s-code t-code : Code) →
  (s t : Term) →
  proof-code ≡ encodeCode (node 11 (s-code ∷ t-code ∷ [])) →
  formula-code ≡ canonicalNatFormula (s ≈ t ⇒ sucᵗ s ≈ sucᵗ t) →
  decodeCanonicalTerm s-code ≡ just s →
  decodeCanonicalTerm t-code ≡ just t →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
sucCongDecodedCoverage s-code t-code s t proof-eq formula-eq s-eq t-eq
  rewrite decodeCanonicalTerm-sound s-code s s-eq
        | decodeCanonicalTerm-sound t-code t t-eq =
  inject-suc-cong
    (s ,Σ (t ,Σ (proof-eq ,× formula-eq)))

addCongDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (a-code b-code c-code d-code : Code) →
  (a b c d : Term) →
  proof-code ≡ encodeCode (node 12 (a-code ∷ b-code ∷ c-code ∷ d-code ∷ [])) →
  formula-code ≡
    canonicalNatFormula
      (a ≈ b ⇒ (c ≈ d ⇒ (a +ᵗ c) ≈ (b +ᵗ d))) →
  decodeCanonicalTerm a-code ≡ just a →
  decodeCanonicalTerm b-code ≡ just b →
  decodeCanonicalTerm c-code ≡ just c →
  decodeCanonicalTerm d-code ≡ just d →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
addCongDecodedCoverage
  a-code b-code c-code d-code a b c d proof-eq formula-eq a-eq b-eq c-eq d-eq
  rewrite decodeCanonicalTerm-sound a-code a a-eq
        | decodeCanonicalTerm-sound b-code b b-eq
        | decodeCanonicalTerm-sound c-code c c-eq
        | decodeCanonicalTerm-sound d-code d d-eq =
  inject-add-cong
    (a ,Σ (b ,Σ (c ,Σ (d ,Σ (proof-eq ,× formula-eq)))))

mulCongDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (a-code b-code c-code d-code : Code) →
  (a b c d : Term) →
  proof-code ≡ encodeCode (node 13 (a-code ∷ b-code ∷ c-code ∷ d-code ∷ [])) →
  formula-code ≡
    canonicalNatFormula
      (a ≈ b ⇒ (c ≈ d ⇒ (a *ᵗ c) ≈ (b *ᵗ d))) →
  decodeCanonicalTerm a-code ≡ just a →
  decodeCanonicalTerm b-code ≡ just b →
  decodeCanonicalTerm c-code ≡ just c →
  decodeCanonicalTerm d-code ≡ just d →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
mulCongDecodedCoverage
  a-code b-code c-code d-code a b c d proof-eq formula-eq a-eq b-eq c-eq d-eq
  rewrite decodeCanonicalTerm-sound a-code a a-eq
        | decodeCanonicalTerm-sound b-code b b-eq
        | decodeCanonicalTerm-sound c-code c c-eq
        | decodeCanonicalTerm-sound d-code d d-eq =
  inject-mul-cong
    (a ,Σ (b ,Σ (c ,Σ (d ,Σ (proof-eq ,× formula-eq)))))

eqUniqueValueDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (y-code z-code c-code : Code) →
  (y z c : Term) →
  proof-code ≡ encodeCode (node 24 (y-code ∷ z-code ∷ c-code ∷ [])) →
  formula-code ≡ canonicalNatFormula (y ≈ c ⇒ (z ≈ c ⇒ y ≈ z)) →
  decodeCanonicalTerm y-code ≡ just y →
  decodeCanonicalTerm z-code ≡ just z →
  decodeCanonicalTerm c-code ≡ just c →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
eqUniqueValueDecodedCoverage
  y-code z-code c-code y z c proof-eq formula-eq y-eq z-eq c-eq
  rewrite decodeCanonicalTerm-sound y-code y y-eq
        | decodeCanonicalTerm-sound z-code z z-eq
        | decodeCanonicalTerm-sound c-code c c-eq =
  inject-eq-unique-value
    (y ,Σ (z ,Σ (c ,Σ (proof-eq ,× formula-eq))))

eqSubstRightDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (a-code b-code y-code : Code) →
  (a b y : Term) →
  proof-code ≡ encodeCode (node 35 (a-code ∷ b-code ∷ y-code ∷ [])) →
  formula-code ≡ canonicalNatFormula (a ≈ b ⇒ (y ≈ a ⇒ y ≈ b)) →
  decodeCanonicalTerm a-code ≡ just a →
  decodeCanonicalTerm b-code ≡ just b →
  decodeCanonicalTerm y-code ≡ just y →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
eqSubstRightDecodedCoverage
  a-code b-code y-code a b y proof-eq formula-eq a-eq b-eq y-eq
  rewrite decodeCanonicalTerm-sound a-code a a-eq
        | decodeCanonicalTerm-sound b-code b b-eq
        | decodeCanonicalTerm-sound y-code y y-eq =
  inject-eq-subst-right
    (a ,Σ (b ,Σ (y ,Σ (proof-eq ,× formula-eq))))

eqSubstSucRightDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (a-code b-code y-code : Code) →
  (a b y : Term) →
  proof-code ≡ encodeCode (node 36 (a-code ∷ b-code ∷ y-code ∷ [])) →
  formula-code ≡ canonicalNatFormula (a ≈ b ⇒ (y ≈ sucᵗ a ⇒ y ≈ sucᵗ b)) →
  decodeCanonicalTerm a-code ≡ just a →
  decodeCanonicalTerm b-code ≡ just b →
  decodeCanonicalTerm y-code ≡ just y →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
eqSubstSucRightDecodedCoverage
  a-code b-code y-code a b y proof-eq formula-eq a-eq b-eq y-eq
  rewrite decodeCanonicalTerm-sound a-code a a-eq
        | decodeCanonicalTerm-sound b-code b b-eq
        | decodeCanonicalTerm-sound y-code y y-eq =
  inject-eq-subst-suc-right
    (a ,Σ (b ,Σ (y ,Σ (proof-eq ,× formula-eq))))

existsElimDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (a b : Code) →
  (A B : Formula) →
  proof-code ≡ encodeCode (node 14 (a ∷ b ∷ [])) →
  formula-code ≡ canonicalNatFormula ((∀ᶠ (A ⇒ wkFormula B)) ⇒ (∃ᶠ A ⇒ B)) →
  decodeCanonicalFormula a ≡ just A →
  decodeCanonicalFormula b ≡ just B →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
existsElimDecodedCoverage a b A B proof-eq formula-eq a-eq b-eq
  rewrite decodeCanonicalFormula-sound a A a-eq
        | decodeCanonicalFormula-sound b B b-eq =
  inject-exists-elim
    (A ,Σ (B ,Σ (proof-eq ,× formula-eq)))

existsPrefixIntroduceDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (k : ℕ) →
  (i a : Code) →
  (I A : Formula) →
  proof-code ≡ encodeCode (node 15 (atom k ∷ i ∷ a ∷ [])) →
  formula-code ≡ canonicalNatFormula (I ⇒ exists-prefix k A) →
  decodeCanonicalFormula i ≡ just I →
  decodeCanonicalFormula a ≡ just A →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
existsPrefixIntroduceDecodedCoverage k i a I A proof-eq formula-eq i-eq a-eq
  rewrite decodeCanonicalFormula-sound i I i-eq
        | decodeCanonicalFormula-sound a A a-eq =
  inject-exists-prefix-introduce
    (k ,Σ (I ,Σ (A ,Σ (proof-eq ,× formula-eq))))

existsPrefixBinaryLiftDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (k : ℕ) →
  (a b c d : Code) →
  (A B C D : Formula) →
  proof-code ≡ encodeCode (node 16 (atom k ∷ a ∷ b ∷ c ∷ d ∷ [])) →
  formula-code ≡
    canonicalNatFormula
      ((A ⇒ (B ⇒ D)) ⇒ (exists-prefix k A ⇒ (exists-prefix k B ⇒ C))) →
  decodeCanonicalFormula a ≡ just A →
  decodeCanonicalFormula b ≡ just B →
  decodeCanonicalFormula c ≡ just C →
  decodeCanonicalFormula d ≡ just D →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
existsPrefixBinaryLiftDecodedCoverage
  k a b c d A B C D proof-eq formula-eq a-eq b-eq c-eq d-eq
  rewrite decodeCanonicalFormula-sound a A a-eq
        | decodeCanonicalFormula-sound b B b-eq
        | decodeCanonicalFormula-sound c C c-eq
        | decodeCanonicalFormula-sound d D d-eq =
  inject-exists-prefix-binary-lift
    (k ,Σ (A ,Σ (B ,Σ (C ,Σ (D ,Σ (proof-eq ,× formula-eq))))))

existsPrefixPremiseMapDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (k : ℕ) →
  (e a b c d : Code) →
  (E A B C D : Formula) →
  proof-code ≡ encodeCode (node 17 (atom k ∷ e ∷ a ∷ b ∷ c ∷ d ∷ [])) →
  formula-code ≡
    canonicalNatFormula
      ((E ⇒ (A ⇒ B)) ⇒ (E ⇒ (exists-prefix k C ⇒ exists-prefix k D))) →
  decodeCanonicalFormula e ≡ just E →
  decodeCanonicalFormula a ≡ just A →
  decodeCanonicalFormula b ≡ just B →
  decodeCanonicalFormula c ≡ just C →
  decodeCanonicalFormula d ≡ just D →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
existsPrefixPremiseMapDecodedCoverage
  k e a b c d E A B C D proof-eq formula-eq e-eq a-eq b-eq c-eq d-eq
  rewrite decodeCanonicalFormula-sound e E e-eq
        | decodeCanonicalFormula-sound a A a-eq
        | decodeCanonicalFormula-sound b B b-eq
        | decodeCanonicalFormula-sound c C c-eq
        | decodeCanonicalFormula-sound d D d-eq =
  inject-exists-prefix-premise-map
    (k ,Σ (E ,Σ (A ,Σ (B ,Σ (C ,Σ (D ,Σ (proof-eq ,× formula-eq)))))))

premiseChangeDecodedCoverage :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  (e e' a b : Code) →
  (E E' A B : Formula) →
  proof-code ≡ encodeCode (node 18 (e ∷ e' ∷ a ∷ b ∷ [])) →
  formula-code ≡ canonicalNatFormula ((E' ⇒ (A ⇒ B)) ⇒ (E ⇒ (A ⇒ B))) →
  decodeCanonicalFormula e ≡ just E →
  decodeCanonicalFormula e' ≡ just E' →
  decodeCanonicalFormula a ≡ just A →
  decodeCanonicalFormula b ≡ just B →
  CurrentProofCheckingTarget d0 d1 d2 d3 d4 d5 proof-code formula-code
premiseChangeDecodedCoverage e e' a b E E' A B proof-eq formula-eq e-eq e'-eq a-eq b-eq
  rewrite decodeCanonicalFormula-sound e E e-eq
        | decodeCanonicalFormula-sound e' E' e'-eq
        | decodeCanonicalFormula-sound a A a-eq
        | decodeCanonicalFormula-sound b B b-eq =
  inject-premise-change
    (E ,Σ (E' ,Σ (A ,Σ (B ,Σ (proof-eq ,× formula-eq)))))
