{-# OPTIONS --safe #-}

module Godel.ProofRuleTargets where

open import Agda.Builtin.List using (List) renaming ([] to []ˡ; _∷_ to _∷ˡ_)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.CanonicalCoding
  using
    ( atom
    ; node
    ; encodeCode
    ; encodeCodeWithRest
    ; encodeCodeListWithRest
    ; canonicalNatFormula
    ; d1
    )
open import Godel.PrimitiveRecursive
open import Godel.PRBooleanHelpers using (fin0; fin1; fin2; fin3; andF; eqNatF; isZeroF)
open import Godel.PRBoundedSearch using (constF)
open import Godel.PRArithmeticSemantics
  using
    ( constF-correct
    ; andF-correct
    ; eqNatF-correct
    ; isZeroF-correct
    ; eqNatNat
    ; isZeroNat
    ; mulNat
    )
open import Godel.PRBooleanSoundness
  using (and-output-sound; and-output-nonzero-sound; and3-output-sound)
open import Godel.PRDigitCoding using (appendDigitF)
open import Godel.PRDigitSemantics using (appendDigitF-correct)
open import Godel.CanonicalCodePR
  using
    ( atomCodeWithRestF
    ; atomCodeWithRestF-correct
    ; nodeCodeWithRestF
    ; nodeCodeWithRestF-correct
    ; closedNumeralNeqFormulaCodeF
    ; closedNumeralNeqFormulaCodeF-correct
    ; eqNatNat-refl-code
    ; eqNatNat-sound-code
    )
open import Godel.PRRepresentabilityFinal
  using (PARepresentsFunction; PARepresentsRelation; prf-represented; prrel-represented)
open import Godel.ProofSystem
open import Godel.PA
open import Godel.ProofCanonicalCoding
open import Godel.ProofCanonicalChecker
  using
    ( checkPAProofCode
    ; neq→==ℕ-false
    )
open import Godel.ProofCheckingPR
  using (proofCodeArgs)
open import Godel.ProofCheckingPRTargets
  using (DecodedExecutableProofCodeNat)

-- Rule-level numeric targets for the future proof-step checker.
-- This first target isolates rule 37, the closed numeral inequality rule.  It
-- is non-recursive and only needs tag/numeral parsing plus natural-number
-- inequality, so it is the smallest useful proof-rule branch to specify.

closedNumeralNeqCode : ℕ → ℕ → ℕ
closedNumeralNeqCode m n =
  encodeCode (node 37 (atom m ∷ˡ atom n ∷ˡ []ˡ))

singleAtomListCodeF : PRF (suc zero)
singleAtomListCodeF =
  compF (appendDigitF d1)
    (compF atomCodeWithRestF
      (projF fin0 ∷
       zeroF ∷ []) ∷ [])

twoAtomListCodeF : PRF (suc (suc zero))
twoAtomListCodeF =
  compF (appendDigitF d1)
    (compF atomCodeWithRestF
      (projF fin0 ∷
       compF singleAtomListCodeF (projF fin1 ∷ []) ∷ []) ∷ [])

closedNumeralNeqProofCodeF : PRF (suc (suc zero))
closedNumeralNeqProofCodeF =
  compF nodeCodeWithRestF
    (constF 37 ∷
     twoAtomListCodeF ∷ [])

singleAtomListCodeF-correct :
  (n : ℕ) →
  evalPRF singleAtomListCodeF (n ∷ []) ≡
  encodeCodeListWithRest (atom n ∷ˡ []ˡ) zero
singleAtomListCodeF-correct n
  rewrite atomCodeWithRestF-correct n zero
        | appendDigitF-correct d1 (encodeCodeWithRest (atom n) zero) =
  refl

twoAtomListCodeF-correct :
  (m n : ℕ) →
  evalPRF twoAtomListCodeF (m ∷ n ∷ []) ≡
  encodeCodeListWithRest (atom m ∷ˡ atom n ∷ˡ []ˡ) zero
twoAtomListCodeF-correct m n
  rewrite singleAtomListCodeF-correct n
        | atomCodeWithRestF-correct
            m
            (encodeCodeListWithRest (atom n ∷ˡ []ˡ) zero)
        | appendDigitF-correct d1
            (encodeCodeWithRest
              (atom m)
              (encodeCodeListWithRest (atom n ∷ˡ []ˡ) zero)) =
  refl

rule37ChildrenArgs :
  ℕ → ℕ → ℕ → Vec ℕ (suc (suc (suc zero)))
rule37ChildrenArgs children-code m n =
  children-code ∷ m ∷ n ∷ []

rule37ChildrenCodeF : PRF (suc (suc (suc zero)))
rule37ChildrenCodeF =
  compF eqNatF
    (projF fin0 ∷
     compF twoAtomListCodeF
      (projF fin1 ∷
       projF fin2 ∷ []) ∷ [])

rule37ChildrenCodePR : PRRel (suc (suc (suc zero)))
rule37ChildrenCodePR =
  rel rule37ChildrenCodeF

Rule37ChildrenCodeNat : ℕ → ℕ → ℕ → Set
Rule37ChildrenCodeNat children-code m n =
  children-code ≡
  encodeCodeListWithRest (atom m ∷ˡ atom n ∷ˡ []ˡ) zero

rule37ChildrenCodeF-correct :
  (children-code m n : ℕ) →
  evalPRF rule37ChildrenCodeF (rule37ChildrenArgs children-code m n) ≡
  eqNatNat
    children-code
    (encodeCodeListWithRest (atom m ∷ˡ atom n ∷ˡ []ˡ) zero)
rule37ChildrenCodeF-correct children-code m n
  rewrite twoAtomListCodeF-correct m n
        | eqNatF-correct
            children-code
            (encodeCodeListWithRest (atom m ∷ˡ atom n ∷ˡ []ˡ) zero) =
  refl

rule37ChildrenCode-complete :
  {children-code m n : ℕ} →
  Rule37ChildrenCodeNat children-code m n →
  PRRel-holds
    rule37ChildrenCodePR
    (rule37ChildrenArgs children-code m n)
rule37ChildrenCode-complete {children-code} {m} {n} eq
  rewrite rule37ChildrenCodeF-correct children-code m n
        | eq
        | eqNatNat-refl-code
            (encodeCodeListWithRest (atom m ∷ˡ atom n ∷ˡ []ˡ) zero) =
  refl

rule37ChildrenCode-sound :
  {children-code m n : ℕ} →
  PRRel-holds
    rule37ChildrenCodePR
    (rule37ChildrenArgs children-code m n) →
  Rule37ChildrenCodeNat children-code m n
rule37ChildrenCode-sound {children-code} {m} {n} holds
  rewrite rule37ChildrenCodeF-correct children-code m n =
  eqNatNat-sound-code
    children-code
    (encodeCodeListWithRest (atom m ∷ˡ atom n ∷ˡ []ˡ) zero)
    holds

rule37ChildrenCodePR-represented :
  PARepresentsRelation rule37ChildrenCodePR
rule37ChildrenCodePR-represented =
  prrel-represented rule37ChildrenCodePR

closedNumeralNeqProofCodeF-correct :
  (m n : ℕ) →
  evalPRF closedNumeralNeqProofCodeF (m ∷ n ∷ []) ≡
  closedNumeralNeqCode m n
closedNumeralNeqProofCodeF-correct m n
  rewrite constF-correct 37 (m ∷ n ∷ [])
        | twoAtomListCodeF-correct m n
        | nodeCodeWithRestF-correct
            37
            (encodeCodeListWithRest (atom m ∷ˡ atom n ∷ˡ []ˡ) zero) =
  refl

closedNumeralNeqProofCodeF-represented :
  PARepresentsFunction closedNumeralNeqProofCodeF
closedNumeralNeqProofCodeF-represented =
  prf-represented closedNumeralNeqProofCodeF

closedNumeralNeqFormula : ℕ → ℕ → Formula
closedNumeralNeqFormula m n =
  ¬ᶠ (numeral m ≈ numeral n)

closedNumeralNeqFormulaCodeF-represented :
  PARepresentsFunction closedNumeralNeqFormulaCodeF
closedNumeralNeqFormulaCodeF-represented =
  prf-represented closedNumeralNeqFormulaCodeF

closedNumeralNeqFormulaCodeF-canonical-correct :
  (m n : ℕ) →
  evalPRF closedNumeralNeqFormulaCodeF (m ∷ n ∷ []) ≡
  canonicalNatFormula (closedNumeralNeqFormula m n)
closedNumeralNeqFormulaCodeF-canonical-correct =
  closedNumeralNeqFormulaCodeF-correct

NatNeqNat : ℕ → ℕ → Set
NatNeqNat m n = ¬ (m ≡ n)

natNeqF : PRF (suc (suc zero))
natNeqF =
  compF isZeroF (eqNatF ∷ [])

natNeqF-correct :
  (m n : ℕ) →
  evalPRF natNeqF (m ∷ n ∷ []) ≡ isZeroNat (eqNatNat m n)
natNeqF-correct m n
  rewrite eqNatF-correct m n
        | isZeroF-correct (eqNatNat m n) =
  refl

rule37-absurd : {A : Set} → ⊥ → A
rule37-absurd ()

rule37-suc-injective :
  {m n : ℕ} → suc m ≡ suc n → m ≡ n
rule37-suc-injective refl = refl

rule37-plus-suc-not-zero :
  (m n : ℕ) → m + suc n ≡ zero → ⊥
rule37-plus-suc-not-zero zero n ()
rule37-plus-suc-not-zero (suc m) n ()

rule37-zero≠suc : {n : ℕ} → zero ≡ suc n → ⊥
rule37-zero≠suc ()

rule37-suc-plus-suc-not-one :
  (m n : ℕ) → suc m + suc n ≡ suc zero → ⊥
rule37-suc-plus-suc-not-one m n eq =
  rule37-plus-suc-not-zero m n (rule37-suc-injective eq)

rule37-mulNat-zeroʳ :
  (m : ℕ) → mulNat m zero ≡ zero
rule37-mulNat-zeroʳ zero = refl
rule37-mulNat-zeroʳ (suc m)
  rewrite rule37-mulNat-zeroʳ m = refl

rule37-mulNat-suc-suc-positive :
  (m n : ℕ) →
  Σ ℕ (λ k → mulNat (suc m) (suc n) ≡ suc k)
rule37-mulNat-suc-suc-positive zero n =
  n ,Σ refl
rule37-mulNat-suc-suc-positive (suc m) n
  with rule37-mulNat-suc-suc-positive m n
... | k ,Σ eq
  rewrite eq =
  (k + suc n) ,Σ refl

rule37-mulNat-one-sound :
  (left right : ℕ) →
  mulNat left right ≡ suc zero →
  (left ≡ suc zero) × (right ≡ suc zero)
rule37-mulNat-one-sound zero right ()
rule37-mulNat-one-sound (suc zero) right eq =
  refl ,× eq
rule37-mulNat-one-sound (suc (suc left)) zero eq
  rewrite rule37-mulNat-zeroʳ (suc (suc left)) =
  rule37-absurd (rule37-zero≠suc eq)
rule37-mulNat-one-sound (suc (suc left)) (suc right) eq
  with rule37-mulNat-suc-suc-positive left right
... | k ,Σ inner-eq
  rewrite inner-eq =
  rule37-absurd (rule37-suc-plus-suc-not-one k right eq)

natNeqNat-complete :
  (m n : ℕ) →
  NatNeqNat m n →
  isZeroNat (eqNatNat m n) ≡ suc zero
natNeqNat-complete zero zero neq =
  rule37-absurd (neq refl)
natNeqNat-complete zero (suc n) neq = refl
natNeqNat-complete (suc m) zero neq = refl
natNeqNat-complete (suc m) (suc n) neq =
  natNeqNat-complete
    m
    n
    (λ eq → neq (cong suc eq))

natNeqNat-sound :
  {m n : ℕ} →
  isZeroNat (eqNatNat m n) ≡ suc zero →
  NatNeqNat m n
natNeqNat-sound {m} {n} holds refl
  rewrite eqNatNat-refl-code n =
  rule37-zero≠suc holds

eqNatNat-nonzero-sound-code :
  (m n : ℕ) →
  Σ ℕ (λ k → eqNatNat m n ≡ suc k) →
  m ≡ n
eqNatNat-nonzero-sound-code zero zero nonzero = refl
eqNatNat-nonzero-sound-code zero (suc n) (k ,Σ ())
eqNatNat-nonzero-sound-code (suc m) zero (k ,Σ ())
eqNatNat-nonzero-sound-code (suc m) (suc n) nonzero =
  cong suc (eqNatNat-nonzero-sound-code m n nonzero)

natNeqNat-nonzero-sound :
  {m n : ℕ} →
  Σ ℕ (λ k → isZeroNat (eqNatNat m n) ≡ suc k) →
  NatNeqNat m n
natNeqNat-nonzero-sound {m} {n} (k ,Σ nonzero) refl
  rewrite eqNatNat-refl-code n =
  rule37-zero≠suc nonzero

rule37WitnessArgs :
  ℕ → ℕ → ℕ → ℕ →
  Vec ℕ (suc (suc (suc (suc zero))))
rule37WitnessArgs m n proof-code formula-code =
  m ∷ n ∷ proof-code ∷ formula-code ∷ []

rule37ProofCodeEqF : PRF (suc (suc (suc (suc zero))))
rule37ProofCodeEqF =
  compF eqNatF
    (projF fin2 ∷
     compF closedNumeralNeqProofCodeF
      (projF fin0 ∷
       projF fin1 ∷ []) ∷ [])

rule37FormulaCodeEqF : PRF (suc (suc (suc (suc zero))))
rule37FormulaCodeEqF =
  compF eqNatF
    (projF fin3 ∷
     compF closedNumeralNeqFormulaCodeF
      (projF fin0 ∷
       projF fin1 ∷ []) ∷ [])

rule37NeqBranchF : PRF (suc (suc (suc (suc zero))))
rule37NeqBranchF =
  compF natNeqF
    (projF fin0 ∷
     projF fin1 ∷ [])

rule37InnerWitnessF : PRF (suc (suc (suc (suc zero))))
rule37InnerWitnessF =
  compF andF
    (rule37FormulaCodeEqF ∷
     rule37NeqBranchF ∷ [])

rule37WitnessF : PRF (suc (suc (suc (suc zero))))
rule37WitnessF =
  compF andF
    (rule37ProofCodeEqF ∷
     rule37InnerWitnessF ∷ [])

rule37WitnessPR : PRRel (suc (suc (suc (suc zero))))
rule37WitnessPR = rel rule37WitnessF

rule37WitnessPR-represented :
  PARepresentsRelation rule37WitnessPR
rule37WitnessPR-represented =
  prrel-represented rule37WitnessPR

Rule37WitnessNat : ℕ → ℕ → ℕ → ℕ → Set
Rule37WitnessNat m n proof-code formula-code =
  NatNeqNat m n ×
  ((proof-code ≡ closedNumeralNeqCode m n) ×
   (formula-code ≡ canonicalNatFormula (closedNumeralNeqFormula m n)))

abstract
  rule37ProofCodeEqF-correct :
    (m n proof-code formula-code : ℕ) →
    evalPRF
      rule37ProofCodeEqF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ eqNatNat proof-code (closedNumeralNeqCode m n)
  rule37ProofCodeEqF-correct m n proof-code formula-code
    rewrite closedNumeralNeqProofCodeF-correct m n
          | eqNatF-correct proof-code (closedNumeralNeqCode m n) =
    refl

  rule37FormulaCodeEqF-correct :
    (m n proof-code formula-code : ℕ) →
    evalPRF
      rule37FormulaCodeEqF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡
    eqNatNat
      formula-code
      (canonicalNatFormula (closedNumeralNeqFormula m n))
  rule37FormulaCodeEqF-correct m n proof-code formula-code
    rewrite closedNumeralNeqFormulaCodeF-canonical-correct m n
          | eqNatF-correct
              formula-code
              (canonicalNatFormula (closedNumeralNeqFormula m n)) =
    refl

  rule37NeqBranchF-correct :
    (m n proof-code formula-code : ℕ) →
    evalPRF
      rule37NeqBranchF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ isZeroNat (eqNatNat m n)
  rule37NeqBranchF-correct m n proof-code formula-code =
    natNeqF-correct m n

abstract
  rule37ProofCodeEqF-complete :
    {m n proof-code formula-code : ℕ} →
    proof-code ≡ closedNumeralNeqCode m n →
    evalPRF
      rule37ProofCodeEqF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ suc zero
  rule37ProofCodeEqF-complete {m} {n} {proof-code} {formula-code}
    proof-eq
    rewrite rule37ProofCodeEqF-correct m n proof-code formula-code
          | proof-eq
          | eqNatNat-refl-code (closedNumeralNeqCode m n) =
    refl

  rule37ProofCodeEqF-sound :
    {m n proof-code formula-code : ℕ} →
    evalPRF
      rule37ProofCodeEqF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ suc zero →
    proof-code ≡ closedNumeralNeqCode m n
  rule37ProofCodeEqF-sound {m} {n} {proof-code} {formula-code}
    holds
    rewrite rule37ProofCodeEqF-correct m n proof-code formula-code =
    eqNatNat-sound-code
      proof-code
      (closedNumeralNeqCode m n)
      holds

  rule37ProofCodeEqF-nonzero-sound :
    {m n proof-code formula-code : ℕ} →
    Σ ℕ
      (λ k →
        evalPRF
          rule37ProofCodeEqF
          (rule37WitnessArgs m n proof-code formula-code)
        ≡ suc k) →
    proof-code ≡ closedNumeralNeqCode m n
  rule37ProofCodeEqF-nonzero-sound {m} {n} {proof-code} {formula-code}
    nonzero
    rewrite rule37ProofCodeEqF-correct m n proof-code formula-code =
    eqNatNat-nonzero-sound-code
      proof-code
      (closedNumeralNeqCode m n)
      nonzero

  rule37FormulaCodeEqF-complete :
    {m n proof-code formula-code : ℕ} →
    formula-code ≡ canonicalNatFormula (closedNumeralNeqFormula m n) →
    evalPRF
      rule37FormulaCodeEqF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ suc zero
  rule37FormulaCodeEqF-complete {m} {n} {proof-code} {formula-code}
    formula-eq
    rewrite rule37FormulaCodeEqF-correct m n proof-code formula-code
          | formula-eq
          | eqNatNat-refl-code
              (canonicalNatFormula (closedNumeralNeqFormula m n)) =
    refl

  rule37FormulaCodeEqF-sound :
    {m n proof-code formula-code : ℕ} →
    evalPRF
      rule37FormulaCodeEqF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ suc zero →
    formula-code ≡ canonicalNatFormula (closedNumeralNeqFormula m n)
  rule37FormulaCodeEqF-sound {m} {n} {proof-code} {formula-code}
    holds
    rewrite rule37FormulaCodeEqF-correct m n proof-code formula-code =
    eqNatNat-sound-code
      formula-code
      (canonicalNatFormula (closedNumeralNeqFormula m n))
      holds

  rule37FormulaCodeEqF-nonzero-sound :
    {m n proof-code formula-code : ℕ} →
    Σ ℕ
      (λ k →
        evalPRF
          rule37FormulaCodeEqF
          (rule37WitnessArgs m n proof-code formula-code)
        ≡ suc k) →
    formula-code ≡ canonicalNatFormula (closedNumeralNeqFormula m n)
  rule37FormulaCodeEqF-nonzero-sound {m} {n} {proof-code} {formula-code}
    nonzero
    rewrite rule37FormulaCodeEqF-correct m n proof-code formula-code =
    eqNatNat-nonzero-sound-code
      formula-code
      (canonicalNatFormula (closedNumeralNeqFormula m n))
      nonzero

  rule37NeqBranchF-complete :
    {m n proof-code formula-code : ℕ} →
    NatNeqNat m n →
    evalPRF
      rule37NeqBranchF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ suc zero
  rule37NeqBranchF-complete {m} {n} {proof-code} {formula-code}
    neq
    rewrite rule37NeqBranchF-correct m n proof-code formula-code
          | natNeqNat-complete m n neq =
    refl

  rule37NeqBranchF-sound :
    {m n proof-code formula-code : ℕ} →
    evalPRF
      rule37NeqBranchF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ suc zero →
    NatNeqNat m n
  rule37NeqBranchF-sound {m} {n} {proof-code} {formula-code}
    holds
    rewrite rule37NeqBranchF-correct m n proof-code formula-code =
    natNeqNat-sound {m} {n} holds

  rule37NeqBranchF-nonzero-sound :
    {m n proof-code formula-code : ℕ} →
    Σ ℕ
      (λ k →
        evalPRF
          rule37NeqBranchF
          (rule37WitnessArgs m n proof-code formula-code)
        ≡ suc k) →
    NatNeqNat m n
  rule37NeqBranchF-nonzero-sound {m} {n} {proof-code} {formula-code}
    nonzero
    rewrite rule37NeqBranchF-correct m n proof-code formula-code =
    natNeqNat-nonzero-sound {m} {n} nonzero

  rule37InnerWitnessF-complete-raw :
    {m n proof-code formula-code : ℕ} →
    evalPRF
      rule37FormulaCodeEqF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ suc zero →
    evalPRF
      rule37NeqBranchF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ suc zero →
    evalPRF
      rule37InnerWitnessF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ suc zero
  rule37InnerWitnessF-complete-raw
    {m} {n} {proof-code} {formula-code}
    formula-one
    neq-one
    rewrite formula-one
          | neq-one
          | andF-correct (suc zero) (suc zero) =
    refl

  rule37InnerWitnessF-correct-raw :
    (m n proof-code formula-code : ℕ) →
    evalPRF
      rule37InnerWitnessF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡
    mulNat
      (evalPRF
        rule37FormulaCodeEqF
        (rule37WitnessArgs m n proof-code formula-code))
      (evalPRF
        rule37NeqBranchF
        (rule37WitnessArgs m n proof-code formula-code))
  rule37InnerWitnessF-correct-raw m n proof-code formula-code
    rewrite andF-correct
              (evalPRF
                rule37FormulaCodeEqF
                (rule37WitnessArgs m n proof-code formula-code))
              (evalPRF
                rule37NeqBranchF
                (rule37WitnessArgs m n proof-code formula-code)) =
    refl

abstract
  rule37InnerWitnessF-sound-raw :
    {m n proof-code formula-code : ℕ} →
    evalPRF
      rule37InnerWitnessF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ suc zero →
    (evalPRF
      rule37FormulaCodeEqF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ suc zero)
    ×
    (evalPRF
      rule37NeqBranchF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ suc zero)
  rule37InnerWitnessF-sound-raw
    {m} {n} {proof-code} {formula-code}
    holds =
    and-output-sound
      (evalPRF
        rule37FormulaCodeEqF
        (rule37WitnessArgs m n proof-code formula-code))
      (evalPRF
        rule37NeqBranchF
        (rule37WitnessArgs m n proof-code formula-code))
      (evalPRF
        rule37InnerWitnessF
        (rule37WitnessArgs m n proof-code formula-code))
      (rule37InnerWitnessF-correct-raw
        m n proof-code formula-code)
      holds

  rule37InnerWitnessF-nonzero-sound :
    {m n proof-code formula-code : ℕ} →
    Σ ℕ
      (λ k →
        evalPRF
          rule37InnerWitnessF
          (rule37WitnessArgs m n proof-code formula-code)
        ≡ suc k) →
    (formula-code ≡ canonicalNatFormula (closedNumeralNeqFormula m n)) ×
    NatNeqNat m n
  rule37InnerWitnessF-nonzero-sound
      {m} {n} {proof-code} {formula-code} nonzero
    with and-output-nonzero-sound
          (evalPRF
            rule37FormulaCodeEqF
            (rule37WitnessArgs m n proof-code formula-code))
          (evalPRF
            rule37NeqBranchF
            (rule37WitnessArgs m n proof-code formula-code))
          (evalPRF
            rule37InnerWitnessF
            (rule37WitnessArgs m n proof-code formula-code))
          (rule37InnerWitnessF-correct-raw
            m n proof-code formula-code)
          nonzero
  ... | formula-nonzero ,× neq-nonzero =
    rule37FormulaCodeEqF-nonzero-sound
      {m} {n} {proof-code} {formula-code}
      formula-nonzero
    ,×
    rule37NeqBranchF-nonzero-sound
      {m} {n} {proof-code} {formula-code}
      neq-nonzero

  rule37WitnessF-complete-raw :
    {m n proof-code formula-code : ℕ} →
    evalPRF
      rule37ProofCodeEqF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ suc zero →
    evalPRF
      rule37InnerWitnessF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ suc zero →
    evalPRF
      rule37WitnessF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ suc zero
  rule37WitnessF-complete-raw
    {m} {n} {proof-code} {formula-code}
    proof-one
    inner-one
    rewrite proof-one
          | inner-one
          | andF-correct (suc zero) (suc zero) =
    refl

  rule37WitnessF-correct-raw :
    (m n proof-code formula-code : ℕ) →
    evalPRF
      rule37WitnessF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡
    mulNat
      (evalPRF
        rule37ProofCodeEqF
        (rule37WitnessArgs m n proof-code formula-code))
      (evalPRF
        rule37InnerWitnessF
        (rule37WitnessArgs m n proof-code formula-code))
  rule37WitnessF-correct-raw m n proof-code formula-code
    rewrite andF-correct
              (evalPRF
                rule37ProofCodeEqF
                (rule37WitnessArgs m n proof-code formula-code))
              (evalPRF
                rule37InnerWitnessF
                (rule37WitnessArgs m n proof-code formula-code)) =
    refl

  rule37WitnessF-correct-flat :
    (m n proof-code formula-code : ℕ) →
    evalPRF
      rule37WitnessF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡
    mulNat
      (evalPRF
        rule37ProofCodeEqF
        (rule37WitnessArgs m n proof-code formula-code))
      (mulNat
        (evalPRF
          rule37FormulaCodeEqF
          (rule37WitnessArgs m n proof-code formula-code))
        (evalPRF
          rule37NeqBranchF
          (rule37WitnessArgs m n proof-code formula-code)))
  rule37WitnessF-correct-flat m n proof-code formula-code
    rewrite rule37WitnessF-correct-raw m n proof-code formula-code
          | rule37InnerWitnessF-correct-raw
              m n proof-code formula-code =
    refl

  rule37WitnessF-sound-ones :
    {m n proof-code formula-code : ℕ} →
    evalPRF
      rule37WitnessF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ suc zero →
    (evalPRF
      rule37ProofCodeEqF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ suc zero)
    ×
    ((evalPRF
      rule37FormulaCodeEqF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ suc zero)
    ×
    (evalPRF
      rule37NeqBranchF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ suc zero))
  rule37WitnessF-sound-ones {m} {n} {proof-code} {formula-code} holds =
    and3-output-sound
      (evalPRF
        rule37ProofCodeEqF
        (rule37WitnessArgs m n proof-code formula-code))
      (evalPRF
        rule37FormulaCodeEqF
        (rule37WitnessArgs m n proof-code formula-code))
      (evalPRF
        rule37NeqBranchF
        (rule37WitnessArgs m n proof-code formula-code))
      (evalPRF
        rule37WitnessF
        (rule37WitnessArgs m n proof-code formula-code))
      (rule37WitnessF-correct-flat
        m n proof-code formula-code)
      holds

  rule37WitnessF-sound-proof :
    {m n proof-code formula-code : ℕ} →
    evalPRF
      rule37WitnessF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ suc zero →
    proof-code ≡ closedNumeralNeqCode m n
  rule37WitnessF-sound-proof {m} {n} {proof-code} {formula-code} holds =
    rule37ProofCodeEqF-sound
      {m} {n} {proof-code} {formula-code}
      (fst
        (rule37WitnessF-sound-ones
          {m} {n} {proof-code} {formula-code}
          holds))

  rule37WitnessF-sound-formula :
    {m n proof-code formula-code : ℕ} →
    evalPRF
      rule37WitnessF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ suc zero →
    formula-code ≡ canonicalNatFormula (closedNumeralNeqFormula m n)
  rule37WitnessF-sound-formula {m} {n} {proof-code} {formula-code} holds =
    rule37FormulaCodeEqF-sound
      {m} {n} {proof-code} {formula-code}
      (fst
        (snd
          (rule37WitnessF-sound-ones
            {m} {n} {proof-code} {formula-code}
            holds)))

  rule37WitnessF-sound-neq :
    {m n proof-code formula-code : ℕ} →
    evalPRF
      rule37WitnessF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ suc zero →
    NatNeqNat m n
  rule37WitnessF-sound-neq {m} {n} {proof-code} {formula-code} holds =
    rule37NeqBranchF-sound
      {m} {n} {proof-code} {formula-code}
      (snd
        (snd
          (rule37WitnessF-sound-ones
            {m} {n} {proof-code} {formula-code}
            holds)))

  rule37WitnessF-sound :
    {m n proof-code formula-code : ℕ} →
    evalPRF
      rule37WitnessF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ suc zero →
    Rule37WitnessNat m n proof-code formula-code
  rule37WitnessF-sound {m} {n} {proof-code} {formula-code} holds =
    rule37WitnessF-sound-neq
      {m} {n} {proof-code} {formula-code}
      holds
    ,×
    ( rule37WitnessF-sound-proof
        {m} {n} {proof-code} {formula-code}
        holds
    ,×
      rule37WitnessF-sound-formula
        {m} {n} {proof-code} {formula-code}
        holds
    )

  rule37WitnessF-nonzero-sound :
    {m n proof-code formula-code : ℕ} →
    Σ ℕ
      (λ k →
        evalPRF
          rule37WitnessF
          (rule37WitnessArgs m n proof-code formula-code)
        ≡ suc k) →
    Rule37WitnessNat m n proof-code formula-code
  rule37WitnessF-nonzero-sound
      {m} {n} {proof-code} {formula-code} nonzero
    with and-output-nonzero-sound
          (evalPRF
            rule37ProofCodeEqF
            (rule37WitnessArgs m n proof-code formula-code))
          (evalPRF
            rule37InnerWitnessF
            (rule37WitnessArgs m n proof-code formula-code))
          (evalPRF
            rule37WitnessF
            (rule37WitnessArgs m n proof-code formula-code))
          (rule37WitnessF-correct-raw
            m n proof-code formula-code)
          nonzero
  ... | proof-nonzero ,× inner-nonzero
    with rule37InnerWitnessF-nonzero-sound
          {m} {n} {proof-code} {formula-code}
          inner-nonzero
  ... | formula-eq ,× neq =
    neq
    ,×
    ( rule37ProofCodeEqF-nonzero-sound
        {m} {n} {proof-code} {formula-code}
        proof-nonzero
    ,×
      formula-eq)

  rule37WitnessF-sound-raw :
    {m n proof-code formula-code : ℕ} →
    evalPRF
      rule37WitnessF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ suc zero →
    (evalPRF
      rule37ProofCodeEqF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ suc zero)
    ×
    (evalPRF
      rule37InnerWitnessF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ suc zero)
  rule37WitnessF-sound-raw
    {m} {n} {proof-code} {formula-code}
    holds =
    and-output-sound
      (evalPRF
        rule37ProofCodeEqF
        (rule37WitnessArgs m n proof-code formula-code))
      (evalPRF
        rule37InnerWitnessF
        (rule37WitnessArgs m n proof-code formula-code))
      (evalPRF
        rule37WitnessF
        (rule37WitnessArgs m n proof-code formula-code))
      (rule37WitnessF-correct-raw
        m n proof-code formula-code)
      holds

abstract
  rule37WitnessF-complete :
    {m n proof-code formula-code : ℕ} →
    Rule37WitnessNat m n proof-code formula-code →
    evalPRF
      rule37WitnessF
      (rule37WitnessArgs m n proof-code formula-code)
    ≡ suc zero
  rule37WitnessF-complete {m} {n} {proof-code} {formula-code}
    (neq ,× (proof-eq ,× formula-eq)) =
    rule37WitnessF-complete-raw
      {m} {n} {proof-code} {formula-code}
      (rule37ProofCodeEqF-complete
        {m} {n} {proof-code} {formula-code}
        proof-eq)
      (rule37InnerWitnessF-complete-raw
        {m} {n} {proof-code} {formula-code}
        (rule37FormulaCodeEqF-complete
          {m} {n} {proof-code} {formula-code}
          formula-eq)
        (rule37NeqBranchF-complete
          {m} {n} {proof-code} {formula-code}
          neq))

ClosedNumeralNeqRuleNat : ℕ → ℕ → Set
ClosedNumeralNeqRuleNat proof-code formula-code =
  Σ ℕ
    (λ m →
      Σ ℕ
        (λ n →
          (¬ (m ≡ n)) ×
          ((proof-code ≡ closedNumeralNeqCode m n) ×
           (formula-code ≡
            canonicalNatFormula (closedNumeralNeqFormula m n)))))

closedNumeralNeqRuleNat-complete :
  (m n : ℕ) →
  (neq : ¬ (m ≡ n)) →
  ClosedNumeralNeqRuleNat
    (canonicalCodePAProof (closed-numeral-neq m n neq))
    (canonicalNatFormula (closedNumeralNeqFormula m n))
closedNumeralNeqRuleNat-complete m n neq =
  m ,Σ (n ,Σ (neq ,× (refl ,× refl)))

closedNumeralNeqRuleNat-to-decoded :
  (proof-code formula-code : ℕ) →
  ClosedNumeralNeqRuleNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
closedNumeralNeqRuleNat-to-decoded
  proof-code
  formula-code
  (m ,Σ (n ,Σ (neq ,× (proof-eq ,× formula-eq)))) =
  node 37 (atom m ∷ˡ atom n ∷ˡ []ˡ) ,Σ
    (closedNumeralNeqFormula m n ,Σ
      (proof-eq ,×
       (formula-eq ,× check-eq)))
  where
    check-eq :
      checkPAProofCode (node 37 (atom m ∷ˡ atom n ∷ˡ []ˡ)) ≡
      just (closedNumeralNeqFormula m n)
    check-eq
      rewrite neq→==ℕ-false m n neq = refl

record ProofRule37PR : Set₁ where
  field
    rule37-pr :
      PRRel (suc (suc zero))

    rule37-complete :
      {proof-code formula-code : ℕ} →
      ClosedNumeralNeqRuleNat proof-code formula-code →
      PRRel-holds rule37-pr (proofCodeArgs proof-code formula-code)

    rule37-sound :
      {proof-code formula-code : ℕ} →
      PRRel-holds rule37-pr (proofCodeArgs proof-code formula-code) →
      ClosedNumeralNeqRuleNat proof-code formula-code

record ProofRule37PARepresentability (D : ProofRule37PR) : Set₁ where
  field
    rule37-represented :
      PARepresentsRelation (ProofRule37PR.rule37-pr D)

proofRule37PR-represented :
  (D : ProofRule37PR) →
  ProofRule37PARepresentability D
proofRule37PR-represented D = record
  { rule37-represented =
      prrel-represented (ProofRule37PR.rule37-pr D)
  }

proofRule37PR-to-decoded :
  (D : ProofRule37PR) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (ProofRule37PR.rule37-pr D)
    (proofCodeArgs proof-code formula-code) →
  DecodedExecutableProofCodeNat proof-code formula-code
proofRule37PR-to-decoded D {proof-code} {formula-code} holds =
  closedNumeralNeqRuleNat-to-decoded
    proof-code
    formula-code
    (ProofRule37PR.rule37-sound D holds)
