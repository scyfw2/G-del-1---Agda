{-# OPTIONS --safe #-}

module Godel.ProofCheckingPRComponents where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.CanonicalCoding
open import Godel.PrimitiveRecursive
open import Godel.PRBooleanHelpers
open import Godel.PRBoundedSearch using (constF)
open import Godel.PRArithmeticSemantics
open import Godel.PRRepresentabilityFinal
  using (PARepresentsRelation; prrel-represented)
open import Godel.ProofCheckingPR
open import Godel.ProofCheckingPRTargets

-- Concrete reusable PR component for proof checking: equality of numeric
-- canonical codes.  This is the first small piece that can be implemented
-- directly from the minimal-basis PR helper layer and reused by the later
-- proof-step checker.

natEqPR : PRRel (suc (suc zero))
natEqPR = rel eqNatF

natEqPR-represented : PARepresentsRelation natEqPR
natEqPR-represented =
  prrel-represented natEqPR

mulNat-one-one : mulNat (suc zero) (suc zero) ≡ suc zero
mulNat-one-one = refl

eqNatNat-refl : (n : ℕ) → eqNatNat n n ≡ suc zero
eqNatNat-refl n
  rewrite lessEqNat-refl n
        | mulNat-one-one = refl

eqNatNat-sound :
  (m n : ℕ) →
  eqNatNat m n ≡ suc zero →
  m ≡ n
eqNatNat-sound zero zero eq = refl
eqNatNat-sound zero (suc n) ()
eqNatNat-sound (suc m) zero ()
eqNatNat-sound (suc m) (suc n) eq =
  cong suc (eqNatNat-sound m n eq)

natEqPR-complete :
  {m n : ℕ} →
  m ≡ n →
  PRRel-holds natEqPR (proofCodeArgs m n)
natEqPR-complete {m} {n} refl
  rewrite eqNatF-correct n n
        | eqNatNat-refl n = refl

natEqPR-sound :
  {m n : ℕ} →
  PRRel-holds natEqPR (proofCodeArgs m n) →
  m ≡ n
natEqPR-sound {m} {n} holds =
  eqNatNat-sound
    m
    n
    (trans (sym (eqNatF-correct m n)) holds)

tagArg : ℕ → Vec ℕ (suc zero)
tagArg tag = tag ∷ []

tagEqF : ℕ → PRF (suc zero)
tagEqF expected =
  compF eqNatF
    (projF fin0 ∷
     constF expected ∷ [])

tagEqPR : ℕ → PRRel (suc zero)
tagEqPR expected = rel (tagEqF expected)

TagEqNat : ℕ → ℕ → Set
TagEqNat input expected = input ≡ expected

tagEqF-correct :
  (expected input : ℕ) →
  evalPRF (tagEqF expected) (tagArg input) ≡
  eqNatNat input expected
tagEqF-correct expected input
  rewrite constF-correct expected (tagArg input)
        | eqNatF-correct input expected = refl

tagEqPR-represented :
  (expected : ℕ) →
  PARepresentsRelation (tagEqPR expected)
tagEqPR-represented expected =
  prrel-represented (tagEqPR expected)

tagEqPR-complete :
  {input expected : ℕ} →
  TagEqNat input expected →
  PRRel-holds (tagEqPR expected) (tagArg input)
tagEqPR-complete {expected = expected} refl
  rewrite tagEqF-correct expected expected
        | eqNatNat-refl expected = refl

tagEqPR-sound :
  {input expected : ℕ} →
  PRRel-holds (tagEqPR expected) (tagArg input) →
  TagEqNat input expected
tagEqPR-sound {input} {expected} holds =
  eqNatNat-sound
    input
    expected
    (trans (sym (tagEqF-correct expected input)) holds)

zeroTestArg : ℕ → Vec ℕ (suc zero)
zeroTestArg input = input ∷ []

zeroTestPR : PRRel (suc zero)
zeroTestPR = rel isZeroF

ZeroNat : ℕ → Set
ZeroNat input = input ≡ zero

zeroTestPR-represented :
  PARepresentsRelation zeroTestPR
zeroTestPR-represented =
  prrel-represented zeroTestPR

zeroTestPR-complete :
  {input : ℕ} →
  ZeroNat input →
  PRRel-holds zeroTestPR (zeroTestArg input)
zeroTestPR-complete refl
  rewrite isZeroF-correct zero = refl

zeroTestPR-sound :
  {input : ℕ} →
  PRRel-holds zeroTestPR (zeroTestArg input) →
  ZeroNat input
zeroTestPR-sound {zero} holds = refl
zeroTestPR-sound {suc input} ()

boolArgs : ℕ → ℕ → Vec ℕ (suc (suc zero))
boolArgs left right = left ∷ right ∷ []

andPR : PRRel (suc (suc zero))
andPR = rel andF

AndTrueNat : ℕ → ℕ → Set
AndTrueNat left right =
  (left ≡ suc zero) × (right ≡ suc zero)

NonzeroNat : ℕ → Set
NonzeroNat n = Σ ℕ (λ k → n ≡ suc k)

OrNonzeroNat : ℕ → ℕ → Set
OrNonzeroNat left right =
  NonzeroNat left ⊎ NonzeroNat right

absurd : {A : Set} → ⊥ → A
absurd ()

suc-injective-code :
  {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-injective-code refl = refl

plus-suc-not-zero :
  (m n : ℕ) → m + suc n ≡ zero → ⊥
plus-suc-not-zero zero n ()
plus-suc-not-zero (suc m) n ()

zero≠suc-code : {n : ℕ} → zero ≡ suc n → ⊥
zero≠suc-code ()

suc-plus-suc-not-one :
  (m n : ℕ) → suc m + suc n ≡ suc zero → ⊥
suc-plus-suc-not-one m n eq =
  plus-suc-not-zero m n (suc-injective-code eq)

mulNat-zeroʳ-code :
  (m : ℕ) → mulNat m zero ≡ zero
mulNat-zeroʳ-code zero = refl
mulNat-zeroʳ-code (suc m)
  rewrite mulNat-zeroʳ-code m = refl

mulNat-suc-suc-positive :
  (m n : ℕ) →
  Σ ℕ (λ k → mulNat (suc m) (suc n) ≡ suc k)
mulNat-suc-suc-positive zero n =
  n ,Σ refl
mulNat-suc-suc-positive (suc m) n
  with mulNat-suc-suc-positive m n
... | k ,Σ eq
  rewrite eq =
  (k + suc n) ,Σ refl

mulNat-one-sound :
  (left right : ℕ) →
  mulNat left right ≡ suc zero →
  AndTrueNat left right
mulNat-one-sound zero right ()
mulNat-one-sound (suc zero) right eq =
  refl ,× eq
mulNat-one-sound (suc (suc left)) zero eq
  rewrite mulNat-zeroʳ-code (suc (suc left)) =
  absurd (zero≠suc-code eq)
mulNat-one-sound (suc (suc left)) (suc right) eq
  with mulNat-suc-suc-positive left right
... | k ,Σ inner-eq
  rewrite inner-eq =
  absurd (suc-plus-suc-not-one k right eq)

andPR-represented :
  PARepresentsRelation andPR
andPR-represented =
  prrel-represented andPR

andPR-complete :
  {left right : ℕ} →
  AndTrueNat left right →
  PRRel-holds andPR (boolArgs left right)
andPR-complete (refl ,× refl)
  rewrite andF-correct (suc zero) (suc zero) = refl

andPR-sound :
  {left right : ℕ} →
  PRRel-holds andPR (boolArgs left right) →
  AndTrueNat left right
andPR-sound {left} {right} holds
  rewrite andF-correct left right =
  mulNat-one-sound left right holds

formulaCodeEqPR : PRRel (suc (suc zero))
formulaCodeEqPR = natEqPR

formulaCodeEqPR-represented : PARepresentsRelation formulaCodeEqPR
formulaCodeEqPR-represented =
  natEqPR-represented

FormulaCodeEqNat : ℕ → Formula → Set
FormulaCodeEqNat formula-code A =
  formula-code ≡ canonicalNatFormula A

formulaCodeEqPR-complete :
  {formula-code : ℕ} → {A : Formula} →
  FormulaCodeEqNat formula-code A →
  PRRel-holds formulaCodeEqPR
    (proofCodeArgs formula-code (canonicalNatFormula A))
formulaCodeEqPR-complete eq =
  natEqPR-complete eq

formulaCodeEqPR-sound :
  {formula-code : ℕ} → {A : Formula} →
  PRRel-holds formulaCodeEqPR
    (proofCodeArgs formula-code (canonicalNatFormula A)) →
  FormulaCodeEqNat formula-code A
formulaCodeEqPR-sound =
  natEqPR-sound

record ProofCheckerFormulaCodeEqPR : Set₁ where
  field
    formula-code-eq-pr : PRRel (suc (suc zero))

    formula-code-eq-represented :
      PARepresentsRelation formula-code-eq-pr

    formula-code-eq-complete :
      {formula-code : ℕ} → {A : Formula} →
      FormulaCodeEqNat formula-code A →
      PRRel-holds formula-code-eq-pr
        (proofCodeArgs formula-code (canonicalNatFormula A))

    formula-code-eq-sound :
      {formula-code : ℕ} → {A : Formula} →
      PRRel-holds formula-code-eq-pr
        (proofCodeArgs formula-code (canonicalNatFormula A)) →
      FormulaCodeEqNat formula-code A

proofCheckerFormulaCodeEqPR : ProofCheckerFormulaCodeEqPR
proofCheckerFormulaCodeEqPR = record
  { formula-code-eq-pr = formulaCodeEqPR
  ; formula-code-eq-represented = formulaCodeEqPR-represented
  ; formula-code-eq-complete = λ {formula-code} {A} eq →
      formulaCodeEqPR-complete {formula-code} {A} eq
  ; formula-code-eq-sound = λ {formula-code} {A} holds →
      formulaCodeEqPR-sound {formula-code} {A} holds
  }

record ProofCheckerTagEqPR : Set₁ where
  field
    tag-eq-pr :
      (expected : ℕ) → PRRel (suc zero)

    tag-eq-represented :
      (expected : ℕ) →
      PARepresentsRelation (tag-eq-pr expected)

    tag-eq-complete :
      {input expected : ℕ} →
      TagEqNat input expected →
      PRRel-holds (tag-eq-pr expected) (tagArg input)

    tag-eq-sound :
      {input expected : ℕ} →
      PRRel-holds (tag-eq-pr expected) (tagArg input) →
      TagEqNat input expected

proofCheckerTagEqPR : ProofCheckerTagEqPR
proofCheckerTagEqPR = record
  { tag-eq-pr = tagEqPR
  ; tag-eq-represented = tagEqPR-represented
  ; tag-eq-complete = λ {input} {expected} eq →
      tagEqPR-complete {input} {expected} eq
  ; tag-eq-sound = λ {input} {expected} holds →
      tagEqPR-sound {input} {expected} holds
  }

record ProofCheckerZeroTestPR : Set₁ where
  field
    zero-test-pr :
      PRRel (suc zero)

    zero-test-represented :
      PARepresentsRelation zero-test-pr

    zero-test-complete :
      {input : ℕ} →
      ZeroNat input →
      PRRel-holds zero-test-pr (zeroTestArg input)

    zero-test-sound :
      {input : ℕ} →
      PRRel-holds zero-test-pr (zeroTestArg input) →
      ZeroNat input

proofCheckerZeroTestPR : ProofCheckerZeroTestPR
proofCheckerZeroTestPR = record
  { zero-test-pr = zeroTestPR
  ; zero-test-represented = zeroTestPR-represented
  ; zero-test-complete = λ {input} eq →
      zeroTestPR-complete {input} eq
  ; zero-test-sound = λ {input} holds →
      zeroTestPR-sound {input} holds
  }

record ProofCheckerAndPR : Set₁ where
  field
    and-pr :
      PRRel (suc (suc zero))

    and-represented :
      PARepresentsRelation and-pr

    and-complete :
      {left right : ℕ} →
      AndTrueNat left right →
      PRRel-holds and-pr (boolArgs left right)

    and-sound :
      {left right : ℕ} →
      PRRel-holds and-pr (boolArgs left right) →
      AndTrueNat left right

proofCheckerAndPR : ProofCheckerAndPR
proofCheckerAndPR = record
  { and-pr = andPR
  ; and-represented = andPR-represented
  ; and-complete = λ {left} {right} proof →
      andPR-complete {left} {right} proof
  ; and-sound = λ {left} {right} holds →
      andPR-sound {left} {right} holds
  }

orPR : PRRel (suc (suc zero))
orPR = rel orF

orPR-represented :
  PARepresentsRelation orPR
orPR-represented =
  prrel-represented orPR

orPR-complete-left :
  {left right : ℕ} →
  NonzeroNat left →
  PRRel-holds orPR (boolArgs left right)
orPR-complete-left {left} {right} (k ,Σ eq)
  rewrite eq
        | orF-correct (suc k) right =
  refl

orPR-complete-right :
  {left right : ℕ} →
  NonzeroNat right →
  PRRel-holds orPR (boolArgs left right)
orPR-complete-right {zero} {right} (k ,Σ eq)
  rewrite eq
        | orF-correct zero (suc k) =
  refl
orPR-complete-right {suc left} {right} nonzero =
  orPR-complete-left {left = suc left} {right = right} (left ,Σ refl)

orPR-complete :
  {left right : ℕ} →
  OrNonzeroNat left right →
  PRRel-holds orPR (boolArgs left right)
orPR-complete {left} {right} (inj₁ left-nonzero) =
  orPR-complete-left {left = left} {right = right} left-nonzero
orPR-complete {left} {right} (inj₂ right-nonzero) =
  orPR-complete-right {left = left} {right = right} right-nonzero

orPR-sound :
  {left right : ℕ} →
  PRRel-holds orPR (boolArgs left right) →
  OrNonzeroNat left right
orPR-sound {zero} {zero} holds
  rewrite orF-correct zero zero =
  absurd (zero≠suc-code holds)
orPR-sound {zero} {suc right} holds =
  inj₂ (right ,Σ refl)
orPR-sound {suc left} {right} holds =
  inj₁ (left ,Σ refl)

record ProofCheckerOrPR : Set₁ where
  field
    or-pr :
      PRRel (suc (suc zero))

    or-represented :
      PARepresentsRelation or-pr

    or-complete :
      {left right : ℕ} →
      OrNonzeroNat left right →
      PRRel-holds or-pr (boolArgs left right)

    or-sound :
      {left right : ℕ} →
      PRRel-holds or-pr (boolArgs left right) →
      OrNonzeroNat left right

proofCheckerOrPR : ProofCheckerOrPR
proofCheckerOrPR = record
  { or-pr = orPR
  ; or-represented = orPR-represented
  ; or-complete = λ {left} {right} proof →
      orPR-complete {left} {right} proof
  ; or-sound = λ {left} {right} holds →
      orPR-sound {left} {right} holds
  }

natNeqF : PRF (suc (suc zero))
natNeqF =
  compF isZeroF (eqNatF ∷ [])

natNeqPR : PRRel (suc (suc zero))
natNeqPR = rel natNeqF

NatNeqNat : ℕ → ℕ → Set
NatNeqNat m n = ¬ (m ≡ n)

natNeqF-correct :
  (m n : ℕ) →
  evalPRF natNeqF (boolArgs m n) ≡ isZeroNat (eqNatNat m n)
natNeqF-correct m n
  rewrite eqNatF-correct m n
        | isZeroF-correct (eqNatNat m n) = refl

natNeqNat-complete :
  (m n : ℕ) →
  NatNeqNat m n →
  isZeroNat (eqNatNat m n) ≡ suc zero
natNeqNat-complete zero zero neq =
  absurd (neq refl)
natNeqNat-complete zero (suc n) neq = refl
natNeqNat-complete (suc m) zero neq = refl
natNeqNat-complete (suc m) (suc n) neq =
  natNeqNat-complete
    m
    n
    (λ eq → neq (cong suc eq))

natNeqPR-represented :
  PARepresentsRelation natNeqPR
natNeqPR-represented =
  prrel-represented natNeqPR

natNeqPR-complete :
  {m n : ℕ} →
  NatNeqNat m n →
  PRRel-holds natNeqPR (boolArgs m n)
natNeqPR-complete {m} {n} neq
  rewrite natNeqF-correct m n
        | natNeqNat-complete m n neq =
  refl

natNeqPR-sound :
  {m n : ℕ} →
  PRRel-holds natNeqPR (boolArgs m n) →
  NatNeqNat m n
natNeqPR-sound {m} {n} holds refl
  rewrite natNeqF-correct n n
        | eqNatNat-refl n =
  zero≠suc-code holds

record ProofCheckerNatNeqPR : Set₁ where
  field
    nat-neq-pr :
      PRRel (suc (suc zero))

    nat-neq-represented :
      PARepresentsRelation nat-neq-pr

    nat-neq-complete :
      {m n : ℕ} →
      NatNeqNat m n →
      PRRel-holds nat-neq-pr (boolArgs m n)

    nat-neq-sound :
      {m n : ℕ} →
      PRRel-holds nat-neq-pr (boolArgs m n) →
      NatNeqNat m n

proofCheckerNatNeqPR : ProofCheckerNatNeqPR
proofCheckerNatNeqPR = record
  { nat-neq-pr = natNeqPR
  ; nat-neq-represented = natNeqPR-represented
  ; nat-neq-complete = λ {m} {n} proof →
      natNeqPR-complete {m} {n} proof
  ; nat-neq-sound = λ {m} {n} holds →
      natNeqPR-sound {m} {n} holds
  }
