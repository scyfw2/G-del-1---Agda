{-# OPTIONS --safe #-}

module Godel.ProofRuleFixedProofOr where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.CanonicalCoding using (canonicalNatFormula)
open import Godel.PrimitiveRecursive
open import Godel.PRBooleanHelpers using (orF)
open import Godel.PRArithmeticSemantics using (eqNatNat; isZeroNat; mulNat; orF-correct)
open import Godel.PRBooleanSoundness using (mulNat-zeroʳ)
open import Godel.PRRepresentabilityFinal
  using (PARepresentsRelation; prrel-represented)
open import Godel.PA
open import Godel.ProofCheckingPR using (proofCodeArgs)
open import Godel.ProofCheckingPRTargets
  using
    ( DecodedExecutableProofCodeNat
    ; ExecutableProofCodeNat
    ; decoded-to-executableProofCodeNat
    )
open import Godel.ProofCanonicalCoding using (canonicalCodePAProof)
open import Godel.ProofRuleFixedPair
open import Godel.ProofRuleFixedProof

-- Binary disjunction for fixed PA-proof leaves.  This is the reusable
-- combinator needed before assembling finite families of fixed proof-checker
-- branches, such as the non-parameterized PA axioms.

NonzeroNat : ℕ → Set
NonzeroNat n = Σ ℕ (λ k → n ≡ suc k)

eqNatNat-nonzero-sound :
  (m n : ℕ) →
  NonzeroNat (eqNatNat m n) →
  m ≡ n
eqNatNat-nonzero-sound zero zero nonzero = refl
eqNatNat-nonzero-sound zero (suc n) (k ,Σ ())
eqNatNat-nonzero-sound (suc m) zero (k ,Σ ())
eqNatNat-nonzero-sound (suc m) (suc n) nonzero =
  cong suc (eqNatNat-nonzero-sound m n nonzero)

mulNat-nonzero-sound :
  (m n : ℕ) →
  NonzeroNat (mulNat m n) →
  NonzeroNat m × NonzeroNat n
mulNat-nonzero-sound zero n (k ,Σ ())
mulNat-nonzero-sound (suc m) zero nonzero
  rewrite mulNat-zeroʳ (suc m) with nonzero
... | k ,Σ ()
mulNat-nonzero-sound (suc m) (suc n) nonzero =
  (m ,Σ refl) ,× (n ,Σ refl)

fixedPairF-nonzero-sound :
  {expected-proof-code expected-formula-code proof-code formula-code : ℕ} →
  NonzeroNat
    (evalPRF
      (fixedPairF expected-proof-code expected-formula-code)
      (proofCodeArgs proof-code formula-code)) →
  FixedPairNat
    expected-proof-code
    expected-formula-code
    proof-code
    formula-code
fixedPairF-nonzero-sound
  {expected-proof-code}
  {expected-formula-code}
  {proof-code}
  {formula-code}
  nonzero
  rewrite fixedPairF-correct
            expected-proof-code
            expected-formula-code
            proof-code
            formula-code
  with mulNat-nonzero-sound
        (eqNatNat proof-code expected-proof-code)
        (eqNatNat formula-code expected-formula-code)
        nonzero
... | proof-nonzero ,× formula-nonzero =
  eqNatNat-nonzero-sound
    proof-code
    expected-proof-code
    proof-nonzero
  ,×
  eqNatNat-nonzero-sound
    formula-code
    expected-formula-code
    formula-nonzero

fixedPAProofF :
  {A : Formula} →
  PA-provable A →
  PRF (suc (suc zero))
fixedPAProofF {A} p =
  fixedPairF
    (canonicalCodePAProof p)
    (canonicalNatFormula A)

fixedProofOrF :
  {A B : Formula} →
  PA-provable A →
  PA-provable B →
  PRF (suc (suc zero))
fixedProofOrF p q =
  compF orF
    (fixedPAProofF p ∷
     fixedPAProofF q ∷ [])

fixedProofOrPR :
  {A B : Formula} →
  PA-provable A →
  PA-provable B →
  PRRel (suc (suc zero))
fixedProofOrPR p q =
  rel (fixedProofOrF p q)

data FixedProofOrNat
  {A B : Formula}
  (p : PA-provable A)
  (q : PA-provable B)
  (proof-code formula-code : ℕ) : Set where
  fixed-left :
    FixedPAProofNat p proof-code formula-code →
    FixedProofOrNat p q proof-code formula-code

  fixed-right :
    FixedPAProofNat q proof-code formula-code →
    FixedProofOrNat p q proof-code formula-code

or-output-complete-left :
  (left right : ℕ) →
  NonzeroNat left →
  isZeroNat (isZeroNat (left + right)) ≡ suc zero
or-output-complete-left zero right (k ,Σ ())
or-output-complete-left (suc left) right nonzero = refl

or-output-complete-right :
  (left right : ℕ) →
  NonzeroNat right →
  isZeroNat (isZeroNat (left + right)) ≡ suc zero
or-output-complete-right zero zero (k ,Σ ())
or-output-complete-right zero (suc right) nonzero = refl
or-output-complete-right (suc left) right nonzero = refl

or-output-nonzero-sound :
  (left right : ℕ) →
  NonzeroNat (isZeroNat (isZeroNat (left + right))) →
  NonzeroNat left ⊎ NonzeroNat right
or-output-nonzero-sound zero zero (k ,Σ ())
or-output-nonzero-sound zero (suc right) nonzero =
  inj₂ (right ,Σ refl)
or-output-nonzero-sound (suc left) right nonzero =
  inj₁ (left ,Σ refl)

fixedProofOrF-complete :
  {A B : Formula} →
  (p : PA-provable A) →
  (q : PA-provable B) →
  {proof-code formula-code : ℕ} →
  FixedProofOrNat p q proof-code formula-code →
  PRRel-holds
    (fixedProofOrPR p q)
    (proofCodeArgs proof-code formula-code)
fixedProofOrF-complete p q {proof-code} {formula-code} (fixed-left fixed)
  rewrite orF-correct
            (evalPRF (fixedPAProofF p) (proofCodeArgs proof-code formula-code))
            (evalPRF (fixedPAProofF q) (proofCodeArgs proof-code formula-code)) =
  or-output-complete-left
    (evalPRF (fixedPAProofF p) (proofCodeArgs proof-code formula-code))
    (evalPRF (fixedPAProofF q) (proofCodeArgs proof-code formula-code))
    (zero ,Σ proofRuleFixedPAProofPR-complete p fixed)
fixedProofOrF-complete p q {proof-code} {formula-code} (fixed-right fixed)
  rewrite orF-correct
            (evalPRF (fixedPAProofF p) (proofCodeArgs proof-code formula-code))
            (evalPRF (fixedPAProofF q) (proofCodeArgs proof-code formula-code)) =
  or-output-complete-right
    (evalPRF (fixedPAProofF p) (proofCodeArgs proof-code formula-code))
    (evalPRF (fixedPAProofF q) (proofCodeArgs proof-code formula-code))
    (zero ,Σ proofRuleFixedPAProofPR-complete q fixed)

fixedProofOrF-sound :
  {A B : Formula} →
  (p : PA-provable A) →
  (q : PA-provable B) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (fixedProofOrPR p q)
    (proofCodeArgs proof-code formula-code) →
  FixedProofOrNat p q proof-code formula-code
fixedProofOrF-sound p q {proof-code} {formula-code} holds
  rewrite orF-correct
            (evalPRF (fixedPAProofF p) (proofCodeArgs proof-code formula-code))
            (evalPRF (fixedPAProofF q) (proofCodeArgs proof-code formula-code))
  with or-output-nonzero-sound
        (evalPRF (fixedPAProofF p) (proofCodeArgs proof-code formula-code))
        (evalPRF (fixedPAProofF q) (proofCodeArgs proof-code formula-code))
        (zero ,Σ holds)
... | inj₁ left-nonzero =
  fixed-left (fixedPairF-nonzero-sound left-nonzero)
... | inj₂ right-nonzero =
  fixed-right (fixedPairF-nonzero-sound right-nonzero)

fixedProofOrNat-to-decoded :
  {A B : Formula} →
  (p : PA-provable A) →
  (q : PA-provable B) →
  {proof-code formula-code : ℕ} →
  FixedProofOrNat p q proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
fixedProofOrNat-to-decoded p q (fixed-left fixed) =
  fixedPAProofNat-to-decoded p fixed
fixedProofOrNat-to-decoded p q (fixed-right fixed) =
  fixedPAProofNat-to-decoded q fixed

fixedProofOrNat-to-executable :
  {A B : Formula} →
  (p : PA-provable A) →
  (q : PA-provable B) →
  {proof-code formula-code : ℕ} →
  FixedProofOrNat p q proof-code formula-code →
  ExecutableProofCodeNat proof-code formula-code
fixedProofOrNat-to-executable p q {proof-code} {formula-code} proof =
  decoded-to-executableProofCodeNat
    proof-code
    formula-code
    (fixedProofOrNat-to-decoded p q proof)

fixedProofOrPR-to-decoded :
  {A B : Formula} →
  (p : PA-provable A) →
  (q : PA-provable B) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (fixedProofOrPR p q)
    (proofCodeArgs proof-code formula-code) →
  DecodedExecutableProofCodeNat proof-code formula-code
fixedProofOrPR-to-decoded p q holds =
  fixedProofOrNat-to-decoded p q
    (fixedProofOrF-sound p q holds)

fixedProofOrPR-to-executable :
  {A B : Formula} →
  (p : PA-provable A) →
  (q : PA-provable B) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (fixedProofOrPR p q)
    (proofCodeArgs proof-code formula-code) →
  ExecutableProofCodeNat proof-code formula-code
fixedProofOrPR-to-executable p q holds =
  fixedProofOrNat-to-executable p q
    (fixedProofOrF-sound p q holds)

fixedProofOrPR-represented :
  {A B : Formula} →
  (p : PA-provable A) →
  (q : PA-provable B) →
  PARepresentsRelation (fixedProofOrPR p q)
fixedProofOrPR-represented p q =
  prrel-represented (fixedProofOrPR p q)
