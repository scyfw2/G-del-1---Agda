{-# OPTIONS --safe #-}

module Godel.ProofRuleFixedCodeLeaf where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax using (Formula)
open import Godel.PrimitiveRecursive
open import Godel.PRBooleanHelpers using (orF)
open import Godel.PRArithmeticSemantics using (isZeroNat; orF-correct)
open import Godel.PRRepresentabilityFinal
  using (PARepresentsRelation; prrel-represented)
open import Godel.CanonicalCoding using (canonicalNatFormula)
open import Godel.PA using (PA-provable)
open import Godel.ProofCanonicalCoding using (canonicalCodePAProof)
open import Godel.ProofCheckingPR using (proofCodeArgs)
open import Godel.ProofCheckingPRTargets
  using
    ( DecodedExecutableProofCodeNat
    ; ExecutableProofCodeNat
    ; decoded-to-executableProofCodeNat
    )
open import Godel.ProofRuleFixedPair
open import Godel.ProofRuleFixedProof
  using
    ( fixedPAProofNat-complete
    ; fixedPAProofNat-to-decoded
    )
open import Godel.ProofRuleFixedProofOr
  using
    ( NonzeroNat
    ; fixedPairF-nonzero-sound
    ; or-output-complete-left
    ; or-output-complete-right
    ; or-output-nonzero-sound
    )

-- Explicit fixed-code proof checker leaves.
--
-- This is the performance-friendly boundary for concrete PA axiom leaves:
-- instead of recomputing large formula/proof codes while composing branches,
-- a caller supplies named numeric codes together with a decoded checker witness
-- for exactly that pair.

record FixedCodeLeafData : Set₁ where
  field
    expected-proof-code :
      ℕ

    expected-formula-code :
      ℕ

    leaf-decoded :
      DecodedExecutableProofCodeNat
        expected-proof-code
        expected-formula-code

FixedCodeLeafNat :
  FixedCodeLeafData →
  ℕ →
  ℕ →
  Set
FixedCodeLeafNat D proof-code formula-code =
  FixedPairNat
    (FixedCodeLeafData.expected-proof-code D)
    (FixedCodeLeafData.expected-formula-code D)
    proof-code
    formula-code

fixedCodeLeafF :
  FixedCodeLeafData →
  PRF (suc (suc zero))
fixedCodeLeafF D =
  fixedPairF
    (FixedCodeLeafData.expected-proof-code D)
    (FixedCodeLeafData.expected-formula-code D)

fixedCodeLeafPR :
  FixedCodeLeafData →
  PRRel (suc (suc zero))
fixedCodeLeafPR D =
  rel (fixedCodeLeafF D)

fixedCodeLeaf-complete :
  (D : FixedCodeLeafData) →
  {proof-code formula-code : ℕ} →
  FixedCodeLeafNat D proof-code formula-code →
  PRRel-holds
    (fixedCodeLeafPR D)
    (proofCodeArgs proof-code formula-code)
fixedCodeLeaf-complete D fixed =
  fixedPairF-complete fixed

fixedCodeLeaf-sound :
  (D : FixedCodeLeafData) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (fixedCodeLeafPR D)
    (proofCodeArgs proof-code formula-code) →
  FixedCodeLeafNat D proof-code formula-code
fixedCodeLeaf-sound D holds =
  fixedPairF-sound holds

fixedCodeLeafNat-to-decoded :
  (D : FixedCodeLeafData) →
  {proof-code formula-code : ℕ} →
  FixedCodeLeafNat D proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
fixedCodeLeafNat-to-decoded D {proof-code} {formula-code} (proof-eq ,× formula-eq) =
  subst
    (λ fc → DecodedExecutableProofCodeNat proof-code fc)
    (sym formula-eq)
    (subst
      (λ pc →
        DecodedExecutableProofCodeNat
          pc
          (FixedCodeLeafData.expected-formula-code D))
      (sym proof-eq)
      (FixedCodeLeafData.leaf-decoded D))

fixedCodeLeafNat-to-executable :
  (D : FixedCodeLeafData) →
  {proof-code formula-code : ℕ} →
  FixedCodeLeafNat D proof-code formula-code →
  ExecutableProofCodeNat proof-code formula-code
fixedCodeLeafNat-to-executable D {proof-code} {formula-code} fixed =
  decoded-to-executableProofCodeNat
    proof-code
    formula-code
    (fixedCodeLeafNat-to-decoded D fixed)

fixedCodeLeafPR-to-decoded :
  (D : FixedCodeLeafData) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (fixedCodeLeafPR D)
    (proofCodeArgs proof-code formula-code) →
  DecodedExecutableProofCodeNat proof-code formula-code
fixedCodeLeafPR-to-decoded D holds =
  fixedCodeLeafNat-to-decoded D
    (fixedCodeLeaf-sound D holds)

fixedCodeLeafPR-to-executable :
  (D : FixedCodeLeafData) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (fixedCodeLeafPR D)
    (proofCodeArgs proof-code formula-code) →
  ExecutableProofCodeNat proof-code formula-code
fixedCodeLeafPR-to-executable D holds =
  fixedCodeLeafNat-to-executable D
    (fixedCodeLeaf-sound D holds)

fixedCodeLeafPR-represented :
  (D : FixedCodeLeafData) →
  PARepresentsRelation (fixedCodeLeafPR D)
fixedCodeLeafPR-represented D =
  prrel-represented (fixedCodeLeafPR D)

fixedPAProofLeafData :
  {A : Formula} →
  PA-provable A →
  FixedCodeLeafData
fixedPAProofLeafData {A} p = record
  { expected-proof-code =
      canonicalCodePAProof p
  ; expected-formula-code =
      canonicalNatFormula A
  ; leaf-decoded =
      fixedPAProofNat-to-decoded
        p
        (fixedPAProofNat-complete p)
  }

-- Binary OR combinator over explicit fixed-code leaves.

fixedCodeLeafOrF :
  FixedCodeLeafData →
  FixedCodeLeafData →
  PRF (suc (suc zero))
fixedCodeLeafOrF left right =
  compF orF
    (fixedCodeLeafF left ∷
     fixedCodeLeafF right ∷ [])

fixedCodeLeafOrPR :
  FixedCodeLeafData →
  FixedCodeLeafData →
  PRRel (suc (suc zero))
fixedCodeLeafOrPR left right =
  rel (fixedCodeLeafOrF left right)

data FixedCodeLeafOrNat
  (left right : FixedCodeLeafData)
  (proof-code formula-code : ℕ) : Set where
  fixed-code-left :
    FixedCodeLeafNat left proof-code formula-code →
    FixedCodeLeafOrNat left right proof-code formula-code

  fixed-code-right :
    FixedCodeLeafNat right proof-code formula-code →
    FixedCodeLeafOrNat left right proof-code formula-code

fixedCodeLeafOr-complete :
  (left right : FixedCodeLeafData) →
  {proof-code formula-code : ℕ} →
  FixedCodeLeafOrNat left right proof-code formula-code →
  PRRel-holds
    (fixedCodeLeafOrPR left right)
    (proofCodeArgs proof-code formula-code)
fixedCodeLeafOr-complete left right {proof-code} {formula-code} (fixed-code-left fixed)
  rewrite orF-correct
            (evalPRF (fixedCodeLeafF left) (proofCodeArgs proof-code formula-code))
            (evalPRF (fixedCodeLeafF right) (proofCodeArgs proof-code formula-code)) =
  or-output-complete-left
    (evalPRF (fixedCodeLeafF left) (proofCodeArgs proof-code formula-code))
    (evalPRF (fixedCodeLeafF right) (proofCodeArgs proof-code formula-code))
    (zero ,Σ fixedCodeLeaf-complete left fixed)
fixedCodeLeafOr-complete left right {proof-code} {formula-code} (fixed-code-right fixed)
  rewrite orF-correct
            (evalPRF (fixedCodeLeafF left) (proofCodeArgs proof-code formula-code))
            (evalPRF (fixedCodeLeafF right) (proofCodeArgs proof-code formula-code)) =
  or-output-complete-right
    (evalPRF (fixedCodeLeafF left) (proofCodeArgs proof-code formula-code))
    (evalPRF (fixedCodeLeafF right) (proofCodeArgs proof-code formula-code))
    (zero ,Σ fixedCodeLeaf-complete right fixed)

fixedCodeLeafOr-sound :
  (left right : FixedCodeLeafData) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (fixedCodeLeafOrPR left right)
    (proofCodeArgs proof-code formula-code) →
  FixedCodeLeafOrNat left right proof-code formula-code
fixedCodeLeafOr-sound left right {proof-code} {formula-code} holds
  rewrite orF-correct
            (evalPRF (fixedCodeLeafF left) (proofCodeArgs proof-code formula-code))
            (evalPRF (fixedCodeLeafF right) (proofCodeArgs proof-code formula-code))
  with or-output-nonzero-sound
        (evalPRF (fixedCodeLeafF left) (proofCodeArgs proof-code formula-code))
        (evalPRF (fixedCodeLeafF right) (proofCodeArgs proof-code formula-code))
        (zero ,Σ holds)
... | inj₁ fixed-code-left-hit =
  fixed-code-left
    (fixedPairF-nonzero-sound fixed-code-left-hit)
... | inj₂ fixed-code-right-hit =
  fixed-code-right
    (fixedPairF-nonzero-sound fixed-code-right-hit)

fixedCodeLeafOr-nonzero-sound :
  (left right : FixedCodeLeafData) →
  {proof-code formula-code : ℕ} →
  NonzeroNat
    (evalPRF
      (fixedCodeLeafOrF left right)
      (proofCodeArgs proof-code formula-code)) →
  FixedCodeLeafOrNat left right proof-code formula-code
fixedCodeLeafOr-nonzero-sound left right {proof-code} {formula-code} nonzero
  rewrite orF-correct
            (evalPRF (fixedCodeLeafF left) (proofCodeArgs proof-code formula-code))
            (evalPRF (fixedCodeLeafF right) (proofCodeArgs proof-code formula-code))
  with or-output-nonzero-sound
        (evalPRF (fixedCodeLeafF left) (proofCodeArgs proof-code formula-code))
        (evalPRF (fixedCodeLeafF right) (proofCodeArgs proof-code formula-code))
        nonzero
... | inj₁ fixed-code-left-hit =
  fixed-code-left
    (fixedPairF-nonzero-sound fixed-code-left-hit)
... | inj₂ fixed-code-right-hit =
  fixed-code-right
    (fixedPairF-nonzero-sound fixed-code-right-hit)

fixedCodeLeafOrNat-to-decoded :
  (left right : FixedCodeLeafData) →
  {proof-code formula-code : ℕ} →
  FixedCodeLeafOrNat left right proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
fixedCodeLeafOrNat-to-decoded left right (fixed-code-left fixed) =
  fixedCodeLeafNat-to-decoded left fixed
fixedCodeLeafOrNat-to-decoded left right (fixed-code-right fixed) =
  fixedCodeLeafNat-to-decoded right fixed

fixedCodeLeafOrNat-to-executable :
  (left right : FixedCodeLeafData) →
  {proof-code formula-code : ℕ} →
  FixedCodeLeafOrNat left right proof-code formula-code →
  ExecutableProofCodeNat proof-code formula-code
fixedCodeLeafOrNat-to-executable left right {proof-code} {formula-code} proof =
  decoded-to-executableProofCodeNat
    proof-code
    formula-code
    (fixedCodeLeafOrNat-to-decoded left right proof)

fixedCodeLeafOrPR-to-decoded :
  (left right : FixedCodeLeafData) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (fixedCodeLeafOrPR left right)
    (proofCodeArgs proof-code formula-code) →
  DecodedExecutableProofCodeNat proof-code formula-code
fixedCodeLeafOrPR-to-decoded left right holds =
  fixedCodeLeafOrNat-to-decoded left right
    (fixedCodeLeafOr-sound left right holds)

fixedCodeLeafOrPR-to-executable :
  (left right : FixedCodeLeafData) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (fixedCodeLeafOrPR left right)
    (proofCodeArgs proof-code formula-code) →
  ExecutableProofCodeNat proof-code formula-code
fixedCodeLeafOrPR-to-executable left right holds =
  fixedCodeLeafOrNat-to-executable left right
    (fixedCodeLeafOr-sound left right holds)

fixedCodeLeafOrPR-represented :
  (left right : FixedCodeLeafData) →
  PARepresentsRelation (fixedCodeLeafOrPR left right)
fixedCodeLeafOrPR-represented left right =
  prrel-represented (fixedCodeLeafOrPR left right)
