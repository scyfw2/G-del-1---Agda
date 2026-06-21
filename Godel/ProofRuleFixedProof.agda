{-# OPTIONS --safe #-}

module Godel.ProofRuleFixedProof where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.CanonicalCoding using (canonicalNatFormula)
open import Godel.PrimitiveRecursive
open import Godel.PA
open import Godel.ProofCanonicalCoding
open import Godel.ProofCanonicalChecker using (checkPAProofCode-complete)
open import Godel.ProofCheckingPR using (proofCodeArgs)
open import Godel.ProofCheckingPRTargets
  using
    ( DecodedExecutableProofCodeNat
    ; ExecutableProofCodeNat
    ; decoded-to-executableProofCodeNat
    )
open import Godel.ProofRuleFixedPair
open import Godel.ProofRuleFixedPairTarget

-- Any already-known PA proof is a fixed proof-checker leaf: its canonical proof
-- code and its conclusion formula code are both fixed numeric values.  This
-- module packages that observation as a small rule target.

FixedPAProofNat :
  {A : Formula} →
  PA-provable A →
  ℕ →
  ℕ →
  Set
FixedPAProofNat {A} p proof-code formula-code =
  FixedPairNat
    (canonicalCodePAProof p)
    (canonicalNatFormula A)
    proof-code
    formula-code

fixedPAProofNat-complete :
  {A : Formula} →
  (p : PA-provable A) →
  FixedPAProofNat
    p
    (canonicalCodePAProof p)
    (canonicalNatFormula A)
fixedPAProofNat-complete p =
  refl ,× refl

fixedPAProofNat-to-decoded :
  {A : Formula} →
  (p : PA-provable A) →
  {proof-code formula-code : ℕ} →
  FixedPAProofNat p proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
fixedPAProofNat-to-decoded {A} p (proof-eq ,× formula-eq) =
  canonicalDerivationCode canonicalPAAxiomCode p ,Σ
    (A ,Σ
      (proof-eq ,×
       (formula-eq ,× checkPAProofCode-complete p)))

fixedPAProofNat-to-executable :
  {A : Formula} →
  (p : PA-provable A) →
  {proof-code formula-code : ℕ} →
  FixedPAProofNat p proof-code formula-code →
  ExecutableProofCodeNat proof-code formula-code
fixedPAProofNat-to-executable p {proof-code} {formula-code} fixed-proof =
  decoded-to-executableProofCodeNat
    proof-code
    formula-code
    (fixedPAProofNat-to-decoded p fixed-proof)

proofRuleFixedPAProofPR :
  {A : Formula} →
  (p : PA-provable A) →
  ProofRuleFixedPairPR
    (canonicalCodePAProof p)
    (canonicalNatFormula A)
proofRuleFixedPAProofPR {A} p =
  proofRuleFixedPairPR
    (canonicalCodePAProof p)
    (canonicalNatFormula A)

proofRuleFixedPAProofPR-complete :
  {A : Formula} →
  (p : PA-provable A) →
  {proof-code formula-code : ℕ} →
  FixedPAProofNat p proof-code formula-code →
  PRRel-holds
    (ProofRuleFixedPairPR.fixed-pair-pr
      (proofRuleFixedPAProofPR p))
    (proofCodeArgs proof-code formula-code)
proofRuleFixedPAProofPR-complete p fixed-proof =
  ProofRuleFixedPairPR.fixed-pair-complete
    (proofRuleFixedPAProofPR p)
    fixed-proof

proofRuleFixedPAProofPR-sound :
  {A : Formula} →
  (p : PA-provable A) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (ProofRuleFixedPairPR.fixed-pair-pr
      (proofRuleFixedPAProofPR p))
    (proofCodeArgs proof-code formula-code) →
  FixedPAProofNat p proof-code formula-code
proofRuleFixedPAProofPR-sound p holds =
  ProofRuleFixedPairPR.fixed-pair-sound
    (proofRuleFixedPAProofPR p)
    holds

proofRuleFixedPAProofPR-to-decoded :
  {A : Formula} →
  (p : PA-provable A) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (ProofRuleFixedPairPR.fixed-pair-pr
      (proofRuleFixedPAProofPR p))
    (proofCodeArgs proof-code formula-code) →
  DecodedExecutableProofCodeNat proof-code formula-code
proofRuleFixedPAProofPR-to-decoded p holds =
  fixedPAProofNat-to-decoded
    p
    (proofRuleFixedPAProofPR-sound p holds)

proofRuleFixedPAProofPR-to-executable :
  {A : Formula} →
  (p : PA-provable A) →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (ProofRuleFixedPairPR.fixed-pair-pr
      (proofRuleFixedPAProofPR p))
    (proofCodeArgs proof-code formula-code) →
  ExecutableProofCodeNat proof-code formula-code
proofRuleFixedPAProofPR-to-executable p {proof-code} {formula-code} holds =
  decoded-to-executableProofCodeNat
    proof-code
    formula-code
    (proofRuleFixedPAProofPR-to-decoded p holds)

proofRuleFixedPAProofPARepresentability :
  {A : Formula} →
  (p : PA-provable A) →
  ProofRuleFixedPairPARepresentability
    (canonicalCodePAProof p)
    (canonicalNatFormula A)
proofRuleFixedPAProofPARepresentability {A} p =
  proofRuleFixedPairPARepresentability
    (canonicalCodePAProof p)
    (canonicalNatFormula A)
