{-# OPTIONS --safe #-}

module Godel.ProofCheckingPR where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.PA
open import Godel.ProofSystem
open import Godel.Coding
open import Godel.CanonicalCoding
open import Godel.PrimitiveRecursive
open import Godel.PRRepresentabilityFinal
open import Godel.ProofCoding
open import Godel.ProofCanonicalCoding
open import Godel.ProofCanonicalChecker
open import Godel.PAFirstIncompleteness

proofCodeArgs : ℕ → ℕ → Vec ℕ (suc (suc zero))
proofCodeArgs proof-code formula-code =
  proof-code ∷ formula-code ∷ []

proofCodeTermArgs : Term → Term → Vec Term (suc (suc zero))
proofCodeTermArgs proof-code formula-code =
  proof-code ∷ formula-code ∷ []

-- Target layer for the primitive-recursive PA proof checker.
--
-- The second argument is the canonical formula code.  This deliberately keeps
-- the PR checker on the decodable canonical syntax-coding route.  The proof
-- code itself is also canonical: it is the numeric encoding of a structural
-- proof-tree Code from Godel.ProofCanonicalCoding.  Semantically, this record
-- represents the executable checker relation from Godel.ProofCanonicalChecker.
record ProofCheckingPR : Set₁ where
  field
    proofCodePAPR : PRRel (suc (suc zero))

    proofCodePAPR-complete :
      {proof-code : ℕ} → {A : Formula} →
      ExecutableProofCodePA proof-code A →
      PRRel-holds
        proofCodePAPR
        (proofCodeArgs proof-code (canonicalNatFormula A))

    proofCodePAPR-sound :
      {proof-code : ℕ} → {A : Formula} →
      PRRel-holds
        proofCodePAPR
        (proofCodeArgs proof-code (canonicalNatFormula A)) →
      ExecutableProofCodePA proof-code A

proofCodePAPR-represented :
  (D : ProofCheckingPR) →
  PARepresentsRelation (ProofCheckingPR.proofCodePAPR D)
proofCodePAPR-represented D =
  prrel-represented (ProofCheckingPR.proofCodePAPR D)

ProofCodePAPRFormula :
  (D : ProofCheckingPR) →
  Term →
  Term →
  Formula
ProofCodePAPRFormula D proof-code formula-code =
  PARepresentsRelation.relationFormula
    (proofCodePAPR-represented D)
    (proofCodeTermArgs proof-code formula-code)

proofCodePAPR-true :
  (D : ProofCheckingPR) →
  {proof-code : ℕ} → {A : Formula} →
  ExecutableProofCodePA proof-code A →
  PA-provable
    (ProofCodePAPRFormula
      D
      (numeral proof-code)
      (numeral (canonicalNatFormula A)))
proofCodePAPR-true D proof-code-pa =
  PARepresentsRelation.represents-true
    (proofCodePAPR-represented D)
    (proofCodeArgs _ _)
    (ProofCheckingPR.proofCodePAPR-complete D proof-code-pa)

proofCodePAPR-false :
  (D : ProofCheckingPR) →
  (proof-code : ℕ) → (A : Formula) →
  ¬ ExecutableProofCodePA proof-code A →
  PA-provable
    (¬ᶠ
      (ProofCodePAPRFormula
        D
        (numeral proof-code)
        (numeral (canonicalNatFormula A))))
proofCodePAPR-false D proof-code A not-proof-code =
  PARepresentsRelation.represents-false
    (proofCodePAPR-represented D)
    (proofCodeArgs proof-code (canonicalNatFormula A))
    (λ pr-holds →
      not-proof-code
        (ProofCheckingPR.proofCodePAPR-sound D pr-holds))

canonicalProofCodePA-checker-true :
  (D : ProofCheckingPR) →
  {proof-code : ℕ} → {A : Formula} →
  CanonicalProofCodePA proof-code A →
  PA-provable
    (ProofCodePAPRFormula
      D
      (numeral proof-code)
      (numeral (canonicalNatFormula A)))
canonicalProofCodePA-checker-true D canonical-proof-code =
  proofCodePAPR-true
    D
    (checkCanonicalPAProofNat-complete canonical-proof-code)

proofCodePAPR-reconstructs-PA-proof :
  (D : ProofCheckingPR) →
  {proof-code : ℕ} → {A : Formula} →
  PRRel-holds
    (ProofCheckingPR.proofCodePAPR D)
    (proofCodeArgs proof-code (canonicalNatFormula A)) →
  PA-provable A
proofCodePAPR-reconstructs-PA-proof D {proof-code} holds =
  checkCanonicalPAProofNat-sound
    proof-code
    (ProofCheckingPR.proofCodePAPR-sound D holds)

proofCodePAPR-sound-decoded :
  (D : ProofCheckingPR) →
  {proof-code : ℕ} → {A : Formula} →
  PRRel-holds
    (ProofCheckingPR.proofCodePAPR D)
    (proofCodeArgs proof-code (canonicalNatFormula A)) →
  DecodedExecutableProofCodePA proof-code A
proofCodePAPR-sound-decoded D {proof-code} holds =
  executableProofCodePA-to-decoded
    proof-code
    (ProofCheckingPR.proofCodePAPR-sound D holds)

decodedProofCodePA-checker-true :
  (D : ProofCheckingPR) →
  {proof-code : ℕ} → {A : Formula} →
  DecodedExecutableProofCodePA proof-code A →
  PA-provable
    (ProofCodePAPRFormula
      D
      (numeral proof-code)
      (numeral (canonicalNatFormula A)))
decodedProofCodePA-checker-true D {proof-code} decoded =
  proofCodePAPR-true
    D
    (decoded-to-executableProofCodePA proof-code decoded)

-- The final incompleteness theorem still talks through Godel.Coding.ProofOf,
-- whose formula code is the legacy codeFormula.  A concrete proof checker PR
-- instance therefore needs this bridge until ProofOf itself is migrated to the
-- canonical formula-code route.  The bridge does not assume that legacy proof
-- codes and canonical proof codes are numerically identical; it records the
-- exact PA-facing implications still needed to connect the two routes.
record ProofPredicatePRBridge (D : ProofCheckingPR) : Set₁ where
  field
    legacy-proofCodePA-implies-checker :
      {proof-code : ℕ} → {A : Formula} →
      ProofCodePA proof-code A →
      PA-provable
        (ProofCodePAPRFormula
          D
          (numeral proof-code)
          (numeral (canonicalNatFormula A)))

    legacy-nonProof-implies-checker-false :
      {proof-code : ℕ} → {A : Formula} →
      ¬ ProofCodePA proof-code A →
      PA-provable
        (¬ᶠ
          (ProofCodePAPRFormula
            D
            (numeral proof-code)
            (numeral (canonicalNatFormula A))))

    checker-implies-ProofOf :
      {proof-code : ℕ} → {A : Formula} →
      PA-provable
        (ProofCodePAPRFormula
          D
          (numeral proof-code)
          (numeral (canonicalNatFormula A))
         ⇒
         ProofOf (numeral proof-code) A)

    ProofOf-implies-checker :
      {proof-code : ℕ} → {A : Formula} →
      PA-provable
        (ProofOf (numeral proof-code) A ⇒
         ProofCodePAPRFormula
          D
          (numeral proof-code)
          (numeral (canonicalNatFormula A)))

proof-checking-pr-represents-proof :
  (D : ProofCheckingPR) →
  ProofPredicatePRBridge D →
  {A : Formula} → {proof-code : ℕ} →
  ProofCodePA proof-code A →
  PA-provable (ProofOf (numeral proof-code) A)
proof-checking-pr-represents-proof D bridge proof-code-pa =
  modus-ponens
    (ProofPredicatePRBridge.checker-implies-ProofOf bridge)
    (ProofPredicatePRBridge.legacy-proofCodePA-implies-checker
      bridge
      proof-code-pa)

proof-checking-pr-represents-nonProof :
  (D : ProofCheckingPR) →
  ProofPredicatePRBridge D →
  {A : Formula} →
  (proof-code : ℕ) →
  ¬ ProofCodePA proof-code A →
  PA-provable (¬ᶠ (ProofOf (numeral proof-code) A))
proof-checking-pr-represents-nonProof D bridge {A} proof-code not-proof-code =
  modus-ponens
    (modus-ponens
      contradiction-to-neg
      (ProofPredicatePRBridge.ProofOf-implies-checker bridge))
    (ProofPredicatePRBridge.legacy-nonProof-implies-checker-false
      bridge
      not-proof-code)

record PAProofPredicatePRData : Set₁ where
  field
    proof-checking-pr : ProofCheckingPR
    proof-predicate-bridge :
      ProofPredicatePRBridge proof-checking-pr

    classical-step-PA :
      {A : Formula} →
      PA-provable ((noProofs A ⇒ A) ⇒ ((¬ᶠ A) ⇒ someProof A))

proof-checking-pr-to-PARepresentability :
  PAProofPredicatePRData →
  PARepresentability
proof-checking-pr-to-PARepresentability D = record
  { represents-proof-PA =
      proof-checking-pr-represents-proof
        (PAProofPredicatePRData.proof-checking-pr D)
        (PAProofPredicatePRData.proof-predicate-bridge D)
  ; represents-nonProof-PA =
      proof-checking-pr-represents-nonProof
        (PAProofPredicatePRData.proof-checking-pr D)
        (PAProofPredicatePRData.proof-predicate-bridge D)
  ; classical-step-PA =
      PAProofPredicatePRData.classical-step-PA D
  }
