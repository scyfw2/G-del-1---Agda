{-# OPTIONS --safe #-}

module Godel.ProofCheckingPRTargets where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Maybe using (just)
open import Godel.Core
open import Godel.Syntax
open import Godel.CanonicalCoding
open import Godel.PrimitiveRecursive
open import Godel.ProofCanonicalChecker
open import Godel.ProofCheckingPR

-- Fully numeric semantic target for the proof checker PR relation.
--
-- ProofCheckingPR is theorem-facing and quantifies over a formula A.  A real
-- PR relation, however, receives only natural-number inputs.  This module
-- packages the exact numeric relation that the eventual proofCodePAPR : PRRel 2
-- should compute.

ExecutableProofCodeNat : ℕ → ℕ → Set
ExecutableProofCodeNat proof-code formula-code =
  Σ Formula
    (λ A →
      (formula-code ≡ canonicalNatFormula A) ×
      ExecutableProofCodePA proof-code A)

DecodedExecutableProofCodeNat : ℕ → ℕ → Set
DecodedExecutableProofCodeNat proof-code formula-code =
  Σ Code
    (λ c →
      Σ Formula
        (λ A →
          (proof-code ≡ encodeCode c) ×
          ((formula-code ≡ canonicalNatFormula A) ×
           (checkPAProofCode c ≡ just A))))

canonicalNatFormula-injective :
  (A B : Formula) →
  canonicalNatFormula A ≡ canonicalNatFormula B →
  A ≡ B
canonicalNatFormula-injective A B eq =
  just-injective
    (trans
      (sym (decodeNatFormula-roundTrip A))
      (trans (cong decodeNatFormula eq)
             (decodeNatFormula-roundTrip B)))

executableProofCodeNat-to-decoded :
  (proof-code formula-code : ℕ) →
  ExecutableProofCodeNat proof-code formula-code →
  DecodedExecutableProofCodeNat proof-code formula-code
executableProofCodeNat-to-decoded proof-code formula-code (A ,Σ (formula-eq ,× exec)) =
  let decoded = executableProofCodePA-to-decoded proof-code exec in
  fstΣ decoded ,Σ
    (A ,Σ
      (fst (sndΣ decoded) ,×
       (formula-eq ,× snd (sndΣ decoded))))

decoded-to-executableProofCodeNat :
  (proof-code formula-code : ℕ) →
  DecodedExecutableProofCodeNat proof-code formula-code →
  ExecutableProofCodeNat proof-code formula-code
decoded-to-executableProofCodeNat proof-code formula-code (c ,Σ (A ,Σ (proof-eq ,× (formula-eq ,× check-eq)))) =
  A ,Σ
    (formula-eq ,×
     decoded-to-executableProofCodePA
       proof-code
       (c ,Σ (proof-eq ,× check-eq)))

record ProofCheckingPRNat : Set₁ where
  field
    proofCodePAPR : PRRel (suc (suc zero))

    proofCodePAPR-complete-nat :
      {proof-code formula-code : ℕ} →
      ExecutableProofCodeNat proof-code formula-code →
      PRRel-holds proofCodePAPR (proofCodeArgs proof-code formula-code)

    proofCodePAPR-sound-nat :
      {proof-code formula-code : ℕ} →
      PRRel-holds proofCodePAPR (proofCodeArgs proof-code formula-code) →
      ExecutableProofCodeNat proof-code formula-code

proofCheckingPRNat-to-ProofCheckingPR :
  ProofCheckingPRNat →
  ProofCheckingPR
proofCheckingPRNat-to-ProofCheckingPR D = record
  { proofCodePAPR = ProofCheckingPRNat.proofCodePAPR D
  ; proofCodePAPR-complete = λ {proof-code} {A} exec →
      ProofCheckingPRNat.proofCodePAPR-complete-nat D
        (A ,Σ (refl ,× exec))
  ; proofCodePAPR-sound = λ {proof-code} {A} holds →
      let sound =
            ProofCheckingPRNat.proofCodePAPR-sound-nat D
              {proof-code}
              {canonicalNatFormula A}
              holds
      in
      subst
        (λ B → ExecutableProofCodePA proof-code B)
        (sym
          (canonicalNatFormula-injective
            A
            (fstΣ sound)
            (fst (sndΣ sound))))
        (snd (sndΣ sound))
  }

record ProofCheckingPRDecodedNat : Set₁ where
  field
    proofCodePAPR : PRRel (suc (suc zero))

    proofCodePAPR-complete-decoded-nat :
      {proof-code formula-code : ℕ} →
      DecodedExecutableProofCodeNat proof-code formula-code →
      PRRel-holds proofCodePAPR (proofCodeArgs proof-code formula-code)

    proofCodePAPR-sound-decoded-nat :
      {proof-code formula-code : ℕ} →
      PRRel-holds proofCodePAPR (proofCodeArgs proof-code formula-code) →
      DecodedExecutableProofCodeNat proof-code formula-code

proofCheckingPRDecodedNat-to-nat :
  ProofCheckingPRDecodedNat →
  ProofCheckingPRNat
proofCheckingPRDecodedNat-to-nat D = record
  { proofCodePAPR =
      ProofCheckingPRDecodedNat.proofCodePAPR D
  ; proofCodePAPR-complete-nat = λ {proof-code} {formula-code} exec →
      ProofCheckingPRDecodedNat.proofCodePAPR-complete-decoded-nat D
        (executableProofCodeNat-to-decoded proof-code formula-code exec)
  ; proofCodePAPR-sound-nat = λ {proof-code} {formula-code} holds →
      decoded-to-executableProofCodeNat
        proof-code
        formula-code
        (ProofCheckingPRDecodedNat.proofCodePAPR-sound-decoded-nat D holds)
  }

proofCheckingPRDecodedNat-to-ProofCheckingPR :
  ProofCheckingPRDecodedNat →
  ProofCheckingPR
proofCheckingPRDecodedNat-to-ProofCheckingPR D =
  proofCheckingPRNat-to-ProofCheckingPR
    (proofCheckingPRDecodedNat-to-nat D)
