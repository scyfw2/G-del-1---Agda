{-# OPTIONS --safe #-}

module Godel.ProofRule37PRHolds where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.ProofCheckingPR using (proofCodeArgs)
open import Godel.ProofRuleTargets

rule37WitnessPR≡inline :
  rule37WitnessPR ≡ rel rule37WitnessF
rule37WitnessPR≡inline = refl

rule37WitnessInline-complete :
  {m n proof-code formula-code : ℕ} →
  Rule37WitnessNat m n proof-code formula-code →
  PRRel-holds
    (rel rule37WitnessF)
    (rule37WitnessArgs m n proof-code formula-code)
rule37WitnessInline-complete {m} {n} {proof-code} {formula-code} witness =
  rule37WitnessF-complete
    {m} {n} {proof-code} {formula-code}
    witness

rule37WitnessInline-sound :
  {m n proof-code formula-code : ℕ} →
  PRRel-holds
    (rel rule37WitnessF)
    (rule37WitnessArgs m n proof-code formula-code) →
  Rule37WitnessNat m n proof-code formula-code
rule37WitnessInline-sound {m} {n} {proof-code} {formula-code} holds =
  rule37WitnessF-sound
    {m} {n} {proof-code} {formula-code}
    holds

rule37WitnessPR-complete :
  {m n proof-code formula-code : ℕ} →
  Rule37WitnessNat m n proof-code formula-code →
  PRRel-holds
    rule37WitnessPR
    (rule37WitnessArgs m n proof-code formula-code)
rule37WitnessPR-complete {m} {n} {proof-code} {formula-code} witness =
  subst
    (λ R →
      PRRel-holds R
        (rule37WitnessArgs m n proof-code formula-code))
    (sym rule37WitnessPR≡inline)
    (rule37WitnessInline-complete
      {m} {n} {proof-code} {formula-code}
      witness)

rule37WitnessPR-sound :
  {m n proof-code formula-code : ℕ} →
  PRRel-holds
    rule37WitnessPR
    (rule37WitnessArgs m n proof-code formula-code) →
  Rule37WitnessNat m n proof-code formula-code
rule37WitnessPR-sound {m} {n} {proof-code} {formula-code} holds =
  rule37WitnessInline-sound
    {m} {n} {proof-code} {formula-code}
    (subst
      (λ R →
        PRRel-holds R
          (rule37WitnessArgs m n proof-code formula-code))
      rule37WitnessPR≡inline
      holds)

Rule37WitnessExists : ℕ → ℕ → Set
Rule37WitnessExists proof-code formula-code =
  Σ ℕ
    (λ m →
      Σ ℕ
        (λ n →
          PRRel-holds
            rule37WitnessPR
            (rule37WitnessArgs m n proof-code formula-code)))

rule37WitnessExists-complete :
  {proof-code formula-code : ℕ} →
  ClosedNumeralNeqRuleNat proof-code formula-code →
  Rule37WitnessExists proof-code formula-code
rule37WitnessExists-complete
  {proof-code}
  {formula-code}
  (m ,Σ (n ,Σ witness)) =
  m ,Σ
    (n ,Σ
      rule37WitnessPR-complete
        {m} {n} {proof-code} {formula-code}
        witness)

rule37WitnessExists-sound :
  {proof-code formula-code : ℕ} →
  Rule37WitnessExists proof-code formula-code →
  ClosedNumeralNeqRuleNat proof-code formula-code
rule37WitnessExists-sound
  {proof-code}
  {formula-code}
  (m ,Σ (n ,Σ holds)) =
  m ,Σ
    (n ,Σ
      rule37WitnessPR-sound
        {m} {n} {proof-code} {formula-code}
        holds)

record ProofRule37WitnessSearchPR : Set₁ where
  field
    rule37-search-pr :
      PRRel (suc (suc zero))

    rule37-search-complete :
      {proof-code formula-code : ℕ} →
      Rule37WitnessExists proof-code formula-code →
      PRRel-holds
        rule37-search-pr
        (proofCodeArgs proof-code formula-code)

    rule37-search-sound :
      {proof-code formula-code : ℕ} →
      PRRel-holds
        rule37-search-pr
        (proofCodeArgs proof-code formula-code) →
      Rule37WitnessExists proof-code formula-code

proofRule37PR-from-witness-search :
  ProofRule37WitnessSearchPR →
  ProofRule37PR
proofRule37PR-from-witness-search D = record
  { rule37-pr =
      ProofRule37WitnessSearchPR.rule37-search-pr D
  ; rule37-complete = λ {proof-code} {formula-code} rule37 →
      ProofRule37WitnessSearchPR.rule37-search-complete D
        {proof-code}
        {formula-code}
        (rule37WitnessExists-complete rule37)
  ; rule37-sound = λ {proof-code} {formula-code} holds →
      rule37WitnessExists-sound
        {proof-code}
        {formula-code}
        (ProofRule37WitnessSearchPR.rule37-search-sound D holds)
  }

proofRule37WitnessSearchPR-represented :
  (D : ProofRule37WitnessSearchPR) →
  ProofRule37PARepresentability
    (proofRule37PR-from-witness-search D)
proofRule37WitnessSearchPR-represented D =
  proofRule37PR-represented
    (proofRule37PR-from-witness-search D)
