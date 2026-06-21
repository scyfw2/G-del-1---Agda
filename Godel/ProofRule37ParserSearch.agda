{-# OPTIONS --safe #-}

module Godel.ProofRule37ParserSearch where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.ProofCheckingPR using (proofCodeArgs)
open import Godel.ProofRule37SearchSkeleton
  using
    ( rule37HitValueFor
    ; rule37SearchFFor
    ; rule37SearchFFor-correct
    ; rule37SearchMMetaFor
    ; rule37SearchNMetaFor
    )
open import Godel.ProofRule37ParserWitness
  using
    ( Rule37ParserWitnessNat
    ; rule37ParserWitnessF
    ; rule37ParserWitnessPR
    )
open import Godel.ProofRuleTargets using (rule37WitnessArgs)

-- A parser-backed bounded-search candidate for rule 37.
--
-- This mirrors Godel.ProofRule37Search, but the searched witness predicate is
-- rule37ParserWitnessF, whose proof-code branch goes through nodeChildrenF and
-- rule37DecomposedWitnessF.

rule37ParserSearchF : PRF (suc (suc zero))
rule37ParserSearchF =
  rule37SearchFFor rule37ParserWitnessF

rule37ParserSearchPR : PRRel (suc (suc zero))
rule37ParserSearchPR =
  rel rule37ParserSearchF

rule37ParserWitnessValue : ℕ → ℕ → ℕ → ℕ → ℕ
rule37ParserWitnessValue m n proof-code formula-code =
  rule37HitValueFor rule37ParserWitnessF m n proof-code formula-code

rule37ParserSearchNMeta : ℕ → ℕ → ℕ → ℕ → ℕ
rule37ParserSearchNMeta bound m proof-code formula-code =
  rule37SearchNMetaFor
    rule37ParserWitnessF
    bound
    m
    proof-code
    formula-code

rule37ParserSearchMMeta : ℕ → ℕ → ℕ → ℕ
rule37ParserSearchMMeta bound proof-code formula-code =
  rule37SearchMMetaFor
    rule37ParserWitnessF
    bound
    proof-code
    formula-code

Rule37ParserWitnessExists : ℕ → ℕ → Set
Rule37ParserWitnessExists proof-code formula-code =
  Σ ℕ
    (λ m →
      Σ ℕ
        (λ n →
          Rule37ParserWitnessNat m n proof-code formula-code))

record Rule37ParserSearchSemantics : Set₁ where
  field
    parser-search-f-correct :
      (proof-code formula-code : ℕ) →
      evalPRF
        rule37ParserSearchF
        (proofCodeArgs proof-code formula-code)
      ≡
      rule37ParserSearchMMeta proof-code proof-code formula-code

rule37ParserSearchF-correct :
  (proof-code formula-code : ℕ) →
  evalPRF
    rule37ParserSearchF
    (proofCodeArgs proof-code formula-code)
  ≡
  rule37ParserSearchMMeta proof-code proof-code formula-code
rule37ParserSearchF-correct =
  rule37SearchFFor-correct rule37ParserWitnessF

rule37ParserSearchSemantics : Rule37ParserSearchSemantics
rule37ParserSearchSemantics = record
  { parser-search-f-correct =
      rule37ParserSearchF-correct
  }

record Rule37ParserSearchCorrect : Set₁ where
  field
    parser-search-semantics :
      Rule37ParserSearchSemantics

    parser-search-complete :
      {proof-code formula-code : ℕ} →
      Rule37ParserWitnessExists proof-code formula-code →
      evalPRF
        rule37ParserSearchF
        (proofCodeArgs proof-code formula-code)
      ≡ suc zero

    parser-search-sound :
      {proof-code formula-code : ℕ} →
      evalPRF
        rule37ParserSearchF
        (proofCodeArgs proof-code formula-code)
      ≡ suc zero →
      Rule37ParserWitnessExists proof-code formula-code
