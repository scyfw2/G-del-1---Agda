{-# OPTIONS --safe #-}

module Godel.ProofRule37ParserSearchHit where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.CanonicalCoding using (_≤_)
open import Godel.PrimitiveRecursive using (evalPRF)
open import Godel.ProofCheckingPR using (proofCodeArgs)
open import Godel.ProofRule37ParserWitness
  using
    ( Rule37ParserWitnessNat )
open import Godel.ProofRule37ParserSearch
  using
    ( Rule37ParserSearchCorrect
    ; Rule37ParserSearchSemantics
    ; Rule37ParserWitnessExists
    ; rule37ParserSearchF
    ; rule37ParserSearchMMeta
    ; rule37ParserWitnessValue
    )
open import Godel.ProofRule37SearchCorrectness
  using
    ( Search2BoundedHit
    ; Search2BoundedNonzero
    ; search2UpTo
    ; search2UpTo-hit-bound
    ; search2UpTo-sound-one
    )

-- Hit-interface factoring for the parser-backed rule-37 bounded search.
--
-- This mirrors Godel.ProofRule37SearchHit, but it takes the parser-search
-- semantic correctness as an explicit input.  That keeps the heavy nested
-- parser witness out of the generic bounded-search proof.

record Rule37ParserSearchHitInterface : Set₁ where
  field
    witness-hit-value : ℕ → ℕ → ℕ → ℕ → ℕ

    parser-search-meta-as-hit-search2 :
      (proof-code formula-code : ℕ) →
      rule37ParserSearchMMeta proof-code proof-code formula-code ≡
      search2UpTo
        (λ m n → witness-hit-value m n proof-code formula-code)
        proof-code
        proof-code

Rule37ParserWitnessBoundedHit :
  Rule37ParserSearchHitInterface → ℕ → ℕ → Set
Rule37ParserWitnessBoundedHit I proof-code formula-code =
  Search2BoundedHit
    (λ m n →
      Rule37ParserSearchHitInterface.witness-hit-value
        I
        m
        n
        proof-code
        formula-code)
    proof-code
    proof-code

Rule37ParserWitnessBoundedNonzero :
  Rule37ParserSearchHitInterface → ℕ → ℕ → Set
Rule37ParserWitnessBoundedNonzero I proof-code formula-code =
  Search2BoundedNonzero
    (λ m n →
      Rule37ParserSearchHitInterface.witness-hit-value
        I
        m
        n
        proof-code
        formula-code)
    proof-code
    proof-code

rule37ParserSearch-complete-bounded-hit :
  (S : Rule37ParserSearchSemantics) →
  (I : Rule37ParserSearchHitInterface) →
  {proof-code formula-code : ℕ} →
  Rule37ParserWitnessBoundedHit I proof-code formula-code →
  evalPRF rule37ParserSearchF (proofCodeArgs proof-code formula-code) ≡
  suc zero
rule37ParserSearch-complete-bounded-hit
    S I {proof-code} {formula-code} hit
  rewrite Rule37ParserSearchSemantics.parser-search-f-correct
            S
            proof-code
            formula-code
        | Rule37ParserSearchHitInterface.parser-search-meta-as-hit-search2
            I
            proof-code
            formula-code =
  search2UpTo-hit-bound hit

rule37ParserSearch-sound-bounded-hit :
  (S : Rule37ParserSearchSemantics) →
  (I : Rule37ParserSearchHitInterface) →
  {proof-code formula-code : ℕ} →
  evalPRF rule37ParserSearchF (proofCodeArgs proof-code formula-code) ≡
  suc zero →
  Rule37ParserWitnessBoundedNonzero I proof-code formula-code
rule37ParserSearch-sound-bounded-hit
    S I {proof-code} {formula-code} search-holds
  rewrite Rule37ParserSearchSemantics.parser-search-f-correct
            S
            proof-code
            formula-code
        | Rule37ParserSearchHitInterface.parser-search-meta-as-hit-search2
            I
            proof-code
            formula-code =
  search2UpTo-sound-one proof-code proof-code search-holds

record Rule37ParserWitnessHitBridge
    (WitnessExists : ℕ → ℕ → Set) : Set₁ where
  field
    hit-interface : Rule37ParserSearchHitInterface

    witness-exists-to-bounded-hit :
      {proof-code formula-code : ℕ} →
      WitnessExists proof-code formula-code →
      Rule37ParserWitnessBoundedHit
        hit-interface
        proof-code
        formula-code

rule37ParserSearch-complete-from-hit-bridge :
  {WitnessExists : ℕ → ℕ → Set} →
  Rule37ParserSearchSemantics →
  Rule37ParserWitnessHitBridge WitnessExists →
  {proof-code formula-code : ℕ} →
  WitnessExists proof-code formula-code →
  evalPRF rule37ParserSearchF (proofCodeArgs proof-code formula-code) ≡
  suc zero
rule37ParserSearch-complete-from-hit-bridge S bridge witness =
  rule37ParserSearch-complete-bounded-hit
    S
    (Rule37ParserWitnessHitBridge.hit-interface bridge)
    (Rule37ParserWitnessHitBridge.witness-exists-to-bounded-hit bridge witness)

record Rule37ParserWitnessHitSoundBridge
    (WitnessExists : ℕ → ℕ → Set) : Set₁ where
  field
    hit-interface : Rule37ParserSearchHitInterface

    bounded-nonzero-to-witness :
      {proof-code formula-code : ℕ} →
      Rule37ParserWitnessBoundedNonzero
        hit-interface
        proof-code
        formula-code →
      WitnessExists proof-code formula-code

rule37ParserSearch-sound-from-hit-bridge :
  {WitnessExists : ℕ → ℕ → Set} →
  Rule37ParserSearchSemantics →
  Rule37ParserWitnessHitSoundBridge WitnessExists →
  {proof-code formula-code : ℕ} →
  evalPRF rule37ParserSearchF (proofCodeArgs proof-code formula-code) ≡
  suc zero →
  WitnessExists proof-code formula-code
rule37ParserSearch-sound-from-hit-bridge S bridge search-holds =
  Rule37ParserWitnessHitSoundBridge.bounded-nonzero-to-witness
    bridge
    (rule37ParserSearch-sound-bounded-hit
      S
      (Rule37ParserWitnessHitSoundBridge.hit-interface bridge)
      search-holds)

rule37ParserSearchHitInterface : Rule37ParserSearchHitInterface
rule37ParserSearchHitInterface = record
  { witness-hit-value =
      rule37ParserWitnessValue
  ; parser-search-meta-as-hit-search2 =
      λ proof-code formula-code → refl
  }

record Rule37ParserWitnessBoundsBridge : Set₁ where
  field
    parser-witness-bounds :
      {m n proof-code formula-code : ℕ} →
      Rule37ParserWitnessNat m n proof-code formula-code →
      (m ≤ proof-code) × (n ≤ proof-code)

rule37ParserSearchCorrect-from-hit-bridges :
  Rule37ParserSearchSemantics →
  Rule37ParserWitnessHitBridge Rule37ParserWitnessExists →
  Rule37ParserWitnessHitSoundBridge Rule37ParserWitnessExists →
  Rule37ParserSearchCorrect
rule37ParserSearchCorrect-from-hit-bridges S complete-bridge sound-bridge =
  record
    { parser-search-semantics =
        S
    ; parser-search-complete =
        λ {proof-code} {formula-code} witness →
          rule37ParserSearch-complete-from-hit-bridge
            S
            complete-bridge
            {proof-code}
            {formula-code}
            witness
    ; parser-search-sound =
        λ {proof-code} {formula-code} holds →
          rule37ParserSearch-sound-from-hit-bridge
            S
            sound-bridge
            {proof-code}
            {formula-code}
            holds
    }
