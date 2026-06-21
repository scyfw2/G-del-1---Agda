{-# OPTIONS --safe #-}

module Godel.ProofRule37SearchHit where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.PrimitiveRecursive using (evalPRF)
open import Godel.ProofCheckingPR using (proofCodeArgs)
open import Godel.ProofRule37Search
  using
    ( rule37SearchF
    ; rule37SearchF-correct
    ; rule37SearchMMeta
    )
open import Godel.ProofRule37SearchCorrectness
  using
    ( NonzeroNat
    ; Search2BoundedHit
    ; Search2BoundedNonzero
    ; search2UpTo
    ; search2UpTo-hit-bound
    ; search2UpTo-nonzero-sound
    ; search2UpTo-sound-one
    )

-- Completeness for the concrete rule-37 bounded search factors through this
-- thin interface.  The interface avoids mentioning the large rule37WitnessF
-- in the bounded-search proof itself; later work only has to instantiate
-- witness-hit-value and prove it agrees with the actual witness checker.

record Rule37SearchHitInterface : Set₁ where
  field
    witness-hit-value : ℕ → ℕ → ℕ → ℕ → ℕ

    search-meta-as-hit-search2 :
      (proof-code formula-code : ℕ) →
      rule37SearchMMeta proof-code proof-code formula-code ≡
      search2UpTo
        (λ m n → witness-hit-value m n proof-code formula-code)
        proof-code
        proof-code

Rule37WitnessBoundedHit :
  Rule37SearchHitInterface → ℕ → ℕ → Set
Rule37WitnessBoundedHit I proof-code formula-code =
  Search2BoundedHit
    (λ m n →
      Rule37SearchHitInterface.witness-hit-value
        I
        m
        n
        proof-code
        formula-code)
    proof-code
    proof-code

Rule37WitnessBoundedNonzero :
  Rule37SearchHitInterface → ℕ → ℕ → Set
Rule37WitnessBoundedNonzero I proof-code formula-code =
  Search2BoundedNonzero
    (λ m n →
      Rule37SearchHitInterface.witness-hit-value
        I
        m
        n
        proof-code
        formula-code)
    proof-code
    proof-code

rule37Search-complete-bounded-hit :
  (I : Rule37SearchHitInterface) →
  {proof-code formula-code : ℕ} →
  Rule37WitnessBoundedHit I proof-code formula-code →
  evalPRF rule37SearchF (proofCodeArgs proof-code formula-code) ≡
  suc zero
rule37Search-complete-bounded-hit I {proof-code} {formula-code} hit
  rewrite rule37SearchF-correct proof-code formula-code
        | Rule37SearchHitInterface.search-meta-as-hit-search2
            I
            proof-code
            formula-code =
  search2UpTo-hit-bound hit

rule37Search-sound-bounded-hit :
  (I : Rule37SearchHitInterface) →
  {proof-code formula-code : ℕ} →
  evalPRF rule37SearchF (proofCodeArgs proof-code formula-code) ≡
  suc zero →
  Rule37WitnessBoundedNonzero I proof-code formula-code
rule37Search-sound-bounded-hit I {proof-code} {formula-code} search-holds
  rewrite rule37SearchF-correct proof-code formula-code
        | Rule37SearchHitInterface.search-meta-as-hit-search2
            I
            proof-code
            formula-code =
  search2UpTo-sound-one proof-code proof-code search-holds

rule37Search-sound-bounded-nonzero :
  (I : Rule37SearchHitInterface) →
  {proof-code formula-code : ℕ} →
  NonzeroNat (evalPRF rule37SearchF (proofCodeArgs proof-code formula-code)) →
  Rule37WitnessBoundedNonzero I proof-code formula-code
rule37Search-sound-bounded-nonzero I {proof-code} {formula-code} search-nonzero
  rewrite rule37SearchF-correct proof-code formula-code
        | Rule37SearchHitInterface.search-meta-as-hit-search2
            I
            proof-code
            formula-code =
  search2UpTo-nonzero-sound proof-code proof-code search-nonzero

record Rule37WitnessHitBridge
    (WitnessExists : ℕ → ℕ → Set) : Set₁ where
  field
    hit-interface : Rule37SearchHitInterface

    witness-exists-to-bounded-hit :
      {proof-code formula-code : ℕ} →
      WitnessExists proof-code formula-code →
      Rule37WitnessBoundedHit
        hit-interface
        proof-code
        formula-code

rule37Search-complete-from-hit-bridge :
  {WitnessExists : ℕ → ℕ → Set} →
  Rule37WitnessHitBridge WitnessExists →
  {proof-code formula-code : ℕ} →
  WitnessExists proof-code formula-code →
  evalPRF rule37SearchF (proofCodeArgs proof-code formula-code) ≡
  suc zero
rule37Search-complete-from-hit-bridge bridge witness =
  rule37Search-complete-bounded-hit
    (Rule37WitnessHitBridge.hit-interface bridge)
    (Rule37WitnessHitBridge.witness-exists-to-bounded-hit bridge witness)

record Rule37WitnessHitSoundBridge
    (WitnessExists : ℕ → ℕ → Set) : Set₁ where
  field
    hit-interface : Rule37SearchHitInterface

    bounded-nonzero-to-witness :
      {proof-code formula-code : ℕ} →
      Rule37WitnessBoundedNonzero
        hit-interface
        proof-code
        formula-code →
      WitnessExists proof-code formula-code

rule37Search-sound-from-hit-bridge :
  {WitnessExists : ℕ → ℕ → Set} →
  Rule37WitnessHitSoundBridge WitnessExists →
  {proof-code formula-code : ℕ} →
  evalPRF rule37SearchF (proofCodeArgs proof-code formula-code) ≡
  suc zero →
  WitnessExists proof-code formula-code
rule37Search-sound-from-hit-bridge bridge search-holds =
  Rule37WitnessHitSoundBridge.bounded-nonzero-to-witness
    bridge
    (rule37Search-sound-bounded-hit
      (Rule37WitnessHitSoundBridge.hit-interface bridge)
      search-holds)

rule37Search-nonzero-sound-from-hit-bridge :
  {WitnessExists : ℕ → ℕ → Set} →
  Rule37WitnessHitSoundBridge WitnessExists →
  {proof-code formula-code : ℕ} →
  NonzeroNat (evalPRF rule37SearchF (proofCodeArgs proof-code formula-code)) →
  WitnessExists proof-code formula-code
rule37Search-nonzero-sound-from-hit-bridge bridge search-nonzero =
  Rule37WitnessHitSoundBridge.bounded-nonzero-to-witness
    bridge
    (rule37Search-sound-bounded-nonzero
      (Rule37WitnessHitSoundBridge.hit-interface bridge)
      search-nonzero)
