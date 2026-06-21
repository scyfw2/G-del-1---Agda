{-# OPTIONS --safe #-}

module Godel.ProofRule37ParserSearchSound where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.ProofCheckingPR using (proofCodeArgs)
open import Godel.PrimitiveRecursive using (evalPRF)
open import Godel.ProofRuleTargets using (rule37WitnessArgs)
open import Godel.ProofRule37ParserWitness
  using
    ( rule37ParserWitnessF
    ; rule37ParserWitness-nonzero-sound
    )
open import Godel.ProofRule37ParserSearch
  using
    ( Rule37ParserSearchSemantics
    ; Rule37ParserWitnessExists
    ; rule37ParserSearchF
    ; rule37ParserSearchMMeta
    )
open import Godel.ProofRule37SearchCorrectness
  using
    ( Search2BoundedNonzero
    ; search2UpTo
    ; search2UpTo-sound-one
    )

-- A specialized soundness bridge for the parser-backed rule-37 search.
--
-- This avoids the generic hit-interface record while proving the concrete
-- soundness half.  The direct bounded-hit predicate mentions the parser
-- witness checker itself, which keeps the final conversion to
-- Rule37ParserWitnessExists small.

rule37ParserWitnessDirectValue :
  ℕ → ℕ → ℕ → ℕ → ℕ
rule37ParserWitnessDirectValue m n proof-code formula-code =
  evalPRF
    rule37ParserWitnessF
    (rule37WitnessArgs m n proof-code formula-code)

Rule37ParserWitnessDirectBoundedNonzero :
  ℕ → ℕ → Set
Rule37ParserWitnessDirectBoundedNonzero proof-code formula-code =
  Search2BoundedNonzero
    (λ m n → rule37ParserWitnessDirectValue m n proof-code formula-code)
    proof-code
    proof-code

rule37ParserSearchMMeta-as-direct-search2 :
  (proof-code formula-code : ℕ) →
  rule37ParserSearchMMeta proof-code proof-code formula-code ≡
  search2UpTo
    (λ m n → rule37ParserWitnessDirectValue m n proof-code formula-code)
    proof-code
    proof-code
rule37ParserSearchMMeta-as-direct-search2 proof-code formula-code =
  refl

rule37ParserSearch-sound-direct-bounded-nonzero :
  Rule37ParserSearchSemantics →
  {proof-code formula-code : ℕ} →
  evalPRF
    rule37ParserSearchF
    (proofCodeArgs proof-code formula-code)
  ≡ suc zero →
  Rule37ParserWitnessDirectBoundedNonzero proof-code formula-code
rule37ParserSearch-sound-direct-bounded-nonzero
    S {proof-code} {formula-code} search-holds
  rewrite Rule37ParserSearchSemantics.parser-search-f-correct
            S
            proof-code
            formula-code
        | rule37ParserSearchMMeta-as-direct-search2
            proof-code
            formula-code =
  search2UpTo-sound-one proof-code proof-code search-holds

rule37Parser-direct-bounded-nonzero-to-witness-exists :
  {proof-code formula-code : ℕ} →
  Rule37ParserWitnessDirectBoundedNonzero proof-code formula-code →
  Rule37ParserWitnessExists proof-code formula-code
rule37Parser-direct-bounded-nonzero-to-witness-exists
    {proof-code}
    {formula-code}
    (m ,Σ (n ,Σ ((_ ,× _) ,× nonzero))) =
  m ,Σ
    (n ,Σ
      rule37ParserWitness-nonzero-sound
        {m = m}
        {n = n}
        {proof-code = proof-code}
        {formula-code = formula-code}
        nonzero)

rule37ParserSearch-sound-direct :
  Rule37ParserSearchSemantics →
  {proof-code formula-code : ℕ} →
  evalPRF
    rule37ParserSearchF
    (proofCodeArgs proof-code formula-code)
  ≡ suc zero →
  Rule37ParserWitnessExists proof-code formula-code
rule37ParserSearch-sound-direct
    S {proof-code} {formula-code} search-holds =
  rule37Parser-direct-bounded-nonzero-to-witness-exists
    {proof-code = proof-code}
    {formula-code = formula-code}
    (rule37ParserSearch-sound-direct-bounded-nonzero
      S
      {proof-code = proof-code}
      {formula-code = formula-code}
      search-holds)
