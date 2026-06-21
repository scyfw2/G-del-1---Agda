{-# OPTIONS --safe #-}

module Godel.ProofRule37ParserSearchComplete where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.ProofRule37ParserBounds
  using (rule37ParserWitness-bounds)
open import Godel.ProofRule37ParserWitness
  using (rule37ParserWitness-complete)
open import Godel.ProofRule37ParserSearch
  using (Rule37ParserWitnessExists)
open import Godel.ProofRule37ParserSearchHit
  using
    ( Rule37ParserWitnessBoundedHit
    ; Rule37ParserWitnessHitBridge
    ; rule37ParserSearchHitInterface
    )

-- Completeness bridge for the parser-backed rule-37 bounded search.
--
-- A semantic parser witness already supplies concrete m,n.  The parser-bounds
-- theorem proves those witnesses lie within proof-code, and
-- rule37ParserWitness-complete proves that the searched hit predicate returns
-- 1 at exactly that pair.

rule37Parser-witness-exists-to-bounded-hit :
  {proof-code formula-code : ℕ} →
  Rule37ParserWitnessExists proof-code formula-code →
  Rule37ParserWitnessBoundedHit
    rule37ParserSearchHitInterface
    proof-code
    formula-code
rule37Parser-witness-exists-to-bounded-hit
    {proof-code}
    {formula-code}
    (m ,Σ (n ,Σ witness)) =
  m ,Σ
    (n ,Σ
      ( rule37ParserWitness-bounds
          {m = m}
          {n = n}
          {proof-code = proof-code}
          {formula-code = formula-code}
          witness
        ,×
        rule37ParserWitness-complete
          {m = m}
          {n = n}
          {proof-code = proof-code}
          {formula-code = formula-code}
          witness ))

rule37ParserWitnessHitBridge :
  Rule37ParserWitnessHitBridge Rule37ParserWitnessExists
rule37ParserWitnessHitBridge = record
  { hit-interface =
      rule37ParserSearchHitInterface
  ; witness-exists-to-bounded-hit =
      rule37Parser-witness-exists-to-bounded-hit
  }
