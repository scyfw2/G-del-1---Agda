{-# OPTIONS --safe #-}

module Godel.ProofRule37ParserSearchCorrect where

open import Godel.ProofRule37ParserSearch
  using
    ( Rule37ParserSearchCorrect
    ; rule37ParserSearchSemantics
    )
open import Godel.ProofRule37ParserSearchComplete
  using (rule37ParserWitnessHitBridge)
open import Godel.ProofRule37ParserSearchHit
  using (rule37ParserSearch-complete-from-hit-bridge)
open import Godel.ProofRule37ParserSearchSound
  using (rule37ParserSearch-sound-direct)

-- Concrete complete/sound package for the parser-backed rule-37 search.
--
-- This closes the search layer for Rule37ParserWitnessExists.  It is still
-- intentionally weaker than the final ProofRule37PR branch: raw parser facts
-- must later be bridged to the canonical ClosedNumeralNeqRuleNat target used
-- by the executable proof checker.

rule37ParserSearchCorrect : Rule37ParserSearchCorrect
rule37ParserSearchCorrect = record
  { parser-search-semantics =
      rule37ParserSearchSemantics
  ; parser-search-complete =
      λ {proof-code} {formula-code} witness →
        rule37ParserSearch-complete-from-hit-bridge
          rule37ParserSearchSemantics
          rule37ParserWitnessHitBridge
          {proof-code}
          {formula-code}
          witness
  ; parser-search-sound =
      λ {proof-code} {formula-code} holds →
        rule37ParserSearch-sound-direct
          rule37ParserSearchSemantics
          {proof-code}
          {formula-code}
          holds
  }
