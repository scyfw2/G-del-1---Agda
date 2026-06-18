{-# OPTIONS --safe #-}

module Godel.NoProofsDiagonalization where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.Coding
open import Godel.CanonicalCoding
open import Godel.DiagonalCoding

-- The noProofs-specific diagonalization route starts from the same template
-- consumed by Godel.Original:
--   ψ(x) := ∀p. ¬ Proof(p,x)
--
-- We keep this stage at the meta level.  DiagRel is the future
-- object-language target for representing the graph below, but this module
-- does not yet prove that PA represents it.
noProofsDiagonalTemplate : Formula
noProofsDiagonalTemplate = noProofsTemplate

noProofsFixedPointCandidate : Formula
noProofsFixedPointCandidate = diagFormula noProofsDiagonalTemplate

noProofsFixedPointCandidate-eq :
  noProofsFixedPointCandidate ≡ diagFormula noProofsDiagonalTemplate
noProofsFixedPointCandidate-eq = refl

noProofsCandidate-diagNatCode :
  DiagNatCode
    (canonicalNatFormula noProofsDiagonalTemplate)
    (canonicalNatFormula noProofsFixedPointCandidate)
noProofsCandidate-diagNatCode =
  diagNatCode-complete noProofsDiagonalTemplate
