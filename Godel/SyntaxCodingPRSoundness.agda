{-# OPTIONS --safe #-}

module Godel.SyntaxCodingPRSoundness where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.PACheckedGraphRelations
open import Godel.ComputableGraphs
open import Godel.SyntaxCodingPR
open import Godel.SyntaxCodingPRCheckers

-- Rebuild target for the next stage.  The old proofs relied on syntax checker
-- behavior hidden in evalPRF; after removing those special cases, the concrete
-- soundness/completeness lemmas must be reconstructed from real numeric PR
-- decoders.
record SyntaxCodingPRSoundnessTarget : Set₁ where
  field
    validTermCodeF-complete :
      {input-code output-code : ℕ} →
      DecodeTermNatCode input-code output-code →
      PRRel-holds decodeTermPR (binaryArgs input-code output-code)

    validTermCodeF-sound :
      {input-code output-code : ℕ} →
      PRRel-holds decodeTermPR (binaryArgs input-code output-code) →
      DecodeTermNatCode input-code output-code

    validFormulaCodeF-complete :
      {input-code output-code : ℕ} →
      DecodeFormulaNatCode input-code output-code →
      PRRel-holds decodeFormulaPR (binaryArgs input-code output-code)

    validFormulaCodeF-sound :
      {input-code output-code : ℕ} →
      PRRel-holds decodeFormulaPR (binaryArgs input-code output-code) →
      DecodeFormulaNatCode input-code output-code

    formulaEqCodeF-complete :
      {left-code right-code : ℕ} →
      FormulaEqNatCode left-code right-code →
      PRRel-holds formulaEqPR (binaryArgs left-code right-code)

    formulaEqCodeF-sound :
      {left-code right-code : ℕ} →
      PRRel-holds formulaEqPR (binaryArgs left-code right-code) →
      FormulaEqNatCode left-code right-code

    subst0CodeF-complete :
      {formula-code term-code output-code : ℕ} →
      DecodedSubst0NatCode formula-code term-code output-code →
      PRRel-holds subst0PR (ternaryArgs formula-code term-code output-code)

    subst0CodeF-sound :
      {formula-code term-code output-code : ℕ} →
      PRRel-holds subst0PR (ternaryArgs formula-code term-code output-code) →
      DecodedSubst0NatCode formula-code term-code output-code

    diagCodeF-complete :
      {input-code output-code : ℕ} →
      DecodedDiagNatCode input-code output-code →
      PRRel-holds diagPR (binaryArgs input-code output-code)

    diagCodeF-sound :
      {input-code output-code : ℕ} →
      PRRel-holds diagPR (binaryArgs input-code output-code) →
      DecodedDiagNatCode input-code output-code
