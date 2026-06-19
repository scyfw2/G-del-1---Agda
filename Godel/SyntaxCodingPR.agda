{-# OPTIONS --safe #-}

module Godel.SyntaxCodingPR where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.PACheckedGraphRelations
open import Godel.ComputableGraphs

binaryArgs : ℕ → ℕ → Vec ℕ (suc (suc zero))
binaryArgs x y = x ∷ y ∷ []

ternaryArgs : ℕ → ℕ → ℕ → Vec ℕ (suc (suc (suc zero)))
ternaryArgs x y z = x ∷ y ∷ z ∷ []

-- This record is the honest bridge still needed between the executable Agda
-- checkers and the primitive-recursive representability theorem.
record SyntaxCodingPR : Set₁ where
  field
    decodeTermPR    : PRRel (suc (suc zero))
    decodeFormulaPR : PRRel (suc (suc zero))
    formulaEqPR     : PRRel (suc (suc zero))
    subst0PR        : PRRel (suc (suc (suc zero)))
    diagPR          : PRRel (suc (suc zero))

    decodeTermPR-complete :
      {input-code output-code : ℕ} →
      DecodeTermNatCode input-code output-code →
      PRRel-holds decodeTermPR (binaryArgs input-code output-code)

    decodeTermPR-sound :
      {input-code output-code : ℕ} →
      PRRel-holds decodeTermPR (binaryArgs input-code output-code) →
      DecodeTermNatCode input-code output-code

    decodeFormulaPR-complete :
      {input-code output-code : ℕ} →
      DecodeFormulaNatCode input-code output-code →
      PRRel-holds decodeFormulaPR (binaryArgs input-code output-code)

    decodeFormulaPR-sound :
      {input-code output-code : ℕ} →
      PRRel-holds decodeFormulaPR (binaryArgs input-code output-code) →
      DecodeFormulaNatCode input-code output-code

    formulaEqPR-complete :
      {left-code right-code : ℕ} →
      FormulaEqNatCode left-code right-code →
      PRRel-holds formulaEqPR (binaryArgs left-code right-code)

    formulaEqPR-sound :
      {left-code right-code : ℕ} →
      PRRel-holds formulaEqPR (binaryArgs left-code right-code) →
      FormulaEqNatCode left-code right-code

    subst0PR-complete :
      {formula-code term-code output-code : ℕ} →
      DecodedSubst0NatCode formula-code term-code output-code →
      PRRel-holds subst0PR
        (ternaryArgs formula-code term-code output-code)

    subst0PR-sound :
      {formula-code term-code output-code : ℕ} →
      PRRel-holds subst0PR
        (ternaryArgs formula-code term-code output-code) →
      DecodedSubst0NatCode formula-code term-code output-code

    diagPR-complete :
      {input-code output-code : ℕ} →
      DecodedDiagNatCode input-code output-code →
      PRRel-holds diagPR (binaryArgs input-code output-code)

    diagPR-sound :
      {input-code output-code : ℕ} →
      PRRel-holds diagPR (binaryArgs input-code output-code) →
      DecodedDiagNatCode input-code output-code
