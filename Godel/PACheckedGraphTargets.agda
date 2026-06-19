{-# OPTIONS --safe #-}

module Godel.PACheckedGraphTargets where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List using ([]; _∷_)
open import Godel.Core
open import Godel.Syntax
open import Godel.PA
open import Godel.PAClosedArithmetic
open import Godel.CanonicalCoding
open import Godel.DecidableCoding
open import Godel.DiagonalCoding
open import Godel.ComputableGraphs
open import Godel.PACheckedGraphRelations public
open import Godel.PARepresentabilityEntry

-- PA-facing helper predicates for decomposing checked graph representability.
-- These relation symbols are staging targets only; this module does not prove
-- that PA represents them.
decodeTermRelSymbol : ℕ
decodeTermRelSymbol = suc subst0RelSymbol

decodeFormulaRelSymbol : ℕ
decodeFormulaRelSymbol = suc decodeTermRelSymbol

formulaEqRelSymbol : ℕ
formulaEqRelSymbol = suc decodeFormulaRelSymbol

DecodeTermRel : Term → Term → Formula
DecodeTermRel input-code output-code =
  Rel decodeTermRelSymbol (input-code ∷ output-code ∷ [])

DecodeFormulaRel : Term → Term → Formula
DecodeFormulaRel input-code output-code =
  Rel decodeFormulaRelSymbol (input-code ∷ output-code ∷ [])

FormulaEqRel : Term → Term → Formula
FormulaEqRel left-code right-code =
  Rel formulaEqRelSymbol (left-code ∷ right-code ∷ [])

record PADecodeRepresentability : Set₁ where
  field
    pa-decode-term-true :
      {input-code output-code : ℕ} →
      DecodeTermNatCode input-code output-code →
      PA-provable
        (DecodeTermRel (numeral input-code) (numeral output-code))

    pa-decode-term-false :
      (input-code output-code : ℕ) →
      ¬ DecodeTermNatCode input-code output-code →
      PA-provable
        (¬ᶠ (DecodeTermRel (numeral input-code) (numeral output-code)))

    pa-decode-formula-true :
      {input-code output-code : ℕ} →
      DecodeFormulaNatCode input-code output-code →
      PA-provable
        (DecodeFormulaRel (numeral input-code) (numeral output-code))

    pa-decode-formula-false :
      (input-code output-code : ℕ) →
      ¬ DecodeFormulaNatCode input-code output-code →
      PA-provable
        (¬ᶠ (DecodeFormulaRel (numeral input-code) (numeral output-code)))

record PAFormulaEqRepresentability : Set₁ where
  field
    pa-formulaEq-true :
      {left-code right-code : ℕ} →
      FormulaEqNatCode left-code right-code →
      PA-provable
        (FormulaEqRel (numeral left-code) (numeral right-code))

    pa-formulaEq-false :
      (left-code right-code : ℕ) →
      ¬ FormulaEqNatCode left-code right-code →
      PA-provable
        (¬ᶠ (FormulaEqRel (numeral left-code) (numeral right-code)))

record PASubst0RepresentabilityTarget : Set₁ where
  field
    pa-subst0-decoded-true :
      {formula-code term-code output-code : ℕ} →
      DecodedSubst0NatCode formula-code term-code output-code →
      PA-provable
        (Subst0Rel
          (numeral formula-code)
          (numeral term-code)
          (numeral output-code))

    pa-subst0-decoded-false :
      (formula-code term-code output-code : ℕ) →
      ¬ DecodedSubst0NatCode formula-code term-code output-code →
      PA-provable
        (¬ᶠ
          (Subst0Rel
            (numeral formula-code)
            (numeral term-code)
            (numeral output-code)))

record PADiagRepresentabilityTarget : Set₁ where
  field
    pa-diag-decoded-true :
      {input-code output-code : ℕ} →
      DecodedDiagNatCode input-code output-code →
      PA-provable
        (DiagRel (numeral input-code) (numeral output-code))

    pa-diag-decoded-false :
      (input-code output-code : ℕ) →
      ¬ DecodedDiagNatCode input-code output-code →
      PA-provable
        (¬ᶠ (DiagRel (numeral input-code) (numeral output-code)))

record PACheckedGraphProofData : Set₁ where
  field
    proof-infrastructure        : PAProofInfrastructure
    decode-representability     : PADecodeRepresentability
    formulaEq-representability  : PAFormulaEqRepresentability
    subst0-target               : PASubst0RepresentabilityTarget
    diag-target                 : PADiagRepresentabilityTarget

decodedSubst0NatCode-to-checked :
  (formula-code term-code output-code : ℕ) →
  DecodedSubst0NatCode formula-code term-code output-code →
  CheckedSubst0NatCode formula-code term-code output-code
decodedSubst0NatCode-to-checked formula-code term-code output-code
  (A ,Σ t ,Σ B ,Σ formula-eq ,× term-eq ,× output-eq ,× B-eq)
  rewrite formula-eq | term-eq | output-eq | B-eq
        | formulaEq-refl (subst0 t A) = refl

decodedDiagNatCode-to-checked :
  (input-code output-code : ℕ) →
  DecodedDiagNatCode input-code output-code →
  CheckedDiagNatCode input-code output-code
decodedDiagNatCode-to-checked input-code output-code
  (A ,Σ B ,Σ input-eq ,× output-eq ,× B-eq)
  rewrite input-eq | output-eq | B-eq
        | formulaEq-refl (diagFormula A) = refl

checkedGraphProofData-to-PARepresentability :
  PACheckedGraphProofData →
  PACheckedGraphRepresentability
checkedGraphProofData-to-PARepresentability D = record
  { pa-checked-diag-true = λ {x} {y} checked →
      PADiagRepresentabilityTarget.pa-diag-decoded-true
        (PACheckedGraphProofData.diag-target D)
        (checkedDiagNatCode-sound-decoded x y checked)
  ; pa-checked-diag-false = λ x y not-checked →
      PADiagRepresentabilityTarget.pa-diag-decoded-false
        (PACheckedGraphProofData.diag-target D)
        x y
        (λ decoded →
          not-checked (decodedDiagNatCode-to-checked x y decoded))
  ; pa-checked-subst0-true = λ {x} {y} {z} checked →
      PASubst0RepresentabilityTarget.pa-subst0-decoded-true
        (PACheckedGraphProofData.subst0-target D)
        (checkedSubst0NatCode-sound-decoded x y z checked)
  ; pa-checked-subst0-false = λ x y z not-checked →
      PASubst0RepresentabilityTarget.pa-subst0-decoded-false
        (PACheckedGraphProofData.subst0-target D)
        x y z
        (λ decoded →
          not-checked (decodedSubst0NatCode-to-checked x y z decoded))
  }
