{-# OPTIONS --safe #-}

module Godel.PACheckedGraphPRTargets where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.PA
open import Godel.PAClosedArithmetic
open import Godel.ComputableGraphs
open import Godel.PACheckedGraphRelations
open import Godel.PACheckedGraphTargets

-- Final PA-facing target shape for the primitive-recursive route.
-- Unlike the older Rel-wrapper target, these formulas are supplied explicitly;
-- the intended source is the PR representability theorem.
record PACheckedGraphPRFormulas : Set₁ where
  field
    DecodeTermFormula    : Term → Term → Formula
    DecodeFormulaFormula : Term → Term → Formula
    FormulaEqFormula     : Term → Term → Formula
    Subst0Formula        : Term → Term → Term → Formula
    DiagFormula          : Term → Term → Formula

record PADecodePRRepresentability
       (F : PACheckedGraphPRFormulas) : Set₁ where
  open PACheckedGraphPRFormulas F
  field
    pa-decode-term-true :
      {input-code output-code : ℕ} →
      DecodeTermNatCode input-code output-code →
      PA-provable
        (DecodeTermFormula (numeral input-code) (numeral output-code))

    pa-decode-term-false :
      (input-code output-code : ℕ) →
      ¬ DecodeTermNatCode input-code output-code →
      PA-provable
        (¬ᶠ (DecodeTermFormula (numeral input-code) (numeral output-code)))

    pa-decode-formula-true :
      {input-code output-code : ℕ} →
      DecodeFormulaNatCode input-code output-code →
      PA-provable
        (DecodeFormulaFormula (numeral input-code) (numeral output-code))

    pa-decode-formula-false :
      (input-code output-code : ℕ) →
      ¬ DecodeFormulaNatCode input-code output-code →
      PA-provable
        (¬ᶠ
          (DecodeFormulaFormula (numeral input-code) (numeral output-code)))

record PAFormulaEqPRRepresentability
       (F : PACheckedGraphPRFormulas) : Set₁ where
  open PACheckedGraphPRFormulas F
  field
    pa-formulaEq-true :
      {left-code right-code : ℕ} →
      FormulaEqNatCode left-code right-code →
      PA-provable
        (FormulaEqFormula (numeral left-code) (numeral right-code))

    pa-formulaEq-false :
      (left-code right-code : ℕ) →
      ¬ FormulaEqNatCode left-code right-code →
      PA-provable
        (¬ᶠ (FormulaEqFormula (numeral left-code) (numeral right-code)))

record PASubst0PRRepresentability
       (F : PACheckedGraphPRFormulas) : Set₁ where
  open PACheckedGraphPRFormulas F
  field
    pa-subst0-decoded-true :
      {formula-code term-code output-code : ℕ} →
      DecodedSubst0NatCode formula-code term-code output-code →
      PA-provable
        (Subst0Formula
          (numeral formula-code)
          (numeral term-code)
          (numeral output-code))

    pa-subst0-decoded-false :
      (formula-code term-code output-code : ℕ) →
      ¬ DecodedSubst0NatCode formula-code term-code output-code →
      PA-provable
        (¬ᶠ
          (Subst0Formula
            (numeral formula-code)
            (numeral term-code)
            (numeral output-code)))

record PADiagPRRepresentability
       (F : PACheckedGraphPRFormulas) : Set₁ where
  open PACheckedGraphPRFormulas F
  field
    pa-diag-decoded-true :
      {input-code output-code : ℕ} →
      DecodedDiagNatCode input-code output-code →
      PA-provable (DiagFormula (numeral input-code) (numeral output-code))

    pa-diag-decoded-false :
      (input-code output-code : ℕ) →
      ¬ DecodedDiagNatCode input-code output-code →
      PA-provable
        (¬ᶠ (DiagFormula (numeral input-code) (numeral output-code)))

record PACheckedGraphPRProofData
       (F : PACheckedGraphPRFormulas) : Set₁ where
  field
    proof-infrastructure        : PAProofInfrastructure
    decode-representability     : PADecodePRRepresentability F
    formulaEq-representability  : PAFormulaEqPRRepresentability F
    subst0-representability     : PASubst0PRRepresentability F
    diag-representability       : PADiagPRRepresentability F

record PACheckedGraphPRRepresentability
       (F : PACheckedGraphPRFormulas) : Set₁ where
  open PACheckedGraphPRFormulas F
  field
    pa-checked-diag-true :
      {x y : ℕ} →
      CheckedDiagNatCode x y →
      PA-provable (DiagFormula (numeral x) (numeral y))

    pa-checked-diag-false :
      (x y : ℕ) →
      ¬ CheckedDiagNatCode x y →
      PA-provable (¬ᶠ (DiagFormula (numeral x) (numeral y)))

    pa-checked-subst0-true :
      {x y z : ℕ} →
      CheckedSubst0NatCode x y z →
      PA-provable
        (Subst0Formula (numeral x) (numeral y) (numeral z))

    pa-checked-subst0-false :
      (x y z : ℕ) →
      ¬ CheckedSubst0NatCode x y z →
      PA-provable
        (¬ᶠ (Subst0Formula (numeral x) (numeral y) (numeral z)))

checkedGraphPRProofData-to-PRRepresentability :
  {F : PACheckedGraphPRFormulas} →
  PACheckedGraphPRProofData F →
  PACheckedGraphPRRepresentability F
checkedGraphPRProofData-to-PRRepresentability {F} D = record
  { pa-checked-diag-true = λ {x} {y} checked →
      PADiagPRRepresentability.pa-diag-decoded-true
        (PACheckedGraphPRProofData.diag-representability D)
        (checkedDiagNatCode-sound-decoded x y checked)
  ; pa-checked-diag-false = λ x y not-checked →
      PADiagPRRepresentability.pa-diag-decoded-false
        (PACheckedGraphPRProofData.diag-representability D)
        x y
        (λ decoded →
          not-checked (decodedDiagNatCode-to-checked x y decoded))
  ; pa-checked-subst0-true = λ {x} {y} {z} checked →
      PASubst0PRRepresentability.pa-subst0-decoded-true
        (PACheckedGraphPRProofData.subst0-representability D)
        (checkedSubst0NatCode-sound-decoded x y z checked)
  ; pa-checked-subst0-false = λ x y z not-checked →
      PASubst0PRRepresentability.pa-subst0-decoded-false
        (PACheckedGraphPRProofData.subst0-representability D)
        x y z
        (λ decoded →
          not-checked (decodedSubst0NatCode-to-checked x y z decoded))
  }
