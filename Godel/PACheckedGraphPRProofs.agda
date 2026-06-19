{-# OPTIONS --safe #-}

module Godel.PACheckedGraphPRProofs where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.PrimitiveRecursive
open import Godel.PRRepresentability
open import Godel.PAObjectLogicProofs
open import Godel.PACheckedGraphRelations
open import Godel.ComputableGraphs
open import Godel.SyntaxCodingPR
open import Godel.PACheckedGraphPRTargets

termBinaryArgs : Term → Term → Vec Term (suc (suc zero))
termBinaryArgs x y = x ∷ y ∷ []

termTernaryArgs : Term → Term → Term → Vec Term (suc (suc (suc zero)))
termTernaryArgs x y z = x ∷ y ∷ z ∷ []

record PACheckedGraphPRInputs : Set₁ where
  field
    syntax-coding-pr : SyntaxCodingPR

    decodeTerm-represented :
      PARepresentsRelation (SyntaxCodingPR.decodeTermPR syntax-coding-pr)

    decodeFormula-represented :
      PARepresentsRelation (SyntaxCodingPR.decodeFormulaPR syntax-coding-pr)

    formulaEq-represented :
      PARepresentsRelation (SyntaxCodingPR.formulaEqPR syntax-coding-pr)

    subst0-represented :
      PARepresentsRelation (SyntaxCodingPR.subst0PR syntax-coding-pr)

    diag-represented :
      PARepresentsRelation (SyntaxCodingPR.diagPR syntax-coding-pr)

paCheckedGraphPRFormulas :
  PACheckedGraphPRInputs →
  PACheckedGraphPRFormulas
paCheckedGraphPRFormulas D = record
  { DecodeTermFormula = λ x y →
      PARepresentsRelation.relationFormula
        (PACheckedGraphPRInputs.decodeTerm-represented D)
        (termBinaryArgs x y)
  ; DecodeFormulaFormula = λ x y →
      PARepresentsRelation.relationFormula
        (PACheckedGraphPRInputs.decodeFormula-represented D)
        (termBinaryArgs x y)
  ; FormulaEqFormula = λ x y →
      PARepresentsRelation.relationFormula
        (PACheckedGraphPRInputs.formulaEq-represented D)
        (termBinaryArgs x y)
  ; Subst0Formula = λ x y z →
      PARepresentsRelation.relationFormula
        (PACheckedGraphPRInputs.subst0-represented D)
        (termTernaryArgs x y z)
  ; DiagFormula = λ x y →
      PARepresentsRelation.relationFormula
        (PACheckedGraphPRInputs.diag-represented D)
        (termBinaryArgs x y)
  }

paDecodePRRepresentability :
  (D : PACheckedGraphPRInputs) →
  PADecodePRRepresentability (paCheckedGraphPRFormulas D)
paDecodePRRepresentability D = record
  { pa-decode-term-true = λ {x} {y} decoded →
      PARepresentsRelation.represents-true
        (PACheckedGraphPRInputs.decodeTerm-represented D)
        (binaryArgs x y)
        (SyntaxCodingPR.decodeTermPR-complete
          (PACheckedGraphPRInputs.syntax-coding-pr D)
          decoded)
  ; pa-decode-term-false = λ x y not-decoded →
      PARepresentsRelation.represents-false
        (PACheckedGraphPRInputs.decodeTerm-represented D)
        (binaryArgs x y)
        (λ pr-holds →
          not-decoded
            (SyntaxCodingPR.decodeTermPR-sound
              (PACheckedGraphPRInputs.syntax-coding-pr D)
              pr-holds))
  ; pa-decode-formula-true = λ {x} {y} decoded →
      PARepresentsRelation.represents-true
        (PACheckedGraphPRInputs.decodeFormula-represented D)
        (binaryArgs x y)
        (SyntaxCodingPR.decodeFormulaPR-complete
          (PACheckedGraphPRInputs.syntax-coding-pr D)
          decoded)
  ; pa-decode-formula-false = λ x y not-decoded →
      PARepresentsRelation.represents-false
        (PACheckedGraphPRInputs.decodeFormula-represented D)
        (binaryArgs x y)
        (λ pr-holds →
          not-decoded
            (SyntaxCodingPR.decodeFormulaPR-sound
              (PACheckedGraphPRInputs.syntax-coding-pr D)
              pr-holds))
  }

paFormulaEqPRRepresentability :
  (D : PACheckedGraphPRInputs) →
  PAFormulaEqPRRepresentability (paCheckedGraphPRFormulas D)
paFormulaEqPRRepresentability D = record
  { pa-formulaEq-true = λ {x} {y} eq-code →
      PARepresentsRelation.represents-true
        (PACheckedGraphPRInputs.formulaEq-represented D)
        (binaryArgs x y)
        (SyntaxCodingPR.formulaEqPR-complete
          (PACheckedGraphPRInputs.syntax-coding-pr D)
          eq-code)
  ; pa-formulaEq-false = λ x y not-eq-code →
      PARepresentsRelation.represents-false
        (PACheckedGraphPRInputs.formulaEq-represented D)
        (binaryArgs x y)
        (λ pr-holds →
          not-eq-code
            (SyntaxCodingPR.formulaEqPR-sound
              (PACheckedGraphPRInputs.syntax-coding-pr D)
              pr-holds))
  }

paSubst0PRRepresentability :
  (D : PACheckedGraphPRInputs) →
  PASubst0PRRepresentability (paCheckedGraphPRFormulas D)
paSubst0PRRepresentability D = record
  { pa-subst0-decoded-true = λ {x} {y} {z} decoded →
      PARepresentsRelation.represents-true
        (PACheckedGraphPRInputs.subst0-represented D)
        (ternaryArgs x y z)
        (SyntaxCodingPR.subst0PR-complete
          (PACheckedGraphPRInputs.syntax-coding-pr D)
          decoded)
  ; pa-subst0-decoded-false = λ x y z not-decoded →
      PARepresentsRelation.represents-false
        (PACheckedGraphPRInputs.subst0-represented D)
        (ternaryArgs x y z)
        (λ pr-holds →
          not-decoded
            (SyntaxCodingPR.subst0PR-sound
              (PACheckedGraphPRInputs.syntax-coding-pr D)
              pr-holds))
  }

paDiagPRRepresentability :
  (D : PACheckedGraphPRInputs) →
  PADiagPRRepresentability (paCheckedGraphPRFormulas D)
paDiagPRRepresentability D = record
  { pa-diag-decoded-true = λ {x} {y} decoded →
      PARepresentsRelation.represents-true
        (PACheckedGraphPRInputs.diag-represented D)
        (binaryArgs x y)
        (SyntaxCodingPR.diagPR-complete
          (PACheckedGraphPRInputs.syntax-coding-pr D)
          decoded)
  ; pa-diag-decoded-false = λ x y not-decoded →
      PARepresentsRelation.represents-false
        (PACheckedGraphPRInputs.diag-represented D)
        (binaryArgs x y)
        (λ pr-holds →
          not-decoded
            (SyntaxCodingPR.diagPR-sound
              (PACheckedGraphPRInputs.syntax-coding-pr D)
              pr-holds))
  }

paCheckedGraphPRProofData :
  (D : PACheckedGraphPRInputs) →
  PACheckedGraphPRProofData (paCheckedGraphPRFormulas D)
paCheckedGraphPRProofData D = record
  { proof-infrastructure = paProofInfrastructure
  ; decode-representability = paDecodePRRepresentability D
  ; formulaEq-representability = paFormulaEqPRRepresentability D
  ; subst0-representability = paSubst0PRRepresentability D
  ; diag-representability = paDiagPRRepresentability D
  }

paCheckedGraphPRRepresentability :
  (D : PACheckedGraphPRInputs) →
  PACheckedGraphPRRepresentability (paCheckedGraphPRFormulas D)
paCheckedGraphPRRepresentability D =
  checkedGraphPRProofData-to-PRRepresentability
    (paCheckedGraphPRProofData D)
