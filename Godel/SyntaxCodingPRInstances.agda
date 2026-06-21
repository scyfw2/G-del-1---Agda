{-# OPTIONS --safe #-}

module Godel.SyntaxCodingPRInstances where

open import Godel.SyntaxCodingPR
open import Godel.PRRepresentabilityFinal
open import Godel.PACheckedGraphPRProofs

record SyntaxCodingPRInstanceData : Set₁ where
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

syntaxCodingPRInstance-to-checkedGraphInputs :
  SyntaxCodingPRInstanceData →
  PACheckedGraphPRInputs
syntaxCodingPRInstance-to-checkedGraphInputs D = record
  { syntax-coding-pr = SyntaxCodingPRInstanceData.syntax-coding-pr D
  ; decodeTerm-represented =
      SyntaxCodingPRInstanceData.decodeTerm-represented D
  ; decodeFormula-represented =
      SyntaxCodingPRInstanceData.decodeFormula-represented D
  ; formulaEq-represented =
      SyntaxCodingPRInstanceData.formulaEq-represented D
  ; subst0-represented =
      SyntaxCodingPRInstanceData.subst0-represented D
  ; diag-represented =
      SyntaxCodingPRInstanceData.diag-represented D
  }
