{-# OPTIONS --safe #-}

module Godel.SyntaxCodingPRCheckers where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.PrimitiveRecursive
open import Godel.SyntaxCodingPRDerived

decodeTermPR : PRRel (suc (suc zero))
decodeTermPR = rel validTermCodeF

decodeFormulaPR : PRRel (suc (suc zero))
decodeFormulaPR = rel validFormulaCodeF

formulaEqPR : PRRel (suc (suc zero))
formulaEqPR = rel formulaEqCodeF

subst0PR : PRRel (suc (suc (suc zero)))
subst0PR = rel subst0CodeF

diagPR : PRRel (suc (suc zero))
diagPR = rel diagCodeF
