{-# OPTIONS --safe #-}

module Godel.SyntaxCodingPRDerived where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.PrimitiveRecursive

-- The previous concrete checker definitions depended on special evalPRF
-- cases.  Those evaluator cases have been removed, so these names are kept as
-- minimal-basis placeholders until the numeric PR decoder/checker layer is
-- rebuilt.

validTermCodeF : PRF (suc (suc zero))
validTermCodeF = zeroF

validFormulaCodeF : PRF (suc (suc zero))
validFormulaCodeF = zeroF

termEqCodeF : PRF (suc (suc zero))
termEqCodeF = zeroF

formulaEqCodeF : PRF (suc (suc zero))
formulaEqCodeF = zeroF

subst0CodeF : PRF (suc (suc (suc zero)))
subst0CodeF = zeroF

diagCodeF : PRF (suc (suc zero))
diagCodeF = zeroF
