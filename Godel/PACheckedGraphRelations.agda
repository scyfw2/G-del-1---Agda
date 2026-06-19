{-# OPTIONS --safe #-}

module Godel.PACheckedGraphRelations where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Maybe using (just)
open import Godel.Core
open import Godel.Syntax
open import Godel.CanonicalCoding
open import Godel.DecidableCoding

DecodeTermNatCode : ℕ → ℕ → Set
DecodeTermNatCode input-code output-code =
  Σ Term (λ t →
    (decodeNatTerm input-code ≡ just t) ×
    (output-code ≡ canonicalNatTerm t))

DecodeFormulaNatCode : ℕ → ℕ → Set
DecodeFormulaNatCode input-code output-code =
  Σ Formula (λ A →
    (decodeNatFormula input-code ≡ just A) ×
    (output-code ≡ canonicalNatFormula A))

TermEqNatCode : ℕ → ℕ → Set
TermEqNatCode left-code right-code =
  Σ Term (λ s →
  Σ Term (λ t →
    (decodeNatTerm left-code ≡ just s) ×
    ((decodeNatTerm right-code ≡ just t) ×
     (termEq s t ≡ true))))

FormulaEqNatCode : ℕ → ℕ → Set
FormulaEqNatCode left-code right-code =
  Σ Formula (λ A →
  Σ Formula (λ B →
    (decodeNatFormula left-code ≡ just A) ×
    ((decodeNatFormula right-code ≡ just B) ×
     (formulaEq A B ≡ true))))
