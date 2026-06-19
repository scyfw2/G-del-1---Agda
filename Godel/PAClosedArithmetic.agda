{-# OPTIONS --safe #-}

module Godel.PAClosedArithmetic where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Syntax
open import Godel.PA
open import Godel.PAObjectLogic

-- PA-facing arithmetic facts about closed numerals.  This is the arithmetic
-- substrate needed before proving PA represents executable checked graph
-- predicates.
record PAClosedArithmetic : Set₁ where
  field
    pa-add-computes :
      (m n : ℕ) →
      PA-provable ((numeral m +ᵗ numeral n) ≈ numeral (m + n))

    pa-mul-computes :
      (m n : ℕ) →
      PA-provable ((numeral m *ᵗ numeral n) ≈ numeral (m * n))

    pa-suc-not-zero-closed :
      (n : ℕ) →
      PA-provable (¬ᶠ (sucᵗ (numeral n) ≈ zeroᵗ))

record PAProofInfrastructure : Set₁ where
  field
    object-logic      : PAObjectLogic
    closed-arithmetic : PAClosedArithmetic
