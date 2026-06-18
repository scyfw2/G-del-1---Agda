{-# OPTIONS --safe #-}

module Godel.PA where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Syntax
open import Godel.ProofSystem

x₀ : Term
x₀ = var zero

x₁ : Term
x₁ = var (suc zero)

-- A simple induction schema for one distinguished variable.
-- More general parameterized induction schemas can be added by weakening A
-- over extra free variables; this version is sufficient as a concrete
-- syntactic placeholder for PA-style arithmetic.
induction : Formula → Formula
induction A = ((subst0 zeroᵗ A) ∧ (∀ᶠ (A ⇒ subst0 (sucᵗ x₀) A))) ⇒ ∀ᶠ A

-- Non-logical Peano-arithmetic axioms, represented as an axiom predicate.
data PA : Formula → Set where
  pa-suc-not-zero :
    PA (∀ᶠ (¬ᶠ (sucᵗ x₀ ≈ zeroᵗ)))

  pa-suc-injective :
    PA (∀ᶠ (∀ᶠ ((sucᵗ x₁ ≈ sucᵗ x₀) ⇒ (x₁ ≈ x₀))))

  pa-add-zero :
    PA (∀ᶠ ((x₀ +ᵗ zeroᵗ) ≈ x₀))

  pa-add-suc :
    PA (∀ᶠ (∀ᶠ (((x₁ +ᵗ sucᵗ x₀) ≈ sucᵗ (x₁ +ᵗ x₀)))))

  pa-mul-zero :
    PA (∀ᶠ ((x₀ *ᵗ zeroᵗ) ≈ zeroᵗ))

  pa-mul-suc :
    PA (∀ᶠ (∀ᶠ (((x₁ *ᵗ sucᵗ x₀) ≈ ((x₁ *ᵗ x₀) +ᵗ x₁)))))

  pa-induction : (A : Formula) → PA (induction A)

PA-provable : Formula → Set
PA-provable = ProvableFrom PA
