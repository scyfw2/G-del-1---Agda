{-# OPTIONS --safe #-}

module Godel.DiagonalCoding where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List using ([]; _∷_)
open import Godel.Core
open import Godel.Syntax
open import Godel.CanonicalCoding

-- Meta-level graph predicates for the canonical numeric syntax coding.
-- These are representability targets for a future object-language treatment;
-- they are not PA proofs yet.
CanonicalTermCode : ℕ → Set
CanonicalTermCode n = Σ Term (λ t → n ≡ canonicalNatTerm t)

CanonicalFormulaCode : ℕ → Set
CanonicalFormulaCode n = Σ Formula (λ A → n ≡ canonicalNatFormula A)

Subst0NatCode : ℕ → ℕ → ℕ → Set
Subst0NatCode formula-code term-code output-code =
  Σ Formula (λ A →
  Σ Term (λ t →
    (formula-code ≡ canonicalNatFormula A) ×
    ((term-code ≡ canonicalNatTerm t) ×
     (output-code ≡ canonicalNatFormula (subst0 t A)))))

DiagNatCode : ℕ → ℕ → Set
DiagNatCode input-code output-code =
  Σ Formula (λ A →
    (input-code ≡ canonicalNatFormula A) ×
    (output-code ≡ canonicalNatFormula (diagFormula A)))

canonicalTermCode-complete :
  (t : Term) → CanonicalTermCode (canonicalNatTerm t)
canonicalTermCode-complete t = t ,Σ refl

canonicalFormulaCode-complete :
  (A : Formula) → CanonicalFormulaCode (canonicalNatFormula A)
canonicalFormulaCode-complete A = A ,Σ refl

subst0NatCode-complete :
  (A : Formula) → (t : Term) →
  Subst0NatCode
    (canonicalNatFormula A)
    (canonicalNatTerm t)
    (canonicalNatFormula (subst0 t A))
subst0NatCode-complete A t =
  A ,Σ t ,Σ refl ,× refl ,× refl

diagNatCode-complete :
  (A : Formula) →
  DiagNatCode
    (canonicalNatFormula A)
    (canonicalNatFormula (diagFormula A))
diagNatCode-complete A = A ,Σ refl ,× refl

subst0RelSymbol : ℕ
subst0RelSymbol = suc diagRelSymbol

Subst0Rel : Term → Term → Term → Formula
Subst0Rel formula-code term-code output-code =
  Rel subst0RelSymbol (formula-code ∷ term-code ∷ output-code ∷ [])
