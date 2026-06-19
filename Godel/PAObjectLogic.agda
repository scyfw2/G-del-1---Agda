{-# OPTIONS --safe #-}

module Godel.PAObjectLogic where

open import Godel.Syntax
open import Godel.PA

-- PA-facing object-logic and equality reasoning infrastructure.
--
-- These fields are proof obligations for a future PA development.  They are
-- intentionally not derived here from the current minimal Hilbert constructors.
record PAObjectLogic : Set₁ where
  field
    eq-refl-PA :
      (t : Term) → PA-provable (t ≈ t)

    eq-sym-PA :
      {s t : Term} → PA-provable (s ≈ t ⇒ t ≈ s)

    eq-trans-PA :
      {r s t : Term} → PA-provable (r ≈ s ⇒ (s ≈ t ⇒ r ≈ t))

    suc-cong-PA :
      {s t : Term} → PA-provable (s ≈ t ⇒ sucᵗ s ≈ sucᵗ t)

    add-cong-PA :
      {a b c d : Term} →
      PA-provable (a ≈ b ⇒ (c ≈ d ⇒ (a +ᵗ c) ≈ (b +ᵗ d)))

    mul-cong-PA :
      {a b c d : Term} →
      PA-provable (a ≈ b ⇒ (c ≈ d ⇒ (a *ᵗ c) ≈ (b *ᵗ d)))
