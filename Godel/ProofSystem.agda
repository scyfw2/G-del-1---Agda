{-# OPTIONS --safe #-}

module Godel.ProofSystem where

open import Godel.Syntax

-- A small Hilbert-style proof calculus parameterized by an axiom predicate.
-- This is deliberately minimal: enough structure to expose modus ponens,
-- universal elimination, and existential introduction used by arithmetic.
data Derives (Ax : Formula → Set) : Formula → Set where
  axiom               : {A : Formula} → Ax A → Derives Ax A

  hilbert-K           : {A B : Formula} →
                        Derives Ax (A ⇒ (B ⇒ A))

  hilbert-S           : {A B C : Formula} →
                        Derives Ax ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)))

  excluded-middle     : {A : Formula} →
                        Derives Ax (A ∨ (¬ᶠ A))

  modus-ponens        : {A B : Formula} →
                        Derives Ax (A ⇒ B) → Derives Ax A → Derives Ax B

  forall-generalize   : {A : Formula} →
                        Derives Ax A → Derives Ax (∀ᶠ A)

  forall-eliminate    : {A : Formula} → (t : Term) →
                        Derives Ax ((∀ᶠ A) ⇒ subst0 t A)

  exists-introduce    : {A : Formula} → (t : Term) →
                        Derives Ax (subst0 t A ⇒ ∃ᶠ A)

  eq-refl-rule        : (t : Term) →
                        Derives Ax (t ≈ t)

  eq-sym-rule         : {s t : Term} →
                        Derives Ax (s ≈ t ⇒ t ≈ s)

  eq-trans-rule       : {r s t : Term} →
                        Derives Ax (r ≈ s ⇒ (s ≈ t ⇒ r ≈ t))

  suc-cong-rule       : {s t : Term} →
                        Derives Ax (s ≈ t ⇒ sucᵗ s ≈ sucᵗ t)

  add-cong-rule       : {a b c d : Term} →
                        Derives Ax (a ≈ b ⇒ (c ≈ d ⇒ (a +ᵗ c) ≈ (b +ᵗ d)))

  mul-cong-rule       : {a b c d : Term} →
                        Derives Ax (a ≈ b ⇒ (c ≈ d ⇒ (a *ᵗ c) ≈ (b *ᵗ d)))

-- The object theory proves A if A is derivable from its axiom predicate.
ProvableFrom : (Formula → Set) → Formula → Set
ProvableFrom Ax A = Derives Ax A
