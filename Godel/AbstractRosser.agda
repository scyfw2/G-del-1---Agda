{-# OPTIONS --safe #-}

module Godel.AbstractRosser where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.AbstractOriginal using (FormalSystem; Consistent)

-- A Rosser sentence interface. This packages the hard Rosser fixed-point
-- construction as two extraction principles: a proof of R yields a proof
-- of ¬R, and a proof of ¬R yields a proof of R. With consistency, neither
-- can exist.
record RosserSentence (S : FormalSystem) : Set where
  open FormalSystem S
  field
    R : Formula
    proof-R-gives-refutation : Provable R → Σ ℕ (λ n → ProofCode n (¬ᶠ R))
    refutation-gives-proof-R : Provable (¬ᶠ R) → Σ ℕ (λ n → ProofCode n R)

module Theorem (S : FormalSystem) (D : RosserSentence S) where
  open FormalSystem S
  open RosserSentence D

  Undecidable : Formula → Set
  Undecidable A = (¬ (Provable A)) × (¬ (Provable (¬ᶠ A)))

  -- Rosser version: consistency alone rules out a proof of R.
  not-provable-R : Consistent S → ¬ (Provable R)
  not-provable-R cons pR =
    cons pR pNotR
    where
      code-of-notR : Σ ℕ (λ n → ProofCode n (¬ᶠ R))
      code-of-notR = proof-R-gives-refutation pR

      pNotR : Provable (¬ᶠ R)
      pNotR = proofCode-sound (sndΣ code-of-notR)

  -- Rosser version: consistency alone rules out a proof of ¬R.
  not-provable-notR : Consistent S → ¬ (Provable (¬ᶠ R))
  not-provable-notR cons pNotR =
    cons pR pNotR
    where
      code-of-R : Σ ℕ (λ n → ProofCode n R)
      code-of-R = refutation-gives-proof-R pNotR

      pR : Provable R
      pR = proofCode-sound (sndΣ code-of-R)

  first-incompleteness-rosser : Consistent S → Undecidable R
  first-incompleteness-rosser cons =
    not-provable-R cons ,× not-provable-notR cons
