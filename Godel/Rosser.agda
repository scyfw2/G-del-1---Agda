{-# OPTIONS --safe #-}

module Godel.Rosser where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.ArithmetizedTheory

-- A Rosser sentence interface.  The hard Rosser construction is packaged as
-- two extraction principles: a proof of R yields a proof-code of ¬R, and a
-- proof of ¬R yields a proof-code of R.  Consistency then forbids both.
record RosserSentence (T : ArithmetizedTheory) : Set where
  open ArithmetizedTheory T
  field
    R : Formula
    proof-R-gives-refutation : Provable R → Σ ℕ (λ n → ProofCode n (¬ᶠ R))
    refutation-gives-proof-R : Provable (¬ᶠ R) → Σ ℕ (λ n → ProofCode n R)

module Theorem (T : ArithmetizedTheory) (D : RosserSentence T) where
  open ArithmetizedTheory T
  open RosserSentence D

  not-provable-R : Consistent T → ¬ (Provable R)
  not-provable-R cons pR =
    cons pR pNotR
    where
      code-of-notR : Σ ℕ (λ n → ProofCode n (¬ᶠ R))
      code-of-notR = proof-R-gives-refutation pR

      pNotR : Provable (¬ᶠ R)
      pNotR = proofCode-sound (sndΣ code-of-notR)

  not-provable-notR : Consistent T → ¬ (Provable (¬ᶠ R))
  not-provable-notR cons pNotR =
    cons pR pNotR
    where
      code-of-R : Σ ℕ (λ n → ProofCode n R)
      code-of-R = refutation-gives-proof-R pNotR

      pR : Provable R
      pR = proofCode-sound (sndΣ code-of-R)

  first-incompleteness-rosser : Consistent T → Undecidable T R
  first-incompleteness-rosser cons =
    not-provable-R cons ,× not-provable-notR cons
