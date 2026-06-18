{-# OPTIONS --safe #-}

module Godel.Diagonal where

open import Godel.Core
open import Godel.Syntax
open import Godel.Coding
open import Godel.ArithmetizedTheory

-- A fixed point of a one-free-variable formula φ is a sentence θ such that
-- the theory proves θ <-> φ(⌜θ⌝).
record FixedPoint (T : ArithmetizedTheory) (φ : Formula) : Set where
  open ArithmetizedTheory T
  field
    θ     : Formula
    θ⇒φθ  : Provable (θ ⇒ subst0 (⌜ θ ⌝ᶠ) φ)
    φθ⇒θ  : Provable (subst0 (⌜ θ ⌝ᶠ) φ ⇒ θ)

-- The diagonal/fixed-point lemma, packaged as an interface.
-- Instantiating this for PA/Q requires the usual representability of the
-- syntactic substitution/diagonal function.
record DiagonalLemma (T : ArithmetizedTheory) : Set where
  field
    fixedPoint : (φ : Formula) → FixedPoint T φ

-- A Gödel sentence G for T has the two formal consequences used in the proof.
record GödelSentence (T : ArithmetizedTheory) : Set where
  open ArithmetizedTheory T
  field
    G : Formula
    g→noProofs     : Provable (G ⇒ noProofs G)
    notG→someProof : Provable ((¬ᶠ G) ⇒ someProof G)

-- The fixed point of noProofsTemplate is the usual Gödel sentence.
gödelFixedPoint : {T : ArithmetizedTheory} → DiagonalLemma T → FixedPoint T noProofsTemplate
gödelFixedPoint D = DiagonalLemma.fixedPoint D noProofsTemplate

-- Convert the fixed-point lemma plus a small classical-logic principle into
-- the exact GödelSentence interface consumed by the theorem.
fromFixedPoint : {T : ArithmetizedTheory} →
                 FixedPoint T noProofsTemplate → GödelSentence T
fromFixedPoint {T} fp = record
  { G = θ
  ; g→noProofs = g→np
  ; notG→someProof = notg→sp
  }
  where
    open ArithmetizedTheory T

    θ : Formula
    θ = FixedPoint.θ fp

    template-eq : subst0 (⌜ θ ⌝ᶠ) noProofsTemplate ≡ noProofs θ
    template-eq = noProofsTemplate-subst0 θ

    g→np : Provable (θ ⇒ noProofs θ)
    g→np = provable-cong (cong (λ X → θ ⇒ X) template-eq) (FixedPoint.θ⇒φθ fp)

    np→g : Provable (noProofs θ ⇒ θ)
    np→g = provable-cong (cong (λ X → X ⇒ θ) template-eq) (FixedPoint.φθ⇒θ fp)

    notg→sp : Provable ((¬ᶠ θ) ⇒ someProof θ)
    notg→sp = mp classical-step np→g
