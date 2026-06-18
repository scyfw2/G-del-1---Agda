{-# OPTIONS --safe #-}

module Godel.PAFirstIncompleteness where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.Coding
open import Godel.ProofSystem
open import Godel.PA
open import Godel.ProofCoding
open import Godel.ArithmetizedTheory
open import Godel.Diagonal
open import Godel.Original

-- The only genuinely deep PA-specific ingredients not proved in this small
-- file are the standard arithmetization/representability facts and the
-- diagonal lemma.  Everything after these fields is a formal Agda proof.
record PARepresentability : Set₁ where
  field
    represents-proof-PA : {A : Formula} → {n : ℕ} →
                          ProofCodePA n A → PA-provable (ProofOf (numeral n) A)

    represents-nonProof-PA : {A : Formula} → (n : ℕ) →
                             ¬ (ProofCodePA n A) →
                             PA-provable (¬ᶠ (ProofOf (numeral n) A))

    classical-step-PA : {A : Formula} →
                        PA-provable ((noProofs A ⇒ A) ⇒ ((¬ᶠ A) ⇒ someProof A))

-- PA, equipped with the concrete proof-code relation above and the standard
-- representability assumptions, is an ArithmetizedTheory.
PA-as-theory : PARepresentability → ArithmetizedTheory
PA-as-theory R = record
  { Provable = PA-provable
  ; provable-cong = λ eq p → subst PA-provable eq p
  ; mp = modus-ponens
  ; all-elim = λ {A} n p → modus-ponens (forall-eliminate (numeral n)) p
  ; ProofCode = ProofCodePA
  ; proofCode-complete = proofCodePA-complete
  ; proofCode-sound = proofCodePA-sound
  ; represents-proof = PARepresentability.represents-proof-PA R
  ; represents-nonProof = PARepresentability.represents-nonProof-PA R
  ; classical-step = PARepresentability.classical-step-PA R
  }

record PAIncompletenessData : Set₁ where
  field
    repr : PARepresentability
    diagonal-lemma-PA : DiagonalLemma (PA-as-theory repr)

PA-GödelSentence : (D : PAIncompletenessData) → GödelSentence (PA-as-theory (PAIncompletenessData.repr D))
PA-GödelSentence D = fromFixedPoint (gödelFixedPoint (PAIncompletenessData.diagonal-lemma-PA D))

PA-GödelFormula : PAIncompletenessData → Formula
PA-GödelFormula D = GödelSentence.G (PA-GödelSentence D)

-- Gödel's first incompleteness theorem for PA in original ω-consistency form,
-- conditional on the standard PA arithmetization and diagonalization data.
PA-first-incompleteness :
  (D : PAIncompletenessData) →
  Consistent (PA-as-theory (PAIncompletenessData.repr D)) →
  OmegaConsistent (PA-as-theory (PAIncompletenessData.repr D)) →
  Undecidable (PA-as-theory (PAIncompletenessData.repr D)) (PA-GödelFormula D)
PA-first-incompleteness D cons omega =
  M.first-incompleteness cons omega
  where
    T : ArithmetizedTheory
    T = PA-as-theory (PAIncompletenessData.repr D)

    module M = Theorem T (PA-GödelSentence D)
