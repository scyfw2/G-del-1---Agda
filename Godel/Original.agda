{-# OPTIONS --safe #-}

module Godel.Original where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.Coding
open import Godel.ArithmetizedTheory
open import Godel.Diagonal

module Theorem (T : ArithmetizedTheory) (D : GödelSentence T) where
  open ArithmetizedTheory T
  open GödelSentence D

  -- If T is consistent, its Gödel sentence is not provable.
  not-provable-G : Consistent T → ¬ (Provable G)
  not-provable-G cons pG =
    cons proof-nG no-proof-nG
    where
      code-of-pG : Σ ℕ (λ n → ProofCode n G)
      code-of-pG = proofCode-complete pG

      n : ℕ
      n = fstΣ code-of-pG

      n-codes-pG : ProofCode n G
      n-codes-pG = sndΣ code-of-pG

      proof-nG : Provable (ProofOf (numeral n) G)
      proof-nG = represents-proof n-codes-pG

      all-no-proofs : Provable (noProofs G)
      all-no-proofs = mp g→noProofs pG

      raw-no-proof-nG : Provable (subst0 (numeral n) (¬ᶠ (ProofOf (var zero) G)))
      raw-no-proof-nG = all-elim n all-no-proofs

      no-proof-nG : Provable (¬ᶠ (ProofOf (numeral n) G))
      no-proof-nG = provable-cong (notProofOf-subst0 n G) raw-no-proof-nG

  -- If T is consistent and ω-consistent, the negation of its Gödel sentence
  -- is not provable.
  not-provable-notG : Consistent T → OmegaConsistent T → ¬ (Provable (¬ᶠ G))
  not-provable-notG cons omega pNotG =
    omega some-proof every-number-is-not-a-proof
    where
      P : Formula
      P = ProofOf (var zero) G

      some-proof : Provable (∃ᶠ P)
      some-proof = mp notG→someProof pNotG

      every-number-is-not-a-proof : (k : ℕ) → Provable (¬ᶠ (subst0 (numeral k) P))
      every-number-is-not-a-proof k =
        provable-cong (sym (cong ¬ᶠ_ (ProofOf-subst0 k G))) represented-no-proof
        where
          no-real-code : ¬ (ProofCode k G)
          no-real-code k-codes-G = cons (proofCode-sound k-codes-G) pNotG

          represented-no-proof : Provable (¬ᶠ (ProofOf (numeral k) G))
          represented-no-proof = represents-nonProof k no-real-code

  -- Gödel's first incompleteness theorem, original ω-consistency version.
  first-incompleteness : Consistent T → OmegaConsistent T → Undecidable T G
  first-incompleteness cons omega =
    not-provable-G cons ,× not-provable-notG cons omega

-- Direct theorem from a diagonal lemma.
module FromDiagonal (T : ArithmetizedTheory) (DL : DiagonalLemma T) where
  GSentence : GödelSentence T
  GSentence = fromFixedPoint (gödelFixedPoint DL)

  open Theorem T GSentence public

-- Direct theorem from the weaker fixed-point interface actually used here.
module FromNoProofsFixedPoint (T : ArithmetizedTheory) (N : NoProofsFixedPoint T) where
  GSentence : GödelSentence T
  GSentence = fromNoProofsFixedPoint N

  open Theorem T GSentence public
