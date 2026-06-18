{-# OPTIONS --safe #-}

module Godel.AbstractOriginal where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core

-- A deliberately abstract interface for a formal arithmetic-like theory.
-- To instantiate this with PA/Q, implement Formula, Provable, proof codes,
-- and the representability fields below.
record FormalSystem : Set₁ where
  infixr 6 _⇒_
  infix  7 ¬ᶠ_

  field
    Formula : Set

    -- Object-language connectives / quantifiers used by the argument.
    _⇒_ : Formula → Formula → Formula
    ¬ᶠ_ : Formula → Formula
    ∀ᶠ  : (ℕ → Formula) → Formula
    ∃ᶠ  : (ℕ → Formula) → Formula
    
    -- Meta-level proposition: the theory proves a formula.
    Provable : Formula → Set

    -- Minimal proof rules needed for the Gödel argument.
    mp       : {A B : Formula} → Provable (A ⇒ B) → Provable A → Provable B
    all-elim : {P : ℕ → Formula} → Provable (∀ᶠ P) → (n : ℕ) → Provable (P n)

    -- Proof n A is the object-language formula saying:
    -- “n is a code of a proof of A”.
    Proof : ℕ → Formula → Formula

    -- ProofCode n A is the meta-level relation saying:
    -- “n really is a proof code of A”.
    ProofCode : ℕ → Formula → Set

    -- Every meta-level proof has a code.
    proofCode-complete : {A : Formula} → Provable A → Σ ℕ (λ n → ProofCode n A)

    -- A real proof code can be decoded to a meta-level proof.
    proofCode-sound : {A : Formula} → {n : ℕ} → ProofCode n A → Provable A

    -- The proof predicate is represented in the object theory.
    represents-proof    : {A : Formula} → {n : ℕ} → ProofCode n A → Provable (Proof n A)
    represents-nonProof : {A : Formula} → (n : ℕ) → ¬ (ProofCode n A) → Provable (¬ᶠ (Proof n A))

-- Usual syntactic consistency: no formula and its negation are both provable.
Consistent : FormalSystem → Set
Consistent S = {A : Formula} → Provable A → Provable (¬ᶠ A) → ⊥
  where
    open FormalSystem S

-- ω-consistency in exactly the form Gödel's original proof needs.
-- If the theory proves ∃ n P(n), then it cannot be that for every n, the theory proves ¬ P(n).
OmegaConsistent : FormalSystem → Set
OmegaConsistent S = {P : ℕ → Formula} →
                    Provable (∃ᶠ P) →
                    ((n : ℕ) → Provable (¬ᶠ (P n))) →
                    ⊥
  where
    open FormalSystem S

-- A Gödel sentence G says, inside the theory:
--   if G, then every number is not a proof of G;
--   if not G, then some number is a proof of G.
-- These are the two directions extracted from the fixed-point construction.
record GödelSentence (S : FormalSystem) : Set where
  open FormalSystem S
  field
    G : Formula
    g→noProofs    : Provable (G ⇒ ∀ᶠ (λ n → ¬ᶠ (Proof n G)))
    notG→someProof : Provable ((¬ᶠ G) ⇒ ∃ᶠ (λ n → Proof n G))

module Theorem (S : FormalSystem) (D : GödelSentence S) where
  open FormalSystem S
  open GödelSentence D

  Undecidable : Formula → Set
  Undecidable A = (¬ (Provable A)) × (¬ (Provable (¬ᶠ A)))

  -- If T is consistent, G is not provable.
  not-provable-G : Consistent S → ¬ (Provable G)
  not-provable-G cons pG =
    cons proof-nG no-proof-nG
    where
      code-of-pG : Σ ℕ (λ n → ProofCode n G)
      code-of-pG = proofCode-complete pG

      n : ℕ
      n = fstΣ code-of-pG

      n-codes-pG : ProofCode n G
      n-codes-pG = sndΣ code-of-pG

      proof-nG : Provable (Proof n G)
      proof-nG = represents-proof n-codes-pG

      all-no-proofs : Provable (∀ᶠ (λ k → ¬ᶠ (Proof k G)))
      all-no-proofs = mp g→noProofs pG

      no-proof-nG : Provable (¬ᶠ (Proof n G))
      no-proof-nG = all-elim all-no-proofs n

  -- If T is consistent and ω-consistent, not-G is not provable.
  not-provable-notG : Consistent S → OmegaConsistent S → ¬ (Provable (¬ᶠ G))
  not-provable-notG cons omega pNotG =
    omega some-proof every-number-is-not-a-proof
    where
      P : ℕ → Formula
      P k = Proof k G

      some-proof : Provable (∃ᶠ P)
      some-proof = mp notG→someProof pNotG

      every-number-is-not-a-proof : (k : ℕ) → Provable (¬ᶠ (P k))
      every-number-is-not-a-proof k = represents-nonProof k no-real-code
        where
          no-real-code : ¬ (ProofCode k G)
          no-real-code k-codes-G = cons (proofCode-sound k-codes-G) pNotG

  -- Gödel's first incompleteness theorem, original ω-consistency version.
  first-incompleteness : Consistent S → OmegaConsistent S → Undecidable G
  first-incompleteness cons omega =
    not-provable-G cons ,× not-provable-notG cons omega
