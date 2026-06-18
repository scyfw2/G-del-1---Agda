{-# OPTIONS --safe #-}

module Godel.ArithmetizedTheory where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.Coding

-- A concrete arithmetized theory over the syntax in Godel.Syntax.
-- Heavy arithmetization facts are fields: proof coding is sound/complete,
-- and the binary proof predicate represents true proof-code and non-proof-code
-- facts inside the object theory.
record ArithmetizedTheory : Set₁ where
  field
    Provable : Formula → Set

    -- Congruence under definitional/propositional equality of formulas.
    provable-cong : {A B : Formula} → A ≡ B → Provable A → Provable B

    -- Proof rules needed by the incompleteness argument.
    mp       : {A B : Formula} → Provable (A ⇒ B) → Provable A → Provable B
    all-elim : {A : Formula} → (n : ℕ) → Provable (∀ᶠ A) → Provable (subst0 (numeral n) A)

    -- Meta-level relation: n really codes a proof of A.
    ProofCode : ℕ → Formula → Set

    -- Every object-level proof has a natural-number code, and every genuine
    -- proof-code decodes to an object-level proof.
    proofCode-complete : {A : Formula} → Provable A → Σ ℕ (λ n → ProofCode n A)
    proofCode-sound    : {A : Formula} → {n : ℕ} → ProofCode n A → Provable A

    -- Representability of the proof predicate.
    represents-proof : {A : Formula} → {n : ℕ} →
                       ProofCode n A → Provable (ProofOf (numeral n) A)

    represents-nonProof : {A : Formula} → (n : ℕ) →
                          ¬ (ProofCode n A) → Provable (¬ᶠ (ProofOf (numeral n) A))

    -- Classical object-logic step used to derive ¬G -> ∃p Proof(p,G)
    -- from the converse fixed-point direction noProofs(G) -> G.
    classical-step : {A : Formula} →
                     Provable ((noProofs A ⇒ A) ⇒ ((¬ᶠ A) ⇒ someProof A))

Consistent : ArithmetizedTheory → Set
Consistent T = {A : Formula} → Provable A → Provable (¬ᶠ A) → ⊥
  where
    open ArithmetizedTheory T

-- ω-consistency in the exact form used by Gödel's original proof:
-- it rules out proving ∃x P(x) while proving ¬P(n) for every numeral n.
OmegaConsistent : ArithmetizedTheory → Set
OmegaConsistent T = {A : Formula} →
                    Provable (∃ᶠ A) →
                    ((n : ℕ) → Provable (¬ᶠ (subst0 (numeral n) A))) →
                    ⊥
  where
    open ArithmetizedTheory T

Undecidable : (T : ArithmetizedTheory) → Formula → Set
Undecidable T A = (¬ (Provable A)) × (¬ (Provable (¬ᶠ A)))
  where
    open ArithmetizedTheory T
