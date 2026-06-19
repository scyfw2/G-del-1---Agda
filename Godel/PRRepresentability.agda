{-# OPTIONS --safe #-}

module Godel.PRRepresentability where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.PA
open import Godel.ProofSystem
open import Godel.PAClosedArithmeticProofs
open import Godel.PrimitiveRecursive

numeralVec : {n : ℕ} → Vec ℕ n → Vec Term n
numeralVec = mapVec numeral

lookup-mapVec :
  {A B : Set} → {n : ℕ} →
  (f : A → B) → (i : Fin n) → (xs : Vec A n) →
  lookup i (mapVec f xs) ≡ f (lookup i xs)
lookup-mapVec f fzero (x ∷ xs) = refl
lookup-mapVec f (fsuc i) (x ∷ xs) = lookup-mapVec f i xs

record PARepresentsFunction {n : ℕ} (f : PRF n) : Set₁ where
  field
    graphFormula :
      Vec Term n → Term → Formula

    represents-value :
      (xs : Vec ℕ n) →
      PA-provable (graphFormula (numeralVec xs) (numeral (evalPRF f xs)))

record PARepresentsRelation {n : ℕ} (R : PRRel n) : Set₁ where
  field
    relationFormula :
      Vec Term n → Formula

    represents-true :
      (xs : Vec ℕ n) →
      PRRel-holds R xs →
      PA-provable (relationFormula (numeralVec xs))

    represents-false :
      (xs : Vec ℕ n) →
      ¬ PRRel-holds R xs →
      PA-provable (¬ᶠ (relationFormula (numeralVec xs)))

data AllPRF {n : ℕ} (P : PRF n → Set₁) :
            {m : ℕ} → Vec (PRF n) m → Set₁ where
  all[] : AllPRF P []
  all∷  : {m : ℕ} → {f : PRF n} → {fs : Vec (PRF n) m} →
          P f → AllPRF P fs → AllPRF P (f ∷ fs)

zeroFormula : {n : ℕ} → Vec Term n → Term → Formula
zeroFormula xs y = y ≈ zeroᵗ

sucFormula : Vec Term (suc zero) → Term → Formula
sucFormula (x ∷ []) y = y ≈ sucᵗ x

projFormula : {n : ℕ} → Fin n → Vec Term n → Term → Formula
projFormula i xs y = y ≈ lookup i xs

zeroF-represented : {n : ℕ} → PARepresentsFunction (zeroF {n})
zeroF-represented = record
  { graphFormula = zeroFormula
  ; represents-value = λ xs → eq-refl-rule zeroᵗ
  }

sucF-represented : PARepresentsFunction sucF
sucF-represented = record
  { graphFormula = sucFormula
  ; represents-value = λ
      { (x ∷ []) → eq-refl-rule (sucᵗ (numeral x)) }
  }

projF-represented :
  {n : ℕ} → (i : Fin n) → PARepresentsFunction (projF i)
projF-represented i = record
  { graphFormula = projFormula i
  ; represents-value = λ xs →
      pa-provable-cong
        (cong
          (λ t → numeral (lookup i xs) ≈ t)
          (sym (lookup-mapVec numeral i xs)))
        (eq-refl-rule (numeral (lookup i xs)))
  }

-- The closure steps below are the genuine remaining work for a full PR
-- representability theorem.  Composition needs existential witnesses for
-- intermediate values; primitive recursion needs sequence coding and bounded
-- reasoning inside PA.
record PACompositionRepresentabilityTarget : Set₁ where
  field
    composition-closes :
      {n m : ℕ} →
      (f : PRF m) →
      (gs : Vec (PRF n) m) →
      PARepresentsFunction f →
      AllPRF PARepresentsFunction gs →
      PARepresentsFunction (compF f gs)

record PAPrimitiveRecursionRepresentabilityTarget : Set₁ where
  field
    primitive-recursion-closes :
      {n : ℕ} →
      (g : PRF n) →
      (h : PRF (suc (suc n))) →
      PARepresentsFunction g →
      PARepresentsFunction h →
      PARepresentsFunction (precF g h)
