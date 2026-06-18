{-# OPTIONS --safe #-}

module Godel.RepresentabilityTargets where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.ArithmetizedTheory
open import Godel.CanonicalCoding
open import Godel.DiagonalCoding
open import Godel.ComputableGraphs

-- Generic representability targets for concrete numeric relations.
-- These records state the object-language formulas that should represent
-- true and false meta-level relation facts.  They do not provide PA instances.
record Represents₂
       (T : ArithmetizedTheory)
       (R : ℕ → ℕ → Set)
       (F : Term → Term → Formula) : Set₁ where
  open ArithmetizedTheory T
  field
    represents₂-true :
      {x y : ℕ} → R x y → Provable (F (numeral x) (numeral y))

    represents₂-false :
      (x y : ℕ) → ¬ (R x y) → Provable (¬ᶠ (F (numeral x) (numeral y)))

record Represents₃
       (T : ArithmetizedTheory)
       (R : ℕ → ℕ → ℕ → Set)
       (F : Term → Term → Term → Formula) : Set₁ where
  open ArithmetizedTheory T
  field
    represents₃-true :
      {x y z : ℕ} → R x y z →
      Provable (F (numeral x) (numeral y) (numeral z))

    represents₃-false :
      (x y z : ℕ) → ¬ (R x y z) →
      Provable (¬ᶠ (F (numeral x) (numeral y) (numeral z)))

DiagRepresentability : ArithmetizedTheory → Set₁
DiagRepresentability T = Represents₂ T DiagNatCode DiagRel

Subst0Representability : ArithmetizedTheory → Set₁
Subst0Representability T = Represents₃ T Subst0NatCode Subst0Rel

CheckedDiagRepresentability : ArithmetizedTheory → Set₁
CheckedDiagRepresentability T = Represents₂ T CheckedDiagNatCode DiagRel

CheckedSubst0Representability : ArithmetizedTheory → Set₁
CheckedSubst0Representability T =
  Represents₃ T CheckedSubst0NatCode Subst0Rel

record PrePARepresentabilityData (T : ArithmetizedTheory) : Set₁ where
  field
    subst0-representability : Subst0Representability T
    diag-representability   : DiagRepresentability T

record CheckedPrePARepresentabilityData (T : ArithmetizedTheory) : Set₁ where
  field
    checked-subst0-representability : CheckedSubst0Representability T
    checked-diag-representability   : CheckedDiagRepresentability T
