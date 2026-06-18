{-# OPTIONS --safe #-}

module Godel.PARepresentabilityEntry where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.PA
open import Godel.CanonicalCoding
open import Godel.ComputableGraphs
open import Godel.DiagonalCoding
open import Godel.RepresentabilityTargets
open import Godel.Diagonal
open import Godel.PAFirstIncompleteness

-- PA-facing entry point for the checked graph layer.
--
-- This record does not prove that PA represents the checked graph predicates;
-- it states the exact PA-provability obligations that a future PA instance
-- must discharge.
record PACheckedGraphRepresentability : Set₁ where
  field
    pa-checked-diag-true :
      {x y : ℕ} →
      CheckedDiagNatCode x y →
      PA-provable (DiagRel (numeral x) (numeral y))

    pa-checked-diag-false :
      (x y : ℕ) →
      ¬ CheckedDiagNatCode x y →
      PA-provable (¬ᶠ (DiagRel (numeral x) (numeral y)))

    pa-checked-subst0-true :
      {x y z : ℕ} →
      CheckedSubst0NatCode x y z →
      PA-provable (Subst0Rel (numeral x) (numeral y) (numeral z))

    pa-checked-subst0-false :
      (x y z : ℕ) →
      ¬ CheckedSubst0NatCode x y z →
      PA-provable (¬ᶠ (Subst0Rel (numeral x) (numeral y) (numeral z)))

pa-checked-graph-representability-as-prePA :
  (repr : PARepresentability) →
  PACheckedGraphRepresentability →
  CheckedPrePARepresentabilityData (PA-as-theory repr)
pa-checked-graph-representability-as-prePA repr graphs = record
  { checked-subst0-representability = record
      { represents₃-true =
          PACheckedGraphRepresentability.pa-checked-subst0-true graphs
      ; represents₃-false =
          PACheckedGraphRepresentability.pa-checked-subst0-false graphs
      }
  ; checked-diag-representability = record
      { represents₂-true =
          PACheckedGraphRepresentability.pa-checked-diag-true graphs
      ; represents₂-false =
          PACheckedGraphRepresentability.pa-checked-diag-false graphs
      }
  }

record PANoProofsFixedPointEntryData : Set₁ where
  field
    repr : PARepresentability
    checked-graphs-PA : PACheckedGraphRepresentability
    noProofs-fixedPoint-from-PA-graphs :
      NoProofsFixedPoint (PA-as-theory repr)

pa-entry-checked-prePA :
  (D : PANoProofsFixedPointEntryData) →
  CheckedPrePARepresentabilityData
    (PA-as-theory (PANoProofsFixedPointEntryData.repr D))
pa-entry-checked-prePA D =
  pa-checked-graph-representability-as-prePA
    (PANoProofsFixedPointEntryData.repr D)
    (PANoProofsFixedPointEntryData.checked-graphs-PA D)

pa-entry-to-noProofs-incompleteness-data :
  PANoProofsFixedPointEntryData →
  PANoProofsIncompletenessData
pa-entry-to-noProofs-incompleteness-data D = record
  { repr = PANoProofsFixedPointEntryData.repr D
  ; noProofs-fixedPoint-PA =
      PANoProofsFixedPointEntryData.noProofs-fixedPoint-from-PA-graphs D
  }
