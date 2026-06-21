{-# OPTIONS --safe #-}

module Godel.PRRepresentabilityFinal where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.PrimitiveRecursive
open import Godel.PRRepresentability public
  using
    ( PARepresentsFunction
    ; PARepresentsRelation
    ; AllPRF
    ; all[]
    ; all∷
    ; numeralVec
    ; lookup-mapVec
    )
open import Godel.PRStructuredRepresentability public
  using
    ( StructuredFunctionRep
    ; structured->PARepresentsFunction
    )
open import Godel.PRStructuredTheorem public
  using
    ( structured-prf-represented
    ; structured-allRepresented
    ; prf-represented
    ; prrel-represented
    )

-- Final public boundary for the project's general primitive-recursive
-- representability theorem.  Godel.PRRepresentability remains available as a
-- legacy/bootstrap module; new high-level code should import this module.
record PAAllPRRepresentability : Set₁ where
  field
    represents-function :
      {n : ℕ} → (f : PRF n) → PARepresentsFunction f

    represents-relation :
      {n : ℕ} → (R : PRRel n) → PARepresentsRelation R

paAllPRRepresentability : PAAllPRRepresentability
paAllPRRepresentability = record
  { represents-function = prf-represented
  ; represents-relation = prrel-represented
  }
