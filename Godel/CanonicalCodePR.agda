{-# OPTIONS --safe #-}

module Godel.CanonicalCodePR where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.PrimitiveRecursive
open import Godel.PRBooleanHelpers
open import Godel.PRRepresentability

isAtomCodeF : PRF (suc zero)
isAtomCodeF = zeroF

isNodeCodeF : PRF (suc zero)
isNodeCodeF = zeroF

atomPayloadF : PRF (suc zero)
atomPayloadF = zeroF

nodeTagF : PRF (suc zero)
nodeTagF = zeroF

nodeChildrenF : PRF (suc zero)
nodeChildrenF = zeroF

codeListNilF : PRF (suc zero)
codeListNilF = zeroF

codeListHeadF : PRF (suc zero)
codeListHeadF = zeroF

codeListTailF : PRF (suc zero)
codeListTailF = zeroF

codeListLengthF : PRF (suc zero)
codeListLengthF = zeroF

codeListNthF : PRF (suc (suc zero))
codeListNthF = zeroF

record CanonicalCodePRDestructors : Set₁ where
  field
    isAtom-represented       : PARepresentsFunction isAtomCodeF
    isNode-represented       : PARepresentsFunction isNodeCodeF
    atomPayload-represented  : PARepresentsFunction atomPayloadF
    nodeTag-represented      : PARepresentsFunction nodeTagF
    nodeChildren-represented : PARepresentsFunction nodeChildrenF
    codeListNil-represented  : PARepresentsFunction codeListNilF
    codeListHead-represented : PARepresentsFunction codeListHeadF
    codeListTail-represented : PARepresentsFunction codeListTailF
    codeListLength-represented : PARepresentsFunction codeListLengthF
    codeListNth-represented    : PARepresentsFunction codeListNthF

canonicalCodePRDestructors : CanonicalCodePRDestructors
canonicalCodePRDestructors = record
  { isAtom-represented = prf-represented isAtomCodeF
  ; isNode-represented = prf-represented isNodeCodeF
  ; atomPayload-represented = prf-represented atomPayloadF
  ; nodeTag-represented = prf-represented nodeTagF
  ; nodeChildren-represented = prf-represented nodeChildrenF
  ; codeListNil-represented = prf-represented codeListNilF
  ; codeListHead-represented = prf-represented codeListHeadF
  ; codeListTail-represented = prf-represented codeListTailF
  ; codeListLength-represented = prf-represented codeListLengthF
  ; codeListNth-represented = prf-represented codeListNthF
  }
