{-# OPTIONS --safe #-}

module Godel.PRBooleanHelpers where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.PrimitiveRecursive
open import Godel.PRRepresentability

fin0 : {n : ℕ} → Fin (suc n)
fin0 = fzero

fin1 : {n : ℕ} → Fin (suc (suc n))
fin1 = fsuc fzero

fin2 : {n : ℕ} → Fin (suc (suc (suc n)))
fin2 = fsuc (fsuc fzero)

fin3 : {n : ℕ} → Fin (suc (suc (suc (suc n))))
fin3 = fsuc (fsuc (fsuc fzero))

addF : PRF (suc (suc zero))
addF =
  precF
    (projF fin0)
    (compF sucF (projF fin1 ∷ []))

mulF : PRF (suc (suc zero))
mulF =
  precF
    zeroF
    (compF addF (projF fin1 ∷ projF fin2 ∷ []))

predF : PRF (suc zero)
predF =
  precF
    zeroF
    (projF fin0)

subFromFirstF : PRF (suc (suc zero))
subFromFirstF =
  precF
    (projF fin0)
    (compF predF (projF fin1 ∷ []))

minusF : PRF (suc (suc zero))
minusF =
  compF subFromFirstF (projF fin1 ∷ projF fin0 ∷ [])

isZeroF : PRF (suc zero)
isZeroF =
  precF
    oneF
    zeroF

notF : PRF (suc zero)
notF = isZeroF

andF : PRF (suc (suc zero))
andF = mulF

lessEqF : PRF (suc (suc zero))
lessEqF =
  compF isZeroF (minusF ∷ [])

eqNatF : PRF (suc (suc zero))
eqNatF =
  compF andF
    (lessEqF ∷
     compF lessEqF (projF fin1 ∷ projF fin0 ∷ []) ∷ [])

orF : PRF (suc (suc zero))
orF =
  compF
    isZeroF
    (compF isZeroF (compF addF (projF fin0 ∷ projF fin1 ∷ []) ∷ []) ∷ [])

ifZeroF : PRF (suc (suc (suc zero)))
ifZeroF =
  compF addF
    (compF mulF
      (compF isZeroF (projF fin0 ∷ []) ∷
       projF fin1 ∷ []) ∷
     compF mulF
      (compF notF (compF isZeroF (projF fin0 ∷ []) ∷ []) ∷
       projF fin2 ∷ []) ∷ [])

xorF : PRF (suc (suc zero))
xorF =
  compF orF
    (compF andF
      (compF notF (projF fin0 ∷ []) ∷
       projF fin1 ∷ []) ∷
     compF andF
      (projF fin0 ∷
       compF notF (projF fin1 ∷ []) ∷ []) ∷ [])

eqBoolF : PRF (suc (suc zero))
eqBoolF =
  compF notF (xorF ∷ [])

boundedSearchF : PRF (suc (suc zero))
boundedSearchF = zeroF

record PRBooleanHelperRepresentability : Set₁ where
  field
    add-represented    : PARepresentsFunction addF
    mul-represented    : PARepresentsFunction mulF
    pred-represented   : PARepresentsFunction predF
    minus-represented  : PARepresentsFunction minusF
    isZero-represented : PARepresentsFunction isZeroF
    not-represented    : PARepresentsFunction notF
    and-represented    : PARepresentsFunction andF
    lessEq-represented : PARepresentsFunction lessEqF
    eqNat-represented  : PARepresentsFunction eqNatF
    or-represented     : PARepresentsFunction orF
    ifZero-represented : PARepresentsFunction ifZeroF
    xor-represented    : PARepresentsFunction xorF
    eqBool-represented : PARepresentsFunction eqBoolF
    boundedSearch-represented : PARepresentsFunction boundedSearchF

prBooleanHelperRepresentability : PRBooleanHelperRepresentability
prBooleanHelperRepresentability = record
  { add-represented = prf-represented addF
  ; mul-represented = prf-represented mulF
  ; pred-represented = prf-represented predF
  ; minus-represented = prf-represented minusF
  ; isZero-represented = prf-represented isZeroF
  ; not-represented = prf-represented notF
  ; and-represented = prf-represented andF
  ; lessEq-represented = prf-represented lessEqF
  ; eqNat-represented = prf-represented eqNatF
  ; or-represented = prf-represented orF
  ; ifZero-represented = prf-represented ifZeroF
  ; xor-represented = prf-represented xorF
  ; eqBool-represented = prf-represented eqBoolF
  ; boundedSearch-represented = prf-represented boundedSearchF
  }
