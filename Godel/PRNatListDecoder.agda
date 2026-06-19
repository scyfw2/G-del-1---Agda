{-# OPTIONS --safe #-}

module Godel.PRNatListDecoder where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.PrimitiveRecursive
open import Godel.PRBooleanHelpers
open import Godel.PRBoundedSearch
open import Godel.PRDigitCoding

digitEqualsAtF : PRF (suc (suc (suc zero)))
digitEqualsAtF =
  compF eqNatF
    (compF digitAtF
       (projF fin0 ∷
        projF fin1 ∷ []) ∷
     projF fin2 ∷ [])

countDigitBaseF : PRF (suc (suc zero))
countDigitBaseF =
  compF digitEqualsAtF
    (zeroF ∷
     projF fin1 ∷
     projF fin0 ∷ [])

countDigitStepF : PRF (suc (suc (suc (suc zero))))
countDigitStepF =
  compF addF
    (projF fin1 ∷
     compF digitEqualsAtF
       (compF sucF (projF fin0 ∷ []) ∷
        projF fin3 ∷
        projF fin2 ∷ []) ∷ [])

countDigitUpToF : PRF (suc (suc (suc zero)))
countDigitUpToF =
  precF countDigitBaseF countDigitStepF

seqLengthF : PRF (suc zero)
seqLengthF =
  compF countDigitUpToF
    (projF fin0 ∷
     constF (suc zero) ∷
     projF fin0 ∷ [])

digit2AtF : PRF (suc (suc (suc zero)))
digit2AtF =
  compF digitEqualsAtF
    (projF fin0 ∷
     projF fin1 ∷
     twoF ∷ [])

d1CountAtF : PRF (suc (suc (suc zero)))
d1CountAtF =
  compF countDigitUpToF
    (projF fin0 ∷
     constF (suc zero) ∷
     projF fin1 ∷ [])

d3CountAtF : PRF (suc (suc (suc zero)))
d3CountAtF =
  compF countDigitUpToF
    (projF fin0 ∷
     threeF ∷
     projF fin1 ∷ [])

seqNthActiveAtF : PRF (suc (suc (suc zero)))
seqNthActiveAtF =
  compF andF
    (digit2AtF ∷
     compF andF
       (compF eqNatF
         (d1CountAtF ∷
          compF sucF (projF fin2 ∷ []) ∷ []) ∷
        compF eqNatF
          (d3CountAtF ∷
           projF fin2 ∷ []) ∷ []) ∷ [])

seqNthBaseF : PRF (suc (suc zero))
seqNthBaseF =
  compF seqNthActiveAtF
    (zeroF ∷
     projF fin0 ∷
     projF fin1 ∷ [])

seqNthStepF : PRF (suc (suc (suc (suc zero))))
seqNthStepF =
  compF addF
    (projF fin1 ∷
     compF seqNthActiveAtF
       (compF sucF (projF fin0 ∷ []) ∷
        projF fin2 ∷
        projF fin3 ∷ []) ∷ [])

seqNthSumF : PRF (suc (suc (suc zero)))
seqNthSumF =
  precF seqNthBaseF seqNthStepF

seqNthF : PRF (suc (suc zero))
seqNthF =
  compF seqNthSumF
    (projF fin0 ∷
     projF fin0 ∷
     projF fin1 ∷ [])
