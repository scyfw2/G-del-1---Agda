{-# OPTIONS --safe #-}

module Godel.PRHistoryValidCheckers where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.PrimitiveRecursive
open import Godel.PRBooleanHelpers
open import Godel.PRNatListDecoder
open import Godel.PRVectorHelpers

historyLengthOkF :
  {n : ℕ} →
  PRF n →
  PRF (suc (suc n)) →
  PRF (suc (suc n))
historyLengthOkF g h =
  compF eqNatF
    (compF seqLengthF (projF fin1 ∷ []) ∷
     compF sucF (projF fin0 ∷ []) ∷ [])

historyInitOkF :
  {n : ℕ} →
  PRF n →
  PRF (suc (suc n))
historyInitOkF g =
  compF eqNatF
    (compF seqNthF (projF fin1 ∷ zeroF ∷ []) ∷
     compF g drop2ProjVec ∷ [])

historyPrevF :
  {n : ℕ} →
  PRF (suc (suc (suc n)))
historyPrevF =
  compF seqNthF
    (projF fin2 ∷
     projF fin0 ∷ [])

historyNextF :
  {n : ℕ} →
  PRF (suc (suc (suc n)))
historyNextF =
  compF seqNthF
    (projF fin2 ∷
     compF sucF (projF fin0 ∷ []) ∷ [])

historyStepExpectedF :
  {n : ℕ} →
  PRF (suc (suc n)) →
  PRF (suc (suc (suc n)))
historyStepExpectedF h =
  compF h
    (projF fin0 ∷
     historyPrevF ∷
     drop3ProjVec)

historyStepOkF :
  {n : ℕ} →
  PRF (suc (suc n)) →
  PRF (suc (suc (suc n)))
historyStepOkF h =
  compF eqNatF
    (historyNextF ∷
     historyStepExpectedF h ∷ [])

historyAllStepsBaseF :
  {n : ℕ} →
  PRF (suc n)
historyAllStepsBaseF = oneF

historyAllStepsStepF :
  {n : ℕ} →
  PRF (suc (suc n)) →
  PRF (suc (suc (suc n)))
historyAllStepsStepF h =
  compF andF
    (projF fin1 ∷
     historyStepOkF h ∷ [])

historyAllStepsF :
  {n : ℕ} →
  PRF (suc (suc n)) →
  PRF (suc (suc n))
historyAllStepsF h =
  precF historyAllStepsBaseF (historyAllStepsStepF h)

history-validF-candidate :
  {n : ℕ} →
  PRF n →
  PRF (suc (suc n)) →
  PRF (suc (suc n))
history-validF-candidate g h =
  compF andF
    (historyLengthOkF g h ∷
     compF andF
       (historyInitOkF g ∷
        historyAllStepsF h ∷ []) ∷ [])
