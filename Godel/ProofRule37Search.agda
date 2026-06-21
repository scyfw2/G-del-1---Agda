{-# OPTIONS --safe #-}

module Godel.ProofRule37Search where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.PRBooleanHelpers using (fin0; fin1; fin2; fin3; orF)
open import Godel.PRArithmeticSemantics using (orF-correct; isZeroNat)
open import Godel.PRRepresentabilityFinal using (PARepresentsRelation; prrel-represented)
open import Godel.ProofCheckingPR using (proofCodeArgs)
open import Godel.ProofRule37PRHolds
  using
    ( Rule37WitnessExists
    ; ProofRule37WitnessSearchPR
    )
open import Godel.ProofRuleTargets

-- A concrete bounded-search candidate for the closed numeral inequality rule.
-- The search scans all m,n <= proof-code and runs the already represented
-- four-argument witness checker rule37WitnessF.  The remaining mathematical
-- task is to prove that canonical rule-37 proof codes always have witnesses
-- below this bound.

fin4 : {n : ℕ} → Fin (suc (suc (suc (suc (suc n)))))
fin4 = fsuc fin3

orNat : ℕ → ℕ → ℕ
orNat m n = isZeroNat (isZeroNat (m + n))

searchUpTo : (ℕ → ℕ) → ℕ → ℕ
searchUpTo P zero = P zero
searchUpTo P (suc bound) =
  orNat (searchUpTo P bound) (P (suc bound))

rule37SearchNBaseF : PRF (suc (suc (suc zero)))
rule37SearchNBaseF =
  compF rule37WitnessF
    (projF fin0 ∷
     zeroF ∷
     projF fin1 ∷
     projF fin2 ∷ [])

rule37SearchNStepF : PRF (suc (suc (suc (suc (suc zero)))))
rule37SearchNStepF =
  compF orF
    (projF fin1 ∷
     compF rule37WitnessF
      (projF fin2 ∷
       compF sucF (projF fin0 ∷ []) ∷
       projF fin3 ∷
       projF fin4 ∷ []) ∷ [])

rule37SearchNF : PRF (suc (suc (suc (suc zero))))
rule37SearchNF =
  precF rule37SearchNBaseF rule37SearchNStepF

rule37SearchMBaseF : PRF (suc (suc zero))
rule37SearchMBaseF =
  compF rule37SearchNF
    (projF fin0 ∷
     zeroF ∷
     projF fin0 ∷
     projF fin1 ∷ [])

rule37SearchMStepF : PRF (suc (suc (suc (suc zero))))
rule37SearchMStepF =
  compF orF
    (projF fin1 ∷
     compF rule37SearchNF
      (projF fin2 ∷
       compF sucF (projF fin0 ∷ []) ∷
       projF fin2 ∷
       projF fin3 ∷ []) ∷ [])

rule37SearchMF : PRF (suc (suc (suc zero)))
rule37SearchMF =
  precF rule37SearchMBaseF rule37SearchMStepF

rule37SearchF : PRF (suc (suc zero))
rule37SearchF =
  compF rule37SearchMF
    (projF fin0 ∷
     projF fin0 ∷
     projF fin1 ∷ [])

rule37SearchPR : PRRel (suc (suc zero))
rule37SearchPR = rel rule37SearchF

rule37WitnessValue : ℕ → ℕ → ℕ → ℕ → ℕ
rule37WitnessValue m n proof-code formula-code =
  evalPRF rule37WitnessF
    (m ∷ n ∷ proof-code ∷ formula-code ∷ [])

rule37SearchNMeta : ℕ → ℕ → ℕ → ℕ → ℕ
rule37SearchNMeta bound m proof-code formula-code =
  searchUpTo
    (λ n → rule37WitnessValue m n proof-code formula-code)
    bound

rule37SearchMMeta : ℕ → ℕ → ℕ → ℕ
rule37SearchMMeta bound proof-code formula-code =
  searchUpTo
    (λ m → rule37SearchNMeta proof-code m proof-code formula-code)
    bound

rule37SearchNF-correct :
  (bound m proof-code formula-code : ℕ) →
  evalPRF rule37SearchNF
    (bound ∷ m ∷ proof-code ∷ formula-code ∷ []) ≡
  rule37SearchNMeta bound m proof-code formula-code
rule37SearchNF-correct zero m proof-code formula-code = refl
rule37SearchNF-correct (suc bound) m proof-code formula-code
  rewrite rule37SearchNF-correct bound m proof-code formula-code
        | orF-correct
            (rule37SearchNMeta bound m proof-code formula-code)
            (evalPRF rule37WitnessF
              (m ∷ suc bound ∷ proof-code ∷ formula-code ∷ [])) =
  refl

rule37SearchMF-correct :
  (bound proof-code formula-code : ℕ) →
  evalPRF rule37SearchMF
    (bound ∷ proof-code ∷ formula-code ∷ []) ≡
  rule37SearchMMeta bound proof-code formula-code
rule37SearchMF-correct zero proof-code formula-code
  rewrite rule37SearchNF-correct proof-code zero proof-code formula-code =
  refl
rule37SearchMF-correct (suc bound) proof-code formula-code
  rewrite rule37SearchMF-correct bound proof-code formula-code
        | rule37SearchNF-correct
            proof-code
            (suc bound)
            proof-code
            formula-code
        | orF-correct
            (rule37SearchMMeta bound proof-code formula-code)
            (rule37SearchNMeta proof-code (suc bound) proof-code formula-code) =
  refl

rule37SearchF-correct :
  (proof-code formula-code : ℕ) →
  evalPRF rule37SearchF (proofCodeArgs proof-code formula-code) ≡
  rule37SearchMMeta proof-code proof-code formula-code
rule37SearchF-correct proof-code formula-code =
  rule37SearchMF-correct proof-code proof-code formula-code

rule37SearchPR-represented :
  PARepresentsRelation rule37SearchPR
rule37SearchPR-represented =
  prrel-represented rule37SearchPR

record Rule37SearchCorrect : Set₁ where
  field
    search-complete :
      {proof-code formula-code : ℕ} →
      Rule37WitnessExists proof-code formula-code →
      evalPRF rule37SearchF (proofCodeArgs proof-code formula-code) ≡
      suc zero

    search-sound :
      {proof-code formula-code : ℕ} →
      evalPRF rule37SearchF (proofCodeArgs proof-code formula-code) ≡
      suc zero →
      Rule37WitnessExists proof-code formula-code

proofRule37WitnessSearchPR-from-search-correct :
  Rule37SearchCorrect →
  ProofRule37WitnessSearchPR
proofRule37WitnessSearchPR-from-search-correct C = record
  { rule37-search-pr =
      rel rule37SearchF
  ; rule37-search-complete = λ {proof-code} {formula-code} witness →
      Rule37SearchCorrect.search-complete C
        {proof-code}
        {formula-code}
        witness
  ; rule37-search-sound = λ {proof-code} {formula-code} holds →
      Rule37SearchCorrect.search-sound C
        {proof-code}
        {formula-code}
        holds
  }
