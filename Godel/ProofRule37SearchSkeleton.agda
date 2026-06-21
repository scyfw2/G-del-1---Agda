{-# OPTIONS --safe #-}

module Godel.ProofRule37SearchSkeleton where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.PRBooleanHelpers using (fin0; fin1; fin2; fin3; orF)
open import Godel.PRArithmeticSemantics using (orF-correct)
open import Godel.ProofCheckingPR using (proofCodeArgs)
open import Godel.ProofRule37Search using (searchUpTo)
open import Godel.ProofRuleTargets using (rule37WitnessArgs)

-- Generic two-dimensional bounded search over a four-argument witness checker.
-- The old rule37SearchF and the parser-backed variant have the same search
-- skeleton; only the searched hit PRF changes.  Proving this once with hitF as
-- a parameter avoids normalizing the concrete witness checker inside the search
-- correctness proof.

PRF₄ : Set
PRF₄ = PRF (suc (suc (suc (suc zero))))

fin4 : {n : ℕ} → Fin (suc (suc (suc (suc (suc n)))))
fin4 = fsuc fin3

rule37SearchNBaseFFor : PRF₄ → PRF (suc (suc (suc zero)))
rule37SearchNBaseFFor hitF =
  compF hitF
    (projF fin0 ∷
     zeroF ∷
     projF fin1 ∷
     projF fin2 ∷ [])

rule37SearchNStepFFor :
  PRF₄ → PRF (suc (suc (suc (suc (suc zero)))))
rule37SearchNStepFFor hitF =
  compF orF
    (projF fin1 ∷
     compF hitF
      (projF fin2 ∷
       compF sucF (projF fin0 ∷ []) ∷
       projF fin3 ∷
       projF fin4 ∷ []) ∷ [])

rule37SearchNFFor : PRF₄ → PRF (suc (suc (suc (suc zero))))
rule37SearchNFFor hitF =
  precF (rule37SearchNBaseFFor hitF) (rule37SearchNStepFFor hitF)

rule37SearchMBaseFFor : PRF₄ → PRF (suc (suc zero))
rule37SearchMBaseFFor hitF =
  compF (rule37SearchNFFor hitF)
    (projF fin0 ∷
     zeroF ∷
     projF fin0 ∷
     projF fin1 ∷ [])

rule37SearchMStepFFor :
  PRF₄ → PRF (suc (suc (suc (suc zero))))
rule37SearchMStepFFor hitF =
  compF orF
    (projF fin1 ∷
     compF (rule37SearchNFFor hitF)
      (projF fin2 ∷
       compF sucF (projF fin0 ∷ []) ∷
       projF fin2 ∷
       projF fin3 ∷ []) ∷ [])

rule37SearchMFFor : PRF₄ → PRF (suc (suc (suc zero)))
rule37SearchMFFor hitF =
  precF (rule37SearchMBaseFFor hitF) (rule37SearchMStepFFor hitF)

rule37SearchFFor : PRF₄ → PRF (suc (suc zero))
rule37SearchFFor hitF =
  compF (rule37SearchMFFor hitF)
    (projF fin0 ∷
     projF fin0 ∷
     projF fin1 ∷ [])

rule37HitValueFor : PRF₄ → ℕ → ℕ → ℕ → ℕ → ℕ
rule37HitValueFor hitF m n proof-code formula-code =
  evalPRF hitF (rule37WitnessArgs m n proof-code formula-code)

rule37SearchNMetaFor : PRF₄ → ℕ → ℕ → ℕ → ℕ → ℕ
rule37SearchNMetaFor hitF bound m proof-code formula-code =
  searchUpTo
    (λ n → rule37HitValueFor hitF m n proof-code formula-code)
    bound

rule37SearchMMetaFor : PRF₄ → ℕ → ℕ → ℕ → ℕ
rule37SearchMMetaFor hitF bound proof-code formula-code =
  searchUpTo
    (λ m → rule37SearchNMetaFor hitF proof-code m proof-code formula-code)
    bound

rule37SearchNFFor-correct :
  (hitF : PRF₄) →
  (bound m proof-code formula-code : ℕ) →
  evalPRF (rule37SearchNFFor hitF)
    (bound ∷ m ∷ proof-code ∷ formula-code ∷ []) ≡
  rule37SearchNMetaFor hitF bound m proof-code formula-code
rule37SearchNFFor-correct hitF zero m proof-code formula-code = refl
rule37SearchNFFor-correct hitF (suc bound) m proof-code formula-code
  rewrite rule37SearchNFFor-correct hitF bound m proof-code formula-code
        | orF-correct
            (rule37SearchNMetaFor hitF bound m proof-code formula-code)
            (evalPRF hitF
              (m ∷ suc bound ∷ proof-code ∷ formula-code ∷ [])) =
  refl

rule37SearchMFFor-correct :
  (hitF : PRF₄) →
  (bound proof-code formula-code : ℕ) →
  evalPRF (rule37SearchMFFor hitF)
    (bound ∷ proof-code ∷ formula-code ∷ []) ≡
  rule37SearchMMetaFor hitF bound proof-code formula-code
rule37SearchMFFor-correct hitF zero proof-code formula-code
  rewrite rule37SearchNFFor-correct
            hitF
            proof-code
            zero
            proof-code
            formula-code =
  refl
rule37SearchMFFor-correct hitF (suc bound) proof-code formula-code
  rewrite rule37SearchMFFor-correct hitF bound proof-code formula-code
        | rule37SearchNFFor-correct
            hitF
            proof-code
            (suc bound)
            proof-code
            formula-code
        | orF-correct
            (rule37SearchMMetaFor hitF bound proof-code formula-code)
            (rule37SearchNMetaFor
              hitF
              proof-code
              (suc bound)
              proof-code
              formula-code) =
  refl

rule37SearchFFor-correct :
  (hitF : PRF₄) →
  (proof-code formula-code : ℕ) →
  evalPRF
    (rule37SearchFFor hitF)
    (proofCodeArgs proof-code formula-code)
  ≡
  rule37SearchMMetaFor hitF proof-code proof-code formula-code
rule37SearchFFor-correct hitF proof-code formula-code =
  rule37SearchMFFor-correct hitF proof-code proof-code formula-code
