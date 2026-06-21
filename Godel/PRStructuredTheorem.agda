{-# OPTIONS --safe #-}

module Godel.PRStructuredTheorem where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.PA
open import Godel.ProofSystem
open import Godel.PAProofCombinators
open import Godel.PrimitiveRecursive
open import Godel.PRRepresentability
  using
    ( PARepresentsFunction
    ; PARepresentsRelation
    ; AllPRF
    ; all[]
    ; all∷
    ; numeralVec
    )
open import Godel.PRStructuredRepresentability
open import Godel.PRHistoryUniqueness

under-mp :
  {A B C : Formula} →
  PA-provable (A ⇒ (B ⇒ C)) →
  PA-provable B →
  PA-provable (A ⇒ C)
under-mp {A} {B} {C} p q =
  modus-ponens
    (modus-ponens
      (hilbert-S {A = A} {B = B} {C = C})
      p)
    (implies-const q)

mutual
  structured-prf-represented :
    {n : ℕ} → (f : PRF n) → StructuredFunctionRep f
  structured-prf-represented zeroF =
    zeroF-structured
  structured-prf-represented sucF =
    sucF-structured
  structured-prf-represented (projF i) =
    projF-structured i
  structured-prf-represented (compF f gs) =
    structured-composition-closes
      f
      gs
      (structured-prf-represented f)
      (structured-allRepresented gs)
  structured-prf-represented (precF g h) =
    structured-primitive-recursion-closes
      g
      h
      (structured-prf-represented g)
      (structured-prf-represented h)

  structured-allRepresented :
    {n m : ℕ} →
    (fs : Vec (PRF n) m) →
    AllPRF StructuredFunctionRep fs
  structured-allRepresented [] = all[]
  structured-allRepresented (f ∷ fs) =
    all∷
      (structured-prf-represented f)
      (structured-allRepresented fs)

prf-represented : {n : ℕ} → (f : PRF n) → PARepresentsFunction f
prf-represented f =
  structured->PARepresentsFunction (structured-prf-represented f)

prrel-represented : {n : ℕ} → (R : PRRel n) → PARepresentsRelation R
prrel-represented R = record
  { relationFormula = λ xs →
      PARepresentsFunction.graphFormula chi-rep xs (numeral (suc zero))
  ; represents-true = λ xs holds →
      pa-provable-cong
        (cong
          (λ k →
            PARepresentsFunction.graphFormula
              chi-rep
              (numeralVec xs)
              (numeral k))
          holds)
        (PARepresentsFunction.represents-value chi-rep xs)
  ; represents-false = λ xs not-holds →
      let
        graph-one : Formula
        graph-one =
          PARepresentsFunction.graphFormula
            chi-rep
            (numeralVec xs)
            (numeral (suc zero))

        graph-value : Formula
        graph-value =
          PARepresentsFunction.graphFormula
            chi-rep
            (numeralVec xs)
            (numeral (evalPRF (PRRel.characteristic R) xs))

        value-proof : PA-provable graph-value
        value-proof =
          PARepresentsFunction.represents-value chi-rep xs

        graph-one-implies-eq :
          PA-provable
            (graph-one ⇒
             numeral (suc zero) ≈
             numeral (evalPRF (PRRel.characteristic R) xs))
        graph-one-implies-eq =
          under-mp
            (PARepresentsFunction.represents-unique
              chi-rep
              xs
              (numeral (suc zero))
              (numeral (evalPRF (PRRel.characteristic R) xs)))
            value-proof

        neq-proof :
          PA-provable
            (¬ᶠ
              (numeral (suc zero) ≈
               numeral (evalPRF (PRRel.characteristic R) xs)))
        neq-proof =
          closed-numeral-neq
            (suc zero)
            (evalPRF (PRRel.characteristic R) xs)
            (λ eq → not-holds (sym eq))
      in
      modus-ponens
        (modus-ponens contradiction-to-neg graph-one-implies-eq)
        neq-proof
  }
  where
    chi-rep : PARepresentsFunction (PRRel.characteristic R)
    chi-rep = prf-represented (PRRel.characteristic R)
