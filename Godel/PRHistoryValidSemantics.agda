{-# OPTIONS --safe #-}

module Godel.PRHistoryValidSemantics where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List using (List; []; _∷_)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.PRBooleanHelpers
open import Godel.PRArithmeticSemantics
open import Godel.PRNatListDecoderSemantics
open import Godel.PRNatListDigitStream
open import Godel.PRHistoryValidCheckers
open import Godel.PRVectorHelpers
import Godel.PRHistoryCoding as History

lessEqNat-zero-left :
  (n : ℕ) → lessEqNat zero n ≡ suc zero
lessEqNat-zero-left zero = refl
lessEqNat-zero-left (suc n) = refl

lessEqNat-pred-left :
  (m n : ℕ) →
  lessEqNat (suc m) n ≡ suc zero →
  lessEqNat m n ≡ suc zero
lessEqNat-pred-left zero n p = lessEqNat-zero-left n
lessEqNat-pred-left (suc m) zero ()
lessEqNat-pred-left (suc m) (suc n) p =
  lessEqNat-pred-left m n p

seqNthNat-historyCode :
  (history : List ℕ) → (index : ℕ) →
  seqNthNat (History.historyCode history) index ≡
  History.historyNthDefault history index zero
seqNthNat-historyCode history index =
  trans
    (seqNthNat-historyCode-as-digits history index)
    (seqNthDigitsUpTo-natListDigits history index)

historyLengthOkNat : ℕ → ℕ → ℕ
historyLengthOkNat x sequence-code =
  eqNatNat (seqLengthNat sequence-code) (suc x)

historyInitOkNat :
  {n : ℕ} →
  PRF n →
  ℕ →
  Vec ℕ n →
  ℕ
historyInitOkNat g sequence-code xs =
  eqNatNat (seqNthNat sequence-code zero) (evalPRF g xs)

historyStepOkNat :
  {n : ℕ} →
  PRF (suc (suc n)) →
  ℕ →
  ℕ →
  Vec ℕ n →
  ℕ
historyStepOkNat h k sequence-code xs =
  eqNatNat
    (seqNthNat sequence-code (suc k))
    (evalPRF h (k ∷ seqNthNat sequence-code k ∷ xs))

historyAllStepsNat :
  {n : ℕ} →
  PRF (suc (suc n)) →
  ℕ →
  ℕ →
  Vec ℕ n →
  ℕ
historyAllStepsNat h zero sequence-code xs = suc zero
historyAllStepsNat h (suc k) sequence-code xs =
  mulNat
    (historyAllStepsNat h k sequence-code xs)
    (historyStepOkNat h k sequence-code xs)

historyValidNat :
  {n : ℕ} →
  PRF n →
  PRF (suc (suc n)) →
  ℕ →
  ℕ →
  Vec ℕ n →
  ℕ
historyValidNat g h x sequence-code xs =
  mulNat
    (historyLengthOkNat x sequence-code)
    (mulNat
      (historyInitOkNat g sequence-code xs)
      (historyAllStepsNat h x sequence-code xs))

historyLengthOkF-correct :
  {n : ℕ} →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (x sequence-code : ℕ) →
  (xs : Vec ℕ n) →
  evalPRF (historyLengthOkF g h) (x ∷ sequence-code ∷ xs) ≡
  historyLengthOkNat x sequence-code
historyLengthOkF-correct g h x sequence-code xs
  rewrite seqLengthF-correct-to-meta sequence-code
        | eqNatF-correct (seqLengthNat sequence-code) (suc x) = refl

historyInitOkF-correct :
  {n : ℕ} →
  (g : PRF n) →
  (x sequence-code : ℕ) →
  (xs : Vec ℕ n) →
  evalPRF (historyInitOkF g) (x ∷ sequence-code ∷ xs) ≡
  historyInitOkNat g sequence-code xs
historyInitOkF-correct g x sequence-code xs
  rewrite seqNthF-correct-to-meta sequence-code zero
        | evalPRFs-drop2ProjVec x sequence-code xs
        | eqNatF-correct
            (seqNthNat sequence-code zero)
            (evalPRF g xs) = refl

historyPrevF-correct :
  {n : ℕ} →
  (k acc sequence-code : ℕ) →
  (xs : Vec ℕ n) →
  evalPRF historyPrevF (k ∷ acc ∷ sequence-code ∷ xs) ≡
  seqNthNat sequence-code k
historyPrevF-correct k acc sequence-code xs =
  seqNthF-correct-to-meta sequence-code k

historyNextF-correct :
  {n : ℕ} →
  (k acc sequence-code : ℕ) →
  (xs : Vec ℕ n) →
  evalPRF historyNextF (k ∷ acc ∷ sequence-code ∷ xs) ≡
  seqNthNat sequence-code (suc k)
historyNextF-correct k acc sequence-code xs =
  seqNthF-correct-to-meta sequence-code (suc k)

historyStepExpectedF-correct :
  {n : ℕ} →
  (h : PRF (suc (suc n))) →
  (k acc sequence-code : ℕ) →
  (xs : Vec ℕ n) →
  evalPRF (historyStepExpectedF h) (k ∷ acc ∷ sequence-code ∷ xs) ≡
  evalPRF h (k ∷ seqNthNat sequence-code k ∷ xs)
historyStepExpectedF-correct h k acc sequence-code xs
  rewrite historyPrevF-correct k acc sequence-code xs
        | evalPRFs-drop3ProjVec k acc sequence-code xs = refl

historyStepOkF-correct :
  {n : ℕ} →
  (h : PRF (suc (suc n))) →
  (k acc sequence-code : ℕ) →
  (xs : Vec ℕ n) →
  evalPRF (historyStepOkF h) (k ∷ acc ∷ sequence-code ∷ xs) ≡
  historyStepOkNat h k sequence-code xs
historyStepOkF-correct h k acc sequence-code xs
  rewrite historyNextF-correct k acc sequence-code xs
        | historyStepExpectedF-correct h k acc sequence-code xs
        | eqNatF-correct
            (seqNthNat sequence-code (suc k))
            (evalPRF h (k ∷ seqNthNat sequence-code k ∷ xs)) = refl

historyAllStepsF-correct :
  {n : ℕ} →
  (h : PRF (suc (suc n))) →
  (x sequence-code : ℕ) →
  (xs : Vec ℕ n) →
  evalPRF (historyAllStepsF h) (x ∷ sequence-code ∷ xs) ≡
  historyAllStepsNat h x sequence-code xs
historyAllStepsF-correct h zero sequence-code xs = refl
historyAllStepsF-correct h (suc x) sequence-code xs
  rewrite historyAllStepsF-correct h x sequence-code xs
        | historyStepOkF-correct
            h
            x
            (historyAllStepsNat h x sequence-code xs)
            sequence-code
            xs
        | andF-correct
            (historyAllStepsNat h x sequence-code xs)
            (historyStepOkNat h x sequence-code xs) = refl

history-validF-candidate-correct-to-meta :
  {n : ℕ} →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (x sequence-code : ℕ) →
  (xs : Vec ℕ n) →
  evalPRF
    (history-validF-candidate g h)
    (x ∷ sequence-code ∷ xs)
  ≡ historyValidNat g h x sequence-code xs
history-validF-candidate-correct-to-meta g h x sequence-code xs
  rewrite historyLengthOkF-correct g h x sequence-code xs
        | historyInitOkF-correct g x sequence-code xs
        | historyAllStepsF-correct h x sequence-code xs
        | andF-correct
            (historyInitOkNat g sequence-code xs)
            (historyAllStepsNat h x sequence-code xs)
        | andF-correct
            (historyLengthOkNat x sequence-code)
            (mulNat
              (historyInitOkNat g sequence-code xs)
              (historyAllStepsNat h x sequence-code xs)) = refl

historyStepOkList :
  {n : ℕ} →
  PRF (suc (suc n)) →
  ℕ →
  List ℕ →
  Vec ℕ n →
  ℕ
historyStepOkList h k history xs =
  eqNatNat
    (History.historyNthDefault history (suc k) zero)
    (evalPRF h
      (k ∷ History.historyNthDefault history k zero ∷ xs))

historyAllStepsList :
  {n : ℕ} →
  PRF (suc (suc n)) →
  ℕ →
  List ℕ →
  Vec ℕ n →
  ℕ
historyAllStepsList h zero history xs = suc zero
historyAllStepsList h (suc k) history xs =
  mulNat
    (historyAllStepsList h k history xs)
    (historyStepOkList h k history xs)

historyStepOkNat-historyCode :
  {n : ℕ} →
  (h : PRF (suc (suc n))) →
  (k : ℕ) →
  (history : List ℕ) →
  (xs : Vec ℕ n) →
  historyStepOkNat h k (History.historyCode history) xs ≡
  historyStepOkList h k history xs
historyStepOkNat-historyCode h k history xs
  rewrite seqNthNat-historyCode history (suc k)
        | seqNthNat-historyCode history k = refl

historyAllStepsNat-historyCode :
  {n : ℕ} →
  (h : PRF (suc (suc n))) →
  (x : ℕ) →
  (history : List ℕ) →
  (xs : Vec ℕ n) →
  historyAllStepsNat h x (History.historyCode history) xs ≡
  historyAllStepsList h x history xs
historyAllStepsNat-historyCode h zero history xs = refl
historyAllStepsNat-historyCode h (suc x) history xs
  rewrite historyAllStepsNat-historyCode h x history xs
        | historyStepOkNat-historyCode h x history xs = refl

historyNthDefault-append-before-length :
  (history : List ℕ) →
  (index y default : ℕ) →
  lessEqNat (suc index) (History.historyLength history) ≡ suc zero →
  History.historyNthDefault (History.appendHistory history y) index default ≡
  History.historyNthDefault history index default
historyNthDefault-append-before-length [] index y default ()
historyNthDefault-append-before-length (x ∷ history) zero y default p = refl
historyNthDefault-append-before-length (x ∷ history) (suc index) y default p =
  historyNthDefault-append-before-length history index y default p

historyAllStepsList-append-before-length :
  {n : ℕ} →
  (h : PRF (suc (suc n))) →
  (steps : ℕ) →
  (history : List ℕ) →
  (y : ℕ) →
  (xs : Vec ℕ n) →
  lessEqNat (suc steps) (History.historyLength history) ≡ suc zero →
  historyAllStepsList h steps (History.appendHistory history y) xs ≡
  historyAllStepsList h steps history xs
historyAllStepsList-append-before-length h zero history y xs p = refl
historyAllStepsList-append-before-length h (suc steps) history y xs p
  rewrite historyAllStepsList-append-before-length
            h
            steps
            history
            y
            xs
            (lessEqNat-pred-left (suc steps) (History.historyLength history) p)
        | historyNthDefault-append-before-length
            history
            (suc steps)
            y
            zero
            p
        | historyNthDefault-append-before-length
            history
            steps
            y
            zero
            (lessEqNat-pred-left
              (suc steps)
              (History.historyLength history)
              p) = refl

historyNthDefault-append-evalHistory-last :
  {n : ℕ} →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (x : ℕ) →
  (xs : Vec ℕ n) →
  (y : ℕ) →
  History.historyNthDefault
    (History.appendHistory (History.evalHistory g h x xs) y)
    x
    zero
  ≡ History.lastHistory g h x xs
historyNthDefault-append-evalHistory-last g h x xs y
  rewrite historyNthDefault-append-before-length
            (History.evalHistory g h x xs)
            x
            y
            zero
            (subst
              (λ length →
                lessEqNat (suc x) length ≡ suc zero)
              (sym (History.historyLength-evalHistory g h x xs))
              (lessEqNat-refl (suc x)))
        | History.historyNth-evalHistory-last g h x xs = refl

historyNthDefault-append-evalHistory-next :
  {n : ℕ} →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (x : ℕ) →
  (xs : Vec ℕ n) →
  (y : ℕ) →
  History.historyNthDefault
    (History.appendHistory (History.evalHistory g h x xs) y)
    (suc x)
    zero
  ≡ y
historyNthDefault-append-evalHistory-next g h x xs y
  rewrite sym (History.historyLength-evalHistory g h x xs) =
  History.historyNthDefault-append-at-length
    (History.evalHistory g h x xs)
    y
    zero

historyStepOkList-evalHistory-last :
  {n : ℕ} →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (x : ℕ) →
  (xs : Vec ℕ n) →
  historyStepOkList
    h
    x
    (History.evalHistory g h (suc x) xs)
    xs
  ≡ suc zero
historyStepOkList-evalHistory-last g h x xs
  rewrite historyNthDefault-append-evalHistory-next
            g
            h
            x
            xs
            (evalPRF h (x ∷ History.lastHistory g h x xs ∷ xs))
        | historyNthDefault-append-evalHistory-last
            g
            h
            x
            xs
            (evalPRF h (x ∷ History.lastHistory g h x xs ∷ xs))
        | eqNatNat-refl
            (evalPRF h (x ∷ History.lastHistory g h x xs ∷ xs)) = refl

historyAllStepsList-evalHistory :
  {n : ℕ} →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (x : ℕ) →
  (xs : Vec ℕ n) →
  historyAllStepsList h x (History.evalHistory g h x xs) xs ≡ suc zero
historyAllStepsList-evalHistory g h zero xs = refl
historyAllStepsList-evalHistory g h (suc x) xs
  rewrite historyAllStepsList-append-before-length
            h
            x
            (History.evalHistory g h x xs)
            (evalPRF h (x ∷ History.lastHistory g h x xs ∷ xs))
            xs
            (subst
              (λ length →
                lessEqNat (suc x) length ≡ suc zero)
              (sym (History.historyLength-evalHistory g h x xs))
              (lessEqNat-refl (suc x)))
        | historyAllStepsList-evalHistory g h x xs
        | historyStepOkList-evalHistory-last g h x xs = refl

historyLengthOkNat-evalHistory :
  {n : ℕ} →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (x : ℕ) →
  (xs : Vec ℕ n) →
  historyLengthOkNat
    x
    (History.historyCode (History.evalHistory g h x xs))
  ≡ suc zero
historyLengthOkNat-evalHistory g h x xs
  rewrite seqLengthNat-historyCode (History.evalHistory g h x xs)
        | History.historyLength-evalHistory g h x xs
        | eqNatNat-refl (suc x) = refl

historyNthDefault-evalHistory-zero :
  {n : ℕ} →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (x : ℕ) →
  (xs : Vec ℕ n) →
  History.historyNthDefault (History.evalHistory g h x xs) zero zero ≡
  evalPRF g xs
historyNthDefault-evalHistory-zero g h zero xs = refl
historyNthDefault-evalHistory-zero g h (suc x) xs
  rewrite historyNthDefault-append-before-length
            (History.evalHistory g h x xs)
            zero
            (evalPRF h (x ∷ History.lastHistory g h x xs ∷ xs))
            zero
            (subst
              (λ length →
                lessEqNat (suc zero) length ≡ suc zero)
              (sym (History.historyLength-evalHistory g h x xs))
              (lessEqNat-zero-left x))
        | historyNthDefault-evalHistory-zero g h x xs = refl

historyInitOkNat-evalHistory :
  {n : ℕ} →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (x : ℕ) →
  (xs : Vec ℕ n) →
  historyInitOkNat
    g
    (History.historyCode (History.evalHistory g h x xs))
    xs
  ≡ suc zero
historyInitOkNat-evalHistory g h x xs
  rewrite seqNthNat-historyCode (History.evalHistory g h x xs) zero
        | historyNthDefault-evalHistory-zero g h x xs
        | eqNatNat-refl (evalPRF g xs) = refl

historyAllStepsNat-evalHistory :
  {n : ℕ} →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (x : ℕ) →
  (xs : Vec ℕ n) →
  historyAllStepsNat
    h
    x
    (History.historyCode (History.evalHistory g h x xs))
    xs
  ≡ suc zero
historyAllStepsNat-evalHistory g h x xs
  rewrite historyAllStepsNat-historyCode h x (History.evalHistory g h x xs) xs =
  historyAllStepsList-evalHistory g h x xs

historyValidNat-evalHistory :
  {n : ℕ} →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (x : ℕ) →
  (xs : Vec ℕ n) →
  historyValidNat
    g
    h
    x
    (History.historyCode (History.evalHistory g h x xs))
    xs
  ≡ suc zero
historyValidNat-evalHistory g h x xs
  rewrite historyLengthOkNat-evalHistory g h x xs
        | historyInitOkNat-evalHistory g h x xs
        | historyAllStepsNat-evalHistory g h x xs = refl

history-valid-correct-concrete :
  {n : ℕ} →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (x : ℕ) →
  (xs : Vec ℕ n) →
  evalPRF
    (history-validF-candidate g h)
    (x ∷ History.historyCode (History.evalHistory g h x xs) ∷ xs)
  ≡ suc zero
history-valid-correct-concrete g h x xs
  rewrite history-validF-candidate-correct-to-meta
            g
            h
            x
            (History.historyCode (History.evalHistory g h x xs))
            xs =
  historyValidNat-evalHistory g h x xs
