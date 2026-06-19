{-# OPTIONS --safe #-}

module Godel.PRNatListDecoderSemantics where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List using (List)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.PRBooleanHelpers
open import Godel.PRArithmeticSemantics
open import Godel.PRDigitSemantics
open import Godel.PRNatListDecoder
open import Godel.PRNatListDigitStream
open import Godel.CanonicalCoding using (Digit)
import Godel.PRHistoryCoding as History

countDigitUpToNat : ℕ → ℕ → ℕ → ℕ
countDigitUpToNat zero digit input =
  digitEqualsAtNat zero input digit
countDigitUpToNat (suc bound) digit input =
  countDigitUpToNat bound digit input +
  digitEqualsAtNat (suc bound) input digit

seqLengthNat : ℕ → ℕ
seqLengthNat input =
  countDigitUpToNat input (suc zero) input

seqNthActiveAtNat : ℕ → ℕ → ℕ → ℕ
seqNthActiveAtNat position input index =
  mulNat
    (digitEqualsAtNat position input (suc (suc zero)))
    (mulNat
      (eqNatNat
        (countDigitUpToNat position (suc zero) input)
        (suc index))
      (eqNatNat
        (countDigitUpToNat position (suc (suc (suc zero))) input)
        index))

seqNthSumNat : ℕ → ℕ → ℕ → ℕ
seqNthSumNat zero input index =
  seqNthActiveAtNat zero input index
seqNthSumNat (suc bound) input index =
  seqNthSumNat bound input index +
  seqNthActiveAtNat (suc bound) input index

seqNthNat : ℕ → ℕ → ℕ
seqNthNat input index =
  seqNthSumNat input input index

digitEqualsAtF-correct :
  (position input digit : ℕ) →
  evalPRF digitEqualsAtF (position ∷ input ∷ digit ∷ []) ≡
  digitEqualsAtNat position input digit
digitEqualsAtF-correct position input digit
  rewrite digitAtF-correct position input
        | eqNatF-correct (digitAtNat position input) digit = refl

countDigitBaseF-correct :
  (digit input : ℕ) →
  evalPRF countDigitBaseF (digit ∷ input ∷ []) ≡
  countDigitUpToNat zero digit input
countDigitBaseF-correct digit input =
  digitEqualsAtF-correct zero input digit

countDigitStepF-correct :
  (bound previous digit input : ℕ) →
  evalPRF countDigitStepF (bound ∷ previous ∷ digit ∷ input ∷ []) ≡
  previous + digitEqualsAtNat (suc bound) input digit
countDigitStepF-correct bound previous digit input
  rewrite digitEqualsAtF-correct (suc bound) input digit
        | addF-correct previous
            (digitEqualsAtNat (suc bound) input digit) = refl

countDigitUpToF-correct :
  (bound digit input : ℕ) →
  evalPRF countDigitUpToF (bound ∷ digit ∷ input ∷ []) ≡
  countDigitUpToNat bound digit input
countDigitUpToF-correct zero digit input =
  countDigitBaseF-correct digit input
countDigitUpToF-correct (suc bound) digit input
  rewrite countDigitUpToF-correct bound digit input
        | countDigitStepF-correct
            bound
            (countDigitUpToNat bound digit input)
            digit
            input = refl

countDigitUpToNat-as-digits :
  (bound digit : ℕ) → (ds : List Digit) → (rest : ℕ) →
  countDigitUpToNat bound digit (appendDigitsWithRest ds rest) ≡
  countDigitDigitsUpTo bound digit ds rest
countDigitUpToNat-as-digits zero digit ds rest
  rewrite digitAtDigitsWithRest-correct zero ds rest = refl
countDigitUpToNat-as-digits (suc bound) digit ds rest
  rewrite countDigitUpToNat-as-digits bound digit ds rest
        | digitAtDigitsWithRest-correct (suc bound) ds rest = refl

countDigitUpToNat-historyCode-nonzero :
  (history : List ℕ) → (target : ℕ) →
  countDigitUpToNat
    (History.historyCode history)
    (suc target)
    (History.historyCode history)
  ≡ countDigitDigits (suc target) (natListDigits history)
countDigitUpToNat-historyCode-nonzero history target
  rewrite historyCode-as-digits history
        | countDigitUpToNat-as-digits
            (appendDigitsWithRest (natListDigits history) zero)
            (suc target)
            (natListDigits history)
            zero
  with scanBound≤natListCode history
... | extra ,Σ eq rewrite eq =
  countDigitDigitsUpTo-complete-nonzero
    (natListDigits history)
    extra
    target

seqLengthNat-historyCode :
  (history : List ℕ) →
  seqLengthNat (History.historyCode history) ≡
  History.historyLength history
seqLengthNat-historyCode history
  rewrite countDigitUpToNat-historyCode-nonzero history zero
        | countDigitDigits-d1-natListDigits history = refl

seqLengthF-correct-to-meta :
  (input : ℕ) →
  evalPRF seqLengthF (input ∷ []) ≡ seqLengthNat input
seqLengthF-correct-to-meta input =
  countDigitUpToF-correct input (suc zero) input

digit2AtF-correct :
  (position input index : ℕ) →
  evalPRF digit2AtF (position ∷ input ∷ index ∷ []) ≡
  digitEqualsAtNat position input (suc (suc zero))
digit2AtF-correct position input index =
  digitEqualsAtF-correct position input (suc (suc zero))

d1CountAtF-correct :
  (position input index : ℕ) →
  evalPRF d1CountAtF (position ∷ input ∷ index ∷ []) ≡
  countDigitUpToNat position (suc zero) input
d1CountAtF-correct position input index =
  countDigitUpToF-correct position (suc zero) input

d3CountAtF-correct :
  (position input index : ℕ) →
  evalPRF d3CountAtF (position ∷ input ∷ index ∷ []) ≡
  countDigitUpToNat position (suc (suc (suc zero))) input
d3CountAtF-correct position input index =
  countDigitUpToF-correct position (suc (suc (suc zero))) input

seqNthActiveAtF-correct :
  (position input index : ℕ) →
  evalPRF seqNthActiveAtF (position ∷ input ∷ index ∷ []) ≡
  seqNthActiveAtNat position input index
seqNthActiveAtF-correct position input index
  rewrite digit2AtF-correct position input index
        | d1CountAtF-correct position input index
        | d3CountAtF-correct position input index
        | eqNatF-correct
            (countDigitUpToNat position (suc zero) input)
            (suc index)
        | eqNatF-correct
            (countDigitUpToNat position (suc (suc (suc zero))) input)
            index
        | andF-correct
            (eqNatNat
              (countDigitUpToNat position (suc zero) input)
              (suc index))
            (eqNatNat
              (countDigitUpToNat position (suc (suc (suc zero))) input)
              index)
        | andF-correct
            (digitEqualsAtNat position input (suc (suc zero)))
            (mulNat
              (eqNatNat
                (countDigitUpToNat position (suc zero) input)
                (suc index))
              (eqNatNat
                (countDigitUpToNat position (suc (suc (suc zero))) input)
                index)) = refl

seqNthBaseF-correct :
  (input index : ℕ) →
  evalPRF seqNthBaseF (input ∷ index ∷ []) ≡
  seqNthSumNat zero input index
seqNthBaseF-correct input index =
  seqNthActiveAtF-correct zero input index

seqNthStepF-correct :
  (bound previous input index : ℕ) →
  evalPRF seqNthStepF (bound ∷ previous ∷ input ∷ index ∷ []) ≡
  previous + seqNthActiveAtNat (suc bound) input index
seqNthStepF-correct bound previous input index
  rewrite seqNthActiveAtF-correct (suc bound) input index
        | addF-correct previous
            (seqNthActiveAtNat (suc bound) input index) = refl

seqNthSumF-correct :
  (bound input index : ℕ) →
  evalPRF seqNthSumF (bound ∷ input ∷ index ∷ []) ≡
  seqNthSumNat bound input index
seqNthSumF-correct zero input index =
  seqNthBaseF-correct input index
seqNthSumF-correct (suc bound) input index
  rewrite seqNthSumF-correct bound input index
        | seqNthStepF-correct
            bound
            (seqNthSumNat bound input index)
            input
            index = refl

seqNthActiveAtNat-as-digits :
  (position : ℕ) → (ds : List Digit) → (index : ℕ) →
  seqNthActiveAtNat
    position
    (appendDigitsWithRest ds zero)
    index
  ≡ seqNthActiveDigitsAt position ds index
seqNthActiveAtNat-as-digits position ds index
  rewrite digitAtDigitsWithRest-correct position ds zero
        | countDigitUpToNat-as-digits
            position
            (suc zero)
            ds
            zero
        | countDigitUpToNat-as-digits
            position
            (suc (suc (suc zero)))
            ds
            zero = refl

seqNthSumNat-as-digits :
  (bound : ℕ) → (ds : List Digit) → (index : ℕ) →
  seqNthSumNat
    bound
    (appendDigitsWithRest ds zero)
    index
  ≡ seqNthDigitsUpTo bound ds index
seqNthSumNat-as-digits zero ds index =
  seqNthActiveAtNat-as-digits zero ds index
seqNthSumNat-as-digits (suc bound) ds index
  rewrite seqNthSumNat-as-digits bound ds index
        | seqNthActiveAtNat-as-digits (suc bound) ds index =
  refl

seqNthNat-historyCode-as-digits :
  (history : List ℕ) → (index : ℕ) →
  seqNthNat (History.historyCode history) index ≡
  seqNthDigitsUpTo
    (scanBound (natListDigits history))
    (natListDigits history)
    index
seqNthNat-historyCode-as-digits history index
  rewrite historyCode-as-digits history
        | seqNthSumNat-as-digits
            (appendDigitsWithRest (natListDigits history) zero)
            (natListDigits history)
            index
  with scanBound≤natListCode history
... | extra ,Σ eq rewrite eq =
  seqNthDigitsUpTo-complete (natListDigits history) extra index

seqNthF-correct-to-meta :
  (input index : ℕ) →
  evalPRF seqNthF (input ∷ index ∷ []) ≡ seqNthNat input index
seqNthF-correct-to-meta input index =
  seqNthSumF-correct input input index
