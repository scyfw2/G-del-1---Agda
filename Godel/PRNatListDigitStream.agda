{-# OPTIONS --safe #-}

module Godel.PRNatListDigitStream where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List using (List; []; _∷_)
open import Godel.Core
open import Godel.PRArithmeticSemantics
  using (eqNatNat; mulNat; lessEqNat; lessEqNat-refl; +-zeroʳ)
open import Godel.PRDigitCoding using (digitToNat)
open import Godel.PRDigitSemantics
open import Godel.CanonicalCoding
  using
    ( Digit; d0; d1; d2; d3
    ; appendDigit; encodeNatWithRest
    ; +-assoc; +-sucʳ
    ; _≤_; ≤-refl; ≤-step; ≤-suc; ≤-trans
    ; n≤appendDigit; suc≤appendDigit₂
    )
import Godel.PRHistoryCoding as History

infixr 5 _++ᵈ_

_++ᵈ_ : List Digit → List Digit → List Digit
[] ++ᵈ ys = ys
(x ∷ xs) ++ᵈ ys = x ∷ (xs ++ᵈ ys)

appendDigitsWithRest : List Digit → ℕ → ℕ
appendDigitsWithRest [] rest = rest
appendDigitsWithRest (d ∷ ds) rest =
  appendDigit d (appendDigitsWithRest ds rest)

natDigits : ℕ → List Digit
natDigits zero = d3 ∷ []
natDigits (suc n) = d2 ∷ natDigits n

natListDigits : List ℕ → List Digit
natListDigits [] = d0 ∷ []
natListDigits (x ∷ xs) =
  d1 ∷ (natDigits x ++ᵈ natListDigits xs)

digitsLength : List Digit → ℕ
digitsLength [] = zero
digitsLength (d ∷ ds) = suc (digitsLength ds)

scanBound : List Digit → ℕ
scanBound [] = zero
scanBound (d ∷ ds) = digitsLength ds

appendDigitsWithRest-++ :
  (xs ys : List Digit) → (rest : ℕ) →
  appendDigitsWithRest (xs ++ᵈ ys) rest ≡
  appendDigitsWithRest xs (appendDigitsWithRest ys rest)
appendDigitsWithRest-++ [] ys rest = refl
appendDigitsWithRest-++ (x ∷ xs) ys rest
  rewrite appendDigitsWithRest-++ xs ys rest = refl

digitsLength-++ :
  (xs ys : List Digit) →
  digitsLength (xs ++ᵈ ys) ≡ digitsLength xs + digitsLength ys
digitsLength-++ [] ys = refl
digitsLength-++ (x ∷ xs) ys =
  cong suc (digitsLength-++ xs ys)

digitsLength-natListDigits :
  (xs : List ℕ) →
  digitsLength (natListDigits xs) ≡
  suc (scanBound (natListDigits xs))
digitsLength-natListDigits [] = refl
digitsLength-natListDigits (x ∷ xs) = refl

suc²≤appendDigit₂ :
  (n : ℕ) → suc (suc n) ≤ appendDigit d2 n
suc²≤appendDigit₂ zero = ≤-refl (suc (suc zero))
suc²≤appendDigit₂ (suc n) =
  ≤-step (≤-step (≤-step (≤-suc (suc²≤appendDigit₂ n))))

suc²≤appendDigit₃ :
  (n : ℕ) → suc (suc n) ≤ appendDigit d3 n
suc²≤appendDigit₃ zero = ≤-step (≤-refl (suc (suc zero)))
suc²≤appendDigit₃ (suc n) =
  ≤-step (≤-step (≤-step (≤-suc (suc²≤appendDigit₃ n))))

encodeNatWithRest-as-digits :
  (n rest : ℕ) →
  encodeNatWithRest n rest ≡
  appendDigitsWithRest (natDigits n) rest
encodeNatWithRest-as-digits zero rest = refl
encodeNatWithRest-as-digits (suc n) rest
  rewrite encodeNatWithRest-as-digits n rest = refl

encodeNatListWithRest-as-digits :
  (xs : List ℕ) → (rest : ℕ) →
  History.encodeNatListWithRest xs rest ≡
  appendDigitsWithRest (natListDigits xs) rest
encodeNatListWithRest-as-digits [] rest = refl
encodeNatListWithRest-as-digits (x ∷ xs) rest
  rewrite encodeNatWithRest-as-digits
            x
            (History.encodeNatListWithRest xs rest)
        | encodeNatListWithRest-as-digits xs rest
        | appendDigitsWithRest-++ (natDigits x) (natListDigits xs) rest =
  refl

historyCode-as-digits :
  (xs : List ℕ) →
  History.historyCode xs ≡
  appendDigitsWithRest (natListDigits xs) zero
historyCode-as-digits xs = encodeNatListWithRest-as-digits xs zero

mutual
  scanBound≤natListCode :
    (xs : List ℕ) →
    scanBound (natListDigits xs) ≤
    appendDigitsWithRest (natListDigits xs) zero
  scanBound≤natListCode [] = ≤-refl zero
  scanBound≤natListCode (x ∷ xs) =
    ≤-trans
      (digitsLengthNatTail≤natTailCode x xs)
      (n≤appendDigit d1
        (appendDigitsWithRest (natDigits x ++ᵈ natListDigits xs) zero))

  digitsLengthNatTail≤natTailCode :
    (x : ℕ) → (xs : List ℕ) →
    digitsLength (natDigits x ++ᵈ natListDigits xs) ≤
    appendDigitsWithRest (natDigits x ++ᵈ natListDigits xs) zero
  digitsLengthNatTail≤natTailCode zero xs
    rewrite appendDigitsWithRest-++ (natDigits zero) (natListDigits xs) zero
          | digitsLength-natListDigits xs =
    ≤-trans
      (≤-suc (≤-suc (scanBound≤natListCode xs)))
      (suc²≤appendDigit₃
        (appendDigitsWithRest (natListDigits xs) zero))
  digitsLengthNatTail≤natTailCode (suc x) xs
    rewrite appendDigitsWithRest-++ (natDigits (suc x)) (natListDigits xs) zero
          | sym (appendDigitsWithRest-++ (natDigits x) (natListDigits xs) zero) =
    ≤-trans
      (≤-suc (digitsLengthNatTail≤natTailCode x xs))
      (suc≤appendDigit₂
        (appendDigitsWithRest (natDigits x ++ᵈ natListDigits xs) zero))

digitAtDigitsWithRest : ℕ → List Digit → ℕ → ℕ
digitAtDigitsWithRest position [] rest = digitAtNat position rest
digitAtDigitsWithRest zero (d ∷ ds) rest = digitToNat d
digitAtDigitsWithRest (suc position) (d ∷ ds) rest =
  digitAtDigitsWithRest position ds rest

digitAtDigitsWithRest-correct :
  (position : ℕ) → (ds : List Digit) → (rest : ℕ) →
  digitAtNat position (appendDigitsWithRest ds rest) ≡
  digitAtDigitsWithRest position ds rest
digitAtDigitsWithRest-correct position [] rest = refl
digitAtDigitsWithRest-correct zero (d ∷ ds) rest =
  digitAt-appendDigit-head d (appendDigitsWithRest ds rest)
digitAtDigitsWithRest-correct (suc position) (d ∷ ds) rest
  rewrite digitAt-appendDigit-tail
            position d (appendDigitsWithRest ds rest) =
  digitAtDigitsWithRest-correct position ds rest

iterDiv4Nat-zero :
  (position : ℕ) → iterDiv4Nat position zero ≡ zero
iterDiv4Nat-zero zero = refl
iterDiv4Nat-zero (suc position)
  rewrite iterDiv4Nat-zero position = refl

digitAtNat-zero :
  (position : ℕ) → digitAtNat position zero ≡ zero
digitAtNat-zero position
  rewrite iterDiv4Nat-zero position = refl

digitAtDigits-after-scanBound :
  (ds : List Digit) → (extra : ℕ) →
  digitAtDigitsWithRest (suc (scanBound ds + extra)) ds zero ≡ zero
digitAtDigits-after-scanBound [] extra =
  digitAtNat-zero (suc extra)
digitAtDigits-after-scanBound (d ∷ []) extra =
  digitAtNat-zero extra
digitAtDigits-after-scanBound (d ∷ e ∷ ds) extra =
  digitAtDigits-after-scanBound (e ∷ ds) extra

digitMatch : ℕ → Digit → ℕ
digitMatch digit d = eqNatNat (digitToNat d) digit

countDigitDigits : ℕ → List Digit → ℕ
countDigitDigits digit [] = zero
countDigitDigits digit (d ∷ ds) =
  digitMatch digit d + countDigitDigits digit ds

countDigitDigits-++ :
  (digit : ℕ) → (xs ys : List Digit) →
  countDigitDigits digit (xs ++ᵈ ys) ≡
  countDigitDigits digit xs + countDigitDigits digit ys
countDigitDigits-++ digit [] ys = refl
countDigitDigits-++ digit (x ∷ xs) ys
  rewrite countDigitDigits-++ digit xs ys
        | +-assoc
            (digitMatch digit x)
            (countDigitDigits digit xs)
            (countDigitDigits digit ys) =
  refl

countDigitDigits-d1-natDigits :
  (n : ℕ) →
  countDigitDigits (suc zero) (natDigits n) ≡ zero
countDigitDigits-d1-natDigits zero = refl
countDigitDigits-d1-natDigits (suc n) =
  countDigitDigits-d1-natDigits n

countDigitDigits-d1-natListDigits :
  (xs : List ℕ) →
  countDigitDigits (suc zero) (natListDigits xs) ≡
  History.historyLength xs
countDigitDigits-d1-natListDigits [] = refl
countDigitDigits-d1-natListDigits (x ∷ xs)
  rewrite countDigitDigits-++ (suc zero) (natDigits x) (natListDigits xs)
        | countDigitDigits-d1-natDigits x
        | countDigitDigits-d1-natListDigits xs = refl

countDigitDigitsUpTo : ℕ → ℕ → List Digit → ℕ → ℕ
countDigitDigitsUpTo zero digit ds rest =
  eqNatNat (digitAtDigitsWithRest zero ds rest) digit
countDigitDigitsUpTo (suc bound) digit ds rest =
  countDigitDigitsUpTo bound digit ds rest +
  eqNatNat (digitAtDigitsWithRest (suc bound) ds rest) digit

countDigitDigitsUpTo-empty-zero-nonzero :
  (bound target : ℕ) →
  countDigitDigitsUpTo bound (suc target) [] zero ≡ zero
countDigitDigitsUpTo-empty-zero-nonzero zero target = refl
countDigitDigitsUpTo-empty-zero-nonzero (suc bound) target
  rewrite countDigitDigitsUpTo-empty-zero-nonzero bound target
        | digitAtNat-zero (suc bound) = refl

countDigitDigitsUpTo-suc-cons :
  (bound digit : ℕ) → (d : Digit) → (ds : List Digit) →
  countDigitDigitsUpTo (suc bound) digit (d ∷ ds) zero ≡
  digitMatch digit d + countDigitDigitsUpTo bound digit ds zero
countDigitDigitsUpTo-suc-cons zero digit d ds = refl
countDigitDigitsUpTo-suc-cons (suc bound) digit d ds
  rewrite countDigitDigitsUpTo-suc-cons bound digit d ds
        | +-assoc
            (digitMatch digit d)
            (countDigitDigitsUpTo bound digit ds zero)
            (eqNatNat (digitAtDigitsWithRest (suc bound) ds zero) digit) =
  refl

countDigitDigitsUpTo-complete-cons-nonzero :
  (d : Digit) → (ds : List Digit) → (extra target : ℕ) →
  countDigitDigitsUpTo (digitsLength ds + extra) (suc target)
    (d ∷ ds) zero
  ≡ countDigitDigits (suc target) (d ∷ ds)
countDigitDigitsUpTo-complete-cons-nonzero d [] zero target
  rewrite +-zeroʳ (digitMatch (suc target) d) = refl
countDigitDigitsUpTo-complete-cons-nonzero d [] (suc extra) target
  rewrite countDigitDigitsUpTo-complete-cons-nonzero d [] extra target
        | digitAtDigits-after-scanBound (d ∷ []) extra
        | +-zeroʳ (digitMatch (suc target) d + zero)
        | +-zeroʳ (digitMatch (suc target) d) =
  refl
countDigitDigitsUpTo-complete-cons-nonzero d (e ∷ ds) extra target
  rewrite countDigitDigitsUpTo-suc-cons
            (digitsLength ds + extra)
            (suc target)
            d
            (e ∷ ds)
        | countDigitDigitsUpTo-complete-cons-nonzero
            e ds extra target =
  refl

countDigitDigitsUpTo-complete-nonzero :
  (ds : List Digit) → (extra target : ℕ) →
  countDigitDigitsUpTo (scanBound ds + extra) (suc target) ds zero ≡
  countDigitDigits (suc target) ds
countDigitDigitsUpTo-complete-nonzero [] extra target =
  countDigitDigitsUpTo-empty-zero-nonzero extra target
countDigitDigitsUpTo-complete-nonzero (d ∷ ds) extra target =
  countDigitDigitsUpTo-complete-cons-nonzero d ds extra target

seqNthActiveDigitsAt : ℕ → List Digit → ℕ → ℕ
seqNthActiveDigitsAt position ds index =
  mulNat
    (eqNatNat
      (digitAtDigitsWithRest position ds zero)
      (suc (suc zero)))
    (mulNat
      (eqNatNat
        (countDigitDigitsUpTo position (suc zero) ds zero)
        (suc index))
      (eqNatNat
        (countDigitDigitsUpTo position (suc (suc (suc zero))) ds zero)
        index))

seqNthDigitsUpTo : ℕ → List Digit → ℕ → ℕ
seqNthDigitsUpTo zero ds index =
  seqNthActiveDigitsAt zero ds index
seqNthDigitsUpTo (suc bound) ds index =
  seqNthDigitsUpTo bound ds index +
  seqNthActiveDigitsAt (suc bound) ds index

seqNthActiveDigits-after-scanBound :
  (ds : List Digit) → (extra index : ℕ) →
  seqNthActiveDigitsAt (suc (scanBound ds + extra)) ds index ≡ zero
seqNthActiveDigits-after-scanBound ds extra index
  rewrite digitAtDigits-after-scanBound ds extra = refl

seqNthDigitsUpTo-complete :
  (ds : List Digit) → (extra index : ℕ) →
  seqNthDigitsUpTo (scanBound ds + extra) ds index ≡
  seqNthDigitsUpTo (scanBound ds) ds index
seqNthDigitsUpTo-complete [] zero index = refl
seqNthDigitsUpTo-complete [] (suc extra) index
  rewrite +-sucʳ (scanBound []) extra
        | seqNthDigitsUpTo-complete [] extra index
        | seqNthActiveDigits-after-scanBound [] extra index
        | +-zeroʳ (seqNthDigitsUpTo (scanBound []) [] index) =
  refl
seqNthDigitsUpTo-complete (d ∷ ds) zero index
  rewrite +-zeroʳ (scanBound (d ∷ ds)) = refl
seqNthDigitsUpTo-complete (d ∷ ds) (suc extra) index
  rewrite +-sucʳ (scanBound (d ∷ ds)) extra
        | seqNthDigitsUpTo-complete (d ∷ ds) extra index
        | seqNthActiveDigits-after-scanBound (d ∷ ds) extra index
        | +-zeroʳ (seqNthDigitsUpTo (scanBound (d ∷ ds)) (d ∷ ds) index) =
  refl

incD1 : Digit → ℕ → ℕ
incD1 d0 n = n
incD1 d1 n = suc n
incD1 d2 n = n
incD1 d3 n = n

incD3 : Digit → ℕ → ℕ
incD3 d0 n = n
incD3 d1 n = n
incD3 d2 n = n
incD3 d3 n = suc n

activeHeadCtx : Digit → ℕ → ℕ → ℕ → ℕ
activeHeadCtx d index d1-count d3-count =
  mulNat
    (digitMatch (suc (suc zero)) d)
    (mulNat
      (eqNatNat (incD1 d d1-count) (suc index))
      (eqNatNat (incD3 d d3-count) index))

eqNatNat-refl :
  (n : ℕ) → eqNatNat n n ≡ suc zero
eqNatNat-refl n rewrite lessEqNat-refl n = refl

mulNat-zeroʳ :
  (n : ℕ) → mulNat n zero ≡ zero
mulNat-zeroʳ zero = refl
mulNat-zeroʳ (suc n) rewrite mulNat-zeroʳ n = refl

lessEqNat-suc-plus-left :
  (offset index : ℕ) →
  lessEqNat (suc (offset + index)) offset ≡ zero
lessEqNat-suc-plus-left zero index = refl
lessEqNat-suc-plus-left (suc offset) index =
  lessEqNat-suc-plus-left offset index

eqNatNat-offset-suc-plus :
  (offset index : ℕ) →
  eqNatNat offset (suc (offset + index)) ≡ zero
eqNatNat-offset-suc-plus offset index
  rewrite lessEqNat-suc-plus-left offset index
        | mulNat-zeroʳ (lessEqNat offset (suc (offset + index))) = refl

lessEqNat-suc-left :
  (n : ℕ) → lessEqNat (suc n) n ≡ zero
lessEqNat-suc-left zero = refl
lessEqNat-suc-left (suc n) = lessEqNat-suc-left n

eqNatNat-suc-left :
  (n : ℕ) → eqNatNat (suc n) n ≡ zero
eqNatNat-suc-left n
  rewrite lessEqNat-suc-left n
        | mulNat-zeroʳ (lessEqNat n (suc n)) = refl

eqNatNat-suc-plus-left :
  (target extra : ℕ) →
  eqNatNat (suc (target + extra)) target ≡ zero
eqNatNat-suc-plus-left target extra
  rewrite lessEqNat-suc-plus-left target extra = refl

digitMatch-d2-d0 : digitMatch (suc (suc zero)) d0 ≡ zero
digitMatch-d2-d0 = refl

digitMatch-d2-d1 : digitMatch (suc (suc zero)) d1 ≡ zero
digitMatch-d2-d1 = refl

digitMatch-d2-d2 : digitMatch (suc (suc zero)) d2 ≡ suc zero
digitMatch-d2-d2 = refl

digitMatch-d2-d3 : digitMatch (suc (suc zero)) d3 ≡ zero
digitMatch-d2-d3 = refl

scanAllCtx : List Digit → ℕ → ℕ → ℕ → ℕ
scanAllCtx [] index d1-count d3-count = zero
scanAllCtx (d ∷ ds) index d1-count d3-count =
  activeHeadCtx d index d1-count d3-count +
  scanAllCtx ds index (incD1 d d1-count) (incD3 d d3-count)

advanceD1 : List Digit → ℕ → ℕ
advanceD1 [] n = n
advanceD1 (d ∷ ds) n = advanceD1 ds (incD1 d n)

advanceD3 : List Digit → ℕ → ℕ
advanceD3 [] n = n
advanceD3 (d ∷ ds) n = advanceD3 ds (incD3 d n)

scanAllCtx-++ :
  (xs ys : List Digit) → (index d1-count d3-count : ℕ) →
  scanAllCtx (xs ++ᵈ ys) index d1-count d3-count ≡
  scanAllCtx xs index d1-count d3-count +
  scanAllCtx ys index (advanceD1 xs d1-count) (advanceD3 xs d3-count)
scanAllCtx-++ [] ys index d1-count d3-count = refl
scanAllCtx-++ (d ∷ ds) ys index d1-count d3-count
  rewrite scanAllCtx-++ ds ys index (incD1 d d1-count) (incD3 d d3-count)
        | +-assoc
            (activeHeadCtx d index d1-count d3-count)
            (scanAllCtx ds index (incD1 d d1-count) (incD3 d d3-count))
            (scanAllCtx ys index
              (advanceD1 ds (incD1 d d1-count))
              (advanceD3 ds (incD3 d d3-count))) =
  refl

advanceD1-natDigits :
  (n offset : ℕ) →
  advanceD1 (natDigits n) offset ≡ offset
advanceD1-natDigits zero offset = refl
advanceD1-natDigits (suc n) offset =
  advanceD1-natDigits n offset

advanceD3-natDigits :
  (n offset : ℕ) →
  advanceD3 (natDigits n) offset ≡ suc offset
advanceD3-natDigits zero offset = refl
advanceD3-natDigits (suc n) offset =
  advanceD3-natDigits n offset

scanAllCtx-natDigits-hit :
  (n offset : ℕ) →
  scanAllCtx (natDigits n) offset (suc offset) offset ≡ n
scanAllCtx-natDigits-hit zero offset = refl
scanAllCtx-natDigits-hit (suc n) offset
  rewrite eqNatNat-refl (suc offset)
        | eqNatNat-refl offset
        | scanAllCtx-natDigits-hit n offset = refl

scanAllCtx-natDigits-miss-after :
  (n offset index : ℕ) →
  scanAllCtx (natDigits n) (suc (offset + index)) (suc offset) offset ≡
  zero
scanAllCtx-natDigits-miss-after zero offset index = refl
scanAllCtx-natDigits-miss-after (suc n) offset index
  rewrite eqNatNat-offset-suc-plus offset index
        | scanAllCtx-natDigits-miss-after n offset index = refl

scanAllCtx-natDigits-past :
  (n offset : ℕ) →
  scanAllCtx (natDigits n) offset (suc (suc offset)) (suc offset) ≡
  zero
scanAllCtx-natDigits-past zero offset = refl
scanAllCtx-natDigits-past (suc n) offset
  rewrite eqNatNat-suc-left offset
        | scanAllCtx-natDigits-past n offset = refl

scanAllCtx-natDigits-past-general :
  (n target extra : ℕ) →
  scanAllCtx
    (natDigits n)
    target
    (suc (target + extra))
    (suc (target + extra))
  ≡ zero
scanAllCtx-natDigits-past-general zero target extra
  rewrite digitMatch-d2-d3 = refl
scanAllCtx-natDigits-past-general (suc n) target extra
  rewrite eqNatNat-suc-plus-left target extra
        | mulNat-zeroʳ
            (eqNatNat (suc (target + extra)) (suc target))
        | mulNat-zeroʳ (digitMatch (suc (suc zero)) d2)
        | scanAllCtx-natDigits-past-general n target extra = refl

scanAllCtx-natDigits-pastD3 :
  (n target extra d1-count : ℕ) →
  scanAllCtx
    (natDigits n)
    target
    d1-count
    (suc (target + extra))
  ≡ zero
scanAllCtx-natDigits-pastD3 zero target extra d1-count
  rewrite digitMatch-d2-d3 = refl
scanAllCtx-natDigits-pastD3 (suc n) target extra d1-count
  rewrite eqNatNat-suc-plus-left target extra
        | mulNat-zeroʳ (eqNatNat d1-count (suc target))
        | mulNat-zeroʳ (digitMatch (suc (suc zero)) d2)
        | scanAllCtx-natDigits-pastD3 n target extra d1-count =
  refl

scanAllCtx-natListDigits-past-general :
  (xs : List ℕ) → (target extra : ℕ) →
  scanAllCtx
    (natListDigits xs)
    target
    (suc (target + extra))
    (suc (target + extra))
  ≡ zero
scanAllCtx-natListDigits-past-general [] target extra = refl
scanAllCtx-natListDigits-past-general (x ∷ xs) target extra
  rewrite scanAllCtx-++ (natDigits x) (natListDigits xs)
            target
            (suc (suc (target + extra)))
            (suc (target + extra))
        | scanAllCtx-natDigits-pastD3
            x target extra (suc (suc (target + extra)))
        | advanceD1-natDigits x (suc (suc (target + extra)))
        | advanceD3-natDigits x (suc (target + extra))
        | sym (+-sucʳ target extra)
        | scanAllCtx-natListDigits-past-general xs target (suc extra) =
  refl

scanAllCtx-natListDigits-past :
  (xs : List ℕ) → (offset : ℕ) →
  scanAllCtx (natListDigits xs) offset (suc offset) (suc offset) ≡ zero
scanAllCtx-natListDigits-past xs offset =
  subst
    (λ n →
      scanAllCtx (natListDigits xs) offset (suc n) (suc n) ≡ zero)
    (+-zeroʳ offset)
    (scanAllCtx-natListDigits-past-general xs offset zero)

ctxCount : ℕ → ℕ → List Digit → ℕ → ℕ
ctxCount position digit ds prefix =
  countDigitDigitsUpTo position digit ds zero + prefix

seqNthActiveDigitsAtCountCtx :
  ℕ → List Digit → ℕ → ℕ → ℕ → ℕ
seqNthActiveDigitsAtCountCtx position ds index d1-count d3-count =
  mulNat
    (eqNatNat
      (digitAtDigitsWithRest position ds zero)
      (suc (suc zero)))
    (mulNat
      (eqNatNat
        (ctxCount position (suc zero) ds d1-count)
        (suc index))
      (eqNatNat
        (ctxCount position (suc (suc (suc zero))) ds d3-count)
        index))

seqNthDigitsUpToCountCtx :
  ℕ → List Digit → ℕ → ℕ → ℕ → ℕ
seqNthDigitsUpToCountCtx zero ds index d1-count d3-count =
  seqNthActiveDigitsAtCountCtx zero ds index d1-count d3-count
seqNthDigitsUpToCountCtx (suc bound) ds index d1-count d3-count =
  seqNthDigitsUpToCountCtx bound ds index d1-count d3-count +
  seqNthActiveDigitsAtCountCtx (suc bound) ds index d1-count d3-count

ctxCount-zero-prefix :
  (position digit : ℕ) → (ds : List Digit) →
  ctxCount position digit ds zero ≡
  countDigitDigitsUpTo position digit ds zero
ctxCount-zero-prefix position digit ds =
  +-zeroʳ (countDigitDigitsUpTo position digit ds zero)

seqNthActiveDigitsAtCountCtx-zero :
  (position : ℕ) → (ds : List Digit) → (index : ℕ) →
  seqNthActiveDigitsAtCountCtx position ds index zero zero ≡
  seqNthActiveDigitsAt position ds index
seqNthActiveDigitsAtCountCtx-zero position ds index
  rewrite ctxCount-zero-prefix position (suc zero) ds
        | ctxCount-zero-prefix position (suc (suc (suc zero))) ds =
  refl

seqNthDigitsUpToCountCtx-zero :
  (bound : ℕ) → (ds : List Digit) → (index : ℕ) →
  seqNthDigitsUpToCountCtx bound ds index zero zero ≡
  seqNthDigitsUpTo bound ds index
seqNthDigitsUpToCountCtx-zero zero ds index =
  seqNthActiveDigitsAtCountCtx-zero zero ds index
seqNthDigitsUpToCountCtx-zero (suc bound) ds index
  rewrite seqNthDigitsUpToCountCtx-zero bound ds index
        | seqNthActiveDigitsAtCountCtx-zero (suc bound) ds index =
  refl

ctxCount-zero-cons-d1 :
  (d : Digit) → (ds : List Digit) → (prefix : ℕ) →
  ctxCount zero (suc zero) (d ∷ ds) prefix ≡ incD1 d prefix
ctxCount-zero-cons-d1 d0 ds prefix = refl
ctxCount-zero-cons-d1 d1 ds prefix = refl
ctxCount-zero-cons-d1 d2 ds prefix = refl
ctxCount-zero-cons-d1 d3 ds prefix = refl

ctxCount-zero-cons-d3 :
  (d : Digit) → (ds : List Digit) → (prefix : ℕ) →
  ctxCount zero (suc (suc (suc zero))) (d ∷ ds) prefix ≡
  incD3 d prefix
ctxCount-zero-cons-d3 d0 ds prefix = refl
ctxCount-zero-cons-d3 d1 ds prefix = refl
ctxCount-zero-cons-d3 d2 ds prefix = refl
ctxCount-zero-cons-d3 d3 ds prefix = refl

ctxCount-suc-cons-d1 :
  (position : ℕ) → (d : Digit) → (ds : List Digit) → (prefix : ℕ) →
  ctxCount (suc position) (suc zero) (d ∷ ds) prefix ≡
  ctxCount position (suc zero) ds (incD1 d prefix)
ctxCount-suc-cons-d1 position d0 ds prefix
  rewrite countDigitDigitsUpTo-suc-cons position (suc zero) d0 ds = refl
ctxCount-suc-cons-d1 position d1 ds prefix =
  trans
    (cong (λ n → n + prefix)
      (countDigitDigitsUpTo-suc-cons position (suc zero) d1 ds))
    (sym (+-sucʳ (countDigitDigitsUpTo position (suc zero) ds zero) prefix))
ctxCount-suc-cons-d1 position d2 ds prefix
  rewrite countDigitDigitsUpTo-suc-cons position (suc zero) d2 ds = refl
ctxCount-suc-cons-d1 position d3 ds prefix
  rewrite countDigitDigitsUpTo-suc-cons position (suc zero) d3 ds = refl

ctxCount-suc-cons-d3 :
  (position : ℕ) → (d : Digit) → (ds : List Digit) → (prefix : ℕ) →
  ctxCount (suc position) (suc (suc (suc zero))) (d ∷ ds) prefix ≡
  ctxCount position (suc (suc (suc zero))) ds (incD3 d prefix)
ctxCount-suc-cons-d3 position d0 ds prefix
  rewrite countDigitDigitsUpTo-suc-cons
            position (suc (suc (suc zero))) d0 ds = refl
ctxCount-suc-cons-d3 position d1 ds prefix
  rewrite countDigitDigitsUpTo-suc-cons
            position (suc (suc (suc zero))) d1 ds = refl
ctxCount-suc-cons-d3 position d2 ds prefix
  rewrite countDigitDigitsUpTo-suc-cons
            position (suc (suc (suc zero))) d2 ds = refl
ctxCount-suc-cons-d3 position d3 ds prefix =
  trans
    (cong (λ n → n + prefix)
      (countDigitDigitsUpTo-suc-cons
        position (suc (suc (suc zero))) d3 ds))
    (sym
      (+-sucʳ
        (countDigitDigitsUpTo position (suc (suc (suc zero))) ds zero)
        prefix))

seqNthActiveDigitsAtCountCtx-zero-cons :
  (d : Digit) → (ds : List Digit) →
  (index d1-count d3-count : ℕ) →
  seqNthActiveDigitsAtCountCtx zero (d ∷ ds) index d1-count d3-count ≡
  activeHeadCtx d index d1-count d3-count
seqNthActiveDigitsAtCountCtx-zero-cons d ds index d1-count d3-count
  rewrite ctxCount-zero-cons-d1 d ds d1-count
        | ctxCount-zero-cons-d3 d ds d3-count = refl

seqNthActiveDigitsAtCountCtx-suc-cons :
  (position : ℕ) → (d : Digit) → (ds : List Digit) →
  (index d1-count d3-count : ℕ) →
  seqNthActiveDigitsAtCountCtx
    (suc position)
    (d ∷ ds)
    index
    d1-count
    d3-count
  ≡
  seqNthActiveDigitsAtCountCtx
    position
    ds
    index
    (incD1 d d1-count)
    (incD3 d d3-count)
seqNthActiveDigitsAtCountCtx-suc-cons
  position d ds index d1-count d3-count
  rewrite ctxCount-suc-cons-d1 position d ds d1-count
        | ctxCount-suc-cons-d3 position d ds d3-count = refl

seqNthDigitsUpToCountCtx-suc-cons :
  (bound : ℕ) → (d : Digit) → (ds : List Digit) →
  (index d1-count d3-count : ℕ) →
  seqNthDigitsUpToCountCtx
    (suc bound)
    (d ∷ ds)
    index
    d1-count
    d3-count
  ≡
  activeHeadCtx d index d1-count d3-count +
  seqNthDigitsUpToCountCtx
    bound
    ds
    index
    (incD1 d d1-count)
    (incD3 d d3-count)
seqNthDigitsUpToCountCtx-suc-cons zero d ds index d1-count d3-count
  rewrite seqNthActiveDigitsAtCountCtx-zero-cons d ds index d1-count d3-count
        | seqNthActiveDigitsAtCountCtx-suc-cons
            zero d ds index d1-count d3-count = refl
seqNthDigitsUpToCountCtx-suc-cons (suc bound) d ds index d1-count d3-count
  rewrite seqNthDigitsUpToCountCtx-suc-cons
            bound d ds index d1-count d3-count
        | seqNthActiveDigitsAtCountCtx-suc-cons
            (suc bound) d ds index d1-count d3-count
        | +-assoc
            (activeHeadCtx d index d1-count d3-count)
            (seqNthDigitsUpToCountCtx
              bound
              ds
              index
              (incD1 d d1-count)
              (incD3 d d3-count))
            (seqNthActiveDigitsAtCountCtx
              (suc bound)
              ds
              index
              (incD1 d d1-count)
              (incD3 d d3-count)) =
  refl

seqNthDigitsUpToCountCtx-scanAll-cons :
  (d : Digit) → (ds : List Digit) → (index d1-count d3-count : ℕ) →
  seqNthDigitsUpToCountCtx
    (digitsLength ds)
    (d ∷ ds)
    index
    d1-count
    d3-count
  ≡ scanAllCtx (d ∷ ds) index d1-count d3-count
seqNthDigitsUpToCountCtx-scanAll-cons d [] index d1-count d3-count
  rewrite seqNthActiveDigitsAtCountCtx-zero-cons d [] index d1-count d3-count
        | +-zeroʳ (activeHeadCtx d index d1-count d3-count) = refl
seqNthDigitsUpToCountCtx-scanAll-cons d (e ∷ ds) index d1-count d3-count
  rewrite seqNthDigitsUpToCountCtx-suc-cons
            (scanBound (e ∷ ds))
            d
            (e ∷ ds)
            index
            d1-count
            d3-count
        | seqNthDigitsUpToCountCtx-scanAll-cons
            e
            ds
            index
            (incD1 d d1-count)
            (incD3 d d3-count) =
  refl

seqNthDigitsUpToCountCtx-scanAll :
  (ds : List Digit) → (index d1-count d3-count : ℕ) →
  seqNthDigitsUpToCountCtx
    (scanBound ds)
    ds
    index
    d1-count
    d3-count
  ≡ scanAllCtx ds index d1-count d3-count
seqNthDigitsUpToCountCtx-scanAll [] index d1-count d3-count
  rewrite digitAtNat-zero zero
        | digitMatch-d2-d0 = refl
seqNthDigitsUpToCountCtx-scanAll (d ∷ ds) index d1-count d3-count =
  seqNthDigitsUpToCountCtx-scanAll-cons d ds index d1-count d3-count

seqNthDigitsUpTo-scanAll :
  (ds : List Digit) → (index : ℕ) →
  seqNthDigitsUpTo (scanBound ds) ds index ≡
  scanAllCtx ds index zero zero
seqNthDigitsUpTo-scanAll ds index =
  trans
    (sym (seqNthDigitsUpToCountCtx-zero (scanBound ds) ds index))
    (seqNthDigitsUpToCountCtx-scanAll ds index zero zero)

seqNthDigitsUpTo-natListDigits :
  (history : List ℕ) → (index : ℕ) →
  seqNthDigitsUpTo
    (scanBound (natListDigits history))
    (natListDigits history)
    index
  ≡ History.historyNthDefault history index zero
seqNthDigitsUpTo-natListDigits history index =
  trans
    (seqNthDigitsUpTo-scanAll (natListDigits history) index)
    (scanAll-main history zero index)
  where
    scanAll-main :
      (history : List ℕ) → (offset index : ℕ) →
      scanAllCtx (natListDigits history) (offset + index) offset offset ≡
      History.historyNthDefault history index zero
    scanAll-main [] offset index = refl
    scanAll-main (x ∷ xs) offset zero
      rewrite +-zeroʳ offset
            | scanAllCtx-++ (natDigits x) (natListDigits xs)
                offset
                (suc offset)
                offset
            | scanAllCtx-natDigits-hit x offset
            | advanceD1-natDigits x (suc offset)
            | advanceD3-natDigits x offset
            | scanAllCtx-natListDigits-past xs offset
            | +-zeroʳ x = refl
    scanAll-main (x ∷ xs) offset (suc index)
      rewrite +-sucʳ offset index
            | scanAllCtx-++ (natDigits x) (natListDigits xs)
                (suc (offset + index))
                (suc offset)
                offset
            | scanAllCtx-natDigits-miss-after x offset index
            | advanceD1-natDigits x (suc offset)
            | advanceD3-natDigits x offset
            | scanAll-main xs (suc offset) index = refl
