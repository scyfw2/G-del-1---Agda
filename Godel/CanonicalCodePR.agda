{-# OPTIONS --safe #-}

module Godel.CanonicalCodePR where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List using (List) renaming ([] to []ˡ; _∷_ to _∷ˡ_)
open import Godel.Core
open import Godel.Syntax
  using
    ( Term
    ; Formula
    ; zeroᵗ
    ; sucᵗ_
    ; numeral
    ; _≈_
    ; ¬ᶠ_
    )
open import Godel.PrimitiveRecursive
open import Godel.PRBooleanHelpers
open import Godel.PRBoundedSearch using (constF; twoF; threeF)
open import Godel.PRArithmeticSemantics
open import Godel.PRDigitCoding
open import Godel.PRDigitSemantics
open import Godel.PRNatListDecoder
  using (digitEqualsAtF; countDigitUpToF)
open import Godel.PRNatListDecoderSemantics
  using
    ( countDigitUpToNat
    ; digitEqualsAtF-correct
    ; countDigitUpToF-correct
    ; countDigitUpToNat-as-digits
    )
open import Godel.PRNatListDigitStream
  using
    ( appendDigitsWithRest
    ; natDigits
    ; scanBound
    ; digitsLength
    ; digitAtDigitsWithRest
    ; digitAtDigitsWithRest-correct
    ; countDigitDigitsUpTo
    ; encodeNatWithRest-as-digits
    ; mulNat-zeroʳ
    )
open import Godel.PRRepresentabilityFinal
  using (PARepresentsFunction; PARepresentsRelation; prf-represented)
open import Godel.PRFunctionGraph
  using
    ( functionGraphRel
    ; functionGraphRel-represented
    )
open import Godel.CanonicalCoding
  using
    ( Code
    ; Digit
    ; atom
    ; node
    ; encodeCode
    ; encodeCodeWithRest
    ; encodeNatWithRest
    ; encodeCodeListWithRest
    ; canonicalCodeTerm
    ; canonicalCodeFormula
    ; appendDigit
    ; d0
    ; d1
    ; d2
    ; d3
    ; _≤_
    ; ≤-refl
    ; ≤-step
    ; ≤-zero
    ; ≤-trans
    ; size≤encodeNatWithRest
    ; +-assoc
    ; +-sucʳ
    )

isAtomCodeF : PRF (suc zero)
isAtomCodeF = isDigit0F

isNodeCodeF : PRF (suc zero)
isNodeCodeF = isDigit1F

AtomHeadNat : ℕ → Set
AtomHeadNat input = mod4Nat input ≡ zero

NodeHeadNat : ℕ → Set
NodeHeadNat input = mod4Nat input ≡ suc zero

CodeListNilHeadNat : ℕ → Set
CodeListNilHeadNat input = mod4Nat input ≡ zero

CodeListConsHeadNat : ℕ → Set
CodeListConsHeadNat input = mod4Nat input ≡ suc zero

eqNatNat-refl-code :
  (n : ℕ) → eqNatNat n n ≡ suc zero
eqNatNat-refl-code zero = refl
eqNatNat-refl-code (suc n) = eqNatNat-refl-code n

eqNatNat-sound-code :
  (m n : ℕ) → eqNatNat m n ≡ suc zero → m ≡ n
eqNatNat-sound-code zero zero eq = refl
eqNatNat-sound-code zero (suc n) ()
eqNatNat-sound-code (suc m) zero ()
eqNatNat-sound-code (suc m) (suc n) eq =
  cong suc (eqNatNat-sound-code m n eq)

isDigitF-correct :
  (d input : ℕ) →
  evalPRF (isDigitF d) (input ∷ []) ≡ eqNatNat (mod4Nat input) d
isDigitF-correct d input
  rewrite mod4F-correct input
        | constF-correct d (input ∷ [])
        | eqNatF-correct (mod4Nat input) d = refl

isAtomCodeF-complete-head :
  (input : ℕ) → AtomHeadNat input →
  PRRel-holds (rel isAtomCodeF) (input ∷ [])
isAtomCodeF-complete-head input atom-head
  rewrite isDigitF-correct zero input
        | atom-head
        | eqNatNat-refl-code zero = refl

isAtomCodeF-sound-head :
  (input : ℕ) →
  PRRel-holds (rel isAtomCodeF) (input ∷ []) →
  AtomHeadNat input
isAtomCodeF-sound-head input holds =
  eqNatNat-sound-code
    (mod4Nat input)
    zero
    (trans (sym (isDigitF-correct zero input)) holds)

isNodeCodeF-complete-head :
  (input : ℕ) → NodeHeadNat input →
  PRRel-holds (rel isNodeCodeF) (input ∷ [])
isNodeCodeF-complete-head input node-head
  rewrite isDigitF-correct (suc zero) input
        | node-head
        | eqNatNat-refl-code (suc zero) = refl

isNodeCodeF-sound-head :
  (input : ℕ) →
  PRRel-holds (rel isNodeCodeF) (input ∷ []) →
  NodeHeadNat input
isNodeCodeF-sound-head input holds =
  eqNatNat-sound-code
    (mod4Nat input)
    (suc zero)
    (trans (sym (isDigitF-correct (suc zero) input)) holds)

isAtomCodeF-canonical-complete :
  (n : ℕ) →
  PRRel-holds (rel isAtomCodeF) (encodeCode (atom n) ∷ [])
isAtomCodeF-canonical-complete n =
  isAtomCodeF-complete-head
    (encodeCode (atom n))
    (mod4Nat-appendDigit d0 (encodeNatWithRest n zero))

codeListNilF : PRF (suc zero)
codeListNilF = isDigit0F

codeListConsF : PRF (suc zero)
codeListConsF = isDigit1F

codeListNilF-complete-head :
  (input : ℕ) → CodeListNilHeadNat input →
  PRRel-holds (rel codeListNilF) (input ∷ [])
codeListNilF-complete-head =
  isAtomCodeF-complete-head

codeListNilF-sound-head :
  (input : ℕ) →
  PRRel-holds (rel codeListNilF) (input ∷ []) →
  CodeListNilHeadNat input
codeListNilF-sound-head =
  isAtomCodeF-sound-head

codeListNilF-canonical-empty-complete :
  PRRel-holds (rel codeListNilF) (encodeCodeListWithRest []ˡ zero ∷ [])
codeListNilF-canonical-empty-complete =
  codeListNilF-complete-head
    (encodeCodeListWithRest []ˡ zero)
    (mod4Nat-appendDigit d0 zero)

codeListNilF-canonical-empty-correct :
  evalPRF codeListNilF (encodeCodeListWithRest []ˡ zero ∷ []) ≡ suc zero
codeListNilF-canonical-empty-correct =
  codeListNilF-canonical-empty-complete

codeListConsF-complete-head :
  (input : ℕ) → CodeListConsHeadNat input →
  PRRel-holds (rel codeListConsF) (input ∷ [])
codeListConsF-complete-head =
  isNodeCodeF-complete-head

codeListConsF-sound-head :
  (input : ℕ) →
  PRRel-holds (rel codeListConsF) (input ∷ []) →
  CodeListConsHeadNat input
codeListConsF-sound-head =
  isNodeCodeF-sound-head

codeListConsF-canonical-cons-complete :
  (head : Code) → (tail : List Code) →
  PRRel-holds
    (rel codeListConsF)
    (encodeCodeListWithRest (head ∷ˡ tail) zero ∷ [])
codeListConsF-canonical-cons-complete head tail =
  codeListConsF-complete-head
    (encodeCodeListWithRest (head ∷ˡ tail) zero)
    (mod4Nat-appendDigit
      d1
      (encodeCodeWithRest head (encodeCodeListWithRest tail zero)))

codeListConsF-canonical-cons-correct :
  (head : Code) → (tail : List Code) →
  evalPRF
    codeListConsF
    (encodeCodeListWithRest (head ∷ˡ tail) zero ∷ [])
  ≡ suc zero
codeListConsF-canonical-cons-correct head tail =
  codeListConsF-canonical-cons-complete head tail

isNodeCodeF-canonical-complete :
  (tag : ℕ) → (children : List Code) →
  PRRel-holds (rel isNodeCodeF) (encodeCode (node tag children) ∷ [])
isNodeCodeF-canonical-complete tag children =
  isNodeCodeF-complete-head
    (encodeCode (node tag children))
    (mod4Nat-appendDigit
      d1
      (encodeNatWithRest tag (encodeCodeListWithRest children zero)))

prefixNatActiveAtF : PRF (suc (suc zero))
prefixNatActiveAtF =
  compF andF
    (compF digitEqualsAtF
      (projF fin0 ∷
       projF fin1 ∷
       twoF ∷ []) ∷
     compF eqNatF
      (compF countDigitUpToF
        (projF fin0 ∷
         threeF ∷
         projF fin1 ∷ []) ∷
       zeroF ∷ []) ∷ [])

prefixNatBaseF : PRF (suc zero)
prefixNatBaseF =
  compF prefixNatActiveAtF
    (zeroF ∷
     projF fin0 ∷ [])

prefixNatStepF : PRF (suc (suc (suc zero)))
prefixNatStepF =
  compF addF
    (projF fin1 ∷
     compF prefixNatActiveAtF
       (compF sucF (projF fin0 ∷ []) ∷
        projF fin2 ∷ []) ∷ [])

prefixNatSumF : PRF (suc (suc zero))
prefixNatSumF =
  precF prefixNatBaseF prefixNatStepF

prefixNatValueF : PRF (suc zero)
prefixNatValueF =
  compF prefixNatSumF
    (projF fin0 ∷
     projF fin0 ∷ [])

atomPayloadF : PRF (suc zero)
atomPayloadF =
  compF prefixNatValueF (div4F ∷ [])

nodeTagF : PRF (suc zero)
nodeTagF =
  compF prefixNatValueF (div4F ∷ [])

prefixNatRestF : PRF (suc zero)
prefixNatRestF =
  compF iterDiv4F
    (compF sucF (prefixNatValueF ∷ []) ∷
     projF fin0 ∷ [])

nodeChildrenF : PRF (suc zero)
nodeChildrenF =
  compF prefixNatRestF (div4F ∷ [])

encodeNatWithRestBaseF : PRF (suc zero)
encodeNatWithRestBaseF =
  compF (appendDigitF d3) (projF fin0 ∷ [])

encodeNatWithRestStepF : PRF (suc (suc (suc zero)))
encodeNatWithRestStepF =
  compF (appendDigitF d2) (projF fin1 ∷ [])

encodeNatWithRestF : PRF (suc (suc zero))
encodeNatWithRestF =
  precF encodeNatWithRestBaseF encodeNatWithRestStepF

atomCodeWithRestF : PRF (suc (suc zero))
atomCodeWithRestF =
  compF (appendDigitF d0)
    (compF encodeNatWithRestF
      (projF fin0 ∷
       projF fin1 ∷ []) ∷ [])

atomCodeF : PRF (suc zero)
atomCodeF =
  compF atomCodeWithRestF
    (projF fin0 ∷
     zeroF ∷ [])

nodeCodeWithRestF : PRF (suc (suc zero))
nodeCodeWithRestF =
  compF (appendDigitF d1)
    (compF encodeNatWithRestF
      (projF fin0 ∷
       projF fin1 ∷ []) ∷ [])

emptyCodeListWithRestF : PRF (suc zero)
emptyCodeListWithRestF =
  compF (appendDigitF d0) (projF fin0 ∷ [])

zeroTermCodeWithRestF : PRF (suc zero)
zeroTermCodeWithRestF =
  compF nodeCodeWithRestF
    (constF 1 ∷
     emptyCodeListWithRestF ∷ [])

emptyRestIterF : PRF (suc (suc zero))
emptyRestIterF =
  precF
    (projF fin0)
    (compF (appendDigitF d0) (projF fin1 ∷ []))

sucNumeralTermWrapF : PRF (suc zero)
sucNumeralTermWrapF =
  compF nodeCodeWithRestF
    (constF 2 ∷
     compF (appendDigitF d1) (projF fin0 ∷ []) ∷ [])

sucNumeralTermWrapIterF : PRF (suc (suc zero))
sucNumeralTermWrapIterF =
  precF
    (projF fin0)
    (compF sucNumeralTermWrapF (projF fin1 ∷ []))

numeralTermCodeWithRestF : PRF (suc (suc zero))
numeralTermCodeWithRestF =
  compF sucNumeralTermWrapIterF
    (projF fin0 ∷
     compF zeroTermCodeWithRestF
      (compF emptyRestIterF
        (projF fin0 ∷
         projF fin1 ∷ []) ∷ []) ∷ [])

numeralTermCodeF : PRF (suc zero)
numeralTermCodeF =
  compF numeralTermCodeWithRestF
    (projF fin0 ∷
     zeroF ∷ [])

singleNumeralTermListWithRestF : PRF (suc (suc zero))
singleNumeralTermListWithRestF =
  compF (appendDigitF d1)
    (compF numeralTermCodeWithRestF
      (projF fin0 ∷
       compF emptyCodeListWithRestF (projF fin1 ∷ []) ∷ []) ∷ [])

twoNumeralTermListWithRestF : PRF (suc (suc (suc zero)))
twoNumeralTermListWithRestF =
  compF (appendDigitF d1)
    (compF numeralTermCodeWithRestF
      (projF fin0 ∷
       compF singleNumeralTermListWithRestF
        (projF fin1 ∷
         projF fin2 ∷ []) ∷ []) ∷ [])

closedNumeralEqFormulaCodeWithRestF :
  PRF (suc (suc (suc zero)))
closedNumeralEqFormulaCodeWithRestF =
  compF nodeCodeWithRestF
    (constF 5 ∷
     twoNumeralTermListWithRestF ∷ [])

closedNumeralEqFormulaCodeF : PRF (suc (suc zero))
closedNumeralEqFormulaCodeF =
  compF closedNumeralEqFormulaCodeWithRestF
    (projF fin0 ∷
     projF fin1 ∷
     zeroF ∷ [])

closedNumeralNeqFormulaCodeF : PRF (suc (suc zero))
closedNumeralNeqFormulaCodeF =
  compF nodeCodeWithRestF
    (constF 11 ∷
     compF (appendDigitF d1)
      (compF closedNumeralEqFormulaCodeWithRestF
        (projF fin0 ∷
         projF fin1 ∷
         zeroF ∷ []) ∷ []) ∷ [])

prefixNatActiveAtNat : ℕ → ℕ → ℕ
prefixNatActiveAtNat position input =
  mulNat
    (digitEqualsAtNat position input (suc (suc zero)))
    (eqNatNat
      (countDigitUpToNat position (suc (suc (suc zero))) input)
      zero)

prefixNatSumNat : ℕ → ℕ → ℕ
prefixNatSumNat zero input =
  prefixNatActiveAtNat zero input
prefixNatSumNat (suc bound) input =
  prefixNatSumNat bound input +
  prefixNatActiveAtNat (suc bound) input

prefixNatValueNat : ℕ → ℕ
prefixNatValueNat input =
  prefixNatSumNat input input

prefixNatActiveDigitsAt : ℕ → List Digit → ℕ → ℕ
prefixNatActiveDigitsAt position digits rest =
  mulNat
    (eqNatNat
      (digitAtDigitsWithRest position digits rest)
      (suc (suc zero)))
    (eqNatNat
      (countDigitDigitsUpTo
        position
        (suc (suc (suc zero)))
        digits
        rest)
      zero)

prefixNatDigitsUpTo : ℕ → List Digit → ℕ → ℕ
prefixNatDigitsUpTo zero digits rest =
  prefixNatActiveDigitsAt zero digits rest
prefixNatDigitsUpTo (suc bound) digits rest =
  prefixNatDigitsUpTo bound digits rest +
  prefixNatActiveDigitsAt (suc bound) digits rest

prefixNatActiveAtNat-as-digits :
  (position : ℕ) → (digits : List Digit) → (rest : ℕ) →
  prefixNatActiveAtNat
    position
    (appendDigitsWithRest digits rest)
  ≡
  prefixNatActiveDigitsAt position digits rest
prefixNatActiveAtNat-as-digits position digits rest
  rewrite digitAtDigitsWithRest-correct position digits rest
        | countDigitUpToNat-as-digits
            position
            (suc (suc (suc zero)))
            digits
            rest = refl

prefixNatSumNat-as-digits :
  (bound : ℕ) → (digits : List Digit) → (rest : ℕ) →
  prefixNatSumNat
    bound
    (appendDigitsWithRest digits rest)
  ≡
  prefixNatDigitsUpTo bound digits rest
prefixNatSumNat-as-digits zero digits rest =
  prefixNatActiveAtNat-as-digits zero digits rest
prefixNatSumNat-as-digits (suc bound) digits rest
  rewrite prefixNatSumNat-as-digits bound digits rest
        | prefixNatActiveAtNat-as-digits (suc bound) digits rest =
  refl

digitsLength-natDigits :
  (n : ℕ) → digitsLength (natDigits n) ≡ suc n
digitsLength-natDigits zero = refl
digitsLength-natDigits (suc n) =
  cong suc (digitsLength-natDigits n)

scanBound-natDigits :
  (n : ℕ) → scanBound (natDigits n) ≡ n
scanBound-natDigits zero = refl
scanBound-natDigits (suc n) =
  digitsLength-natDigits n

prefixNatActiveDigitsAt-zero-d2 :
  (digits : List Digit) → (rest : ℕ) →
  prefixNatActiveDigitsAt zero (d2 ∷ˡ digits) rest ≡ suc zero
prefixNatActiveDigitsAt-zero-d2 digits rest = refl

countDigitDigitsUpTo-suc-cons-rest :
  (bound digit : ℕ) → (d : Digit) → (digits : List Digit) →
  (rest : ℕ) →
  countDigitDigitsUpTo (suc bound) digit (d ∷ˡ digits) rest ≡
  eqNatNat (digitToNat d) digit +
  countDigitDigitsUpTo bound digit digits rest
countDigitDigitsUpTo-suc-cons-rest zero digit d digits rest = refl
countDigitDigitsUpTo-suc-cons-rest (suc bound) digit d digits rest
  rewrite countDigitDigitsUpTo-suc-cons-rest bound digit d digits rest
        | +-assoc
            (eqNatNat (digitToNat d) digit)
            (countDigitDigitsUpTo bound digit digits rest)
            (eqNatNat
              (digitAtDigitsWithRest (suc bound) digits rest)
              digit) =
  refl

prefixNatActiveDigitsAt-suc-d2 :
  (position : ℕ) → (digits : List Digit) → (rest : ℕ) →
  prefixNatActiveDigitsAt (suc position) (d2 ∷ˡ digits) rest ≡
  prefixNatActiveDigitsAt position digits rest
prefixNatActiveDigitsAt-suc-d2 position digits rest
  rewrite countDigitDigitsUpTo-suc-cons-rest
            position
            (suc (suc (suc zero)))
            d2
            digits
            rest =
  refl

prefixNatActiveDigitsAt-suc-d3 :
  (position : ℕ) → (digits : List Digit) → (rest : ℕ) →
  prefixNatActiveDigitsAt (suc position) (d3 ∷ˡ digits) rest ≡ zero
prefixNatActiveDigitsAt-suc-d3 position digits rest
  rewrite countDigitDigitsUpTo-suc-cons-rest
            position
            (suc (suc (suc zero)))
            d3
            digits
            rest
        | mulNat-zeroʳ
            (eqNatNat
              (digitAtDigitsWithRest position digits rest)
              (suc (suc zero))) =
  refl

prefixNatDigitsUpTo-suc-d2 :
  (bound : ℕ) → (digits : List Digit) → (rest : ℕ) →
  prefixNatDigitsUpTo (suc bound) (d2 ∷ˡ digits) rest ≡
  suc (prefixNatDigitsUpTo bound digits rest)
prefixNatDigitsUpTo-suc-d2 zero digits rest
  rewrite prefixNatActiveDigitsAt-zero-d2 digits rest
        | prefixNatActiveDigitsAt-suc-d2 zero digits rest = refl
prefixNatDigitsUpTo-suc-d2 (suc bound) digits rest
  rewrite prefixNatDigitsUpTo-suc-d2 bound digits rest
        | prefixNatActiveDigitsAt-suc-d2 (suc bound) digits rest =
  refl

prefixNatDigitsUpTo-natDigits-bound :
  (n rest : ℕ) →
  prefixNatDigitsUpTo n (natDigits n) rest ≡ n
prefixNatDigitsUpTo-natDigits-bound zero rest = refl
prefixNatDigitsUpTo-natDigits-bound (suc n) rest
  rewrite prefixNatDigitsUpTo-suc-d2 n (natDigits n) rest
        | prefixNatDigitsUpTo-natDigits-bound n rest = refl

prefixNatDigitsUpTo-natDigits :
  (n rest : ℕ) →
  prefixNatDigitsUpTo (scanBound (natDigits n)) (natDigits n) rest ≡ n
prefixNatDigitsUpTo-natDigits n rest
  rewrite scanBound-natDigits n =
  prefixNatDigitsUpTo-natDigits-bound n rest

prefixNatActiveDigitsAt-after-natDigits-bound :
  (n rest extra : ℕ) →
  prefixNatActiveDigitsAt
    (suc (n + extra))
    (natDigits n)
    rest
  ≡ zero
prefixNatActiveDigitsAt-after-natDigits-bound zero rest extra
  rewrite prefixNatActiveDigitsAt-suc-d3 extra []ˡ rest = refl
prefixNatActiveDigitsAt-after-natDigits-bound (suc n) rest extra
  rewrite prefixNatActiveDigitsAt-suc-d2
            (suc (n + extra))
            (natDigits n)
            rest
        | prefixNatActiveDigitsAt-after-natDigits-bound n rest extra =
  refl

prefixNatActiveDigitsAt-after-natDigits :
  (n rest extra : ℕ) →
  prefixNatActiveDigitsAt
    (suc (scanBound (natDigits n) + extra))
    (natDigits n)
    rest
  ≡ zero
prefixNatActiveDigitsAt-after-natDigits n rest extra
  rewrite scanBound-natDigits n =
  prefixNatActiveDigitsAt-after-natDigits-bound n rest extra

prefixNatDigitsUpTo-complete-natDigits :
  (n rest extra : ℕ) →
  prefixNatDigitsUpTo
    (scanBound (natDigits n) + extra)
    (natDigits n)
    rest
  ≡
  prefixNatDigitsUpTo (scanBound (natDigits n)) (natDigits n) rest
prefixNatDigitsUpTo-complete-natDigits n rest zero
  rewrite +-zeroʳ (scanBound (natDigits n)) = refl
prefixNatDigitsUpTo-complete-natDigits n rest (suc extra)
  rewrite +-sucʳ (scanBound (natDigits n)) extra
        | prefixNatDigitsUpTo-complete-natDigits n rest extra
        | prefixNatActiveDigitsAt-after-natDigits n rest extra
        | +-zeroʳ
            (prefixNatDigitsUpTo
              (scanBound (natDigits n))
              (natDigits n)
              rest) =
  refl

n≤sucn-code : (n : ℕ) → n ≤ suc n
n≤sucn-code n = ≤-step (≤-refl n)

n≤encodeNatWithRest :
  (n rest : ℕ) → n ≤ encodeNatWithRest n rest
n≤encodeNatWithRest n rest =
  ≤-trans
    (n≤sucn-code n)
    (subst
      (λ bound → bound ≤ encodeNatWithRest n rest)
      (cong suc (+-zeroʳ n))
      (size≤encodeNatWithRest n zero rest (≤-zero rest)))

scanBound≤encodeNatWithRest :
  (n rest : ℕ) →
  scanBound (natDigits n) ≤ encodeNatWithRest n rest
scanBound≤encodeNatWithRest n rest =
  subst
    (λ bound → bound ≤ encodeNatWithRest n rest)
    (sym (scanBound-natDigits n))
    (n≤encodeNatWithRest n rest)

prefixNatValueNat-encodeNatWithRest :
  (n rest : ℕ) →
  prefixNatValueNat (encodeNatWithRest n rest) ≡ n
prefixNatValueNat-encodeNatWithRest n rest
  with scanBound≤encodeNatWithRest n rest
... | extra ,Σ eq
  rewrite encodeNatWithRest-as-digits n rest
        | prefixNatSumNat-as-digits
            (appendDigitsWithRest (natDigits n) rest)
            (natDigits n)
            rest
        | eq
        | prefixNatDigitsUpTo-complete-natDigits n rest extra
        | prefixNatDigitsUpTo-natDigits n rest =
  refl

prefixNatActiveAtF-correct :
  (position input : ℕ) →
  evalPRF prefixNatActiveAtF (position ∷ input ∷ []) ≡
  prefixNatActiveAtNat position input
prefixNatActiveAtF-correct position input
  rewrite digitEqualsAtF-correct
            position input (suc (suc zero))
        | countDigitUpToF-correct
            position (suc (suc (suc zero))) input
        | eqNatF-correct
            (countDigitUpToNat position (suc (suc (suc zero))) input)
            zero
        | andF-correct
            (digitEqualsAtNat position input (suc (suc zero)))
            (eqNatNat
              (countDigitUpToNat position (suc (suc (suc zero))) input)
              zero) = refl

prefixNatBaseF-correct :
  (input : ℕ) →
  evalPRF prefixNatBaseF (input ∷ []) ≡
  prefixNatSumNat zero input
prefixNatBaseF-correct input =
  prefixNatActiveAtF-correct zero input

prefixNatStepF-correct :
  (bound previous input : ℕ) →
  evalPRF prefixNatStepF (bound ∷ previous ∷ input ∷ []) ≡
  previous + prefixNatActiveAtNat (suc bound) input
prefixNatStepF-correct bound previous input
  rewrite prefixNatActiveAtF-correct (suc bound) input
        | addF-correct previous
            (prefixNatActiveAtNat (suc bound) input) = refl

prefixNatSumF-correct :
  (bound input : ℕ) →
  evalPRF prefixNatSumF (bound ∷ input ∷ []) ≡
  prefixNatSumNat bound input
prefixNatSumF-correct zero input =
  prefixNatBaseF-correct input
prefixNatSumF-correct (suc bound) input
  rewrite prefixNatSumF-correct bound input
        | prefixNatStepF-correct
            bound
            (prefixNatSumNat bound input)
            input = refl

prefixNatValueF-correct :
  (input : ℕ) →
  evalPRF prefixNatValueF (input ∷ []) ≡
  prefixNatValueNat input
prefixNatValueF-correct input =
  prefixNatSumF-correct input input

atomPayloadF-correct-to-prefix :
  (input : ℕ) →
  evalPRF atomPayloadF (input ∷ []) ≡
  prefixNatValueNat (div4Nat input)
atomPayloadF-correct-to-prefix input
  rewrite div4F-correct input
        | prefixNatValueF-correct (div4Nat input) = refl

nodeTagF-correct-to-prefix :
  (input : ℕ) →
  evalPRF nodeTagF (input ∷ []) ≡
  prefixNatValueNat (div4Nat input)
nodeTagF-correct-to-prefix =
  atomPayloadF-correct-to-prefix

prefixNatRestNat : ℕ → ℕ
prefixNatRestNat input =
  iterDiv4Nat (suc (prefixNatValueNat input)) input

prefixNatRestF-correct :
  (input : ℕ) →
  evalPRF prefixNatRestF (input ∷ []) ≡
  prefixNatRestNat input
prefixNatRestF-correct input
  rewrite prefixNatValueF-correct input
        | iterDiv4F-correct (suc (prefixNatValueNat input)) input =
  refl

nodeChildrenF-correct-to-prefix :
  (input : ℕ) →
  evalPRF nodeChildrenF (input ∷ []) ≡
  prefixNatRestNat (div4Nat input)
nodeChildrenF-correct-to-prefix input
  rewrite div4F-correct input
        | prefixNatRestF-correct (div4Nat input) =
  refl

iterDiv4Nat-encodeNatWithRest :
  (n rest : ℕ) →
  iterDiv4Nat (suc n) (encodeNatWithRest n rest) ≡ rest
iterDiv4Nat-encodeNatWithRest zero rest =
  div4Nat-appendDigit d3 rest
iterDiv4Nat-encodeNatWithRest (suc n) rest
  rewrite iterDiv4Nat-appendDigit-tail
            (suc n)
            d2
            (encodeNatWithRest n rest)
        | iterDiv4Nat-encodeNatWithRest n rest =
  refl

prefixNatRestNat-encodeNatWithRest :
  (n rest : ℕ) →
  prefixNatRestNat (encodeNatWithRest n rest) ≡ rest
prefixNatRestNat-encodeNatWithRest n rest
  rewrite prefixNatValueNat-encodeNatWithRest n rest
        | iterDiv4Nat-encodeNatWithRest n rest =
  refl

atomPayloadF-canonical-correct :
  (n : ℕ) →
  evalPRF atomPayloadF (encodeCode (atom n) ∷ []) ≡ n
atomPayloadF-canonical-correct n
  rewrite atomPayloadF-correct-to-prefix (encodeCode (atom n))
        | div4Nat-appendDigit d0 (encodeNatWithRest n zero)
        | prefixNatValueNat-encodeNatWithRest n zero =
  refl

nodeTagF-canonical-correct :
  (tag : ℕ) → (children : List Code) →
  evalPRF nodeTagF (encodeCode (node tag children) ∷ []) ≡ tag
nodeTagF-canonical-correct tag children
  rewrite nodeTagF-correct-to-prefix (encodeCode (node tag children))
        | div4Nat-appendDigit
            d1
            (encodeNatWithRest tag (encodeCodeListWithRest children zero))
        | prefixNatValueNat-encodeNatWithRest
            tag
            (encodeCodeListWithRest children zero) =
  refl

nodeChildrenF-canonical-correct :
  (tag : ℕ) → (children : List Code) →
  evalPRF nodeChildrenF (encodeCode (node tag children) ∷ []) ≡
  encodeCodeListWithRest children zero
nodeChildrenF-canonical-correct tag children
  rewrite nodeChildrenF-correct-to-prefix (encodeCode (node tag children))
        | div4Nat-appendDigit
            d1
            (encodeNatWithRest tag (encodeCodeListWithRest children zero))
        | prefixNatRestNat-encodeNatWithRest
            tag
            (encodeCodeListWithRest children zero) =
  refl

encodeNatWithRestBaseF-correct :
  (rest : ℕ) →
  evalPRF encodeNatWithRestBaseF (rest ∷ []) ≡
  appendDigit d3 rest
encodeNatWithRestBaseF-correct rest =
  appendDigitF-correct d3 rest

encodeNatWithRestStepF-correct :
  (n previous rest : ℕ) →
  evalPRF encodeNatWithRestStepF (n ∷ previous ∷ rest ∷ []) ≡
  appendDigit d2 previous
encodeNatWithRestStepF-correct n previous rest =
  appendDigitF-correct d2 previous

encodeNatWithRestF-correct :
  (n rest : ℕ) →
  evalPRF encodeNatWithRestF (n ∷ rest ∷ []) ≡
  encodeNatWithRest n rest
encodeNatWithRestF-correct zero rest =
  encodeNatWithRestBaseF-correct rest
encodeNatWithRestF-correct (suc n) rest
  rewrite encodeNatWithRestF-correct n rest
        | encodeNatWithRestStepF-correct
            n
            (encodeNatWithRest n rest)
            rest =
  refl

atomCodeWithRestF-correct :
  (n rest : ℕ) →
  evalPRF atomCodeWithRestF (n ∷ rest ∷ []) ≡
  appendDigit d0 (encodeNatWithRest n rest)
atomCodeWithRestF-correct n rest
  rewrite encodeNatWithRestF-correct n rest
        | appendDigitF-correct d0 (encodeNatWithRest n rest) =
  refl

atomCodeF-canonical-correct :
  (n : ℕ) →
  evalPRF atomCodeF (n ∷ []) ≡ encodeCode (atom n)
atomCodeF-canonical-correct n =
  atomCodeWithRestF-correct n zero

nodeCodeWithRestF-correct :
  (tag children-code : ℕ) →
  evalPRF nodeCodeWithRestF (tag ∷ children-code ∷ []) ≡
  appendDigit d1 (encodeNatWithRest tag children-code)
nodeCodeWithRestF-correct tag children-code
  rewrite encodeNatWithRestF-correct tag children-code
        | appendDigitF-correct
            d1
            (encodeNatWithRest tag children-code) =
  refl

nodeCodeWithRestF-canonical-correct :
  (tag : ℕ) → (children : List Code) →
  evalPRF
    nodeCodeWithRestF
    (tag ∷ encodeCodeListWithRest children zero ∷ [])
  ≡ encodeCode (node tag children)
nodeCodeWithRestF-canonical-correct tag children =
  nodeCodeWithRestF-correct tag (encodeCodeListWithRest children zero)

emptyCodeListWithRestF-correct :
  (rest : ℕ) →
  evalPRF emptyCodeListWithRestF (rest ∷ []) ≡
  encodeCodeListWithRest []ˡ rest
emptyCodeListWithRestF-correct rest =
  appendDigitF-correct d0 rest

zeroTermCodeWithRestF-correct :
  (rest : ℕ) →
  evalPRF zeroTermCodeWithRestF (rest ∷ []) ≡
  encodeCodeWithRest (canonicalCodeTerm zeroᵗ) rest
zeroTermCodeWithRestF-correct rest
  rewrite constF-correct 1 (rest ∷ [])
        | emptyCodeListWithRestF-correct rest
        | nodeCodeWithRestF-correct
            1
            (encodeCodeListWithRest []ˡ rest) =
  refl

emptyRestIterNat : ℕ → ℕ → ℕ
emptyRestIterNat zero rest = rest
emptyRestIterNat (suc n) rest =
  appendDigit d0 (emptyRestIterNat n rest)

emptyRestIterF-correct :
  (n rest : ℕ) →
  evalPRF emptyRestIterF (n ∷ rest ∷ []) ≡
  emptyRestIterNat n rest
emptyRestIterF-correct zero rest = refl
emptyRestIterF-correct (suc n) rest
  rewrite emptyRestIterF-correct n rest
        | appendDigitF-correct d0 (emptyRestIterNat n rest) =
  refl

emptyRestIterNat-shift :
  (n rest : ℕ) →
  emptyRestIterNat n (appendDigit d0 rest) ≡
  appendDigit d0 (emptyRestIterNat n rest)
emptyRestIterNat-shift zero rest = refl
emptyRestIterNat-shift (suc n) rest
  rewrite emptyRestIterNat-shift n rest = refl

sucNumeralTermWrapNat : ℕ → ℕ
sucNumeralTermWrapNat child-code =
  appendDigit d1 (encodeNatWithRest 2 (appendDigit d1 child-code))

sucNumeralTermWrapF-correct :
  (child-code : ℕ) →
  evalPRF sucNumeralTermWrapF (child-code ∷ []) ≡
  sucNumeralTermWrapNat child-code
sucNumeralTermWrapF-correct child-code
  rewrite constF-correct 2 (child-code ∷ [])
        | appendDigitF-correct d1 child-code
        | nodeCodeWithRestF-correct
            2
            (appendDigit d1 child-code) =
  refl

sucNumeralTermWrapIterNat : ℕ → ℕ → ℕ
sucNumeralTermWrapIterNat zero base = base
sucNumeralTermWrapIterNat (suc n) base =
  sucNumeralTermWrapNat (sucNumeralTermWrapIterNat n base)

sucNumeralTermWrapIterF-correct :
  (n base : ℕ) →
  evalPRF sucNumeralTermWrapIterF (n ∷ base ∷ []) ≡
  sucNumeralTermWrapIterNat n base
sucNumeralTermWrapIterF-correct zero base = refl
sucNumeralTermWrapIterF-correct (suc n) base
  rewrite sucNumeralTermWrapIterF-correct n base
        | sucNumeralTermWrapF-correct
            (sucNumeralTermWrapIterNat n base) =
  refl

numeralTermCodeWithRestNat : ℕ → ℕ → ℕ
numeralTermCodeWithRestNat n rest =
  sucNumeralTermWrapIterNat
    n
    (encodeCodeWithRest
      (canonicalCodeTerm zeroᵗ)
      (emptyRestIterNat n rest))

numeralTermCodeWithRestNat-correct :
  (n rest : ℕ) →
  numeralTermCodeWithRestNat n rest ≡
  encodeCodeWithRest (canonicalCodeTerm (numeral n)) rest
numeralTermCodeWithRestNat-correct zero rest = refl
numeralTermCodeWithRestNat-correct (suc n) rest
  rewrite sym (emptyRestIterNat-shift n rest)
        | numeralTermCodeWithRestNat-correct n (appendDigit d0 rest) =
  refl

numeralTermCodeWithRestF-correct :
  (n rest : ℕ) →
  evalPRF numeralTermCodeWithRestF (n ∷ rest ∷ []) ≡
  encodeCodeWithRest (canonicalCodeTerm (numeral n)) rest
numeralTermCodeWithRestF-correct n rest
  rewrite emptyRestIterF-correct n rest
        | zeroTermCodeWithRestF-correct (emptyRestIterNat n rest)
        | sucNumeralTermWrapIterF-correct
            n
            (encodeCodeWithRest
              (canonicalCodeTerm zeroᵗ)
              (emptyRestIterNat n rest))
        | numeralTermCodeWithRestNat-correct n rest =
  refl

numeralTermCodeF-canonical-correct :
  (n : ℕ) →
  evalPRF numeralTermCodeF (n ∷ []) ≡
  encodeCode (canonicalCodeTerm (numeral n))
numeralTermCodeF-canonical-correct n =
  numeralTermCodeWithRestF-correct n zero

singleNumeralTermListWithRestF-correct :
  (n rest : ℕ) →
  evalPRF singleNumeralTermListWithRestF (n ∷ rest ∷ []) ≡
  encodeCodeListWithRest (canonicalCodeTerm (numeral n) ∷ˡ []ˡ) rest
singleNumeralTermListWithRestF-correct n rest
  rewrite emptyCodeListWithRestF-correct rest
        | numeralTermCodeWithRestF-correct
            n
            (encodeCodeListWithRest []ˡ rest)
        | appendDigitF-correct
            d1
            (encodeCodeWithRest
              (canonicalCodeTerm (numeral n))
              (encodeCodeListWithRest []ˡ rest)) =
  refl

twoNumeralTermListWithRestF-correct :
  (m n rest : ℕ) →
  evalPRF twoNumeralTermListWithRestF (m ∷ n ∷ rest ∷ []) ≡
  encodeCodeListWithRest
    (canonicalCodeTerm (numeral m) ∷ˡ
     canonicalCodeTerm (numeral n) ∷ˡ []ˡ)
    rest
twoNumeralTermListWithRestF-correct m n rest
  rewrite singleNumeralTermListWithRestF-correct n rest
        | numeralTermCodeWithRestF-correct
            m
            (encodeCodeListWithRest
              (canonicalCodeTerm (numeral n) ∷ˡ []ˡ)
              rest)
        | appendDigitF-correct
            d1
            (encodeCodeWithRest
              (canonicalCodeTerm (numeral m))
              (encodeCodeListWithRest
                (canonicalCodeTerm (numeral n) ∷ˡ []ˡ)
                rest)) =
  refl

closedNumeralEqFormulaCodeWithRestF-correct :
  (m n rest : ℕ) →
  evalPRF
    closedNumeralEqFormulaCodeWithRestF
    (m ∷ n ∷ rest ∷ [])
  ≡
  encodeCodeWithRest
    (canonicalCodeFormula (numeral m ≈ numeral n))
    rest
closedNumeralEqFormulaCodeWithRestF-correct m n rest
  rewrite constF-correct 5 (m ∷ n ∷ rest ∷ [])
        | twoNumeralTermListWithRestF-correct m n rest
        | nodeCodeWithRestF-correct
            5
            (encodeCodeListWithRest
              (canonicalCodeTerm (numeral m) ∷ˡ
               canonicalCodeTerm (numeral n) ∷ˡ []ˡ)
              rest) =
  refl

closedNumeralEqFormulaCodeF-canonical-correct :
  (m n : ℕ) →
  evalPRF closedNumeralEqFormulaCodeF (m ∷ n ∷ []) ≡
  encodeCode (canonicalCodeFormula (numeral m ≈ numeral n))
closedNumeralEqFormulaCodeF-canonical-correct m n =
  closedNumeralEqFormulaCodeWithRestF-correct m n zero

closedNumeralNeqFormulaCodeF-correct :
  (m n : ℕ) →
  evalPRF closedNumeralNeqFormulaCodeF (m ∷ n ∷ []) ≡
  encodeCode (canonicalCodeFormula (¬ᶠ (numeral m ≈ numeral n)))
closedNumeralNeqFormulaCodeF-correct m n
  rewrite constF-correct 11 (m ∷ n ∷ [])
        | closedNumeralEqFormulaCodeWithRestF-correct m n zero
        | appendDigitF-correct
            d1
            (encodeCodeWithRest
              (canonicalCodeFormula (numeral m ≈ numeral n))
              zero)
        | nodeCodeWithRestF-correct
            11
            (encodeCodeListWithRest
              (canonicalCodeFormula (numeral m ≈ numeral n) ∷ˡ []ˡ)
              zero) =
  refl

codeListHeadF : PRF (suc zero)
codeListHeadF = zeroF

codeListTailF : PRF (suc zero)
codeListTailF = zeroF

codeListLengthF : PRF (suc zero)
codeListLengthF = zeroF

codeListNthF : PRF (suc (suc zero))
codeListNthF = zeroF

codeListHeadGraphPR : PRRel (suc (suc zero))
codeListHeadGraphPR = functionGraphRel codeListHeadF

codeListTailGraphPR : PRRel (suc (suc zero))
codeListTailGraphPR = functionGraphRel codeListTailF

codeListLengthGraphPR : PRRel (suc (suc zero))
codeListLengthGraphPR = functionGraphRel codeListLengthF

codeListNthGraphPR : PRRel (suc (suc (suc zero)))
codeListNthGraphPR = functionGraphRel codeListNthF

record CanonicalCodePRDestructors : Set₁ where
  field
    isAtom-represented       : PARepresentsFunction isAtomCodeF
    isNode-represented       : PARepresentsFunction isNodeCodeF
    atomPayload-represented  : PARepresentsFunction atomPayloadF
    nodeTag-represented      : PARepresentsFunction nodeTagF
    nodeChildren-represented : PARepresentsFunction nodeChildrenF
    codeListNil-represented  : PARepresentsFunction codeListNilF
    codeListCons-represented : PARepresentsFunction codeListConsF
    codeListHead-represented : PARepresentsFunction codeListHeadF
    codeListTail-represented : PARepresentsFunction codeListTailF
    codeListLength-represented : PARepresentsFunction codeListLengthF
    codeListNth-represented    : PARepresentsFunction codeListNthF
    codeListHead-graph-represented :
      PARepresentsRelation codeListHeadGraphPR
    codeListTail-graph-represented :
      PARepresentsRelation codeListTailGraphPR
    codeListLength-graph-represented :
      PARepresentsRelation codeListLengthGraphPR
    codeListNth-graph-represented :
      PARepresentsRelation codeListNthGraphPR

canonicalCodePRDestructors : CanonicalCodePRDestructors
canonicalCodePRDestructors = record
  { isAtom-represented = prf-represented isAtomCodeF
  ; isNode-represented = prf-represented isNodeCodeF
  ; atomPayload-represented = prf-represented atomPayloadF
  ; nodeTag-represented = prf-represented nodeTagF
  ; nodeChildren-represented = prf-represented nodeChildrenF
  ; codeListNil-represented = prf-represented codeListNilF
  ; codeListCons-represented = prf-represented codeListConsF
  ; codeListHead-represented = prf-represented codeListHeadF
  ; codeListTail-represented = prf-represented codeListTailF
  ; codeListLength-represented = prf-represented codeListLengthF
  ; codeListNth-represented = prf-represented codeListNthF
  ; codeListHead-graph-represented =
      functionGraphRel-represented codeListHeadF
  ; codeListTail-graph-represented =
      functionGraphRel-represented codeListTailF
  ; codeListLength-graph-represented =
      functionGraphRel-represented codeListLengthF
  ; codeListNth-graph-represented =
      functionGraphRel-represented codeListNthF
  }

record CanonicalCodePRBuilders : Set₁ where
  field
    encodeNatWithRest-represented :
      PARepresentsFunction encodeNatWithRestF
    atomCodeWithRest-represented :
      PARepresentsFunction atomCodeWithRestF
    atomCode-represented :
      PARepresentsFunction atomCodeF
    nodeCodeWithRest-represented :
      PARepresentsFunction nodeCodeWithRestF
    numeralTermCodeWithRest-represented :
      PARepresentsFunction numeralTermCodeWithRestF
    numeralTermCode-represented :
      PARepresentsFunction numeralTermCodeF
    closedNumeralEqFormulaCodeWithRest-represented :
      PARepresentsFunction closedNumeralEqFormulaCodeWithRestF
    closedNumeralEqFormulaCode-represented :
      PARepresentsFunction closedNumeralEqFormulaCodeF
    closedNumeralNeqFormulaCode-represented :
      PARepresentsFunction closedNumeralNeqFormulaCodeF

canonicalCodePRBuilders : CanonicalCodePRBuilders
canonicalCodePRBuilders = record
  { encodeNatWithRest-represented = prf-represented encodeNatWithRestF
  ; atomCodeWithRest-represented = prf-represented atomCodeWithRestF
  ; atomCode-represented = prf-represented atomCodeF
  ; nodeCodeWithRest-represented = prf-represented nodeCodeWithRestF
  ; numeralTermCodeWithRest-represented =
      prf-represented numeralTermCodeWithRestF
  ; numeralTermCode-represented =
      prf-represented numeralTermCodeF
  ; closedNumeralEqFormulaCodeWithRest-represented =
      prf-represented closedNumeralEqFormulaCodeWithRestF
  ; closedNumeralEqFormulaCode-represented =
      prf-represented closedNumeralEqFormulaCodeF
  ; closedNumeralNeqFormulaCode-represented =
      prf-represented closedNumeralNeqFormulaCodeF
  }
