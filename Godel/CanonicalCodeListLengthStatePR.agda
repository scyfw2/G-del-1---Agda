{-# OPTIONS --safe #-}

module Godel.CanonicalCodeListLengthStatePR where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List renaming ([] to []ˡ; _∷_ to _∷ˡ_)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.PRBooleanHelpers
  using
    ( fin0
    ; fin1
    ; fin2
    ; fin3
    ; addF
    ; mulF
    ; eqNatF
    ; andF
    ; ifZeroF
    )
open import Godel.PRBoundedSearch using (constF; twoF; threeF)
open import Godel.PRDigitCoding
  using
    ( div4F
    ; mod4F
    ; appendDigitF
    )
open import Godel.PRDigitSemantics
  using
    ( appendDigitF-correct
    ; mod4F-correct
    ; div4F-correct
    ; mod4Nat
    ; div4Nat
    )
import Godel.PRArithmeticSemantics as Arith
open import Godel.PRConcreteSequenceCoding
  using (seqNth-correct-concrete)
import Godel.PRHistoryCoding as History
open import Godel.PRNatListDecoder using (seqNthF)
open import Godel.CanonicalCoding
  using (d0; d1; d2; d3; appendDigit; encodeNatWithRest)
open import Godel.CanonicalCodeParserTargets using (args₂)
import Godel.CanonicalCodeListLengthNumericState as NS

-- A concrete PRF skeleton for the code-list-length scanner.
--
-- The state is encoded as a canonical nat-list:
--
--   [ rest , stack , parsed-length , ok ]
--
-- `rest` is the remaining base-4 input stream, `stack` is a base-5 encoded
-- control stack, `parsed-length` is the root-list length accumulated so far,
-- and `ok` is a Boolean flag.  The control stack cells are:
--
--   1 = root list
--   2 = nested list
--   3 = code
--   4 = nat
--
-- This module builds the actual minimal-basis PRF term that follows the Lean
-- stack-machine prototype.  The remaining proof obligation is to show that its
-- evaluator agrees with `codeListLengthScannerCheck`.

fourF : {n : ℕ} → PRF n
fourF = constF (suc (suc (suc (suc zero))))

fiveF : {n : ℕ} → PRF n
fiveF = constF (suc (suc (suc (suc (suc zero)))))

suc5F : PRF (suc zero)
suc5F =
  compF sucF
    (compF sucF
      (compF sucF
        (compF sucF
          (compF sucF (projF fin0 ∷ []) ∷ []) ∷ []) ∷ []) ∷ [])

ifBoolF : {n : ℕ} → PRF n → PRF n → PRF n → PRF n
ifBoolF cond thenF elseF =
  compF ifZeroF (cond ∷ elseF ∷ thenF ∷ [])

ifEqF : {n : ℕ} → PRF n → ℕ → PRF n → PRF n → PRF n
ifEqF value target thenF elseF =
  ifBoolF
    (compF eqNatF (value ∷ constF target ∷ []))
    thenF
    elseF

mod5StepF : PRF (suc (suc zero))
mod5StepF =
  compF ifZeroF
    (compF eqNatF (projF fin1 ∷ fourF ∷ []) ∷
     compF sucF (projF fin1 ∷ []) ∷
     zeroF ∷ [])

mod5F : PRF (suc zero)
mod5F = precF zeroF mod5StepF

div5StepF : PRF (suc (suc zero))
div5StepF =
  compF ifZeroF
    (compF mod5F (compF sucF (projF fin0 ∷ []) ∷ []) ∷
     compF sucF (projF fin1 ∷ []) ∷
     projF fin1 ∷ [])

div5F : PRF (suc zero)
div5F = precF zeroF div5StepF

append5FrameF : ℕ → PRF (suc zero)
append5FrameF frame =
  precF (constF frame)
    (compF suc5F (projF fin1 ∷ []))

pushFrameF : {n : ℕ} → ℕ → PRF n → PRF n
pushFrameF frame stackF =
  compF (append5FrameF frame) (stackF ∷ [])

encodeNatWithRestF : PRF (suc (suc zero))
encodeNatWithRestF =
  precF
    (appendDigitF d3)
    (compF (appendDigitF d2) (projF fin1 ∷ []))

consNatListF : PRF (suc (suc zero))
consNatListF =
  compF (appendDigitF d1)
    (compF encodeNatWithRestF (projF fin0 ∷ projF fin1 ∷ []) ∷ [])

stateCodeF : PRF (suc (suc (suc (suc zero))))
stateCodeF =
  compF consNatListF
    ( projF fin0 ∷
      compF consNatListF
        ( projF fin1 ∷
          compF consNatListF
            ( projF fin2 ∷
              compF consNatListF
                (projF fin3 ∷ zeroF ∷ []) ∷ []) ∷ []) ∷ [])

encodeNatWithRestF-correct :
  (n rest : ℕ) →
  evalPRF encodeNatWithRestF (n ∷ rest ∷ []) ≡
  encodeNatWithRest n rest
encodeNatWithRestF-correct zero rest
  rewrite appendDigitF-correct d3 rest =
  refl
encodeNatWithRestF-correct (suc n) rest
  rewrite encodeNatWithRestF-correct n rest
        | appendDigitF-correct d2 (encodeNatWithRest n rest) =
  refl

consNatListF-correct :
  (x tail-code : ℕ) →
  evalPRF consNatListF (x ∷ tail-code ∷ []) ≡
  appendDigit d1 (encodeNatWithRest x tail-code)
consNatListF-correct x tail-code
  rewrite encodeNatWithRestF-correct x tail-code
        | appendDigitF-correct d1
            (encodeNatWithRest x tail-code) =
  refl

stateCodeF-correct :
  (rest stack len ok : ℕ) →
  evalPRF stateCodeF (rest ∷ stack ∷ len ∷ ok ∷ []) ≡
  History.historyCode (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)
stateCodeF-correct rest stack len ok
  rewrite consNatListF-correct ok zero
        | consNatListF-correct
            len
            (History.encodeNatListWithRest (ok ∷ˡ []ˡ) zero)
        | consNatListF-correct
            stack
            (History.encodeNatListWithRest (len ∷ˡ ok ∷ˡ []ˡ) zero)
        | consNatListF-correct
            rest
            (History.encodeNatListWithRest
              (stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)
              zero) =
  refl

abstract
  mkStateF :
    {n : ℕ} →
    PRF n → PRF n → PRF n → PRF n → PRF n
  mkStateF restF stackF lenF okF =
    compF stateCodeF (restF ∷ stackF ∷ lenF ∷ okF ∷ [])

  mkStateF-correct :
    {n : ℕ} →
    (restF stackF lenF okF : PRF n) → (xs : Vec ℕ n) →
    evalPRF (mkStateF restF stackF lenF okF) xs ≡
    History.historyCode
      ( evalPRF restF xs
      ∷ˡ evalPRF stackF xs
      ∷ˡ evalPRF lenF xs
      ∷ˡ evalPRF okF xs
      ∷ˡ []ˡ)
  mkStateF-correct restF stackF lenF okF xs
    rewrite stateCodeF-correct
              (evalPRF restF xs)
              (evalPRF stackF xs)
              (evalPRF lenF xs)
              (evalPRF okF xs) =
    refl

stateFieldF : ℕ → PRF (suc zero)
stateFieldF index =
  compF seqNthF (projF fin0 ∷ constF index ∷ [])

stateRestF : PRF (suc zero)
stateRestF = stateFieldF zero

stateStackF : PRF (suc zero)
stateStackF = stateFieldF (suc zero)

stateLenF : PRF (suc zero)
stateLenF = stateFieldF (suc (suc zero))

stateOkF : PRF (suc zero)
stateOkF = stateFieldF (suc (suc (suc zero)))

stateDigitF : PRF (suc zero)
stateDigitF = compF mod4F (stateRestF ∷ [])

stateRestTailF : PRF (suc zero)
stateRestTailF = compF div4F (stateRestF ∷ [])

stateStackTopF : PRF (suc zero)
stateStackTopF = compF mod5F (stateStackF ∷ [])

stateStackTailF : PRF (suc zero)
stateStackTailF = compF div5F (stateStackF ∷ [])

stateLenSucF : PRF (suc zero)
stateLenSucF = compF sucF (stateLenF ∷ [])

stateFailF : PRF (suc zero)
stateFailF =
  mkStateF stateRestF stateStackF stateLenF zeroF

rootD0F : PRF (suc zero)
rootD0F =
  mkStateF stateRestTailF stateStackTailF stateLenF oneF

rootD1F : PRF (suc zero)
rootD1F =
  mkStateF
    stateRestTailF
    (pushFrameF
      (suc (suc (suc zero)))
      (pushFrameF (suc zero) stateStackTailF))
    stateLenSucF
    oneF

nestedD0F : PRF (suc zero)
nestedD0F =
  mkStateF stateRestTailF stateStackTailF stateLenF oneF

nestedD1F : PRF (suc zero)
nestedD1F =
  mkStateF
    stateRestTailF
    (pushFrameF
      (suc (suc (suc zero)))
      (pushFrameF (suc (suc zero)) stateStackTailF))
    stateLenF
    oneF

codeD0F : PRF (suc zero)
codeD0F =
  mkStateF
    stateRestTailF
    (pushFrameF (suc (suc (suc (suc zero)))) stateStackTailF)
    stateLenF
    oneF

codeD1F : PRF (suc zero)
codeD1F =
  mkStateF
    stateRestTailF
    (pushFrameF
      (suc (suc (suc (suc zero))))
      (pushFrameF (suc (suc zero)) stateStackTailF))
    stateLenF
    oneF

natD2F : PRF (suc zero)
natD2F =
  mkStateF stateRestTailF stateStackF stateLenF oneF

natD3F : PRF (suc zero)
natD3F =
  mkStateF stateRestTailF stateStackTailF stateLenF oneF

rootStepF : PRF (suc zero)
rootStepF =
  ifEqF stateDigitF zero rootD0F
    (ifEqF stateDigitF (suc zero) rootD1F stateFailF)

nestedStepF : PRF (suc zero)
nestedStepF =
  ifEqF stateDigitF zero nestedD0F
    (ifEqF stateDigitF (suc zero) nestedD1F stateFailF)

codeStepF : PRF (suc zero)
codeStepF =
  ifEqF stateDigitF zero codeD0F
    (ifEqF stateDigitF (suc zero) codeD1F stateFailF)

natStepF : PRF (suc zero)
natStepF =
  ifEqF stateDigitF (suc (suc zero)) natD2F
    (ifEqF stateDigitF (suc (suc (suc zero))) natD3F stateFailF)

stackNonemptyStepF : PRF (suc zero)
stackNonemptyStepF =
  ifEqF stateStackTopF (suc zero) rootStepF
    (ifEqF stateStackTopF (suc (suc zero)) nestedStepF
      (ifEqF stateStackTopF (suc (suc (suc zero))) codeStepF
        (ifEqF stateStackTopF
          (suc (suc (suc (suc zero))))
          natStepF
          stateFailF)))

stackEmptyStepF : PRF (suc zero)
stackEmptyStepF =
  ifEqF stateRestF zero (projF fin0) stateFailF

stateStepF : PRF (suc zero)
stateStepF =
  ifBoolF stateOkF
    (ifEqF stateStackF zero stackEmptyStepF stackNonemptyStepF)
    (projF fin0)

startStateF : PRF (suc zero)
startStateF =
  mkStateF
    (projF fin0)
    (constF (suc zero))
    zeroF
    oneF

stateStepForPrecF : PRF (suc (suc (suc zero)))
stateStepForPrecF =
  compF stateStepF (projF fin1 ∷ [])

runScannerStateFuelF : PRF (suc (suc zero))
runScannerStateFuelF =
  precF startStateF stateStepForPrecF

runScannerStateF : PRF (suc (suc zero))
runScannerStateF =
  compF runScannerStateFuelF
    (compF sucF (projF fin0 ∷ []) ∷
     projF fin0 ∷ [])

finalRestF : PRF (suc (suc zero))
finalRestF =
  compF stateRestF (runScannerStateF ∷ [])

finalStackF : PRF (suc (suc zero))
finalStackF =
  compF stateStackF (runScannerStateF ∷ [])

finalLenF : PRF (suc (suc zero))
finalLenF =
  compF stateLenF (runScannerStateF ∷ [])

finalOkF : PRF (suc (suc zero))
finalOkF =
  compF stateOkF (runScannerStateF ∷ [])

lengthScannerF : PRF (suc (suc zero))
lengthScannerF =
  compF andF
    ( finalOkF ∷
      compF andF
        ( compF eqNatF (finalRestF ∷ zeroF ∷ []) ∷
          compF andF
            ( compF eqNatF (finalStackF ∷ zeroF ∷ []) ∷
              compF eqNatF (finalLenF ∷ projF fin1 ∷ []) ∷ []) ∷ []) ∷ [])

codeListLengthScannerPR : PRRel (suc (suc zero))
codeListLengthScannerPR = rel lengthScannerF

ifBoolF-correct :
  {n : ℕ} → (cond thenF elseF : PRF n) → (xs : Vec ℕ n) →
  evalPRF (ifBoolF cond thenF elseF) xs ≡
  Arith.ifZeroNat
    (evalPRF cond xs)
    (evalPRF elseF xs)
    (evalPRF thenF xs)
ifBoolF-correct cond thenF elseF xs
  rewrite Arith.ifZeroF-correct
            (evalPRF cond xs)
            (evalPRF elseF xs)
            (evalPRF thenF xs) =
  refl

ifEqF-correct :
  {n : ℕ} → (value : PRF n) → (target : ℕ) →
  (thenF elseF : PRF n) → (xs : Vec ℕ n) →
  evalPRF (ifEqF value target thenF elseF) xs ≡
  Arith.ifZeroNat
    (Arith.eqNatNat (evalPRF value xs) target)
    (evalPRF elseF xs)
    (evalPRF thenF xs)
ifEqF-correct value target thenF elseF xs
  rewrite ifBoolF-correct
            (compF eqNatF (value ∷ constF target ∷ []))
            thenF
            elseF
            xs
        | Arith.constF-correct target xs
        | Arith.eqNatF-correct (evalPRF value xs) target =
  refl

ifBoolF-select-true :
  {n : ℕ} → (cond thenF elseF : PRF n) → (xs : Vec ℕ n) →
  evalPRF cond xs ≡ suc zero →
  evalPRF (ifBoolF cond thenF elseF) xs ≡ evalPRF thenF xs
ifBoolF-select-true cond thenF elseF xs cond-true
  rewrite ifBoolF-correct cond thenF elseF xs
        | cond-true =
  refl

ifBoolF-select-false :
  {n : ℕ} → (cond thenF elseF : PRF n) → (xs : Vec ℕ n) →
  evalPRF cond xs ≡ zero →
  evalPRF (ifBoolF cond thenF elseF) xs ≡ evalPRF elseF xs
ifBoolF-select-false cond thenF elseF xs cond-false
  rewrite ifBoolF-correct cond thenF elseF xs
        | cond-false =
  refl

ifEqF-select-true :
  {n : ℕ} → (value : PRF n) → (target : ℕ) →
  (thenF elseF : PRF n) → (xs : Vec ℕ n) →
  Arith.eqNatNat (evalPRF value xs) target ≡ suc zero →
  evalPRF (ifEqF value target thenF elseF) xs ≡ evalPRF thenF xs
ifEqF-select-true value target thenF elseF xs eq-true
  rewrite ifEqF-correct value target thenF elseF xs
        | eq-true =
  refl

ifEqF-select-false :
  {n : ℕ} → (value : PRF n) → (target : ℕ) →
  (thenF elseF : PRF n) → (xs : Vec ℕ n) →
  Arith.eqNatNat (evalPRF value xs) target ≡ zero →
  evalPRF (ifEqF value target thenF elseF) xs ≡ evalPRF elseF xs
ifEqF-select-false value target thenF elseF xs eq-false
  rewrite ifEqF-correct value target thenF elseF xs
        | eq-false =
  refl

mod5StepNat : ℕ → ℕ
mod5StepNat r =
  Arith.ifZeroNat
    (Arith.eqNatNat r (suc (suc (suc (suc zero)))))
    (suc r)
    zero

mod5StepF-correct :
  (n r : ℕ) →
  evalPRF mod5StepF (n ∷ r ∷ []) ≡ mod5StepNat r
mod5StepF-correct n r
  rewrite Arith.constF-correct
            (suc (suc (suc (suc zero))))
            (n ∷ r ∷ [])
        | Arith.eqNatF-correct r (suc (suc (suc (suc zero))))
        | Arith.ifZeroF-correct
            (Arith.eqNatNat r (suc (suc (suc (suc zero)))))
            (suc r)
            zero =
  refl

mod5Nat-suc :
  (n : ℕ) → NS.mod5Nat (suc n) ≡ mod5StepNat (NS.mod5Nat n)
mod5Nat-suc zero = refl
mod5Nat-suc (suc zero) = refl
mod5Nat-suc (suc (suc zero)) = refl
mod5Nat-suc (suc (suc (suc zero))) = refl
mod5Nat-suc (suc (suc (suc (suc zero)))) = refl
mod5Nat-suc (suc (suc (suc (suc (suc n))))) =
  mod5Nat-suc n

mod5F-correct :
  (n : ℕ) → evalPRF mod5F (n ∷ []) ≡ NS.mod5Nat n
mod5F-correct zero = refl
mod5F-correct (suc n)
  rewrite mod5F-correct n
        | mod5StepF-correct n (NS.mod5Nat n)
        | mod5Nat-suc n =
  refl

div5StepNat : ℕ → ℕ → ℕ
div5StepNat n q =
  Arith.ifZeroNat (NS.mod5Nat (suc n)) (suc q) q

div5StepF-correct :
  (n q : ℕ) →
  evalPRF div5StepF (n ∷ q ∷ []) ≡ div5StepNat n q
div5StepF-correct n q
  rewrite mod5F-correct (suc n)
        | Arith.ifZeroF-correct (NS.mod5Nat (suc n)) (suc q) q =
  refl

suc-ifZeroNat :
  (c t e : ℕ) →
  suc (Arith.ifZeroNat c t e) ≡
  Arith.ifZeroNat c (suc t) (suc e)
suc-ifZeroNat zero t e = refl
suc-ifZeroNat (suc c) t e = refl

div5Nat-suc :
  (n : ℕ) → NS.div5Nat (suc n) ≡ div5StepNat n (NS.div5Nat n)
div5Nat-suc zero = refl
div5Nat-suc (suc zero) = refl
div5Nat-suc (suc (suc zero)) = refl
div5Nat-suc (suc (suc (suc zero))) = refl
div5Nat-suc (suc (suc (suc (suc zero)))) = refl
div5Nat-suc (suc (suc (suc (suc (suc n)))))
  rewrite div5Nat-suc n
        | suc-ifZeroNat
            (NS.mod5Nat (suc n))
            (suc (NS.div5Nat n))
            (NS.div5Nat n) =
  refl

div5F-correct :
  (n : ℕ) → evalPRF div5F (n ∷ []) ≡ NS.div5Nat n
div5F-correct zero = refl
div5F-correct (suc n)
  rewrite div5F-correct n
        | div5StepF-correct n (NS.div5Nat n)
        | div5Nat-suc n =
  refl

suc5F-correct :
  (n : ℕ) →
  evalPRF suc5F (n ∷ []) ≡
  suc (suc (suc (suc (suc n))))
suc5F-correct n = refl

append5FrameF-correct-1 :
  (stack : ℕ) →
  evalPRF (append5FrameF (suc zero)) (stack ∷ []) ≡
  NS.append5 (suc zero) stack
append5FrameF-correct-1 zero
  rewrite Arith.constF-correct (suc zero) [] =
  refl
append5FrameF-correct-1 (suc stack)
  rewrite append5FrameF-correct-1 stack
        | suc5F-correct (NS.append5 (suc zero) stack) =
  refl

append5FrameF-correct-2 :
  (stack : ℕ) →
  evalPRF (append5FrameF (suc (suc zero))) (stack ∷ []) ≡
  NS.append5 (suc (suc zero)) stack
append5FrameF-correct-2 zero
  rewrite Arith.constF-correct (suc (suc zero)) [] =
  refl
append5FrameF-correct-2 (suc stack)
  rewrite append5FrameF-correct-2 stack
        | suc5F-correct (NS.append5 (suc (suc zero)) stack) =
  refl

append5FrameF-correct-3 :
  (stack : ℕ) →
  evalPRF (append5FrameF (suc (suc (suc zero)))) (stack ∷ []) ≡
  NS.append5 (suc (suc (suc zero))) stack
append5FrameF-correct-3 zero
  rewrite Arith.constF-correct (suc (suc (suc zero))) [] =
  refl
append5FrameF-correct-3 (suc stack)
  rewrite append5FrameF-correct-3 stack
        | suc5F-correct (NS.append5 (suc (suc (suc zero))) stack) =
  refl

append5FrameF-correct-4 :
  (stack : ℕ) →
  evalPRF (append5FrameF (suc (suc (suc (suc zero))))) (stack ∷ []) ≡
  NS.append5 (suc (suc (suc (suc zero)))) stack
append5FrameF-correct-4 zero
  rewrite Arith.constF-correct (suc (suc (suc (suc zero)))) [] =
  refl
append5FrameF-correct-4 (suc stack)
  rewrite append5FrameF-correct-4 stack
        | suc5F-correct (NS.append5 (suc (suc (suc (suc zero)))) stack) =
  refl

pushFrameF-correct-1 :
  {n : ℕ} → (stackF : PRF n) → (xs : Vec ℕ n) →
  evalPRF (pushFrameF (suc zero) stackF) xs ≡
  NS.append5 (suc zero) (evalPRF stackF xs)
pushFrameF-correct-1 stackF xs =
  append5FrameF-correct-1 (evalPRF stackF xs)

pushFrameF-correct-2 :
  {n : ℕ} → (stackF : PRF n) → (xs : Vec ℕ n) →
  evalPRF (pushFrameF (suc (suc zero)) stackF) xs ≡
  NS.append5 (suc (suc zero)) (evalPRF stackF xs)
pushFrameF-correct-2 stackF xs =
  append5FrameF-correct-2 (evalPRF stackF xs)

pushFrameF-correct-3 :
  {n : ℕ} → (stackF : PRF n) → (xs : Vec ℕ n) →
  evalPRF (pushFrameF (suc (suc (suc zero))) stackF) xs ≡
  NS.append5 (suc (suc (suc zero))) (evalPRF stackF xs)
pushFrameF-correct-3 stackF xs =
  append5FrameF-correct-3 (evalPRF stackF xs)

pushFrameF-correct-4 :
  {n : ℕ} → (stackF : PRF n) → (xs : Vec ℕ n) →
  evalPRF (pushFrameF (suc (suc (suc (suc zero)))) stackF) xs ≡
  NS.append5 (suc (suc (suc (suc zero)))) (evalPRF stackF xs)
pushFrameF-correct-4 stackF xs =
  append5FrameF-correct-4 (evalPRF stackF xs)

pushFrameF-correct-1-code :
  (stackF : PRF (suc zero)) →
  (rest stack len ok : ℕ) →
  evalPRF
    (pushFrameF (suc zero) stackF)
    (History.historyCode
      (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)
    ∷ []) ≡
  NS.append5
    (suc zero)
    (evalPRF stackF
      (History.historyCode
        (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)
      ∷ []))
pushFrameF-correct-1-code stackF rest stack len ok =
  pushFrameF-correct-1
    stackF
    (History.historyCode
      (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)
    ∷ [])

pushFrameF-correct-2-code :
  (stackF : PRF (suc zero)) →
  (rest stack len ok : ℕ) →
  evalPRF
    (pushFrameF (suc (suc zero)) stackF)
    (History.historyCode
      (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)
    ∷ []) ≡
  NS.append5
    (suc (suc zero))
    (evalPRF stackF
      (History.historyCode
        (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)
      ∷ []))
pushFrameF-correct-2-code stackF rest stack len ok =
  pushFrameF-correct-2
    stackF
    (History.historyCode
      (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)
    ∷ [])

pushFrameF-correct-3-code :
  (stackF : PRF (suc zero)) →
  (rest stack len ok : ℕ) →
  evalPRF
    (pushFrameF (suc (suc (suc zero))) stackF)
    (History.historyCode
      (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)
    ∷ []) ≡
  NS.append5
    (suc (suc (suc zero)))
    (evalPRF stackF
      (History.historyCode
        (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)
      ∷ []))
pushFrameF-correct-3-code stackF rest stack len ok =
  pushFrameF-correct-3
    stackF
    (History.historyCode
      (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)
    ∷ [])

pushFrameF-correct-4-code :
  (stackF : PRF (suc zero)) →
  (rest stack len ok : ℕ) →
  evalPRF
    (pushFrameF (suc (suc (suc (suc zero)))) stackF)
    (History.historyCode
      (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)
    ∷ []) ≡
  NS.append5
    (suc (suc (suc (suc zero))))
    (evalPRF stackF
      (History.historyCode
        (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)
      ∷ []))
pushFrameF-correct-4-code stackF rest stack len ok =
  pushFrameF-correct-4
    stackF
    (History.historyCode
      (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)
    ∷ [])

stateInput : ℕ → ℕ → ℕ → ℕ → ℕ
stateInput rest stack len ok =
  evalPRF stateCodeF (rest ∷ stack ∷ len ∷ ok ∷ [])

stateRestF-correct :
  (rest stack len ok : ℕ) →
  evalPRF stateRestF
    (evalPRF stateCodeF (rest ∷ stack ∷ len ∷ ok ∷ []) ∷ []) ≡
  rest
stateRestF-correct rest stack len ok
  rewrite stateCodeF-correct rest stack len ok
        | seqNth-correct-concrete
            (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)
            zero =
  refl

stateStackF-correct :
  (rest stack len ok : ℕ) →
  evalPRF stateStackF
    (evalPRF stateCodeF (rest ∷ stack ∷ len ∷ ok ∷ []) ∷ []) ≡
  stack
stateStackF-correct rest stack len ok
  rewrite stateCodeF-correct rest stack len ok
        | seqNth-correct-concrete
            (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)
            (suc zero) =
  refl

stateLenF-correct :
  (rest stack len ok : ℕ) →
  evalPRF stateLenF
    (evalPRF stateCodeF (rest ∷ stack ∷ len ∷ ok ∷ []) ∷ []) ≡
  len
stateLenF-correct rest stack len ok
  rewrite stateCodeF-correct rest stack len ok
        | seqNth-correct-concrete
            (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)
            (suc (suc zero)) =
  refl

stateOkF-correct :
  (rest stack len ok : ℕ) →
  evalPRF stateOkF
    (evalPRF stateCodeF (rest ∷ stack ∷ len ∷ ok ∷ []) ∷ []) ≡
  ok
stateOkF-correct rest stack len ok
  rewrite stateCodeF-correct rest stack len ok
        | seqNth-correct-concrete
            (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)
            (suc (suc (suc zero))) =
  refl

stateRestF-correct-code :
  (rest stack len ok : ℕ) →
  evalPRF stateRestF
    (History.historyCode
      (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)
    ∷ []) ≡
  rest
stateRestF-correct-code rest stack len ok
  rewrite sym (stateCodeF-correct rest stack len ok)
        | stateRestF-correct rest stack len ok =
  refl

stateStackF-correct-code :
  (rest stack len ok : ℕ) →
  evalPRF stateStackF
    (History.historyCode
      (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)
    ∷ []) ≡
  stack
stateStackF-correct-code rest stack len ok
  rewrite sym (stateCodeF-correct rest stack len ok)
        | stateStackF-correct rest stack len ok =
  refl

stateLenF-correct-code :
  (rest stack len ok : ℕ) →
  evalPRF stateLenF
    (History.historyCode
      (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)
    ∷ []) ≡
  len
stateLenF-correct-code rest stack len ok
  rewrite sym (stateCodeF-correct rest stack len ok)
        | stateLenF-correct rest stack len ok =
  refl

stateOkF-correct-code :
  (rest stack len ok : ℕ) →
  evalPRF stateOkF
    (History.historyCode
      (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)
    ∷ []) ≡
  ok
stateOkF-correct-code rest stack len ok
  rewrite sym (stateCodeF-correct rest stack len ok)
        | stateOkF-correct rest stack len ok =
  refl

stateDigitF-correct-code :
  (rest stack len ok : ℕ) →
  evalPRF stateDigitF
    (History.historyCode
      (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)
    ∷ []) ≡
  mod4Nat rest
stateDigitF-correct-code rest stack len ok
  rewrite stateRestF-correct-code rest stack len ok
        | mod4F-correct rest =
  refl

stateStackTopF-correct-code :
  (rest stack len ok : ℕ) →
  evalPRF stateStackTopF
    (History.historyCode
      (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)
    ∷ []) ≡
  NS.mod5Nat stack
stateStackTopF-correct-code rest stack len ok
  rewrite stateStackF-correct-code rest stack len ok
        | mod5F-correct stack =
  refl

stateDigitF-correct :
  (rest stack len ok : ℕ) →
  evalPRF stateDigitF
    (evalPRF stateCodeF (rest ∷ stack ∷ len ∷ ok ∷ []) ∷ []) ≡
  mod4Nat rest
stateDigitF-correct rest stack len ok
  rewrite stateRestF-correct rest stack len ok
        | mod4F-correct rest =
  refl

stateRestTailF-correct :
  (rest stack len ok : ℕ) →
  evalPRF stateRestTailF
    (evalPRF stateCodeF (rest ∷ stack ∷ len ∷ ok ∷ []) ∷ []) ≡
  div4Nat rest
stateRestTailF-correct rest stack len ok
  rewrite stateRestF-correct rest stack len ok
        | div4F-correct rest =
  refl

stateStackTopF-correct :
  (rest stack len ok : ℕ) →
  evalPRF stateStackTopF
    (evalPRF stateCodeF (rest ∷ stack ∷ len ∷ ok ∷ []) ∷ []) ≡
  NS.mod5Nat stack
stateStackTopF-correct rest stack len ok
  rewrite stateStackF-correct rest stack len ok
        | mod5F-correct stack =
  refl

stateStackTailF-correct :
  (rest stack len ok : ℕ) →
  evalPRF stateStackTailF
    (evalPRF stateCodeF (rest ∷ stack ∷ len ∷ ok ∷ []) ∷ []) ≡
  NS.div5Nat stack
stateStackTailF-correct rest stack len ok
  rewrite stateStackF-correct rest stack len ok
        | div5F-correct stack =
  refl

stateLenSucF-correct :
  (rest stack len ok : ℕ) →
  evalPRF stateLenSucF
    (evalPRF stateCodeF (rest ∷ stack ∷ len ∷ ok ∷ []) ∷ []) ≡
  suc len
stateLenSucF-correct rest stack len ok
  rewrite stateLenF-correct rest stack len ok =
  refl

stateRestTailF-correct-code :
  (rest stack len ok : ℕ) →
  evalPRF stateRestTailF
    (History.historyCode
      (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)
    ∷ []) ≡
  div4Nat rest
stateRestTailF-correct-code rest stack len ok
  rewrite stateRestF-correct-code rest stack len ok
        | div4F-correct rest =
  refl

stateStackTailF-correct-code :
  (rest stack len ok : ℕ) →
  evalPRF stateStackTailF
    (History.historyCode
      (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)
    ∷ []) ≡
  NS.div5Nat stack
stateStackTailF-correct-code rest stack len ok
  rewrite stateStackF-correct-code rest stack len ok
        | div5F-correct stack =
  refl

stateLenSucF-correct-code :
  (rest stack len ok : ℕ) →
  evalPRF stateLenSucF
    (History.historyCode
      (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)
    ∷ []) ≡
  suc len
stateLenSucF-correct-code rest stack len ok
  rewrite stateLenF-correct-code rest stack len ok =
  refl

stateFailF-correct :
  (rest stack len ok : ℕ) →
  evalPRF stateFailF
    (evalPRF stateCodeF (rest ∷ stack ∷ len ∷ ok ∷ []) ∷ []) ≡
  evalPRF stateCodeF (rest ∷ stack ∷ len ∷ zero ∷ [])
stateFailF-correct rest stack len ok
  rewrite mkStateF-correct
            stateRestF
            stateStackF
            stateLenF
            zeroF
            (evalPRF stateCodeF (rest ∷ stack ∷ len ∷ ok ∷ []) ∷ [])
        | stateRestF-correct rest stack len ok
        | stateStackF-correct rest stack len ok
        | stateLenF-correct rest stack len ok
        | stateCodeF-correct rest stack len zero =
  refl

-- The theorem still to prove in the next step:
--
--   evalPRF lengthScannerF (args₂ list-code len)
--     ≡ codeListLengthScannerCheck list-code len
--
-- Once proved, `Godel.CanonicalCodeListLengthScanner.scannerCandidate->checkCandidate`
-- turns this PRF into the `CodeListLengthPRCandidate` needed by rule37.
