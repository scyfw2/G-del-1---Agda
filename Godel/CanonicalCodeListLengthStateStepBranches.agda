{-# OPTIONS --safe #-}

module Godel.CanonicalCodeListLengthStateStepBranches where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List renaming ([] to []ˡ; _∷_ to _∷ˡ_)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.CanonicalCoding using (Digit; d0; d1; d2; d3; appendDigit)
open import Godel.PRDigitSemantics using (mod4Nat-appendDigit; div4Nat-appendDigit)
import Godel.PRArithmeticSemantics as Arith
import Godel.PRHistoryCoding as History
import Godel.CanonicalCodeListLengthStackMachine as SM
import Godel.CanonicalCodeListLengthNumericState as NS
import Godel.CanonicalCodeListLengthStatePR as StatePR

-- Branch-wise bridge from the concrete PRF state step to the stable numeric
-- state semantics.  This module deliberately uses the canonical state code
-- directly as input; `StatePR.stateCodeF-correct` is used only when proving
-- that a PRF branch builds the expected canonical output state.  That keeps
-- Agda from expanding the full `stateCodeF` primitive-recursive term on both
-- sides of every branch equation.

stateInput : ℕ → ℕ → ℕ → ℕ → ℕ
stateInput rest stack len ok =
  History.historyCode (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ)

historyCode-cong4 :
  {rest rest' stack stack' len len' ok ok' : ℕ} →
  rest ≡ rest' →
  stack ≡ stack' →
  len ≡ len' →
  ok ≡ ok' →
  History.historyCode (rest ∷ˡ stack ∷ˡ len ∷ˡ ok ∷ˡ []ˡ) ≡
  History.historyCode (rest' ∷ˡ stack' ∷ˡ len' ∷ˡ ok' ∷ˡ []ˡ)
historyCode-cong4 refl refl refl refl = refl

oneF-correct :
  {n : ℕ} → (xs : Vec ℕ n) →
  evalPRF oneF xs ≡ suc zero
oneF-correct xs = refl

stateFailF-correct-code :
  (rest stack len ok : ℕ) →
  evalPRF StatePR.stateFailF
    (stateInput rest stack len ok ∷ []) ≡
  stateInput rest stack len zero
stateFailF-correct-code rest stack len ok
  rewrite sym (StatePR.stateCodeF-correct rest stack len ok)
        | StatePR.stateFailF-correct rest stack len ok
        | StatePR.stateCodeF-correct rest stack len zero =
  refl

mkBranch-correct :
  (restF stackF lenF okF : PRF (suc zero)) →
  (in-rest in-stack in-len in-ok : ℕ) →
  (out-rest out-stack out-len out-ok : ℕ) →
  evalPRF restF (stateInput in-rest in-stack in-len in-ok ∷ []) ≡
    out-rest →
  evalPRF stackF (stateInput in-rest in-stack in-len in-ok ∷ []) ≡
    out-stack →
  evalPRF lenF (stateInput in-rest in-stack in-len in-ok ∷ []) ≡
    out-len →
  evalPRF okF (stateInput in-rest in-stack in-len in-ok ∷ []) ≡
    out-ok →
  evalPRF (StatePR.mkStateF restF stackF lenF okF)
    (stateInput in-rest in-stack in-len in-ok ∷ []) ≡
  stateInput out-rest out-stack out-len out-ok
mkBranch-correct restF stackF lenF okF
  in-rest in-stack in-len in-ok
  out-rest out-stack out-len out-ok
  rest-ok stack-ok len-ok ok-ok =
  trans
    (StatePR.mkStateF-correct
      restF
      stackF
      lenF
      okF
      (stateInput in-rest in-stack in-len in-ok ∷ []))
    (historyCode-cong4 rest-ok stack-ok len-ok ok-ok)

restTail-append-correct :
  (d : Digit) →
  (rest stack len ok : ℕ) →
  evalPRF StatePR.stateRestTailF
    (stateInput (appendDigit d rest) stack len ok ∷ []) ≡
  rest
restTail-append-correct d rest stack len ok =
  trans
    (StatePR.stateRestTailF-correct-code
      (appendDigit d rest)
      stack
      len
      ok)
    (div4Nat-appendDigit d rest)

stackTail-push-correct :
  (d : Digit) → (frame : SM.Frame) →
  (rest stack len : ℕ) →
  evalPRF StatePR.stateStackTailF
    (stateInput
      (appendDigit d rest)
      (NS.pushFrame frame stack)
      len
      (suc zero)
    ∷ []) ≡
  stack
stackTail-push-correct d frame rest stack len =
  trans
    (StatePR.stateStackTailF-correct-code
      (appendDigit d rest)
      (NS.pushFrame frame stack)
      len
      (suc zero))
    (NS.stackTail-push frame stack)

digitEq-d0-zero :
  (rest stack len ok : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateDigitF
      (stateInput (appendDigit d0 rest) stack len ok ∷ []))
    zero ≡
  suc zero
digitEq-d0-zero rest stack len ok
  rewrite StatePR.stateDigitF-correct-code
            (appendDigit d0 rest)
            stack
            len
            ok
        | mod4Nat-appendDigit d0 rest =
  refl

digitEq-d1-zero :
  (rest stack len ok : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateDigitF
      (stateInput (appendDigit d1 rest) stack len ok ∷ []))
    zero ≡
  zero
digitEq-d1-zero rest stack len ok
  rewrite StatePR.stateDigitF-correct-code
            (appendDigit d1 rest)
            stack
            len
            ok
        | mod4Nat-appendDigit d1 rest =
  refl

digitEq-d1-one :
  (rest stack len ok : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateDigitF
      (stateInput (appendDigit d1 rest) stack len ok ∷ []))
    (suc zero) ≡
  suc zero
digitEq-d1-one rest stack len ok
  rewrite StatePR.stateDigitF-correct-code
            (appendDigit d1 rest)
            stack
            len
            ok
        | mod4Nat-appendDigit d1 rest =
  refl

digitEq-d1-two :
  (rest stack len ok : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateDigitF
      (stateInput (appendDigit d1 rest) stack len ok ∷ []))
    (suc (suc zero)) ≡
  zero
digitEq-d1-two rest stack len ok
  rewrite StatePR.stateDigitF-correct-code
            (appendDigit d1 rest)
            stack
            len
            ok
        | mod4Nat-appendDigit d1 rest =
  refl

digitEq-d1-three :
  (rest stack len ok : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateDigitF
      (stateInput (appendDigit d1 rest) stack len ok ∷ []))
    (suc (suc (suc zero))) ≡
  zero
digitEq-d1-three rest stack len ok
  rewrite StatePR.stateDigitF-correct-code
            (appendDigit d1 rest)
            stack
            len
            ok
        | mod4Nat-appendDigit d1 rest =
  refl

digitEq-d0-two :
  (rest stack len ok : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateDigitF
      (stateInput (appendDigit d0 rest) stack len ok ∷ []))
    (suc (suc zero)) ≡
  zero
digitEq-d0-two rest stack len ok
  rewrite StatePR.stateDigitF-correct-code
            (appendDigit d0 rest)
            stack
            len
            ok
        | mod4Nat-appendDigit d0 rest =
  refl

digitEq-d0-three :
  (rest stack len ok : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateDigitF
      (stateInput (appendDigit d0 rest) stack len ok ∷ []))
    (suc (suc (suc zero))) ≡
  zero
digitEq-d0-three rest stack len ok
  rewrite StatePR.stateDigitF-correct-code
            (appendDigit d0 rest)
            stack
            len
            ok
        | mod4Nat-appendDigit d0 rest =
  refl

digitEq-d2-two :
  (rest stack len ok : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateDigitF
      (stateInput (appendDigit d2 rest) stack len ok ∷ []))
    (suc (suc zero)) ≡
  suc zero
digitEq-d2-two rest stack len ok
  rewrite StatePR.stateDigitF-correct-code
            (appendDigit d2 rest)
            stack
            len
            ok
        | mod4Nat-appendDigit d2 rest =
  refl

digitEq-d2-zero :
  (rest stack len ok : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateDigitF
      (stateInput (appendDigit d2 rest) stack len ok ∷ []))
    zero ≡
  zero
digitEq-d2-zero rest stack len ok
  rewrite StatePR.stateDigitF-correct-code
            (appendDigit d2 rest)
            stack
            len
            ok
        | mod4Nat-appendDigit d2 rest =
  refl

digitEq-d2-one :
  (rest stack len ok : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateDigitF
      (stateInput (appendDigit d2 rest) stack len ok ∷ []))
    (suc zero) ≡
  zero
digitEq-d2-one rest stack len ok
  rewrite StatePR.stateDigitF-correct-code
            (appendDigit d2 rest)
            stack
            len
            ok
        | mod4Nat-appendDigit d2 rest =
  refl

digitEq-d3-two :
  (rest stack len ok : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateDigitF
      (stateInput (appendDigit d3 rest) stack len ok ∷ []))
    (suc (suc zero)) ≡
  zero
digitEq-d3-two rest stack len ok
  rewrite StatePR.stateDigitF-correct-code
            (appendDigit d3 rest)
            stack
            len
            ok
        | mod4Nat-appendDigit d3 rest =
  refl

digitEq-d3-zero :
  (rest stack len ok : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateDigitF
      (stateInput (appendDigit d3 rest) stack len ok ∷ []))
    zero ≡
  zero
digitEq-d3-zero rest stack len ok
  rewrite StatePR.stateDigitF-correct-code
            (appendDigit d3 rest)
            stack
            len
            ok
        | mod4Nat-appendDigit d3 rest =
  refl

digitEq-d3-one :
  (rest stack len ok : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateDigitF
      (stateInput (appendDigit d3 rest) stack len ok ∷ []))
    (suc zero) ≡
  zero
digitEq-d3-one rest stack len ok
  rewrite StatePR.stateDigitF-correct-code
            (appendDigit d3 rest)
            stack
            len
            ok
        | mod4Nat-appendDigit d3 rest =
  refl

digitEq-d3-three :
  (rest stack len ok : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateDigitF
      (stateInput (appendDigit d3 rest) stack len ok ∷ []))
    (suc (suc (suc zero))) ≡
  suc zero
digitEq-d3-three rest stack len ok
  rewrite StatePR.stateDigitF-correct-code
            (appendDigit d3 rest)
            stack
            len
            ok
        | mod4Nat-appendDigit d3 rest =
  refl

stackTopEq-root-one :
  (rest stack len : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateStackTopF
      (stateInput
        rest
        (NS.pushFrame SM.rootList stack)
        len
        (suc zero)
      ∷ []))
    (suc zero) ≡
  suc zero
stackTopEq-root-one rest stack len
  rewrite StatePR.stateStackTopF-correct-code
            rest
            (NS.pushFrame SM.rootList stack)
            len
            (suc zero)
        | NS.stackTop-push SM.rootList stack =
  refl

stackTopEq-nested-one :
  (rest stack len : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateStackTopF
      (stateInput
        rest
        (NS.pushFrame SM.nestedList stack)
        len
        (suc zero)
      ∷ []))
    (suc zero) ≡
  zero
stackTopEq-nested-one rest stack len
  rewrite StatePR.stateStackTopF-correct-code
            rest
            (NS.pushFrame SM.nestedList stack)
            len
            (suc zero)
        | NS.stackTop-push SM.nestedList stack =
  refl

stackTopEq-nested-two :
  (rest stack len : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateStackTopF
      (stateInput
        rest
        (NS.pushFrame SM.nestedList stack)
        len
        (suc zero)
      ∷ []))
    (suc (suc zero)) ≡
  suc zero
stackTopEq-nested-two rest stack len
  rewrite StatePR.stateStackTopF-correct-code
            rest
            (NS.pushFrame SM.nestedList stack)
            len
            (suc zero)
        | NS.stackTop-push SM.nestedList stack =
  refl

stackTopEq-code-one :
  (rest stack len : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateStackTopF
      (stateInput
        rest
        (NS.pushFrame SM.codeFrame stack)
        len
        (suc zero)
      ∷ []))
    (suc zero) ≡
  zero
stackTopEq-code-one rest stack len
  rewrite StatePR.stateStackTopF-correct-code
            rest
            (NS.pushFrame SM.codeFrame stack)
            len
            (suc zero)
        | NS.stackTop-push SM.codeFrame stack =
  refl

stackTopEq-code-two :
  (rest stack len : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateStackTopF
      (stateInput
        rest
        (NS.pushFrame SM.codeFrame stack)
        len
        (suc zero)
      ∷ []))
    (suc (suc zero)) ≡
  zero
stackTopEq-code-two rest stack len
  rewrite StatePR.stateStackTopF-correct-code
            rest
            (NS.pushFrame SM.codeFrame stack)
            len
            (suc zero)
        | NS.stackTop-push SM.codeFrame stack =
  refl

stackTopEq-code-three :
  (rest stack len : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateStackTopF
      (stateInput
        rest
        (NS.pushFrame SM.codeFrame stack)
        len
        (suc zero)
      ∷ []))
    (suc (suc (suc zero))) ≡
  suc zero
stackTopEq-code-three rest stack len
  rewrite StatePR.stateStackTopF-correct-code
            rest
            (NS.pushFrame SM.codeFrame stack)
            len
            (suc zero)
        | NS.stackTop-push SM.codeFrame stack =
  refl

stackTopEq-nat-one :
  (rest stack len : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateStackTopF
      (stateInput
        rest
        (NS.pushFrame SM.natFrame stack)
        len
        (suc zero)
      ∷ []))
    (suc zero) ≡
  zero
stackTopEq-nat-one rest stack len
  rewrite StatePR.stateStackTopF-correct-code
            rest
            (NS.pushFrame SM.natFrame stack)
            len
            (suc zero)
        | NS.stackTop-push SM.natFrame stack =
  refl

stackTopEq-nat-two :
  (rest stack len : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateStackTopF
      (stateInput
        rest
        (NS.pushFrame SM.natFrame stack)
        len
        (suc zero)
      ∷ []))
    (suc (suc zero)) ≡
  zero
stackTopEq-nat-two rest stack len
  rewrite StatePR.stateStackTopF-correct-code
            rest
            (NS.pushFrame SM.natFrame stack)
            len
            (suc zero)
        | NS.stackTop-push SM.natFrame stack =
  refl

stackTopEq-nat-three :
  (rest stack len : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateStackTopF
      (stateInput
        rest
        (NS.pushFrame SM.natFrame stack)
        len
        (suc zero)
      ∷ []))
    (suc (suc (suc zero))) ≡
  zero
stackTopEq-nat-three rest stack len
  rewrite StatePR.stateStackTopF-correct-code
            rest
            (NS.pushFrame SM.natFrame stack)
            len
            (suc zero)
        | NS.stackTop-push SM.natFrame stack =
  refl

stackTopEq-nat-four :
  (rest stack len : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateStackTopF
      (stateInput
        rest
        (NS.pushFrame SM.natFrame stack)
        len
        (suc zero)
      ∷ []))
    (suc (suc (suc (suc zero)))) ≡
  suc zero
stackTopEq-nat-four rest stack len
  rewrite StatePR.stateStackTopF-correct-code
            rest
            (NS.pushFrame SM.natFrame stack)
            len
            (suc zero)
        | NS.stackTop-push SM.natFrame stack =
  refl

eqNatNat-frame-zero :
  (frame : SM.Frame) → (stack : ℕ) →
  Arith.eqNatNat (NS.pushFrame frame stack) zero ≡ zero
eqNatNat-frame-zero SM.rootList zero = refl
eqNatNat-frame-zero SM.rootList (suc stack) = refl
eqNatNat-frame-zero SM.nestedList zero = refl
eqNatNat-frame-zero SM.nestedList (suc stack) = refl
eqNatNat-frame-zero SM.codeFrame zero = refl
eqNatNat-frame-zero SM.codeFrame (suc stack) = refl
eqNatNat-frame-zero SM.natFrame zero = refl
eqNatNat-frame-zero SM.natFrame (suc stack) = refl

stackEq-push-zero :
  (frame : SM.Frame) →
  (rest stack len : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateStackF
      (stateInput rest (NS.pushFrame frame stack) len (suc zero) ∷ []))
    zero ≡
  zero
stackEq-push-zero frame rest stack len
  rewrite StatePR.stateStackF-correct-code
            rest
            (NS.pushFrame frame stack)
            len
            (suc zero)
        | eqNatNat-frame-zero frame stack =
  refl

stackEq-zero-zero :
  (rest len ok : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateStackF
      (stateInput rest zero len ok ∷ []))
    zero ≡
  suc zero
stackEq-zero-zero rest len ok
  rewrite StatePR.stateStackF-correct-code rest zero len ok =
  refl

restEq-zero-zero :
  (stack len ok : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateRestF
      (stateInput zero stack len ok ∷ []))
    zero ≡
  suc zero
restEq-zero-zero stack len ok
  rewrite StatePR.stateRestF-correct-code zero stack len ok =
  refl

restEq-suc-zero :
  (rest stack len ok : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateRestF
      (stateInput (suc rest) stack len ok ∷ []))
    zero ≡
  zero
restEq-suc-zero rest stack len ok
  rewrite StatePR.stateRestF-correct-code (suc rest) stack len ok =
  refl

stateStepF-nonempty-select :
  (rest stack len : ℕ) →
  Arith.eqNatNat
    (evalPRF StatePR.stateStackF
      (stateInput rest stack len (suc zero) ∷ []))
    zero ≡
  zero →
  evalPRF StatePR.stateStepF
    (stateInput rest stack len (suc zero) ∷ []) ≡
  evalPRF StatePR.stackNonemptyStepF
    (stateInput rest stack len (suc zero) ∷ [])
stateStepF-nonempty-select rest stack len stack-nonzero =
  trans
    (StatePR.ifBoolF-select-true
      StatePR.stateOkF
      (StatePR.ifEqF
        StatePR.stateStackF
        zero
        StatePR.stackEmptyStepF
        StatePR.stackNonemptyStepF)
      (projF fzero)
      (stateInput rest stack len (suc zero) ∷ [])
      (StatePR.stateOkF-correct-code rest stack len (suc zero)))
    (StatePR.ifEqF-select-false
      StatePR.stateStackF
      zero
      StatePR.stackEmptyStepF
      StatePR.stackNonemptyStepF
      (stateInput rest stack len (suc zero) ∷ [])
      stack-nonzero)

pushRootAfterTail-correct :
  (d : Digit) → (frame : SM.Frame) →
  (rest stack len : ℕ) →
  evalPRF (StatePR.pushFrameF (suc zero) StatePR.stateStackTailF)
    (stateInput
      (appendDigit d rest)
      (NS.pushFrame frame stack)
      len
      (suc zero)
    ∷ []) ≡
  NS.pushFrame SM.rootList stack
pushRootAfterTail-correct d frame rest stack len
  rewrite StatePR.pushFrameF-correct-1-code
            StatePR.stateStackTailF
            (appendDigit d rest)
            (NS.pushFrame frame stack)
            len
            (suc zero)
        | stackTail-push-correct d frame rest stack len =
  refl

pushNestedAfterTail-correct :
  (d : Digit) → (frame : SM.Frame) →
  (rest stack len : ℕ) →
  evalPRF (StatePR.pushFrameF (suc (suc zero)) StatePR.stateStackTailF)
    (stateInput
      (appendDigit d rest)
      (NS.pushFrame frame stack)
      len
      (suc zero)
    ∷ []) ≡
  NS.pushFrame SM.nestedList stack
pushNestedAfterTail-correct d frame rest stack len
  rewrite StatePR.pushFrameF-correct-2-code
            StatePR.stateStackTailF
            (appendDigit d rest)
            (NS.pushFrame frame stack)
            len
            (suc zero)
        | stackTail-push-correct d frame rest stack len =
  refl

pushNatAfterTail-correct :
  (d : Digit) → (frame : SM.Frame) →
  (rest stack len : ℕ) →
  evalPRF
    (StatePR.pushFrameF
      (suc (suc (suc (suc zero))))
      StatePR.stateStackTailF)
    (stateInput
      (appendDigit d rest)
      (NS.pushFrame frame stack)
      len
      (suc zero)
    ∷ []) ≡
  NS.pushFrame SM.natFrame stack
pushNatAfterTail-correct d frame rest stack len
  rewrite StatePR.pushFrameF-correct-4-code
            StatePR.stateStackTailF
            (appendDigit d rest)
            (NS.pushFrame frame stack)
            len
            (suc zero)
        | stackTail-push-correct d frame rest stack len =
  refl

rootD0F-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.rootD0F
    (stateInput
      (appendDigit d0 rest)
      (NS.pushFrame SM.rootList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput rest stack len (suc zero)
rootD0F-correct rest stack len
  rewrite StatePR.mkStateF-correct
            StatePR.stateRestTailF
            StatePR.stateStackTailF
            StatePR.stateLenF
            oneF
            (stateInput
              (appendDigit d0 rest)
              (NS.pushFrame SM.rootList stack)
              len
              (suc zero)
            ∷ [])
        | StatePR.stateRestTailF-correct-code
            (appendDigit d0 rest)
            (NS.pushFrame SM.rootList stack)
            len
            (suc zero)
        | div4Nat-appendDigit d0 rest
        | StatePR.stateStackTailF-correct-code
            (appendDigit d0 rest)
            (NS.pushFrame SM.rootList stack)
            len
            (suc zero)
        | NS.stackTail-push SM.rootList stack
        | StatePR.stateLenF-correct-code
            (appendDigit d0 rest)
            (NS.pushFrame SM.rootList stack)
            len
            (suc zero) =
  refl

rootD1StackF-correct :
  (rest stack len : ℕ) →
  evalPRF
    (StatePR.pushFrameF
      (suc (suc (suc zero)))
      (StatePR.pushFrameF (suc zero) StatePR.stateStackTailF))
    (stateInput
      (appendDigit d1 rest)
      (NS.pushFrame SM.rootList stack)
      len
      (suc zero)
    ∷ []) ≡
  NS.pushFrame SM.codeFrame (NS.pushFrame SM.rootList stack)
rootD1StackF-correct rest stack len
  rewrite StatePR.pushFrameF-correct-3-code
            (StatePR.pushFrameF
              (suc zero)
              StatePR.stateStackTailF)
            (appendDigit d1 rest)
            (NS.pushFrame SM.rootList stack)
            len
            (suc zero)
        | StatePR.pushFrameF-correct-1-code
            StatePR.stateStackTailF
            (appendDigit d1 rest)
            (NS.pushFrame SM.rootList stack)
            len
            (suc zero)
        | StatePR.stateStackTailF-correct-code
            (appendDigit d1 rest)
            (NS.pushFrame SM.rootList stack)
            len
            (suc zero)
        | NS.stackTail-push SM.rootList stack =
  refl

rootD1F-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.rootD1F
    (stateInput
      (appendDigit d1 rest)
      (NS.pushFrame SM.rootList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    rest
    (NS.pushFrame SM.codeFrame (NS.pushFrame SM.rootList stack))
    (suc len)
    (suc zero)
rootD1F-correct rest stack len =
  trans
    (StatePR.mkStateF-correct
      StatePR.stateRestTailF
      (StatePR.pushFrameF
        (suc (suc (suc zero)))
        (StatePR.pushFrameF
          (suc zero)
          StatePR.stateStackTailF))
      StatePR.stateLenSucF
      oneF
      (stateInput
        (appendDigit d1 rest)
        (NS.pushFrame SM.rootList stack)
        len
        (suc zero)
      ∷ []))
    (historyCode-cong4
      (trans
        (StatePR.stateRestTailF-correct-code
          (appendDigit d1 rest)
          (NS.pushFrame SM.rootList stack)
          len
          (suc zero))
        (div4Nat-appendDigit d1 rest))
      (rootD1StackF-correct rest stack len)
      (StatePR.stateLenSucF-correct-code
        (appendDigit d1 rest)
        (NS.pushFrame SM.rootList stack)
        len
        (suc zero))
      (oneF-correct
        (stateInput
          (appendDigit d1 rest)
          (NS.pushFrame SM.rootList stack)
          len
        (suc zero)
      ∷ [])))

nestedD0F-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.nestedD0F
    (stateInput
      (appendDigit d0 rest)
      (NS.pushFrame SM.nestedList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput rest stack len (suc zero)
nestedD0F-correct rest stack len =
  mkBranch-correct
    StatePR.stateRestTailF
    StatePR.stateStackTailF
    StatePR.stateLenF
    oneF
    (appendDigit d0 rest)
    (NS.pushFrame SM.nestedList stack)
    len
    (suc zero)
    rest
    stack
    len
    (suc zero)
    (restTail-append-correct
      d0
      rest
      (NS.pushFrame SM.nestedList stack)
      len
      (suc zero))
    (stackTail-push-correct d0 SM.nestedList rest stack len)
    (StatePR.stateLenF-correct-code
      (appendDigit d0 rest)
      (NS.pushFrame SM.nestedList stack)
      len
      (suc zero))
    (oneF-correct
      (stateInput
        (appendDigit d0 rest)
        (NS.pushFrame SM.nestedList stack)
        len
        (suc zero)
      ∷ []))

nestedD1StackF-correct :
  (rest stack len : ℕ) →
  evalPRF
    (StatePR.pushFrameF
      (suc (suc (suc zero)))
      (StatePR.pushFrameF (suc (suc zero)) StatePR.stateStackTailF))
    (stateInput
      (appendDigit d1 rest)
      (NS.pushFrame SM.nestedList stack)
      len
      (suc zero)
    ∷ []) ≡
  NS.pushFrame SM.codeFrame (NS.pushFrame SM.nestedList stack)
nestedD1StackF-correct rest stack len
  rewrite StatePR.pushFrameF-correct-3-code
            (StatePR.pushFrameF
              (suc (suc zero))
              StatePR.stateStackTailF)
            (appendDigit d1 rest)
            (NS.pushFrame SM.nestedList stack)
            len
            (suc zero)
        | pushNestedAfterTail-correct
            d1
            SM.nestedList
            rest
            stack
            len =
  refl

nestedD1F-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.nestedD1F
    (stateInput
      (appendDigit d1 rest)
      (NS.pushFrame SM.nestedList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    rest
    (NS.pushFrame SM.codeFrame (NS.pushFrame SM.nestedList stack))
    len
    (suc zero)
nestedD1F-correct rest stack len =
  mkBranch-correct
    StatePR.stateRestTailF
    (StatePR.pushFrameF
      (suc (suc (suc zero)))
      (StatePR.pushFrameF
        (suc (suc zero))
        StatePR.stateStackTailF))
    StatePR.stateLenF
    oneF
    (appendDigit d1 rest)
    (NS.pushFrame SM.nestedList stack)
    len
    (suc zero)
    rest
    (NS.pushFrame SM.codeFrame (NS.pushFrame SM.nestedList stack))
    len
    (suc zero)
    (restTail-append-correct
      d1
      rest
      (NS.pushFrame SM.nestedList stack)
      len
      (suc zero))
    (nestedD1StackF-correct rest stack len)
    (StatePR.stateLenF-correct-code
      (appendDigit d1 rest)
      (NS.pushFrame SM.nestedList stack)
      len
      (suc zero))
    (oneF-correct
      (stateInput
        (appendDigit d1 rest)
        (NS.pushFrame SM.nestedList stack)
        len
        (suc zero)
      ∷ []))

codeD0F-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.codeD0F
    (stateInput
      (appendDigit d0 rest)
      (NS.pushFrame SM.codeFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput rest (NS.pushFrame SM.natFrame stack) len (suc zero)
codeD0F-correct rest stack len =
  mkBranch-correct
    StatePR.stateRestTailF
    (StatePR.pushFrameF
      (suc (suc (suc (suc zero))))
      StatePR.stateStackTailF)
    StatePR.stateLenF
    oneF
    (appendDigit d0 rest)
    (NS.pushFrame SM.codeFrame stack)
    len
    (suc zero)
    rest
    (NS.pushFrame SM.natFrame stack)
    len
    (suc zero)
    (restTail-append-correct
      d0
      rest
      (NS.pushFrame SM.codeFrame stack)
      len
      (suc zero))
    (pushNatAfterTail-correct d0 SM.codeFrame rest stack len)
    (StatePR.stateLenF-correct-code
      (appendDigit d0 rest)
      (NS.pushFrame SM.codeFrame stack)
      len
      (suc zero))
    (oneF-correct
      (stateInput
        (appendDigit d0 rest)
        (NS.pushFrame SM.codeFrame stack)
        len
        (suc zero)
      ∷ []))

codeD1StackF-correct :
  (rest stack len : ℕ) →
  evalPRF
    (StatePR.pushFrameF
      (suc (suc (suc (suc zero))))
      (StatePR.pushFrameF (suc (suc zero)) StatePR.stateStackTailF))
    (stateInput
      (appendDigit d1 rest)
      (NS.pushFrame SM.codeFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  NS.pushFrame SM.natFrame (NS.pushFrame SM.nestedList stack)
codeD1StackF-correct rest stack len
  rewrite StatePR.pushFrameF-correct-4-code
            (StatePR.pushFrameF
              (suc (suc zero))
              StatePR.stateStackTailF)
            (appendDigit d1 rest)
            (NS.pushFrame SM.codeFrame stack)
            len
            (suc zero)
        | pushNestedAfterTail-correct
            d1
            SM.codeFrame
            rest
            stack
            len =
  refl

codeD1F-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.codeD1F
    (stateInput
      (appendDigit d1 rest)
      (NS.pushFrame SM.codeFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    rest
    (NS.pushFrame SM.natFrame (NS.pushFrame SM.nestedList stack))
    len
    (suc zero)
codeD1F-correct rest stack len =
  mkBranch-correct
    StatePR.stateRestTailF
    (StatePR.pushFrameF
      (suc (suc (suc (suc zero))))
      (StatePR.pushFrameF
        (suc (suc zero))
        StatePR.stateStackTailF))
    StatePR.stateLenF
    oneF
    (appendDigit d1 rest)
    (NS.pushFrame SM.codeFrame stack)
    len
    (suc zero)
    rest
    (NS.pushFrame SM.natFrame (NS.pushFrame SM.nestedList stack))
    len
    (suc zero)
    (restTail-append-correct
      d1
      rest
      (NS.pushFrame SM.codeFrame stack)
      len
      (suc zero))
    (codeD1StackF-correct rest stack len)
    (StatePR.stateLenF-correct-code
      (appendDigit d1 rest)
      (NS.pushFrame SM.codeFrame stack)
      len
      (suc zero))
    (oneF-correct
      (stateInput
        (appendDigit d1 rest)
        (NS.pushFrame SM.codeFrame stack)
        len
        (suc zero)
      ∷ []))

natD2F-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.natD2F
    (stateInput
      (appendDigit d2 rest)
      (NS.pushFrame SM.natFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput rest (NS.pushFrame SM.natFrame stack) len (suc zero)
natD2F-correct rest stack len =
  mkBranch-correct
    StatePR.stateRestTailF
    StatePR.stateStackF
    StatePR.stateLenF
    oneF
    (appendDigit d2 rest)
    (NS.pushFrame SM.natFrame stack)
    len
    (suc zero)
    rest
    (NS.pushFrame SM.natFrame stack)
    len
    (suc zero)
    (restTail-append-correct
      d2
      rest
      (NS.pushFrame SM.natFrame stack)
      len
      (suc zero))
    (StatePR.stateStackF-correct-code
      (appendDigit d2 rest)
      (NS.pushFrame SM.natFrame stack)
      len
      (suc zero))
    (StatePR.stateLenF-correct-code
      (appendDigit d2 rest)
      (NS.pushFrame SM.natFrame stack)
      len
      (suc zero))
    (oneF-correct
      (stateInput
        (appendDigit d2 rest)
        (NS.pushFrame SM.natFrame stack)
        len
        (suc zero)
      ∷ []))

natD3F-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.natD3F
    (stateInput
      (appendDigit d3 rest)
      (NS.pushFrame SM.natFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput rest stack len (suc zero)
natD3F-correct rest stack len =
  mkBranch-correct
    StatePR.stateRestTailF
    StatePR.stateStackTailF
    StatePR.stateLenF
    oneF
    (appendDigit d3 rest)
    (NS.pushFrame SM.natFrame stack)
    len
    (suc zero)
    rest
    stack
    len
    (suc zero)
    (restTail-append-correct
      d3
      rest
      (NS.pushFrame SM.natFrame stack)
      len
      (suc zero))
    (stackTail-push-correct d3 SM.natFrame rest stack len)
    (StatePR.stateLenF-correct-code
      (appendDigit d3 rest)
      (NS.pushFrame SM.natFrame stack)
      len
      (suc zero))
    (oneF-correct
      (stateInput
        (appendDigit d3 rest)
        (NS.pushFrame SM.natFrame stack)
        len
        (suc zero)
      ∷ []))

rootStepF-d0-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.rootStepF
    (stateInput
      (appendDigit d0 rest)
      (NS.pushFrame SM.rootList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput rest stack len (suc zero)
rootStepF-d0-correct rest stack len
  = trans
      (StatePR.ifEqF-select-true
        StatePR.stateDigitF
        zero
        StatePR.rootD0F
        (StatePR.ifEqF
          StatePR.stateDigitF
          (suc zero)
          StatePR.rootD1F
          StatePR.stateFailF)
        (stateInput
          (appendDigit d0 rest)
          (NS.pushFrame SM.rootList stack)
          len
          (suc zero)
        ∷ [])
        (digitEq-d0-zero
          rest
          (NS.pushFrame SM.rootList stack)
          len
          (suc zero)))
      (rootD0F-correct rest stack len)

rootStepF-d1-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.rootStepF
    (stateInput
      (appendDigit d1 rest)
      (NS.pushFrame SM.rootList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    rest
    (NS.pushFrame SM.codeFrame (NS.pushFrame SM.rootList stack))
    (suc len)
    (suc zero)
rootStepF-d1-correct rest stack len =
  trans
    (StatePR.ifEqF-select-false
      StatePR.stateDigitF
      zero
      StatePR.rootD0F
      (StatePR.ifEqF
        StatePR.stateDigitF
        (suc zero)
        StatePR.rootD1F
        StatePR.stateFailF)
      (stateInput
        (appendDigit d1 rest)
        (NS.pushFrame SM.rootList stack)
        len
        (suc zero)
      ∷ [])
      (digitEq-d1-zero
        rest
        (NS.pushFrame SM.rootList stack)
        len
        (suc zero)))
    (trans
      (StatePR.ifEqF-select-true
        StatePR.stateDigitF
        (suc zero)
        StatePR.rootD1F
        StatePR.stateFailF
        (stateInput
          (appendDigit d1 rest)
          (NS.pushFrame SM.rootList stack)
          len
          (suc zero)
        ∷ [])
        (digitEq-d1-one
          rest
          (NS.pushFrame SM.rootList stack)
          len
          (suc zero)))
      (rootD1F-correct rest stack len))

rootStepF-d2-fail-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.rootStepF
    (stateInput
      (appendDigit d2 rest)
      (NS.pushFrame SM.rootList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    (appendDigit d2 rest)
    (NS.pushFrame SM.rootList stack)
    len
    zero
rootStepF-d2-fail-correct rest stack len =
  trans
    (StatePR.ifEqF-select-false
      StatePR.stateDigitF
      zero
      StatePR.rootD0F
      (StatePR.ifEqF
        StatePR.stateDigitF
        (suc zero)
        StatePR.rootD1F
        StatePR.stateFailF)
      (stateInput
        (appendDigit d2 rest)
        (NS.pushFrame SM.rootList stack)
        len
        (suc zero)
      ∷ [])
      (digitEq-d2-zero
        rest
        (NS.pushFrame SM.rootList stack)
        len
        (suc zero)))
    (trans
      (StatePR.ifEqF-select-false
        StatePR.stateDigitF
        (suc zero)
        StatePR.rootD1F
        StatePR.stateFailF
        (stateInput
          (appendDigit d2 rest)
          (NS.pushFrame SM.rootList stack)
          len
          (suc zero)
        ∷ [])
        (digitEq-d2-one
          rest
          (NS.pushFrame SM.rootList stack)
          len
          (suc zero)))
      (stateFailF-correct-code
        (appendDigit d2 rest)
        (NS.pushFrame SM.rootList stack)
        len
        (suc zero)))

rootStepF-d3-fail-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.rootStepF
    (stateInput
      (appendDigit d3 rest)
      (NS.pushFrame SM.rootList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    (appendDigit d3 rest)
    (NS.pushFrame SM.rootList stack)
    len
    zero
rootStepF-d3-fail-correct rest stack len =
  trans
    (StatePR.ifEqF-select-false
      StatePR.stateDigitF
      zero
      StatePR.rootD0F
      (StatePR.ifEqF
        StatePR.stateDigitF
        (suc zero)
        StatePR.rootD1F
        StatePR.stateFailF)
      (stateInput
        (appendDigit d3 rest)
        (NS.pushFrame SM.rootList stack)
        len
        (suc zero)
      ∷ [])
      (digitEq-d3-zero
        rest
        (NS.pushFrame SM.rootList stack)
        len
        (suc zero)))
    (trans
      (StatePR.ifEqF-select-false
        StatePR.stateDigitF
        (suc zero)
        StatePR.rootD1F
        StatePR.stateFailF
        (stateInput
          (appendDigit d3 rest)
          (NS.pushFrame SM.rootList stack)
          len
          (suc zero)
        ∷ [])
        (digitEq-d3-one
          rest
          (NS.pushFrame SM.rootList stack)
          len
          (suc zero)))
      (stateFailF-correct-code
        (appendDigit d3 rest)
        (NS.pushFrame SM.rootList stack)
        len
        (suc zero)))

nestedStepF-d0-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.nestedStepF
    (stateInput
      (appendDigit d0 rest)
      (NS.pushFrame SM.nestedList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput rest stack len (suc zero)
nestedStepF-d0-correct rest stack len =
  trans
    (StatePR.ifEqF-select-true
      StatePR.stateDigitF
      zero
      StatePR.nestedD0F
      (StatePR.ifEqF
        StatePR.stateDigitF
        (suc zero)
        StatePR.nestedD1F
        StatePR.stateFailF)
      (stateInput
        (appendDigit d0 rest)
        (NS.pushFrame SM.nestedList stack)
        len
        (suc zero)
      ∷ [])
      (digitEq-d0-zero
        rest
        (NS.pushFrame SM.nestedList stack)
        len
        (suc zero)))
    (nestedD0F-correct rest stack len)

nestedStepF-d1-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.nestedStepF
    (stateInput
      (appendDigit d1 rest)
      (NS.pushFrame SM.nestedList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    rest
    (NS.pushFrame SM.codeFrame (NS.pushFrame SM.nestedList stack))
    len
    (suc zero)
nestedStepF-d1-correct rest stack len =
  trans
    (StatePR.ifEqF-select-false
      StatePR.stateDigitF
      zero
      StatePR.nestedD0F
      (StatePR.ifEqF
        StatePR.stateDigitF
        (suc zero)
        StatePR.nestedD1F
        StatePR.stateFailF)
      (stateInput
        (appendDigit d1 rest)
        (NS.pushFrame SM.nestedList stack)
        len
        (suc zero)
      ∷ [])
      (digitEq-d1-zero
        rest
        (NS.pushFrame SM.nestedList stack)
        len
        (suc zero)))
    (trans
      (StatePR.ifEqF-select-true
        StatePR.stateDigitF
        (suc zero)
        StatePR.nestedD1F
        StatePR.stateFailF
        (stateInput
          (appendDigit d1 rest)
          (NS.pushFrame SM.nestedList stack)
          len
          (suc zero)
        ∷ [])
        (digitEq-d1-one
          rest
          (NS.pushFrame SM.nestedList stack)
          len
          (suc zero)))
      (nestedD1F-correct rest stack len))

nestedStepF-d2-fail-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.nestedStepF
    (stateInput
      (appendDigit d2 rest)
      (NS.pushFrame SM.nestedList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    (appendDigit d2 rest)
    (NS.pushFrame SM.nestedList stack)
    len
    zero
nestedStepF-d2-fail-correct rest stack len =
  trans
    (StatePR.ifEqF-select-false
      StatePR.stateDigitF
      zero
      StatePR.nestedD0F
      (StatePR.ifEqF
        StatePR.stateDigitF
        (suc zero)
        StatePR.nestedD1F
        StatePR.stateFailF)
      (stateInput
        (appendDigit d2 rest)
        (NS.pushFrame SM.nestedList stack)
        len
        (suc zero)
      ∷ [])
      (digitEq-d2-zero
        rest
        (NS.pushFrame SM.nestedList stack)
        len
        (suc zero)))
    (trans
      (StatePR.ifEqF-select-false
        StatePR.stateDigitF
        (suc zero)
        StatePR.nestedD1F
        StatePR.stateFailF
        (stateInput
          (appendDigit d2 rest)
          (NS.pushFrame SM.nestedList stack)
          len
          (suc zero)
        ∷ [])
        (digitEq-d2-one
          rest
          (NS.pushFrame SM.nestedList stack)
          len
          (suc zero)))
      (stateFailF-correct-code
        (appendDigit d2 rest)
        (NS.pushFrame SM.nestedList stack)
        len
        (suc zero)))

nestedStepF-d3-fail-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.nestedStepF
    (stateInput
      (appendDigit d3 rest)
      (NS.pushFrame SM.nestedList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    (appendDigit d3 rest)
    (NS.pushFrame SM.nestedList stack)
    len
    zero
nestedStepF-d3-fail-correct rest stack len =
  trans
    (StatePR.ifEqF-select-false
      StatePR.stateDigitF
      zero
      StatePR.nestedD0F
      (StatePR.ifEqF
        StatePR.stateDigitF
        (suc zero)
        StatePR.nestedD1F
        StatePR.stateFailF)
      (stateInput
        (appendDigit d3 rest)
        (NS.pushFrame SM.nestedList stack)
        len
        (suc zero)
      ∷ [])
      (digitEq-d3-zero
        rest
        (NS.pushFrame SM.nestedList stack)
        len
        (suc zero)))
    (trans
      (StatePR.ifEqF-select-false
        StatePR.stateDigitF
        (suc zero)
        StatePR.nestedD1F
        StatePR.stateFailF
        (stateInput
          (appendDigit d3 rest)
          (NS.pushFrame SM.nestedList stack)
          len
          (suc zero)
        ∷ [])
        (digitEq-d3-one
          rest
          (NS.pushFrame SM.nestedList stack)
          len
          (suc zero)))
      (stateFailF-correct-code
        (appendDigit d3 rest)
        (NS.pushFrame SM.nestedList stack)
        len
        (suc zero)))

codeStepF-d0-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.codeStepF
    (stateInput
      (appendDigit d0 rest)
      (NS.pushFrame SM.codeFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput rest (NS.pushFrame SM.natFrame stack) len (suc zero)
codeStepF-d0-correct rest stack len =
  trans
    (StatePR.ifEqF-select-true
      StatePR.stateDigitF
      zero
      StatePR.codeD0F
      (StatePR.ifEqF
        StatePR.stateDigitF
        (suc zero)
        StatePR.codeD1F
        StatePR.stateFailF)
      (stateInput
        (appendDigit d0 rest)
        (NS.pushFrame SM.codeFrame stack)
        len
        (suc zero)
      ∷ [])
      (digitEq-d0-zero
        rest
        (NS.pushFrame SM.codeFrame stack)
        len
        (suc zero)))
    (codeD0F-correct rest stack len)

codeStepF-d1-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.codeStepF
    (stateInput
      (appendDigit d1 rest)
      (NS.pushFrame SM.codeFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    rest
    (NS.pushFrame SM.natFrame (NS.pushFrame SM.nestedList stack))
    len
    (suc zero)
codeStepF-d1-correct rest stack len =
  trans
    (StatePR.ifEqF-select-false
      StatePR.stateDigitF
      zero
      StatePR.codeD0F
      (StatePR.ifEqF
        StatePR.stateDigitF
        (suc zero)
        StatePR.codeD1F
        StatePR.stateFailF)
      (stateInput
        (appendDigit d1 rest)
        (NS.pushFrame SM.codeFrame stack)
        len
        (suc zero)
      ∷ [])
      (digitEq-d1-zero
        rest
        (NS.pushFrame SM.codeFrame stack)
        len
        (suc zero)))
    (trans
      (StatePR.ifEqF-select-true
        StatePR.stateDigitF
        (suc zero)
        StatePR.codeD1F
        StatePR.stateFailF
        (stateInput
          (appendDigit d1 rest)
          (NS.pushFrame SM.codeFrame stack)
          len
          (suc zero)
        ∷ [])
        (digitEq-d1-one
          rest
          (NS.pushFrame SM.codeFrame stack)
          len
          (suc zero)))
      (codeD1F-correct rest stack len))

codeStepF-d2-fail-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.codeStepF
    (stateInput
      (appendDigit d2 rest)
      (NS.pushFrame SM.codeFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    (appendDigit d2 rest)
    (NS.pushFrame SM.codeFrame stack)
    len
    zero
codeStepF-d2-fail-correct rest stack len =
  trans
    (StatePR.ifEqF-select-false
      StatePR.stateDigitF
      zero
      StatePR.codeD0F
      (StatePR.ifEqF
        StatePR.stateDigitF
        (suc zero)
        StatePR.codeD1F
        StatePR.stateFailF)
      (stateInput
        (appendDigit d2 rest)
        (NS.pushFrame SM.codeFrame stack)
        len
        (suc zero)
      ∷ [])
      (digitEq-d2-zero
        rest
        (NS.pushFrame SM.codeFrame stack)
        len
        (suc zero)))
    (trans
      (StatePR.ifEqF-select-false
        StatePR.stateDigitF
        (suc zero)
        StatePR.codeD1F
        StatePR.stateFailF
        (stateInput
          (appendDigit d2 rest)
          (NS.pushFrame SM.codeFrame stack)
          len
          (suc zero)
        ∷ [])
        (digitEq-d2-one
          rest
          (NS.pushFrame SM.codeFrame stack)
          len
          (suc zero)))
      (stateFailF-correct-code
        (appendDigit d2 rest)
        (NS.pushFrame SM.codeFrame stack)
        len
        (suc zero)))

codeStepF-d3-fail-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.codeStepF
    (stateInput
      (appendDigit d3 rest)
      (NS.pushFrame SM.codeFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    (appendDigit d3 rest)
    (NS.pushFrame SM.codeFrame stack)
    len
    zero
codeStepF-d3-fail-correct rest stack len =
  trans
    (StatePR.ifEqF-select-false
      StatePR.stateDigitF
      zero
      StatePR.codeD0F
      (StatePR.ifEqF
        StatePR.stateDigitF
        (suc zero)
        StatePR.codeD1F
        StatePR.stateFailF)
      (stateInput
        (appendDigit d3 rest)
        (NS.pushFrame SM.codeFrame stack)
        len
        (suc zero)
      ∷ [])
      (digitEq-d3-zero
        rest
        (NS.pushFrame SM.codeFrame stack)
        len
        (suc zero)))
    (trans
      (StatePR.ifEqF-select-false
        StatePR.stateDigitF
        (suc zero)
        StatePR.codeD1F
        StatePR.stateFailF
        (stateInput
          (appendDigit d3 rest)
          (NS.pushFrame SM.codeFrame stack)
          len
          (suc zero)
        ∷ [])
        (digitEq-d3-one
          rest
          (NS.pushFrame SM.codeFrame stack)
          len
          (suc zero)))
      (stateFailF-correct-code
        (appendDigit d3 rest)
        (NS.pushFrame SM.codeFrame stack)
        len
        (suc zero)))

natStepF-d2-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.natStepF
    (stateInput
      (appendDigit d2 rest)
      (NS.pushFrame SM.natFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput rest (NS.pushFrame SM.natFrame stack) len (suc zero)
natStepF-d2-correct rest stack len =
  trans
    (StatePR.ifEqF-select-true
      StatePR.stateDigitF
      (suc (suc zero))
      StatePR.natD2F
      (StatePR.ifEqF
        StatePR.stateDigitF
        (suc (suc (suc zero)))
        StatePR.natD3F
        StatePR.stateFailF)
      (stateInput
        (appendDigit d2 rest)
        (NS.pushFrame SM.natFrame stack)
        len
        (suc zero)
      ∷ [])
      (digitEq-d2-two
        rest
        (NS.pushFrame SM.natFrame stack)
        len
        (suc zero)))
    (natD2F-correct rest stack len)

natStepF-d3-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.natStepF
    (stateInput
      (appendDigit d3 rest)
      (NS.pushFrame SM.natFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput rest stack len (suc zero)
natStepF-d3-correct rest stack len =
  trans
    (StatePR.ifEqF-select-false
      StatePR.stateDigitF
      (suc (suc zero))
      StatePR.natD2F
      (StatePR.ifEqF
        StatePR.stateDigitF
        (suc (suc (suc zero)))
        StatePR.natD3F
        StatePR.stateFailF)
      (stateInput
        (appendDigit d3 rest)
        (NS.pushFrame SM.natFrame stack)
        len
        (suc zero)
      ∷ [])
      (digitEq-d3-two
        rest
        (NS.pushFrame SM.natFrame stack)
        len
        (suc zero)))
    (trans
      (StatePR.ifEqF-select-true
        StatePR.stateDigitF
        (suc (suc (suc zero)))
        StatePR.natD3F
        StatePR.stateFailF
        (stateInput
          (appendDigit d3 rest)
          (NS.pushFrame SM.natFrame stack)
          len
          (suc zero)
        ∷ [])
            (digitEq-d3-three
              rest
              (NS.pushFrame SM.natFrame stack)
              len
              (suc zero)))
      (natD3F-correct rest stack len))

natStepF-d0-fail-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.natStepF
    (stateInput
      (appendDigit d0 rest)
      (NS.pushFrame SM.natFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    (appendDigit d0 rest)
    (NS.pushFrame SM.natFrame stack)
    len
    zero
natStepF-d0-fail-correct rest stack len =
  trans
    (StatePR.ifEqF-select-false
      StatePR.stateDigitF
      (suc (suc zero))
      StatePR.natD2F
      (StatePR.ifEqF
        StatePR.stateDigitF
        (suc (suc (suc zero)))
        StatePR.natD3F
        StatePR.stateFailF)
      (stateInput
        (appendDigit d0 rest)
        (NS.pushFrame SM.natFrame stack)
        len
        (suc zero)
      ∷ [])
      (digitEq-d0-two
        rest
        (NS.pushFrame SM.natFrame stack)
        len
        (suc zero)))
    (trans
      (StatePR.ifEqF-select-false
        StatePR.stateDigitF
        (suc (suc (suc zero)))
        StatePR.natD3F
        StatePR.stateFailF
        (stateInput
          (appendDigit d0 rest)
          (NS.pushFrame SM.natFrame stack)
          len
          (suc zero)
        ∷ [])
        (digitEq-d0-three
          rest
          (NS.pushFrame SM.natFrame stack)
          len
          (suc zero)))
      (stateFailF-correct-code
        (appendDigit d0 rest)
        (NS.pushFrame SM.natFrame stack)
        len
        (suc zero)))

natStepF-d1-fail-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.natStepF
    (stateInput
      (appendDigit d1 rest)
      (NS.pushFrame SM.natFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    (appendDigit d1 rest)
    (NS.pushFrame SM.natFrame stack)
    len
    zero
natStepF-d1-fail-correct rest stack len =
  trans
    (StatePR.ifEqF-select-false
      StatePR.stateDigitF
      (suc (suc zero))
      StatePR.natD2F
      (StatePR.ifEqF
        StatePR.stateDigitF
        (suc (suc (suc zero)))
        StatePR.natD3F
        StatePR.stateFailF)
      (stateInput
        (appendDigit d1 rest)
        (NS.pushFrame SM.natFrame stack)
        len
        (suc zero)
      ∷ [])
      (digitEq-d1-two
        rest
        (NS.pushFrame SM.natFrame stack)
        len
        (suc zero)))
    (trans
      (StatePR.ifEqF-select-false
        StatePR.stateDigitF
        (suc (suc (suc zero)))
        StatePR.natD3F
        StatePR.stateFailF
        (stateInput
          (appendDigit d1 rest)
          (NS.pushFrame SM.natFrame stack)
          len
          (suc zero)
        ∷ [])
        (digitEq-d1-three
          rest
          (NS.pushFrame SM.natFrame stack)
          len
          (suc zero)))
      (stateFailF-correct-code
        (appendDigit d1 rest)
        (NS.pushFrame SM.natFrame stack)
        len
        (suc zero)))

stackNonemptyStepF-root-d0-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stackNonemptyStepF
    (stateInput
      (appendDigit d0 rest)
      (NS.pushFrame SM.rootList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput rest stack len (suc zero)
stackNonemptyStepF-root-d0-correct rest stack len =
  trans
    (StatePR.ifEqF-select-true
      StatePR.stateStackTopF
      (suc zero)
      StatePR.rootStepF
      (StatePR.ifEqF
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF)))
      (stateInput
        (appendDigit d0 rest)
        (NS.pushFrame SM.rootList stack)
        len
        (suc zero)
      ∷ [])
      (stackTopEq-root-one (appendDigit d0 rest) stack len))
    (rootStepF-d0-correct rest stack len)

stackNonemptyStepF-root-d1-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stackNonemptyStepF
    (stateInput
      (appendDigit d1 rest)
      (NS.pushFrame SM.rootList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    rest
    (NS.pushFrame SM.codeFrame (NS.pushFrame SM.rootList stack))
    (suc len)
    (suc zero)
stackNonemptyStepF-root-d1-correct rest stack len =
  trans
    (StatePR.ifEqF-select-true
      StatePR.stateStackTopF
      (suc zero)
      StatePR.rootStepF
      (StatePR.ifEqF
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF)))
      (stateInput
        (appendDigit d1 rest)
        (NS.pushFrame SM.rootList stack)
        len
        (suc zero)
      ∷ [])
      (stackTopEq-root-one (appendDigit d1 rest) stack len))
    (rootStepF-d1-correct rest stack len)

stackNonemptyStepF-nested-d0-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stackNonemptyStepF
    (stateInput
      (appendDigit d0 rest)
      (NS.pushFrame SM.nestedList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput rest stack len (suc zero)
stackNonemptyStepF-nested-d0-correct rest stack len =
  trans
    (StatePR.ifEqF-select-false
      StatePR.stateStackTopF
      (suc zero)
      StatePR.rootStepF
      (StatePR.ifEqF
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF)))
      (stateInput
        (appendDigit d0 rest)
        (NS.pushFrame SM.nestedList stack)
        len
        (suc zero)
      ∷ [])
      (stackTopEq-nested-one (appendDigit d0 rest) stack len))
    (trans
      (StatePR.ifEqF-select-true
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF))
        (stateInput
          (appendDigit d0 rest)
          (NS.pushFrame SM.nestedList stack)
          len
          (suc zero)
        ∷ [])
        (stackTopEq-nested-two (appendDigit d0 rest) stack len))
      (nestedStepF-d0-correct rest stack len))

stackNonemptyStepF-nested-d1-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stackNonemptyStepF
    (stateInput
      (appendDigit d1 rest)
      (NS.pushFrame SM.nestedList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    rest
    (NS.pushFrame SM.codeFrame (NS.pushFrame SM.nestedList stack))
    len
    (suc zero)
stackNonemptyStepF-nested-d1-correct rest stack len =
  trans
    (StatePR.ifEqF-select-false
      StatePR.stateStackTopF
      (suc zero)
      StatePR.rootStepF
      (StatePR.ifEqF
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF)))
      (stateInput
        (appendDigit d1 rest)
        (NS.pushFrame SM.nestedList stack)
        len
        (suc zero)
      ∷ [])
      (stackTopEq-nested-one (appendDigit d1 rest) stack len))
    (trans
      (StatePR.ifEqF-select-true
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF))
        (stateInput
          (appendDigit d1 rest)
          (NS.pushFrame SM.nestedList stack)
          len
          (suc zero)
        ∷ [])
        (stackTopEq-nested-two (appendDigit d1 rest) stack len))
      (nestedStepF-d1-correct rest stack len))

stackNonemptyStepF-code-d0-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stackNonemptyStepF
    (stateInput
      (appendDigit d0 rest)
      (NS.pushFrame SM.codeFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput rest (NS.pushFrame SM.natFrame stack) len (suc zero)
stackNonemptyStepF-code-d0-correct rest stack len =
  trans
    (StatePR.ifEqF-select-false
      StatePR.stateStackTopF
      (suc zero)
      StatePR.rootStepF
      (StatePR.ifEqF
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF)))
      (stateInput
        (appendDigit d0 rest)
        (NS.pushFrame SM.codeFrame stack)
        len
        (suc zero)
      ∷ [])
      (stackTopEq-code-one (appendDigit d0 rest) stack len))
    (trans
      (StatePR.ifEqF-select-false
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF))
        (stateInput
          (appendDigit d0 rest)
          (NS.pushFrame SM.codeFrame stack)
          len
          (suc zero)
        ∷ [])
        (stackTopEq-code-two (appendDigit d0 rest) stack len))
      (trans
        (StatePR.ifEqF-select-true
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF)
          (stateInput
            (appendDigit d0 rest)
            (NS.pushFrame SM.codeFrame stack)
            len
            (suc zero)
          ∷ [])
          (stackTopEq-code-three (appendDigit d0 rest) stack len))
        (codeStepF-d0-correct rest stack len)))

stackNonemptyStepF-code-d1-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stackNonemptyStepF
    (stateInput
      (appendDigit d1 rest)
      (NS.pushFrame SM.codeFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    rest
    (NS.pushFrame SM.natFrame (NS.pushFrame SM.nestedList stack))
    len
    (suc zero)
stackNonemptyStepF-code-d1-correct rest stack len =
  trans
    (StatePR.ifEqF-select-false
      StatePR.stateStackTopF
      (suc zero)
      StatePR.rootStepF
      (StatePR.ifEqF
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF)))
      (stateInput
        (appendDigit d1 rest)
        (NS.pushFrame SM.codeFrame stack)
        len
        (suc zero)
      ∷ [])
      (stackTopEq-code-one (appendDigit d1 rest) stack len))
    (trans
      (StatePR.ifEqF-select-false
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF))
        (stateInput
          (appendDigit d1 rest)
          (NS.pushFrame SM.codeFrame stack)
          len
          (suc zero)
        ∷ [])
        (stackTopEq-code-two (appendDigit d1 rest) stack len))
      (trans
        (StatePR.ifEqF-select-true
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF)
          (stateInput
            (appendDigit d1 rest)
            (NS.pushFrame SM.codeFrame stack)
            len
            (suc zero)
          ∷ [])
          (stackTopEq-code-three (appendDigit d1 rest) stack len))
        (codeStepF-d1-correct rest stack len)))

stackNonemptyStepF-nat-d2-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stackNonemptyStepF
    (stateInput
      (appendDigit d2 rest)
      (NS.pushFrame SM.natFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput rest (NS.pushFrame SM.natFrame stack) len (suc zero)
stackNonemptyStepF-nat-d2-correct rest stack len =
  trans
    (StatePR.ifEqF-select-false
      StatePR.stateStackTopF
      (suc zero)
      StatePR.rootStepF
      (StatePR.ifEqF
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF)))
      (stateInput
        (appendDigit d2 rest)
        (NS.pushFrame SM.natFrame stack)
        len
        (suc zero)
      ∷ [])
      (stackTopEq-nat-one (appendDigit d2 rest) stack len))
    (trans
      (StatePR.ifEqF-select-false
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF))
        (stateInput
          (appendDigit d2 rest)
          (NS.pushFrame SM.natFrame stack)
          len
          (suc zero)
        ∷ [])
        (stackTopEq-nat-two (appendDigit d2 rest) stack len))
      (trans
        (StatePR.ifEqF-select-false
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF)
          (stateInput
            (appendDigit d2 rest)
            (NS.pushFrame SM.natFrame stack)
            len
            (suc zero)
          ∷ [])
          (stackTopEq-nat-three (appendDigit d2 rest) stack len))
        (trans
          (StatePR.ifEqF-select-true
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF
            (stateInput
              (appendDigit d2 rest)
              (NS.pushFrame SM.natFrame stack)
              len
              (suc zero)
            ∷ [])
            (stackTopEq-nat-four (appendDigit d2 rest) stack len))
          (natStepF-d2-correct rest stack len))))

stackNonemptyStepF-nat-d3-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stackNonemptyStepF
    (stateInput
      (appendDigit d3 rest)
      (NS.pushFrame SM.natFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput rest stack len (suc zero)
stackNonemptyStepF-nat-d3-correct rest stack len =
  trans
    (StatePR.ifEqF-select-false
      StatePR.stateStackTopF
      (suc zero)
      StatePR.rootStepF
      (StatePR.ifEqF
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF)))
      (stateInput
        (appendDigit d3 rest)
        (NS.pushFrame SM.natFrame stack)
        len
        (suc zero)
      ∷ [])
      (stackTopEq-nat-one (appendDigit d3 rest) stack len))
    (trans
      (StatePR.ifEqF-select-false
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF))
        (stateInput
          (appendDigit d3 rest)
          (NS.pushFrame SM.natFrame stack)
          len
          (suc zero)
        ∷ [])
        (stackTopEq-nat-two (appendDigit d3 rest) stack len))
      (trans
        (StatePR.ifEqF-select-false
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF)
          (stateInput
            (appendDigit d3 rest)
            (NS.pushFrame SM.natFrame stack)
            len
            (suc zero)
          ∷ [])
          (stackTopEq-nat-three (appendDigit d3 rest) stack len))
        (trans
          (StatePR.ifEqF-select-true
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF
            (stateInput
              (appendDigit d3 rest)
              (NS.pushFrame SM.natFrame stack)
              len
              (suc zero)
            ∷ [])
            (stackTopEq-nat-four (appendDigit d3 rest) stack len))
          (natStepF-d3-correct rest stack len))))

stackNonemptyStepF-root-d2-fail-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stackNonemptyStepF
    (stateInput
      (appendDigit d2 rest)
      (NS.pushFrame SM.rootList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    (appendDigit d2 rest)
    (NS.pushFrame SM.rootList stack)
    len
    zero
stackNonemptyStepF-root-d2-fail-correct rest stack len =
  trans
    (StatePR.ifEqF-select-true
      StatePR.stateStackTopF
      (suc zero)
      StatePR.rootStepF
      (StatePR.ifEqF
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF)))
      (stateInput
        (appendDigit d2 rest)
        (NS.pushFrame SM.rootList stack)
        len
        (suc zero)
      ∷ [])
      (stackTopEq-root-one (appendDigit d2 rest) stack len))
    (rootStepF-d2-fail-correct rest stack len)

stackNonemptyStepF-root-d3-fail-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stackNonemptyStepF
    (stateInput
      (appendDigit d3 rest)
      (NS.pushFrame SM.rootList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    (appendDigit d3 rest)
    (NS.pushFrame SM.rootList stack)
    len
    zero
stackNonemptyStepF-root-d3-fail-correct rest stack len =
  trans
    (StatePR.ifEqF-select-true
      StatePR.stateStackTopF
      (suc zero)
      StatePR.rootStepF
      (StatePR.ifEqF
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF)))
      (stateInput
        (appendDigit d3 rest)
        (NS.pushFrame SM.rootList stack)
        len
        (suc zero)
      ∷ [])
      (stackTopEq-root-one (appendDigit d3 rest) stack len))
    (rootStepF-d3-fail-correct rest stack len)

stackNonemptyStepF-nested-d2-fail-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stackNonemptyStepF
    (stateInput
      (appendDigit d2 rest)
      (NS.pushFrame SM.nestedList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    (appendDigit d2 rest)
    (NS.pushFrame SM.nestedList stack)
    len
    zero
stackNonemptyStepF-nested-d2-fail-correct rest stack len =
  trans
    (StatePR.ifEqF-select-false
      StatePR.stateStackTopF
      (suc zero)
      StatePR.rootStepF
      (StatePR.ifEqF
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF)))
      (stateInput
        (appendDigit d2 rest)
        (NS.pushFrame SM.nestedList stack)
        len
        (suc zero)
      ∷ [])
      (stackTopEq-nested-one (appendDigit d2 rest) stack len))
    (trans
      (StatePR.ifEqF-select-true
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF))
        (stateInput
          (appendDigit d2 rest)
          (NS.pushFrame SM.nestedList stack)
          len
          (suc zero)
        ∷ [])
        (stackTopEq-nested-two (appendDigit d2 rest) stack len))
      (nestedStepF-d2-fail-correct rest stack len))

stackNonemptyStepF-nested-d3-fail-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stackNonemptyStepF
    (stateInput
      (appendDigit d3 rest)
      (NS.pushFrame SM.nestedList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    (appendDigit d3 rest)
    (NS.pushFrame SM.nestedList stack)
    len
    zero
stackNonemptyStepF-nested-d3-fail-correct rest stack len =
  trans
    (StatePR.ifEqF-select-false
      StatePR.stateStackTopF
      (suc zero)
      StatePR.rootStepF
      (StatePR.ifEqF
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF)))
      (stateInput
        (appendDigit d3 rest)
        (NS.pushFrame SM.nestedList stack)
        len
        (suc zero)
      ∷ [])
      (stackTopEq-nested-one (appendDigit d3 rest) stack len))
    (trans
      (StatePR.ifEqF-select-true
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF))
        (stateInput
          (appendDigit d3 rest)
          (NS.pushFrame SM.nestedList stack)
          len
          (suc zero)
        ∷ [])
        (stackTopEq-nested-two (appendDigit d3 rest) stack len))
      (nestedStepF-d3-fail-correct rest stack len))

stackNonemptyStepF-code-d2-fail-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stackNonemptyStepF
    (stateInput
      (appendDigit d2 rest)
      (NS.pushFrame SM.codeFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    (appendDigit d2 rest)
    (NS.pushFrame SM.codeFrame stack)
    len
    zero
stackNonemptyStepF-code-d2-fail-correct rest stack len =
  trans
    (StatePR.ifEqF-select-false
      StatePR.stateStackTopF
      (suc zero)
      StatePR.rootStepF
      (StatePR.ifEqF
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF)))
      (stateInput
        (appendDigit d2 rest)
        (NS.pushFrame SM.codeFrame stack)
        len
        (suc zero)
      ∷ [])
      (stackTopEq-code-one (appendDigit d2 rest) stack len))
    (trans
      (StatePR.ifEqF-select-false
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF))
        (stateInput
          (appendDigit d2 rest)
          (NS.pushFrame SM.codeFrame stack)
          len
          (suc zero)
        ∷ [])
        (stackTopEq-code-two (appendDigit d2 rest) stack len))
      (trans
        (StatePR.ifEqF-select-true
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF)
          (stateInput
            (appendDigit d2 rest)
            (NS.pushFrame SM.codeFrame stack)
            len
            (suc zero)
          ∷ [])
          (stackTopEq-code-three (appendDigit d2 rest) stack len))
        (codeStepF-d2-fail-correct rest stack len)))

stackNonemptyStepF-code-d3-fail-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stackNonemptyStepF
    (stateInput
      (appendDigit d3 rest)
      (NS.pushFrame SM.codeFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    (appendDigit d3 rest)
    (NS.pushFrame SM.codeFrame stack)
    len
    zero
stackNonemptyStepF-code-d3-fail-correct rest stack len =
  trans
    (StatePR.ifEqF-select-false
      StatePR.stateStackTopF
      (suc zero)
      StatePR.rootStepF
      (StatePR.ifEqF
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF)))
      (stateInput
        (appendDigit d3 rest)
        (NS.pushFrame SM.codeFrame stack)
        len
        (suc zero)
      ∷ [])
      (stackTopEq-code-one (appendDigit d3 rest) stack len))
    (trans
      (StatePR.ifEqF-select-false
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF))
        (stateInput
          (appendDigit d3 rest)
          (NS.pushFrame SM.codeFrame stack)
          len
          (suc zero)
        ∷ [])
        (stackTopEq-code-two (appendDigit d3 rest) stack len))
      (trans
        (StatePR.ifEqF-select-true
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF)
          (stateInput
            (appendDigit d3 rest)
            (NS.pushFrame SM.codeFrame stack)
            len
            (suc zero)
          ∷ [])
          (stackTopEq-code-three (appendDigit d3 rest) stack len))
        (codeStepF-d3-fail-correct rest stack len)))

stackNonemptyStepF-nat-d0-fail-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stackNonemptyStepF
    (stateInput
      (appendDigit d0 rest)
      (NS.pushFrame SM.natFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    (appendDigit d0 rest)
    (NS.pushFrame SM.natFrame stack)
    len
    zero
stackNonemptyStepF-nat-d0-fail-correct rest stack len =
  trans
    (StatePR.ifEqF-select-false
      StatePR.stateStackTopF
      (suc zero)
      StatePR.rootStepF
      (StatePR.ifEqF
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF)))
      (stateInput
        (appendDigit d0 rest)
        (NS.pushFrame SM.natFrame stack)
        len
        (suc zero)
      ∷ [])
      (stackTopEq-nat-one (appendDigit d0 rest) stack len))
    (trans
      (StatePR.ifEqF-select-false
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF))
        (stateInput
          (appendDigit d0 rest)
          (NS.pushFrame SM.natFrame stack)
          len
          (suc zero)
        ∷ [])
        (stackTopEq-nat-two (appendDigit d0 rest) stack len))
      (trans
        (StatePR.ifEqF-select-false
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF)
          (stateInput
            (appendDigit d0 rest)
            (NS.pushFrame SM.natFrame stack)
            len
            (suc zero)
          ∷ [])
          (stackTopEq-nat-three (appendDigit d0 rest) stack len))
        (trans
          (StatePR.ifEqF-select-true
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF
            (stateInput
              (appendDigit d0 rest)
              (NS.pushFrame SM.natFrame stack)
              len
              (suc zero)
            ∷ [])
            (stackTopEq-nat-four (appendDigit d0 rest) stack len))
          (natStepF-d0-fail-correct rest stack len))))

stackNonemptyStepF-nat-d1-fail-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stackNonemptyStepF
    (stateInput
      (appendDigit d1 rest)
      (NS.pushFrame SM.natFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    (appendDigit d1 rest)
    (NS.pushFrame SM.natFrame stack)
    len
    zero
stackNonemptyStepF-nat-d1-fail-correct rest stack len =
  trans
    (StatePR.ifEqF-select-false
      StatePR.stateStackTopF
      (suc zero)
      StatePR.rootStepF
      (StatePR.ifEqF
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF)))
      (stateInput
        (appendDigit d1 rest)
        (NS.pushFrame SM.natFrame stack)
        len
        (suc zero)
      ∷ [])
      (stackTopEq-nat-one (appendDigit d1 rest) stack len))
    (trans
      (StatePR.ifEqF-select-false
        StatePR.stateStackTopF
        (suc (suc zero))
        StatePR.nestedStepF
        (StatePR.ifEqF
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF))
        (stateInput
          (appendDigit d1 rest)
          (NS.pushFrame SM.natFrame stack)
          len
          (suc zero)
        ∷ [])
        (stackTopEq-nat-two (appendDigit d1 rest) stack len))
      (trans
        (StatePR.ifEqF-select-false
          StatePR.stateStackTopF
          (suc (suc (suc zero)))
          StatePR.codeStepF
          (StatePR.ifEqF
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF)
          (stateInput
            (appendDigit d1 rest)
            (NS.pushFrame SM.natFrame stack)
            len
            (suc zero)
          ∷ [])
          (stackTopEq-nat-three (appendDigit d1 rest) stack len))
        (trans
          (StatePR.ifEqF-select-true
            StatePR.stateStackTopF
            (suc (suc (suc (suc zero))))
            StatePR.natStepF
            StatePR.stateFailF
            (stateInput
              (appendDigit d1 rest)
              (NS.pushFrame SM.natFrame stack)
              len
              (suc zero)
            ∷ [])
            (stackTopEq-nat-four (appendDigit d1 rest) stack len))
          (natStepF-d1-fail-correct rest stack len))))

stateStepF-root-d0-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stateStepF
    (stateInput
      (appendDigit d0 rest)
      (NS.pushFrame SM.rootList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput rest stack len (suc zero)
stateStepF-root-d0-correct rest stack len =
  trans
    (stateStepF-nonempty-select
      (appendDigit d0 rest)
      (NS.pushFrame SM.rootList stack)
      len
      (stackEq-push-zero SM.rootList (appendDigit d0 rest) stack len))
    (stackNonemptyStepF-root-d0-correct rest stack len)

stateStepF-root-d1-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stateStepF
    (stateInput
      (appendDigit d1 rest)
      (NS.pushFrame SM.rootList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    rest
    (NS.pushFrame SM.codeFrame (NS.pushFrame SM.rootList stack))
    (suc len)
    (suc zero)
stateStepF-root-d1-correct rest stack len =
  trans
    (stateStepF-nonempty-select
      (appendDigit d1 rest)
      (NS.pushFrame SM.rootList stack)
      len
      (stackEq-push-zero SM.rootList (appendDigit d1 rest) stack len))
    (stackNonemptyStepF-root-d1-correct rest stack len)

stateStepF-nested-d0-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stateStepF
    (stateInput
      (appendDigit d0 rest)
      (NS.pushFrame SM.nestedList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput rest stack len (suc zero)
stateStepF-nested-d0-correct rest stack len =
  trans
    (stateStepF-nonempty-select
      (appendDigit d0 rest)
      (NS.pushFrame SM.nestedList stack)
      len
      (stackEq-push-zero SM.nestedList (appendDigit d0 rest) stack len))
    (stackNonemptyStepF-nested-d0-correct rest stack len)

stateStepF-nested-d1-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stateStepF
    (stateInput
      (appendDigit d1 rest)
      (NS.pushFrame SM.nestedList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    rest
    (NS.pushFrame SM.codeFrame (NS.pushFrame SM.nestedList stack))
    len
    (suc zero)
stateStepF-nested-d1-correct rest stack len =
  trans
    (stateStepF-nonempty-select
      (appendDigit d1 rest)
      (NS.pushFrame SM.nestedList stack)
      len
      (stackEq-push-zero SM.nestedList (appendDigit d1 rest) stack len))
    (stackNonemptyStepF-nested-d1-correct rest stack len)

stateStepF-code-d0-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stateStepF
    (stateInput
      (appendDigit d0 rest)
      (NS.pushFrame SM.codeFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput rest (NS.pushFrame SM.natFrame stack) len (suc zero)
stateStepF-code-d0-correct rest stack len =
  trans
    (stateStepF-nonempty-select
      (appendDigit d0 rest)
      (NS.pushFrame SM.codeFrame stack)
      len
      (stackEq-push-zero SM.codeFrame (appendDigit d0 rest) stack len))
    (stackNonemptyStepF-code-d0-correct rest stack len)

stateStepF-code-d1-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stateStepF
    (stateInput
      (appendDigit d1 rest)
      (NS.pushFrame SM.codeFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    rest
    (NS.pushFrame SM.natFrame (NS.pushFrame SM.nestedList stack))
    len
    (suc zero)
stateStepF-code-d1-correct rest stack len =
  trans
    (stateStepF-nonempty-select
      (appendDigit d1 rest)
      (NS.pushFrame SM.codeFrame stack)
      len
      (stackEq-push-zero SM.codeFrame (appendDigit d1 rest) stack len))
    (stackNonemptyStepF-code-d1-correct rest stack len)

stateStepF-nat-d2-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stateStepF
    (stateInput
      (appendDigit d2 rest)
      (NS.pushFrame SM.natFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput rest (NS.pushFrame SM.natFrame stack) len (suc zero)
stateStepF-nat-d2-correct rest stack len =
  trans
    (stateStepF-nonempty-select
      (appendDigit d2 rest)
      (NS.pushFrame SM.natFrame stack)
      len
      (stackEq-push-zero SM.natFrame (appendDigit d2 rest) stack len))
    (stackNonemptyStepF-nat-d2-correct rest stack len)

stateStepF-nat-d3-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stateStepF
    (stateInput
      (appendDigit d3 rest)
      (NS.pushFrame SM.natFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput rest stack len (suc zero)
stateStepF-nat-d3-correct rest stack len =
  trans
    (stateStepF-nonempty-select
      (appendDigit d3 rest)
      (NS.pushFrame SM.natFrame stack)
      len
      (stackEq-push-zero SM.natFrame (appendDigit d3 rest) stack len))
    (stackNonemptyStepF-nat-d3-correct rest stack len)

stateStepF-root-d2-fail-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stateStepF
    (stateInput
      (appendDigit d2 rest)
      (NS.pushFrame SM.rootList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    (appendDigit d2 rest)
    (NS.pushFrame SM.rootList stack)
    len
    zero
stateStepF-root-d2-fail-correct rest stack len =
  trans
    (stateStepF-nonempty-select
      (appendDigit d2 rest)
      (NS.pushFrame SM.rootList stack)
      len
      (stackEq-push-zero SM.rootList (appendDigit d2 rest) stack len))
    (stackNonemptyStepF-root-d2-fail-correct rest stack len)

stateStepF-root-d3-fail-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stateStepF
    (stateInput
      (appendDigit d3 rest)
      (NS.pushFrame SM.rootList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    (appendDigit d3 rest)
    (NS.pushFrame SM.rootList stack)
    len
    zero
stateStepF-root-d3-fail-correct rest stack len =
  trans
    (stateStepF-nonempty-select
      (appendDigit d3 rest)
      (NS.pushFrame SM.rootList stack)
      len
      (stackEq-push-zero SM.rootList (appendDigit d3 rest) stack len))
    (stackNonemptyStepF-root-d3-fail-correct rest stack len)

stateStepF-nested-d2-fail-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stateStepF
    (stateInput
      (appendDigit d2 rest)
      (NS.pushFrame SM.nestedList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    (appendDigit d2 rest)
    (NS.pushFrame SM.nestedList stack)
    len
    zero
stateStepF-nested-d2-fail-correct rest stack len =
  trans
    (stateStepF-nonempty-select
      (appendDigit d2 rest)
      (NS.pushFrame SM.nestedList stack)
      len
      (stackEq-push-zero SM.nestedList (appendDigit d2 rest) stack len))
    (stackNonemptyStepF-nested-d2-fail-correct rest stack len)

stateStepF-nested-d3-fail-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stateStepF
    (stateInput
      (appendDigit d3 rest)
      (NS.pushFrame SM.nestedList stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    (appendDigit d3 rest)
    (NS.pushFrame SM.nestedList stack)
    len
    zero
stateStepF-nested-d3-fail-correct rest stack len =
  trans
    (stateStepF-nonempty-select
      (appendDigit d3 rest)
      (NS.pushFrame SM.nestedList stack)
      len
      (stackEq-push-zero SM.nestedList (appendDigit d3 rest) stack len))
    (stackNonemptyStepF-nested-d3-fail-correct rest stack len)

stateStepF-code-d2-fail-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stateStepF
    (stateInput
      (appendDigit d2 rest)
      (NS.pushFrame SM.codeFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    (appendDigit d2 rest)
    (NS.pushFrame SM.codeFrame stack)
    len
    zero
stateStepF-code-d2-fail-correct rest stack len =
  trans
    (stateStepF-nonempty-select
      (appendDigit d2 rest)
      (NS.pushFrame SM.codeFrame stack)
      len
      (stackEq-push-zero SM.codeFrame (appendDigit d2 rest) stack len))
    (stackNonemptyStepF-code-d2-fail-correct rest stack len)

stateStepF-code-d3-fail-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stateStepF
    (stateInput
      (appendDigit d3 rest)
      (NS.pushFrame SM.codeFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    (appendDigit d3 rest)
    (NS.pushFrame SM.codeFrame stack)
    len
    zero
stateStepF-code-d3-fail-correct rest stack len =
  trans
    (stateStepF-nonempty-select
      (appendDigit d3 rest)
      (NS.pushFrame SM.codeFrame stack)
      len
      (stackEq-push-zero SM.codeFrame (appendDigit d3 rest) stack len))
    (stackNonemptyStepF-code-d3-fail-correct rest stack len)

stateStepF-nat-d0-fail-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stateStepF
    (stateInput
      (appendDigit d0 rest)
      (NS.pushFrame SM.natFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    (appendDigit d0 rest)
    (NS.pushFrame SM.natFrame stack)
    len
    zero
stateStepF-nat-d0-fail-correct rest stack len =
  trans
    (stateStepF-nonempty-select
      (appendDigit d0 rest)
      (NS.pushFrame SM.natFrame stack)
      len
      (stackEq-push-zero SM.natFrame (appendDigit d0 rest) stack len))
    (stackNonemptyStepF-nat-d0-fail-correct rest stack len)

stateStepF-nat-d1-fail-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stateStepF
    (stateInput
      (appendDigit d1 rest)
      (NS.pushFrame SM.natFrame stack)
      len
      (suc zero)
    ∷ []) ≡
  stateInput
    (appendDigit d1 rest)
    (NS.pushFrame SM.natFrame stack)
    len
    zero
stateStepF-nat-d1-fail-correct rest stack len =
  trans
    (stateStepF-nonempty-select
      (appendDigit d1 rest)
      (NS.pushFrame SM.natFrame stack)
      len
      (stackEq-push-zero SM.natFrame (appendDigit d1 rest) stack len))
    (stackNonemptyStepF-nat-d1-fail-correct rest stack len)

stateStepF-failed-correct :
  (rest stack len : ℕ) →
  evalPRF StatePR.stateStepF
    (stateInput rest stack len zero ∷ []) ≡
  stateInput rest stack len zero
stateStepF-failed-correct rest stack len =
  StatePR.ifBoolF-select-false
    StatePR.stateOkF
    (StatePR.ifEqF
      StatePR.stateStackF
      zero
      StatePR.stackEmptyStepF
      StatePR.stackNonemptyStepF)
    (projF fzero)
    (stateInput rest stack len zero ∷ [])
    (StatePR.stateOkF-correct-code rest stack len zero)

stateStepF-done-correct :
  (len : ℕ) →
  evalPRF StatePR.stateStepF
    (stateInput zero zero len (suc zero) ∷ []) ≡
  stateInput zero zero len (suc zero)
stateStepF-done-correct len =
  trans
    (StatePR.ifBoolF-select-true
      StatePR.stateOkF
      (StatePR.ifEqF
        StatePR.stateStackF
        zero
        StatePR.stackEmptyStepF
        StatePR.stackNonemptyStepF)
      (projF fzero)
      (stateInput zero zero len (suc zero) ∷ [])
      (StatePR.stateOkF-correct-code zero zero len (suc zero)))
    (trans
      (StatePR.ifEqF-select-true
        StatePR.stateStackF
        zero
        StatePR.stackEmptyStepF
        StatePR.stackNonemptyStepF
        (stateInput zero zero len (suc zero) ∷ [])
        (stackEq-zero-zero zero len (suc zero)))
      (StatePR.ifEqF-select-true
        StatePR.stateRestF
        zero
        (projF fzero)
        StatePR.stateFailF
        (stateInput zero zero len (suc zero) ∷ [])
        (restEq-zero-zero zero len (suc zero))))

stateStepF-empty-nonzero-correct :
  (rest len : ℕ) →
  evalPRF StatePR.stateStepF
    (stateInput (suc rest) zero len (suc zero) ∷ []) ≡
  stateInput (suc rest) zero len zero
stateStepF-empty-nonzero-correct rest len =
  trans
    (StatePR.ifBoolF-select-true
      StatePR.stateOkF
      (StatePR.ifEqF
        StatePR.stateStackF
        zero
        StatePR.stackEmptyStepF
        StatePR.stackNonemptyStepF)
      (projF fzero)
      (stateInput (suc rest) zero len (suc zero) ∷ [])
      (StatePR.stateOkF-correct-code (suc rest) zero len (suc zero)))
    (trans
      (StatePR.ifEqF-select-true
        StatePR.stateStackF
        zero
        StatePR.stackEmptyStepF
        StatePR.stackNonemptyStepF
        (stateInput (suc rest) zero len (suc zero) ∷ [])
        (stackEq-zero-zero (suc rest) len (suc zero)))
      (trans
        (StatePR.ifEqF-select-false
          StatePR.stateRestF
          zero
          (projF fzero)
          StatePR.stateFailF
          (stateInput (suc rest) zero len (suc zero) ∷ [])
          (restEq-suc-zero rest zero len (suc zero)))
        (stateFailF-correct-code (suc rest) zero len (suc zero))))

abstract
  stateStepF-root-d0-opaque :
    (rest stack len : ℕ) →
    evalPRF StatePR.stateStepF
      (stateInput
        (appendDigit d0 rest)
        (NS.pushFrame SM.rootList stack)
        len
        (suc zero)
      ∷ []) ≡
    stateInput rest stack len (suc zero)
  stateStepF-root-d0-opaque = stateStepF-root-d0-correct

  stateStepF-root-d1-opaque :
    (rest stack len : ℕ) →
    evalPRF StatePR.stateStepF
      (stateInput
        (appendDigit d1 rest)
        (NS.pushFrame SM.rootList stack)
        len
        (suc zero)
      ∷ []) ≡
    stateInput
      rest
      (NS.pushFrame SM.codeFrame (NS.pushFrame SM.rootList stack))
      (suc len)
      (suc zero)
  stateStepF-root-d1-opaque = stateStepF-root-d1-correct

  stateStepF-nested-d0-opaque :
    (rest stack len : ℕ) →
    evalPRF StatePR.stateStepF
      (stateInput
        (appendDigit d0 rest)
        (NS.pushFrame SM.nestedList stack)
        len
        (suc zero)
      ∷ []) ≡
    stateInput rest stack len (suc zero)
  stateStepF-nested-d0-opaque = stateStepF-nested-d0-correct

  stateStepF-nested-d1-opaque :
    (rest stack len : ℕ) →
    evalPRF StatePR.stateStepF
      (stateInput
        (appendDigit d1 rest)
        (NS.pushFrame SM.nestedList stack)
        len
        (suc zero)
      ∷ []) ≡
    stateInput
      rest
      (NS.pushFrame SM.codeFrame (NS.pushFrame SM.nestedList stack))
      len
      (suc zero)
  stateStepF-nested-d1-opaque = stateStepF-nested-d1-correct

  stateStepF-code-d0-opaque :
    (rest stack len : ℕ) →
    evalPRF StatePR.stateStepF
      (stateInput
        (appendDigit d0 rest)
        (NS.pushFrame SM.codeFrame stack)
        len
        (suc zero)
      ∷ []) ≡
    stateInput rest (NS.pushFrame SM.natFrame stack) len (suc zero)
  stateStepF-code-d0-opaque = stateStepF-code-d0-correct

  stateStepF-code-d1-opaque :
    (rest stack len : ℕ) →
    evalPRF StatePR.stateStepF
      (stateInput
        (appendDigit d1 rest)
        (NS.pushFrame SM.codeFrame stack)
        len
        (suc zero)
      ∷ []) ≡
    stateInput
      rest
      (NS.pushFrame SM.natFrame (NS.pushFrame SM.nestedList stack))
      len
      (suc zero)
  stateStepF-code-d1-opaque = stateStepF-code-d1-correct

  stateStepF-nat-d2-opaque :
    (rest stack len : ℕ) →
    evalPRF StatePR.stateStepF
      (stateInput
        (appendDigit d2 rest)
        (NS.pushFrame SM.natFrame stack)
        len
        (suc zero)
      ∷ []) ≡
    stateInput rest (NS.pushFrame SM.natFrame stack) len (suc zero)
  stateStepF-nat-d2-opaque = stateStepF-nat-d2-correct

  stateStepF-nat-d3-opaque :
    (rest stack len : ℕ) →
    evalPRF StatePR.stateStepF
      (stateInput
        (appendDigit d3 rest)
        (NS.pushFrame SM.natFrame stack)
        len
        (suc zero)
      ∷ []) ≡
    stateInput rest stack len (suc zero)
  stateStepF-nat-d3-opaque = stateStepF-nat-d3-correct

  stateStepF-root-d2-fail-opaque :
    (rest stack len : ℕ) →
    evalPRF StatePR.stateStepF
      (stateInput
        (appendDigit d2 rest)
        (NS.pushFrame SM.rootList stack)
        len
        (suc zero)
      ∷ []) ≡
    stateInput
      (appendDigit d2 rest)
      (NS.pushFrame SM.rootList stack)
      len
      zero
  stateStepF-root-d2-fail-opaque = stateStepF-root-d2-fail-correct

  stateStepF-root-d3-fail-opaque :
    (rest stack len : ℕ) →
    evalPRF StatePR.stateStepF
      (stateInput
        (appendDigit d3 rest)
        (NS.pushFrame SM.rootList stack)
        len
        (suc zero)
      ∷ []) ≡
    stateInput
      (appendDigit d3 rest)
      (NS.pushFrame SM.rootList stack)
      len
      zero
  stateStepF-root-d3-fail-opaque = stateStepF-root-d3-fail-correct

  stateStepF-nested-d2-fail-opaque :
    (rest stack len : ℕ) →
    evalPRF StatePR.stateStepF
      (stateInput
        (appendDigit d2 rest)
        (NS.pushFrame SM.nestedList stack)
        len
        (suc zero)
      ∷ []) ≡
    stateInput
      (appendDigit d2 rest)
      (NS.pushFrame SM.nestedList stack)
      len
      zero
  stateStepF-nested-d2-fail-opaque = stateStepF-nested-d2-fail-correct

  stateStepF-nested-d3-fail-opaque :
    (rest stack len : ℕ) →
    evalPRF StatePR.stateStepF
      (stateInput
        (appendDigit d3 rest)
        (NS.pushFrame SM.nestedList stack)
        len
        (suc zero)
      ∷ []) ≡
    stateInput
      (appendDigit d3 rest)
      (NS.pushFrame SM.nestedList stack)
      len
      zero
  stateStepF-nested-d3-fail-opaque = stateStepF-nested-d3-fail-correct

  stateStepF-code-d2-fail-opaque :
    (rest stack len : ℕ) →
    evalPRF StatePR.stateStepF
      (stateInput
        (appendDigit d2 rest)
        (NS.pushFrame SM.codeFrame stack)
        len
        (suc zero)
      ∷ []) ≡
    stateInput
      (appendDigit d2 rest)
      (NS.pushFrame SM.codeFrame stack)
      len
      zero
  stateStepF-code-d2-fail-opaque = stateStepF-code-d2-fail-correct

  stateStepF-code-d3-fail-opaque :
    (rest stack len : ℕ) →
    evalPRF StatePR.stateStepF
      (stateInput
        (appendDigit d3 rest)
        (NS.pushFrame SM.codeFrame stack)
        len
        (suc zero)
      ∷ []) ≡
    stateInput
      (appendDigit d3 rest)
      (NS.pushFrame SM.codeFrame stack)
      len
      zero
  stateStepF-code-d3-fail-opaque = stateStepF-code-d3-fail-correct

  stateStepF-nat-d0-fail-opaque :
    (rest stack len : ℕ) →
    evalPRF StatePR.stateStepF
      (stateInput
        (appendDigit d0 rest)
        (NS.pushFrame SM.natFrame stack)
        len
        (suc zero)
      ∷ []) ≡
    stateInput
      (appendDigit d0 rest)
      (NS.pushFrame SM.natFrame stack)
      len
      zero
  stateStepF-nat-d0-fail-opaque = stateStepF-nat-d0-fail-correct

  stateStepF-nat-d1-fail-opaque :
    (rest stack len : ℕ) →
    evalPRF StatePR.stateStepF
      (stateInput
        (appendDigit d1 rest)
        (NS.pushFrame SM.natFrame stack)
        len
        (suc zero)
      ∷ []) ≡
    stateInput
      (appendDigit d1 rest)
      (NS.pushFrame SM.natFrame stack)
      len
      zero
  stateStepF-nat-d1-fail-opaque = stateStepF-nat-d1-fail-correct

  stateStepF-failed-opaque :
    (rest stack len : ℕ) →
    evalPRF StatePR.stateStepF
      (stateInput rest stack len zero ∷ []) ≡
    stateInput rest stack len zero
  stateStepF-failed-opaque = stateStepF-failed-correct

  stateStepF-done-opaque :
    (len : ℕ) →
    evalPRF StatePR.stateStepF
      (stateInput zero zero len (suc zero) ∷ []) ≡
    stateInput zero zero len (suc zero)
  stateStepF-done-opaque = stateStepF-done-correct

  stateStepF-empty-nonzero-opaque :
    (rest len : ℕ) →
    evalPRF StatePR.stateStepF
      (stateInput (suc rest) zero len (suc zero) ∷ []) ≡
    stateInput (suc rest) zero len zero
  stateStepF-empty-nonzero-opaque = stateStepF-empty-nonzero-correct
