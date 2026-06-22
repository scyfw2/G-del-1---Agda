{-# OPTIONS --safe #-}

module Godel.CanonicalCodeListLengthNumericState where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List using (List; []; _∷_)
open import Godel.Core
open import Godel.CanonicalCoding
  using
    ( Code
    ; atom
    ; node
    ; Digit
    ; d0
    ; d1
    ; d2
    ; d3
    ; DigitRest
    ; digitRest
    ; appendDigit
    ; undigit
    ; undigit-appendDigit
    ; +-assoc
    ; +-zeroʳ
    ; +-sucʳ
    )
open import Godel.CanonicalCodeParserTargets using (codeListLength)
open import Godel.PRNatListDigitStream
  using
    ( _++ᵈ_
    ; appendDigitsWithRest
    ; digitsLength
    ; digitsLength-++
    ; natDigits
    )
import Godel.CanonicalCodeListLengthStackMachine as SM

-- Numeric-state mirror for the stack-machine scanner.
--
-- `CanonicalCodeListLengthStackMachine` proves the explicit digit-stream
-- induction.  This module starts the bridge to `CanonicalCodeListLengthStatePR`:
-- it encodes the remaining digit stream and control stack as natural numbers,
-- defines the meta-level numeric step, and proves the valid branch equations.
-- These lemmas are the intended semantic target for the PRF `stateStepF`.

append5 : ℕ → ℕ → ℕ
append5 zero zero = zero
append5 (suc zero) zero = suc zero
append5 (suc (suc zero)) zero = suc (suc zero)
append5 (suc (suc (suc zero))) zero = suc (suc (suc zero))
append5 (suc (suc (suc (suc zero)))) zero =
  suc (suc (suc (suc zero)))
append5 (suc (suc (suc (suc (suc c))))) zero = zero
append5 c (suc rest) =
  suc (suc (suc (suc (suc (append5 c rest)))))

mod5Nat : ℕ → ℕ
mod5Nat zero = zero
mod5Nat (suc zero) = suc zero
mod5Nat (suc (suc zero)) = suc (suc zero)
mod5Nat (suc (suc (suc zero))) = suc (suc (suc zero))
mod5Nat (suc (suc (suc (suc zero)))) =
  suc (suc (suc (suc zero)))
mod5Nat (suc (suc (suc (suc (suc n))))) = mod5Nat n

div5Nat : ℕ → ℕ
div5Nat zero = zero
div5Nat (suc zero) = zero
div5Nat (suc (suc zero)) = zero
div5Nat (suc (suc (suc zero))) = zero
div5Nat (suc (suc (suc (suc zero)))) = zero
div5Nat (suc (suc (suc (suc (suc n))))) = suc (div5Nat n)

frameCell : SM.Frame → ℕ
frameCell SM.rootList = suc zero
frameCell SM.nestedList = suc (suc zero)
frameCell SM.codeFrame = suc (suc (suc zero))
frameCell SM.natFrame = suc (suc (suc (suc zero)))

pushFrame : SM.Frame → ℕ → ℕ
pushFrame f stack = append5 (frameCell f) stack

encodeStack : List SM.Frame → ℕ
encodeStack [] = zero
encodeStack (f ∷ fs) = pushFrame f (encodeStack fs)

stackTop : ℕ → ℕ
stackTop = mod5Nat

stackTail : ℕ → ℕ
stackTail = div5Nat

mod5-append5-1 :
  (rest : ℕ) → mod5Nat (append5 (suc zero) rest) ≡ suc zero
mod5-append5-1 zero = refl
mod5-append5-1 (suc rest) = mod5-append5-1 rest

mod5-append5-2 :
  (rest : ℕ) →
  mod5Nat (append5 (suc (suc zero)) rest) ≡ suc (suc zero)
mod5-append5-2 zero = refl
mod5-append5-2 (suc rest) = mod5-append5-2 rest

mod5-append5-3 :
  (rest : ℕ) →
  mod5Nat (append5 (suc (suc (suc zero))) rest) ≡
  suc (suc (suc zero))
mod5-append5-3 zero = refl
mod5-append5-3 (suc rest) = mod5-append5-3 rest

mod5-append5-4 :
  (rest : ℕ) →
  mod5Nat (append5 (suc (suc (suc (suc zero)))) rest) ≡
  suc (suc (suc (suc zero)))
mod5-append5-4 zero = refl
mod5-append5-4 (suc rest) = mod5-append5-4 rest

div5-append5-1 :
  (rest : ℕ) → div5Nat (append5 (suc zero) rest) ≡ rest
div5-append5-1 zero = refl
div5-append5-1 (suc rest)
  rewrite div5-append5-1 rest =
  refl

div5-append5-2 :
  (rest : ℕ) → div5Nat (append5 (suc (suc zero)) rest) ≡ rest
div5-append5-2 zero = refl
div5-append5-2 (suc rest)
  rewrite div5-append5-2 rest =
  refl

div5-append5-3 :
  (rest : ℕ) →
  div5Nat (append5 (suc (suc (suc zero))) rest) ≡ rest
div5-append5-3 zero = refl
div5-append5-3 (suc rest)
  rewrite div5-append5-3 rest =
  refl

div5-append5-4 :
  (rest : ℕ) →
  div5Nat (append5 (suc (suc (suc (suc zero)))) rest) ≡ rest
div5-append5-4 zero = refl
div5-append5-4 (suc rest)
  rewrite div5-append5-4 rest =
  refl

stackTop-push :
  (f : SM.Frame) → (stack : ℕ) →
  stackTop (pushFrame f stack) ≡ frameCell f
stackTop-push SM.rootList stack = mod5-append5-1 stack
stackTop-push SM.nestedList stack = mod5-append5-2 stack
stackTop-push SM.codeFrame stack = mod5-append5-3 stack
stackTop-push SM.natFrame stack = mod5-append5-4 stack

stackTail-push :
  (f : SM.Frame) → (stack : ℕ) →
  stackTail (pushFrame f stack) ≡ stack
stackTail-push SM.rootList stack = div5-append5-1 stack
stackTail-push SM.nestedList stack = div5-append5-2 stack
stackTail-push SM.codeFrame stack = div5-append5-3 stack
stackTail-push SM.natFrame stack = div5-append5-4 stack

record NumState : Set where
  constructor numState
  field
    rest  : ℕ
    stack : ℕ
    len   : ℕ
    ok    : Bool

open NumState

encodeMachineState : List Digit → SM.MachineState → NumState
encodeMachineState ds st =
  numState
    (appendDigitsWithRest ds zero)
    (encodeStack (SM.MachineState.stack st))
    (SM.MachineState.len st)
    (SM.MachineState.ok st)

failNum : NumState → NumState
failNum st = numState (rest st) (stack st) (len st) false

stepNum : NumState → NumState
stepNum (numState rest stack len false) =
  numState rest stack len false
stepNum (numState rest stack len true) with stackTop stack | undigit rest
... | zero | digitRest d input-rest =
  numState rest stack len false
... | suc zero | digitRest d0 input-rest =
  numState input-rest (stackTail stack) len true
... | suc zero | digitRest d1 input-rest =
  numState
    input-rest
    (pushFrame SM.codeFrame (pushFrame SM.rootList (stackTail stack)))
    (suc len)
    true
... | suc zero | digitRest d2 input-rest =
  numState rest stack len false
... | suc zero | digitRest d3 input-rest =
  numState rest stack len false
... | suc (suc zero) | digitRest d0 input-rest =
  numState input-rest (stackTail stack) len true
... | suc (suc zero) | digitRest d1 input-rest =
  numState
    input-rest
    (pushFrame SM.codeFrame (pushFrame SM.nestedList (stackTail stack)))
    len
    true
... | suc (suc zero) | digitRest d2 input-rest =
  numState rest stack len false
... | suc (suc zero) | digitRest d3 input-rest =
  numState rest stack len false
... | suc (suc (suc zero)) | digitRest d0 input-rest =
  numState input-rest (pushFrame SM.natFrame (stackTail stack)) len true
... | suc (suc (suc zero)) | digitRest d1 input-rest =
  numState
    input-rest
    (pushFrame SM.natFrame (pushFrame SM.nestedList (stackTail stack)))
    len
    true
... | suc (suc (suc zero)) | digitRest d2 input-rest =
  numState rest stack len false
... | suc (suc (suc zero)) | digitRest d3 input-rest =
  numState rest stack len false
... | suc (suc (suc (suc zero))) | digitRest d0 input-rest =
  numState rest stack len false
... | suc (suc (suc (suc zero))) | digitRest d1 input-rest =
  numState rest stack len false
... | suc (suc (suc (suc zero))) | digitRest d2 input-rest =
  numState input-rest stack len true
... | suc (suc (suc (suc zero))) | digitRest d3 input-rest =
  numState input-rest (stackTail stack) len true
... | suc (suc (suc (suc (suc extra)))) | digitRest d input-rest =
  numState rest stack len false

-- Stable semantic target for the PRF-level `stateStepF`.
--
-- `stepNum` is useful for exact prefix-length runs.  The concrete scanner PRF
-- runs for a numeric fuel that can be larger than the digit-prefix length, so
-- the completed state must be stable instead of failing on an empty stack.
stepNumStable : NumState → NumState
stepNumStable (numState rest stack len false) =
  numState rest stack len false
stepNumStable (numState zero zero len true) =
  numState zero zero len true
stepNumStable (numState (suc rest) zero len true) =
  numState (suc rest) zero len false
stepNumStable (numState rest (suc stack) len true) =
  stepNum (numState rest (suc stack) len true)

runNumStableFuel : ℕ → NumState → NumState
runNumStableFuel zero st = st
runNumStableFuel (suc fuel) st =
  runNumStableFuel fuel (stepNumStable st)

runNumStableFuel-done :
  (fuel len : ℕ) →
  runNumStableFuel fuel (numState zero zero len true) ≡
  numState zero zero len true
runNumStableFuel-done zero len = refl
runNumStableFuel-done (suc fuel) len =
  runNumStableFuel-done fuel len

stepNumStable-failed :
  (rest stack len : ℕ) →
  stepNumStable (numState rest stack len false) ≡
  numState rest stack len false
stepNumStable-failed rest stack len = refl

stepNumStable-done :
  (len : ℕ) →
  stepNumStable (numState zero zero len true) ≡
  numState zero zero len true
stepNumStable-done len = refl

stepNumStable-empty-nonzero :
  (rest len : ℕ) →
  stepNumStable (numState (suc rest) zero len true) ≡
  numState (suc rest) zero len false
stepNumStable-empty-nonzero rest len = refl

undigit-appendDigitsWithRest :
  (d : Digit) → (ds : List Digit) →
  undigit (appendDigitsWithRest (d ∷ ds) zero) ≡
  digitRest d (appendDigitsWithRest ds zero)
undigit-appendDigitsWithRest d ds =
  undigit-appendDigit d (appendDigitsWithRest ds zero)

stepNum-root-d0 :
  (ds : List Digit) → (stack : List SM.Frame) → (len : ℕ) →
  stepNum
    (encodeMachineState
      (d0 ∷ ds)
      (SM.state (SM.rootList ∷ stack) len true))
  ≡
  encodeMachineState ds (SM.state stack len true)
stepNum-root-d0 ds stack len
  rewrite stackTop-push SM.rootList (encodeStack stack)
        | undigit-appendDigitsWithRest d0 ds
        | stackTail-push SM.rootList (encodeStack stack) =
  refl

stepNum-root-d1 :
  (ds : List Digit) → (stack : List SM.Frame) → (len : ℕ) →
  stepNum
    (encodeMachineState
      (d1 ∷ ds)
      (SM.state (SM.rootList ∷ stack) len true))
  ≡
  encodeMachineState
    ds
    (SM.state (SM.codeFrame ∷ SM.rootList ∷ stack) (suc len) true)
stepNum-root-d1 ds stack len
  rewrite stackTop-push SM.rootList (encodeStack stack)
        | undigit-appendDigitsWithRest d1 ds
        | stackTail-push SM.rootList (encodeStack stack) =
  refl

stepNum-nested-d0 :
  (ds : List Digit) → (stack : List SM.Frame) → (len : ℕ) →
  stepNum
    (encodeMachineState
      (d0 ∷ ds)
      (SM.state (SM.nestedList ∷ stack) len true))
  ≡
  encodeMachineState ds (SM.state stack len true)
stepNum-nested-d0 ds stack len
  rewrite stackTop-push SM.nestedList (encodeStack stack)
        | undigit-appendDigitsWithRest d0 ds
        | stackTail-push SM.nestedList (encodeStack stack) =
  refl

stepNum-nested-d1 :
  (ds : List Digit) → (stack : List SM.Frame) → (len : ℕ) →
  stepNum
    (encodeMachineState
      (d1 ∷ ds)
      (SM.state (SM.nestedList ∷ stack) len true))
  ≡
  encodeMachineState
    ds
    (SM.state (SM.codeFrame ∷ SM.nestedList ∷ stack) len true)
stepNum-nested-d1 ds stack len
  rewrite stackTop-push SM.nestedList (encodeStack stack)
        | undigit-appendDigitsWithRest d1 ds
        | stackTail-push SM.nestedList (encodeStack stack) =
  refl

stepNum-code-d0 :
  (ds : List Digit) → (stack : List SM.Frame) → (len : ℕ) →
  stepNum
    (encodeMachineState
      (d0 ∷ ds)
      (SM.state (SM.codeFrame ∷ stack) len true))
  ≡
  encodeMachineState ds (SM.state (SM.natFrame ∷ stack) len true)
stepNum-code-d0 ds stack len
  rewrite stackTop-push SM.codeFrame (encodeStack stack)
        | undigit-appendDigitsWithRest d0 ds
        | stackTail-push SM.codeFrame (encodeStack stack) =
  refl

stepNum-code-d1 :
  (ds : List Digit) → (stack : List SM.Frame) → (len : ℕ) →
  stepNum
    (encodeMachineState
      (d1 ∷ ds)
      (SM.state (SM.codeFrame ∷ stack) len true))
  ≡
  encodeMachineState
    ds
    (SM.state (SM.natFrame ∷ SM.nestedList ∷ stack) len true)
stepNum-code-d1 ds stack len
  rewrite stackTop-push SM.codeFrame (encodeStack stack)
        | undigit-appendDigitsWithRest d1 ds
        | stackTail-push SM.codeFrame (encodeStack stack) =
  refl

stepNum-nat-d2 :
  (ds : List Digit) → (stack : List SM.Frame) → (len : ℕ) →
  stepNum
    (encodeMachineState
      (d2 ∷ ds)
      (SM.state (SM.natFrame ∷ stack) len true))
  ≡
  encodeMachineState ds (SM.state (SM.natFrame ∷ stack) len true)
stepNum-nat-d2 ds stack len
  rewrite stackTop-push SM.natFrame (encodeStack stack)
        | undigit-appendDigitsWithRest d2 ds =
  refl

stepNum-nat-d3 :
  (ds : List Digit) → (stack : List SM.Frame) → (len : ℕ) →
  stepNum
    (encodeMachineState
      (d3 ∷ ds)
      (SM.state (SM.natFrame ∷ stack) len true))
  ≡
  encodeMachineState ds (SM.state stack len true)
stepNum-nat-d3 ds stack len
  rewrite stackTop-push SM.natFrame (encodeStack stack)
        | undigit-appendDigitsWithRest d3 ds
        | stackTail-push SM.natFrame (encodeStack stack) =
  refl

runNumFuel : ℕ → NumState → NumState
runNumFuel zero st = st
runNumFuel (suc fuel) st = runNumFuel fuel (stepNum st)

runNumFuel-add :
  (a b : ℕ) → (st : NumState) →
  runNumFuel (a + b) st ≡ runNumFuel b (runNumFuel a st)
runNumFuel-add zero b st = refl
runNumFuel-add (suc a) b st =
  runNumFuel-add a b (stepNum st)

++ᵈ-identityʳ :
  (xs : List Digit) → xs ++ᵈ [] ≡ xs
++ᵈ-identityʳ [] = refl
++ᵈ-identityʳ (x ∷ xs) =
  cong (λ ys → x ∷ ys) (++ᵈ-identityʳ xs)

digitsLength-++-zeroʳ :
  (xs : List Digit) →
  digitsLength (xs ++ᵈ []) ≡ digitsLength xs
digitsLength-++-zeroʳ xs
  rewrite digitsLength-++ xs []
        | +-zeroʳ (digitsLength xs) =
  refl

mutual
  codeDigitsWithRest-length :
    (c : Code) → (suffix : List Digit) →
    digitsLength (SM.codeDigitsWithRest c suffix) ≡
    digitsLength (SM.codeDigitsWithRest c []) + digitsLength suffix
  codeDigitsWithRest-length (atom n) suffix
    rewrite digitsLength-++ (natDigits n) suffix
          | digitsLength-++-zeroʳ (natDigits n) =
    refl
  codeDigitsWithRest-length (node tag children) suffix
    rewrite digitsLength-++ (natDigits tag)
              (SM.codeListDigitsWithRest children suffix)
          | codeListDigitsWithRest-length children suffix
          | digitsLength-++ (natDigits tag)
              (SM.codeListDigitsWithRest children [])
          | +-assoc
              (digitsLength (natDigits tag))
              (digitsLength (SM.codeListDigitsWithRest children []))
              (digitsLength suffix) =
    refl

  codeListDigitsWithRest-length :
    (codes : List Code) → (suffix : List Digit) →
    digitsLength (SM.codeListDigitsWithRest codes suffix) ≡
    digitsLength (SM.codeListDigitsWithRest codes []) + digitsLength suffix
  codeListDigitsWithRest-length [] suffix = refl
  codeListDigitsWithRest-length (head ∷ tail) suffix
    rewrite codeDigitsWithRest-length
              head
              (SM.codeListDigitsWithRest tail suffix)
          | codeListDigitsWithRest-length tail suffix
          | codeDigitsWithRest-length
              head
              (SM.codeListDigitsWithRest tail [])
          | +-assoc
              (digitsLength (SM.codeDigitsWithRest head []))
              (digitsLength (SM.codeListDigitsWithRest tail []))
              (digitsLength suffix) =
    refl

runNum-nat-prefix-complete :
  (n : ℕ) → (suffix : List Digit) →
  (stack : List SM.Frame) → (len : ℕ) →
  runNumFuel
    (digitsLength (natDigits n))
    (encodeMachineState
      (natDigits n ++ᵈ suffix)
      (SM.state (SM.natFrame ∷ stack) len true))
  ≡
  encodeMachineState suffix (SM.state stack len true)
runNum-nat-prefix-complete zero suffix stack len
  rewrite stepNum-nat-d3 suffix stack len =
  refl
runNum-nat-prefix-complete (suc n) suffix stack len
  rewrite stepNum-nat-d2 (natDigits n ++ᵈ suffix) stack len =
  runNum-nat-prefix-complete n suffix stack len

mutual
  runNum-code-prefix-complete :
    (c : Code) → (suffix : List Digit) →
    (stack : List SM.Frame) → (len : ℕ) →
    runNumFuel
      (digitsLength (SM.codeDigitsWithRest c []))
      (encodeMachineState
        (SM.codeDigitsWithRest c suffix)
        (SM.state (SM.codeFrame ∷ stack) len true))
    ≡
    encodeMachineState suffix (SM.state stack len true)
  runNum-code-prefix-complete (atom n) suffix stack len
    rewrite stepNum-code-d0 (natDigits n ++ᵈ suffix) stack len
          | digitsLength-++-zeroʳ (natDigits n) =
    runNum-nat-prefix-complete n suffix stack len
  runNum-code-prefix-complete (node tag children) suffix stack len
    rewrite stepNum-code-d1
              (natDigits tag ++ᵈ
                SM.codeListDigitsWithRest children suffix)
              stack
              len
          | digitsLength-++ (natDigits tag)
              (SM.codeListDigitsWithRest children [])
          | runNumFuel-add
              (digitsLength (natDigits tag))
              (digitsLength (SM.codeListDigitsWithRest children []))
              (encodeMachineState
                (natDigits tag ++ᵈ
                  SM.codeListDigitsWithRest children suffix)
                (SM.state
                  (SM.natFrame ∷ SM.nestedList ∷ stack)
                  len
                  true))
          | runNum-nat-prefix-complete
              tag
              (SM.codeListDigitsWithRest children suffix)
              (SM.nestedList ∷ stack)
              len =
    runNum-nestedList-prefix-complete children suffix stack len

  runNum-rootList-prefix-complete :
    (codes : List Code) → (suffix : List Digit) →
    (stack : List SM.Frame) → (len : ℕ) →
    runNumFuel
      (digitsLength (SM.codeListDigitsWithRest codes []))
      (encodeMachineState
        (SM.codeListDigitsWithRest codes suffix)
        (SM.state (SM.rootList ∷ stack) len true))
    ≡
    encodeMachineState suffix
      (SM.state stack (len + codeListLength codes) true)
  runNum-rootList-prefix-complete [] suffix stack len
    rewrite stepNum-root-d0 suffix stack len
          | +-zeroʳ len =
    refl
  runNum-rootList-prefix-complete (head ∷ tail) suffix stack len
    rewrite stepNum-root-d1
              (SM.codeDigitsWithRest
                head
                (SM.codeListDigitsWithRest tail suffix))
              stack
              len
          | codeDigitsWithRest-length
              head
              (SM.codeListDigitsWithRest tail [])
          | runNumFuel-add
              (digitsLength (SM.codeDigitsWithRest head []))
              (digitsLength (SM.codeListDigitsWithRest tail []))
              (encodeMachineState
                (SM.codeDigitsWithRest
                  head
                  (SM.codeListDigitsWithRest tail suffix))
                (SM.state (SM.codeFrame ∷ SM.rootList ∷ stack) (suc len) true))
          | runNum-code-prefix-complete
              head
              (SM.codeListDigitsWithRest tail suffix)
              (SM.rootList ∷ stack)
              (suc len)
          | runNum-rootList-prefix-complete tail suffix stack (suc len)
          | +-sucʳ len (codeListLength tail) =
    refl

  runNum-nestedList-prefix-complete :
    (codes : List Code) → (suffix : List Digit) →
    (stack : List SM.Frame) → (len : ℕ) →
    runNumFuel
      (digitsLength (SM.codeListDigitsWithRest codes []))
      (encodeMachineState
        (SM.codeListDigitsWithRest codes suffix)
        (SM.state (SM.nestedList ∷ stack) len true))
    ≡
    encodeMachineState suffix (SM.state stack len true)
  runNum-nestedList-prefix-complete [] suffix stack len
    rewrite stepNum-nested-d0 suffix stack len =
    refl
  runNum-nestedList-prefix-complete (head ∷ tail) suffix stack len
    rewrite stepNum-nested-d1
              (SM.codeDigitsWithRest
                head
                (SM.codeListDigitsWithRest tail suffix))
              stack
              len
          | codeDigitsWithRest-length
              head
              (SM.codeListDigitsWithRest tail [])
          | runNumFuel-add
              (digitsLength (SM.codeDigitsWithRest head []))
              (digitsLength (SM.codeListDigitsWithRest tail []))
              (encodeMachineState
                (SM.codeDigitsWithRest
                  head
                  (SM.codeListDigitsWithRest tail suffix))
                (SM.state (SM.codeFrame ∷ SM.nestedList ∷ stack) len true))
          | runNum-code-prefix-complete
              head
              (SM.codeListDigitsWithRest tail suffix)
              (SM.nestedList ∷ stack)
              len =
    runNum-nestedList-prefix-complete tail suffix stack len

runNum-codeList-closed-complete :
  (codes : List Code) →
  runNumFuel
    (digitsLength (SM.codeListDigitsWithRest codes []))
    (encodeMachineState
      (SM.codeListDigitsWithRest codes [])
      (SM.state (SM.rootList ∷ []) zero true))
  ≡
  encodeMachineState [] (SM.state [] (codeListLength codes) true)
runNum-codeList-closed-complete codes =
  runNum-rootList-prefix-complete codes [] [] zero
