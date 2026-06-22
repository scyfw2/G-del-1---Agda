{-# OPTIONS --safe #-}

module Godel.CanonicalCodeListLengthStackMachine where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Godel.Core
open import Godel.CanonicalCoding
  using (Code; atom; node; Digit; d0; d1; d2; d3; +-zeroʳ; +-sucʳ)
open import Godel.CanonicalCodeParserTargets using (codeListLength)
open import Godel.PRNatListDigitStream
  using (_++ᵈ_; natDigits)

-- A meta-level mirror of the encoded-stack scanner route.
--
-- This module is the Agda counterpart of
-- LeanShadow.CodeListLengthStackMachineMini.  It proves the canonical
-- completeness induction for a stack machine over explicit digit streams.
-- The PRF-side module `CanonicalCodeListLengthStatePR` uses numeric base-4
-- input and an encoded stack; its remaining evaluator proof should follow the
-- same induction shape.

codeDigitsWithRest : Code → List Digit → List Digit
codeListDigitsWithRest : List Code → List Digit → List Digit

codeDigitsWithRest (atom n) rest =
  d0 ∷ (natDigits n ++ᵈ rest)
codeDigitsWithRest (node tag children) rest =
  d1 ∷ (natDigits tag ++ᵈ codeListDigitsWithRest children rest)

codeListDigitsWithRest [] rest = d0 ∷ rest
codeListDigitsWithRest (head ∷ tail) rest =
  d1 ∷ codeDigitsWithRest head (codeListDigitsWithRest tail rest)

data Frame : Set where
  rootList nestedList codeFrame natFrame : Frame

record MachineState : Set where
  constructor state
  field
    stack : List Frame
    len   : ℕ
    ok    : Bool

open MachineState

startState : MachineState
startState = state (rootList ∷ []) zero true

failState : MachineState → MachineState
failState st = state (stack st) (len st) false

stepState : MachineState → Digit → MachineState
stepState (state stack len false) d = state stack len false
stepState (state [] len true) d = state [] len false
stepState (state (rootList ∷ stack) len true) d0 =
  state stack len true
stepState (state (rootList ∷ stack) len true) d1 =
  state (codeFrame ∷ rootList ∷ stack) (suc len) true
stepState (state (rootList ∷ stack) len true) d2 =
  state (rootList ∷ stack) len false
stepState (state (rootList ∷ stack) len true) d3 =
  state (rootList ∷ stack) len false
stepState (state (nestedList ∷ stack) len true) d0 =
  state stack len true
stepState (state (nestedList ∷ stack) len true) d1 =
  state (codeFrame ∷ nestedList ∷ stack) len true
stepState (state (nestedList ∷ stack) len true) d2 =
  state (nestedList ∷ stack) len false
stepState (state (nestedList ∷ stack) len true) d3 =
  state (nestedList ∷ stack) len false
stepState (state (codeFrame ∷ stack) len true) d0 =
  state (natFrame ∷ stack) len true
stepState (state (codeFrame ∷ stack) len true) d1 =
  state (natFrame ∷ nestedList ∷ stack) len true
stepState (state (codeFrame ∷ stack) len true) d2 =
  state (codeFrame ∷ stack) len false
stepState (state (codeFrame ∷ stack) len true) d3 =
  state (codeFrame ∷ stack) len false
stepState (state (natFrame ∷ stack) len true) d0 =
  state (natFrame ∷ stack) len false
stepState (state (natFrame ∷ stack) len true) d1 =
  state (natFrame ∷ stack) len false
stepState (state (natFrame ∷ stack) len true) d2 =
  state (natFrame ∷ stack) len true
stepState (state (natFrame ∷ stack) len true) d3 =
  state stack len true

runState : List Digit → MachineState → MachineState
runState [] st = st
runState (d ∷ ds) st = runState ds (stepState st d)

acceptState : MachineState → Maybe ℕ
acceptState (state [] len true) = just len
acceptState (state [] len false) = nothing
acceptState (state (f ∷ fs) len ok) = nothing

parseCodeListLengthStackMachine : List Digit → Maybe ℕ
parseCodeListLengthStackMachine input =
  acceptState (runState input startState)

runState-natDigits-complete :
  (n : ℕ) → (suffix : List Digit) →
  (stack : List Frame) → (len : ℕ) →
  runState
    (natDigits n ++ᵈ suffix)
    (state (natFrame ∷ stack) len true)
  ≡
  runState suffix (state stack len true)
runState-natDigits-complete zero suffix stack len = refl
runState-natDigits-complete (suc n) suffix stack len =
  runState-natDigits-complete n suffix stack len

mutual
  runState-code-complete :
    (c : Code) → (suffix : List Digit) →
    (stack : List Frame) → (len : ℕ) →
    runState
      (codeDigitsWithRest c suffix)
      (state (codeFrame ∷ stack) len true)
    ≡
    runState suffix (state stack len true)
  runState-code-complete (atom n) suffix stack len =
    runState-natDigits-complete n suffix stack len
  runState-code-complete (node tag children) suffix stack len
    rewrite
      runState-natDigits-complete
        tag
        (codeListDigitsWithRest children suffix)
        (nestedList ∷ stack)
        len =
    runState-nestedList-complete children suffix stack len

  runState-rootList-complete :
    (codes : List Code) → (suffix : List Digit) →
    (stack : List Frame) → (len : ℕ) →
    runState
      (codeListDigitsWithRest codes suffix)
      (state (rootList ∷ stack) len true)
    ≡
    runState suffix
      (state stack (len + codeListLength codes) true)
  runState-rootList-complete [] suffix stack len
    rewrite +-zeroʳ len =
    refl
  runState-rootList-complete (head ∷ tail) suffix stack len
    rewrite
      runState-code-complete
        head
        (codeListDigitsWithRest tail suffix)
        (rootList ∷ stack)
        (suc len)
      | runState-rootList-complete tail suffix stack (suc len)
      | +-sucʳ len (codeListLength tail) =
    refl

  runState-nestedList-complete :
    (codes : List Code) → (suffix : List Digit) →
    (stack : List Frame) → (len : ℕ) →
    runState
      (codeListDigitsWithRest codes suffix)
      (state (nestedList ∷ stack) len true)
    ≡
    runState suffix (state stack len true)
  runState-nestedList-complete [] suffix stack len = refl
  runState-nestedList-complete (head ∷ tail) suffix stack len
    rewrite
      runState-code-complete
        head
        (codeListDigitsWithRest tail suffix)
        (nestedList ∷ stack)
        len =
    runState-nestedList-complete tail suffix stack len

parseCodeListLengthStackMachine-complete :
  (codes : List Code) →
  parseCodeListLengthStackMachine
    (codeListDigitsWithRest codes [])
  ≡
  just (codeListLength codes)
parseCodeListLengthStackMachine-complete codes
  rewrite runState-rootList-complete codes [] [] zero =
  refl
