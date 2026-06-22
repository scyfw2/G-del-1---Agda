import LeanShadow.CodeListLengthScannerMini
import Init.Omega

namespace LeanShadow.CodeListLengthStackMachineMini

open LeanShadow.CodeListLengthMini
open LeanShadow.CodeListLengthMini.Digit
open LeanShadow.CodeListLengthScannerMini

/-!
An encoded-stack route for the code-list-length scanner.

`CodeListLengthScannerMini` already proves the important semantic theorem:
the scanner checker agrees with the canonical parser/checker.  This module
isolates the lower-level state-machine shape that should be copied back to
Agda when building the actual minimal-basis PRF:

* finite control stack frames;
* one transition per input digit/fuel tick;
* base-5 encoded stack push/top/tail operations.

This file intentionally does not claim the final Agda theorem
`evalPRF lengthScannerF = codeListLengthScannerCheck`.  It provides the state
encoding and operational skeleton needed for that theorem.
-/

inductive Frame where
  | rootList
  | nestedList
  | code
  | nat
deriving DecidableEq, Repr

open Frame

structure MachineState where
  stack : List Frame
  len : Nat
  ok : Bool
deriving DecidableEq, Repr

def startState : MachineState :=
  { stack := [rootList], len := 0, ok := true }

def stepState (st : MachineState) (d : Digit) : MachineState :=
  if st.ok = false then st
  else
    match st.stack, d with
    | [], _ =>
        { st with ok := false }
    | rootList :: stack, d0 =>
        { st with stack := stack }
    | rootList :: stack, d1 =>
        { stack := code :: rootList :: stack, len := st.len + 1, ok := true }
    | rootList :: _, _ =>
        { st with ok := false }
    | nestedList :: stack, d0 =>
        { st with stack := stack }
    | nestedList :: stack, d1 =>
        { st with stack := code :: nestedList :: stack }
    | nestedList :: _, _ =>
        { st with ok := false }
    | code :: stack, d0 =>
        { st with stack := nat :: stack }
    | code :: stack, d1 =>
        { st with stack := nat :: nestedList :: stack }
    | code :: _, _ =>
        { st with ok := false }
    | nat :: stack, d2 =>
        { st with stack := nat :: stack }
    | nat :: stack, d3 =>
        { st with stack := stack }
    | nat :: _, _ =>
        { st with ok := false }

def runState : List Digit -> MachineState -> MachineState
  | [], st => st
  | d :: ds, st => runState ds (stepState st d)

def parseCodeListLengthStackMachine (input : List Digit) : Option Nat :=
  let final := runState input startState
  if final.ok && final.stack.isEmpty then
    some final.len
  else
    none

def codeListLengthStackMachineCheck (input : List Digit) (len : Nat) : Nat :=
  match parseCodeListLengthStackMachine input with
  | some parsedLen => if len = parsedLen then 1 else 0
  | none => 0

example : parseCodeListLengthStackMachine [d0] = some 0 := by
  rfl

example : parseCodeListLengthStackMachine [d1, d0, d3, d0] = some 1 := by
  rfl

example : parseCodeListLengthStackMachine [d1, d2, d2, d3, d0] = none := by
  rfl

theorem runState_append
    (pref suffix : List Digit) (st : MachineState) :
    runState (pref ++ suffix) st = runState suffix (runState pref st) := by
  induction pref generalizing st with
  | nil => rfl
  | cons d pref ih =>
      simp [runState, ih]

theorem runState_nat_complete
    (n : Nat) (suffix : List Digit) (stack : List Frame) (len : Nat) :
    runState
      (encodeNatWithRest n suffix)
      { stack := nat :: stack, len := len, ok := true } =
    runState suffix { stack := stack, len := len, ok := true } := by
  induction n generalizing suffix stack len with
  | zero => rfl
  | succ n ih =>
      change
        runState
          (encodeNatWithRest n suffix)
          (stepState { stack := nat :: stack, len := len, ok := true } d2) =
        runState suffix { stack := stack, len := len, ok := true }
      simpa [stepState] using ih suffix stack len

mutual
  theorem runState_code_complete
      (c : Code) (suffix : List Digit) (stack : List Frame) (len : Nat) :
      runState
        (encodeCodeWithRest c suffix)
        { stack := code :: stack, len := len, ok := true } =
      runState suffix { stack := stack, len := len, ok := true } := by
    cases c with
    | atom n =>
        simp [encodeCodeWithRest, runState, stepState]
        exact runState_nat_complete n suffix stack len
    | node tag children =>
        simp [encodeCodeWithRest, runState, stepState]
        rw [runState_nat_complete tag (encodeCodeListWithRest children suffix)
              (nestedList :: stack) len]
        exact runState_nestedList_complete children suffix stack len

  theorem runState_rootList_complete
      (codes : List Code) (suffix : List Digit) (stack : List Frame) (len : Nat) :
      runState
        (encodeCodeListWithRest codes suffix)
        { stack := rootList :: stack, len := len, ok := true } =
      runState suffix
        { stack := stack, len := len + codes.length, ok := true } := by
    cases codes with
    | nil =>
        simp [encodeCodeListWithRest, runState, stepState]
    | cons head tail =>
        simp [encodeCodeListWithRest, runState, stepState]
        rw [runState_code_complete head (encodeCodeListWithRest tail suffix)
              (rootList :: stack) (len + 1)]
        rw [runState_rootList_complete tail suffix stack (len + 1)]
        have hLen :
            { stack := stack, len := len + 1 + tail.length, ok := true } =
            ({ stack := stack, len := len + (tail.length + 1), ok := true } :
              MachineState) := by
          simp
          omega
        rw [hLen]

  theorem runState_nestedList_complete
      (codes : List Code) (suffix : List Digit) (stack : List Frame) (len : Nat) :
      runState
        (encodeCodeListWithRest codes suffix)
        { stack := nestedList :: stack, len := len, ok := true } =
      runState suffix { stack := stack, len := len, ok := true } := by
    cases codes with
    | nil =>
        simp [encodeCodeListWithRest, runState, stepState]
    | cons head tail =>
        simp [encodeCodeListWithRest, runState, stepState]
        rw [runState_code_complete head (encodeCodeListWithRest tail suffix)
              (nestedList :: stack) len]
        exact runState_nestedList_complete tail suffix stack len
end

theorem parseCodeListLengthStackMachine_complete (codes : List Code) :
    parseCodeListLengthStackMachine
      (encodeCodeListWithRest codes []) =
    some codes.length := by
  unfold parseCodeListLengthStackMachine startState
  rw [runState_rootList_complete codes [] [] 0]
  simp [runState]

theorem codeListLengthStackMachineCheck_complete (codes : List Code) :
    codeListLengthStackMachineCheck
      (encodeCodeListWithRest codes [])
      codes.length = 1 := by
  unfold codeListLengthStackMachineCheck
  rw [parseCodeListLengthStackMachine_complete codes]
  simp

def frameCell : Frame -> Nat
  | rootList => 1
  | nestedList => 2
  | code => 3
  | nat => 4

def decodeFrameCell : Nat -> Option Frame
  | 1 => some rootList
  | 2 => some nestedList
  | 3 => some code
  | 4 => some nat
  | _ => none

def pushFrame (f : Frame) (stack : Nat) : Nat :=
  frameCell f + 5 * stack

@[simp]
theorem pushFrame_ne_zero (f : Frame) (stack : Nat) :
    pushFrame f stack ≠ 0 := by
  cases f <;> simp [pushFrame, frameCell]

def stackTop (stack : Nat) : Option Frame :=
  decodeFrameCell (stack % 5)

def stackTail (stack : Nat) : Nat :=
  stack / 5

def encodeStack : List Frame -> Nat
  | [] => 0
  | f :: fs => pushFrame f (encodeStack fs)

theorem stackTop_push (f : Frame) (stack : Nat) :
    stackTop (pushFrame f stack) = some f := by
  cases f <;>
    simp [stackTop, pushFrame, frameCell, decodeFrameCell,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]

theorem stackTail_push (f : Frame) (stack : Nat) :
    stackTail (pushFrame f stack) = stack := by
  cases f <;>
    simp [stackTail, pushFrame, frameCell, Nat.add_mul_div_left,
      Nat.div_eq_of_lt]

theorem encodeStack_top_tail (f : Frame) (fs : List Frame) :
    stackTop (encodeStack (f :: fs)) = some f /\
    stackTail (encodeStack (f :: fs)) = encodeStack fs := by
  exact ⟨stackTop_push f (encodeStack fs), stackTail_push f (encodeStack fs)⟩

def digitCell : Digit -> Nat
  | d0 => 0
  | d1 => 1
  | d2 => 2
  | d3 => 3

def decodeDigitCell : Nat -> Digit
  | 0 => d0
  | 1 => d1
  | 2 => d2
  | 3 => d3
  | _ => d0

def encodeDigits : List Digit -> Nat
  | [] => 0
  | d :: ds => digitCell d + 4 * encodeDigits ds

def headDigit (input : Nat) : Digit :=
  decodeDigitCell (input % 4)

def tailDigits (input : Nat) : Nat :=
  input / 4

theorem headDigit_cons (d : Digit) (ds : List Digit) :
    headDigit (encodeDigits (d :: ds)) = d := by
  cases d <;>
    simp [headDigit, encodeDigits, digitCell, decodeDigitCell,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]

theorem tailDigits_cons (d : Digit) (ds : List Digit) :
    tailDigits (encodeDigits (d :: ds)) = encodeDigits ds := by
  cases d <;>
    simp [tailDigits, encodeDigits, digitCell, Nat.add_mul_div_left,
      Nat.div_eq_of_lt]

structure NumState where
  rest : Nat
  stack : Nat
  len : Nat
  ok : Bool
deriving DecidableEq, Repr

def encodeMachineState (rest : List Digit) (st : MachineState) : NumState :=
  { rest := encodeDigits rest
  , stack := encodeStack st.stack
  , len := st.len
  , ok := st.ok }

def failNum (st : NumState) : NumState :=
  { st with ok := false }

def stepNum (st : NumState) : NumState :=
  if st.ok = false then st
  else
    match stackTop st.stack, headDigit st.rest with
    | none, _ =>
        failNum st
    | some rootList, d0 =>
        { rest := tailDigits st.rest
        , stack := stackTail st.stack
        , len := st.len
        , ok := true }
    | some rootList, d1 =>
        { rest := tailDigits st.rest
        , stack := pushFrame code (pushFrame rootList (stackTail st.stack))
        , len := st.len + 1
        , ok := true }
    | some rootList, _ =>
        failNum st
    | some nestedList, d0 =>
        { rest := tailDigits st.rest
        , stack := stackTail st.stack
        , len := st.len
        , ok := true }
    | some nestedList, d1 =>
        { rest := tailDigits st.rest
        , stack := pushFrame code (pushFrame nestedList (stackTail st.stack))
        , len := st.len
        , ok := true }
    | some nestedList, _ =>
        failNum st
    | some code, d0 =>
        { rest := tailDigits st.rest
        , stack := pushFrame nat (stackTail st.stack)
        , len := st.len
        , ok := true }
    | some code, d1 =>
        { rest := tailDigits st.rest
        , stack := pushFrame nat (pushFrame nestedList (stackTail st.stack))
        , len := st.len
        , ok := true }
    | some code, _ =>
        failNum st
    | some nat, d2 =>
        { rest := tailDigits st.rest
        , stack := st.stack
        , len := st.len
        , ok := true }
    | some nat, d3 =>
        { rest := tailDigits st.rest
        , stack := stackTail st.stack
        , len := st.len
        , ok := true }
    | some nat, _ =>
        failNum st

/-!
`stepNum` is the semantic transition used for exact prefix-length runs.
Agda's PRF-level `stateStepF` has one additional stabilization branch: after
the input is fully consumed and the control stack is empty, it keeps the final
state unchanged.  This is needed because the concrete PRF later runs for a
numeric fuel such as `suc input-code`, which can be larger than the actual
digit-prefix length.

The small evaluator below mirrors the Agda `stateStepF` branch structure after
the state fields have been projected out of the canonical state code.
-/

def rootStepEval (st : NumState) : NumState :=
  match headDigit st.rest with
  | d0 =>
      { rest := tailDigits st.rest
      , stack := stackTail st.stack
      , len := st.len
      , ok := true }
  | d1 =>
      { rest := tailDigits st.rest
      , stack := pushFrame code (pushFrame rootList (stackTail st.stack))
      , len := st.len + 1
      , ok := true }
  | _ => failNum st

def nestedStepEval (st : NumState) : NumState :=
  match headDigit st.rest with
  | d0 =>
      { rest := tailDigits st.rest
      , stack := stackTail st.stack
      , len := st.len
      , ok := true }
  | d1 =>
      { rest := tailDigits st.rest
      , stack := pushFrame code (pushFrame nestedList (stackTail st.stack))
      , len := st.len
      , ok := true }
  | _ => failNum st

def codeStepEval (st : NumState) : NumState :=
  match headDigit st.rest with
  | d0 =>
      { rest := tailDigits st.rest
      , stack := pushFrame nat (stackTail st.stack)
      , len := st.len
      , ok := true }
  | d1 =>
      { rest := tailDigits st.rest
      , stack := pushFrame nat (pushFrame nestedList (stackTail st.stack))
      , len := st.len
      , ok := true }
  | _ => failNum st

def natStepEval (st : NumState) : NumState :=
  match headDigit st.rest with
  | d2 =>
      { rest := tailDigits st.rest
      , stack := st.stack
      , len := st.len
      , ok := true }
  | d3 =>
      { rest := tailDigits st.rest
      , stack := stackTail st.stack
      , len := st.len
      , ok := true }
  | _ => failNum st

def stackNonemptyStepEval (st : NumState) : NumState :=
  match stackTop st.stack with
  | some rootList => rootStepEval st
  | some nestedList => nestedStepEval st
  | some code => codeStepEval st
  | some nat => natStepEval st
  | none => failNum st

def stackEmptyStepEval (st : NumState) : NumState :=
  if st.rest = 0 then st else failNum st

def stateStepEval (st : NumState) : NumState :=
  if st.ok = false then st
  else if st.stack = 0 then stackEmptyStepEval st
  else stackNonemptyStepEval st

def runStateStepEvalFuel : Nat -> NumState -> NumState
  | 0, st => st
  | Nat.succ fuel, st => runStateStepEvalFuel fuel (stateStepEval st)

def stepNumStable (st : NumState) : NumState :=
  if st.ok = false then st
  else if st.stack = 0 then
    if st.rest = 0 then st else failNum st
  else stepNum st

def runNumStableFuel : Nat -> NumState -> NumState
  | 0, st => st
  | Nat.succ fuel, st => runNumStableFuel fuel (stepNumStable st)

theorem stateStepEval_eq_stepNumStable (st : NumState) :
    stateStepEval st = stepNumStable st := by
  by_cases hOk : st.ok = false
  · simp [stateStepEval, stepNumStable, hOk]
  · by_cases hStack : st.stack = 0
    · simp [stateStepEval, stepNumStable, hOk, hStack, stackEmptyStepEval]
    · unfold stateStepEval stepNumStable
      simp [hOk, hStack]
      unfold stackNonemptyStepEval rootStepEval nestedStepEval codeStepEval
        natStepEval stepNum
      simp [hOk]
      cases stackTop st.stack with
      | none =>
          cases headDigit st.rest <;> simp [failNum]
      | some top =>
          cases top <;> cases headDigit st.rest <;> simp [failNum]

theorem stateStepEval_done (len : Nat) :
    stateStepEval { rest := 0, stack := 0, len := len, ok := true } =
    ({ rest := 0, stack := 0, len := len, ok := true } : NumState) := by
  simp [stateStepEval, stackEmptyStepEval]

theorem runStateStepEvalFuel_eq_runNumStableFuel
    (fuel : Nat) (st : NumState) :
    runStateStepEvalFuel fuel st = runNumStableFuel fuel st := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel ih =>
      simp [runStateStepEvalFuel, runNumStableFuel,
        stateStepEval_eq_stepNumStable, ih]

theorem runStateStepEvalFuel_add (a b : Nat) (st : NumState) :
    runStateStepEvalFuel (a + b) st =
    runStateStepEvalFuel b (runStateStepEvalFuel a st) := by
  induction a generalizing st with
  | zero => simp [runStateStepEvalFuel]
  | succ a ih =>
      simp [runStateStepEvalFuel, Nat.succ_add]
      exact ih (stateStepEval st)

theorem runStateStepEvalFuel_done (fuel len : Nat) :
    runStateStepEvalFuel fuel
      { rest := 0, stack := 0, len := len, ok := true } =
    ({ rest := 0, stack := 0, len := len, ok := true } : NumState) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      simp [runStateStepEvalFuel, stateStepEval_done, ih]

def runNumFuel : Nat -> NumState -> NumState
  | 0, st => st
  | Nat.succ fuel, st => runNumFuel fuel (stepNum st)

theorem runNumFuel_add (a b : Nat) (st : NumState) :
    runNumFuel (a + b) st = runNumFuel b (runNumFuel a st) := by
  induction a generalizing st with
  | zero => simp [runNumFuel]
  | succ a ih =>
      simp [runNumFuel, Nat.succ_add]
      exact ih (stepNum st)

theorem stepNum_root_d0 (ds : List Digit) (stack : List Frame) (len : Nat) :
    stepNum
      (encodeMachineState
        (d0 :: ds)
        { stack := rootList :: stack, len := len, ok := true }) =
    encodeMachineState ds { stack := stack, len := len, ok := true } := by
  simp [stepNum, encodeMachineState, headDigit_cons, tailDigits_cons,
    encodeStack, stackTop_push, stackTail_push]

theorem stepNum_root_d1 (ds : List Digit) (stack : List Frame) (len : Nat) :
    stepNum
      (encodeMachineState
        (d1 :: ds)
        { stack := rootList :: stack, len := len, ok := true }) =
    encodeMachineState
      ds
      { stack := code :: rootList :: stack, len := len + 1, ok := true } := by
  simp [stepNum, encodeMachineState, headDigit_cons, tailDigits_cons,
    stackTop_push, stackTail_push, encodeStack]

theorem stepNum_nested_d0 (ds : List Digit) (stack : List Frame) (len : Nat) :
    stepNum
      (encodeMachineState
        (d0 :: ds)
        { stack := nestedList :: stack, len := len, ok := true }) =
    encodeMachineState ds { stack := stack, len := len, ok := true } := by
  simp [stepNum, encodeMachineState, headDigit_cons, tailDigits_cons,
    encodeStack, stackTop_push, stackTail_push]

theorem stepNum_nested_d1 (ds : List Digit) (stack : List Frame) (len : Nat) :
    stepNum
      (encodeMachineState
        (d1 :: ds)
        { stack := nestedList :: stack, len := len, ok := true }) =
    encodeMachineState
      ds
      { stack := code :: nestedList :: stack, len := len, ok := true } := by
  simp [stepNum, encodeMachineState, headDigit_cons, tailDigits_cons,
    stackTop_push, stackTail_push, encodeStack]

theorem stepNum_code_d0 (ds : List Digit) (stack : List Frame) (len : Nat) :
    stepNum
      (encodeMachineState
        (d0 :: ds)
        { stack := code :: stack, len := len, ok := true }) =
    encodeMachineState ds { stack := nat :: stack, len := len, ok := true } := by
  simp [stepNum, encodeMachineState, headDigit_cons, tailDigits_cons,
    stackTop_push, stackTail_push, encodeStack]

theorem stepNum_code_d1 (ds : List Digit) (stack : List Frame) (len : Nat) :
    stepNum
      (encodeMachineState
        (d1 :: ds)
        { stack := code :: stack, len := len, ok := true }) =
    encodeMachineState
      ds
      { stack := nat :: nestedList :: stack, len := len, ok := true } := by
  simp [stepNum, encodeMachineState, headDigit_cons, tailDigits_cons,
    stackTop_push, stackTail_push, encodeStack]

theorem stepNum_nat_d2 (ds : List Digit) (stack : List Frame) (len : Nat) :
    stepNum
      (encodeMachineState
        (d2 :: ds)
        { stack := nat :: stack, len := len, ok := true }) =
    encodeMachineState ds { stack := nat :: stack, len := len, ok := true } := by
  simp [stepNum, encodeMachineState, headDigit_cons, tailDigits_cons,
    encodeStack, stackTop_push]

theorem stepNum_nat_d3 (ds : List Digit) (stack : List Frame) (len : Nat) :
    stepNum
      (encodeMachineState
        (d3 :: ds)
        { stack := nat :: stack, len := len, ok := true }) =
    encodeMachineState ds { stack := stack, len := len, ok := true } := by
  simp [stepNum, encodeMachineState, headDigit_cons, tailDigits_cons,
    encodeStack, stackTop_push, stackTail_push]

theorem stateStepEval_failed (rest stack len : Nat) :
    stateStepEval { rest := rest, stack := stack, len := len, ok := false } =
    ({ rest := rest, stack := stack, len := len, ok := false } : NumState) := by
  simp [stateStepEval]

theorem runStateStepEvalFuel_failed (fuel rest stack len : Nat) :
    runStateStepEvalFuel fuel
      { rest := rest, stack := stack, len := len, ok := false } =
    ({ rest := rest, stack := stack, len := len, ok := false } : NumState) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      simp [runStateStepEvalFuel, stateStepEval_failed, ih]

theorem stateStepEval_empty_nonzero (rest len : Nat) (h : rest ≠ 0) :
    stateStepEval { rest := rest, stack := 0, len := len, ok := true } =
    ({ rest := rest, stack := 0, len := len, ok := false } : NumState) := by
  simp [stateStepEval, stackEmptyStepEval, h, failNum]

theorem runStateStepEvalFuel_empty_nonzero
    (fuel rest len : Nat) (h : rest ≠ 0) :
    runStateStepEvalFuel (Nat.succ fuel)
      { rest := rest, stack := 0, len := len, ok := true } =
    ({ rest := rest, stack := 0, len := len, ok := false } : NumState) := by
  simp [runStateStepEvalFuel, stateStepEval_empty_nonzero rest len h]
  exact runStateStepEvalFuel_failed fuel rest 0 len

theorem stateStepEval_root_d2_failed
    (ds : List Digit) (stack : List Frame) (len : Nat) :
    stateStepEval
      (encodeMachineState
        (d2 :: ds)
        { stack := rootList :: stack, len := len, ok := true }) =
    { encodeMachineState
        (d2 :: ds)
        { stack := rootList :: stack, len := len, ok := true } with
  ok := false } := by
  simp [stateStepEval, stackNonemptyStepEval, rootStepEval,
    encodeMachineState, headDigit_cons, encodeStack, stackTop_push, failNum]

theorem stateStepEval_root_d3_failed
    (ds : List Digit) (stack : List Frame) (len : Nat) :
    stateStepEval
      (encodeMachineState
        (d3 :: ds)
        { stack := rootList :: stack, len := len, ok := true }) =
    { encodeMachineState
        (d3 :: ds)
        { stack := rootList :: stack, len := len, ok := true } with
  ok := false } := by
  simp [stateStepEval, stackNonemptyStepEval, rootStepEval,
    encodeMachineState, headDigit_cons, encodeStack, stackTop_push, failNum]

theorem stateStepEval_nested_d2_failed
    (ds : List Digit) (stack : List Frame) (len : Nat) :
    stateStepEval
      (encodeMachineState
        (d2 :: ds)
        { stack := nestedList :: stack, len := len, ok := true }) =
    { encodeMachineState
        (d2 :: ds)
        { stack := nestedList :: stack, len := len, ok := true } with
  ok := false } := by
  simp [stateStepEval, stackNonemptyStepEval, nestedStepEval,
    encodeMachineState, headDigit_cons, encodeStack, stackTop_push, failNum]

theorem stateStepEval_nested_d3_failed
    (ds : List Digit) (stack : List Frame) (len : Nat) :
    stateStepEval
      (encodeMachineState
        (d3 :: ds)
        { stack := nestedList :: stack, len := len, ok := true }) =
    { encodeMachineState
        (d3 :: ds)
        { stack := nestedList :: stack, len := len, ok := true } with
  ok := false } := by
  simp [stateStepEval, stackNonemptyStepEval, nestedStepEval,
    encodeMachineState, headDigit_cons, encodeStack, stackTop_push, failNum]

theorem stateStepEval_code_d2_failed
    (ds : List Digit) (stack : List Frame) (len : Nat) :
    stateStepEval
      (encodeMachineState
        (d2 :: ds)
        { stack := code :: stack, len := len, ok := true }) =
    { encodeMachineState
        (d2 :: ds)
        { stack := code :: stack, len := len, ok := true } with
  ok := false } := by
  simp [stateStepEval, stackNonemptyStepEval, codeStepEval,
    encodeMachineState, headDigit_cons, encodeStack, stackTop_push, failNum]

theorem stateStepEval_code_d3_failed
    (ds : List Digit) (stack : List Frame) (len : Nat) :
    stateStepEval
      (encodeMachineState
        (d3 :: ds)
        { stack := code :: stack, len := len, ok := true }) =
    { encodeMachineState
        (d3 :: ds)
        { stack := code :: stack, len := len, ok := true } with
  ok := false } := by
  simp [stateStepEval, stackNonemptyStepEval, codeStepEval,
    encodeMachineState, headDigit_cons, encodeStack, stackTop_push, failNum]

theorem stateStepEval_nat_d0_failed
    (ds : List Digit) (stack : List Frame) (len : Nat) :
    stateStepEval
      (encodeMachineState
        (d0 :: ds)
        { stack := nat :: stack, len := len, ok := true }) =
    { encodeMachineState
        (d0 :: ds)
        { stack := nat :: stack, len := len, ok := true } with
  ok := false } := by
  simp [stateStepEval, stackNonemptyStepEval, natStepEval,
    encodeMachineState, headDigit_cons, encodeStack, stackTop_push, failNum]

theorem stateStepEval_nat_d1_failed
    (ds : List Digit) (stack : List Frame) (len : Nat) :
    stateStepEval
      (encodeMachineState
        (d1 :: ds)
        { stack := nat :: stack, len := len, ok := true }) =
    { encodeMachineState
        (d1 :: ds)
        { stack := nat :: stack, len := len, ok := true } with
  ok := false } := by
  simp [stateStepEval, stackNonemptyStepEval, natStepEval,
    encodeMachineState, headDigit_cons, encodeStack, stackTop_push, failNum]

theorem stateStepEval_root_d0 (ds : List Digit) (stack : List Frame) (len : Nat) :
    stateStepEval
      (encodeMachineState
        (d0 :: ds)
        { stack := rootList :: stack, len := len, ok := true }) =
    encodeMachineState ds { stack := stack, len := len, ok := true } := by
  simp [stateStepEval, stackNonemptyStepEval, rootStepEval,
    encodeMachineState, headDigit_cons, tailDigits_cons,
    encodeStack, stackTop_push, stackTail_push]

theorem stateStepEval_root_d1 (ds : List Digit) (stack : List Frame) (len : Nat) :
    stateStepEval
      (encodeMachineState
        (d1 :: ds)
        { stack := rootList :: stack, len := len, ok := true }) =
    encodeMachineState
      ds
      { stack := code :: rootList :: stack, len := len + 1, ok := true } := by
  simp [stateStepEval, stackNonemptyStepEval, rootStepEval,
    encodeMachineState, headDigit_cons, tailDigits_cons,
    stackTop_push, stackTail_push, encodeStack]

theorem stateStepEval_nested_d0
    (ds : List Digit) (stack : List Frame) (len : Nat) :
    stateStepEval
      (encodeMachineState
        (d0 :: ds)
        { stack := nestedList :: stack, len := len, ok := true }) =
    encodeMachineState ds { stack := stack, len := len, ok := true } := by
  simp [stateStepEval, stackNonemptyStepEval, nestedStepEval,
    encodeMachineState, headDigit_cons, tailDigits_cons,
    encodeStack, stackTop_push, stackTail_push]

theorem stateStepEval_nested_d1
    (ds : List Digit) (stack : List Frame) (len : Nat) :
    stateStepEval
      (encodeMachineState
        (d1 :: ds)
        { stack := nestedList :: stack, len := len, ok := true }) =
    encodeMachineState
      ds
      { stack := code :: nestedList :: stack, len := len, ok := true } := by
  simp [stateStepEval, stackNonemptyStepEval, nestedStepEval,
    encodeMachineState, headDigit_cons, tailDigits_cons,
    stackTop_push, stackTail_push, encodeStack]

theorem stateStepEval_code_d0
    (ds : List Digit) (stack : List Frame) (len : Nat) :
    stateStepEval
      (encodeMachineState
        (d0 :: ds)
        { stack := code :: stack, len := len, ok := true }) =
    encodeMachineState ds { stack := nat :: stack, len := len, ok := true } := by
  simp [stateStepEval, stackNonemptyStepEval, codeStepEval,
    encodeMachineState, headDigit_cons, tailDigits_cons,
    stackTop_push, stackTail_push, encodeStack]

theorem stateStepEval_code_d1
    (ds : List Digit) (stack : List Frame) (len : Nat) :
    stateStepEval
      (encodeMachineState
        (d1 :: ds)
        { stack := code :: stack, len := len, ok := true }) =
    encodeMachineState
      ds
      { stack := nat :: nestedList :: stack, len := len, ok := true } := by
  simp [stateStepEval, stackNonemptyStepEval, codeStepEval,
    encodeMachineState, headDigit_cons, tailDigits_cons,
    stackTop_push, stackTail_push, encodeStack]

theorem stateStepEval_nat_d2
    (ds : List Digit) (stack : List Frame) (len : Nat) :
    stateStepEval
      (encodeMachineState
        (d2 :: ds)
        { stack := nat :: stack, len := len, ok := true }) =
    encodeMachineState ds { stack := nat :: stack, len := len, ok := true } := by
  simp [stateStepEval, stackNonemptyStepEval, natStepEval,
    encodeMachineState, headDigit_cons, tailDigits_cons,
    encodeStack, stackTop_push]

theorem stateStepEval_nat_d3
    (ds : List Digit) (stack : List Frame) (len : Nat) :
    stateStepEval
      (encodeMachineState
        (d3 :: ds)
        { stack := nat :: stack, len := len, ok := true }) =
    encodeMachineState ds { stack := stack, len := len, ok := true } := by
  simp [stateStepEval, stackNonemptyStepEval, natStepEval,
    encodeMachineState, headDigit_cons, tailDigits_cons,
    encodeStack, stackTop_push, stackTail_push]

theorem runStateStepEval_nat_prefix_complete
    (n : Nat) (suffix : List Digit) (stack : List Frame) (len : Nat) :
    runStateStepEvalFuel
      (encodeNatWithRest n []).length
      (encodeMachineState
        (encodeNatWithRest n suffix)
        { stack := nat :: stack, len := len, ok := true }) =
    encodeMachineState suffix { stack := stack, len := len, ok := true } := by
  induction n generalizing suffix stack len with
  | zero =>
      simp [encodeNatWithRest, runStateStepEvalFuel, stateStepEval_nat_d3]
  | succ n ih =>
      simp [encodeNatWithRest, runStateStepEvalFuel]
      rw [stateStepEval_nat_d2]
      exact ih suffix stack len

mutual
  theorem runStateStepEval_code_prefix_complete
      (c : Code) (suffix : List Digit) (stack : List Frame) (len : Nat) :
      runStateStepEvalFuel
        (encodeCodeWithRest c []).length
        (encodeMachineState
          (encodeCodeWithRest c suffix)
          { stack := code :: stack, len := len, ok := true }) =
      encodeMachineState suffix { stack := stack, len := len, ok := true } := by
    cases c with
    | atom n =>
        simp [encodeCodeWithRest, runStateStepEvalFuel]
        rw [stateStepEval_code_d0]
        exact runStateStepEval_nat_prefix_complete n suffix stack len
    | node tag children =>
        simp [encodeCodeWithRest, runStateStepEvalFuel]
        rw [stateStepEval_code_d1]
        rw [encodeNatWithRest_length tag (encodeCodeListWithRest children [])]
        rw [runStateStepEvalFuel_add]
        rw [runStateStepEval_nat_prefix_complete tag
              (encodeCodeListWithRest children suffix)
              (nestedList :: stack) len]
        exact runStateStepEval_nestedList_prefix_complete children suffix stack len

  theorem runStateStepEval_rootList_prefix_complete
      (codes : List Code) (suffix : List Digit) (stack : List Frame) (len : Nat) :
      runStateStepEvalFuel
        (encodeCodeListWithRest codes []).length
        (encodeMachineState
          (encodeCodeListWithRest codes suffix)
          { stack := rootList :: stack, len := len, ok := true }) =
      encodeMachineState suffix
        { stack := stack, len := len + codes.length, ok := true } := by
    cases codes with
    | nil =>
        simp [encodeCodeListWithRest, runStateStepEvalFuel,
          stateStepEval_root_d0]
    | cons head tail =>
        simp [encodeCodeListWithRest, runStateStepEvalFuel]
        rw [stateStepEval_root_d1]
        rw [encodeCodeWithRest_length head (encodeCodeListWithRest tail [])]
        rw [runStateStepEvalFuel_add]
        rw [runStateStepEval_code_prefix_complete head
              (encodeCodeListWithRest tail suffix)
              (rootList :: stack) (len + 1)]
        rw [runStateStepEval_rootList_prefix_complete tail suffix stack (len + 1)]
        have hLen :
            ({ rest := encodeDigits suffix,
               stack := encodeStack stack,
               len := len + 1 + tail.length,
               ok := true } : NumState) =
            ({ rest := encodeDigits suffix,
               stack := encodeStack stack,
               len := len + (tail.length + 1),
               ok := true } : NumState) := by
          simp
          omega
        change
          ({ rest := encodeDigits suffix,
             stack := encodeStack stack,
             len := len + 1 + tail.length,
             ok := true } : NumState) =
          ({ rest := encodeDigits suffix,
             stack := encodeStack stack,
             len := len + (tail.length + 1),
             ok := true } : NumState)
        exact hLen

  theorem runStateStepEval_nestedList_prefix_complete
      (codes : List Code) (suffix : List Digit) (stack : List Frame) (len : Nat) :
      runStateStepEvalFuel
        (encodeCodeListWithRest codes []).length
        (encodeMachineState
          (encodeCodeListWithRest codes suffix)
          { stack := nestedList :: stack, len := len, ok := true }) =
      encodeMachineState suffix { stack := stack, len := len, ok := true } := by
    cases codes with
    | nil =>
        simp [encodeCodeListWithRest, runStateStepEvalFuel,
          stateStepEval_nested_d0]
    | cons head tail =>
        simp [encodeCodeListWithRest, runStateStepEvalFuel]
        rw [stateStepEval_nested_d1]
        rw [encodeCodeWithRest_length head (encodeCodeListWithRest tail [])]
        rw [runStateStepEvalFuel_add]
        rw [runStateStepEval_code_prefix_complete head
              (encodeCodeListWithRest tail suffix)
              (nestedList :: stack) len]
        exact runStateStepEval_nestedList_prefix_complete tail suffix stack len
end

theorem runStateStepEval_codeList_closed_complete
    (codes : List Code) :
    runStateStepEvalFuel
      (encodeCodeListWithRest codes []).length
      (encodeMachineState
        (encodeCodeListWithRest codes [])
        { stack := rootList :: [], len := 0, ok := true }) =
    encodeMachineState [] { stack := [], len := codes.length, ok := true } := by
  simpa using runStateStepEval_rootList_prefix_complete codes [] [] 0

theorem runStateStepEval_codeList_closed_complete_extra
    (codes : List Code) (extra : Nat) :
    runStateStepEvalFuel
      ((encodeCodeListWithRest codes []).length + extra)
      (encodeMachineState
        (encodeCodeListWithRest codes [])
        { stack := rootList :: [], len := 0, ok := true }) =
    encodeMachineState [] { stack := [], len := codes.length, ok := true } := by
  rw [runStateStepEvalFuel_add]
  rw [runStateStepEval_codeList_closed_complete codes]
  exact runStateStepEvalFuel_done extra codes.length

theorem runNum_nat_prefix_complete
    (n : Nat) (suffix : List Digit) (stack : List Frame) (len : Nat) :
    runNumFuel
      (encodeNatWithRest n []).length
      (encodeMachineState
        (encodeNatWithRest n suffix)
        { stack := nat :: stack, len := len, ok := true }) =
    encodeMachineState suffix { stack := stack, len := len, ok := true } := by
  induction n generalizing suffix stack len with
  | zero =>
      simp [encodeNatWithRest, runNumFuel, stepNum_nat_d3]
  | succ n ih =>
      simp [encodeNatWithRest, runNumFuel]
      rw [stepNum_nat_d2]
      exact ih suffix stack len

mutual
  theorem runNum_code_prefix_complete
      (c : Code) (suffix : List Digit) (stack : List Frame) (len : Nat) :
      runNumFuel
        (encodeCodeWithRest c []).length
        (encodeMachineState
          (encodeCodeWithRest c suffix)
          { stack := code :: stack, len := len, ok := true }) =
      encodeMachineState suffix { stack := stack, len := len, ok := true } := by
    cases c with
    | atom n =>
        simp [encodeCodeWithRest, runNumFuel]
        rw [stepNum_code_d0]
        exact runNum_nat_prefix_complete n suffix stack len
    | node tag children =>
        simp [encodeCodeWithRest, runNumFuel]
        rw [stepNum_code_d1]
        rw [encodeNatWithRest_length tag (encodeCodeListWithRest children [])]
        rw [runNumFuel_add]
        rw [runNum_nat_prefix_complete tag (encodeCodeListWithRest children suffix)
              (nestedList :: stack) len]
        exact runNum_nestedList_prefix_complete children suffix stack len

  theorem runNum_rootList_prefix_complete
      (codes : List Code) (suffix : List Digit) (stack : List Frame) (len : Nat) :
      runNumFuel
        (encodeCodeListWithRest codes []).length
        (encodeMachineState
          (encodeCodeListWithRest codes suffix)
          { stack := rootList :: stack, len := len, ok := true }) =
      encodeMachineState suffix
        { stack := stack, len := len + codes.length, ok := true } := by
    cases codes with
    | nil =>
        simp [encodeCodeListWithRest, runNumFuel, stepNum_root_d0]
    | cons head tail =>
        simp [encodeCodeListWithRest, runNumFuel]
        rw [stepNum_root_d1]
        rw [encodeCodeWithRest_length head (encodeCodeListWithRest tail [])]
        rw [runNumFuel_add]
        rw [runNum_code_prefix_complete head (encodeCodeListWithRest tail suffix)
              (rootList :: stack) (len + 1)]
        rw [runNum_rootList_prefix_complete tail suffix stack (len + 1)]
        have hLen :
            ({ rest := encodeDigits suffix,
               stack := encodeStack stack,
               len := len + 1 + tail.length,
               ok := true } : NumState) =
            ({ rest := encodeDigits suffix,
               stack := encodeStack stack,
               len := len + (tail.length + 1),
               ok := true } : NumState) := by
          simp
          omega
        change
          ({ rest := encodeDigits suffix,
             stack := encodeStack stack,
             len := len + 1 + tail.length,
             ok := true } : NumState) =
          ({ rest := encodeDigits suffix,
             stack := encodeStack stack,
             len := len + (tail.length + 1),
             ok := true } : NumState)
        exact hLen

  theorem runNum_nestedList_prefix_complete
      (codes : List Code) (suffix : List Digit) (stack : List Frame) (len : Nat) :
      runNumFuel
        (encodeCodeListWithRest codes []).length
        (encodeMachineState
          (encodeCodeListWithRest codes suffix)
          { stack := nestedList :: stack, len := len, ok := true }) =
      encodeMachineState suffix { stack := stack, len := len, ok := true } := by
    cases codes with
    | nil =>
        simp [encodeCodeListWithRest, runNumFuel, stepNum_nested_d0]
    | cons head tail =>
        simp [encodeCodeListWithRest, runNumFuel]
        rw [stepNum_nested_d1]
        rw [encodeCodeWithRest_length head (encodeCodeListWithRest tail [])]
        rw [runNumFuel_add]
        rw [runNum_code_prefix_complete head (encodeCodeListWithRest tail suffix)
              (nestedList :: stack) len]
        exact runNum_nestedList_prefix_complete tail suffix stack len
end

theorem runNum_codeList_closed_complete (codes : List Code) :
    runNumFuel
      (encodeCodeListWithRest codes []).length
      (encodeMachineState
        (encodeCodeListWithRest codes [])
        { stack := rootList :: [], len := 0, ok := true }) =
    encodeMachineState [] { stack := [], len := codes.length, ok := true } := by
  simpa using runNum_rootList_prefix_complete codes [] [] 0

/-!
The valid-branch `stepNum_*` lemmas above are the key bridge to Agda's
`stateStepF`: they show that the encoded numeric state consumes the same valid
digits as the explicit stack machine.  The full prefix-length fuel induction is
now stated with prefix fuel only.  The first attempted whole-rest fuel
statement was deliberately not kept, because it incorrectly ran through the
continuation suffix as well.
-/

end LeanShadow.CodeListLengthStackMachineMini
