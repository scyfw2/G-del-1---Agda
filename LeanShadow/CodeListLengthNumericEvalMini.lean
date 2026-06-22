import LeanShadow.CodeListLengthStackMachineMini

namespace LeanShadow.CodeListLengthNumericEvalMini

open LeanShadow.CodeListLengthMini
open LeanShadow.CodeListLengthMini.Digit
open LeanShadow.CodeListLengthStackMachineMini
open LeanShadow.CodeListLengthScannerMini

/-!
This file is the small Lean route-finder for Agda's remaining scanner theorem.

It does not prove the final all-input theorem

```text
evalPRF lengthScannerF (args₂ list-code len)
  = codeListLengthScannerCheck list-code len
```

Instead it isolates the bridge that is directly portable to Agda:

* run the numeric state-machine evaluator for an explicit fuel;
* use the canonical prefix theorem plus completed-state stability;
* package the final-state check.

The remaining all-input theorem needs one more correspondence lemma between
arbitrary numeric inputs and the recursive scanner/parser.
-/

def scannerStartStateEval (input : Nat) : NumState :=
  { rest := input
  , stack := encodeStack [Frame.rootList]
  , len := 0
  , ok := true }

def scannerFinalCheckEval (st : NumState) (expectedLen : Nat) : Nat :=
  if st.ok = true then
    if st.rest = 0 then
      if st.stack = 0 then
        if st.len = expectedLen then 1 else 0
      else 0
    else 0
  else 0

def lengthScannerEvalCheckWithFuel
    (fuel input expectedLen : Nat) : Nat :=
  scannerFinalCheckEval
    (runStateStepEvalFuel fuel (scannerStartStateEval input))
    expectedLen

/-!
`runStateStepEvalFuel` is tail-iterative:

```text
run (succ fuel) st = run fuel (step st)
```

Agda's `precF start step` evaluator is snoc-style:

```text
prec 0     input = start input
prec (n+1) input = step (prec n input)
```

The next theorem is the Lean version of the remaining Agda bridge:
the two iteration styles agree for the same deterministic step.
-/

def runScannerStateFuelEval : Nat -> Nat -> NumState
  | 0, input => scannerStartStateEval input
  | Nat.succ fuel, input =>
      stateStepEval (runScannerStateFuelEval fuel input)

theorem runStateStepEvalFuel_snoc
    (fuel : Nat) (st : NumState) :
    runStateStepEvalFuel (Nat.succ fuel) st =
    stateStepEval (runStateStepEvalFuel fuel st) := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel ih =>
      simp [runStateStepEvalFuel]
      exact ih (stateStepEval st)

theorem runScannerStateFuelEval_eq_tail_runner
    (fuel input : Nat) :
    runScannerStateFuelEval fuel input =
    runStateStepEvalFuel fuel (scannerStartStateEval input) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      simp [runScannerStateFuelEval]
      rw [ih]
      exact (runStateStepEvalFuel_snoc fuel
        (scannerStartStateEval input)).symm

def lengthScannerPRStyleEvalCheckWithFuel
    (fuel input expectedLen : Nat) : Nat :=
  scannerFinalCheckEval
    (runScannerStateFuelEval fuel input)
    expectedLen

theorem lengthScannerPRStyleEvalCheckWithFuel_eq_tail
    (fuel input expectedLen : Nat) :
    lengthScannerPRStyleEvalCheckWithFuel fuel input expectedLen =
    lengthScannerEvalCheckWithFuel fuel input expectedLen := by
  unfold lengthScannerPRStyleEvalCheckWithFuel lengthScannerEvalCheckWithFuel
  rw [runScannerStateFuelEval_eq_tail_runner]

theorem scannerStartStateEval_codeList
    (codes : List Code) :
    scannerStartStateEval
      (encodeDigits (encodeCodeListWithRest codes [])) =
    encodeMachineState
      (encodeCodeListWithRest codes [])
      { stack := [Frame.rootList], len := 0, ok := true } := by
  rfl

theorem scannerFinalCheckEval_accept (len : Nat) :
    scannerFinalCheckEval
      ({ rest := 0, stack := 0, len := len, ok := true } : NumState)
      len = 1 := by
  simp [scannerFinalCheckEval]

theorem scannerFinalCheckEval_reject_wrong_len
    {actual expected : Nat} (h : actual ≠ expected) :
    scannerFinalCheckEval
      ({ rest := 0, stack := 0, len := actual, ok := true } : NumState)
      expected = 0 := by
  simp [scannerFinalCheckEval, h]

theorem lengthScannerEvalCheckWithFuel_codeList_complete_extra
    (codes : List Code) (extra : Nat) :
    lengthScannerEvalCheckWithFuel
      ((encodeCodeListWithRest codes []).length + extra)
      (encodeDigits (encodeCodeListWithRest codes []))
      codes.length = 1 := by
  unfold lengthScannerEvalCheckWithFuel
  rw [scannerStartStateEval_codeList codes]
  rw [runStateStepEval_codeList_closed_complete_extra codes extra]
  exact scannerFinalCheckEval_accept codes.length

theorem lengthScannerPRStyleEvalCheckWithFuel_codeList_complete_extra
    (codes : List Code) (extra : Nat) :
    lengthScannerPRStyleEvalCheckWithFuel
      ((encodeCodeListWithRest codes []).length + extra)
      (encodeDigits (encodeCodeListWithRest codes []))
      codes.length = 1 := by
  rw [lengthScannerPRStyleEvalCheckWithFuel_eq_tail]
  exact lengthScannerEvalCheckWithFuel_codeList_complete_extra codes extra

theorem lengthScannerEvalCheckWithFuel_codeList_wrong_len_extra
    (codes : List Code) (expected extra : Nat)
    (h : codes.length ≠ expected) :
    lengthScannerEvalCheckWithFuel
      ((encodeCodeListWithRest codes []).length + extra)
      (encodeDigits (encodeCodeListWithRest codes []))
      expected = 0 := by
  unfold lengthScannerEvalCheckWithFuel
  rw [scannerStartStateEval_codeList codes]
  rw [runStateStepEval_codeList_closed_complete_extra codes extra]
  exact scannerFinalCheckEval_reject_wrong_len h







/- Fixed numeric fuel bridge.  Lean confirms the useful proof shape:
   once canonical-code bounds provide

     prefix-length <= encoded-input + 1,

   the existing `prefix-length + extra` theorem specializes to fixed fuel
   `suc input`.

The unconditional bound is proved through a syntax-size bridge rather than by
trying to bound arbitrary digit suffixes.  Plain digit suffixes can contain
many trailing `d0`s with numeric value `0`; canonical code/list structure pays
for those terminators through the surrounding nonzero tags.
-/

mutual
  def codeSize : Code -> Nat
    | Code.atom n => n + 1
    | Code.node tag children => tag + 1 + codeListSize children

  def codeListSize : List Code -> Nat
    | [] => 0
    | head :: tail => 1 + codeSize head + codeListSize tail
end

theorem codeSize_pos (c : Code) : 1 ≤ codeSize c := by
  cases c with
  | atom n =>
      simp [codeSize]
  | node tag children =>
      simp [codeSize]
      omega

theorem encodeNatWithRest_length_linear
    (n : Nat) (rest : List Digit) :
    (encodeNatWithRest n rest).length = n + 1 + rest.length := by
  induction n with
  | zero =>
      simp [encodeNatWithRest]
      omega
  | succ n ih =>
      simp [encodeNatWithRest, ih]
      omega

mutual
  theorem codeDigits_length_le_size
      (c : Code) (rest : List Digit) :
      (encodeCodeWithRest c rest).length ≤
      2 * codeSize c + rest.length + 1 := by
    cases c with
    | atom n =>
        simp [encodeCodeWithRest, codeSize, encodeNatWithRest_length_linear]
        omega
    | node tag children =>
        simp [encodeCodeWithRest, codeSize, encodeNatWithRest_length_linear]
        have hChildren := codeListDigits_length_le_size children rest
        omega

  theorem codeListDigits_length_le_size
      (codes : List Code) (rest : List Digit) :
      (encodeCodeListWithRest codes rest).length ≤
      2 * codeListSize codes + rest.length + 1 := by
    cases codes with
    | nil =>
        simp [encodeCodeListWithRest, codeListSize]
    | cons head tail =>
        simp [encodeCodeListWithRest, codeListSize]
        have hHead :=
          codeDigits_length_le_size head (encodeCodeListWithRest tail rest)
        have hTail := codeListDigits_length_le_size tail rest
        omega
end

theorem natSize_base_le_encodeNatWithRest
    (tag base : Nat) (rest : List Digit)
    (hBase : base ≤ encodeDigits rest) :
    tag + base + 1 ≤ encodeDigits (encodeNatWithRest tag rest) := by
  induction tag with
  | zero =>
      simp [encodeNatWithRest, encodeDigits, digitCell]
      omega
  | succ tag ih =>
      simp [encodeNatWithRest, encodeDigits, digitCell]
      have h := ih
      omega

mutual
  theorem codeSize_base_le_encodeCodeWithRest
      (c : Code) (base : Nat) (rest : List Digit)
      (hBase : base ≤ encodeDigits rest) :
      codeSize c + base ≤ encodeDigits (encodeCodeWithRest c rest) := by
    cases c with
    | atom n =>
        simp [encodeCodeWithRest, codeSize, encodeDigits, digitCell]
        have hNat := natSize_base_le_encodeNatWithRest n base rest hBase
        omega
    | node tag children =>
        simp [encodeCodeWithRest, codeSize, encodeDigits, digitCell]
        have hChildren :=
          codeListSize_base_le_encodeCodeListWithRest children base rest hBase
        have hNat :=
          natSize_base_le_encodeNatWithRest
            tag (codeListSize children + base)
            (encodeCodeListWithRest children rest)
            hChildren
        omega

  theorem codeListSize_base_le_encodeCodeListWithRest
      (codes : List Code) (base : Nat) (rest : List Digit)
      (hBase : base ≤ encodeDigits rest) :
      codeListSize codes + base ≤
      encodeDigits (encodeCodeListWithRest codes rest) := by
    cases codes with
    | nil =>
        simp [encodeCodeListWithRest, codeListSize, encodeDigits, digitCell]
        omega
    | cons head tail =>
        simp [encodeCodeListWithRest, codeListSize, encodeDigits, digitCell]
        have hTail :=
          codeListSize_base_le_encodeCodeListWithRest tail base rest hBase
        have hHead :=
          codeSize_base_le_encodeCodeWithRest
            head (codeListSize tail + base)
            (encodeCodeListWithRest tail rest)
            hTail
        omega
end

theorem codeListSize_le_encodeClosed (codes : List Code) :
    codeListSize codes ≤ encodeDigits (encodeCodeListWithRest codes []) := by
  simpa using
    codeListSize_base_le_encodeCodeListWithRest codes 0 [] (by simp [encodeDigits])

theorem two_codeListSize_le_encodeClosed (codes : List Code) :
    2 * codeListSize codes ≤
    encodeDigits (encodeCodeListWithRest codes []) := by
  cases codes with
  | nil =>
      simp [codeListSize, encodeCodeListWithRest, encodeDigits, digitCell]
  | cons head tail =>
      simp [codeListSize, encodeCodeListWithRest, encodeDigits, digitCell]
      have hTail := codeListSize_le_encodeClosed tail
      have hHead :=
        codeSize_base_le_encodeCodeWithRest
          head (codeListSize tail)
          (encodeCodeListWithRest tail [])
          hTail
      have hPos := codeSize_pos head
      omega

theorem codeListClosed_length_le_encode_plus_one
    (codes : List Code) :
    (encodeCodeListWithRest codes []).length ≤
    encodeDigits (encodeCodeListWithRest codes []) + 1 := by
  have hLen :
      (encodeCodeListWithRest codes []).length ≤
      2 * codeListSize codes + 1 := by
    simpa using codeListDigits_length_le_size codes []
  have hSize := two_codeListSize_le_encodeClosed codes
  omega

theorem lengthScannerEvalCheckWithFuel_codeList_complete_fixed_of_bound
    (codes : List Code)
    (hBound :
      (encodeCodeListWithRest codes []).length ≤
      encodeDigits (encodeCodeListWithRest codes []) + 1) :
    lengthScannerEvalCheckWithFuel
      (encodeDigits (encodeCodeListWithRest codes []) + 1)
      (encodeDigits (encodeCodeListWithRest codes []))
      codes.length = 1 := by
  let extra := encodeDigits (encodeCodeListWithRest codes []) + 1 -
    (encodeCodeListWithRest codes []).length
  have hFuel :
      encodeDigits (encodeCodeListWithRest codes []) + 1 =
      (encodeCodeListWithRest codes []).length + extra := by
    unfold extra
    omega
  rw [hFuel]
  exact lengthScannerEvalCheckWithFuel_codeList_complete_extra codes extra

theorem lengthScannerPRStyleEvalCheckWithFuel_codeList_complete_fixed_of_bound
    (codes : List Code)
    (hBound :
      (encodeCodeListWithRest codes []).length ≤
      encodeDigits (encodeCodeListWithRest codes []) + 1) :
    lengthScannerPRStyleEvalCheckWithFuel
      (encodeDigits (encodeCodeListWithRest codes []) + 1)
      (encodeDigits (encodeCodeListWithRest codes []))
      codes.length = 1 := by
  rw [lengthScannerPRStyleEvalCheckWithFuel_eq_tail]
  exact lengthScannerEvalCheckWithFuel_codeList_complete_fixed_of_bound
    codes hBound

theorem lengthScannerEvalCheckWithFuel_codeList_complete_fixed
    (codes : List Code) :
    lengthScannerEvalCheckWithFuel
      (encodeDigits (encodeCodeListWithRest codes []) + 1)
      (encodeDigits (encodeCodeListWithRest codes []))
      codes.length = 1 :=
  lengthScannerEvalCheckWithFuel_codeList_complete_fixed_of_bound
    codes
    (codeListClosed_length_le_encode_plus_one codes)

theorem lengthScannerPRStyleEvalCheckWithFuel_codeList_complete_fixed
    (codes : List Code) :
    lengthScannerPRStyleEvalCheckWithFuel
      (encodeDigits (encodeCodeListWithRest codes []) + 1)
      (encodeDigits (encodeCodeListWithRest codes []))
      codes.length = 1 :=
  lengthScannerPRStyleEvalCheckWithFuel_codeList_complete_fixed_of_bound
    codes
    (codeListClosed_length_le_encode_plus_one codes)

end LeanShadow.CodeListLengthNumericEvalMini
