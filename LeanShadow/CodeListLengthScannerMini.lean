import LeanShadow.CodeListLengthMini

namespace LeanShadow.CodeListLengthScannerMini

/-!
This file is the next mini-prototype after `CodeListLengthMini`.

`CodeListLengthMini` proves that the semantic parser/checker is correct.  Here
we model the missing Agda step more closely: define a checker candidate that
does not build `Code` trees.  It only skips encoded nats/codes and computes the
length of an encoded code-list.  Then we prove that this scanner checker agrees
with `CodeListLengthMini.codeListLengthCheck`.

This is still a Lean mini-prototype, not the Agda minimal-basis PRF itself.  The
important transferable lesson is that the PRF can target a scanner equation:

```text
scanner-checker(input,len) = semantic codeListLengthCheck(input,len)
```

rather than reconstructing full syntax values inside the PRF.
-/

open LeanShadow.CodeListLengthMini
open LeanShadow.CodeListLengthMini.Digit

mutual
  def skipNatFuel : Nat -> List Digit -> Option (List Digit)
    | 0, _ => none
    | Nat.succ _, [] => none
    | Nat.succ fuel, d2 :: rest => skipNatFuel fuel rest
    | Nat.succ _, d3 :: rest => some rest
    | Nat.succ _, _ :: _ => none

  def skipCodeFuel : Nat -> List Digit -> Option (List Digit)
    | 0, _ => none
    | Nat.succ _, [] => none
    | Nat.succ fuel, d0 :: rest => skipNatFuel fuel rest
    | Nat.succ fuel, d1 :: rest =>
        match skipNatFuel fuel rest with
        | some afterTag =>
            match codeListLengthFuel fuel afterTag with
            | some (_, finalRest) => some finalRest
            | none => none
        | none => none
    | Nat.succ _, _ :: _ => none

  def codeListLengthFuel : Nat -> List Digit -> Option (Nat × List Digit)
    | 0, _ => none
    | Nat.succ _, [] => none
    | Nat.succ _, d0 :: rest => some (0, rest)
    | Nat.succ fuel, d1 :: rest =>
        match skipCodeFuel fuel rest with
        | some afterHead =>
            match codeListLengthFuel fuel afterHead with
            | some (len, finalRest) => some (Nat.succ len, finalRest)
            | none => none
        | none => none
    | Nat.succ _, _ :: _ => none
end

def parseCodeListLengthDirect (input : List Digit) : Option Nat :=
  match codeListLengthFuel (input.length + 1) input with
  | some (len, []) => some len
  | _ => none

def codeListLengthScannerCheck (input : List Digit) (len : Nat) : Nat :=
  match parseCodeListLengthDirect input with
  | some parsedLen => if len = parsedLen then 1 else 0
  | none => 0

mutual
  theorem skipNatFuel_agrees :
      forall (fuel : Nat) (input : List Digit),
        skipNatFuel fuel input =
        match parseNatFuel fuel input with
        | some (_, rest) => some rest
        | none => none
    | 0, _ => rfl
    | Nat.succ fuel, [] => rfl
    | Nat.succ fuel, d0 :: rest => rfl
    | Nat.succ fuel, d1 :: rest => rfl
    | Nat.succ fuel, d2 :: rest => by
        unfold skipNatFuel parseNatFuel
        rw [skipNatFuel_agrees fuel rest]
        cases parseNatFuel fuel rest <;> rfl
    | Nat.succ fuel, d3 :: rest => rfl

  theorem skipCodeFuel_agrees :
      forall (fuel : Nat) (input : List Digit),
        skipCodeFuel fuel input =
        match parseCodeFuel fuel input with
        | some (_, rest) => some rest
        | none => none
    | 0, _ => rfl
    | Nat.succ fuel, [] => rfl
    | Nat.succ fuel, d0 :: rest => by
        unfold skipCodeFuel parseCodeFuel
        rw [skipNatFuel_agrees fuel rest]
        cases parseNatFuel fuel rest <;> rfl
    | Nat.succ fuel, d1 :: rest => by
        unfold skipCodeFuel parseCodeFuel
        rw [skipNatFuel_agrees fuel rest]
        cases hNat : parseNatFuel fuel rest with
        | none => rfl
        | some natPair =>
            cases natPair with
            | mk tag afterTag =>
                simp
                rw [codeListLengthFuel_agrees fuel afterTag]
                cases parseCodeListFuel fuel afterTag <;> rfl
    | Nat.succ fuel, d2 :: rest => rfl
    | Nat.succ fuel, d3 :: rest => rfl

  theorem codeListLengthFuel_agrees :
      forall (fuel : Nat) (input : List Digit),
        codeListLengthFuel fuel input =
        match parseCodeListFuel fuel input with
        | some (codes, rest) => some (codes.length, rest)
        | none => none
    | 0, _ => rfl
    | Nat.succ fuel, [] => rfl
    | Nat.succ fuel, d0 :: rest => rfl
    | Nat.succ fuel, d1 :: rest => by
        unfold codeListLengthFuel parseCodeListFuel
        rw [skipCodeFuel_agrees fuel rest]
        cases hCode : parseCodeFuel fuel rest with
        | none => rfl
        | some codePair =>
            cases codePair with
            | mk head afterHead =>
                simp
                rw [codeListLengthFuel_agrees fuel afterHead]
                cases parseCodeListFuel fuel afterHead <;> rfl
    | Nat.succ fuel, d2 :: rest => rfl
    | Nat.succ fuel, d3 :: rest => rfl
end

theorem parseCodeListLengthDirect_agrees (input : List Digit) :
    parseCodeListLengthDirect input =
    match parseCodeList input with
    | some codes => some codes.length
    | none => none := by
  unfold parseCodeListLengthDirect parseCodeList
  rw [codeListLengthFuel_agrees (input.length + 1) input]
  cases parseCodeListFuel (input.length + 1) input with
  | none => rfl
  | some pair =>
      cases pair with
      | mk codes rest =>
          cases rest <;> rfl

theorem codeListLengthScannerCheck_correct
    (input : List Digit) (len : Nat) :
    codeListLengthScannerCheck input len =
    codeListLengthCheck input len := by
  unfold codeListLengthScannerCheck codeListLengthCheck
  rw [parseCodeListLengthDirect_agrees input]
  cases parseCodeList input with
  | none => rfl
  | some codes =>
      by_cases h : len = codes.length <;> simp [h]

theorem codeListLengthScannerCheck_complete
    (codes : List Code) :
    codeListLengthScannerCheck
      (encodeCodeListWithRest codes [])
      codes.length = 1 := by
  rw [codeListLengthScannerCheck_correct]
  exact codeListLengthCheck_complete codes

theorem codeListLengthScannerCheck_sound
    {input : List Digit} {len : Nat} :
    codeListLengthScannerCheck input len = 1 ->
    CodeListLengthNat input len := by
  intro h
  apply codeListLengthCheck_sound
  rwa [codeListLengthScannerCheck_correct] at h

theorem codeListLengthScannerCheck_nonzero_sound
    {input : List Digit} {len : Nat} :
    codeListLengthScannerCheck input len ≠ 0 ->
    CodeListLengthNat input len := by
  intro h
  apply codeListLengthCheck_nonzero_sound
  intro hZero
  apply h
  rwa [codeListLengthScannerCheck_correct]

end LeanShadow.CodeListLengthScannerMini
