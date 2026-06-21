import Init.Omega

namespace LeanShadow.CodeListLengthMini

/-!
A focused Lean mini-prototype for the current Agda bottleneck:

```text
concrete code-list-length-pr
CodeListLengthNonzeroSound
```

This is not a replacement for the Agda proof.  It is a small executable model
of the same proof shape:

* a self-delimiting base-4-ish digit stream;
* canonical `Code` and `List Code` encoders with rest;
* fuelled parsers, mirroring Agda's termination strategy;
* a length checker returning `0/1`;
* completeness, soundness, and nonzero-sound for the length relation.
-/

inductive Digit where
  | d0 | d1 | d2 | d3
deriving DecidableEq, Repr

inductive Code where
  | atom : Nat -> Code
  | node : Nat -> List Code -> Code
deriving Repr

open Digit
open Code

def encodeNatWithRest : Nat -> List Digit -> List Digit
  | 0, rest => d3 :: rest
  | Nat.succ n, rest => d2 :: encodeNatWithRest n rest

mutual
  def encodeCodeWithRest : Code -> List Digit -> List Digit
    | atom n, rest => d0 :: encodeNatWithRest n rest
    | node tag children, rest =>
        d1 :: encodeNatWithRest tag (encodeCodeListWithRest children rest)

  def encodeCodeListWithRest : List Code -> List Digit -> List Digit
    | [], rest => d0 :: rest
    | head :: tail, rest =>
        d1 :: encodeCodeWithRest head (encodeCodeListWithRest tail rest)
end

mutual
  def parseNatFuel : Nat -> List Digit -> Option (Nat × List Digit)
    | 0, _ => none
    | Nat.succ _, [] => none
    | Nat.succ fuel, d2 :: rest =>
        match parseNatFuel fuel rest with
        | some (n, finalRest) => some (Nat.succ n, finalRest)
        | none => none
    | Nat.succ _, d3 :: rest => some (0, rest)
    | Nat.succ _, _ :: _ => none

  def parseCodeFuel : Nat -> List Digit -> Option (Code × List Digit)
    | 0, _ => none
    | Nat.succ _, [] => none
    | Nat.succ fuel, d0 :: rest =>
        match parseNatFuel fuel rest with
        | some (n, finalRest) => some (atom n, finalRest)
        | none => none
    | Nat.succ fuel, d1 :: rest =>
        match parseNatFuel fuel rest with
        | some (tag, afterTag) =>
            match parseCodeListFuel fuel afterTag with
            | some (children, finalRest) => some (node tag children, finalRest)
            | none => none
        | none => none
    | Nat.succ _, _ :: _ => none

  def parseCodeListFuel : Nat -> List Digit -> Option (List Code × List Digit)
    | 0, _ => none
    | Nat.succ _, [] => none
    | Nat.succ _, d0 :: rest => some ([], rest)
    | Nat.succ fuel, d1 :: rest =>
        match parseCodeFuel fuel rest with
        | some (head, afterHead) =>
            match parseCodeListFuel fuel afterHead with
            | some (tail, finalRest) => some (head :: tail, finalRest)
            | none => none
        | none => none
    | Nat.succ _, _ :: _ => none
end

def parseCodeList (input : List Digit) : Option (List Code) :=
  match parseCodeListFuel (input.length + 1) input with
  | some (codes, []) => some codes
  | _ => none

def codeListLengthCheck (input : List Digit) (len : Nat) : Nat :=
  match parseCodeList input with
  | some codes => if len = codes.length then 1 else 0
  | none => 0

def CodeListLengthNat (input : List Digit) (len : Nat) : Prop :=
  exists codes,
    input = encodeCodeListWithRest codes [] /\
    len = codes.length

theorem encodeNatWithRest_length (n : Nat) (rest : List Digit) :
    (encodeNatWithRest n rest).length =
    (encodeNatWithRest n []).length + rest.length := by
  induction n generalizing rest with
  | zero =>
      simp [encodeNatWithRest]
      omega
  | succ n ih =>
      simp [encodeNatWithRest]
      rw [ih rest]
      omega

mutual
  theorem encodeCodeWithRest_length (c : Code) (rest : List Digit) :
      (encodeCodeWithRest c rest).length =
      (encodeCodeWithRest c []).length + rest.length := by
    cases c with
    | atom n =>
        simp [encodeCodeWithRest]
        rw [encodeNatWithRest_length n rest]
        omega
    | node tag children =>
        simp [encodeCodeWithRest]
        rw [encodeNatWithRest_length tag (encodeCodeListWithRest children rest)]
        rw [encodeNatWithRest_length tag (encodeCodeListWithRest children [])]
        rw [encodeCodeListWithRest_length children rest]
        omega

  theorem encodeCodeListWithRest_length
      (codes : List Code) (rest : List Digit) :
      (encodeCodeListWithRest codes rest).length =
      (encodeCodeListWithRest codes []).length + rest.length := by
    cases codes with
    | nil =>
        simp [encodeCodeListWithRest]
        omega
    | cons head tail =>
        simp [encodeCodeListWithRest]
        rw [encodeCodeWithRest_length head (encodeCodeListWithRest tail rest)]
        rw [encodeCodeWithRest_length head (encodeCodeListWithRest tail [])]
        rw [encodeCodeListWithRest_length tail rest]
        omega
end

theorem parseNatFuel_complete_of_lt
    (n : Nat) (rest : List Digit) {fuel : Nat}
    (hFuel : (encodeNatWithRest n rest).length < fuel) :
    parseNatFuel fuel (encodeNatWithRest n rest) =
    some (n, rest) := by
  induction n generalizing rest fuel with
  | zero =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp [encodeNatWithRest, parseNatFuel]
  | succ n ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp [encodeNatWithRest, parseNatFuel]
          have hTail : (encodeNatWithRest n rest).length < fuel := by
            simp [encodeNatWithRest] at hFuel
            omega
          rw [ih rest hTail]

mutual
  theorem parseCodeFuel_complete_of_lt
      (c : Code) (rest : List Digit) {fuel : Nat}
      (hFuel : (encodeCodeWithRest c rest).length < fuel) :
      parseCodeFuel fuel
        (encodeCodeWithRest c rest) =
      some (c, rest) := by
    cases fuel with
    | zero => omega
    | succ fuel =>
        cases c with
        | atom n =>
            simp [encodeCodeWithRest, parseCodeFuel]
            have hNat : (encodeNatWithRest n rest).length < fuel := by
              simp [encodeCodeWithRest] at hFuel
              omega
            rw [parseNatFuel_complete_of_lt n rest hNat]
        | node tag children =>
            simp [encodeCodeWithRest, parseCodeFuel]
            have hNat :
                (encodeNatWithRest tag
                  (encodeCodeListWithRest children rest)).length < fuel := by
              simp [encodeCodeWithRest] at hFuel
              omega
            rw [parseNatFuel_complete_of_lt tag
              (encodeCodeListWithRest children rest) hNat]
            simp
            have hList :
                (encodeCodeListWithRest children rest).length < fuel := by
              have hLen :=
                encodeNatWithRest_length
                  tag
                  (encodeCodeListWithRest children rest)
              omega
            rw [parseCodeListFuel_complete_of_lt children rest hList]

  theorem parseCodeListFuel_complete_of_lt
      (codes : List Code) (rest : List Digit) {fuel : Nat}
      (hFuel : (encodeCodeListWithRest codes rest).length < fuel) :
      parseCodeListFuel fuel
        (encodeCodeListWithRest codes rest) =
      some (codes, rest) := by
    cases fuel with
    | zero => omega
    | succ fuel =>
        cases codes with
        | nil =>
            simp [encodeCodeListWithRest, parseCodeListFuel]
        | cons head tail =>
            simp [encodeCodeListWithRest, parseCodeListFuel]
            have hHead :
                (encodeCodeWithRest head
                  (encodeCodeListWithRest tail rest)).length < fuel := by
              simp [encodeCodeListWithRest] at hFuel
              omega
            rw [parseCodeFuel_complete_of_lt head
              (encodeCodeListWithRest tail rest) hHead]
            simp
            have hTail :
                (encodeCodeListWithRest tail rest).length < fuel := by
              have hLen :=
                encodeCodeWithRest_length
                  head
                  (encodeCodeListWithRest tail rest)
              omega
            rw [parseCodeListFuel_complete_of_lt tail rest hTail]
end

theorem parseCodeList_complete (codes : List Code) :
    parseCodeList (encodeCodeListWithRest codes []) = some codes := by
  unfold parseCodeList
  have hFuel :
      (encodeCodeListWithRest codes []).length <
      (encodeCodeListWithRest codes []).length + 1 := by
    omega
  rw [parseCodeListFuel_complete_of_lt codes [] hFuel]

theorem codeListLengthCheck_complete (codes : List Code) :
    codeListLengthCheck
      (encodeCodeListWithRest codes [])
      codes.length = 1 := by
  unfold codeListLengthCheck
  rw [parseCodeList_complete codes]
  simp

theorem parseNatFuel_sound :
    forall {fuel input n rest},
      parseNatFuel fuel input = some (n, rest) ->
      input = encodeNatWithRest n rest
  | 0, _, _, _, h => by contradiction
  | Nat.succ fuel, [], _, _, h => by contradiction
  | Nat.succ fuel, d0 :: tail, _, _, h => by
      simp [parseNatFuel] at h
  | Nat.succ fuel, d1 :: tail, _, _, h => by
      simp [parseNatFuel] at h
  | Nat.succ fuel, d2 :: tail, n, rest, h => by
      unfold parseNatFuel at h
      cases hTail : parseNatFuel fuel tail with
      | none =>
          simp [hTail] at h
      | some pair =>
          cases pair with
          | mk parsed tailRest =>
              simp [hTail] at h
              rcases h with ⟨hn, hrest⟩
              have ih :=
                parseNatFuel_sound
                  (fuel := fuel)
                  (input := tail)
                  (n := parsed)
                  (rest := tailRest)
                  hTail
              cases hn
              cases hrest
              simp [encodeNatWithRest, ih]
  | Nat.succ fuel, d3 :: tail, n, rest, h => by
      simp [parseNatFuel] at h
      rcases h with ⟨hn, hrest⟩
      cases hn
      cases hrest
      rfl

mutual
  theorem parseCodeFuel_sound :
      forall {fuel input c rest},
        parseCodeFuel fuel input = some (c, rest) ->
        input = encodeCodeWithRest c rest
    | 0, _, _, _, h => by contradiction
    | Nat.succ fuel, [], _, _, h => by contradiction
    | Nat.succ fuel, d0 :: tail, c, rest, h => by
        unfold parseCodeFuel at h
        cases hNat : parseNatFuel fuel tail with
        | none =>
            simp [hNat] at h
        | some pair =>
            cases pair with
            | mk n finalRest =>
                simp [hNat] at h
                rcases h with ⟨hc, hrest⟩
                have natSound :=
                  parseNatFuel_sound
                    (fuel := fuel)
                    (input := tail)
                    (n := n)
                    (rest := finalRest)
                    hNat
                cases hc
                cases hrest
                simp [encodeCodeWithRest, natSound]
    | Nat.succ fuel, d1 :: tail, c, rest, h => by
        unfold parseCodeFuel at h
        cases hNat : parseNatFuel fuel tail with
        | none =>
            simp [hNat] at h
        | some tagPair =>
            cases tagPair with
            | mk tag afterTag =>
                cases hList : parseCodeListFuel fuel afterTag with
                | none =>
                    simp [hNat, hList] at h
                | some listPair =>
                    cases listPair with
                    | mk children finalRest =>
                        simp [hNat, hList] at h
                        rcases h with ⟨hc, hrest⟩
                        have natSound :=
                          parseNatFuel_sound
                            (fuel := fuel)
                            (input := tail)
                            (n := tag)
                            (rest := afterTag)
                            hNat
                        have listSound :=
                          parseCodeListFuel_sound
                            (fuel := fuel)
                            (input := afterTag)
                            (codes := children)
                            (rest := finalRest)
                            hList
                        cases hc
                        cases hrest
                        simp [encodeCodeWithRest, natSound, listSound]
    | Nat.succ fuel, d2 :: tail, _, _, h => by
        simp [parseCodeFuel] at h
    | Nat.succ fuel, d3 :: tail, _, _, h => by
        simp [parseCodeFuel] at h

  theorem parseCodeListFuel_sound :
      forall {fuel input codes rest},
        parseCodeListFuel fuel input = some (codes, rest) ->
        input = encodeCodeListWithRest codes rest
    | 0, _, _, _, h => by contradiction
    | Nat.succ fuel, [], _, _, h => by contradiction
    | Nat.succ fuel, d0 :: tail, codes, rest, h => by
        simp [parseCodeListFuel] at h
        rcases h with ⟨hcodes, hrest⟩
        cases hcodes
        cases hrest
        rfl
    | Nat.succ fuel, d1 :: tail, codes, rest, h => by
        unfold parseCodeListFuel at h
        cases hCode : parseCodeFuel fuel tail with
        | none =>
            simp [hCode] at h
        | some codePair =>
            cases codePair with
            | mk head afterHead =>
                cases hList : parseCodeListFuel fuel afterHead with
                | none =>
                    simp [hCode, hList] at h
                | some listPair =>
                    cases listPair with
                    | mk tailCodes finalRest =>
                        simp [hCode, hList] at h
                        rcases h with ⟨hcodes, hrest⟩
                        have codeSound :=
                          parseCodeFuel_sound
                            (fuel := fuel)
                            (input := tail)
                            (c := head)
                            (rest := afterHead)
                            hCode
                        have listSound :=
                          parseCodeListFuel_sound
                            (fuel := fuel)
                            (input := afterHead)
                            (codes := tailCodes)
                            (rest := finalRest)
                            hList
                        cases hcodes
                        cases hrest
                        simp [encodeCodeListWithRest, codeSound, listSound]
    | Nat.succ fuel, d2 :: tail, _, _, h => by
        simp [parseCodeListFuel] at h
    | Nat.succ fuel, d3 :: tail, _, _, h => by
        simp [parseCodeListFuel] at h
end

theorem parseCodeList_sound
    {input : List Digit} {codes : List Code} :
    parseCodeList input = some codes ->
    input = encodeCodeListWithRest codes [] := by
  intro h
  unfold parseCodeList at h
  cases hParse : parseCodeListFuel (input.length + 1) input with
  | none =>
      simp [hParse] at h
  | some pair =>
      cases pair with
      | mk parsed rest =>
          cases rest with
          | nil =>
              simp [hParse] at h
              have parsedSound :=
                parseCodeListFuel_sound
                  (fuel := input.length + 1)
                  (input := input)
                  (rest := [])
                  hParse
              simpa [h] using parsedSound
          | cons d ds =>
              simp [hParse] at h

theorem codeListLengthCheck_sound
    {input : List Digit} {len : Nat} :
    codeListLengthCheck input len = 1 ->
    CodeListLengthNat input len := by
  intro h
  unfold codeListLengthCheck at h
  cases hParse : parseCodeList input with
  | none =>
      simp [hParse] at h
  | some codes =>
      by_cases hLen : len = codes.length
      · refine ⟨codes, ?_, hLen⟩
        exact parseCodeList_sound hParse
      · simp [hParse, hLen] at h

theorem codeListLengthCheck_nonzero_sound
    {input : List Digit} {len : Nat} :
    codeListLengthCheck input len ≠ 0 ->
    CodeListLengthNat input len := by
  intro h
  unfold codeListLengthCheck at h
  cases hParse : parseCodeList input with
  | none =>
      simp [hParse] at h
  | some codes =>
      by_cases hLen : len = codes.length
      · refine ⟨codes, ?_, hLen⟩
        exact parseCodeList_sound hParse
      · simp [hParse, hLen] at h

def sampleCodeList : List Code :=
  [atom 2, node 5 [atom 0], atom 1]

example :
    codeListLengthCheck
      (encodeCodeListWithRest sampleCodeList [])
      3 = 1 := by
  native_decide

example :
    CodeListLengthNat
      (encodeCodeListWithRest sampleCodeList [])
      3 :=
  codeListLengthCheck_sound (by native_decide)

end LeanShadow.CodeListLengthMini
