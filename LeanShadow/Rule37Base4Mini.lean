import LeanShadow.Rule37CanonicalMini
import Init.Omega

namespace LeanShadow.Rule37Base4Mini

/-!
A rule-37 mini-prototype that is closer to the Agda base-4 coding style.

The code is still intentionally smaller than the Agda canonical code, but it is
now a genuine base-4 digit stream:

* natural payload `n` is encoded as `n` copies of digit `2`, followed by `0`;
* an atom is digit `1` followed by the natural payload;
* a node is digit `3`, then a unary tag payload, then a two-atom child list.

For rule 37:

```text
node 37 [atom m, atom n]
```

becomes:

```text
3 :: natDigits 37 ++ atomDigits m ++ atomDigits n
```

This mirrors the Agda proof obligations more closely: parser correctness,
canonical equality, and witness bounds are proved from base-4 parser facts.
-/

abbrev Digit := Nat

def natDigits : Nat -> List Digit
  | 0 => [0]
  | Nat.succ n => 2 :: natDigits n

def atomDigits (n : Nat) : List Digit :=
  1 :: natDigits n

def rule37Digits (m n : Nat) : List Digit :=
  3 :: natDigits 37 ++ atomDigits m ++ atomDigits n

def encodeDigits : List Digit -> Nat
  | [] => 0
  | d :: ds => d + 4 * encodeDigits ds

def rule37Code (m n : Nat) : Nat :=
  encodeDigits (rule37Digits m n)

def parseNatPayload : List Digit -> Option (Nat × List Digit)
  | [] => none
  | 0 :: rest => some (0, rest)
  | 2 :: rest =>
      match parseNatPayload rest with
      | some (n, rest') => some (Nat.succ n, rest')
      | none => none
  | _ :: _ => none

def parseAtom : List Digit -> Option (Nat × List Digit)
  | 1 :: rest => parseNatPayload rest
  | _ => none

def parseRule37 : List Digit -> Option (Nat × Nat) :=
  fun ds =>
    match ds with
    | 3 :: rest =>
        match parseNatPayload rest with
        | some (tag, afterTag) =>
            if tag = 37 then
              match parseAtom afterTag with
              | some (m, afterM) =>
                  match parseAtom afterM with
                  | some (n, []) => some (m, n)
                  | _ => none
              | _ => none
            else
              none
        | _ => none
    | _ => none

theorem parseNatPayload_complete (n : Nat) (rest : List Digit) :
    parseNatPayload (natDigits n ++ rest) = some (n, rest) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change
        (match parseNatPayload (natDigits n ++ rest) with
         | some (k, rest') => some (Nat.succ k, rest')
         | none => none) = some (Nat.succ n, rest)
      rw [ih]

theorem parseAtom_complete (n : Nat) (rest : List Digit) :
    parseAtom (atomDigits n ++ rest) = some (n, rest) := by
  simp [atomDigits, parseAtom, parseNatPayload_complete n rest]

theorem parseRule37_complete (m n : Nat) :
    parseRule37 (rule37Digits m n) = some (m, n) := by
  unfold parseRule37 rule37Digits
  change
    (match parseNatPayload (natDigits 37 ++ atomDigits m ++ atomDigits n) with
     | some (tag, afterTag) =>
        if tag = 37 then
          match parseAtom afterTag with
          | some (m', afterM) =>
              match parseAtom afterM with
              | some (n', []) => some (m', n')
              | _ => none
          | _ => none
        else none
     | none => none) = some (m, n)
  have hPayload :
      parseNatPayload (natDigits 37 ++ atomDigits m ++ atomDigits n) =
      some (37, atomDigits m ++ atomDigits n) := by
    simpa [List.append_assoc]
      using parseNatPayload_complete 37 (atomDigits m ++ atomDigits n)
  rw [hPayload]
  simp
  rw [parseAtom_complete m (atomDigits n)]
  simp
  have hAtomN :
      parseAtom (atomDigits n) = some (n, []) := by
    simpa using parseAtom_complete n []
  rw [hAtomN]

theorem parseNatPayload_sound :
    forall {input rest : List Digit} {n : Nat},
      parseNatPayload input = some (n, rest) ->
      input = natDigits n ++ rest
  | [], _, _, h => by contradiction
  | 0 :: tail, rest, n, h => by
      simp [parseNatPayload] at h
      rcases h with ⟨hn, hrest⟩
      cases hn
      cases hrest
      rfl
  | 1 :: tail, rest, n, h => by
      simp [parseNatPayload] at h
  | 2 :: tail, rest, n, h => by
      unfold parseNatPayload at h
      cases hTail : parseNatPayload tail with
      | none =>
          simp [hTail] at h
      | some pair =>
          cases pair with
          | mk k tailRest =>
              simp [hTail] at h
              rcases h with ⟨hn, hrest⟩
              have ih :=
                parseNatPayload_sound
                  (input := tail)
                  (rest := tailRest)
                  (n := k)
                  hTail
              cases hn
              cases hrest
              simp [natDigits, ih]
  | 3 :: tail, rest, n, h => by
      simp [parseNatPayload] at h

theorem parseAtom_sound
    {input rest : List Digit} {n : Nat} :
    parseAtom input = some (n, rest) ->
    input = atomDigits n ++ rest := by
  intro h
  cases input with
  | nil =>
      simp [parseAtom] at h
  | cons d ds =>
      cases d with
      | zero => simp [parseAtom] at h
      | succ d1 =>
          cases d1 with
          | zero =>
              unfold parseAtom at h
              have natSound := parseNatPayload_sound h
              simp [atomDigits, natSound]
          | succ d2 =>
              cases d2 <;> simp [parseAtom] at h

theorem parseRule37_sound
    {input : List Digit} {m n : Nat} :
    parseRule37 input = some (m, n) ->
    input = rule37Digits m n := by
  intro h
  unfold parseRule37 at h
  cases input with
  | nil => simp at h
  | cons d rest =>
      cases d with
      | zero => simp at h
      | succ d1 =>
          cases d1 with
          | zero => simp at h
          | succ d2 =>
              cases d2 with
              | zero => simp at h
              | succ d3 =>
                  cases d3 with
                  | zero =>
                      cases hTag : parseNatPayload rest with
                      | none => simp [hTag] at h
                      | some tagPair =>
                          cases tagPair with
                          | mk tag afterTag =>
                              by_cases h37 : tag = 37
                              · cases hAtomM : parseAtom afterTag with
                                | none => simp [hTag, h37, hAtomM] at h
                                | some mPair =>
                                    cases mPair with
                                    | mk m' afterM =>
                                        cases hAtomN : parseAtom afterM with
                                        | none => simp [hTag, h37, hAtomM, hAtomN] at h
                                        | some nPair =>
                                            cases nPair with
                                            | mk n' afterN =>
                                                cases afterN with
                                                | nil =>
                                                    simp [hTag, h37, hAtomM, hAtomN] at h
                                                    rcases h with ⟨hm, hn⟩
                                                    have tagSound0 :=
                                                      parseNatPayload_sound
                                                        (input := rest)
                                                        (rest := afterTag)
                                                        (n := tag)
                                                        hTag
                                                    have atomMSound0 :=
                                                      parseAtom_sound
                                                        (input := afterTag)
                                                        (rest := afterM)
                                                        (n := m')
                                                        hAtomM
                                                    have atomNSound0 :=
                                                      parseAtom_sound
                                                        (input := afterM)
                                                        (rest := [])
                                                        (n := n')
                                                        hAtomN
                                                    cases h37
                                                    cases hm
                                                    cases hn
                                                    unfold rule37Digits
                                                    simp [tagSound0, atomMSound0, atomNSound0]
                                                | cons x xs =>
                                                    simp [hTag, h37, hAtomM, hAtomN] at h
                              · simp [hTag, h37] at h
                  | succ _ => simp at h

theorem rule37Code_eq_from_parser
    {input : List Digit} {m n : Nat} :
    parseRule37 input = some (m, n) ->
    encodeDigits input = rule37Code m n := by
  intro h
  rw [parseRule37_sound h]
  rfl

theorem natDigits_length (n : Nat) :
    (natDigits n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [natDigits, ih]

theorem length_atomDigits (n : Nat) :
    (atomDigits n).length = n + 2 := by
  simp [atomDigits, natDigits_length n]

theorem length_rule37Digits (m n : Nat) :
    (rule37Digits m n).length = 1 + 38 + (m + 2) + (n + 2) := by
  unfold rule37Digits
  simp [natDigits_length, length_atomDigits]
  omega

theorem m_bound_by_rule37_length (m n : Nat) :
    m <= (rule37Digits m n).length := by
  rw [length_rule37Digits]
  omega

theorem n_bound_by_rule37_length (m n : Nat) :
    n <= (rule37Digits m n).length := by
  rw [length_rule37Digits]
  omega

theorem witnessBound_from_base4_parser
    {input : List Digit} {m n : Nat} :
    parseRule37 input = some (m, n) ->
    m <= input.length /\ n <= input.length := by
  intro h
  have hInput := parseRule37_sound h
  constructor
  · rw [hInput]
    exact m_bound_by_rule37_length m n
  · rw [hInput]
    exact n_bound_by_rule37_length m n

end LeanShadow.Rule37Base4Mini
