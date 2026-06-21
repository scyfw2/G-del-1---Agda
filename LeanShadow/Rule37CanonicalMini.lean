import LeanShadow.Rule37Mini
import Init.Omega

namespace LeanShadow.Rule37CanonicalMini

/-!
A second rule-37 mini-prototype, focused on the three facts isolated by
`Rule37Mini`:

* canonical parser correctness;
* canonical proof-code equality from parsed node/list facts;
* witness bounds.

This uses a toy canonical code with an explicit inverse parser.  It is not the
Agda base-4 encoding, but the proof shape mirrors the Agda obligations.
-/

inductive Code where
  | atom : Nat -> Code
  | node : Nat -> List Code -> Code
deriving Repr

def encodeList : List Code -> Nat
  | [] => 0
  | Code.atom n :: cs => n + 1 + encodeList cs
  | Code.node tag _ :: cs => tag + 1 + encodeList cs

def encode : Code -> Nat
  | Code.atom n => n + 1
  | Code.node tag children => tag + 1 + encodeList children

def closedNumeralNeqCode (m n : Nat) : Code :=
  Code.node 37 [Code.atom m, Code.atom n]

def closedNumeralNeqNatCode (m n : Nat) : Nat :=
  encode (closedNumeralNeqCode m n)

def decodeToy (input : Nat) : Option Code :=
  match input with
  | 0 => none
  | Nat.succ n => some (Code.atom n)

def parseCode (input : Code) : Option Code :=
  some input

def parseNode37 (input : Code) : Option (List Code) :=
  match parseCode input with
  | some (Code.node 37 children) => some children
  | _ => none

def parseTwoAtomChildren : List Code -> Option (Nat × Nat)
  | [Code.atom m, Code.atom n] => some (m, n)
  | _ => none

def canonicalRule37Parser (input : Code) : Option (Nat × Nat) :=
  match parseNode37 input with
  | some children => parseTwoAtomChildren children
  | none => none

theorem parseCode_correct (c : Code) :
    parseCode c = some c := by
  rfl

theorem parseNode37_complete (m n : Nat) :
    parseNode37 (closedNumeralNeqCode m n) =
    some [Code.atom m, Code.atom n] := by
  rfl

theorem parseTwoAtomChildren_complete (m n : Nat) :
    parseTwoAtomChildren [Code.atom m, Code.atom n] = some (m, n) := by
  rfl

theorem canonicalRule37Parser_complete (m n : Nat) :
    canonicalRule37Parser (closedNumeralNeqCode m n) = some (m, n) := by
  rfl

theorem parseTwoAtomChildren_sound
    {children : List Code} {m n : Nat} :
    parseTwoAtomChildren children = some (m, n) ->
    children = [Code.atom m, Code.atom n] := by
  intro h
  cases children with
  | nil => simp [parseTwoAtomChildren] at h
  | cons c cs =>
      cases c with
      | node tag xs => simp [parseTwoAtomChildren] at h
      | atom m' =>
          cases cs with
          | nil => simp [parseTwoAtomChildren] at h
          | cons d ds =>
              cases d with
              | node tag ys => simp [parseTwoAtomChildren] at h
              | atom n' =>
                  cases ds with
                  | nil =>
                      simp [parseTwoAtomChildren] at h
                      rcases h with ⟨hm, hn⟩
                      cases hm
                      cases hn
                      rfl
                  | cons e es =>
                      simp [parseTwoAtomChildren] at h

theorem parseNode37_sound
    {input : Code} {children : List Code} :
    parseNode37 input = some children ->
    input = Code.node 37 children := by
  intro h
  cases input with
  | atom n =>
      simp [parseNode37, parseCode] at h
  | node tag xs =>
      by_cases hTag : tag = 37
      · subst tag
        simp [parseNode37, parseCode] at h
        cases h
        rfl
      · simp [parseNode37, parseCode, hTag] at h

theorem canonicalRule37Parser_sound
    {input : Code} {m n : Nat} :
    canonicalRule37Parser input = some (m, n) ->
    input = closedNumeralNeqCode m n := by
  intro h
  unfold canonicalRule37Parser at h
  cases hNode : parseNode37 input with
  | none =>
      simp [hNode] at h
  | some children =>
      have hChildren : parseTwoAtomChildren children = some (m, n) := by
        simpa [hNode] using h
      have hNodeEq : input = Code.node 37 children :=
        parseNode37_sound hNode
      have hChildrenEq : children = [Code.atom m, Code.atom n] :=
        parseTwoAtomChildren_sound hChildren
      rw [hNodeEq, hChildrenEq]
      rfl

def CanonicalNodeChildrenNat (input : Code) (m n : Nat) : Prop :=
  canonicalRule37Parser input = some (m, n)

theorem canonicalNodeChildren_to_closedCode
    {input : Code} {m n : Nat} :
    CanonicalNodeChildrenNat input m n ->
    input = closedNumeralNeqCode m n :=
  canonicalRule37Parser_sound

theorem canonicalNodeChildren_natCode_eq
    {input : Code} {m n : Nat} :
    CanonicalNodeChildrenNat input m n ->
    encode input = closedNumeralNeqNatCode m n := by
  intro h
  rw [canonicalNodeChildren_to_closedCode h]
  rfl

theorem atom_lt_closedCode_left (m n : Nat) :
    m <= closedNumeralNeqNatCode m n := by
  simp [closedNumeralNeqNatCode, closedNumeralNeqCode, encode, encodeList]
  omega

theorem atom_lt_closedCode_right (m n : Nat) :
    n <= closedNumeralNeqNatCode m n := by
  simp [closedNumeralNeqNatCode, closedNumeralNeqCode, encode, encodeList]
  omega

theorem witnessBound_from_canonical_parser
    {input : Code} {m n : Nat} :
    CanonicalNodeChildrenNat input m n ->
    m <= encode input /\ n <= encode input := by
  intro h
  have hCode : encode input = closedNumeralNeqNatCode m n :=
    canonicalNodeChildren_natCode_eq h
  constructor
  · rw [hCode]
    exact atom_lt_closedCode_left m n
  · rw [hCode]
    exact atom_lt_closedCode_right m n

end LeanShadow.Rule37CanonicalMini
