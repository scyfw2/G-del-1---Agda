{-# OPTIONS --safe #-}

module Godel.CanonicalCodeListLengthScanner where

open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Bool using (true; false)
open import Godel.Core
open import Godel.PrimitiveRecursive using (PRRel; evalPRF)
open import Godel.CanonicalCoding
  using
    ( Code
    ; Digit
    ; d0
    ; d1
    ; d2
    ; d3
    ; digitRest
    ; undigit
    ; decodeNatWithRest
    ; decodeCodeWithRest
    ; decodeCodeListWithRest
    )
open import Godel.CanonicalCodeParserTargets
  using (args₂; codeListLength)
open import Godel.CanonicalCodeListLengthCheck
  using
    ( codeListLengthCheck
    ; CodeListLengthPRCandidate
    )
open import Godel.CanonicalCodeParserSemantics
  using (parseCodeListLength)
open import Godel.DecidableCoding using (_==ℕ_)

-- Scanner version of the code-list-length parser.
--
-- The full semantic checker in CanonicalCodeListLengthCheck uses the existing
-- decoder, which builds a `List Code`.  This module follows the Lean scanner
-- prototype: skip encoded code values and compute the list length directly.
-- The scanner is still meta-level Agda code, not the final minimal-basis PRF,
-- but the final PRF should be proved against this smaller scanner.

skipNatWithRestFuel : ℕ → ℕ → Maybe ℕ
skipNatWithRestFuel fuel input
  with decodeNatWithRest fuel input
... | just (n ,× rest) = just rest
... | nothing = nothing

skipCodeWithRestFuel : ℕ → ℕ → Maybe ℕ
scanCodeListLengthWithRestFuel : ℕ → ℕ → Maybe (ℕ × ℕ)

skipCodeWithRestFuel zero input = nothing
skipCodeWithRestFuel (suc fuel) input with undigit input
... | digitRest d0 rest = skipNatWithRestFuel fuel rest
... | digitRest d1 rest with skipNatWithRestFuel fuel rest
... | just after-tag
  with scanCodeListLengthWithRestFuel fuel after-tag
... | just (len ,× final-rest) = just final-rest
... | nothing = nothing
skipCodeWithRestFuel (suc fuel) input | digitRest d1 rest | nothing = nothing
skipCodeWithRestFuel (suc fuel) input | digitRest _ rest = nothing

scanCodeListLengthWithRestFuel zero input = nothing
scanCodeListLengthWithRestFuel (suc fuel) input with undigit input
... | digitRest d0 rest = just (zero ,× rest)
... | digitRest d1 rest with skipCodeWithRestFuel fuel rest
... | just after-head
  with scanCodeListLengthWithRestFuel fuel after-head
... | just (len ,× final-rest) = just (suc len ,× final-rest)
... | nothing = nothing
scanCodeListLengthWithRestFuel (suc fuel) input | digitRest d1 rest | nothing = nothing
scanCodeListLengthWithRestFuel (suc fuel) input | digitRest _ rest = nothing

natRest : Maybe (ℕ × ℕ) → Maybe ℕ
natRest (just (n ,× rest)) = just rest
natRest nothing = nothing

skipNatWithRestFuel-agrees :
  (fuel input : ℕ) →
  skipNatWithRestFuel fuel input ≡
  natRest (decodeNatWithRest fuel input)
skipNatWithRestFuel-agrees fuel input
  with decodeNatWithRest fuel input
... | just (n ,× rest) = refl
... | nothing = refl

codeRest : Maybe (Code × ℕ) → Maybe ℕ
codeRest (just (code ,× rest)) = just rest
codeRest nothing = nothing

codeListLengthRest :
  Maybe (List Code × ℕ) → Maybe (ℕ × ℕ)
codeListLengthRest (just (codes ,× rest)) =
  just (codeListLength codes ,× rest)
codeListLengthRest nothing = nothing

mutual
  skipCodeWithRestFuel-agrees :
    (fuel input : ℕ) →
    skipCodeWithRestFuel fuel input ≡
    codeRest (decodeCodeWithRest fuel input)
  skipCodeWithRestFuel-agrees zero input = refl
  skipCodeWithRestFuel-agrees (suc fuel) input
    with undigit input
  ... | digitRest d0 rest with decodeNatWithRest fuel rest
  ... | just (n ,× final-rest) = refl
  ... | nothing = refl
  skipCodeWithRestFuel-agrees (suc fuel) input
    | digitRest d1 rest
    with decodeNatWithRest fuel rest
  ... | just (tag ,× after-tag)
    rewrite scanCodeListLengthWithRestFuel-agrees fuel after-tag
    with decodeCodeListWithRest fuel after-tag
  ... | just (n ,× final-rest) = refl
  ... | nothing = refl
  skipCodeWithRestFuel-agrees (suc fuel) input
    | digitRest d1 rest
    | nothing = refl
  skipCodeWithRestFuel-agrees (suc fuel) input
    | digitRest d2 rest = refl
  skipCodeWithRestFuel-agrees (suc fuel) input
    | digitRest d3 rest = refl

  scanCodeListLengthWithRestFuel-agrees :
    (fuel input : ℕ) →
    scanCodeListLengthWithRestFuel fuel input ≡
    codeListLengthRest (decodeCodeListWithRest fuel input)
  scanCodeListLengthWithRestFuel-agrees zero input = refl
  scanCodeListLengthWithRestFuel-agrees (suc fuel) input
    with undigit input
  ... | digitRest d0 rest = refl
  ... | digitRest d1 rest
    with decodeCodeWithRest fuel rest | skipCodeWithRestFuel-agrees fuel rest
  ... | just (head ,× after-head)
    | skip-eq
    rewrite skip-eq
          | scanCodeListLengthWithRestFuel-agrees fuel after-head
    with decodeCodeListWithRest fuel after-head
  ... | just (tail ,× final-rest) = refl
  ... | nothing = refl
  scanCodeListLengthWithRestFuel-agrees (suc fuel) input
    | digitRest d1 rest
    | nothing
    | skip-eq rewrite skip-eq = refl
  scanCodeListLengthWithRestFuel-agrees (suc fuel) input
    | digitRest d2 rest = refl
  scanCodeListLengthWithRestFuel-agrees (suc fuel) input
    | digitRest d3 rest = refl

scanCodeListLength : ℕ → Maybe ℕ
scanCodeListLength input
  with scanCodeListLengthWithRestFuel (suc input) input
... | just (len ,× zero) = just len
... | just (len ,× suc rest) = nothing
... | nothing = nothing

scanCodeListLength-agrees :
  (input : ℕ) →
  scanCodeListLength input ≡ parseCodeListLength input
scanCodeListLength-agrees input
  rewrite scanCodeListLengthWithRestFuel-agrees (suc input) input
  with decodeCodeListWithRest (suc input) input
... | just (codes ,× zero) = refl
... | just (codes ,× suc rest) = refl
... | nothing = refl

codeListLengthScannerCheck : ℕ → ℕ → ℕ
codeListLengthScannerCheck list-code len
  with scanCodeListLength list-code
... | just parsed-len with parsed-len ==ℕ len
... | true = suc zero
... | false = zero
codeListLengthScannerCheck list-code len | nothing = zero

codeListLengthScannerCheck-correct :
  (list-code len : ℕ) →
  codeListLengthScannerCheck list-code len ≡
  codeListLengthCheck list-code len
codeListLengthScannerCheck-correct list-code len
  rewrite scanCodeListLength-agrees list-code
  with parseCodeListLength list-code
... | just parsed-len with parsed-len ==ℕ len
... | true = refl
... | false = refl
codeListLengthScannerCheck-correct list-code len
  | nothing = refl

record CodeListLengthScannerPRCandidate : Set₁ where
  field
    code-list-length-scanner-pr :
      PRRel (suc (suc zero))

    code-list-length-scanner-correct :
      (list-code len : ℕ) →
      evalPRF (PRRel.characteristic code-list-length-scanner-pr)
        (args₂ list-code len)
      ≡ codeListLengthScannerCheck list-code len

scannerCandidate->checkCandidate :
  CodeListLengthScannerPRCandidate →
  CodeListLengthPRCandidate
scannerCandidate->checkCandidate Candidate = record
  { code-list-length-pr =
      CodeListLengthScannerPRCandidate.code-list-length-scanner-pr Candidate
  ; code-list-length-correct =
      λ list-code len →
        trans
          (CodeListLengthScannerPRCandidate.code-list-length-scanner-correct
            Candidate
            list-code
            len)
          (codeListLengthScannerCheck-correct list-code len)
  }
