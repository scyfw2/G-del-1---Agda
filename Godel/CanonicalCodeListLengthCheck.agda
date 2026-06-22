{-# OPTIONS --safe #-}

module Godel.CanonicalCodeListLengthCheck where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.DecidableCoding using (_==ℕ_; ==ℕ-refl; ==ℕ-sound)
open import Godel.CanonicalCoding using (inspect; [_])
open import Godel.CanonicalCodeParserTargets
  using
    ( args₂
    ; CodeListLengthNat
    ; CanonicalCodeParserPR
    ; codeListLength
    )
open import Godel.CanonicalCodeParserSemantics
  using
    ( parseCodeListLength
    ; parseCodeListLength-canonical
    ; parseCodeListLength-sound
    )
open import Godel.CanonicalCodeNodeParserFromListLength
  using (CodeListLengthNonzeroSound)
open import Godel.ProofRule37SearchCorrectness
  using (NonzeroNat)

-- Executable semantic checker for the code-list-length relation.
--
-- This is the Agda counterpart of LeanShadow/CodeListLengthMini.lean.  It is
-- not yet the final minimal-basis PRF parser; instead it fixes the exact
-- semantic target that the future PRF must compute.  Once a concrete PRF is
-- proved equal to this checker, completeness, soundness, and nonzero-sound
-- follow without re-opening the canonical parser proof.

codeListLengthCheck : ℕ → ℕ → ℕ
codeListLengthCheck list-code len
  with parseCodeListLength list-code
... | just parsed-len with parsed-len ==ℕ len
... | true = suc zero
... | false = zero
codeListLengthCheck list-code len | nothing = zero

codeListLengthCheck-complete :
  {list-code len : ℕ} →
  CodeListLengthNat list-code len →
  codeListLengthCheck list-code len ≡ suc zero
codeListLengthCheck-complete
    {list-code}
    {len}
    (codes ,Σ (list-eq ,× len-eq))
  rewrite list-eq
        | len-eq
        | parseCodeListLength-canonical codes
        | ==ℕ-refl (codeListLength codes) =
  refl

codeListLengthCheck-sound :
  {list-code len : ℕ} →
  codeListLengthCheck list-code len ≡ suc zero →
  CodeListLengthNat list-code len
codeListLengthCheck-sound {list-code} {len} check-eq
  with parseCodeListLength list-code
     | inspect parseCodeListLength list-code
... | just parsed-len | [ parse-eq ]
  with parsed-len ==ℕ len | inspect (_==ℕ_ parsed-len) len
... | true | [ len-eq ] =
  subst
    (CodeListLengthNat list-code)
    (==ℕ-sound parsed-len len len-eq)
    (parseCodeListLength-sound list-code parsed-len parse-eq)
... | false | [ len-eq ] with check-eq
... | ()
codeListLengthCheck-sound {list-code} {len} ()
  | nothing | [ parse-eq ]

codeListLengthCheck-nonzero-sound :
  {list-code len : ℕ} →
  NonzeroNat (codeListLengthCheck list-code len) →
  CodeListLengthNat list-code len
codeListLengthCheck-nonzero-sound {list-code} {len} nonzero
  with parseCodeListLength list-code
     | inspect parseCodeListLength list-code
... | just parsed-len | [ parse-eq ]
  with parsed-len ==ℕ len | inspect (_==ℕ_ parsed-len) len
... | true | [ len-eq ] =
  subst
    (CodeListLengthNat list-code)
    (==ℕ-sound parsed-len len len-eq)
    (parseCodeListLength-sound list-code parsed-len parse-eq)
... | false | [ len-eq ] with nonzero
... | k ,Σ ()
codeListLengthCheck-nonzero-sound {list-code} {len} nonzero
  | nothing | [ parse-eq ] with nonzero
... | k ,Σ ()

-- A narrow obligation for the future concrete PRF implementation.
-- The final task is to build a minimal-basis PRF whose evaluator agrees with
-- codeListLengthCheck.  This record lets downstream adapters use that one
-- theorem without depending on the implementation details of the parser PRF.

record CodeListLengthPRCandidate : Set₁ where
  field
    code-list-length-pr :
      PRRel (suc (suc zero))

    code-list-length-correct :
      (list-code len : ℕ) →
      evalPRF (PRRel.characteristic code-list-length-pr)
        (args₂ list-code len)
      ≡ codeListLengthCheck list-code len

codeListLengthPRCandidate-complete :
  (Candidate : CodeListLengthPRCandidate) →
  {list-code len : ℕ} →
  CodeListLengthNat list-code len →
  PRRel-holds
    (CodeListLengthPRCandidate.code-list-length-pr Candidate)
    (args₂ list-code len)
codeListLengthPRCandidate-complete Candidate {list-code} {len} length-nat
  rewrite CodeListLengthPRCandidate.code-list-length-correct
            Candidate
            list-code
            len =
  codeListLengthCheck-complete length-nat

codeListLengthPRCandidate-sound :
  (Candidate : CodeListLengthPRCandidate) →
  {list-code len : ℕ} →
  PRRel-holds
    (CodeListLengthPRCandidate.code-list-length-pr Candidate)
    (args₂ list-code len) →
  CodeListLengthNat list-code len
codeListLengthPRCandidate-sound Candidate {list-code} {len} holds =
  codeListLengthCheck-sound
    (trans
      (sym
        (CodeListLengthPRCandidate.code-list-length-correct
          Candidate
          list-code
          len))
      holds)

codeListLengthPRCandidate-nonzero-sound :
  (Candidate : CodeListLengthPRCandidate) →
  {list-code len : ℕ} →
  NonzeroNat
    (evalPRF
      (PRRel.characteristic
        (CodeListLengthPRCandidate.code-list-length-pr Candidate))
      (args₂ list-code len)) →
  CodeListLengthNat list-code len
codeListLengthPRCandidate-nonzero-sound
    Candidate
    {list-code}
    {len}
    (k ,Σ nonzero-eq) =
  codeListLengthCheck-nonzero-sound
    {list-code}
    {len}
    (k ,Σ
      trans
        (sym
          (CodeListLengthPRCandidate.code-list-length-correct
            Candidate
            list-code
            len))
        nonzero-eq)

ParserCodeListLengthCheckCorrect :
  CanonicalCodeParserPR → Set
ParserCodeListLengthCheckCorrect Parser =
  (list-code len : ℕ) →
  evalPRF
    (PRRel.characteristic
      (CanonicalCodeParserPR.code-list-length-pr Parser))
    (args₂ list-code len)
  ≡ codeListLengthCheck list-code len

codeListLengthNonzeroSound-from-check :
  (Parser : CanonicalCodeParserPR) →
  ParserCodeListLengthCheckCorrect Parser →
  CodeListLengthNonzeroSound Parser
codeListLengthNonzeroSound-from-check Parser correct {list-code} {len}
    (k ,Σ nonzero-eq) =
  codeListLengthCheck-nonzero-sound
    {list-code}
    {len}
    (k ,Σ
      trans
        (sym (correct list-code len))
        nonzero-eq)
