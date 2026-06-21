{-# OPTIONS --safe #-}

module Godel.CanonicalCodeRawAtomListPR where

open import Agda.Builtin.List using (List) renaming (_∷_ to _∷ˡ_)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.PRBooleanHelpers using (andF; eqNatF; fin0; fin1; fin2)
open import Godel.PRArithmeticSemantics
  using (mulNat; eqNatNat; andF-correct; eqNatF-correct)
open import Godel.PRBooleanSoundness using (and4-output-sound)
open import Godel.PRDigitCoding using (div4F)
open import Godel.PRDigitSemantics
  using (div4Nat; div4F-correct; div4Nat-appendDigit; mod4Nat-appendDigit)
open import Godel.PRRepresentabilityFinal
  using (PARepresentsRelation; prrel-represented)
open import Godel.CanonicalCoding
  using
    ( Code
    ; atom
    ; encodeCode
    ; encodeCodeWithRest
    ; encodeCodeListWithRest
    ; encodeNatWithRest
    ; appendDigit
    ; d0
    ; d1
    )
open import Godel.CanonicalCodePR
  using
    ( AtomHeadNat
    ; CodeListConsHeadNat
    ; isAtomCodeF
    ; codeListConsF
    ; atomPayloadF
    ; atomPayloadF-correct-to-prefix
    ; atomCodeF
    ; atomCodeF-canonical-correct
    ; prefixNatRestF
    ; prefixNatRestF-correct
    ; prefixNatValueNat-encodeNatWithRest
    ; prefixNatRestNat
    ; prefixNatRestNat-encodeNatWithRest
    ; codeListConsF-complete-head
    ; codeListConsF-canonical-cons-complete
    ; codeListConsF-sound-head
    ; isAtomCodeF-complete-head
    ; isAtomCodeF-sound-head
    ; eqNatNat-refl-code
    ; eqNatNat-sound-code
    )
open import Godel.CanonicalCodeParserTargets using (args₃)

-- Atom-specific payload parser for canonical code lists.
--
-- A general code-list head parser must skip an arbitrary self-delimiting Code.
-- This module implements the important first concrete payload branch: the
-- list is cons and the head code is an atom.  Rule 37 uses atom payloads, so
-- this branch is directly useful for proof-rule parsing while the fully
-- general list parser is still being rebuilt.

atomRestF : PRF (suc zero)
atomRestF =
  compF prefixNatRestF (div4F ∷ [])

atomHeadCodeFromListF : PRF (suc zero)
atomHeadCodeFromListF =
  compF atomCodeF
    (compF atomPayloadF
      (compF div4F (projF fin0 ∷ []) ∷ []) ∷ [])

atomTailFromListF : PRF (suc zero)
atomTailFromListF =
  compF atomRestF
    (compF div4F (projF fin0 ∷ []) ∷ [])

rawAtomListHeadTailF : PRF (suc (suc (suc zero)))
rawAtomListHeadTailF =
  compF andF
    ( compF codeListConsF (projF fin0 ∷ []) ∷
      compF andF
        ( compF isAtomCodeF
          (compF div4F (projF fin0 ∷ []) ∷ []) ∷
          compF andF
          ( compF eqNatF
            ( compF atomHeadCodeFromListF (projF fin0 ∷ []) ∷
              projF fin1 ∷ []) ∷
            compF eqNatF
            ( compF atomTailFromListF (projF fin0 ∷ []) ∷
              projF fin2 ∷ []) ∷ []) ∷ []) ∷ [])

rawAtomListHeadTailPR : PRRel (suc (suc (suc zero)))
rawAtomListHeadTailPR =
  rel rawAtomListHeadTailF

RawAtomListHeadTailNat : ℕ → ℕ → ℕ → Set
RawAtomListHeadTailNat list-code head-code tail-code =
  CodeListConsHeadNat list-code ×
  (AtomHeadNat (evalPRF div4F (list-code ∷ [])) ×
   ((head-code ≡ evalPRF atomHeadCodeFromListF (list-code ∷ [])) ×
    (tail-code ≡ evalPRF atomTailFromListF (list-code ∷ []))))

atomRestF-correct-to-prefix :
  (input : ℕ) →
  evalPRF atomRestF (input ∷ []) ≡
  prefixNatRestNat (div4Nat input)
atomRestF-correct-to-prefix input
  rewrite div4F-correct input
        | prefixNatRestF-correct (div4Nat input) =
  refl

atomPayloadF-withRest-correct :
  (n rest : ℕ) →
  evalPRF atomPayloadF (encodeCodeWithRest (atom n) rest ∷ []) ≡ n
atomPayloadF-withRest-correct n rest
  rewrite atomPayloadF-correct-to-prefix (encodeCodeWithRest (atom n) rest)
        | div4Nat-appendDigit d0 (encodeNatWithRest n rest)
        | prefixNatValueNat-encodeNatWithRest n rest =
  refl

atomRestF-withRest-correct :
  (n rest : ℕ) →
  evalPRF atomRestF (encodeCodeWithRest (atom n) rest ∷ []) ≡ rest
atomRestF-withRest-correct n rest
  rewrite atomRestF-correct-to-prefix (encodeCodeWithRest (atom n) rest)
        | div4Nat-appendDigit d0 (encodeNatWithRest n rest)
        | prefixNatRestNat-encodeNatWithRest n rest =
  refl

atomHeadCodeFromListF-canonical-correct :
  (n : ℕ) → (tail : List Code) →
  evalPRF
    atomHeadCodeFromListF
    (encodeCodeListWithRest (atom n ∷ˡ tail) zero ∷ [])
  ≡ encodeCode (atom n)
atomHeadCodeFromListF-canonical-correct n tail
  rewrite div4F-correct (encodeCodeListWithRest (atom n ∷ˡ tail) zero)
        | div4Nat-appendDigit
            d1
            (encodeCodeWithRest
              (atom n)
              (encodeCodeListWithRest tail zero))
        | atomPayloadF-withRest-correct
            n
            (encodeCodeListWithRest tail zero)
        | atomCodeF-canonical-correct n =
  refl

atomTailFromListF-canonical-correct :
  (n : ℕ) → (tail : List Code) →
  evalPRF
    atomTailFromListF
    (encodeCodeListWithRest (atom n ∷ˡ tail) zero ∷ [])
  ≡ encodeCodeListWithRest tail zero
atomTailFromListF-canonical-correct n tail
  rewrite div4F-correct (encodeCodeListWithRest (atom n ∷ˡ tail) zero)
        | div4Nat-appendDigit
            d1
            (encodeCodeWithRest
              (atom n)
              (encodeCodeListWithRest tail zero))
        | atomRestF-withRest-correct
            n
            (encodeCodeListWithRest tail zero) =
  refl

rawAtomListHeadTailF-correct :
  (list-code head-code tail-code : ℕ) →
  evalPRF
    rawAtomListHeadTailF
    (args₃ list-code head-code tail-code)
  ≡
  mulNat
    (evalPRF codeListConsF (list-code ∷ []))
    (mulNat
      (evalPRF isAtomCodeF (evalPRF div4F (list-code ∷ []) ∷ []))
      (mulNat
        (eqNatNat
          (evalPRF atomHeadCodeFromListF (list-code ∷ []))
          head-code)
        (eqNatNat
          (evalPRF atomTailFromListF (list-code ∷ []))
          tail-code)))
rawAtomListHeadTailF-correct list-code head-code tail-code
  rewrite andF-correct
            (evalPRF codeListConsF (list-code ∷ []))
            (evalPRF
              (compF andF
                ( compF isAtomCodeF
                  (compF div4F (projF fin0 ∷ []) ∷ []) ∷
                  compF andF
                  ( compF eqNatF
                    ( compF atomHeadCodeFromListF (projF fin0 ∷ []) ∷
                      projF fin1 ∷ []) ∷
                    compF eqNatF
                    ( compF atomTailFromListF (projF fin0 ∷ []) ∷
                      projF fin2 ∷ []) ∷ []) ∷ []))
              (args₃ list-code head-code tail-code))
        | andF-correct
            (evalPRF
              (compF isAtomCodeF
                (compF div4F (projF fin0 ∷ []) ∷ []))
              (args₃ list-code head-code tail-code))
            (evalPRF
              (compF andF
                ( compF eqNatF
                  ( compF atomHeadCodeFromListF (projF fin0 ∷ []) ∷
                    projF fin1 ∷ []) ∷
                  compF eqNatF
                  ( compF atomTailFromListF (projF fin0 ∷ []) ∷
                    projF fin2 ∷ []) ∷ []))
              (args₃ list-code head-code tail-code))
        | andF-correct
            (evalPRF
              (compF eqNatF
                ( compF atomHeadCodeFromListF (projF fin0 ∷ []) ∷
                  projF fin1 ∷ []))
              (args₃ list-code head-code tail-code))
            (evalPRF
              (compF eqNatF
                ( compF atomTailFromListF (projF fin0 ∷ []) ∷
                  projF fin2 ∷ []))
              (args₃ list-code head-code tail-code))
        | eqNatF-correct
            (evalPRF atomHeadCodeFromListF (list-code ∷ []))
            head-code
        | eqNatF-correct
            (evalPRF atomTailFromListF (list-code ∷ []))
            tail-code =
  refl

rawAtomListHeadTail-complete :
  {list-code head-code tail-code : ℕ} →
  RawAtomListHeadTailNat list-code head-code tail-code →
  PRRel-holds rawAtomListHeadTailPR (args₃ list-code head-code tail-code)
rawAtomListHeadTail-complete {list-code} {head-code} {tail-code}
    (cons-head ,× (atom-head ,× (head-eq ,× tail-eq)))
  rewrite rawAtomListHeadTailF-correct list-code head-code tail-code
        | codeListConsF-complete-head list-code cons-head
        | isAtomCodeF-complete-head
            (evalPRF div4F (list-code ∷ []))
            atom-head
        | head-eq
        | eqNatNat-refl-code
            (evalPRF atomHeadCodeFromListF (list-code ∷ []))
        | tail-eq
        | eqNatNat-refl-code
            (evalPRF atomTailFromListF (list-code ∷ [])) =
  refl

rawAtomListHeadTail-sound :
  {list-code head-code tail-code : ℕ} →
  PRRel-holds rawAtomListHeadTailPR (args₃ list-code head-code tail-code) →
  RawAtomListHeadTailNat list-code head-code tail-code
rawAtomListHeadTail-sound {list-code} {head-code} {tail-code} holds
  with and4-output-sound
        (evalPRF codeListConsF (list-code ∷ []))
        (evalPRF isAtomCodeF (evalPRF div4F (list-code ∷ []) ∷ []))
        (eqNatNat
          (evalPRF atomHeadCodeFromListF (list-code ∷ []))
          head-code)
        (eqNatNat
          (evalPRF atomTailFromListF (list-code ∷ []))
          tail-code)
        (evalPRF
          rawAtomListHeadTailF
          (args₃ list-code head-code tail-code))
        (rawAtomListHeadTailF-correct list-code head-code tail-code)
        holds
... | cons-one ,× (atom-one ,× (head-one ,× tail-one)) =
  codeListConsF-sound-head list-code cons-one ,×
  ( isAtomCodeF-sound-head
      (evalPRF div4F (list-code ∷ []))
      atom-one
    ,×
    ( sym
        (eqNatNat-sound-code
          (evalPRF atomHeadCodeFromListF (list-code ∷ []))
          head-code
          head-one)
      ,×
      sym
        (eqNatNat-sound-code
          (evalPRF atomTailFromListF (list-code ∷ []))
          tail-code
          tail-one)))

rawAtomListHeadTailNat-canonical :
  (n : ℕ) → (tail : List Code) →
  RawAtomListHeadTailNat
    (encodeCodeListWithRest (atom n ∷ˡ tail) zero)
    (encodeCode (atom n))
    (encodeCodeListWithRest tail zero)
rawAtomListHeadTailNat-canonical n tail =
  codeListConsF-sound-head
    (encodeCodeListWithRest (atom n ∷ˡ tail) zero)
    (codeListConsF-canonical-cons-complete (atom n) tail)
  ,×
  ( atom-head
    ,×
    ( sym (atomHeadCodeFromListF-canonical-correct n tail)
      ,×
      sym (atomTailFromListF-canonical-correct n tail)))
  where
    atom-head :
      AtomHeadNat
        (evalPRF div4F
          (encodeCodeListWithRest (atom n ∷ˡ tail) zero ∷ []))
    atom-head
      rewrite div4F-correct
                (encodeCodeListWithRest (atom n ∷ˡ tail) zero)
            | div4Nat-appendDigit
                d1
                (encodeCodeWithRest
                  (atom n)
                  (encodeCodeListWithRest tail zero))
            | div4Nat-appendDigit
                d0
                (encodeNatWithRest
                  n
                  (encodeCodeListWithRest tail zero))
            | mod4Nat-appendDigit
                d0
                (encodeNatWithRest
                  n
                  (encodeCodeListWithRest tail zero)) =
      refl

rawAtomListHeadTail-canonical-complete :
  (n : ℕ) → (tail : List Code) →
  PRRel-holds
    rawAtomListHeadTailPR
    (args₃
      (encodeCodeListWithRest (atom n ∷ˡ tail) zero)
      (encodeCode (atom n))
      (encodeCodeListWithRest tail zero))
rawAtomListHeadTail-canonical-complete n tail =
  rawAtomListHeadTail-complete
    {list-code = encodeCodeListWithRest (atom n ∷ˡ tail) zero}
    {head-code = encodeCode (atom n)}
    {tail-code = encodeCodeListWithRest tail zero}
    (rawAtomListHeadTailNat-canonical n tail)

record CanonicalCodeRawAtomListPR : Set₁ where
  field
    raw-atom-list-head-tail-pr :
      PRRel (suc (suc (suc zero)))

    raw-atom-list-head-tail-complete :
      {list-code head-code tail-code : ℕ} →
      RawAtomListHeadTailNat list-code head-code tail-code →
      PRRel-holds
        raw-atom-list-head-tail-pr
        (args₃ list-code head-code tail-code)

    raw-atom-list-head-tail-sound :
      {list-code head-code tail-code : ℕ} →
      PRRel-holds
        raw-atom-list-head-tail-pr
        (args₃ list-code head-code tail-code) →
      RawAtomListHeadTailNat list-code head-code tail-code

canonicalCodeRawAtomListPR : CanonicalCodeRawAtomListPR
canonicalCodeRawAtomListPR = record
  { raw-atom-list-head-tail-pr = rawAtomListHeadTailPR
  ; raw-atom-list-head-tail-complete =
      λ {list-code} {head-code} {tail-code} →
        rawAtomListHeadTail-complete
          {list-code}
          {head-code}
          {tail-code}
  ; raw-atom-list-head-tail-sound =
      λ {list-code} {head-code} {tail-code} →
        rawAtomListHeadTail-sound
          {list-code}
          {head-code}
          {tail-code}
  }

record CanonicalCodeRawAtomListPARepresentability
    (D : CanonicalCodeRawAtomListPR) : Set₁ where
  field
    raw-atom-list-head-tail-represented :
      PARepresentsRelation
        (CanonicalCodeRawAtomListPR.raw-atom-list-head-tail-pr D)

canonicalCodeRawAtomListPR-represented :
  (D : CanonicalCodeRawAtomListPR) →
  CanonicalCodeRawAtomListPARepresentability D
canonicalCodeRawAtomListPR-represented D = record
  { raw-atom-list-head-tail-represented =
      prrel-represented
        (CanonicalCodeRawAtomListPR.raw-atom-list-head-tail-pr D)
  }

canonicalCodeRawAtomListPARepresentability :
  CanonicalCodeRawAtomListPARepresentability canonicalCodeRawAtomListPR
canonicalCodeRawAtomListPARepresentability =
  canonicalCodeRawAtomListPR-represented canonicalCodeRawAtomListPR
