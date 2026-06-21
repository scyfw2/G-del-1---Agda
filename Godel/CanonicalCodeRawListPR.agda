{-# OPTIONS --safe #-}

module Godel.CanonicalCodeRawListPR where

open import Agda.Builtin.List using (List) renaming ([] to []ˡ; _∷_ to _∷ˡ_)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.PrimitiveRecursive
open import Godel.PRRepresentabilityFinal
  using (PARepresentsRelation; prrel-represented)
open import Godel.CanonicalCoding
  using
    ( Code
    ; encodeCodeListWithRest
    )
open import Godel.CanonicalCodePR
  using
    ( CodeListNilHeadNat
    ; CodeListConsHeadNat
    ; codeListNilF
    ; codeListConsF
    ; codeListNilF-complete-head
    ; codeListNilF-sound-head
    ; codeListConsF-complete-head
    ; codeListConsF-sound-head
    ; codeListNilF-canonical-empty-complete
    ; codeListConsF-canonical-cons-complete
    )

-- Raw list-shape branch checks for canonical code lists.  These are the
-- first branching tests needed by the later code-list parser: nil is a d0
-- head, and cons is a d1 head.  The head/tail payload parser is intentionally
-- separate.

RawCodeListNilNat : ℕ → Set
RawCodeListNilNat input =
  CodeListNilHeadNat input

RawCodeListConsNat : ℕ → Set
RawCodeListConsNat input =
  CodeListConsHeadNat input

rawCodeListNilPR : PRRel (suc zero)
rawCodeListNilPR =
  rel codeListNilF

rawCodeListConsPR : PRRel (suc zero)
rawCodeListConsPR =
  rel codeListConsF

rawCodeListNil-complete :
  {input : ℕ} →
  RawCodeListNilNat input →
  PRRel-holds rawCodeListNilPR (input ∷ [])
rawCodeListNil-complete {input} =
  codeListNilF-complete-head input

rawCodeListNil-sound :
  {input : ℕ} →
  PRRel-holds rawCodeListNilPR (input ∷ []) →
  RawCodeListNilNat input
rawCodeListNil-sound {input} =
  codeListNilF-sound-head input

rawCodeListCons-complete :
  {input : ℕ} →
  RawCodeListConsNat input →
  PRRel-holds rawCodeListConsPR (input ∷ [])
rawCodeListCons-complete {input} =
  codeListConsF-complete-head input

rawCodeListCons-sound :
  {input : ℕ} →
  PRRel-holds rawCodeListConsPR (input ∷ []) →
  RawCodeListConsNat input
rawCodeListCons-sound {input} =
  codeListConsF-sound-head input

rawCodeListNil-canonical-complete :
  PRRel-holds
    rawCodeListNilPR
    (encodeCodeListWithRest []ˡ zero ∷ [])
rawCodeListNil-canonical-complete =
  codeListNilF-canonical-empty-complete

rawCodeListCons-canonical-complete :
  (head : Code) → (tail : List Code) →
  PRRel-holds
    rawCodeListConsPR
    (encodeCodeListWithRest (head ∷ˡ tail) zero ∷ [])
rawCodeListCons-canonical-complete =
  codeListConsF-canonical-cons-complete

record CanonicalCodeRawListPR : Set₁ where
  field
    raw-list-nil-pr :
      PRRel (suc zero)

    raw-list-cons-pr :
      PRRel (suc zero)

    raw-list-nil-complete :
      {input : ℕ} →
      RawCodeListNilNat input →
      PRRel-holds raw-list-nil-pr (input ∷ [])

    raw-list-nil-sound :
      {input : ℕ} →
      PRRel-holds raw-list-nil-pr (input ∷ []) →
      RawCodeListNilNat input

    raw-list-cons-complete :
      {input : ℕ} →
      RawCodeListConsNat input →
      PRRel-holds raw-list-cons-pr (input ∷ [])

    raw-list-cons-sound :
      {input : ℕ} →
      PRRel-holds raw-list-cons-pr (input ∷ []) →
      RawCodeListConsNat input

canonicalCodeRawListPR : CanonicalCodeRawListPR
canonicalCodeRawListPR = record
  { raw-list-nil-pr = rawCodeListNilPR
  ; raw-list-cons-pr = rawCodeListConsPR
  ; raw-list-nil-complete =
      λ {input} → rawCodeListNil-complete {input}
  ; raw-list-nil-sound =
      λ {input} → rawCodeListNil-sound {input}
  ; raw-list-cons-complete =
      λ {input} → rawCodeListCons-complete {input}
  ; raw-list-cons-sound =
      λ {input} → rawCodeListCons-sound {input}
  }

record CanonicalCodeRawListPARepresentability
    (D : CanonicalCodeRawListPR) : Set₁ where
  field
    raw-list-nil-represented :
      PARepresentsRelation
        (CanonicalCodeRawListPR.raw-list-nil-pr D)

    raw-list-cons-represented :
      PARepresentsRelation
        (CanonicalCodeRawListPR.raw-list-cons-pr D)

canonicalCodeRawListPR-represented :
  (D : CanonicalCodeRawListPR) →
  CanonicalCodeRawListPARepresentability D
canonicalCodeRawListPR-represented D = record
  { raw-list-nil-represented =
      prrel-represented (CanonicalCodeRawListPR.raw-list-nil-pr D)
  ; raw-list-cons-represented =
      prrel-represented (CanonicalCodeRawListPR.raw-list-cons-pr D)
  }

canonicalCodeRawListPARepresentability :
  CanonicalCodeRawListPARepresentability canonicalCodeRawListPR
canonicalCodeRawListPARepresentability =
  canonicalCodeRawListPR-represented canonicalCodeRawListPR
