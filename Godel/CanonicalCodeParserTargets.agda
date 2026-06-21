{-# OPTIONS --safe #-}

module Godel.CanonicalCodeParserTargets where

open import Agda.Builtin.List using (List) renaming ([] to []ˡ; _∷_ to _∷ˡ_)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.PRRepresentabilityFinal
  using (PARepresentsRelation; prrel-represented)
open import Godel.CanonicalCoding
  using
    ( Code
    ; encodeCode
    ; encodeCodeWithRest
    ; encodeCodeListWithRest
    )

-- Numeric semantic targets for the self-delimiting canonical-code parser.
-- These relations are the intended correctness specifications for the future
-- PRF implementations of codeListHeadF / codeListTailF / codeListLengthF /
-- codeListNthF in Godel.CanonicalCodePR.

args₂ : ℕ → ℕ → Vec ℕ (suc (suc zero))
args₂ x y = x ∷ y ∷ []

args₃ : ℕ → ℕ → ℕ → Vec ℕ (suc (suc (suc zero)))
args₃ x y z = x ∷ y ∷ z ∷ []

CodeWithRestNat : ℕ → ℕ → ℕ → Set
CodeWithRestNat input code rest =
  Σ Code
    (λ c →
      (input ≡ encodeCodeWithRest c rest) ×
      (code ≡ encodeCode c))

CodeSkipNat : ℕ → ℕ → Set
CodeSkipNat input rest =
  Σ Code
    (λ c →
      input ≡ encodeCodeWithRest c rest)

CodeListWithRestNat : ℕ → List Code → ℕ → Set
CodeListWithRestNat input codes rest =
  input ≡ encodeCodeListWithRest codes rest

codeListLength : List Code → ℕ
codeListLength []ˡ = zero
codeListLength (head ∷ˡ tail) = suc (codeListLength tail)

codeListNthDefault : List Code → ℕ → ℕ → ℕ
codeListNthDefault []ˡ index default = default
codeListNthDefault (head ∷ˡ tail) zero default = encodeCode head
codeListNthDefault (head ∷ˡ tail) (suc index) default =
  codeListNthDefault tail index default

CodeListNthIn : List Code → ℕ → ℕ → Set
CodeListNthIn []ˡ index nth-code =
  nth-code ≡ zero
CodeListNthIn (head ∷ˡ tail) zero nth-code =
  nth-code ≡ encodeCode head
CodeListNthIn (head ∷ˡ tail) (suc index) nth-code =
  CodeListNthIn tail index nth-code

codeListNthDefault-complete :
  (codes : List Code) → (index : ℕ) →
  CodeListNthIn codes index (codeListNthDefault codes index zero)
codeListNthDefault-complete []ˡ index = refl
codeListNthDefault-complete (head ∷ˡ tail) zero = refl
codeListNthDefault-complete (head ∷ˡ tail) (suc index) =
  codeListNthDefault-complete tail index

CodeListHeadNat : ℕ → ℕ → Set
CodeListHeadNat list-code head-code =
  Σ Code
    (λ head →
      Σ (List Code)
        (λ tail →
          (list-code ≡ encodeCodeListWithRest (head ∷ˡ tail) zero) ×
          (head-code ≡ encodeCode head)))

CodeListTailNat : ℕ → ℕ → Set
CodeListTailNat list-code tail-code =
  Σ Code
    (λ head →
      Σ (List Code)
        (λ tail →
          (list-code ≡ encodeCodeListWithRest (head ∷ˡ tail) zero) ×
          (tail-code ≡ encodeCodeListWithRest tail zero)))

CodeListLengthNat : ℕ → ℕ → Set
CodeListLengthNat list-code len =
  Σ (List Code)
    (λ codes →
      (list-code ≡ encodeCodeListWithRest codes zero) ×
      (len ≡ codeListLength codes))

CodeListNthNat : ℕ → ℕ → ℕ → Set
CodeListNthNat list-code index nth-code =
  Σ (List Code)
    (λ codes →
      (list-code ≡ encodeCodeListWithRest codes zero) ×
      CodeListNthIn codes index nth-code)

codeListHeadNat-complete :
  (head : Code) → (tail : List Code) →
  CodeListHeadNat
    (encodeCodeListWithRest (head ∷ˡ tail) zero)
    (encodeCode head)
codeListHeadNat-complete head tail =
  head ,Σ (tail ,Σ (refl ,× refl))

codeListTailNat-complete :
  (head : Code) → (tail : List Code) →
  CodeListTailNat
    (encodeCodeListWithRest (head ∷ˡ tail) zero)
    (encodeCodeListWithRest tail zero)
codeListTailNat-complete head tail =
  head ,Σ (tail ,Σ (refl ,× refl))

codeListLengthNat-complete :
  (codes : List Code) →
  CodeListLengthNat
    (encodeCodeListWithRest codes zero)
    (codeListLength codes)
codeListLengthNat-complete codes =
  codes ,Σ (refl ,× refl)

codeListNthNat-complete :
  (codes : List Code) → (index : ℕ) →
  CodeListNthNat
    (encodeCodeListWithRest codes zero)
    index
    (codeListNthDefault codes index zero)
codeListNthNat-complete codes index =
  codes ,Σ (refl ,× codeListNthDefault-complete codes index)

codeSkipNat-complete :
  (code : Code) → (rest : ℕ) →
  CodeSkipNat (encodeCodeWithRest code rest) rest
codeSkipNat-complete code rest =
  code ,Σ refl

codeSkipNat-sound :
  (input rest : ℕ) →
  CodeSkipNat input rest →
  Σ Code
    (λ code →
      input ≡ encodeCodeWithRest code rest)
codeSkipNat-sound input rest proof = proof

codeListHeadNat-sound :
  (list-code head-code : ℕ) →
  CodeListHeadNat list-code head-code →
  Σ Code
    (λ head →
      Σ (List Code)
        (λ tail →
          (list-code ≡ encodeCodeListWithRest (head ∷ˡ tail) zero) ×
          (head-code ≡ encodeCode head)))
codeListHeadNat-sound list-code head-code proof = proof

codeListTailNat-sound :
  (list-code tail-code : ℕ) →
  CodeListTailNat list-code tail-code →
  Σ Code
    (λ head →
      Σ (List Code)
        (λ tail →
          (list-code ≡ encodeCodeListWithRest (head ∷ˡ tail) zero) ×
          (tail-code ≡ encodeCodeListWithRest tail zero)))
codeListTailNat-sound list-code tail-code proof = proof

record CanonicalCodeParserPR : Set₁ where
  field
    code-with-rest-pr :
      PRRel (suc (suc (suc zero)))

    code-skip-pr :
      PRRel (suc (suc zero))

    code-list-head-pr :
      PRRel (suc (suc zero))

    code-list-tail-pr :
      PRRel (suc (suc zero))

    code-list-length-pr :
      PRRel (suc (suc zero))

    code-list-nth-pr :
      PRRel (suc (suc (suc zero)))

    code-with-rest-complete :
      {input code rest : ℕ} →
      CodeWithRestNat input code rest →
      PRRel-holds code-with-rest-pr (args₃ input code rest)

    code-with-rest-sound :
      {input code rest : ℕ} →
      PRRel-holds code-with-rest-pr (args₃ input code rest) →
      CodeWithRestNat input code rest

    code-skip-complete :
      {input rest : ℕ} →
      CodeSkipNat input rest →
      PRRel-holds code-skip-pr (args₂ input rest)

    code-skip-sound :
      {input rest : ℕ} →
      PRRel-holds code-skip-pr (args₂ input rest) →
      CodeSkipNat input rest

    code-list-head-complete :
      {list-code head-code : ℕ} →
      CodeListHeadNat list-code head-code →
      PRRel-holds code-list-head-pr (args₂ list-code head-code)

    code-list-head-sound :
      {list-code head-code : ℕ} →
      PRRel-holds code-list-head-pr (args₂ list-code head-code) →
      CodeListHeadNat list-code head-code

    code-list-tail-complete :
      {list-code tail-code : ℕ} →
      CodeListTailNat list-code tail-code →
      PRRel-holds code-list-tail-pr (args₂ list-code tail-code)

    code-list-tail-sound :
      {list-code tail-code : ℕ} →
      PRRel-holds code-list-tail-pr (args₂ list-code tail-code) →
      CodeListTailNat list-code tail-code

    code-list-length-complete :
      {list-code len : ℕ} →
      CodeListLengthNat list-code len →
      PRRel-holds code-list-length-pr (args₂ list-code len)

    code-list-length-sound :
      {list-code len : ℕ} →
      PRRel-holds code-list-length-pr (args₂ list-code len) →
      CodeListLengthNat list-code len

    code-list-nth-complete :
      {list-code index nth-code : ℕ} →
      CodeListNthNat list-code index nth-code →
      PRRel-holds code-list-nth-pr (args₃ list-code index nth-code)

    code-list-nth-sound :
      {list-code index nth-code : ℕ} →
      PRRel-holds code-list-nth-pr (args₃ list-code index nth-code) →
      CodeListNthNat list-code index nth-code

record CanonicalCodeParserPARepresentability
    (D : CanonicalCodeParserPR) : Set₁ where
  field
    code-with-rest-represented :
      PARepresentsRelation
        (CanonicalCodeParserPR.code-with-rest-pr D)

    code-skip-represented :
      PARepresentsRelation
        (CanonicalCodeParserPR.code-skip-pr D)

    code-list-head-represented :
      PARepresentsRelation
        (CanonicalCodeParserPR.code-list-head-pr D)

    code-list-tail-represented :
      PARepresentsRelation
        (CanonicalCodeParserPR.code-list-tail-pr D)

    code-list-length-represented :
      PARepresentsRelation
        (CanonicalCodeParserPR.code-list-length-pr D)

    code-list-nth-represented :
      PARepresentsRelation
        (CanonicalCodeParserPR.code-list-nth-pr D)

canonicalCodeParserPR-represented :
  (D : CanonicalCodeParserPR) →
  CanonicalCodeParserPARepresentability D
canonicalCodeParserPR-represented D = record
  { code-with-rest-represented =
      prrel-represented (CanonicalCodeParserPR.code-with-rest-pr D)
  ; code-skip-represented =
      prrel-represented (CanonicalCodeParserPR.code-skip-pr D)
  ; code-list-head-represented =
      prrel-represented (CanonicalCodeParserPR.code-list-head-pr D)
  ; code-list-tail-represented =
      prrel-represented (CanonicalCodeParserPR.code-list-tail-pr D)
  ; code-list-length-represented =
      prrel-represented (CanonicalCodeParserPR.code-list-length-pr D)
  ; code-list-nth-represented =
      prrel-represented (CanonicalCodeParserPR.code-list-nth-pr D)
  }
