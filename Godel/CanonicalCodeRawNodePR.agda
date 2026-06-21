{-# OPTIONS --safe #-}

module Godel.CanonicalCodeRawNodePR where

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.PRBooleanHelpers using (andF; eqNatF; fin0; fin1; fin2)
open import Godel.PRArithmeticSemantics
  using (mulNat; eqNatNat; andF-correct; eqNatF-correct)
open import Godel.PRBooleanSoundness
  using (and-output-nonzero-sound; and3-output-sound)
open import Godel.PRDigitSemantics using (mod4Nat)
open import Godel.PRRepresentabilityFinal
  using (PARepresentsRelation; prrel-represented)
open import Godel.CanonicalCoding
  using
    ( Code
    ; node
    ; encodeCode
    ; encodeCodeListWithRest
    )
open import Godel.CanonicalCodePR
  using
    ( NodeHeadNat
    ; isNodeCodeF
    ; nodeTagF
    ; nodeChildrenF
    ; isNodeCodeF-complete-head
    ; isNodeCodeF-sound-head
    ; isNodeCodeF-canonical-complete
    ; isDigitF-correct
    ; nodeTagF-canonical-correct
    ; nodeChildrenF-canonical-correct
    ; eqNatNat-refl-code
    ; eqNatNat-sound-code
    )
open import Godel.CanonicalCodeNodeTargets using (NodeCodeNat)
open import Godel.CanonicalCodeParserTargets using (args₃)

eqNatNat-nonzero-sound-code :
  (m n : ℕ) →
  Σ ℕ (λ k → eqNatNat m n ≡ suc k) →
  m ≡ n
eqNatNat-nonzero-sound-code zero zero nonzero = refl
eqNatNat-nonzero-sound-code zero (suc n) (k ,Σ ())
eqNatNat-nonzero-sound-code (suc m) zero (k ,Σ ())
eqNatNat-nonzero-sound-code (suc m) (suc n) nonzero =
  cong suc (eqNatNat-nonzero-sound-code m n nonzero)

-- A lightweight parser layer for the outer code-tree node shape.
--
-- This is intentionally weaker than NodeCodeNat from
-- CanonicalCodeNodeTargets: it checks the raw node head and the PRF
-- destructors for tag/children-code.  The full NodeCodeNat target also
-- requires the children-code to be a decoded canonical list of Code values.
-- Keeping this layer separate lets proof-rule dispatch use concrete PR
-- branch data before the full code-list parser is rebuilt.

RawNodeCodeNat : ℕ → ℕ → ℕ → Set
RawNodeCodeNat input tag children-code =
  NodeHeadNat input ×
  ((tag ≡ evalPRF nodeTagF (input ∷ [])) ×
   (children-code ≡ evalPRF nodeChildrenF (input ∷ [])))

rawNodeCodeF : PRF (suc (suc (suc zero)))
rawNodeCodeF =
  compF andF
    ( compF isNodeCodeF (projF fin0 ∷ []) ∷
      compF andF
        ( compF eqNatF
          ( compF nodeTagF (projF fin0 ∷ []) ∷
            projF fin1 ∷ []) ∷
          compF eqNatF
          ( compF nodeChildrenF (projF fin0 ∷ []) ∷
            projF fin2 ∷ []) ∷ []) ∷ [])

rawNodeCodePR : PRRel (suc (suc (suc zero)))
rawNodeCodePR = rel rawNodeCodeF

rawNodeCodeF-correct :
  (input tag children-code : ℕ) →
  evalPRF rawNodeCodeF (args₃ input tag children-code) ≡
  mulNat
    (evalPRF isNodeCodeF (input ∷ []))
    (mulNat
      (eqNatNat (evalPRF nodeTagF (input ∷ [])) tag)
      (eqNatNat
        (evalPRF nodeChildrenF (input ∷ []))
        children-code))
rawNodeCodeF-correct input tag children-code
  rewrite andF-correct
            (evalPRF isNodeCodeF (input ∷ []))
            (evalPRF
              (compF andF
                ( compF eqNatF
                  ( compF nodeTagF (projF fin0 ∷ []) ∷
                    projF fin1 ∷ []) ∷
                  compF eqNatF
                  ( compF nodeChildrenF (projF fin0 ∷ []) ∷
                    projF fin2 ∷ []) ∷ []))
              (args₃ input tag children-code))
        | andF-correct
            (evalPRF
              (compF eqNatF
                ( compF nodeTagF (projF fin0 ∷ []) ∷
                  projF fin1 ∷ []))
              (args₃ input tag children-code))
            (evalPRF
              (compF eqNatF
                ( compF nodeChildrenF (projF fin0 ∷ []) ∷
                  projF fin2 ∷ []))
              (args₃ input tag children-code))
        | eqNatF-correct
            (evalPRF nodeTagF (input ∷ []))
            tag
        | eqNatF-correct
            (evalPRF nodeChildrenF (input ∷ []))
            children-code =
  refl

rawNodeCode-complete :
  {input tag children-code : ℕ} →
  RawNodeCodeNat input tag children-code →
  PRRel-holds rawNodeCodePR (args₃ input tag children-code)
rawNodeCode-complete {input} {tag} {children-code}
    (node-head ,× (tag-eq ,× children-eq))
  rewrite rawNodeCodeF-correct input tag children-code
        | isNodeCodeF-complete-head input node-head
        | tag-eq
        | eqNatNat-refl-code (evalPRF nodeTagF (input ∷ []))
        | children-eq
        | eqNatNat-refl-code (evalPRF nodeChildrenF (input ∷ [])) =
  refl

rawNodeCode-sound :
  {input tag children-code : ℕ} →
  PRRel-holds rawNodeCodePR (args₃ input tag children-code) →
  RawNodeCodeNat input tag children-code
rawNodeCode-sound {input} {tag} {children-code} holds
  with and3-output-sound
        (evalPRF isNodeCodeF (input ∷ []))
        (eqNatNat (evalPRF nodeTagF (input ∷ [])) tag)
        (eqNatNat (evalPRF nodeChildrenF (input ∷ [])) children-code)
        (evalPRF rawNodeCodeF (args₃ input tag children-code))
        (rawNodeCodeF-correct input tag children-code)
        holds
... | node-one ,× (tag-one ,× children-one) =
  isNodeCodeF-sound-head input node-one ,×
  ( sym
      (eqNatNat-sound-code
        (evalPRF nodeTagF (input ∷ []))
        tag
        tag-one)
    ,×
    sym
      (eqNatNat-sound-code
        (evalPRF nodeChildrenF (input ∷ []))
        children-code
        children-one))

isNodeCodeF-nonzero-sound-head :
  (input : ℕ) →
  Σ ℕ
    (λ k →
      evalPRF isNodeCodeF (input ∷ []) ≡ suc k) →
  NodeHeadNat input
isNodeCodeF-nonzero-sound-head input (k ,Σ nonzero) =
  eqNatNat-nonzero-sound-code
    (mod4Nat input)
    (suc zero)
    (k ,Σ trans (sym (isDigitF-correct (suc zero) input)) nonzero)

rawNodeCode-nonzero-sound :
  {input tag children-code : ℕ} →
  Σ ℕ
    (λ k →
      evalPRF rawNodeCodeF (args₃ input tag children-code) ≡ suc k) →
  RawNodeCodeNat input tag children-code
rawNodeCode-nonzero-sound {input} {tag} {children-code} nonzero
  with and-output-nonzero-sound
        (evalPRF isNodeCodeF (input ∷ []))
        (mulNat
          (eqNatNat (evalPRF nodeTagF (input ∷ [])) tag)
          (eqNatNat
            (evalPRF nodeChildrenF (input ∷ []))
            children-code))
        (evalPRF rawNodeCodeF (args₃ input tag children-code))
        (rawNodeCodeF-correct input tag children-code)
        nonzero
... | node-nz ,× rest-nz
  with and-output-nonzero-sound
        (eqNatNat (evalPRF nodeTagF (input ∷ [])) tag)
        (eqNatNat
          (evalPRF nodeChildrenF (input ∷ []))
          children-code)
        (mulNat
          (eqNatNat (evalPRF nodeTagF (input ∷ [])) tag)
          (eqNatNat
            (evalPRF nodeChildrenF (input ∷ []))
            children-code))
        refl
        rest-nz
... | tag-nz ,× children-nz =
  isNodeCodeF-nonzero-sound-head input node-nz
  ,×
  ( sym
      (eqNatNat-nonzero-sound-code
        (evalPRF nodeTagF (input ∷ []))
        tag
        tag-nz)
    ,×
    sym
      (eqNatNat-nonzero-sound-code
        (evalPRF nodeChildrenF (input ∷ []))
        children-code
        children-nz))

rawNodeCodeNat-canonical :
  (tag : ℕ) → (children : List Code) →
  RawNodeCodeNat
    (encodeCode (node tag children))
    tag
    (encodeCodeListWithRest children zero)
rawNodeCodeNat-canonical tag children =
  isNodeCodeF-sound-head
    (encodeCode (node tag children))
    (isNodeCodeF-canonical-complete tag children)
  ,×
  ( sym (nodeTagF-canonical-correct tag children)
    ,×
    sym (nodeChildrenF-canonical-correct tag children))

nodeCodeNat-to-rawNodeCodeNat :
  {input tag children-code : ℕ} →
  NodeCodeNat input tag children-code →
  RawNodeCodeNat input tag children-code
nodeCodeNat-to-rawNodeCodeNat {tag = tag}
    (children ,Σ (input-eq ,× children-code-eq))
  rewrite input-eq | children-code-eq =
  rawNodeCodeNat-canonical tag children

nodeCodeNat-to-rawNodeCode-complete :
  {input tag children-code : ℕ} →
  NodeCodeNat input tag children-code →
  PRRel-holds rawNodeCodePR (args₃ input tag children-code)
nodeCodeNat-to-rawNodeCode-complete
    {input} {tag} {children-code} node-code =
  rawNodeCode-complete
    {input = input}
    {tag = tag}
    {children-code = children-code}
    (nodeCodeNat-to-rawNodeCodeNat
      {input = input}
      {tag = tag}
      {children-code = children-code}
      node-code)

rawNodeCode-canonical-complete :
  (tag : ℕ) → (children : List Code) →
  PRRel-holds
    rawNodeCodePR
    (args₃
      (encodeCode (node tag children))
      tag
      (encodeCodeListWithRest children zero))
rawNodeCode-canonical-complete tag children =
  rawNodeCode-complete
    {input = encodeCode (node tag children)}
    {tag = tag}
    {children-code = encodeCodeListWithRest children zero}
    (rawNodeCodeNat-canonical tag children)

record CanonicalCodeRawNodePR : Set₁ where
  field
    raw-node-pr :
      PRRel (suc (suc (suc zero)))

    raw-node-complete :
      {input tag children-code : ℕ} →
      RawNodeCodeNat input tag children-code →
      PRRel-holds raw-node-pr (args₃ input tag children-code)

    raw-node-sound :
      {input tag children-code : ℕ} →
      PRRel-holds raw-node-pr (args₃ input tag children-code) →
      RawNodeCodeNat input tag children-code

canonicalCodeRawNodePR : CanonicalCodeRawNodePR
canonicalCodeRawNodePR = record
  { raw-node-pr = rawNodeCodePR
  ; raw-node-complete =
      λ {input} {tag} {children-code} →
        rawNodeCode-complete {input} {tag} {children-code}
  ; raw-node-sound =
      λ {input} {tag} {children-code} →
        rawNodeCode-sound {input} {tag} {children-code}
  }

record CanonicalCodeRawNodePARepresentability
    (D : CanonicalCodeRawNodePR) : Set₁ where
  field
    raw-node-represented :
      PARepresentsRelation
        (CanonicalCodeRawNodePR.raw-node-pr D)

canonicalCodeRawNodePR-represented :
  (D : CanonicalCodeRawNodePR) →
  CanonicalCodeRawNodePARepresentability D
canonicalCodeRawNodePR-represented D = record
  { raw-node-represented =
      prrel-represented (CanonicalCodeRawNodePR.raw-node-pr D)
  }

canonicalCodeRawNodePARepresentability :
  CanonicalCodeRawNodePARepresentability canonicalCodeRawNodePR
canonicalCodeRawNodePARepresentability =
  canonicalCodeRawNodePR-represented canonicalCodeRawNodePR
