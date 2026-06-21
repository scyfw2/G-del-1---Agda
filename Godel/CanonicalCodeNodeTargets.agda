{-# OPTIONS --safe #-}

module Godel.CanonicalCodeNodeTargets where

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.PRRepresentabilityFinal
  using (PARepresentsRelation; prrel-represented)
open import Godel.CanonicalCoding
  using
    ( Code
    ; node
    ; encodeCode
    ; encodeCodeListWithRest
    )
open import Godel.CanonicalCodeParserTargets using (args₃)

-- Numeric target for the outer node parser used by the proof checker.
-- A proof-code branch must first expose a rule tag and a list-code for its
-- children before rule-specific checks can run.

NodeCodeNat : ℕ → ℕ → ℕ → Set
NodeCodeNat input tag children-code =
  Σ (List Code)
    (λ children →
      (input ≡ encodeCode (node tag children)) ×
      (children-code ≡ encodeCodeListWithRest children zero))

nodeCodeNat-complete :
  (tag : ℕ) → (children : List Code) →
  NodeCodeNat
    (encodeCode (node tag children))
    tag
    (encodeCodeListWithRest children zero)
nodeCodeNat-complete tag children =
  children ,Σ (refl ,× refl)

nodeCodeNat-sound :
  (input tag children-code : ℕ) →
  NodeCodeNat input tag children-code →
  Σ (List Code)
    (λ children →
      (input ≡ encodeCode (node tag children)) ×
      (children-code ≡ encodeCodeListWithRest children zero))
nodeCodeNat-sound input tag children-code proof = proof

record CanonicalCodeNodeParserPR : Set₁ where
  field
    node-code-pr :
      PRRel (suc (suc (suc zero)))

    node-code-complete :
      {input tag children-code : ℕ} →
      NodeCodeNat input tag children-code →
      PRRel-holds node-code-pr (args₃ input tag children-code)

    node-code-sound :
      {input tag children-code : ℕ} →
      PRRel-holds node-code-pr (args₃ input tag children-code) →
      NodeCodeNat input tag children-code

record CanonicalCodeNodeParserPARepresentability
    (D : CanonicalCodeNodeParserPR) : Set₁ where
  field
    node-code-represented :
      PARepresentsRelation
        (CanonicalCodeNodeParserPR.node-code-pr D)

canonicalCodeNodeParserPR-represented :
  (D : CanonicalCodeNodeParserPR) →
  CanonicalCodeNodeParserPARepresentability D
canonicalCodeNodeParserPR-represented D = record
  { node-code-represented =
      prrel-represented (CanonicalCodeNodeParserPR.node-code-pr D)
  }
