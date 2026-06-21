{-# OPTIONS --safe #-}

module Godel.ProofRule37NodeChildren where

open import Agda.Builtin.List using (List) renaming ([] to []ˡ; _∷_ to _∷ˡ_)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.CanonicalCoding
  using
    ( atom
    ; encodeCodeListWithRest
    )
open import Godel.CanonicalCodeParserTargets using (args₃)
open import Godel.CanonicalCodeRawNodePR
  using
    ( RawNodeCodeNat
    ; rawNodeCodeF
    ; rawNodeCodePR
    ; rawNodeCode-complete
    ; rawNodeCode-sound
    ; rawNodeCode-nonzero-sound
    ; rawNodeCodeNat-canonical
    )
open import Godel.PrimitiveRecursive
open import Godel.PRBooleanHelpers using (andF; fin0; fin1; fin2; fin3)
open import Godel.PRBoundedSearch using (constF)
open import Godel.PRArithmeticSemantics
  using
    ( andF-correct
    ; constF-correct
    ; mulNat
    )
open import Godel.PRBooleanSoundness
  using (and-output-sound; and-output-nonzero-sound)
open import Godel.PRRepresentabilityFinal
  using
    ( PARepresentsRelation
    ; prrel-represented
    )
open import Godel.ProofRuleTargets
  using
    ( Rule37ChildrenCodeNat
    ; closedNumeralNeqCode
    ; eqNatNat-nonzero-sound-code
    ; rule37ChildrenArgs
    ; rule37ChildrenCodeF
    ; rule37ChildrenCodeF-correct
    ; rule37ChildrenCodePR
    ; rule37ChildrenCode-complete
    ; rule37ChildrenCode-sound
    )

-- A small concrete branch for the rule-37 proof-code shape.
--
-- It deliberately stops at the outer proof-code node and its children-code:
-- the formula-code and m != n checks stay in ProofRuleTargets.  This keeps the
-- rule-37 path decomposed into small PR relations instead of one normalization-
-- heavy monolithic checker.

args₄ : ℕ → ℕ → ℕ → ℕ → Vec ℕ (suc (suc (suc (suc zero))))
args₄ a b c d = a ∷ b ∷ c ∷ d ∷ []

rule37NodeChildrenF : PRF (suc (suc (suc (suc zero))))
rule37NodeChildrenF =
  compF andF
    ( compF rawNodeCodeF
      ( projF fin0 ∷
        constF 37 ∷
        projF fin1 ∷ []) ∷
      compF rule37ChildrenCodeF
      ( projF fin1 ∷
        projF fin2 ∷
        projF fin3 ∷ []) ∷ [])

rule37NodeChildrenPR : PRRel (suc (suc (suc (suc zero))))
rule37NodeChildrenPR =
  rel rule37NodeChildrenF

Rule37NodeChildrenNat : ℕ → ℕ → ℕ → ℕ → Set
Rule37NodeChildrenNat proof-code children-code m n =
  RawNodeCodeNat proof-code 37 children-code ×
  Rule37ChildrenCodeNat children-code m n

rule37NodeChildrenF-correct :
  (proof-code children-code m n : ℕ) →
  evalPRF rule37NodeChildrenF
    (args₄ proof-code children-code m n)
  ≡
  mulNat
    (evalPRF rawNodeCodeF (args₃ proof-code 37 children-code))
    (evalPRF
      rule37ChildrenCodeF
      (rule37ChildrenArgs children-code m n))
rule37NodeChildrenF-correct proof-code children-code m n
  rewrite constF-correct
            37
            (args₄ proof-code children-code m n)
        | andF-correct
            (evalPRF rawNodeCodeF (args₃ proof-code 37 children-code))
            (evalPRF
              rule37ChildrenCodeF
              (rule37ChildrenArgs children-code m n)) =
  refl

rule37NodeChildren-complete :
  {proof-code children-code m n : ℕ} →
  Rule37NodeChildrenNat proof-code children-code m n →
  PRRel-holds
    rule37NodeChildrenPR
    (args₄ proof-code children-code m n)
rule37NodeChildren-complete
    {proof-code} {children-code} {m} {n}
    (raw-node ,× children-code-ok)
  rewrite rule37NodeChildrenF-correct proof-code children-code m n
        | rawNodeCode-complete
            {input = proof-code}
            {tag = 37}
            {children-code = children-code}
            raw-node
        | rule37ChildrenCode-complete
            {children-code = children-code}
            {m = m}
            {n = n}
            children-code-ok =
  refl

rule37NodeChildren-sound :
  {proof-code children-code m n : ℕ} →
  PRRel-holds
    rule37NodeChildrenPR
    (args₄ proof-code children-code m n) →
  Rule37NodeChildrenNat proof-code children-code m n
rule37NodeChildren-sound
    {proof-code} {children-code} {m} {n} holds
  with and-output-sound
        (evalPRF rawNodeCodeF (args₃ proof-code 37 children-code))
        (evalPRF
          rule37ChildrenCodeF
          (rule37ChildrenArgs children-code m n))
        (evalPRF
          rule37NodeChildrenF
          (args₄ proof-code children-code m n))
        (rule37NodeChildrenF-correct proof-code children-code m n)
        holds
... | raw-node-one ,× children-code-one =
  ( rawNodeCode-sound
      {input = proof-code}
      {tag = 37}
      {children-code = children-code}
      raw-node-one
  )
  ,×
  rule37ChildrenCode-sound
    {children-code = children-code}
    {m = m}
    {n = n}
    children-code-one

rule37ChildrenCode-nonzero-sound :
  {children-code m n : ℕ} →
  Σ ℕ
    (λ k →
      evalPRF
        rule37ChildrenCodeF
        (rule37ChildrenArgs children-code m n)
      ≡ suc k) →
  Rule37ChildrenCodeNat children-code m n
rule37ChildrenCode-nonzero-sound {children-code} {m} {n} nonzero
  rewrite rule37ChildrenCodeF-correct children-code m n =
  eqNatNat-nonzero-sound-code
    children-code
    (encodeCodeListWithRest (atom m ∷ˡ atom n ∷ˡ []ˡ) zero)
    nonzero

rule37NodeChildren-nonzero-sound :
  {proof-code children-code m n : ℕ} →
  Σ ℕ
    (λ k →
      evalPRF
        rule37NodeChildrenF
        (args₄ proof-code children-code m n)
      ≡ suc k) →
  Rule37NodeChildrenNat proof-code children-code m n
rule37NodeChildren-nonzero-sound
    {proof-code} {children-code} {m} {n} nonzero
  with and-output-nonzero-sound
        (evalPRF rawNodeCodeF (args₃ proof-code 37 children-code))
        (evalPRF
          rule37ChildrenCodeF
          (rule37ChildrenArgs children-code m n))
        (evalPRF
          rule37NodeChildrenF
          (args₄ proof-code children-code m n))
        (rule37NodeChildrenF-correct proof-code children-code m n)
        nonzero
... | raw-node-nz ,× children-code-nz =
  rawNodeCode-nonzero-sound
    {input = proof-code}
    {tag = 37}
    {children-code = children-code}
    raw-node-nz
  ,×
  rule37ChildrenCode-nonzero-sound
    {children-code = children-code}
    {m = m}
    {n = n}
    children-code-nz

rule37NodeChildrenNat-canonical :
  (m n : ℕ) →
  Rule37NodeChildrenNat
    (closedNumeralNeqCode m n)
    (encodeCodeListWithRest (atom m ∷ˡ atom n ∷ˡ []ˡ) zero)
    m
    n
rule37NodeChildrenNat-canonical m n =
  rawNodeCodeNat-canonical 37 (atom m ∷ˡ atom n ∷ˡ []ˡ)
  ,×
  refl

rule37NodeChildren-canonical-complete :
  (m n : ℕ) →
  PRRel-holds
    rule37NodeChildrenPR
    (args₄
      (closedNumeralNeqCode m n)
      (encodeCodeListWithRest (atom m ∷ˡ atom n ∷ˡ []ˡ) zero)
      m
      n)
rule37NodeChildren-canonical-complete m n =
  rule37NodeChildren-complete
    {proof-code = closedNumeralNeqCode m n}
    {children-code =
      encodeCodeListWithRest (atom m ∷ˡ atom n ∷ˡ []ˡ) zero}
    {m = m}
    {n = n}
    (rule37NodeChildrenNat-canonical m n)

rule37NodeChildrenPR-represented :
  PARepresentsRelation rule37NodeChildrenPR
rule37NodeChildrenPR-represented =
  prrel-represented rule37NodeChildrenPR
