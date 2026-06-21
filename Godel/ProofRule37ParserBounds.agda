{-# OPTIONS --safe #-}

module Godel.ProofRule37ParserBounds where

open import Agda.Builtin.List renaming ([] to []ˡ; _∷_ to _∷ˡ_)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.CanonicalCoding
  using
    ( atom
    ; codeListSize
    ; encodeCodeListWithRest
    ; _≤_
    ; ≤-refl
    ; ≤-zero
    ; ≤-step
    ; ≤-suc
    ; ≤-trans
    ; codeListSize+base≤encodeCodeListWithRest
    )
open import Godel.CanonicalCodePR
  using
    ( nodeChildrenF
    ; nodeChildrenF-correct-to-prefix
    ; prefixNatValueNat
    ; prefixNatRestNat
    )
open import Godel.PrimitiveRecursive using (evalPRF; []; _∷_)
open import Godel.PRDigitSemantics using (div4Nat; iterDiv4Nat)
open import Godel.ProofRule37Bounds
  using
    ( head-atom-payload≤codeListSize
    ; tail-atom-payload≤codeListSize
    ; x≤x+y
    )
open import Godel.ProofRule37NodeChildren
  using (Rule37NodeChildrenNat)
open import Godel.ProofRule37ParserWitness
  using (Rule37ParserWitnessNat)
open import Godel.ProofRule37ParserSearchHit
  using
    ( Rule37ParserWitnessBoundsBridge )
open import Godel.ProofRuleTargets
  using (Rule37ChildrenCodeNat)

-- Bounds for the parser-backed rule-37 search.
--
-- The old rule37 bounds only handled the canonical closed-rule code directly.
-- The parser route instead learns that proof-code is a raw node and that its
-- parsed children-code is exactly [atom m, atom n].  This module proves that
-- those parser facts are enough to keep m and n within the proof-code bound
-- used by the two-dimensional search.

div4Nat≤input : (input : ℕ) → div4Nat input ≤ input
div4Nat≤input zero = ≤-refl zero
div4Nat≤input (suc zero) = ≤-zero (suc zero)
div4Nat≤input (suc (suc zero)) = ≤-zero (suc (suc zero))
div4Nat≤input (suc (suc (suc zero))) =
  ≤-zero (suc (suc (suc zero)))
div4Nat≤input (suc (suc (suc (suc input)))) =
  ≤-step
    (≤-step
      (≤-step
        (≤-suc (div4Nat≤input input))))

iterDiv4Nat≤input :
  (steps input : ℕ) → iterDiv4Nat steps input ≤ input
iterDiv4Nat≤input zero input =
  ≤-refl input
iterDiv4Nat≤input (suc steps) input =
  ≤-trans
    (div4Nat≤input (iterDiv4Nat steps input))
    (iterDiv4Nat≤input steps input)

prefixNatRestNat≤input :
  (input : ℕ) → prefixNatRestNat input ≤ input
prefixNatRestNat≤input input =
  iterDiv4Nat≤input
    (suc (prefixNatValueNat input))
    input

nodeChildrenF-value≤input :
  (input : ℕ) →
  evalPRF nodeChildrenF (input ∷ []) ≤ input
nodeChildrenF-value≤input input
  rewrite nodeChildrenF-correct-to-prefix input =
  ≤-trans
    (prefixNatRestNat≤input (div4Nat input))
    (div4Nat≤input input)

rule37-left-witness≤childrenCode :
  {children-code m n : ℕ} →
  Rule37ChildrenCodeNat children-code m n →
  m ≤ children-code
rule37-left-witness≤childrenCode {children-code} {m} {n} children-eq =
  subst
    (λ code → m ≤ code)
    (sym children-eq)
    (≤-trans
      (≤-trans
        (head-atom-payload≤codeListSize m n)
        (x≤x+y
          (codeListSize (atom m ∷ˡ atom n ∷ˡ []ˡ))
          zero))
      (codeListSize+base≤encodeCodeListWithRest
        (atom m ∷ˡ atom n ∷ˡ []ˡ)
        zero
        zero
        (≤-refl zero)))

rule37-right-witness≤childrenCode :
  {children-code m n : ℕ} →
  Rule37ChildrenCodeNat children-code m n →
  n ≤ children-code
rule37-right-witness≤childrenCode {children-code} {m} {n} children-eq =
  subst
    (λ code → n ≤ code)
    (sym children-eq)
    (≤-trans
      (≤-trans
        (tail-atom-payload≤codeListSize m n)
        (x≤x+y
          (codeListSize (atom m ∷ˡ atom n ∷ˡ []ˡ))
          zero))
      (codeListSize+base≤encodeCodeListWithRest
        (atom m ∷ˡ atom n ∷ˡ []ˡ)
        zero
        zero
        (≤-refl zero)))

rule37-childrenCode≤proofCode :
  {proof-code children-code : ℕ} →
  children-code ≡ evalPRF nodeChildrenF (proof-code ∷ []) →
  children-code ≤ proof-code
rule37-childrenCode≤proofCode {proof-code} {children-code} children-eq =
  subst
    (λ code → code ≤ proof-code)
    (sym children-eq)
    (nodeChildrenF-value≤input proof-code)

rule37NodeChildren-bounds :
  {proof-code children-code m n : ℕ} →
  Rule37NodeChildrenNat proof-code children-code m n →
  (m ≤ proof-code) × (n ≤ proof-code)
rule37NodeChildren-bounds
    {proof-code} {children-code} {m} {n}
    ((_ ,× (_ ,× children-eq)) ,× children-ok) =
  let children≤proof =
        rule37-childrenCode≤proofCode
          {proof-code = proof-code}
          {children-code = children-code}
          children-eq
  in
  ≤-trans
    (rule37-left-witness≤childrenCode
      {children-code = children-code}
      {m = m}
      {n = n}
      children-ok)
    children≤proof
  ,×
  ≤-trans
    (rule37-right-witness≤childrenCode
      {children-code = children-code}
      {m = m}
      {n = n}
      children-ok)
    children≤proof

rule37ParserWitness-bounds :
  {m n proof-code formula-code : ℕ} →
  Rule37ParserWitnessNat m n proof-code formula-code →
  (m ≤ proof-code) × (n ≤ proof-code)
rule37ParserWitness-bounds (_ ,× (node-children ,× _)) =
  rule37NodeChildren-bounds node-children

rule37ParserWitnessBoundsBridge :
  Rule37ParserWitnessBoundsBridge
rule37ParserWitnessBoundsBridge = record
  { parser-witness-bounds =
      rule37ParserWitness-bounds
  }
