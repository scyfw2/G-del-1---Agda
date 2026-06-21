{-# OPTIONS --safe #-}

module Godel.ProofRule37CanonicalWitness where

open import Agda.Builtin.List renaming ([] to []ˡ; _∷_ to _∷ˡ_)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.PrimitiveRecursive
  using (PRRel; PRRel-holds)
open import Godel.CanonicalCoding
  using
    ( atom
    ; encodeCodeListWithRest
    )
open import Godel.CanonicalCodeNodeTargets
  using (nodeCodeNat-complete)
open import Godel.ProofCheckingPR
  using (proofCodeArgs)
open import Godel.ProofRule37CanonicalBridge
  using
    ( Rule37CanonicalParserWitnessNat
    ; Rule37CanonicalNodeChildrenNat
    ; rule37CanonicalParserWitness-to-closedRule37
    )
open import Godel.ProofRuleTargets
  using
    ( ClosedNumeralNeqRuleNat
    ; ProofRule37PARepresentability
    ; ProofRule37PR
    ; Rule37ChildrenCodeNat
    ; closedNumeralNeqCode
    ; closedNumeralNeqFormula
    ; proofRule37PR-represented
    )

-- Canonical semantic witness target for rule 37.
--
-- The parser-search layer currently has a raw witness target.  For the final
-- ProofRule37PR branch we need the stronger target based on full canonical
-- node/list parsing; this module proves that target is exactly strong enough
-- to recover the legacy ClosedNumeralNeqRuleNat relation.

twoAtomChildrenCode : ℕ → ℕ → ℕ
twoAtomChildrenCode m n =
  encodeCodeListWithRest (atom m ∷ˡ atom n ∷ˡ []ˡ) zero

rule37CanonicalNodeChildren-canonical :
  (m n : ℕ) →
  Rule37CanonicalNodeChildrenNat
    (closedNumeralNeqCode m n)
    (twoAtomChildrenCode m n)
    m
    n
rule37CanonicalNodeChildren-canonical m n =
  nodeCodeNat-complete 37 (atom m ∷ˡ atom n ∷ˡ []ˡ)
  ,×
  refl

Rule37CanonicalWitnessExists : ℕ → ℕ → Set
Rule37CanonicalWitnessExists proof-code formula-code =
  Σ ℕ
    (λ m →
      Σ ℕ
        (λ n →
          Rule37CanonicalParserWitnessNat
            m
            n
            proof-code
            formula-code))

closedRule37-to-canonicalWitness :
  {proof-code formula-code : ℕ} →
  ClosedNumeralNeqRuleNat proof-code formula-code →
  Rule37CanonicalWitnessExists proof-code formula-code
closedRule37-to-canonicalWitness
    {proof-code} {formula-code}
    (m ,Σ (n ,Σ (neq ,× (proof-eq ,× formula-eq))))
  rewrite proof-eq =
  m ,Σ
    (n ,Σ
      (neq ,×
       ((twoAtomChildrenCode m n ,Σ
          rule37CanonicalNodeChildren-canonical m n)
        ,×
        formula-eq)))

canonicalWitness-to-closedRule37 :
  {proof-code formula-code : ℕ} →
  Rule37CanonicalWitnessExists proof-code formula-code →
  ClosedNumeralNeqRuleNat proof-code formula-code
canonicalWitness-to-closedRule37
    (m ,Σ (n ,Σ witness)) =
  rule37CanonicalParserWitness-to-closedRule37
    {m = m}
    {n = n}
    witness

record ProofRule37CanonicalWitnessSearchPR : Set₁ where
  field
    rule37-canonical-search-pr :
      PRRel (suc (suc zero))

    rule37-canonical-search-complete :
      {proof-code formula-code : ℕ} →
      Rule37CanonicalWitnessExists proof-code formula-code →
      PRRel-holds
        rule37-canonical-search-pr
        (proofCodeArgs proof-code formula-code)

    rule37-canonical-search-sound :
      {proof-code formula-code : ℕ} →
      PRRel-holds
        rule37-canonical-search-pr
        (proofCodeArgs proof-code formula-code) →
      Rule37CanonicalWitnessExists proof-code formula-code

proofRule37PR-from-canonical-witness-search :
  ProofRule37CanonicalWitnessSearchPR →
  ProofRule37PR
proofRule37PR-from-canonical-witness-search D = record
  { rule37-pr =
      ProofRule37CanonicalWitnessSearchPR.rule37-canonical-search-pr D
  ; rule37-complete =
      λ {proof-code} {formula-code} rule37 →
        ProofRule37CanonicalWitnessSearchPR.rule37-canonical-search-complete D
          {proof-code}
          {formula-code}
          (closedRule37-to-canonicalWitness rule37)
  ; rule37-sound =
      λ {proof-code} {formula-code} holds →
        canonicalWitness-to-closedRule37
          (ProofRule37CanonicalWitnessSearchPR.rule37-canonical-search-sound D
            {proof-code}
            {formula-code}
            holds)
  }

proofRule37CanonicalWitnessSearchPR-represented :
  (D : ProofRule37CanonicalWitnessSearchPR) →
  ProofRule37PARepresentability
    (proofRule37PR-from-canonical-witness-search D)
proofRule37CanonicalWitnessSearchPR-represented D =
  proofRule37PR-represented
    (proofRule37PR-from-canonical-witness-search D)
