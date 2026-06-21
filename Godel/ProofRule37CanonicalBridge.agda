{-# OPTIONS --safe #-}

module Godel.ProofRule37CanonicalBridge where

open import Agda.Builtin.List using (List) renaming ([] to []ˡ; _∷_ to _∷ˡ_)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.CanonicalCoding
  using
    ( Code
    ; atom
    ; node
    ; encodeCode
    ; encodeCodeListWithRest
    ; canonicalNatFormula
    )
open import Godel.CanonicalCodeNodeTargets
  using (NodeCodeNat)
open import Godel.CanonicalCodeParserSemantics
  using
    ( parseCodeList
    ; parseCodeList-canonical
    )
open import Godel.ProofRuleTargets
  using
    ( ClosedNumeralNeqRuleNat
    ; NatNeqNat
    ; Rule37ChildrenCodeNat
    ; closedNumeralNeqCode
    ; closedNumeralNeqFormula
    )

-- Bridge from a full canonical node/list parser target back to the legacy
-- ClosedNumeralNeqRuleNat semantic target.
--
-- The raw parser branch used by the lightweight rule-37 search only exposes
-- nodeTagF/nodeChildrenF values.  That is enough for search bounds and parser
-- search correctness, but not enough to reconstruct canonical proof-code
-- equality.  This module records the stronger bridge needed by the final
-- ProofRule37PR branch: once the outer node parser is the full canonical
-- NodeCodeNat target, and the children-code is the canonical two-atom list,
-- the legacy closed-rule target follows.

just-pair-fst-injective :
  {A B : Set} → {x y : A} → {u v : B} →
  just (x ,× u) ≡ just (y ,× v) →
  x ≡ y
just-pair-fst-injective refl = refl

encodeCodeListWithRest-zero-injective :
  (xs ys : List Code) →
  encodeCodeListWithRest xs zero ≡
  encodeCodeListWithRest ys zero →
  xs ≡ ys
encodeCodeListWithRest-zero-injective xs ys eq =
  just-pair-fst-injective
    (trans
      (sym (parseCodeList-canonical xs))
      (trans
        (cong parseCodeList eq)
        (parseCodeList-canonical ys)))

Rule37CanonicalNodeChildrenNat :
  ℕ → ℕ → ℕ → ℕ → Set
Rule37CanonicalNodeChildrenNat proof-code children-code m n =
  NodeCodeNat proof-code 37 children-code ×
  Rule37ChildrenCodeNat children-code m n

rule37CanonicalNodeChildren-proofCode :
  {proof-code children-code m n : ℕ} →
  Rule37CanonicalNodeChildrenNat proof-code children-code m n →
  proof-code ≡ closedNumeralNeqCode m n
rule37CanonicalNodeChildren-proofCode
    {proof-code} {children-code} {m} {n}
    ((children ,Σ (proof-eq ,× children-code-eq)) ,× children-ok) =
  trans
    proof-eq
    (cong
      (λ cs → encodeCode (node 37 cs))
      (encodeCodeListWithRest-zero-injective
        children
        (atom m ∷ˡ atom n ∷ˡ []ˡ)
        (trans (sym children-code-eq) children-ok)))

Rule37CanonicalParserWitnessNat :
  ℕ → ℕ → ℕ → ℕ → Set
Rule37CanonicalParserWitnessNat m n proof-code formula-code =
  NatNeqNat m n ×
  (Σ ℕ
    (λ children-code →
      Rule37CanonicalNodeChildrenNat proof-code children-code m n) ×
   (formula-code ≡ canonicalNatFormula (closedNumeralNeqFormula m n)))

rule37CanonicalParserWitness-to-closedRule37 :
  {m n proof-code formula-code : ℕ} →
  Rule37CanonicalParserWitnessNat m n proof-code formula-code →
  ClosedNumeralNeqRuleNat proof-code formula-code
rule37CanonicalParserWitness-to-closedRule37
    {m} {n} {proof-code} {formula-code}
    (neq ,× ((children-code ,Σ node-children) ,× formula-eq)) =
  m ,Σ
    (n ,Σ
      (neq ,×
       ( rule37CanonicalNodeChildren-proofCode
           {proof-code = proof-code}
           {children-code = children-code}
           {m = m}
           {n = n}
           node-children
       ,×
         formula-eq )))
