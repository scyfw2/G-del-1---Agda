{-# OPTIONS --safe #-}

module Godel.ProofRule37CanonicalSearch where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.CanonicalCoding using (_≤_)
open import Godel.PrimitiveRecursive
  using
    ( PRF
    ; PRRel
    ; PRRel-holds
    ; Fin
    ; rel
    ; evalPRF
    ; zeroF
    ; sucF
    ; projF
    ; compF
    ; _∷_
    ; []
    )
open import Godel.PRBooleanHelpers using (andF; fin0; fin1; fin2; fin3)
open import Godel.PRBoundedSearch using (constF)
open import Godel.PRArithmeticSemantics
  using (andF-correct; constF-correct; mulNat)
open import Godel.PRBooleanSoundness
  using (and-output-sound; and-output-nonzero-sound; and3-output-sound)
open import Godel.CanonicalCodePR using (nodeChildrenF)
open import Godel.CanonicalCodeNodeTargets
  using
    ( CanonicalCodeNodeParserPR
    ; NodeCodeNat
    )
open import Godel.CanonicalCodeParserTargets using (args₃)
open import Godel.CanonicalCodeRawNodePR
  using (nodeCodeNat-to-rawNodeCodeNat)
open import Godel.ProofCheckingPR using (proofCodeArgs)
open import Godel.ProofCheckingRule37Branch
  using (ProofRule37CheckingBranchData)
open import Godel.ProofRuleFixedProofOr using (NonzeroNat)
open import Godel.ProofRule37SearchSkeleton
  using
    ( rule37HitValueFor
    ; rule37SearchFFor
    ; rule37SearchFFor-correct
    ; rule37SearchMMetaFor
    )
open import Godel.ProofRule37SearchCorrectness
  using
    ( search2UpTo
    ; search2UpTo-hit-bound
    ; search2UpTo-nonzero-sound
    )
open import Godel.ProofRule37NodeChildren
  using
    ( args₄
    ; rule37ChildrenCode-nonzero-sound
    )
open import Godel.ProofRule37Bounds
  using
    ( rule37-left-witness≤proofCode
    ; rule37-right-witness≤proofCode
    )
open import Godel.ProofRule37CanonicalBridge
  using
    ( Rule37CanonicalParserWitnessNat
    ; Rule37CanonicalNodeChildrenNat
    ; rule37CanonicalParserWitness-to-closedRule37
    ; rule37CanonicalNodeChildren-proofCode
    )
open import Godel.ProofRule37CanonicalWitness
  using
    ( Rule37CanonicalWitnessExists
    ; ProofRule37CanonicalWitnessSearchPR
    ; canonicalWitness-to-closedRule37
    ; proofRule37PR-from-canonical-witness-search
    )
open import Godel.ProofRuleTargets
  using
    ( ClosedNumeralNeqRuleNat
    ; closedNumeralNeqCode
    ; closedNumeralNeqFormula
    ; NatNeqNat
    ; ProofRule37PR
    ; ProofRule37PARepresentability
    ; Rule37ChildrenCodeNat
    ; rule37WitnessArgs
    ; rule37ChildrenArgs
    ; rule37ChildrenCodeF
    ; rule37ChildrenCode-complete
    ; rule37ChildrenCode-sound
    ; rule37FormulaCodeEqF
    ; rule37FormulaCodeEqF-complete
    ; rule37FormulaCodeEqF-sound
    ; rule37FormulaCodeEqF-nonzero-sound
    ; rule37NeqBranchF
    ; rule37NeqBranchF-complete
    ; rule37NeqBranchF-sound
    ; rule37NeqBranchF-nonzero-sound
    ; proofRule37PR-represented
    )

fin4 : {n : ℕ} → Fin (suc (suc (suc (suc (suc n)))))
fin4 = Godel.PrimitiveRecursive.fsuc fin3

-- Canonical bounded witness layer for rule 37.
--
-- The parser/search pipeline ultimately needs to search over m,n bounded by
-- the proof-code.  The canonical parser witness already contains enough
-- information to recover the legacy ClosedNumeralNeqRuleNat target, and that
-- target gives the required bounds.  This module packages that bridge without
-- pretending that the concrete bounded-search PRF has already been derived.

Rule37CanonicalBoundedWitnessExists : ℕ → ℕ → Set
Rule37CanonicalBoundedWitnessExists proof-code formula-code =
  Σ ℕ
    (λ m →
      Σ ℕ
        (λ n →
          ((m ≤ proof-code) × (n ≤ proof-code)) ×
          Rule37CanonicalParserWitnessNat
            m
            n
            proof-code
            formula-code))

canonicalParserWitness-bounds :
  {m n proof-code formula-code : ℕ} →
  Rule37CanonicalParserWitnessNat m n proof-code formula-code →
  (m ≤ proof-code) × (n ≤ proof-code)
canonicalParserWitness-bounds
    {m} {n} {proof-code}
    (_ ,× ((children-code ,Σ node-children) ,× _)) =
  let proof-eq =
        rule37CanonicalNodeChildren-proofCode
          {proof-code = proof-code}
          {children-code = children-code}
          {m = m}
          {n = n}
          node-children
  in
  rule37-left-witness≤proofCode
    {m = m}
    {n = n}
    {proof-code = proof-code}
    proof-eq
  ,×
  rule37-right-witness≤proofCode
    {m = m}
    {n = n}
    {proof-code = proof-code}
    proof-eq

canonicalWitness-to-bounded :
  {proof-code formula-code : ℕ} →
  Rule37CanonicalWitnessExists proof-code formula-code →
  Rule37CanonicalBoundedWitnessExists proof-code formula-code
canonicalWitness-to-bounded (m ,Σ (n ,Σ witness)) =
  m ,Σ
    (n ,Σ
      (canonicalParserWitness-bounds
        {m = m}
        {n = n}
        witness
       ,×
       witness))

boundedCanonicalWitness-to-canonical :
  {proof-code formula-code : ℕ} →
  Rule37CanonicalBoundedWitnessExists proof-code formula-code →
  Rule37CanonicalWitnessExists proof-code formula-code
boundedCanonicalWitness-to-canonical
    (m ,Σ (n ,Σ (_ ,× witness))) =
  m ,Σ (n ,Σ witness)

boundedCanonicalWitness-to-closedRule37 :
  {proof-code formula-code : ℕ} →
  Rule37CanonicalBoundedWitnessExists proof-code formula-code →
  ClosedNumeralNeqRuleNat proof-code formula-code
boundedCanonicalWitness-to-closedRule37 bounded =
  canonicalWitness-to-closedRule37
    (boundedCanonicalWitness-to-canonical bounded)

nodeCodeNat-children-value :
  {proof-code tag children-code : ℕ} →
  NodeCodeNat proof-code tag children-code →
  evalPRF nodeChildrenF (proof-code ∷ []) ≡ children-code
nodeCodeNat-children-value
    {proof-code} {tag} {children-code} node-code =
  sym
    (snd
      (snd
        (nodeCodeNat-to-rawNodeCodeNat
          {input = proof-code}
          {tag = tag}
          {children-code = children-code}
          node-code)))

NodeCodeNonzeroSound :
  CanonicalCodeNodeParserPR → Set
NodeCodeNonzeroSound Node =
  {input tag children-code : ℕ} →
  NonzeroNat
    (evalPRF
      (PRRel.characteristic
        (CanonicalCodeNodeParserPR.node-code-pr Node))
      (args₃ input tag children-code)) →
  NodeCodeNat input tag children-code

record CanonicalCodeNodeParserSearchData : Set₁ where
  field
    node-parser-pr :
      CanonicalCodeNodeParserPR

    node-code-nonzero-sound :
      NodeCodeNonzeroSound node-parser-pr

rule37CanonicalNodeChildrenF :
  CanonicalCodeNodeParserPR →
  PRF (suc (suc (suc (suc zero))))
rule37CanonicalNodeChildrenF Node =
  compF andF
    ( compF
      (PRRel.characteristic
        (CanonicalCodeNodeParserPR.node-code-pr Node))
      ( projF fin0 ∷
        constF 37 ∷
        projF fin1 ∷ []) ∷
      compF rule37ChildrenCodeF
      ( projF fin1 ∷
        projF fin2 ∷
        projF fin3 ∷ []) ∷ [])

rule37CanonicalNodeChildrenF-correct :
  (Node : CanonicalCodeNodeParserPR) →
  (proof-code children-code m n : ℕ) →
  evalPRF
    (rule37CanonicalNodeChildrenF Node)
    (args₄ proof-code children-code m n)
  ≡
  mulNat
    (evalPRF
      (PRRel.characteristic
        (CanonicalCodeNodeParserPR.node-code-pr Node))
      (args₃ proof-code 37 children-code))
    (evalPRF
      rule37ChildrenCodeF
      (rule37ChildrenArgs children-code m n))
rule37CanonicalNodeChildrenF-correct Node proof-code children-code m n
  rewrite constF-correct
            37
            (args₄ proof-code children-code m n)
        | andF-correct
            (evalPRF
              (PRRel.characteristic
                (CanonicalCodeNodeParserPR.node-code-pr Node))
              (args₃ proof-code 37 children-code))
            (evalPRF
              rule37ChildrenCodeF
              (rule37ChildrenArgs children-code m n)) =
  refl

rule37CanonicalNodeChildren-complete :
  (Node : CanonicalCodeNodeParserPR) →
  {proof-code children-code m n : ℕ} →
  Rule37CanonicalNodeChildrenNat proof-code children-code m n →
  PRRel-holds
    (rel (rule37CanonicalNodeChildrenF Node))
    (args₄ proof-code children-code m n)
rule37CanonicalNodeChildren-complete
    Node {proof-code} {children-code} {m} {n}
    (node-code ,× children-ok)
  rewrite rule37CanonicalNodeChildrenF-correct
            Node
            proof-code
            children-code
            m
            n
        | CanonicalCodeNodeParserPR.node-code-complete
            Node
            {input = proof-code}
            {tag = 37}
            {children-code = children-code}
            node-code
        | rule37ChildrenCode-complete
            {children-code = children-code}
            {m = m}
            {n = n}
            children-ok =
  refl

rule37CanonicalNodeChildren-sound :
  (Node : CanonicalCodeNodeParserPR) →
  {proof-code children-code m n : ℕ} →
  PRRel-holds
    (rel (rule37CanonicalNodeChildrenF Node))
    (args₄ proof-code children-code m n) →
  Rule37CanonicalNodeChildrenNat proof-code children-code m n
rule37CanonicalNodeChildren-sound
    Node {proof-code} {children-code} {m} {n} holds
  with and-output-sound
        (evalPRF
          (PRRel.characteristic
            (CanonicalCodeNodeParserPR.node-code-pr Node))
          (args₃ proof-code 37 children-code))
        (evalPRF
          rule37ChildrenCodeF
          (rule37ChildrenArgs children-code m n))
        (evalPRF
          (rule37CanonicalNodeChildrenF Node)
          (args₄ proof-code children-code m n))
        (rule37CanonicalNodeChildrenF-correct
          Node
          proof-code
          children-code
          m
          n)
        holds
... | node-one ,× children-one =
  CanonicalCodeNodeParserPR.node-code-sound
    Node
    {input = proof-code}
    {tag = 37}
    {children-code = children-code}
    node-one
  ,×
  rule37ChildrenCode-sound
    {children-code = children-code}
    {m = m}
    {n = n}
    children-one

rule37CanonicalNodeChildren-nonzero-sound :
  (Node : CanonicalCodeNodeParserPR) →
  NodeCodeNonzeroSound Node →
  {proof-code children-code m n : ℕ} →
  NonzeroNat
    (evalPRF
      (rule37CanonicalNodeChildrenF Node)
      (args₄ proof-code children-code m n)) →
  Rule37CanonicalNodeChildrenNat proof-code children-code m n
rule37CanonicalNodeChildren-nonzero-sound
    Node node-nonzero-sound
    {proof-code} {children-code} {m} {n} nonzero
  with and-output-nonzero-sound
        (evalPRF
          (PRRel.characteristic
            (CanonicalCodeNodeParserPR.node-code-pr Node))
          (args₃ proof-code 37 children-code))
        (evalPRF
          rule37ChildrenCodeF
          (rule37ChildrenArgs children-code m n))
        (evalPRF
          (rule37CanonicalNodeChildrenF Node)
          (args₄ proof-code children-code m n))
        (rule37CanonicalNodeChildrenF-correct
          Node
          proof-code
          children-code
          m
          n)
        nonzero
... | node-nz ,× children-nz =
  node-nonzero-sound
    {input = proof-code}
    {tag = 37}
    {children-code = children-code}
    node-nz
  ,×
  rule37ChildrenCode-nonzero-sound
    {children-code = children-code}
    {m = m}
    {n = n}
    children-nz

rule37CanonicalNodeChildrenBranchF :
  CanonicalCodeNodeParserPR →
  PRF (suc (suc (suc (suc zero))))
rule37CanonicalNodeChildrenBranchF Node =
  compF (rule37CanonicalNodeChildrenF Node)
    ( projF fin2 ∷
      compF nodeChildrenF (projF fin2 ∷ []) ∷
      projF fin0 ∷
      projF fin1 ∷ [])

rule37CanonicalFormulaBranchF :
  PRF (suc (suc (suc (suc zero))))
rule37CanonicalFormulaBranchF =
  rule37FormulaCodeEqF

rule37CanonicalNeqBranchF :
  PRF (suc (suc (suc (suc zero))))
rule37CanonicalNeqBranchF =
  rule37NeqBranchF

rule37CanonicalInnerWitnessF :
  PRF (suc (suc (suc (suc zero))))
rule37CanonicalInnerWitnessF =
  compF andF
    (rule37CanonicalFormulaBranchF ∷
     rule37CanonicalNeqBranchF ∷ [])

rule37CanonicalWitnessF :
  CanonicalCodeNodeParserPR →
  PRF (suc (suc (suc (suc zero))))
rule37CanonicalWitnessF Node =
  compF andF
    (rule37CanonicalNodeChildrenBranchF Node ∷
     rule37CanonicalInnerWitnessF ∷ [])

rule37CanonicalWitnessF-correct-flat :
  (Node : CanonicalCodeNodeParserPR) →
  (m n proof-code formula-code : ℕ) →
  evalPRF
    (rule37CanonicalWitnessF Node)
    (rule37WitnessArgs m n proof-code formula-code)
  ≡
  mulNat
    (evalPRF
      (rule37CanonicalNodeChildrenF Node)
      (args₄
        proof-code
        (evalPRF nodeChildrenF (proof-code ∷ []))
        m
        n))
    (mulNat
      (evalPRF
        rule37FormulaCodeEqF
        (rule37WitnessArgs m n proof-code formula-code))
      (evalPRF
        rule37NeqBranchF
        (rule37WitnessArgs m n proof-code formula-code)))
rule37CanonicalWitnessF-correct-flat Node m n proof-code formula-code
  rewrite andF-correct
            (evalPRF
              (rule37CanonicalNodeChildrenBranchF Node)
              (rule37WitnessArgs m n proof-code formula-code))
            (evalPRF
              rule37CanonicalInnerWitnessF
              (rule37WitnessArgs m n proof-code formula-code))
        | andF-correct
            (evalPRF
              rule37FormulaCodeEqF
              (rule37WitnessArgs m n proof-code formula-code))
            (evalPRF
              rule37NeqBranchF
              (rule37WitnessArgs m n proof-code formula-code)) =
  refl

rule37CanonicalWitness-complete :
  (Node : CanonicalCodeNodeParserPR) →
  {m n proof-code formula-code : ℕ} →
  Rule37CanonicalParserWitnessNat m n proof-code formula-code →
  PRRel-holds
    (rel (rule37CanonicalWitnessF Node))
    (rule37WitnessArgs m n proof-code formula-code)
rule37CanonicalWitness-complete
    Node {m} {n} {proof-code} {formula-code}
    (neq ,× ((children-code ,Σ (node-code ,× children-ok)) ,× formula-eq))
  rewrite nodeCodeNat-children-value
            {proof-code = proof-code}
            {tag = 37}
            {children-code = children-code}
            node-code
        | rule37CanonicalWitnessF-correct-flat
            Node
            m
            n
            proof-code
            formula-code
        | rule37CanonicalNodeChildren-complete
            Node
            {proof-code = proof-code}
            {children-code = children-code}
            {m = m}
            {n = n}
            (node-code ,× children-ok)
        | rule37FormulaCodeEqF-complete
            {m = m}
            {n = n}
            {proof-code = proof-code}
            {formula-code = formula-code}
            formula-eq
        | rule37NeqBranchF-complete
            {m = m}
            {n = n}
            {proof-code = proof-code}
            {formula-code = formula-code}
            neq =
  refl

rule37CanonicalWitness-sound :
  (Node : CanonicalCodeNodeParserPR) →
  {m n proof-code formula-code : ℕ} →
  PRRel-holds
    (rel (rule37CanonicalWitnessF Node))
    (rule37WitnessArgs m n proof-code formula-code) →
  Rule37CanonicalParserWitnessNat m n proof-code formula-code
rule37CanonicalWitness-sound
    Node {m} {n} {proof-code} {formula-code} holds
  with and3-output-sound
        (evalPRF
          (rule37CanonicalNodeChildrenF Node)
          (args₄
            proof-code
            (evalPRF nodeChildrenF (proof-code ∷ []))
            m
            n))
        (evalPRF
          rule37FormulaCodeEqF
          (rule37WitnessArgs m n proof-code formula-code))
        (evalPRF
          rule37NeqBranchF
          (rule37WitnessArgs m n proof-code formula-code))
        (evalPRF
          (rule37CanonicalWitnessF Node)
          (rule37WitnessArgs m n proof-code formula-code))
        (rule37CanonicalWitnessF-correct-flat
          Node
          m
          n
          proof-code
          formula-code)
        holds
... | node-children-one ,× (formula-one ,× neq-one) =
  rule37NeqBranchF-sound
    {m = m}
    {n = n}
    {proof-code = proof-code}
    {formula-code = formula-code}
    neq-one
  ,×
  ( (evalPRF nodeChildrenF (proof-code ∷ []) ,Σ
      rule37CanonicalNodeChildren-sound
        Node
        {proof-code = proof-code}
        {children-code = evalPRF nodeChildrenF (proof-code ∷ [])}
        {m = m}
        {n = n}
        node-children-one)
    ,×
    rule37FormulaCodeEqF-sound
      {m = m}
      {n = n}
      {proof-code = proof-code}
      {formula-code = formula-code}
      formula-one)

rule37CanonicalWitness-nonzero-sound :
  (Node : CanonicalCodeNodeParserPR) →
  NodeCodeNonzeroSound Node →
  {m n proof-code formula-code : ℕ} →
  NonzeroNat
    (evalPRF
      (rule37CanonicalWitnessF Node)
      (rule37WitnessArgs m n proof-code formula-code)) →
  Rule37CanonicalParserWitnessNat m n proof-code formula-code
rule37CanonicalWitness-nonzero-sound
    Node node-nonzero-sound
    {m} {n} {proof-code} {formula-code} nonzero
  with and-output-nonzero-sound
        (evalPRF
          (rule37CanonicalNodeChildrenF Node)
          (args₄
            proof-code
            (evalPRF nodeChildrenF (proof-code ∷ []))
            m
            n))
        (mulNat
          (evalPRF
            rule37FormulaCodeEqF
            (rule37WitnessArgs m n proof-code formula-code))
          (evalPRF
            rule37NeqBranchF
            (rule37WitnessArgs m n proof-code formula-code)))
        (evalPRF
          (rule37CanonicalWitnessF Node)
          (rule37WitnessArgs m n proof-code formula-code))
        (rule37CanonicalWitnessF-correct-flat
          Node
          m
          n
          proof-code
          formula-code)
        nonzero
... | node-children-nz ,× inner-nz
  with and-output-nonzero-sound
        (evalPRF
          rule37FormulaCodeEqF
          (rule37WitnessArgs m n proof-code formula-code))
        (evalPRF
          rule37NeqBranchF
          (rule37WitnessArgs m n proof-code formula-code))
        (mulNat
          (evalPRF
            rule37FormulaCodeEqF
            (rule37WitnessArgs m n proof-code formula-code))
          (evalPRF
            rule37NeqBranchF
            (rule37WitnessArgs m n proof-code formula-code)))
        refl
        inner-nz
... | formula-nz ,× neq-nz =
  rule37NeqBranchF-nonzero-sound
    {m = m}
    {n = n}
    {proof-code = proof-code}
    {formula-code = formula-code}
    neq-nz
  ,×
  ( (evalPRF nodeChildrenF (proof-code ∷ []) ,Σ
      rule37CanonicalNodeChildren-nonzero-sound
        Node
        node-nonzero-sound
        {proof-code = proof-code}
        {children-code = evalPRF nodeChildrenF (proof-code ∷ [])}
        {m = m}
        {n = n}
        node-children-nz)
    ,×
    rule37FormulaCodeEqF-nonzero-sound
      {m = m}
      {n = n}
      {proof-code = proof-code}
      {formula-code = formula-code}
      formula-nz)

rule37CanonicalSearchF :
  CanonicalCodeNodeParserPR →
  PRF (suc (suc zero))
rule37CanonicalSearchF Node =
  rule37SearchFFor (rule37CanonicalWitnessF Node)

rule37CanonicalSearchPR :
  CanonicalCodeNodeParserPR →
  PRRel (suc (suc zero))
rule37CanonicalSearchPR Node =
  rel (rule37CanonicalSearchF Node)

rule37CanonicalSearchMMeta :
  CanonicalCodeNodeParserPR →
  ℕ → ℕ → ℕ → ℕ
rule37CanonicalSearchMMeta Node =
  rule37SearchMMetaFor (rule37CanonicalWitnessF Node)

rule37CanonicalSearchMMeta-as-search2 :
  (Node : CanonicalCodeNodeParserPR) →
  (proof-code formula-code : ℕ) →
  rule37CanonicalSearchMMeta Node proof-code proof-code formula-code ≡
  search2UpTo
    (λ m n →
      rule37HitValueFor
        (rule37CanonicalWitnessF Node)
        m
        n
        proof-code
        formula-code)
    proof-code
    proof-code
rule37CanonicalSearchMMeta-as-search2 Node proof-code formula-code =
  refl

rule37CanonicalSearch-complete :
  (Node : CanonicalCodeNodeParserPR) →
  {proof-code formula-code : ℕ} →
  Rule37CanonicalBoundedWitnessExists proof-code formula-code →
  PRRel-holds
    (rule37CanonicalSearchPR Node)
    (proofCodeArgs proof-code formula-code)
rule37CanonicalSearch-complete
    Node {proof-code} {formula-code}
    (m ,Σ (n ,Σ ((m≤proof ,× n≤proof) ,× witness)))
  rewrite rule37SearchFFor-correct
            (rule37CanonicalWitnessF Node)
            proof-code
            formula-code
        | rule37CanonicalSearchMMeta-as-search2
            Node
            proof-code
            formula-code =
  search2UpTo-hit-bound
    {P =
      λ current-m current-n →
        rule37HitValueFor
          (rule37CanonicalWitnessF Node)
          current-m
          current-n
          proof-code
          formula-code}
    {outer-bound = proof-code}
    {inner-bound = proof-code}
    (m ,Σ
      (n ,Σ
        ((m≤proof ,× n≤proof) ,×
         rule37CanonicalWitness-complete
          Node
          {m = m}
          {n = n}
          {proof-code = proof-code}
          {formula-code = formula-code}
          witness)))

rule37CanonicalSearch-nonzero-sound :
  (Node : CanonicalCodeNodeParserPR) →
  NodeCodeNonzeroSound Node →
  {proof-code formula-code : ℕ} →
  NonzeroNat
    (evalPRF
      (rule37CanonicalSearchF Node)
      (proofCodeArgs proof-code formula-code)) →
  Rule37CanonicalBoundedWitnessExists proof-code formula-code
rule37CanonicalSearch-nonzero-sound
    Node node-nonzero-sound
    {proof-code} {formula-code} nonzero
  rewrite rule37SearchFFor-correct
            (rule37CanonicalWitnessF Node)
            proof-code
            formula-code
        | rule37CanonicalSearchMMeta-as-search2
            Node
            proof-code
            formula-code
  with search2UpTo-nonzero-sound
        {P =
          λ current-m current-n →
            rule37HitValueFor
              (rule37CanonicalWitnessF Node)
              current-m
              current-n
              proof-code
              formula-code}
        proof-code
        proof-code
        nonzero
... | m ,Σ (n ,Σ (bounds ,× hit-nonzero)) =
  m ,Σ
    (n ,Σ
      (bounds ,×
       rule37CanonicalWitness-nonzero-sound
        Node
        node-nonzero-sound
        {m = m}
        {n = n}
        {proof-code = proof-code}
        {formula-code = formula-code}
        hit-nonzero))

rule37CanonicalSearch-sound :
  (Node : CanonicalCodeNodeParserPR) →
  NodeCodeNonzeroSound Node →
  {proof-code formula-code : ℕ} →
  PRRel-holds
    (rule37CanonicalSearchPR Node)
    (proofCodeArgs proof-code formula-code) →
  Rule37CanonicalBoundedWitnessExists proof-code formula-code
rule37CanonicalSearch-sound Node node-nonzero-sound holds =
  rule37CanonicalSearch-nonzero-sound
    Node
    node-nonzero-sound
    (zero ,Σ holds)

-- Abstract interface for the eventual bounded canonical witness search.
-- A concrete implementation should instantiate this with a PR relation that
-- searches only m,n <= proof-code and checks the canonical parser witness.

record ProofRule37CanonicalBoundedSearchPR : Set₁ where
  field
    rule37-canonical-bounded-search-pr :
      PRRel (suc (suc zero))

    rule37-canonical-bounded-search-complete :
      {proof-code formula-code : ℕ} →
      Rule37CanonicalBoundedWitnessExists proof-code formula-code →
      PRRel-holds
        rule37-canonical-bounded-search-pr
        (proofCodeArgs proof-code formula-code)

    rule37-canonical-bounded-search-sound :
      {proof-code formula-code : ℕ} →
      PRRel-holds
        rule37-canonical-bounded-search-pr
        (proofCodeArgs proof-code formula-code) →
      Rule37CanonicalBoundedWitnessExists proof-code formula-code

canonicalBoundedSearch-to-witness-search :
  ProofRule37CanonicalBoundedSearchPR →
  ProofRule37CanonicalWitnessSearchPR
canonicalBoundedSearch-to-witness-search D = record
  { rule37-canonical-search-pr =
      ProofRule37CanonicalBoundedSearchPR.rule37-canonical-bounded-search-pr D
  ; rule37-canonical-search-complete =
      λ {proof-code} {formula-code} witness →
        ProofRule37CanonicalBoundedSearchPR.rule37-canonical-bounded-search-complete
          D
          {proof-code}
          {formula-code}
          (canonicalWitness-to-bounded witness)
  ; rule37-canonical-search-sound =
      λ {proof-code} {formula-code} holds →
        boundedCanonicalWitness-to-canonical
          (ProofRule37CanonicalBoundedSearchPR.rule37-canonical-bounded-search-sound
            D
            {proof-code}
            {formula-code}
            holds)
  }

proofRule37PR-from-canonical-bounded-search :
  ProofRule37CanonicalBoundedSearchPR →
  ProofRule37PR
proofRule37PR-from-canonical-bounded-search D =
  proofRule37PR-from-canonical-witness-search
    (canonicalBoundedSearch-to-witness-search D)

proofRule37CanonicalBoundedSearchPR-represented :
  (D : ProofRule37CanonicalBoundedSearchPR) →
  ProofRule37PARepresentability
    (proofRule37PR-from-canonical-bounded-search D)
proofRule37CanonicalBoundedSearchPR-represented D =
  proofRule37PR-represented
    (proofRule37PR-from-canonical-bounded-search D)

record ProofRule37CanonicalCheckingBranchData : Set₁ where
  field
    canonical-bounded-search-data :
      ProofRule37CanonicalBoundedSearchPR

    canonical-bounded-search-nonzero-sound :
      {proof-code formula-code : ℕ} →
      NonzeroNat
        (evalPRF
          (PRRel.characteristic
            (ProofRule37CanonicalBoundedSearchPR.rule37-canonical-bounded-search-pr
              canonical-bounded-search-data))
          (proofCodeArgs proof-code formula-code)) →
      Rule37CanonicalBoundedWitnessExists proof-code formula-code

proofRule37CanonicalBoundedSearchPR-from-node-parser :
  CanonicalCodeNodeParserSearchData →
  ProofRule37CanonicalBoundedSearchPR
proofRule37CanonicalBoundedSearchPR-from-node-parser NodeData = record
  { rule37-canonical-bounded-search-pr =
      rule37CanonicalSearchPR Node
  ; rule37-canonical-bounded-search-complete =
      λ {proof-code} {formula-code} →
        rule37CanonicalSearch-complete
          Node
          {proof-code}
          {formula-code}
  ; rule37-canonical-bounded-search-sound =
      λ {proof-code} {formula-code} →
        rule37CanonicalSearch-sound
          Node
          node-nonzero-sound
          {proof-code}
          {formula-code}
  }
  where
    Node : CanonicalCodeNodeParserPR
    Node = CanonicalCodeNodeParserSearchData.node-parser-pr NodeData

    node-nonzero-sound : NodeCodeNonzeroSound Node
    node-nonzero-sound =
      CanonicalCodeNodeParserSearchData.node-code-nonzero-sound NodeData

proofRule37CanonicalCheckingBranchData-from-node-parser :
  CanonicalCodeNodeParserSearchData →
  ProofRule37CanonicalCheckingBranchData
proofRule37CanonicalCheckingBranchData-from-node-parser NodeData = record
  { canonical-bounded-search-data =
      proofRule37CanonicalBoundedSearchPR-from-node-parser NodeData
  ; canonical-bounded-search-nonzero-sound =
      λ {proof-code} {formula-code} →
        rule37CanonicalSearch-nonzero-sound
          Node
          node-nonzero-sound
          {proof-code}
          {formula-code}
  }
  where
    Node : CanonicalCodeNodeParserPR
    Node = CanonicalCodeNodeParserSearchData.node-parser-pr NodeData

    node-nonzero-sound : NodeCodeNonzeroSound Node
    node-nonzero-sound =
      CanonicalCodeNodeParserSearchData.node-code-nonzero-sound NodeData

proofRule37CheckingBranchData-from-canonical-bounded-search :
  ProofRule37CanonicalCheckingBranchData →
  ProofRule37CheckingBranchData
proofRule37CheckingBranchData-from-canonical-bounded-search D = record
  { rule37-pr-data =
      proofRule37PR-from-canonical-bounded-search
        (ProofRule37CanonicalCheckingBranchData.canonical-bounded-search-data
          D)
  ; rule37-nonzero-sound =
      λ {proof-code} {formula-code} nonzero →
        boundedCanonicalWitness-to-closedRule37
          (ProofRule37CanonicalCheckingBranchData.canonical-bounded-search-nonzero-sound
            D
            {proof-code}
            {formula-code}
            nonzero)
  }
