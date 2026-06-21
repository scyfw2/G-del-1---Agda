{-# OPTIONS --safe #-}

module Godel.CanonicalCodeNodeParserFromListLength where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.CanonicalCoding
  using
    ( Code
    ; node
    ; encodeCode
    ; encodeCodeListWithRest
    ; encodeNatWithRest
    ; appendDigit
    ; d1
    ; codeListSize
    ; _≤_
    ; ≤-refl
    ; ≤-zero
    ; ≤-suc
    ; ≤-trans
    ; +-zeroʳ
    ; codeListSize+base≤encodeCodeListWithRest
    ; +-comm
    )
open import Godel.PrimitiveRecursive
open import Godel.PRBooleanHelpers using (orF; andF; eqNatF; fin0; fin1; fin2)
open import Godel.PRArithmeticSemantics
  using (orF-correct; andF-correct; eqNatF-correct; eqNatNat; mulNat)
open import Godel.PRBooleanSoundness
  using (and-output-sound; and-output-nonzero-sound)
open import Godel.CanonicalCodePR
  using
    ( nodeCodeWithRestF
    ; nodeCodeWithRestF-correct
    ; eqNatNat-refl-code
    ; eqNatNat-sound-code
    )
open import Godel.CanonicalCodeParserTargets
  using
    ( args₂
    ; args₃
    ; codeListLength
    ; CodeListLengthNat
    ; CanonicalCodeParserPR
    )
open import Godel.CanonicalCodeNodeTargets
  using
    ( NodeCodeNat
    ; CanonicalCodeNodeParserPR
    )
open import Godel.ProofRule37Search
  using
    ( searchUpTo
    ; orNat
    )
open import Godel.ProofRule37SearchCorrectness
  using
    ( NonzeroNat
    ; searchUpTo-hit-bound
    ; searchUpTo-nonzero-sound
    )
open import Godel.ProofRuleTargets
  using (eqNatNat-nonzero-sound-code)

-- Full node parsing can be reduced to two numeric checks:
--
--   1. input is exactly the node-code builder applied to tag and children-code;
--   2. children-code is a valid canonical code-list at rest 0.
--
-- The second check is implemented by bounded search over the represented
-- code-list-length relation.  This avoids using the raw node destructors as a
-- proof of well-formedness: raw destructors can read tag/children fields from
-- malformed node-shaped digit streams, while NodeCodeNat requires a genuine
-- canonical children list.

CodeListLengthNonzeroSound :
  CanonicalCodeParserPR → Set
CodeListLengthNonzeroSound Parser =
  {list-code len : ℕ} →
  NonzeroNat
    (evalPRF
      (PRRel.characteristic
        (CanonicalCodeParserPR.code-list-length-pr Parser))
      (args₂ list-code len)) →
  CodeListLengthNat list-code len

y≤x+y : (x y : ℕ) → y ≤ x + y
y≤x+y x y = x ,Σ +-comm x y

codeListLength≤codeListSize :
  (codes : List Code) →
  codeListLength codes ≤ codeListSize codes
codeListLength≤codeListSize [] =
  ≤-refl zero
codeListLength≤codeListSize (head ∷ tail) =
  ≤-suc
    (≤-trans
      (codeListLength≤codeListSize tail)
      (y≤x+y (Godel.CanonicalCoding.codeSize head) (codeListSize tail)))

codeListLength≤listCode :
  {list-code : ℕ} → (codes : List Code) →
  list-code ≡ encodeCodeListWithRest codes zero →
  codeListLength codes ≤ list-code
codeListLength≤listCode {list-code} codes list-eq =
  subst
    (λ code → codeListLength codes ≤ code)
    (sym list-eq)
    (≤-trans
      (codeListLength≤codeListSize codes)
      (subst
        (λ size → size ≤ encodeCodeListWithRest codes zero)
        (+-zeroʳ (codeListSize codes))
        (codeListSize+base≤encodeCodeListWithRest
          codes
          zero
          zero
          (≤-refl zero))))

codeListLengthSearchBaseF :
  CanonicalCodeParserPR →
  PRF (suc zero)
codeListLengthSearchBaseF Parser =
  compF
    (PRRel.characteristic
      (CanonicalCodeParserPR.code-list-length-pr Parser))
    (projF fin0 ∷ zeroF ∷ [])

codeListLengthSearchStepF :
  CanonicalCodeParserPR →
  PRF (suc (suc (suc zero)))
codeListLengthSearchStepF Parser =
  compF orF
    (projF fin1 ∷
     compF
      (PRRel.characteristic
        (CanonicalCodeParserPR.code-list-length-pr Parser))
      (projF fin2 ∷
       compF sucF (projF fin0 ∷ []) ∷ []) ∷ [])

codeListLengthSearchF :
  CanonicalCodeParserPR →
  PRF (suc (suc zero))
codeListLengthSearchF Parser =
  precF
    (codeListLengthSearchBaseF Parser)
    (codeListLengthSearchStepF Parser)

codeListValidF :
  CanonicalCodeParserPR →
  PRF (suc zero)
codeListValidF Parser =
  compF
    (codeListLengthSearchF Parser)
    (projF fin0 ∷ projF fin0 ∷ [])

codeListLengthSearchMeta :
  CanonicalCodeParserPR →
  ℕ → ℕ → ℕ
codeListLengthSearchMeta Parser bound list-code =
  searchUpTo
    (λ len →
      evalPRF
        (PRRel.characteristic
          (CanonicalCodeParserPR.code-list-length-pr Parser))
        (args₂ list-code len))
    bound

codeListLengthSearchF-correct :
  (Parser : CanonicalCodeParserPR) →
  (bound list-code : ℕ) →
  evalPRF
    (codeListLengthSearchF Parser)
    (bound ∷ list-code ∷ [])
  ≡ codeListLengthSearchMeta Parser bound list-code
codeListLengthSearchF-correct Parser zero list-code = refl
codeListLengthSearchF-correct Parser (suc bound) list-code
  rewrite codeListLengthSearchF-correct Parser bound list-code
        | orF-correct
            (codeListLengthSearchMeta Parser bound list-code)
            (evalPRF
              (PRRel.characteristic
                (CanonicalCodeParserPR.code-list-length-pr Parser))
              (args₂ list-code (suc bound))) =
  refl

codeListValidF-correct :
  (Parser : CanonicalCodeParserPR) →
  (list-code : ℕ) →
  evalPRF (codeListValidF Parser) (list-code ∷ []) ≡
  codeListLengthSearchMeta Parser list-code list-code
codeListValidF-correct Parser list-code =
  codeListLengthSearchF-correct Parser list-code list-code

codeListValid-complete :
  (Parser : CanonicalCodeParserPR) →
  {list-code len : ℕ} →
  len ≤ list-code →
  CodeListLengthNat list-code len →
  evalPRF (codeListValidF Parser) (list-code ∷ []) ≡ suc zero
codeListValid-complete Parser {list-code} {len} len≤list-code length-nat
  rewrite codeListValidF-correct Parser list-code =
  searchUpTo-hit-bound
    {P =
      λ current-len →
        evalPRF
          (PRRel.characteristic
            (CanonicalCodeParserPR.code-list-length-pr Parser))
          (args₂ list-code current-len)}
    {n = len}
    {bound = list-code}
    len≤list-code
    (CanonicalCodeParserPR.code-list-length-complete
      Parser
      {list-code = list-code}
      {len = len}
      length-nat)

codeListValid-nonzero-sound :
  (Parser : CanonicalCodeParserPR) →
  CodeListLengthNonzeroSound Parser →
  {list-code : ℕ} →
  NonzeroNat (evalPRF (codeListValidF Parser) (list-code ∷ [])) →
  Σ ℕ (λ len → CodeListLengthNat list-code len)
codeListValid-nonzero-sound Parser length-nonzero-sound {list-code} nonzero
  rewrite codeListValidF-correct Parser list-code
  with searchUpTo-nonzero-sound
        {P =
          λ current-len →
            evalPRF
              (PRRel.characteristic
                (CanonicalCodeParserPR.code-list-length-pr Parser))
              (args₂ list-code current-len)}
        list-code
        nonzero
... | len ,Σ (_ ,× len-hit) =
  len ,Σ
    length-nonzero-sound
      {list-code = list-code}
      {len = len}
      len-hit

nodeCodeBuilderEqF :
  PRF (suc (suc (suc zero)))
nodeCodeBuilderEqF =
  compF eqNatF
    (projF fin0 ∷
     compF nodeCodeWithRestF
      (projF fin1 ∷
       projF fin2 ∷ []) ∷ [])

nodeCodeBuilderEqF-correct :
  (input tag children-code : ℕ) →
  evalPRF nodeCodeBuilderEqF (args₃ input tag children-code) ≡
  eqNatNat
    input
    (evalPRF nodeCodeWithRestF (tag ∷ children-code ∷ []))
nodeCodeBuilderEqF-correct input tag children-code
  rewrite eqNatF-correct
            input
            (evalPRF nodeCodeWithRestF (tag ∷ children-code ∷ [])) =
  refl

nodeCodeF :
  CanonicalCodeParserPR →
  PRF (suc (suc (suc zero)))
nodeCodeF Parser =
  compF andF
    (nodeCodeBuilderEqF ∷
     compF (codeListValidF Parser) (projF fin2 ∷ []) ∷ [])

nodeCodePR :
  CanonicalCodeParserPR →
  PRRel (suc (suc (suc zero)))
nodeCodePR Parser =
  rel (nodeCodeF Parser)

nodeCodeF-correct :
  (Parser : CanonicalCodeParserPR) →
  (input tag children-code : ℕ) →
  evalPRF (nodeCodeF Parser) (args₃ input tag children-code) ≡
  mulNat
    (evalPRF nodeCodeBuilderEqF (args₃ input tag children-code))
    (evalPRF (codeListValidF Parser) (children-code ∷ []))
nodeCodeF-correct Parser input tag children-code
  rewrite andF-correct
            (evalPRF nodeCodeBuilderEqF
              (args₃ input tag children-code))
            (evalPRF (codeListValidF Parser) (children-code ∷ [])) =
  refl

nodeCode-complete :
  (Parser : CanonicalCodeParserPR) →
  {input tag children-code : ℕ} →
  NodeCodeNat input tag children-code →
  PRRel-holds (nodeCodePR Parser) (args₃ input tag children-code)
nodeCode-complete Parser {input} {tag} {children-code}
    (children ,Σ (input-eq ,× children-eq))
  rewrite nodeCodeF-correct Parser input tag children-code
        | nodeCodeBuilderEqF-correct input tag children-code
        | input-eq
        | children-eq
        | nodeCodeWithRestF-correct
            tag
            (encodeCodeListWithRest children zero)
        | eqNatNat-refl-code
            (encodeCode (node tag children))
        | codeListValid-complete
            Parser
            {list-code = encodeCodeListWithRest children zero}
            {len = codeListLength children}
            (codeListLength≤listCode
              children
              refl)
            (children ,Σ (refl ,× refl)) =
  refl

nodeCode-sound :
  (Parser : CanonicalCodeParserPR) →
  CodeListLengthNonzeroSound Parser →
  {input tag children-code : ℕ} →
  PRRel-holds (nodeCodePR Parser) (args₃ input tag children-code) →
  NodeCodeNat input tag children-code
nodeCode-sound
    Parser length-nonzero-sound
    {input} {tag} {children-code} holds
  with and-output-sound
        (evalPRF nodeCodeBuilderEqF (args₃ input tag children-code))
        (evalPRF (codeListValidF Parser) (children-code ∷ []))
        (evalPRF (nodeCodeF Parser) (args₃ input tag children-code))
        (nodeCodeF-correct Parser input tag children-code)
        holds
... | builder-one ,× valid-one
  with codeListValid-nonzero-sound
        Parser
        length-nonzero-sound
        {list-code = children-code}
        (zero ,Σ valid-one)
... | len ,Σ (children ,Σ (children-eq ,× _)) =
  children ,Σ
    ( trans
        (eqNatNat-sound-code
          input
          (evalPRF nodeCodeWithRestF (tag ∷ children-code ∷ []))
          (trans
            (sym (nodeCodeBuilderEqF-correct input tag children-code))
            builder-one))
        (trans
          (nodeCodeWithRestF-correct tag children-code)
          (cong (λ code → appendDigit d1 (encodeNatWithRest tag code))
            children-eq))
    ,×
      children-eq)

nodeCode-nonzero-sound :
  (Parser : CanonicalCodeParserPR) →
  CodeListLengthNonzeroSound Parser →
  {input tag children-code : ℕ} →
  NonzeroNat
    (evalPRF (nodeCodeF Parser) (args₃ input tag children-code)) →
  NodeCodeNat input tag children-code
nodeCode-nonzero-sound
    Parser length-nonzero-sound
    {input} {tag} {children-code} nonzero
  with and-output-nonzero-sound
        (evalPRF nodeCodeBuilderEqF (args₃ input tag children-code))
        (evalPRF (codeListValidF Parser) (children-code ∷ []))
        (evalPRF (nodeCodeF Parser) (args₃ input tag children-code))
        (nodeCodeF-correct Parser input tag children-code)
        nonzero
... | builder-nz ,× valid-nz
  with codeListValid-nonzero-sound
        Parser
        length-nonzero-sound
        {list-code = children-code}
        valid-nz
... | len ,Σ (children ,Σ (children-eq ,× _)) =
  children ,Σ
    ( trans
        (eqNatNat-nonzero-sound-code
          input
          (evalPRF nodeCodeWithRestF (tag ∷ children-code ∷ []))
          (subst
            (λ value → NonzeroNat value)
            (nodeCodeBuilderEqF-correct input tag children-code)
            builder-nz))
        (trans
          (nodeCodeWithRestF-correct tag children-code)
          (cong (λ code → appendDigit d1 (encodeNatWithRest tag code))
            children-eq))
    ,×
      children-eq)

canonicalCodeNodeParserPR-from-code-list-length :
  (Parser : CanonicalCodeParserPR) →
  CodeListLengthNonzeroSound Parser →
  CanonicalCodeNodeParserPR
canonicalCodeNodeParserPR-from-code-list-length Parser length-nonzero-sound =
  record
    { node-code-pr =
        nodeCodePR Parser
    ; node-code-complete =
        λ {input} {tag} {children-code} →
          nodeCode-complete
            Parser
            {input = input}
            {tag = tag}
            {children-code = children-code}
    ; node-code-sound =
        λ {input} {tag} {children-code} →
          nodeCode-sound
            Parser
            length-nonzero-sound
            {input = input}
            {tag = tag}
            {children-code = children-code}
    }
