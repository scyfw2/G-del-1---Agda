{-# OPTIONS --safe #-}

module Godel.ProofRule37FromCodeListLength where

open import Godel.CanonicalCodeParserTargets
  using (CanonicalCodeParserPR)
open import Godel.CanonicalCodeNodeParserFromListLength
  using
    ( CodeListLengthNonzeroSound
    ; canonicalCodeNodeParserPR-from-code-list-length
    ; nodeCode-nonzero-sound
    )
open import Godel.ProofCheckingRule37Branch
  using (ProofRule37CheckingBranchData)
open import Godel.ProofRule37CanonicalSearch
  using
    ( CanonicalCodeNodeParserSearchData
    ; proofRule37CanonicalCheckingBranchData-from-node-parser
    ; proofRule37CheckingBranchData-from-canonical-bounded-search
    )

-- This module closes the wiring from the remaining canonical list-length
-- parser obligation to the final rule-37 branch data.
--
-- Once a concrete CanonicalCodeParserPR supplies code-list-length-pr with
-- nonzero soundness, the full NodeCodeNat parser, the bounded canonical
-- witness search, and the ProofCheckingRule37Branch adapter are all obtained
-- by composition.

canonicalCodeNodeParserSearchData-from-code-list-length :
  (Parser : CanonicalCodeParserPR) →
  CodeListLengthNonzeroSound Parser →
  CanonicalCodeNodeParserSearchData
canonicalCodeNodeParserSearchData-from-code-list-length
    Parser length-nonzero-sound =
  record
    { node-parser-pr =
        canonicalCodeNodeParserPR-from-code-list-length
          Parser
          length-nonzero-sound
    ; node-code-nonzero-sound =
        λ {input} {tag} {children-code} →
          nodeCode-nonzero-sound
            Parser
            length-nonzero-sound
            {input = input}
            {tag = tag}
            {children-code = children-code}
    }

proofRule37CheckingBranchData-from-code-list-length :
  (Parser : CanonicalCodeParserPR) →
  CodeListLengthNonzeroSound Parser →
  ProofRule37CheckingBranchData
proofRule37CheckingBranchData-from-code-list-length
    Parser length-nonzero-sound =
  proofRule37CheckingBranchData-from-canonical-bounded-search
    (proofRule37CanonicalCheckingBranchData-from-node-parser
      (canonicalCodeNodeParserSearchData-from-code-list-length
        Parser
        length-nonzero-sound))
