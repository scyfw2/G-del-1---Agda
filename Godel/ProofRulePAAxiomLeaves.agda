{-# OPTIONS --safe #-}

module Godel.ProofRulePAAxiomLeaves where

open import Godel.PRRepresentabilityFinal using (PARepresentsRelation)
open import Godel.ProofSystem using (axiom)
open import Godel.PA
open import Godel.ProofRuleFixedCodeLeaf

-- Named fixed-code leaves for the non-parameterized PA axiom constructors.
--
-- The induction schema branch carries a formula parameter, so it belongs to a
-- later parser-backed branch.  These six leaves are fixed proof/formula-code
-- pairs.  We keep them as named leaves first; concrete multi-leaf aggregation
-- needs a finer opaque-code boundary to avoid normalizing several large
-- formula codes at once.

paSucNotZeroLeaf : FixedCodeLeafData
paSucNotZeroLeaf =
  fixedPAProofLeafData (axiom pa-suc-not-zero)

paSucInjectiveLeaf : FixedCodeLeafData
paSucInjectiveLeaf =
  fixedPAProofLeafData (axiom pa-suc-injective)

paAddZeroLeaf : FixedCodeLeafData
paAddZeroLeaf =
  fixedPAProofLeafData (axiom pa-add-zero)

paAddSucLeaf : FixedCodeLeafData
paAddSucLeaf =
  fixedPAProofLeafData (axiom pa-add-suc)

paMulZeroLeaf : FixedCodeLeafData
paMulZeroLeaf =
  fixedPAProofLeafData (axiom pa-mul-zero)

paMulSucLeaf : FixedCodeLeafData
paMulSucLeaf =
  fixedPAProofLeafData (axiom pa-mul-suc)

paSucNotZeroLeaf-represented :
  PARepresentsRelation (fixedCodeLeafPR paSucNotZeroLeaf)
paSucNotZeroLeaf-represented =
  fixedCodeLeafPR-represented paSucNotZeroLeaf

paSucInjectiveLeaf-represented :
  PARepresentsRelation (fixedCodeLeafPR paSucInjectiveLeaf)
paSucInjectiveLeaf-represented =
  fixedCodeLeafPR-represented paSucInjectiveLeaf

paAddZeroLeaf-represented :
  PARepresentsRelation (fixedCodeLeafPR paAddZeroLeaf)
paAddZeroLeaf-represented =
  fixedCodeLeafPR-represented paAddZeroLeaf

paAddSucLeaf-represented :
  PARepresentsRelation (fixedCodeLeafPR paAddSucLeaf)
paAddSucLeaf-represented =
  fixedCodeLeafPR-represented paAddSucLeaf

paMulZeroLeaf-represented :
  PARepresentsRelation (fixedCodeLeafPR paMulZeroLeaf)
paMulZeroLeaf-represented =
  fixedCodeLeafPR-represented paMulZeroLeaf

paMulSucLeaf-represented :
  PARepresentsRelation (fixedCodeLeafPR paMulSucLeaf)
paMulSucLeaf-represented =
  fixedCodeLeafPR-represented paMulSucLeaf
