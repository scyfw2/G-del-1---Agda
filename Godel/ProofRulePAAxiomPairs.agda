{-# OPTIONS --safe #-}

module Godel.ProofRulePAAxiomPairs where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.PrimitiveRecursive
open import Godel.PRRepresentabilityFinal using (PARepresentsRelation)
open import Godel.ProofRulePRDisjunction
open import Godel.ProofRuleFixedCodeLeaf
open import Godel.ProofRulePAAxiomLeaves

-- Pairwise PR relations for the six non-parameterized PA axiom leaves.
--
-- This module deliberately only exposes the relation and PA representability
-- layer.  The generic decoded/executable adapters live in
-- ProofRuleFixedCodeLeaf; specializing them directly to concrete PA axioms can
-- force Agda to normalize large canonical formula-code expressions.

paAxiom01LeafPR : PRRel (suc (suc zero))
paAxiom01LeafPR =
  fixedCodeLeafOrPR
    paSucNotZeroLeaf
    paSucInjectiveLeaf

paAxiom23LeafPR : PRRel (suc (suc zero))
paAxiom23LeafPR =
  fixedCodeLeafOrPR
    paAddZeroLeaf
    paAddSucLeaf

paAxiom45LeafPR : PRRel (suc (suc zero))
paAxiom45LeafPR =
  fixedCodeLeafOrPR
    paMulZeroLeaf
    paMulSucLeaf

paAxiom01LeafPR-represented :
  PARepresentsRelation paAxiom01LeafPR
paAxiom01LeafPR-represented =
  fixedCodeLeafOrPR-represented
    paSucNotZeroLeaf
    paSucInjectiveLeaf

paAxiom23LeafPR-represented :
  PARepresentsRelation paAxiom23LeafPR
paAxiom23LeafPR-represented =
  fixedCodeLeafOrPR-represented
    paAddZeroLeaf
    paAddSucLeaf

paAxiom45LeafPR-represented :
  PARepresentsRelation paAxiom45LeafPR
paAxiom45LeafPR-represented =
  fixedCodeLeafOrPR-represented
    paMulZeroLeaf
    paMulSucLeaf

paAxiom0123LeafPR : PRRel (suc (suc zero))
paAxiom0123LeafPR =
  orProofRulePR
    paAxiom01LeafPR
    paAxiom23LeafPR

paFixedAxiomLeafPR : PRRel (suc (suc zero))
paFixedAxiomLeafPR =
  orProofRulePR
    paAxiom0123LeafPR
    paAxiom45LeafPR

paAxiom0123LeafPR-represented :
  PARepresentsRelation paAxiom0123LeafPR
paAxiom0123LeafPR-represented =
  orProofRulePR-represented
    paAxiom01LeafPR
    paAxiom23LeafPR

paFixedAxiomLeafPR-represented :
  PARepresentsRelation paFixedAxiomLeafPR
paFixedAxiomLeafPR-represented =
  orProofRulePR-represented
    paAxiom0123LeafPR
    paAxiom45LeafPR
