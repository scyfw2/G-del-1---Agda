{-# OPTIONS --safe #-}

module Godel.ProofCheckingFixedLeafBranches where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.ProofRuleFixedCodeLeaf
  using
    ( FixedCodeLeafData
    ; FixedCodeLeafNat
    )
open import Godel.ProofCheckingBranch

-- Purely parameterized OR trees for fixed proof-code/formula-code leaves.
--
-- This module deliberately does not import the concrete PA axiom leaves.  The
-- concrete constants can be supplied later through FixedCodeLeafData without
-- making this aggregation layer normalize their canonical proof/formula codes.

FixedLeafTarget₂ :
  FixedCodeLeafData →
  FixedCodeLeafData →
  ℕ →
  ℕ →
  Set
FixedLeafTarget₂ left right =
  OrProofCheckingTarget
    (FixedCodeLeafNat left)
    (FixedCodeLeafNat right)

fixedLeafTargetedBranch₂ :
  (left right : FixedCodeLeafData) →
  TargetedProofCheckingBranchPR (FixedLeafTarget₂ left right)
fixedLeafTargetedBranch₂ left right =
  orTargetedProofCheckingBranchPR
    (fixedCodeLeafTargetedBranch left)
    (fixedCodeLeafTargetedBranch right)

FixedLeafTarget₄ :
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  ℕ →
  ℕ →
  Set
FixedLeafTarget₄ d0 d1 d2 d3 =
  OrProofCheckingTarget
    (FixedLeafTarget₂ d0 d1)
    (FixedLeafTarget₂ d2 d3)

fixedLeafTargetedBranch₄ :
  (d0 d1 d2 d3 : FixedCodeLeafData) →
  TargetedProofCheckingBranchPR (FixedLeafTarget₄ d0 d1 d2 d3)
fixedLeafTargetedBranch₄ d0 d1 d2 d3 =
  orTargetedProofCheckingBranchPR
    (fixedLeafTargetedBranch₂ d0 d1)
    (fixedLeafTargetedBranch₂ d2 d3)

FixedLeafNestedTarget₆ :
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  FixedCodeLeafData →
  ℕ →
  ℕ →
  Set
FixedLeafNestedTarget₆ d0 d1 d2 d3 d4 d5 =
  OrProofCheckingTarget
    (FixedLeafTarget₄ d0 d1 d2 d3)
    (FixedLeafTarget₂ d4 d5)

fixedLeafNestedTargetedBranch₆ :
  (d0 d1 d2 d3 d4 d5 : FixedCodeLeafData) →
  TargetedProofCheckingBranchPR
    (FixedLeafNestedTarget₆ d0 d1 d2 d3 d4 d5)
fixedLeafNestedTargetedBranch₆ d0 d1 d2 d3 d4 d5 =
  orTargetedProofCheckingBranchPR
    (fixedLeafTargetedBranch₄ d0 d1 d2 d3)
    (fixedLeafTargetedBranch₂ d4 d5)

data FixedLeafTarget₆
    (d0 d1 d2 d3 d4 d5 : FixedCodeLeafData)
    (proof-code formula-code : ℕ) :
    Set where
  fixed-leaf₀ :
    FixedCodeLeafNat d0 proof-code formula-code →
    FixedLeafTarget₆ d0 d1 d2 d3 d4 d5 proof-code formula-code

  fixed-leaf₁ :
    FixedCodeLeafNat d1 proof-code formula-code →
    FixedLeafTarget₆ d0 d1 d2 d3 d4 d5 proof-code formula-code

  fixed-leaf₂ :
    FixedCodeLeafNat d2 proof-code formula-code →
    FixedLeafTarget₆ d0 d1 d2 d3 d4 d5 proof-code formula-code

  fixed-leaf₃ :
    FixedCodeLeafNat d3 proof-code formula-code →
    FixedLeafTarget₆ d0 d1 d2 d3 d4 d5 proof-code formula-code

  fixed-leaf₄ :
    FixedCodeLeafNat d4 proof-code formula-code →
    FixedLeafTarget₆ d0 d1 d2 d3 d4 d5 proof-code formula-code

  fixed-leaf₅ :
    FixedCodeLeafNat d5 proof-code formula-code →
    FixedLeafTarget₆ d0 d1 d2 d3 d4 d5 proof-code formula-code

fixedLeafTarget₆-to-nested :
  {d0 d1 d2 d3 d4 d5 : FixedCodeLeafData} →
  {proof-code formula-code : ℕ} →
  FixedLeafTarget₆ d0 d1 d2 d3 d4 d5 proof-code formula-code →
  FixedLeafNestedTarget₆ d0 d1 d2 d3 d4 d5 proof-code formula-code
fixedLeafTarget₆-to-nested (fixed-leaf₀ hit) =
  branch-left (branch-left (branch-left hit))
fixedLeafTarget₆-to-nested (fixed-leaf₁ hit) =
  branch-left (branch-left (branch-right hit))
fixedLeafTarget₆-to-nested (fixed-leaf₂ hit) =
  branch-left (branch-right (branch-left hit))
fixedLeafTarget₆-to-nested (fixed-leaf₃ hit) =
  branch-left (branch-right (branch-right hit))
fixedLeafTarget₆-to-nested (fixed-leaf₄ hit) =
  branch-right (branch-left hit)
fixedLeafTarget₆-to-nested (fixed-leaf₅ hit) =
  branch-right (branch-right hit)

fixedLeafTargetedBranch₆ :
  (d0 d1 d2 d3 d4 d5 : FixedCodeLeafData) →
  TargetedProofCheckingBranchPR (FixedLeafTarget₆ d0 d1 d2 d3 d4 d5)
fixedLeafTargetedBranch₆ d0 d1 d2 d3 d4 d5 =
  targetedProofCheckingBranch-map
    fixedLeafTarget₆-to-nested
    (fixedLeafNestedTargetedBranch₆ d0 d1 d2 d3 d4 d5)
