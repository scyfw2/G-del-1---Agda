{-# OPTIONS --safe #-}

module Godel.ProofRule37Bounds where

open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.CanonicalCoding
  using
    ( Code
    ; atom
    ; node
    ; codeSize
    ; codeListSize
    ; codeSize≤encodeCode
    ; _≤_
    ; ≤-refl
    ; ≤-step
    ; ≤-trans
    ; +-comm
    )
open import Godel.ProofRuleTargets using (closedNumeralNeqCode)

-- The rule-37 search uses the proof code itself as a bound for the witnesses
-- m,n.  This module proves the purely coding-theoretic part of that fact:
-- the m,n stored in the canonical closed-numeral-inequality proof node are
-- bounded by the numeric code of that node.

x≤x+y : (x y : ℕ) → x ≤ x + y
x≤x+y x y = y ,Σ refl

y≤x+y : (x y : ℕ) → y ≤ x + y
y≤x+y x y = x ,Σ +-comm x y

x≤suc-x+y : (x y : ℕ) → x ≤ suc (x + y)
x≤suc-x+y x y = ≤-step (x≤x+y x y)

y≤suc-x+y : (x y : ℕ) → y ≤ suc (x + y)
y≤suc-x+y x y = ≤-step (y≤x+y x y)

atom-payload≤codeSize : (n : ℕ) → n ≤ codeSize (atom n)
atom-payload≤codeSize n =
  ≤-step (≤-refl n)

head-atom-payload≤codeListSize :
  (m n : ℕ) →
  m ≤ codeListSize (atom m ∷ atom n ∷ [])
head-atom-payload≤codeListSize m n =
  ≤-trans
    (atom-payload≤codeSize m)
    (x≤suc-x+y
      (codeSize (atom m))
      (codeListSize (atom n ∷ [])))

tail-atom-payload≤codeListSize :
  (m n : ℕ) →
  n ≤ codeListSize (atom m ∷ atom n ∷ [])
tail-atom-payload≤codeListSize m n =
  ≤-trans
    (≤-trans
      (atom-payload≤codeSize n)
      (x≤suc-x+y (codeSize (atom n)) (codeListSize [])))
    (y≤suc-x+y
      (codeSize (atom m))
      (codeListSize (atom n ∷ [])))

children≤rule37NodeSize :
  (m n : ℕ) →
  codeListSize (atom m ∷ atom n ∷ []) ≤
  codeSize (node 37 (atom m ∷ atom n ∷ []))
children≤rule37NodeSize m n =
  y≤suc-x+y 37 (codeListSize (atom m ∷ atom n ∷ []))

rule37-left-witness≤codeSize :
  (m n : ℕ) →
  m ≤ codeSize (node 37 (atom m ∷ atom n ∷ []))
rule37-left-witness≤codeSize m n =
  ≤-trans
    (head-atom-payload≤codeListSize m n)
    (children≤rule37NodeSize m n)

rule37-right-witness≤codeSize :
  (m n : ℕ) →
  n ≤ codeSize (node 37 (atom m ∷ atom n ∷ []))
rule37-right-witness≤codeSize m n =
  ≤-trans
    (tail-atom-payload≤codeListSize m n)
    (children≤rule37NodeSize m n)

rule37-left-witness≤closedCode :
  (m n : ℕ) →
  m ≤ closedNumeralNeqCode m n
rule37-left-witness≤closedCode m n =
  ≤-trans
    (rule37-left-witness≤codeSize m n)
    (codeSize≤encodeCode (node 37 (atom m ∷ atom n ∷ [])))

rule37-right-witness≤closedCode :
  (m n : ℕ) →
  n ≤ closedNumeralNeqCode m n
rule37-right-witness≤closedCode m n =
  ≤-trans
    (rule37-right-witness≤codeSize m n)
    (codeSize≤encodeCode (node 37 (atom m ∷ atom n ∷ [])))

rule37-left-witness≤proofCode :
  {m n proof-code : ℕ} →
  proof-code ≡ closedNumeralNeqCode m n →
  m ≤ proof-code
rule37-left-witness≤proofCode {m} {n} proof-eq =
  subst
    (λ code → m ≤ code)
    (sym proof-eq)
    (rule37-left-witness≤closedCode m n)

rule37-right-witness≤proofCode :
  {m n proof-code : ℕ} →
  proof-code ≡ closedNumeralNeqCode m n →
  n ≤ proof-code
rule37-right-witness≤proofCode {m} {n} proof-eq =
  subst
    (λ code → n ≤ code)
    (sym proof-eq)
    (rule37-right-witness≤closedCode m n)
