{-# OPTIONS --safe #-}

module Godel.Coding where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List using (List; []; _∷_)
open import Godel.Core
open import Godel.Syntax

-- Small numerals used as tags for Gödel coding.
one two three four five six seven eight nine ten eleven twelve thirteen : ℕ
one      = suc zero
two      = suc one
three    = suc two
four     = suc three
five     = suc four
six      = suc five
seven    = suc six
eight    = suc seven
nine     = suc eight
ten      = suc nine
eleven   = suc ten
twelve   = suc eleven
thirteen = suc twelve

-- A simple total pairing function.  For the abstract theorem we only need a
-- stable code assignment; injectivity/decoding are part of the arithmetization
-- assumptions, not used by the metatheorem below.
pair : ℕ → ℕ → ℕ
pair m n = suc ((m + n) + (m * n))

tag : ℕ → ℕ → ℕ
tag k payload = pair k payload

codeTerm : Term → ℕ
codeTerms : List Term → ℕ
codeFormula : Formula → ℕ

codeTerm (var x)     = tag zero x
codeTerm zeroᵗ       = tag one zero
codeTerm (sucᵗ t)    = tag two (codeTerm t)
codeTerm (s +ᵗ t)    = tag three (pair (codeTerm s) (codeTerm t))
codeTerm (s *ᵗ t)    = tag four (pair (codeTerm s) (codeTerm t))

codeTerms []       = zero
codeTerms (t ∷ ts) = pair (codeTerm t) (codeTerms ts)

codeFormula (s ≈ t)    = tag five (pair (codeTerm s) (codeTerm t))
codeFormula (Rel r ts) = tag six (pair r (codeTerms ts))
codeFormula ⊥ᶠ         = tag seven zero
codeFormula (A ⇒ B)    = tag eight (pair (codeFormula A) (codeFormula B))
codeFormula (A ∧ B)    = tag nine (pair (codeFormula A) (codeFormula B))
codeFormula (A ∨ B)    = tag ten (pair (codeFormula A) (codeFormula B))
codeFormula (¬ᶠ A)     = tag eleven (codeFormula A)
codeFormula (∀ᶠ A)     = tag twelve (codeFormula A)
codeFormula (∃ᶠ A)     = tag thirteen (codeFormula A)

⌜_⌝ᶠ : Formula → Term
⌜ A ⌝ᶠ = numeral (codeFormula A)

-- Object-language formula: p is a proof-code of formula A.
ProofOf : Term → Formula → Formula
ProofOf p A = ProofRel p ⌜ A ⌝ᶠ

-- The two formulas used in Gödel's sentence.
noProofs : Formula → Formula
noProofs A = ∀ᶠ (¬ᶠ (ProofOf (var zero) A))

someProof : Formula → Formula
someProof A = ∃ᶠ (ProofOf (var zero) A)

-- Template with one free variable x:  ∀p ¬ Proof(p , x).
-- Inside the ∀, the external x is de Bruijn variable 1.
noProofsTemplate : Formula
noProofsTemplate = ∀ᶠ (¬ᶠ (ProofRel (var zero) (var (suc zero))))

-- Computation lemmas connecting the template/substitution view to ProofOf.
ProofOf-subst0 : (n : ℕ) → (A : Formula) →
                 subst0 (numeral n) (ProofOf (var zero) A) ≡ ProofOf (numeral n) A
ProofOf-subst0 n A =
  cong (λ t → ProofRel (numeral n) t)
       (subst-numeral (single (numeral n)) (codeFormula A))

notProofOf-subst0 : (n : ℕ) → (A : Formula) →
                    subst0 (numeral n) (¬ᶠ (ProofOf (var zero) A))
                    ≡ ¬ᶠ (ProofOf (numeral n) A)
notProofOf-subst0 n A = cong ¬ᶠ_ (ProofOf-subst0 n A)

noProofsTemplate-subst0 : (A : Formula) →
                          subst0 (⌜ A ⌝ᶠ) noProofsTemplate ≡ noProofs A
noProofsTemplate-subst0 A =
  cong (λ t → ∀ᶠ (¬ᶠ (ProofRel (var zero) t)))
       (wk-numeral (codeFormula A))
