{-# OPTIONS --safe #-}

module Godel.Syntax where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List using (List; []; _∷_)
open import Godel.Core

infix  9 sucᵗ_
infixl 8 _*ᵗ_
infixl 7 _+ᵗ_
infix  6 _≈_
infixr 5 _⇒_
infixr 4 _∧_
infixr 3 _∨_
infix  7 ¬ᶠ_

-- First-order arithmetic terms with de Bruijn variables.
data Term : Set where
  var   : ℕ → Term
  zeroᵗ : Term
  sucᵗ_ : Term → Term
  _+ᵗ_  : Term → Term → Term
  _*ᵗ_  : Term → Term → Term

-- Formulas.  Rel r ts is an arbitrary r-th relation symbol applied to ts.
-- We reserve one relation symbol for the arithmetized proof predicate.
data Formula : Set where
  _≈_  : Term → Term → Formula
  Rel  : ℕ → List Term → Formula
  ⊥ᶠ   : Formula
  _⇒_  : Formula → Formula → Formula
  _∧_  : Formula → Formula → Formula
  _∨_  : Formula → Formula → Formula
  ¬ᶠ_  : Formula → Formula
  ∀ᶠ   : Formula → Formula
  ∃ᶠ   : Formula → Formula

Ren : Set
Ren = ℕ → ℕ

Sub : Set
Sub = ℕ → Term

-- Extend a renaming/substitution under one binder.
extRen : Ren → Ren
extRen ρ zero    = zero
extRen ρ (suc x) = suc (ρ x)

renameTerm : Ren → Term → Term
renameTerms : Ren → List Term → List Term
renameFormula : Ren → Formula → Formula

renameTerm ρ (var x)     = var (ρ x)
renameTerm ρ zeroᵗ       = zeroᵗ
renameTerm ρ (sucᵗ t)    = sucᵗ (renameTerm ρ t)
renameTerm ρ (s +ᵗ t)    = renameTerm ρ s +ᵗ renameTerm ρ t
renameTerm ρ (s *ᵗ t)    = renameTerm ρ s *ᵗ renameTerm ρ t

renameTerms ρ []       = []
renameTerms ρ (t ∷ ts) = renameTerm ρ t ∷ renameTerms ρ ts

renameFormula ρ (s ≈ t)    = renameTerm ρ s ≈ renameTerm ρ t
renameFormula ρ (Rel r ts) = Rel r (renameTerms ρ ts)
renameFormula ρ ⊥ᶠ         = ⊥ᶠ
renameFormula ρ (A ⇒ B)    = renameFormula ρ A ⇒ renameFormula ρ B
renameFormula ρ (A ∧ B)    = renameFormula ρ A ∧ renameFormula ρ B
renameFormula ρ (A ∨ B)    = renameFormula ρ A ∨ renameFormula ρ B
renameFormula ρ (¬ᶠ A)     = ¬ᶠ (renameFormula ρ A)
renameFormula ρ (∀ᶠ A)     = ∀ᶠ (renameFormula (extRen ρ) A)
renameFormula ρ (∃ᶠ A)     = ∃ᶠ (renameFormula (extRen ρ) A)

wkTerm : Term → Term
wkTerm = renameTerm suc

wkFormula : Formula → Formula
wkFormula = renameFormula suc

extSub : Sub → Sub
extSub σ zero    = var zero
extSub σ (suc x) = wkTerm (σ x)

substTerm : Sub → Term → Term
substTerms : Sub → List Term → List Term
substFormula : Sub → Formula → Formula

substTerm σ (var x)     = σ x
substTerm σ zeroᵗ       = zeroᵗ
substTerm σ (sucᵗ t)    = sucᵗ (substTerm σ t)
substTerm σ (s +ᵗ t)    = substTerm σ s +ᵗ substTerm σ t
substTerm σ (s *ᵗ t)    = substTerm σ s *ᵗ substTerm σ t

substTerms σ []       = []
substTerms σ (t ∷ ts) = substTerm σ t ∷ substTerms σ ts

substFormula σ (s ≈ t)    = substTerm σ s ≈ substTerm σ t
substFormula σ (Rel r ts) = Rel r (substTerms σ ts)
substFormula σ ⊥ᶠ         = ⊥ᶠ
substFormula σ (A ⇒ B)    = substFormula σ A ⇒ substFormula σ B
substFormula σ (A ∧ B)    = substFormula σ A ∧ substFormula σ B
substFormula σ (A ∨ B)    = substFormula σ A ∨ substFormula σ B
substFormula σ (¬ᶠ A)     = ¬ᶠ (substFormula σ A)
substFormula σ (∀ᶠ A)     = ∀ᶠ (substFormula (extSub σ) A)
substFormula σ (∃ᶠ A)     = ∃ᶠ (substFormula (extSub σ) A)

-- Substitute a single term for de Bruijn variable 0.
single : Term → Sub
single t zero    = t
single t (suc x) = var x

subst0 : Term → Formula → Formula
subst0 t A = substFormula (single t) A

-- Numerals 0, S 0, S (S 0), ...
numeral : ℕ → Term
numeral zero    = zeroᵗ
numeral (suc n) = sucᵗ (numeral n)

-- Numerals are closed: weakening and substitution leave them unchanged.
wk-numeral : (n : ℕ) → wkTerm (numeral n) ≡ numeral n
wk-numeral zero = refl
wk-numeral (suc n) = cong sucᵗ_ (wk-numeral n)

subst-numeral : (σ : Sub) → (n : ℕ) → substTerm σ (numeral n) ≡ numeral n
subst-numeral σ zero = refl
subst-numeral σ (suc n) = cong sucᵗ_ (subst-numeral σ n)

-- Relation symbol reserved for the binary proof predicate Proof(p , a).
proofRelSymbol : ℕ
proofRelSymbol = suc (suc (suc (suc (suc zero))))

ProofRel : Term → Term → Formula
ProofRel proof-code formula-code = Rel proofRelSymbol (proof-code ∷ formula-code ∷ [])
