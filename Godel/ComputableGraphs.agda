{-# OPTIONS --safe #-}

module Godel.ComputableGraphs where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Godel.Core
open import Godel.Syntax
open import Godel.CanonicalCoding
open import Godel.DiagonalCoding
open import Godel.DecidableCoding

subst0NatCode? : ℕ → ℕ → ℕ → Bool
subst0NatCode? formula-code term-code output-code
  with decodeNatFormula formula-code
     | decodeNatTerm term-code
     | decodeNatFormula output-code
... | just A | just t | just B = formulaEq (subst0 t A) B
... | _      | _      | _      = false

diagNatCode? : ℕ → ℕ → Bool
diagNatCode? input-code output-code
  with decodeNatFormula input-code
     | decodeNatFormula output-code
... | just A | just B = formulaEq (diagFormula A) B
... | _      | _      = false

CheckedSubst0NatCode : ℕ → ℕ → ℕ → Set
CheckedSubst0NatCode formula-code term-code output-code =
  subst0NatCode? formula-code term-code output-code ≡ true

CheckedDiagNatCode : ℕ → ℕ → Set
CheckedDiagNatCode input-code output-code =
  diagNatCode? input-code output-code ≡ true

checkedSubst0NatCode-complete :
  (A : Formula) → (t : Term) →
  CheckedSubst0NatCode
    (canonicalNatFormula A)
    (canonicalNatTerm t)
    (canonicalNatFormula (subst0 t A))
checkedSubst0NatCode-complete A t
  rewrite decodeNatFormula-roundTrip A
        | decodeNatTerm-roundTrip t
        | decodeNatFormula-roundTrip (subst0 t A)
        | formulaEq-refl (subst0 t A) = refl

checkedDiagNatCode-complete :
  (A : Formula) →
  CheckedDiagNatCode
    (canonicalNatFormula A)
    (canonicalNatFormula (diagFormula A))
checkedDiagNatCode-complete A
  rewrite decodeNatFormula-roundTrip A
        | decodeNatFormula-roundTrip (diagFormula A)
        | formulaEq-refl (diagFormula A) = refl

DecodedSubst0NatCode : ℕ → ℕ → ℕ → Set
DecodedSubst0NatCode formula-code term-code output-code =
  Σ Formula (λ A →
  Σ Term (λ t →
  Σ Formula (λ B →
    (decodeNatFormula formula-code ≡ just A) ×
    ((decodeNatTerm term-code ≡ just t) ×
     ((decodeNatFormula output-code ≡ just B) ×
      (B ≡ subst0 t A))))))

DecodedDiagNatCode : ℕ → ℕ → Set
DecodedDiagNatCode input-code output-code =
  Σ Formula (λ A →
  Σ Formula (λ B →
    (decodeNatFormula input-code ≡ just A) ×
    ((decodeNatFormula output-code ≡ just B) ×
     (B ≡ diagFormula A))))

checkedSubst0NatCode-sound-decoded :
  (a t b : ℕ) →
  CheckedSubst0NatCode a t b →
  DecodedSubst0NatCode a t b
checkedSubst0NatCode-sound-decoded a t b checked
  with decodeNatFormula a | inspect decodeNatFormula a
     | decodeNatTerm t | inspect decodeNatTerm t
     | decodeNatFormula b | inspect decodeNatFormula b
... | just A | [ a-eq ]
    | just u | [ t-eq ]
    | just B | [ b-eq ] =
  A ,Σ u ,Σ B ,Σ
  refl ,× refl ,× refl ,×
  sym (formulaEq-sound (subst0 u A) B checked)
checkedSubst0NatCode-sound-decoded a t b ()
  | just A | [ a-eq ] | just u | [ t-eq ] | nothing | [ b-eq ]
checkedSubst0NatCode-sound-decoded a t b ()
  | just A | [ a-eq ] | nothing | [ t-eq ] | mb | [ b-eq ]
checkedSubst0NatCode-sound-decoded a t b ()
  | nothing | [ a-eq ] | mt | [ t-eq ] | mb | [ b-eq ]

checkedDiagNatCode-sound-decoded :
  (a b : ℕ) →
  CheckedDiagNatCode a b →
  DecodedDiagNatCode a b
checkedDiagNatCode-sound-decoded a b checked
  with decodeNatFormula a | inspect decodeNatFormula a
     | decodeNatFormula b | inspect decodeNatFormula b
... | just A | [ a-eq ] | just B | [ b-eq ] =
  A ,Σ B ,Σ
  refl ,× refl ,×
  sym (formulaEq-sound (diagFormula A) B checked)
checkedDiagNatCode-sound-decoded a b ()
  | just A | [ a-eq ] | nothing | [ b-eq ]
checkedDiagNatCode-sound-decoded a b ()
  | nothing | [ a-eq ] | mb | [ b-eq ]

checkedSubst0NatCode-sound :
  (a t b : ℕ) →
  CheckedSubst0NatCode a t b →
  Subst0NatCode a t b
checkedSubst0NatCode-sound a t b checked
  with checkedSubst0NatCode-sound-decoded a t b checked
... | A ,Σ u ,Σ B ,Σ a-eq ,× t-eq ,× b-eq ,× B-eq =
  A ,Σ u ,Σ
  decodeNatFormula-canonical a A a-eq ,×
  decodeNatTerm-canonical t u t-eq ,×
  trans (decodeNatFormula-canonical b B b-eq)
        (cong canonicalNatFormula B-eq)

checkedDiagNatCode-sound :
  (a b : ℕ) →
  CheckedDiagNatCode a b →
  DiagNatCode a b
checkedDiagNatCode-sound a b checked
  with checkedDiagNatCode-sound-decoded a b checked
... | A ,Σ B ,Σ a-eq ,× b-eq ,× B-eq =
  A ,Σ
  decodeNatFormula-canonical a A a-eq ,×
  trans (decodeNatFormula-canonical b B b-eq)
        (cong canonicalNatFormula B-eq)
