{-# OPTIONS --safe #-}

module Godel.CanonicalCoding where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Godel.Core
open import Godel.Syntax
open import Godel.Coding

-- A structural, canonical syntax code used as a checked staging layer before
-- replacing the original numeric coding with a fully decodable Gödel coding.
data Code : Set where
  atom : ℕ → Code
  node : ℕ → List Code → Code

+-assoc : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
+-assoc zero b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

+-zeroʳ : (a : ℕ) → a + zero ≡ a
+-zeroʳ zero = refl
+-zeroʳ (suc a) = cong suc (+-zeroʳ a)

+-sucʳ : (a b : ℕ) → a + suc b ≡ suc (a + b)
+-sucʳ zero b = refl
+-sucʳ (suc a) b = cong suc (+-sucʳ a b)

+-comm : (a b : ℕ) → a + b ≡ b + a
+-comm zero b = sym (+-zeroʳ b)
+-comm (suc a) b rewrite +-sucʳ b a | +-comm a b = refl

+-swap-mid : (a b c : ℕ) → a + (b + c) ≡ b + (a + c)
+-swap-mid a b c
  rewrite sym (+-assoc a b c) | +-comm a b | +-assoc b a c = refl

canonicalCodeTerm : Term → Code
canonicalCodeTerms : List Term → Code
canonicalCodeFormula : Formula → Code

canonicalCodeTerm (var x)     = node 0 (atom x ∷ [])
canonicalCodeTerm zeroᵗ       = node 1 []
canonicalCodeTerm (sucᵗ t)    = node 2 (canonicalCodeTerm t ∷ [])
canonicalCodeTerm (s +ᵗ t)    = node 3 (canonicalCodeTerm s ∷ canonicalCodeTerm t ∷ [])
canonicalCodeTerm (s *ᵗ t)    = node 4 (canonicalCodeTerm s ∷ canonicalCodeTerm t ∷ [])

canonicalCodeTerms []       = node 0 []
canonicalCodeTerms (t ∷ ts) = node 1 (canonicalCodeTerm t ∷ canonicalCodeTerms ts ∷ [])

canonicalCodeFormula (s ≈ t)    = node 5 (canonicalCodeTerm s ∷ canonicalCodeTerm t ∷ [])
canonicalCodeFormula (Rel r ts) = node 6 (atom r ∷ canonicalCodeTerms ts ∷ [])
canonicalCodeFormula ⊥ᶠ         = node 7 []
canonicalCodeFormula (A ⇒ B)    = node 8 (canonicalCodeFormula A ∷ canonicalCodeFormula B ∷ [])
canonicalCodeFormula (A ∧ B)    = node 9 (canonicalCodeFormula A ∷ canonicalCodeFormula B ∷ [])
canonicalCodeFormula (A ∨ B)    = node 10 (canonicalCodeFormula A ∷ canonicalCodeFormula B ∷ [])
canonicalCodeFormula (¬ᶠ A)     = node 11 (canonicalCodeFormula A ∷ [])
canonicalCodeFormula (∀ᶠ A)     = node 12 (canonicalCodeFormula A ∷ [])
canonicalCodeFormula (∃ᶠ A)     = node 13 (canonicalCodeFormula A ∷ [])

decodeTerm : ℕ → Code → Maybe Term
decodeTerms : ℕ → Code → Maybe (List Term)
decodeFormula : ℕ → Code → Maybe Formula

decodeTerm zero c = nothing
decodeTerm (suc fuel) (node 0 (atom x ∷ [])) = just (var x)
decodeTerm (suc fuel) (node 1 []) = just zeroᵗ
decodeTerm (suc fuel) (node 2 (c ∷ [])) with decodeTerm (suc fuel) c
... | just t = just (sucᵗ t)
... | nothing = nothing
decodeTerm (suc fuel) (node 3 (c ∷ d ∷ []))
  with decodeTerm (suc fuel) c | decodeTerm (suc fuel) d
... | just s | just t = just (s +ᵗ t)
... | _      | _      = nothing
decodeTerm (suc fuel) (node 4 (c ∷ d ∷ []))
  with decodeTerm (suc fuel) c | decodeTerm (suc fuel) d
... | just s | just t = just (s *ᵗ t)
... | _      | _      = nothing
decodeTerm (suc fuel) c = nothing

decodeTerms zero c = nothing
decodeTerms (suc fuel) (node 0 []) = just []
decodeTerms (suc fuel) (node 1 (c ∷ cs ∷ []))
  with decodeTerm (suc fuel) c | decodeTerms (suc fuel) cs
... | just t | just ts = just (t ∷ ts)
... | _      | _       = nothing
decodeTerms (suc fuel) c = nothing

decodeFormula zero c = nothing
decodeFormula (suc fuel) (node 5 (c ∷ d ∷ []))
  with decodeTerm (suc fuel) c | decodeTerm (suc fuel) d
... | just s | just t = just (s ≈ t)
... | _      | _      = nothing
decodeFormula (suc fuel) (node 6 (atom r ∷ cs ∷ [])) with decodeTerms (suc fuel) cs
... | just ts = just (Rel r ts)
... | nothing = nothing
decodeFormula (suc fuel) (node 7 []) = just ⊥ᶠ
decodeFormula (suc fuel) (node 8 (c ∷ d ∷ []))
  with decodeFormula (suc fuel) c | decodeFormula (suc fuel) d
... | just A | just B = just (A ⇒ B)
... | _      | _      = nothing
decodeFormula (suc fuel) (node 9 (c ∷ d ∷ []))
  with decodeFormula (suc fuel) c | decodeFormula (suc fuel) d
... | just A | just B = just (A ∧ B)
... | _      | _      = nothing
decodeFormula (suc fuel) (node 10 (c ∷ d ∷ []))
  with decodeFormula (suc fuel) c | decodeFormula (suc fuel) d
... | just A | just B = just (A ∨ B)
... | _      | _      = nothing
decodeFormula (suc fuel) (node 11 (c ∷ [])) with decodeFormula (suc fuel) c
... | just A = just (¬ᶠ A)
... | nothing = nothing
decodeFormula (suc fuel) (node 12 (c ∷ [])) with decodeFormula (suc fuel) c
... | just A = just (∀ᶠ A)
... | nothing = nothing
decodeFormula (suc fuel) (node 13 (c ∷ [])) with decodeFormula (suc fuel) c
... | just A = just (∃ᶠ A)
... | nothing = nothing
decodeFormula (suc fuel) c = nothing

decodeTerm-roundTrip :
  (fuel : ℕ) → (t : Term) → decodeTerm (suc fuel) (canonicalCodeTerm t) ≡ just t
decodeTerm-roundTrip fuel (var x) = refl
decodeTerm-roundTrip fuel zeroᵗ = refl
decodeTerm-roundTrip fuel (sucᵗ t)
  rewrite decodeTerm-roundTrip fuel t = refl
decodeTerm-roundTrip fuel (s +ᵗ t)
  rewrite decodeTerm-roundTrip fuel s | decodeTerm-roundTrip fuel t = refl
decodeTerm-roundTrip fuel (s *ᵗ t)
  rewrite decodeTerm-roundTrip fuel s | decodeTerm-roundTrip fuel t = refl

decodeTerms-roundTrip :
  (fuel : ℕ) → (ts : List Term) → decodeTerms (suc fuel) (canonicalCodeTerms ts) ≡ just ts
decodeTerms-roundTrip fuel [] = refl
decodeTerms-roundTrip fuel (t ∷ ts)
  rewrite decodeTerm-roundTrip fuel t | decodeTerms-roundTrip fuel ts = refl

decodeFormula-roundTrip :
  (fuel : ℕ) → (A : Formula) → decodeFormula (suc fuel) (canonicalCodeFormula A) ≡ just A
decodeFormula-roundTrip fuel (s ≈ t)
  rewrite decodeTerm-roundTrip fuel s | decodeTerm-roundTrip fuel t = refl
decodeFormula-roundTrip fuel (Rel r ts)
  rewrite decodeTerms-roundTrip fuel ts = refl
decodeFormula-roundTrip fuel ⊥ᶠ = refl
decodeFormula-roundTrip fuel (A ⇒ B)
  rewrite decodeFormula-roundTrip fuel A | decodeFormula-roundTrip fuel B = refl
decodeFormula-roundTrip fuel (A ∧ B)
  rewrite decodeFormula-roundTrip fuel A | decodeFormula-roundTrip fuel B = refl
decodeFormula-roundTrip fuel (A ∨ B)
  rewrite decodeFormula-roundTrip fuel A | decodeFormula-roundTrip fuel B = refl
decodeFormula-roundTrip fuel (¬ᶠ A)
  rewrite decodeFormula-roundTrip fuel A = refl
decodeFormula-roundTrip fuel (∀ᶠ A)
  rewrite decodeFormula-roundTrip fuel A = refl
decodeFormula-roundTrip fuel (∃ᶠ A)
  rewrite decodeFormula-roundTrip fuel A = refl

-- Numeric coding for canonical structural codes.
--
-- This is intentionally separate from Godel.Coding.codeFormula.  The original
-- codeFormula remains the Gödel code consumed by the current theorem; this
-- layer is a decodable staging code for future arithmetization work.
data Digit : Set where
  d0 d1 d2 d3 : Digit

data DigitRest : Set where
  digitRest : Digit → ℕ → DigitRest

appendDigit : Digit → ℕ → ℕ
appendDigit d0 zero = zero
appendDigit d1 zero = suc zero
appendDigit d2 zero = suc (suc zero)
appendDigit d3 zero = suc (suc (suc zero))
appendDigit d (suc rest) = suc (suc (suc (suc (appendDigit d rest))))

undigit : ℕ → DigitRest
undigit zero = digitRest d0 zero
undigit (suc zero) = digitRest d1 zero
undigit (suc (suc zero)) = digitRest d2 zero
undigit (suc (suc (suc zero))) = digitRest d3 zero
undigit (suc (suc (suc (suc n)))) with undigit n
... | digitRest d rest = digitRest d (suc rest)

undigit-appendDigit :
  (d : Digit) → (rest : ℕ) → undigit (appendDigit d rest) ≡ digitRest d rest
undigit-appendDigit d0 zero = refl
undigit-appendDigit d1 zero = refl
undigit-appendDigit d2 zero = refl
undigit-appendDigit d3 zero = refl
undigit-appendDigit d0 (suc rest) rewrite undigit-appendDigit d0 rest = refl
undigit-appendDigit d1 (suc rest) rewrite undigit-appendDigit d1 rest = refl
undigit-appendDigit d2 (suc rest) rewrite undigit-appendDigit d2 rest = refl
undigit-appendDigit d3 (suc rest) rewrite undigit-appendDigit d3 rest = refl

encodeNatWithRest : ℕ → ℕ → ℕ
encodeNatWithRest zero rest = appendDigit d3 rest
encodeNatWithRest (suc n) rest = appendDigit d2 (encodeNatWithRest n rest)

decodeNatWithRest : ℕ → ℕ → Maybe (ℕ × ℕ)
decodeNatWithRest zero input = nothing
decodeNatWithRest (suc fuel) input with undigit input
... | digitRest d2 rest with decodeNatWithRest fuel rest
... | just (n ,× final) = just (suc n ,× final)
... | nothing = nothing
decodeNatWithRest (suc fuel) input | digitRest d3 rest = just (zero ,× rest)
decodeNatWithRest (suc fuel) input | digitRest _ rest = nothing

decodeNatWithRest-roundTrip :
  (n rest extra : ℕ) →
  decodeNatWithRest (suc (n + extra)) (encodeNatWithRest n rest) ≡ just (n ,× rest)
decodeNatWithRest-roundTrip zero rest extra
  rewrite undigit-appendDigit d3 rest = refl
decodeNatWithRest-roundTrip (suc n) rest extra
  rewrite undigit-appendDigit d2 (encodeNatWithRest n rest)
        | decodeNatWithRest-roundTrip n rest extra = refl

encodeCodeWithRest : Code → ℕ → ℕ
encodeCodeListWithRest : List Code → ℕ → ℕ

encodeCodeWithRest (atom n) rest =
  appendDigit d0 (encodeNatWithRest n rest)
encodeCodeWithRest (node tag cs) rest =
  appendDigit d1 (encodeNatWithRest tag (encodeCodeListWithRest cs rest))

encodeCodeListWithRest [] rest = appendDigit d0 rest
encodeCodeListWithRest (c ∷ cs) rest =
  appendDigit d1 (encodeCodeWithRest c (encodeCodeListWithRest cs rest))

encodeCode : Code → ℕ
encodeCode c = encodeCodeWithRest c zero

codeSize : Code → ℕ
codeListSize : List Code → ℕ

codeSize (atom n) = suc n
codeSize (node tag cs) = suc (tag + codeListSize cs)

codeListSize [] = zero
codeListSize (c ∷ cs) = suc (codeSize c + codeListSize cs)

decodeCodeWithRest : ℕ → ℕ → Maybe (Code × ℕ)
decodeCodeListWithRest : ℕ → ℕ → Maybe (List Code × ℕ)

decodeCodeWithRest zero input = nothing
decodeCodeWithRest (suc fuel) input with undigit input
... | digitRest d0 rest with decodeNatWithRest fuel rest
... | just (n ,× final) = just (atom n ,× final)
... | nothing = nothing
decodeCodeWithRest (suc fuel) input | digitRest d1 rest with decodeNatWithRest fuel rest
... | just (tag ,× rest') with decodeCodeListWithRest fuel rest'
... | just (cs ,× final) = just (node tag cs ,× final)
... | nothing = nothing
decodeCodeWithRest (suc fuel) input | digitRest d1 rest | nothing = nothing
decodeCodeWithRest (suc fuel) input | digitRest _ rest = nothing

decodeCodeListWithRest zero input = nothing
decodeCodeListWithRest (suc fuel) input with undigit input
... | digitRest d0 rest = just ([] ,× rest)
... | digitRest d1 rest with decodeCodeWithRest fuel rest
... | just (c ,× rest') with decodeCodeListWithRest fuel rest'
... | just (cs ,× final) = just ((c ∷ cs) ,× final)
... | nothing = nothing
decodeCodeListWithRest (suc fuel) input | digitRest d1 rest | nothing = nothing
decodeCodeListWithRest (suc fuel) input | digitRest _ rest = nothing

decodeCode : ℕ → ℕ → Maybe Code
decodeCode fuel input with decodeCodeWithRest fuel input
... | just (c ,× zero) = just c
... | just (c ,× suc rest) = nothing
... | nothing = nothing

mutual
  decodeCodeWithRest-roundTrip :
    (c : Code) → (rest extra : ℕ) →
    decodeCodeWithRest (suc (codeSize c + extra)) (encodeCodeWithRest c rest)
    ≡ just (c ,× rest)
  decodeCodeWithRest-roundTrip (atom n) rest extra
    rewrite undigit-appendDigit d0 (encodeNatWithRest n rest)
          | decodeNatWithRest-roundTrip n rest extra = refl
  decodeCodeWithRest-roundTrip (node tag cs) rest extra
    rewrite undigit-appendDigit d1 (encodeNatWithRest tag (encodeCodeListWithRest cs rest))
          | +-assoc tag (codeListSize cs) extra
          | decodeNatWithRest-roundTrip tag (encodeCodeListWithRest cs rest) (codeListSize cs + extra)
          | +-swap-mid tag (codeListSize cs) extra
          | decodeCodeListWithRest-roundTrip cs rest (tag + extra) = refl

  decodeCodeListWithRest-roundTrip :
    (cs : List Code) → (rest extra : ℕ) →
    decodeCodeListWithRest (suc (codeListSize cs + extra)) (encodeCodeListWithRest cs rest)
    ≡ just (cs ,× rest)
  decodeCodeListWithRest-roundTrip [] rest extra
    rewrite undigit-appendDigit d0 rest = refl
  decodeCodeListWithRest-roundTrip (c ∷ cs) rest extra
    rewrite undigit-appendDigit d1 (encodeCodeWithRest c (encodeCodeListWithRest cs rest))
          | +-assoc (codeSize c) (codeListSize cs) extra
          | decodeCodeWithRest-roundTrip c (encodeCodeListWithRest cs rest) (codeListSize cs + extra)
          | +-swap-mid (codeSize c) (codeListSize cs) extra
          | decodeCodeListWithRest-roundTrip cs rest (codeSize c + extra) = refl

decodeCode-roundTrip :
  (c : Code) → decodeCode (suc (codeSize c)) (encodeCode c) ≡ just c
decodeCode-roundTrip c
  rewrite sym (+-zeroʳ (codeSize c))
        | decodeCodeWithRest-roundTrip c zero zero = refl

canonicalNatTerm : Term → ℕ
canonicalNatTerm t = encodeCode (canonicalCodeTerm t)

canonicalNatFormula : Formula → ℕ
canonicalNatFormula A = encodeCode (canonicalCodeFormula A)

decodeNatTermWithFuel : ℕ → ℕ → Maybe Term
decodeNatTermWithFuel fuel input with decodeCode fuel input
... | just c with decodeTerm fuel c
... | just t = just t
... | nothing = nothing
decodeNatTermWithFuel fuel input | nothing = nothing

decodeNatFormulaWithFuel : ℕ → ℕ → Maybe Formula
decodeNatFormulaWithFuel fuel input with decodeCode fuel input
... | just c with decodeFormula fuel c
... | just A = just A
... | nothing = nothing
decodeNatFormulaWithFuel fuel input | nothing = nothing

decodeNatTerm : ℕ → Maybe Term
decodeNatTerm input = decodeNatTermWithFuel (suc input) input

decodeNatFormula : ℕ → Maybe Formula
decodeNatFormula input = decodeNatFormulaWithFuel (suc input) input

decodeNatTermWithFuel-roundTrip :
  (t : Term) →
  decodeNatTermWithFuel (suc (codeSize (canonicalCodeTerm t))) (canonicalNatTerm t)
  ≡ just t
decodeNatTermWithFuel-roundTrip t
  rewrite decodeCode-roundTrip (canonicalCodeTerm t)
        | decodeTerm-roundTrip (codeSize (canonicalCodeTerm t)) t = refl

decodeNatFormulaWithFuel-roundTrip :
  (A : Formula) →
  decodeNatFormulaWithFuel (suc (codeSize (canonicalCodeFormula A))) (canonicalNatFormula A)
  ≡ just A
decodeNatFormulaWithFuel-roundTrip A
  rewrite decodeCode-roundTrip (canonicalCodeFormula A)
        | decodeFormula-roundTrip (codeSize (canonicalCodeFormula A)) A = refl

diagFormula : Formula → Formula
diagFormula A = subst0 (⌜ A ⌝ᶠ) A

diagCode : Formula → ℕ
diagCode A = codeFormula (diagFormula A)

DiagCode : ℕ → ℕ → Set
DiagCode a b = Σ Formula (λ A → (a ≡ codeFormula A) × (b ≡ diagCode A))

diagRelSymbol : ℕ
diagRelSymbol = suc proofRelSymbol

DiagRel : Term → Term → Formula
DiagRel input-code output-code = Rel diagRelSymbol (input-code ∷ output-code ∷ [])

simpleEquation : Formula
simpleEquation = numeral 1 ≈ numeral 1

roundTrip-numeral-two :
  decodeTerm 1 (canonicalCodeTerm (numeral 2)) ≡ just (numeral 2)
roundTrip-numeral-two = decodeTerm-roundTrip 0 (numeral 2)

roundTrip-simpleEquation :
  decodeFormula 1 (canonicalCodeFormula simpleEquation) ≡ just simpleEquation
roundTrip-simpleEquation = decodeFormula-roundTrip 0 simpleEquation

roundTrip-noProofsTemplate :
  decodeFormula 1 (canonicalCodeFormula noProofsTemplate) ≡ just noProofsTemplate
roundTrip-noProofsTemplate = decodeFormula-roundTrip 0 noProofsTemplate

roundTrip-diag-noProofsTemplate :
  decodeFormula 1 (canonicalCodeFormula (diagFormula noProofsTemplate))
  ≡ just (diagFormula noProofsTemplate)
roundTrip-diag-noProofsTemplate = decodeFormula-roundTrip 0 (diagFormula noProofsTemplate)

roundTrip-nat-numeral-two :
  decodeNatTermWithFuel
    (suc (codeSize (canonicalCodeTerm (numeral 2))))
    (canonicalNatTerm (numeral 2))
  ≡ just (numeral 2)
roundTrip-nat-numeral-two = decodeNatTermWithFuel-roundTrip (numeral 2)

roundTrip-nat-simpleEquation :
  decodeNatFormulaWithFuel
    (suc (codeSize (canonicalCodeFormula simpleEquation)))
    (canonicalNatFormula simpleEquation)
  ≡ just simpleEquation
roundTrip-nat-simpleEquation = decodeNatFormulaWithFuel-roundTrip simpleEquation
