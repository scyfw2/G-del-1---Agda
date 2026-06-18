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

infix 1 Reveal_·_is_

data Reveal_·_is_ {A B : Set} (f : A → B) (x : A) : B → Set where
  [_] : {y : B} → f x ≡ y → Reveal f · x is y

inspect : {A B : Set} → (f : A → B) → (x : A) → Reveal f · x is f x
inspect f x = [ refl ]

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

decodeTerm-sound :
  (fuel : ℕ) → (c : Code) → (t : Term) →
  decodeTerm fuel c ≡ just t →
  c ≡ canonicalCodeTerm t
decodeTerms-sound :
  (fuel : ℕ) → (c : Code) → (ts : List Term) →
  decodeTerms fuel c ≡ just ts →
  c ≡ canonicalCodeTerms ts
decodeFormula-sound :
  (fuel : ℕ) → (c : Code) → (A : Formula) →
  decodeFormula fuel c ≡ just A →
  c ≡ canonicalCodeFormula A

decodeTerm-sound zero c t ()
decodeTerm-sound (suc fuel) (atom n) t ()
decodeTerm-sound (suc fuel) (node 0 []) t ()
decodeTerm-sound (suc fuel) (node 0 (atom x ∷ [])) t eq with eq
... | refl = refl
decodeTerm-sound (suc fuel) (node 0 (node tag cs ∷ [])) t ()
decodeTerm-sound (suc fuel) (node 0 (atom x ∷ d ∷ cs)) t ()
decodeTerm-sound (suc fuel) (node 0 (node tag ds ∷ d ∷ cs)) t ()
decodeTerm-sound (suc fuel) (node 1 []) t eq with eq
... | refl = refl
decodeTerm-sound (suc fuel) (node 1 (c ∷ cs)) t ()
decodeTerm-sound (suc fuel) (node 2 []) t ()
decodeTerm-sound (suc fuel) (node 2 (c ∷ [])) t eq
  with decodeTerm (suc fuel) c | inspect (decodeTerm (suc fuel)) c
... | just u | [ rec-eq ] with eq
... | refl rewrite decodeTerm-sound (suc fuel) c u rec-eq = refl
decodeTerm-sound (suc fuel) (node 2 (c ∷ [])) t eq
  | nothing | [ rec-eq ] = impossible eq
  where
    impossible : nothing ≡ just t → node 2 (c ∷ []) ≡ canonicalCodeTerm t
    impossible ()
decodeTerm-sound (suc fuel) (node 2 (c ∷ d ∷ cs)) t ()
decodeTerm-sound (suc fuel) (node 3 []) t ()
decodeTerm-sound (suc fuel) (node 3 (c ∷ [])) t ()
decodeTerm-sound (suc fuel) (node 3 (c ∷ d ∷ [])) t eq
  with decodeTerm (suc fuel) c | inspect (decodeTerm (suc fuel)) c
     | decodeTerm (suc fuel) d | inspect (decodeTerm (suc fuel)) d
... | just u | [ c-eq ] | just v | [ d-eq ] with eq
... | refl
  rewrite decodeTerm-sound (suc fuel) c u c-eq
        | decodeTerm-sound (suc fuel) d v d-eq = refl
decodeTerm-sound (suc fuel) (node 3 (c ∷ d ∷ [])) t eq
  | just u | [ c-eq ] | nothing | [ d-eq ] = impossible eq
  where
    impossible : nothing ≡ just t → node 3 (c ∷ d ∷ []) ≡ canonicalCodeTerm t
    impossible ()
decodeTerm-sound (suc fuel) (node 3 (c ∷ d ∷ [])) t eq
  | nothing | [ c-eq ] | md | [ d-eq ] = impossible eq
  where
    impossible : nothing ≡ just t → node 3 (c ∷ d ∷ []) ≡ canonicalCodeTerm t
    impossible ()
decodeTerm-sound (suc fuel) (node 3 (c ∷ d ∷ e ∷ cs)) t ()
decodeTerm-sound (suc fuel) (node 4 []) t ()
decodeTerm-sound (suc fuel) (node 4 (c ∷ [])) t ()
decodeTerm-sound (suc fuel) (node 4 (c ∷ d ∷ [])) t eq
  with decodeTerm (suc fuel) c | inspect (decodeTerm (suc fuel)) c
     | decodeTerm (suc fuel) d | inspect (decodeTerm (suc fuel)) d
... | just u | [ c-eq ] | just v | [ d-eq ] with eq
... | refl
  rewrite decodeTerm-sound (suc fuel) c u c-eq
        | decodeTerm-sound (suc fuel) d v d-eq = refl
decodeTerm-sound (suc fuel) (node 4 (c ∷ d ∷ [])) t eq
  | just u | [ c-eq ] | nothing | [ d-eq ] = impossible eq
  where
    impossible : nothing ≡ just t → node 4 (c ∷ d ∷ []) ≡ canonicalCodeTerm t
    impossible ()
decodeTerm-sound (suc fuel) (node 4 (c ∷ d ∷ [])) t eq
  | nothing | [ c-eq ] | md | [ d-eq ] = impossible eq
  where
    impossible : nothing ≡ just t → node 4 (c ∷ d ∷ []) ≡ canonicalCodeTerm t
    impossible ()
decodeTerm-sound (suc fuel) (node 4 (c ∷ d ∷ e ∷ cs)) t ()
decodeTerm-sound (suc fuel) (node (suc (suc (suc (suc (suc tag))))) cs) t ()

decodeTerms-sound zero c ts ()
decodeTerms-sound (suc fuel) (atom n) ts ()
decodeTerms-sound (suc fuel) (node 0 []) ts eq with eq
... | refl = refl
decodeTerms-sound (suc fuel) (node 0 (c ∷ cs)) ts ()
decodeTerms-sound (suc fuel) (node 1 []) ts ()
decodeTerms-sound (suc fuel) (node 1 (c ∷ [])) ts ()
decodeTerms-sound (suc fuel) (node 1 (c ∷ cs ∷ [])) ts eq
  with decodeTerm (suc fuel) c | inspect (decodeTerm (suc fuel)) c
     | decodeTerms (suc fuel) cs | inspect (decodeTerms (suc fuel)) cs
... | just t | [ c-eq ] | just rest | [ cs-eq ] with eq
... | refl
  rewrite decodeTerm-sound (suc fuel) c t c-eq
        | decodeTerms-sound (suc fuel) cs rest cs-eq = refl
decodeTerms-sound (suc fuel) (node 1 (c ∷ cs ∷ [])) ts eq
  | just t | [ c-eq ] | nothing | [ cs-eq ] = impossible eq
  where
    impossible : nothing ≡ just ts → node 1 (c ∷ cs ∷ []) ≡ canonicalCodeTerms ts
    impossible ()
decodeTerms-sound (suc fuel) (node 1 (c ∷ cs ∷ [])) ts eq
  | nothing | [ c-eq ] | mts | [ cs-eq ] = impossible eq
  where
    impossible : nothing ≡ just ts → node 1 (c ∷ cs ∷ []) ≡ canonicalCodeTerms ts
    impossible ()
decodeTerms-sound (suc fuel) (node 1 (c ∷ cs ∷ d ∷ ds)) ts ()
decodeTerms-sound (suc fuel) (node (suc (suc tag)) cs) ts ()

decodeFormula-sound zero c A ()
decodeFormula-sound (suc fuel) (atom n) A ()
decodeFormula-sound (suc fuel) (node 0 cs) A ()
decodeFormula-sound (suc fuel) (node 1 cs) A ()
decodeFormula-sound (suc fuel) (node 2 cs) A ()
decodeFormula-sound (suc fuel) (node 3 cs) A ()
decodeFormula-sound (suc fuel) (node 4 cs) A ()
decodeFormula-sound (suc fuel) (node 5 []) A ()
decodeFormula-sound (suc fuel) (node 5 (c ∷ [])) A ()
decodeFormula-sound (suc fuel) (node 5 (c ∷ d ∷ [])) A eq
  with decodeTerm (suc fuel) c | inspect (decodeTerm (suc fuel)) c
     | decodeTerm (suc fuel) d | inspect (decodeTerm (suc fuel)) d
... | just s | [ c-eq ] | just t | [ d-eq ] with eq
... | refl
  rewrite decodeTerm-sound (suc fuel) c s c-eq
        | decodeTerm-sound (suc fuel) d t d-eq = refl
decodeFormula-sound (suc fuel) (node 5 (c ∷ d ∷ [])) A eq
  | just s | [ c-eq ] | nothing | [ d-eq ] = impossible eq
  where
    impossible : nothing ≡ just A → node 5 (c ∷ d ∷ []) ≡ canonicalCodeFormula A
    impossible ()
decodeFormula-sound (suc fuel) (node 5 (c ∷ d ∷ [])) A eq
  | nothing | [ c-eq ] | md | [ d-eq ] = impossible eq
  where
    impossible : nothing ≡ just A → node 5 (c ∷ d ∷ []) ≡ canonicalCodeFormula A
    impossible ()
decodeFormula-sound (suc fuel) (node 5 (c ∷ d ∷ e ∷ cs)) A ()
decodeFormula-sound (suc fuel) (node 6 []) A ()
decodeFormula-sound (suc fuel) (node 6 (atom r ∷ [])) A ()
decodeFormula-sound (suc fuel) (node 6 (atom r ∷ cs ∷ [])) A eq
  with decodeTerms (suc fuel) cs | inspect (decodeTerms (suc fuel)) cs
... | just ts | [ cs-eq ] with eq
... | refl rewrite decodeTerms-sound (suc fuel) cs ts cs-eq = refl
decodeFormula-sound (suc fuel) (node 6 (atom r ∷ cs ∷ [])) A eq
  | nothing | [ cs-eq ] = impossible eq
  where
    impossible : nothing ≡ just A → node 6 (atom r ∷ cs ∷ []) ≡ canonicalCodeFormula A
    impossible ()
decodeFormula-sound (suc fuel) (node 6 (node tag ds ∷ cs)) A ()
decodeFormula-sound (suc fuel) (node 6 (atom r ∷ cs ∷ d ∷ ds)) A ()
decodeFormula-sound (suc fuel) (node 7 []) A eq with eq
... | refl = refl
decodeFormula-sound (suc fuel) (node 7 (c ∷ cs)) A ()
decodeFormula-sound (suc fuel) (node 8 []) A ()
decodeFormula-sound (suc fuel) (node 8 (c ∷ [])) A ()
decodeFormula-sound (suc fuel) (node 8 (c ∷ d ∷ [])) A eq
  with decodeFormula (suc fuel) c | inspect (decodeFormula (suc fuel)) c
     | decodeFormula (suc fuel) d | inspect (decodeFormula (suc fuel)) d
... | just B | [ c-eq ] | just C | [ d-eq ] with eq
... | refl
  rewrite decodeFormula-sound (suc fuel) c B c-eq
        | decodeFormula-sound (suc fuel) d C d-eq = refl
decodeFormula-sound (suc fuel) (node 8 (c ∷ d ∷ [])) A eq
  | just B | [ c-eq ] | nothing | [ d-eq ] = impossible eq
  where
    impossible : nothing ≡ just A → node 8 (c ∷ d ∷ []) ≡ canonicalCodeFormula A
    impossible ()
decodeFormula-sound (suc fuel) (node 8 (c ∷ d ∷ [])) A eq
  | nothing | [ c-eq ] | md | [ d-eq ] = impossible eq
  where
    impossible : nothing ≡ just A → node 8 (c ∷ d ∷ []) ≡ canonicalCodeFormula A
    impossible ()
decodeFormula-sound (suc fuel) (node 8 (c ∷ d ∷ e ∷ cs)) A ()
decodeFormula-sound (suc fuel) (node 9 []) A ()
decodeFormula-sound (suc fuel) (node 9 (c ∷ [])) A ()
decodeFormula-sound (suc fuel) (node 9 (c ∷ d ∷ [])) A eq
  with decodeFormula (suc fuel) c | inspect (decodeFormula (suc fuel)) c
     | decodeFormula (suc fuel) d | inspect (decodeFormula (suc fuel)) d
... | just B | [ c-eq ] | just C | [ d-eq ] with eq
... | refl
  rewrite decodeFormula-sound (suc fuel) c B c-eq
        | decodeFormula-sound (suc fuel) d C d-eq = refl
decodeFormula-sound (suc fuel) (node 9 (c ∷ d ∷ [])) A eq
  | just B | [ c-eq ] | nothing | [ d-eq ] = impossible eq
  where
    impossible : nothing ≡ just A → node 9 (c ∷ d ∷ []) ≡ canonicalCodeFormula A
    impossible ()
decodeFormula-sound (suc fuel) (node 9 (c ∷ d ∷ [])) A eq
  | nothing | [ c-eq ] | md | [ d-eq ] = impossible eq
  where
    impossible : nothing ≡ just A → node 9 (c ∷ d ∷ []) ≡ canonicalCodeFormula A
    impossible ()
decodeFormula-sound (suc fuel) (node 9 (c ∷ d ∷ e ∷ cs)) A ()
decodeFormula-sound (suc fuel) (node 10 []) A ()
decodeFormula-sound (suc fuel) (node 10 (c ∷ [])) A ()
decodeFormula-sound (suc fuel) (node 10 (c ∷ d ∷ [])) A eq
  with decodeFormula (suc fuel) c | inspect (decodeFormula (suc fuel)) c
     | decodeFormula (suc fuel) d | inspect (decodeFormula (suc fuel)) d
... | just B | [ c-eq ] | just C | [ d-eq ] with eq
... | refl
  rewrite decodeFormula-sound (suc fuel) c B c-eq
        | decodeFormula-sound (suc fuel) d C d-eq = refl
decodeFormula-sound (suc fuel) (node 10 (c ∷ d ∷ [])) A eq
  | just B | [ c-eq ] | nothing | [ d-eq ] = impossible eq
  where
    impossible : nothing ≡ just A → node 10 (c ∷ d ∷ []) ≡ canonicalCodeFormula A
    impossible ()
decodeFormula-sound (suc fuel) (node 10 (c ∷ d ∷ [])) A eq
  | nothing | [ c-eq ] | md | [ d-eq ] = impossible eq
  where
    impossible : nothing ≡ just A → node 10 (c ∷ d ∷ []) ≡ canonicalCodeFormula A
    impossible ()
decodeFormula-sound (suc fuel) (node 10 (c ∷ d ∷ e ∷ cs)) A ()
decodeFormula-sound (suc fuel) (node 11 []) A ()
decodeFormula-sound (suc fuel) (node 11 (c ∷ [])) A eq
  with decodeFormula (suc fuel) c | inspect (decodeFormula (suc fuel)) c
... | just B | [ c-eq ] with eq
... | refl rewrite decodeFormula-sound (suc fuel) c B c-eq = refl
decodeFormula-sound (suc fuel) (node 11 (c ∷ [])) A eq
  | nothing | [ c-eq ] = impossible eq
  where
    impossible : nothing ≡ just A → node 11 (c ∷ []) ≡ canonicalCodeFormula A
    impossible ()
decodeFormula-sound (suc fuel) (node 11 (c ∷ d ∷ cs)) A ()
decodeFormula-sound (suc fuel) (node 12 []) A ()
decodeFormula-sound (suc fuel) (node 12 (c ∷ [])) A eq
  with decodeFormula (suc fuel) c | inspect (decodeFormula (suc fuel)) c
... | just B | [ c-eq ] with eq
... | refl rewrite decodeFormula-sound (suc fuel) c B c-eq = refl
decodeFormula-sound (suc fuel) (node 12 (c ∷ [])) A eq
  | nothing | [ c-eq ] = impossible eq
  where
    impossible : nothing ≡ just A → node 12 (c ∷ []) ≡ canonicalCodeFormula A
    impossible ()
decodeFormula-sound (suc fuel) (node 12 (c ∷ d ∷ cs)) A ()
decodeFormula-sound (suc fuel) (node 13 []) A ()
decodeFormula-sound (suc fuel) (node 13 (c ∷ [])) A eq
  with decodeFormula (suc fuel) c | inspect (decodeFormula (suc fuel)) c
... | just B | [ c-eq ] with eq
... | refl rewrite decodeFormula-sound (suc fuel) c B c-eq = refl
decodeFormula-sound (suc fuel) (node 13 (c ∷ [])) A eq
  | nothing | [ c-eq ] = impossible eq
  where
    impossible : nothing ≡ just A → node 13 (c ∷ []) ≡ canonicalCodeFormula A
    impossible ()
decodeFormula-sound (suc fuel) (node 13 (c ∷ d ∷ cs)) A ()
decodeFormula-sound (suc fuel)
  (node (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc tag)))))))))))))) cs)
  A ()

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

encodeDigitRest : DigitRest → ℕ
encodeDigitRest (digitRest d rest) = appendDigit d rest

undigit-sound : (input : ℕ) → input ≡ encodeDigitRest (undigit input)
undigit-sound zero = refl
undigit-sound (suc zero) = refl
undigit-sound (suc (suc zero)) = refl
undigit-sound (suc (suc (suc zero))) = refl
undigit-sound (suc (suc (suc (suc input)))) with undigit input | undigit-sound input
... | digitRest d0 rest | eq =
  cong suc (cong suc (cong suc (cong suc eq)))
... | digitRest d1 rest | eq =
  cong suc (cong suc (cong suc (cong suc eq)))
... | digitRest d2 rest | eq =
  cong suc (cong suc (cong suc (cong suc eq)))
... | digitRest d3 rest | eq =
  cong suc (cong suc (cong suc (cong suc eq)))

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

decodeNatWithRest-sound :
  (fuel input n rest : ℕ) →
  decodeNatWithRest fuel input ≡ just (n ,× rest) →
  input ≡ encodeNatWithRest n rest
decodeNatWithRest-sound zero input n rest ()
decodeNatWithRest-sound (suc fuel) input n rest eq
  with undigit input | undigit-sound input
... | digitRest d0 input-rest | input-eq = false≡just eq
  where
    false≡just :
      nothing ≡ just (n ,× rest) →
      input ≡ encodeNatWithRest n rest
    false≡just ()
... | digitRest d1 input-rest | input-eq = false≡just eq
  where
    false≡just :
      nothing ≡ just (n ,× rest) →
      input ≡ encodeNatWithRest n rest
    false≡just ()
... | digitRest d2 input-rest | input-eq
  with decodeNatWithRest fuel input-rest | inspect (decodeNatWithRest fuel) input-rest
... | just (n' ,× final) | [ rec-eq ] with eq
... | refl =
  trans input-eq
        (cong (appendDigit d2)
              (decodeNatWithRest-sound fuel input-rest n' final rec-eq))
decodeNatWithRest-sound (suc fuel) input n rest eq
  | digitRest d2 input-rest | input-eq
  | nothing | [ rec-eq ] = false≡just eq
  where
    false≡just :
      nothing ≡ just (n ,× rest) →
      input ≡ encodeNatWithRest n rest
    false≡just ()
decodeNatWithRest-sound (suc fuel) input n rest eq
  | digitRest d3 input-rest | input-eq with eq
... | refl = input-eq

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

infix 4 _≤_

_≤_ : ℕ → ℕ → Set
m ≤ n = Σ ℕ (λ extra → n ≡ m + extra)

≤-refl : (n : ℕ) → n ≤ n
≤-refl n = zero ,Σ sym (+-zeroʳ n)

≤-zero : (n : ℕ) → zero ≤ n
≤-zero n = n ,Σ refl

≤-step : {m n : ℕ} → m ≤ n → m ≤ suc n
≤-step {m} (extra ,Σ eq) =
  suc extra ,Σ trans (cong suc eq) (sym (+-sucʳ m extra))

≤-suc : {m n : ℕ} → m ≤ n → suc m ≤ suc n
≤-suc (extra ,Σ eq) = extra ,Σ cong suc eq

≤-trans : {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans {m} (extra₁ ,Σ eq₁) (extra₂ ,Σ eq₂) =
  extra₁ + extra₂ ,Σ
  trans eq₂ (trans (cong (λ x → x + extra₂) eq₁)
                    (+-assoc m extra₁ extra₂))

n≤appendDigit : (d : Digit) → (n : ℕ) → n ≤ appendDigit d n
n≤appendDigit d zero = ≤-zero (appendDigit d zero)
n≤appendDigit d0 (suc n) =
  ≤-step (≤-step (≤-step (≤-suc (n≤appendDigit d0 n))))
n≤appendDigit d1 (suc n) =
  ≤-step (≤-step (≤-step (≤-suc (n≤appendDigit d1 n))))
n≤appendDigit d2 (suc n) =
  ≤-step (≤-step (≤-step (≤-suc (n≤appendDigit d2 n))))
n≤appendDigit d3 (suc n) =
  ≤-step (≤-step (≤-step (≤-suc (n≤appendDigit d3 n))))

suc≤appendDigit₁ : (n : ℕ) → suc n ≤ appendDigit d1 n
suc≤appendDigit₁ zero = ≤-refl (suc zero)
suc≤appendDigit₁ (suc n) =
  ≤-step (≤-step (≤-step (≤-suc (suc≤appendDigit₁ n))))

suc≤appendDigit₂ : (n : ℕ) → suc n ≤ appendDigit d2 n
suc≤appendDigit₂ zero = ≤-step (≤-refl (suc zero))
suc≤appendDigit₂ (suc n) =
  ≤-step (≤-step (≤-step (≤-suc (suc≤appendDigit₂ n))))

suc≤appendDigit₃ : (n : ℕ) → suc n ≤ appendDigit d3 n
suc≤appendDigit₃ zero = ≤-step (≤-step (≤-refl (suc zero)))
suc≤appendDigit₃ (suc n) =
  ≤-step (≤-step (≤-step (≤-suc (suc≤appendDigit₃ n))))

size≤encodeNatWithRest :
  (tag base rest : ℕ) →
  base ≤ rest →
  suc (tag + base) ≤ encodeNatWithRest tag rest
size≤encodeNatWithRest zero base rest base≤rest =
  ≤-trans (≤-suc base≤rest) (suc≤appendDigit₃ rest)
size≤encodeNatWithRest (suc tag) base rest base≤rest =
  ≤-trans (≤-suc (size≤encodeNatWithRest tag base rest base≤rest))
          (suc≤appendDigit₂ (encodeNatWithRest tag rest))

mutual
  codeSize+base≤encodeCodeWithRest :
    (c : Code) → (base rest : ℕ) →
    base ≤ rest →
    codeSize c + base ≤ encodeCodeWithRest c rest
  codeSize+base≤encodeCodeWithRest (atom n) base rest base≤rest =
    ≤-trans (size≤encodeNatWithRest n base rest base≤rest)
            (n≤appendDigit d0 (encodeNatWithRest n rest))
  codeSize+base≤encodeCodeWithRest (node tag cs) base rest base≤rest
    rewrite +-assoc tag (codeListSize cs) base =
    ≤-trans
      (size≤encodeNatWithRest
        tag
        (codeListSize cs + base)
        (encodeCodeListWithRest cs rest)
        (codeListSize+base≤encodeCodeListWithRest cs base rest base≤rest))
      (n≤appendDigit d1
        (encodeNatWithRest tag (encodeCodeListWithRest cs rest)))

  codeListSize+base≤encodeCodeListWithRest :
    (cs : List Code) → (base rest : ℕ) →
    base ≤ rest →
    codeListSize cs + base ≤ encodeCodeListWithRest cs rest
  codeListSize+base≤encodeCodeListWithRest [] base rest base≤rest =
    ≤-trans base≤rest (n≤appendDigit d0 rest)
  codeListSize+base≤encodeCodeListWithRest (c ∷ cs) base rest base≤rest
    rewrite +-assoc (codeSize c) (codeListSize cs) base =
    ≤-trans
      (≤-suc
        (codeSize+base≤encodeCodeWithRest
          c
          (codeListSize cs + base)
          (encodeCodeListWithRest cs rest)
          (codeListSize+base≤encodeCodeListWithRest cs base rest base≤rest)))
      (suc≤appendDigit₁
        (encodeCodeWithRest c (encodeCodeListWithRest cs rest)))

codeSize≤encodeCode : (c : Code) → codeSize c ≤ encodeCode c
codeSize≤encodeCode c =
  subst (λ size → size ≤ encodeCode c)
        (+-zeroʳ (codeSize c))
        (codeSize+base≤encodeCodeWithRest c zero zero (≤-refl zero))

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
  decodeCodeWithRest-sound :
    (fuel input : ℕ) → (c : Code) → (rest : ℕ) →
    decodeCodeWithRest fuel input ≡ just (c ,× rest) →
    input ≡ encodeCodeWithRest c rest
  decodeCodeWithRest-sound zero input c rest ()
  decodeCodeWithRest-sound (suc fuel) input c rest eq
    with undigit input | undigit-sound input
  ... | digitRest d0 input-rest | input-eq
    with decodeNatWithRest fuel input-rest | inspect (decodeNatWithRest fuel) input-rest
  ... | just (n ,× final) | [ nat-eq ] with eq
  ... | refl =
    trans input-eq
          (cong (appendDigit d0)
                (decodeNatWithRest-sound fuel input-rest n final nat-eq))
  decodeCodeWithRest-sound (suc fuel) input c rest eq
    | digitRest d0 input-rest | input-eq
    | nothing | [ nat-eq ] = impossible eq
    where
      impossible :
        nothing ≡ just (c ,× rest) →
        input ≡ encodeCodeWithRest c rest
      impossible ()
  decodeCodeWithRest-sound (suc fuel) input c rest eq
    | digitRest d1 input-rest | input-eq
    with decodeNatWithRest fuel input-rest | inspect (decodeNatWithRest fuel) input-rest
  ... | just (tag ,× rest') | [ nat-eq ]
    with decodeCodeListWithRest fuel rest' | inspect (decodeCodeListWithRest fuel) rest'
  ... | just (cs ,× final) | [ list-eq ] with eq
  ... | refl =
    trans input-eq
          (cong (appendDigit d1)
                (trans
                  (decodeNatWithRest-sound fuel input-rest tag rest' nat-eq)
                  (cong (encodeNatWithRest tag)
                        (decodeCodeListWithRest-sound fuel rest' cs final list-eq))))
  decodeCodeWithRest-sound (suc fuel) input c rest eq
    | digitRest d1 input-rest | input-eq
    | just (tag ,× rest') | [ nat-eq ]
    | nothing | [ list-eq ] = impossible eq
    where
      impossible :
        nothing ≡ just (c ,× rest) →
        input ≡ encodeCodeWithRest c rest
      impossible ()
  decodeCodeWithRest-sound (suc fuel) input c rest eq
    | digitRest d1 input-rest | input-eq
    | nothing | [ nat-eq ] = impossible eq
    where
      impossible :
        nothing ≡ just (c ,× rest) →
        input ≡ encodeCodeWithRest c rest
      impossible ()
  decodeCodeWithRest-sound (suc fuel) input c rest eq
    | digitRest d2 input-rest | input-eq = impossible eq
    where
      impossible :
        nothing ≡ just (c ,× rest) →
        input ≡ encodeCodeWithRest c rest
      impossible ()
  decodeCodeWithRest-sound (suc fuel) input c rest eq
    | digitRest d3 input-rest | input-eq = impossible eq
    where
      impossible :
        nothing ≡ just (c ,× rest) →
        input ≡ encodeCodeWithRest c rest
      impossible ()

  decodeCodeListWithRest-sound :
    (fuel input : ℕ) → (cs : List Code) → (rest : ℕ) →
    decodeCodeListWithRest fuel input ≡ just (cs ,× rest) →
    input ≡ encodeCodeListWithRest cs rest
  decodeCodeListWithRest-sound zero input cs rest ()
  decodeCodeListWithRest-sound (suc fuel) input cs rest eq
    with undigit input | undigit-sound input
  ... | digitRest d0 input-rest | input-eq with eq
  ... | refl = input-eq
  decodeCodeListWithRest-sound (suc fuel) input cs rest eq
    | digitRest d1 input-rest | input-eq
    with decodeCodeWithRest fuel input-rest | inspect (decodeCodeWithRest fuel) input-rest
  ... | just (c ,× rest') | [ code-eq ]
    with decodeCodeListWithRest fuel rest' | inspect (decodeCodeListWithRest fuel) rest'
  ... | just (cs' ,× final) | [ list-eq ] with eq
  ... | refl =
    trans input-eq
          (cong (appendDigit d1)
                (trans
                  (decodeCodeWithRest-sound fuel input-rest c rest' code-eq)
                  (cong (encodeCodeWithRest c)
                        (decodeCodeListWithRest-sound fuel rest' cs' final list-eq))))
  decodeCodeListWithRest-sound (suc fuel) input cs rest eq
    | digitRest d1 input-rest | input-eq
    | just (c ,× rest') | [ code-eq ]
    | nothing | [ list-eq ] = impossible eq
    where
      impossible :
        nothing ≡ just (cs ,× rest) →
        input ≡ encodeCodeListWithRest cs rest
      impossible ()
  decodeCodeListWithRest-sound (suc fuel) input cs rest eq
    | digitRest d1 input-rest | input-eq
    | nothing | [ code-eq ] = impossible eq
    where
      impossible :
        nothing ≡ just (cs ,× rest) →
        input ≡ encodeCodeListWithRest cs rest
      impossible ()
  decodeCodeListWithRest-sound (suc fuel) input cs rest eq
    | digitRest d2 input-rest | input-eq = impossible eq
    where
      impossible :
        nothing ≡ just (cs ,× rest) →
        input ≡ encodeCodeListWithRest cs rest
      impossible ()
  decodeCodeListWithRest-sound (suc fuel) input cs rest eq
    | digitRest d3 input-rest | input-eq = impossible eq
    where
      impossible :
        nothing ≡ just (cs ,× rest) →
        input ≡ encodeCodeListWithRest cs rest
      impossible ()

decodeCode-sound :
  (fuel input : ℕ) → (c : Code) →
  decodeCode fuel input ≡ just c →
  input ≡ encodeCode c
decodeCode-sound fuel input c eq
  with decodeCodeWithRest fuel input | inspect (decodeCodeWithRest fuel) input
... | just (c' ,× zero) | [ code-eq ] with eq
... | refl = decodeCodeWithRest-sound fuel input c zero code-eq
decodeCode-sound fuel input c eq
  | just (c' ,× suc rest) | [ code-eq ] = impossible eq
  where
    impossible : nothing ≡ just c → input ≡ encodeCode c
    impossible ()
decodeCode-sound fuel input c eq
  | nothing | [ code-eq ] = impossible eq
  where
    impossible : nothing ≡ just c → input ≡ encodeCode c
    impossible ()

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

decodeCode-roundTrip-extra :
  (c : Code) → (extra : ℕ) →
  decodeCode (suc (codeSize c + extra)) (encodeCode c) ≡ just c
decodeCode-roundTrip-extra c extra
  rewrite decodeCodeWithRest-roundTrip c zero extra = refl

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

decodeNatTermWithFuel-roundTrip-extra :
  (t : Term) → (extra : ℕ) →
  decodeNatTermWithFuel
    (suc (codeSize (canonicalCodeTerm t) + extra))
    (canonicalNatTerm t)
  ≡ just t
decodeNatTermWithFuel-roundTrip-extra t extra
  rewrite decodeCode-roundTrip-extra (canonicalCodeTerm t) extra
        | decodeTerm-roundTrip (codeSize (canonicalCodeTerm t) + extra) t = refl

decodeNatFormulaWithFuel-roundTrip :
  (A : Formula) →
  decodeNatFormulaWithFuel (suc (codeSize (canonicalCodeFormula A))) (canonicalNatFormula A)
  ≡ just A
decodeNatFormulaWithFuel-roundTrip A
  rewrite decodeCode-roundTrip (canonicalCodeFormula A)
        | decodeFormula-roundTrip (codeSize (canonicalCodeFormula A)) A = refl

decodeNatFormulaWithFuel-roundTrip-extra :
  (A : Formula) → (extra : ℕ) →
  decodeNatFormulaWithFuel
    (suc (codeSize (canonicalCodeFormula A) + extra))
    (canonicalNatFormula A)
  ≡ just A
decodeNatFormulaWithFuel-roundTrip-extra A extra
  rewrite decodeCode-roundTrip-extra (canonicalCodeFormula A) extra
        | decodeFormula-roundTrip (codeSize (canonicalCodeFormula A) + extra) A = refl

decodeNatTerm-roundTrip :
  (t : Term) → decodeNatTerm (canonicalNatTerm t) ≡ just t
decodeNatTerm-roundTrip t with codeSize≤encodeCode (canonicalCodeTerm t)
... | extra ,Σ eq =
  subst
    (λ fuel →
      decodeNatTermWithFuel (suc fuel) (canonicalNatTerm t) ≡ just t)
    (sym eq)
    (decodeNatTermWithFuel-roundTrip-extra t extra)

decodeNatFormula-roundTrip :
  (A : Formula) → decodeNatFormula (canonicalNatFormula A) ≡ just A
decodeNatFormula-roundTrip A with codeSize≤encodeCode (canonicalCodeFormula A)
... | extra ,Σ eq =
  subst
    (λ fuel →
      decodeNatFormulaWithFuel (suc fuel) (canonicalNatFormula A) ≡ just A)
    (sym eq)
    (decodeNatFormulaWithFuel-roundTrip-extra A extra)

decodeNatTerm-canonical :
  (n : ℕ) → (t : Term) →
  decodeNatTerm n ≡ just t →
  n ≡ canonicalNatTerm t
decodeNatTerm-canonical n t eq
  with decodeCode (suc n) n | inspect (decodeCode (suc n)) n
... | just c | [ code-eq ]
  with decodeTerm (suc n) c | inspect (decodeTerm (suc n)) c
... | just u | [ term-eq ] with eq
... | refl =
  trans (decodeCode-sound (suc n) n c code-eq)
        (cong encodeCode (decodeTerm-sound (suc n) c u term-eq))
decodeNatTerm-canonical n t eq
  | just c | [ code-eq ]
  | nothing | [ term-eq ] = impossible eq
  where
    impossible : nothing ≡ just t → n ≡ canonicalNatTerm t
    impossible ()
decodeNatTerm-canonical n t eq
  | nothing | [ code-eq ] = impossible eq
  where
    impossible : nothing ≡ just t → n ≡ canonicalNatTerm t
    impossible ()

decodeNatFormula-canonical :
  (n : ℕ) → (A : Formula) →
  decodeNatFormula n ≡ just A →
  n ≡ canonicalNatFormula A
decodeNatFormula-canonical n A eq
  with decodeCode (suc n) n | inspect (decodeCode (suc n)) n
... | just c | [ code-eq ]
  with decodeFormula (suc n) c | inspect (decodeFormula (suc n)) c
... | just B | [ formula-eq ] with eq
... | refl =
  trans (decodeCode-sound (suc n) n c code-eq)
        (cong encodeCode (decodeFormula-sound (suc n) c B formula-eq))
decodeNatFormula-canonical n A eq
  | just c | [ code-eq ]
  | nothing | [ formula-eq ] = impossible eq
  where
    impossible : nothing ≡ just A → n ≡ canonicalNatFormula A
    impossible ()
decodeNatFormula-canonical n A eq
  | nothing | [ code-eq ] = impossible eq
  where
    impossible : nothing ≡ just A → n ≡ canonicalNatFormula A
    impossible ()

abstract
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
