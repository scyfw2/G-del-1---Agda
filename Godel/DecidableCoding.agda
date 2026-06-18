{-# OPTIONS --safe #-}

module Godel.DecidableCoding where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List using (List; []; _∷_)
open import Godel.Core
open import Godel.Syntax

infix 6 _==ℕ_
infixr 5 _&&_

_&&_ : Bool → Bool → Bool
true && b = b
false && b = false

_==ℕ_ : ℕ → ℕ → Bool
zero ==ℕ zero = true
zero ==ℕ suc n = false
suc m ==ℕ zero = false
suc m ==ℕ suc n = m ==ℕ n

termEq : Term → Term → Bool
termsEq : List Term → List Term → Bool
formulaEq : Formula → Formula → Bool

termEq (var m) (var n) = m ==ℕ n
termEq zeroᵗ zeroᵗ = true
termEq (sucᵗ s) (sucᵗ t) = termEq s t
termEq (s₁ +ᵗ s₂) (t₁ +ᵗ t₂) = termEq s₁ t₁ && termEq s₂ t₂
termEq (s₁ *ᵗ s₂) (t₁ *ᵗ t₂) = termEq s₁ t₁ && termEq s₂ t₂
termEq s t = false

termsEq [] [] = true
termsEq (s ∷ ss) (t ∷ ts) = termEq s t && termsEq ss ts
termsEq ss ts = false

formulaEq (s₁ ≈ s₂) (t₁ ≈ t₂) = termEq s₁ t₁ && termEq s₂ t₂
formulaEq (Rel r ss) (Rel q ts) = (r ==ℕ q) && termsEq ss ts
formulaEq ⊥ᶠ ⊥ᶠ = true
formulaEq (A₁ ⇒ A₂) (B₁ ⇒ B₂) = formulaEq A₁ B₁ && formulaEq A₂ B₂
formulaEq (A₁ ∧ A₂) (B₁ ∧ B₂) = formulaEq A₁ B₁ && formulaEq A₂ B₂
formulaEq (A₁ ∨ A₂) (B₁ ∨ B₂) = formulaEq A₁ B₁ && formulaEq A₂ B₂
formulaEq (¬ᶠ A) (¬ᶠ B) = formulaEq A B
formulaEq (∀ᶠ A) (∀ᶠ B) = formulaEq A B
formulaEq (∃ᶠ A) (∃ᶠ B) = formulaEq A B
formulaEq A B = false

==ℕ-refl : (n : ℕ) → n ==ℕ n ≡ true
==ℕ-refl zero = refl
==ℕ-refl (suc n) = ==ℕ-refl n

termEq-refl : (t : Term) → termEq t t ≡ true
termsEq-refl : (ts : List Term) → termsEq ts ts ≡ true
formulaEq-refl : (A : Formula) → formulaEq A A ≡ true

termEq-refl (var n) = ==ℕ-refl n
termEq-refl zeroᵗ = refl
termEq-refl (sucᵗ t) = termEq-refl t
termEq-refl (s +ᵗ t)
  rewrite termEq-refl s | termEq-refl t = refl
termEq-refl (s *ᵗ t)
  rewrite termEq-refl s | termEq-refl t = refl

termsEq-refl [] = refl
termsEq-refl (t ∷ ts)
  rewrite termEq-refl t | termsEq-refl ts = refl

formulaEq-refl (s ≈ t)
  rewrite termEq-refl s | termEq-refl t = refl
formulaEq-refl (Rel r ts)
  rewrite ==ℕ-refl r | termsEq-refl ts = refl
formulaEq-refl ⊥ᶠ = refl
formulaEq-refl (A ⇒ B)
  rewrite formulaEq-refl A | formulaEq-refl B = refl
formulaEq-refl (A ∧ B)
  rewrite formulaEq-refl A | formulaEq-refl B = refl
formulaEq-refl (A ∨ B)
  rewrite formulaEq-refl A | formulaEq-refl B = refl
formulaEq-refl (¬ᶠ A) = formulaEq-refl A
formulaEq-refl (∀ᶠ A) = formulaEq-refl A
formulaEq-refl (∃ᶠ A) = formulaEq-refl A

false≠true : false ≡ true → ⊥
false≠true ()

&&-sound-left : (a b : Bool) → a && b ≡ true → a ≡ true
&&-sound-left true b eq = refl
&&-sound-left false b ()

&&-sound-right : (a b : Bool) → a && b ≡ true → b ≡ true
&&-sound-right true b eq = eq
&&-sound-right false b ()

==ℕ-sound : (m n : ℕ) → m ==ℕ n ≡ true → m ≡ n
==ℕ-sound zero zero eq = refl
==ℕ-sound zero (suc n) ()
==ℕ-sound (suc m) zero ()
==ℕ-sound (suc m) (suc n) eq = cong suc (==ℕ-sound m n eq)

termEq-sound : (s t : Term) → termEq s t ≡ true → s ≡ t
termsEq-sound : (ss ts : List Term) → termsEq ss ts ≡ true → ss ≡ ts
formulaEq-sound : (A B : Formula) → formulaEq A B ≡ true → A ≡ B

termEq-sound (var m) (var n) eq =
  cong var (==ℕ-sound m n eq)
termEq-sound (var m) zeroᵗ ()
termEq-sound (var m) (sucᵗ t) ()
termEq-sound (var m) (t₁ +ᵗ t₂) ()
termEq-sound (var m) (t₁ *ᵗ t₂) ()
termEq-sound zeroᵗ (var n) ()
termEq-sound zeroᵗ zeroᵗ eq = refl
termEq-sound zeroᵗ (sucᵗ t) ()
termEq-sound zeroᵗ (t₁ +ᵗ t₂) ()
termEq-sound zeroᵗ (t₁ *ᵗ t₂) ()
termEq-sound (sucᵗ s) (var n) ()
termEq-sound (sucᵗ s) zeroᵗ ()
termEq-sound (sucᵗ s) (sucᵗ t) eq =
  cong sucᵗ_ (termEq-sound s t eq)
termEq-sound (sucᵗ s) (t₁ +ᵗ t₂) ()
termEq-sound (sucᵗ s) (t₁ *ᵗ t₂) ()
termEq-sound (s₁ +ᵗ s₂) (var n) ()
termEq-sound (s₁ +ᵗ s₂) zeroᵗ ()
termEq-sound (s₁ +ᵗ s₂) (sucᵗ t) ()
termEq-sound (s₁ +ᵗ s₂) (t₁ +ᵗ t₂) eq
  rewrite termEq-sound s₁ t₁ (&&-sound-left (termEq s₁ t₁) (termEq s₂ t₂) eq)
        | termEq-sound s₂ t₂ (&&-sound-right (termEq s₁ t₁) (termEq s₂ t₂) eq) = refl
termEq-sound (s₁ +ᵗ s₂) (t₁ *ᵗ t₂) ()
termEq-sound (s₁ *ᵗ s₂) (var n) ()
termEq-sound (s₁ *ᵗ s₂) zeroᵗ ()
termEq-sound (s₁ *ᵗ s₂) (sucᵗ t) ()
termEq-sound (s₁ *ᵗ s₂) (t₁ +ᵗ t₂) ()
termEq-sound (s₁ *ᵗ s₂) (t₁ *ᵗ t₂) eq
  rewrite termEq-sound s₁ t₁ (&&-sound-left (termEq s₁ t₁) (termEq s₂ t₂) eq)
        | termEq-sound s₂ t₂ (&&-sound-right (termEq s₁ t₁) (termEq s₂ t₂) eq) = refl

termsEq-sound [] [] eq = refl
termsEq-sound [] (t ∷ ts) ()
termsEq-sound (s ∷ ss) [] ()
termsEq-sound (s ∷ ss) (t ∷ ts) eq
  rewrite termEq-sound s t (&&-sound-left (termEq s t) (termsEq ss ts) eq)
        | termsEq-sound ss ts (&&-sound-right (termEq s t) (termsEq ss ts) eq) = refl

formulaEq-sound (s₁ ≈ s₂) (t₁ ≈ t₂) eq
  rewrite termEq-sound s₁ t₁ (&&-sound-left (termEq s₁ t₁) (termEq s₂ t₂) eq)
        | termEq-sound s₂ t₂ (&&-sound-right (termEq s₁ t₁) (termEq s₂ t₂) eq) = refl
formulaEq-sound (s₁ ≈ s₂) (Rel r ts) ()
formulaEq-sound (s₁ ≈ s₂) ⊥ᶠ ()
formulaEq-sound (s₁ ≈ s₂) (B₁ ⇒ B₂) ()
formulaEq-sound (s₁ ≈ s₂) (B₁ ∧ B₂) ()
formulaEq-sound (s₁ ≈ s₂) (B₁ ∨ B₂) ()
formulaEq-sound (s₁ ≈ s₂) (¬ᶠ B) ()
formulaEq-sound (s₁ ≈ s₂) (∀ᶠ B) ()
formulaEq-sound (s₁ ≈ s₂) (∃ᶠ B) ()
formulaEq-sound (Rel r ss) (t₁ ≈ t₂) ()
formulaEq-sound (Rel r ss) (Rel q ts) eq
  rewrite ==ℕ-sound r q (&&-sound-left (r ==ℕ q) (termsEq ss ts) eq)
        | termsEq-sound ss ts (&&-sound-right (r ==ℕ q) (termsEq ss ts) eq) = refl
formulaEq-sound (Rel r ss) ⊥ᶠ ()
formulaEq-sound (Rel r ss) (B₁ ⇒ B₂) ()
formulaEq-sound (Rel r ss) (B₁ ∧ B₂) ()
formulaEq-sound (Rel r ss) (B₁ ∨ B₂) ()
formulaEq-sound (Rel r ss) (¬ᶠ B) ()
formulaEq-sound (Rel r ss) (∀ᶠ B) ()
formulaEq-sound (Rel r ss) (∃ᶠ B) ()
formulaEq-sound ⊥ᶠ (t₁ ≈ t₂) ()
formulaEq-sound ⊥ᶠ (Rel r ts) ()
formulaEq-sound ⊥ᶠ ⊥ᶠ eq = refl
formulaEq-sound ⊥ᶠ (B₁ ⇒ B₂) ()
formulaEq-sound ⊥ᶠ (B₁ ∧ B₂) ()
formulaEq-sound ⊥ᶠ (B₁ ∨ B₂) ()
formulaEq-sound ⊥ᶠ (¬ᶠ B) ()
formulaEq-sound ⊥ᶠ (∀ᶠ B) ()
formulaEq-sound ⊥ᶠ (∃ᶠ B) ()
formulaEq-sound (A₁ ⇒ A₂) (t₁ ≈ t₂) ()
formulaEq-sound (A₁ ⇒ A₂) (Rel r ts) ()
formulaEq-sound (A₁ ⇒ A₂) ⊥ᶠ ()
formulaEq-sound (A₁ ⇒ A₂) (B₁ ⇒ B₂) eq
  rewrite formulaEq-sound A₁ B₁ (&&-sound-left (formulaEq A₁ B₁) (formulaEq A₂ B₂) eq)
        | formulaEq-sound A₂ B₂ (&&-sound-right (formulaEq A₁ B₁) (formulaEq A₂ B₂) eq) = refl
formulaEq-sound (A₁ ⇒ A₂) (B₁ ∧ B₂) ()
formulaEq-sound (A₁ ⇒ A₂) (B₁ ∨ B₂) ()
formulaEq-sound (A₁ ⇒ A₂) (¬ᶠ B) ()
formulaEq-sound (A₁ ⇒ A₂) (∀ᶠ B) ()
formulaEq-sound (A₁ ⇒ A₂) (∃ᶠ B) ()
formulaEq-sound (A₁ ∧ A₂) (t₁ ≈ t₂) ()
formulaEq-sound (A₁ ∧ A₂) (Rel r ts) ()
formulaEq-sound (A₁ ∧ A₂) ⊥ᶠ ()
formulaEq-sound (A₁ ∧ A₂) (B₁ ⇒ B₂) ()
formulaEq-sound (A₁ ∧ A₂) (B₁ ∧ B₂) eq
  rewrite formulaEq-sound A₁ B₁ (&&-sound-left (formulaEq A₁ B₁) (formulaEq A₂ B₂) eq)
        | formulaEq-sound A₂ B₂ (&&-sound-right (formulaEq A₁ B₁) (formulaEq A₂ B₂) eq) = refl
formulaEq-sound (A₁ ∧ A₂) (B₁ ∨ B₂) ()
formulaEq-sound (A₁ ∧ A₂) (¬ᶠ B) ()
formulaEq-sound (A₁ ∧ A₂) (∀ᶠ B) ()
formulaEq-sound (A₁ ∧ A₂) (∃ᶠ B) ()
formulaEq-sound (A₁ ∨ A₂) (t₁ ≈ t₂) ()
formulaEq-sound (A₁ ∨ A₂) (Rel r ts) ()
formulaEq-sound (A₁ ∨ A₂) ⊥ᶠ ()
formulaEq-sound (A₁ ∨ A₂) (B₁ ⇒ B₂) ()
formulaEq-sound (A₁ ∨ A₂) (B₁ ∧ B₂) ()
formulaEq-sound (A₁ ∨ A₂) (B₁ ∨ B₂) eq
  rewrite formulaEq-sound A₁ B₁ (&&-sound-left (formulaEq A₁ B₁) (formulaEq A₂ B₂) eq)
        | formulaEq-sound A₂ B₂ (&&-sound-right (formulaEq A₁ B₁) (formulaEq A₂ B₂) eq) = refl
formulaEq-sound (A₁ ∨ A₂) (¬ᶠ B) ()
formulaEq-sound (A₁ ∨ A₂) (∀ᶠ B) ()
formulaEq-sound (A₁ ∨ A₂) (∃ᶠ B) ()
formulaEq-sound (¬ᶠ A) (t₁ ≈ t₂) ()
formulaEq-sound (¬ᶠ A) (Rel r ts) ()
formulaEq-sound (¬ᶠ A) ⊥ᶠ ()
formulaEq-sound (¬ᶠ A) (B₁ ⇒ B₂) ()
formulaEq-sound (¬ᶠ A) (B₁ ∧ B₂) ()
formulaEq-sound (¬ᶠ A) (B₁ ∨ B₂) ()
formulaEq-sound (¬ᶠ A) (¬ᶠ B) eq =
  cong ¬ᶠ_ (formulaEq-sound A B eq)
formulaEq-sound (¬ᶠ A) (∀ᶠ B) ()
formulaEq-sound (¬ᶠ A) (∃ᶠ B) ()
formulaEq-sound (∀ᶠ A) (t₁ ≈ t₂) ()
formulaEq-sound (∀ᶠ A) (Rel r ts) ()
formulaEq-sound (∀ᶠ A) ⊥ᶠ ()
formulaEq-sound (∀ᶠ A) (B₁ ⇒ B₂) ()
formulaEq-sound (∀ᶠ A) (B₁ ∧ B₂) ()
formulaEq-sound (∀ᶠ A) (B₁ ∨ B₂) ()
formulaEq-sound (∀ᶠ A) (¬ᶠ B) ()
formulaEq-sound (∀ᶠ A) (∀ᶠ B) eq =
  cong ∀ᶠ (formulaEq-sound A B eq)
formulaEq-sound (∀ᶠ A) (∃ᶠ B) ()
formulaEq-sound (∃ᶠ A) (t₁ ≈ t₂) ()
formulaEq-sound (∃ᶠ A) (Rel r ts) ()
formulaEq-sound (∃ᶠ A) ⊥ᶠ ()
formulaEq-sound (∃ᶠ A) (B₁ ⇒ B₂) ()
formulaEq-sound (∃ᶠ A) (B₁ ∧ B₂) ()
formulaEq-sound (∃ᶠ A) (B₁ ∨ B₂) ()
formulaEq-sound (∃ᶠ A) (¬ᶠ B) ()
formulaEq-sound (∃ᶠ A) (∀ᶠ B) ()
formulaEq-sound (∃ᶠ A) (∃ᶠ B) eq =
  cong ∃ᶠ (formulaEq-sound A B eq)
