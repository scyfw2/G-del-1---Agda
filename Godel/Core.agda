{-# OPTIONS --safe #-}

module Godel.Core where
open import Agda.Builtin.Equality public using (_≡_; refl)

infix  3 ¬_
infixr 4 _,×_
infixr 4 _,Σ_
infixr 3 _⊎_

-- Empty type: a contradiction has no constructors.
data ⊥ : Set where

-- Unit type.
record ⊤ : Set where
  constructor tt

-- Meta-level negation.
¬_ : Set → Set
¬ A = A → ⊥

-- Non-dependent pair.
record _×_ (A B : Set) : Set where
  constructor _,×_
  field
    fst : A
    snd : B
open _×_ public

-- Dependent pair / existential.
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,Σ_
  field
    fstΣ : A
    sndΣ : B fstΣ
open Σ public

∃ : {A : Set} → (A → Set) → Set
∃ {A} B = Σ A B

-- Sum type.
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

-- Equality helpers.
sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

subst : {A : Set} → (P : A → Set) → {x y : A} → x ≡ y → P x → P y
subst P refl px = px
