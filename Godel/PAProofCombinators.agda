{-# OPTIONS --safe #-}

module Godel.PAProofCombinators where

open import Godel.Syntax
open import Godel.ProofSystem
open import Godel.PA

mp₂ :
  {A B C : Formula} →
  PA-provable (A ⇒ (B ⇒ C)) →
  PA-provable A →
  PA-provable B →
  PA-provable C
mp₂ p q r = modus-ponens (modus-ponens p q) r

and-intro-use :
  {A B : Formula} →
  PA-provable A →
  PA-provable B →
  PA-provable (A ∧ B)
and-intro-use = mp₂ and-introduce

and-left-use :
  {A B : Formula} →
  PA-provable (A ∧ B) →
  PA-provable A
and-left-use = modus-ponens and-elim-left

and-right-use :
  {A B : Formula} →
  PA-provable (A ∧ B) →
  PA-provable B
and-right-use = modus-ponens and-elim-right

and-left-imp-use :
  {A B C D E : Formula} →
  PA-provable (A ⇒ (C ⇒ E)) →
  PA-provable ((A ∧ B) ⇒ ((C ∧ D) ⇒ E))
and-left-imp-use p = modus-ponens and-left-imp p

implies-refl : {A : Formula} → PA-provable (A ⇒ A)
implies-refl {A} =
  modus-ponens
    (modus-ponens
      (hilbert-S {A = A} {B = A ⇒ A} {C = A})
      (hilbert-K {A = A} {B = A ⇒ A}))
    (hilbert-K {A = A} {B = A})

implies-trans :
  {A B C : Formula} →
  PA-provable (A ⇒ B) →
  PA-provable (B ⇒ C) →
  PA-provable (A ⇒ C)
implies-trans {A} {B} {C} p q =
  modus-ponens
    (modus-ponens
      (hilbert-S {A = A} {B = B} {C = C})
      (modus-ponens (hilbert-K {A = B ⇒ C} {B = A}) q))
    p

nested-and-intro :
  {A B : Formula} →
  PA-provable A →
  PA-provable B →
  PA-provable (A ∧ B)
nested-and-intro = and-intro-use

nested-and-proj-left :
  {A B : Formula} →
  PA-provable (A ∧ B) →
  PA-provable A
nested-and-proj-left = and-left-use

nested-and-proj-right :
  {A B : Formula} →
  PA-provable (A ∧ B) →
  PA-provable B
nested-and-proj-right = and-right-use

exists-intro-use :
  {A : Formula} → (t : Term) →
  PA-provable (subst0 t A) →
  PA-provable (∃ᶠ A)
exists-intro-use t p = modus-ponens (exists-introduce t) p

exists-elim-use :
  {A B : Formula} →
  PA-provable (∀ᶠ (A ⇒ wkFormula B)) →
  PA-provable (∃ᶠ A) →
  PA-provable B
exists-elim-use p q = modus-ponens (modus-ponens exists-eliminate p) q
