{-# OPTIONS --safe #-}

module Godel.ProofSystem where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax

exists-prefix : ℕ → Formula → Formula
exists-prefix zero A = A
exists-prefix (suc n) A = ∃ᶠ (exists-prefix n A)

-- A small Hilbert-style proof calculus parameterized by an axiom predicate.
-- This is deliberately minimal: enough structure to expose modus ponens,
-- universal elimination, and existential introduction used by arithmetic.
data Derives (Ax : Formula → Set) : Formula → Set where
  axiom               : {A : Formula} → Ax A → Derives Ax A

  hilbert-K           : {A B : Formula} →
                        Derives Ax (A ⇒ (B ⇒ A))

  hilbert-S           : {A B C : Formula} →
                        Derives Ax ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)))

  excluded-middle     : {A : Formula} →
                        Derives Ax (A ∨ (¬ᶠ A))

  modus-ponens        : {A B : Formula} →
                        Derives Ax (A ⇒ B) → Derives Ax A → Derives Ax B

  forall-generalize   : {A : Formula} →
                        Derives Ax A → Derives Ax (∀ᶠ A)

  forall-eliminate    : {A : Formula} → (t : Term) →
                        Derives Ax ((∀ᶠ A) ⇒ subst0 t A)

  exists-introduce    : {A : Formula} → (t : Term) →
                        Derives Ax (subst0 t A ⇒ ∃ᶠ A)

  exists-eliminate    : {A B : Formula} →
                        Derives Ax ((∀ᶠ (A ⇒ wkFormula B)) ⇒ (∃ᶠ A ⇒ B))

  exists-prefix-introduce-any :
                        (k : ℕ) → {I A : Formula} →
                        Derives Ax (I ⇒ exists-prefix k A)

  exists-prefix-binary-lift :
                        (k : ℕ) → {A B C D : Formula} →
                        Derives Ax
                          ((A ⇒ (B ⇒ D)) ⇒
                           (exists-prefix k A ⇒
                            (exists-prefix k B ⇒ C)))

  exists-prefix-premise-map-any :
                        (k : ℕ) → {E A B C D : Formula} →
                        Derives Ax
                          ((E ⇒ (A ⇒ B)) ⇒
                           (E ⇒
                            (exists-prefix k C ⇒ exists-prefix k D)))

  premise-change-any  : {E E' A B : Formula} →
                        Derives Ax
                          ((E' ⇒ (A ⇒ B)) ⇒
                           (E ⇒ (A ⇒ B)))

  and-introduce       : {A B : Formula} →
                        Derives Ax (A ⇒ (B ⇒ (A ∧ B)))

  and-elim-left       : {A B : Formula} →
                        Derives Ax ((A ∧ B) ⇒ A)

  and-elim-right      : {A B : Formula} →
                        Derives Ax ((A ∧ B) ⇒ B)

  or-intro-left       : {A B : Formula} →
                        Derives Ax (A ⇒ (A ∨ B))

  or-intro-right      : {A B : Formula} →
                        Derives Ax (B ⇒ (A ∨ B))

  eq-refl-rule        : (t : Term) →
                        Derives Ax (t ≈ t)

  eq-sym-rule         : {s t : Term} →
                        Derives Ax (s ≈ t ⇒ t ≈ s)

  eq-trans-rule       : {r s t : Term} →
                        Derives Ax (r ≈ s ⇒ (s ≈ t ⇒ r ≈ t))

  suc-cong-rule       : {s t : Term} →
                        Derives Ax (s ≈ t ⇒ sucᵗ s ≈ sucᵗ t)

  add-cong-rule       : {a b c d : Term} →
                        Derives Ax (a ≈ b ⇒ (c ≈ d ⇒ (a +ᵗ c) ≈ (b +ᵗ d)))

  mul-cong-rule       : {a b c d : Term} →
                        Derives Ax (a ≈ b ⇒ (c ≈ d ⇒ (a *ᵗ c) ≈ (b *ᵗ d)))

  eq-unique-value     : {y z c : Term} →
                        Derives Ax (y ≈ c ⇒ (z ≈ c ⇒ y ≈ z))

  and-left-imp        : {A B C D E : Formula} →
                        Derives Ax
                          ((A ⇒ (C ⇒ E)) ⇒
                           ((A ∧ B) ⇒ ((C ∧ D) ⇒ E)))

  and-right-imp       : {A B C D E : Formula} →
                        Derives Ax
                          ((B ⇒ (D ⇒ E)) ⇒
                           ((A ∧ B) ⇒ ((C ∧ D) ⇒ E)))

  and-left-imp1       : {A B C E : Formula} →
                        Derives Ax
                          ((A ⇒ (C ⇒ E)) ⇒
                           ((A ∧ B) ⇒ (C ⇒ E)))

  and-right-imp1      : {A B C E : Formula} →
                        Derives Ax
                          ((B ⇒ (C ⇒ E)) ⇒
                           ((A ∧ B) ⇒ (C ⇒ E)))

  imp-and-intro2      : {A B C D : Formula} →
                        Derives Ax
                          ((A ⇒ (B ⇒ C)) ⇒
                           ((A ⇒ (B ⇒ D)) ⇒
                            (A ⇒ (B ⇒ (C ∧ D)))))

  and-both-map        : {A B C D : Formula} →
                        Derives Ax
                          ((A ⇒ C) ⇒
                           ((B ⇒ D) ⇒
                            ((A ∧ B) ⇒ (C ∧ D))))

  and-left-map        : {A B C : Formula} →
                        Derives Ax
                          ((A ⇒ C) ⇒
                           ((A ∧ B) ⇒ (C ∧ B)))

  premise-and-both-map :
                        {E A B C D : Formula} →
                        Derives Ax
                          ((E ⇒ (A ⇒ C)) ⇒
                           ((E ⇒ (B ⇒ D)) ⇒
                            (E ⇒ ((A ∧ B) ⇒ (C ∧ D)))))

  premise-and-left-map :
                        {E A B C : Formula} →
                        Derives Ax
                          ((E ⇒ (A ⇒ C)) ⇒
                           (E ⇒ ((A ∧ B) ⇒ (C ∧ B))))

  body-unique-compose : {A B C D E F G : Formula} →
                        Derives Ax
                          ((A ⇒ (C ⇒ E)) ⇒
                           ((E ⇒ (B ⇒ F)) ⇒
                            ((F ⇒ (D ⇒ G)) ⇒
                             ((A ∧ B) ⇒ ((C ∧ D) ⇒ G)))))

  eq-subst-right      : {a b y : Term} →
                        Derives Ax (a ≈ b ⇒ (y ≈ a ⇒ y ≈ b))

  eq-subst-suc-right  : {a b y : Term} →
                        Derives Ax (a ≈ b ⇒ (y ≈ sucᵗ a ⇒ y ≈ sucᵗ b))

  closed-numeral-neq  : (m n : ℕ) →
                        ¬ (m ≡ n) →
                        Derives Ax (¬ᶠ (numeral m ≈ numeral n))

  contradiction-to-neg :
                        {A B : Formula} →
                        Derives Ax ((A ⇒ B) ⇒ (¬ᶠ B ⇒ ¬ᶠ A))

-- The object theory proves A if A is derivable from its axiom predicate.
ProvableFrom : (Formula → Set) → Formula → Set
ProvableFrom Ax A = Derives Ax A
