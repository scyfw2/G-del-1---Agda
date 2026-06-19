{-# OPTIONS --safe #-}

module Godel.PAClosedArithmeticProofs where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.ProofSystem
open import Godel.PA
open import Godel.PAObjectLogic
open import Godel.PAClosedArithmetic

pa-provable-cong : {A B : Formula} → A ≡ B → PA-provable A → PA-provable B
pa-provable-cong eq p = subst PA-provable eq p

pa-all-elim : {A : Formula} → (t : Term) →
              PA-provable (∀ᶠ A) → PA-provable (subst0 t A)
pa-all-elim t p = modus-ponens (forall-eliminate t) p

mp₂ :
  {A B C : Formula} →
  PA-provable (A ⇒ (B ⇒ C)) →
  PA-provable A →
  PA-provable B →
  PA-provable C
mp₂ p q r = modus-ponens (modus-ponens p q) r

eq-trans-use :
  PAObjectLogic → {r s t : Term} →
  PA-provable (r ≈ s) → PA-provable (s ≈ t) → PA-provable (r ≈ t)
eq-trans-use logic =
  mp₂ (PAObjectLogic.eq-trans-PA logic)

suc-cong-use :
  PAObjectLogic → {s t : Term} →
  PA-provable (s ≈ t) → PA-provable (sucᵗ s ≈ sucᵗ t)
suc-cong-use logic p = modus-ponens (PAObjectLogic.suc-cong-PA logic) p

add-cong-use :
  PAObjectLogic → {a b c d : Term} →
  PA-provable (a ≈ b) →
  PA-provable (c ≈ d) →
  PA-provable ((a +ᵗ c) ≈ (b +ᵗ d))
add-cong-use logic =
  mp₂ (PAObjectLogic.add-cong-PA logic)

mul-cong-use :
  PAObjectLogic → {a b c d : Term} →
  PA-provable (a ≈ b) →
  PA-provable (c ≈ d) →
  PA-provable ((a *ᵗ c) ≈ (b *ᵗ d))
mul-cong-use logic =
  mp₂ (PAObjectLogic.mul-cong-PA logic)

+-assoc : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
+-assoc zero b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

+-zeroʳ : (m : ℕ) → m + zero ≡ m
+-zeroʳ zero = refl
+-zeroʳ (suc m) = cong suc (+-zeroʳ m)

+-sucʳ : (m n : ℕ) → m + suc n ≡ suc (m + n)
+-sucʳ zero n = refl
+-sucʳ (suc m) n = cong suc (+-sucʳ m n)

*-zeroʳ : (m : ℕ) → m * zero ≡ zero
*-zeroʳ zero = refl
*-zeroʳ (suc m) rewrite *-zeroʳ m = refl

*-sucʳ : (m n : ℕ) → m * suc n ≡ (m * n) + m
*-sucʳ zero n = refl
*-sucʳ (suc m) n
  rewrite *-sucʳ m n
        | sym (+-assoc n (m * n) m)
        | +-sucʳ (n + (m * n)) m = refl

subst-wk-numeral :
  (m n : ℕ) →
  substTerm (single (numeral n)) (wkTerm (numeral m)) ≡ numeral m
subst-wk-numeral m n =
  trans
    (cong (substTerm (single (numeral n))) (wk-numeral m))
    (subst-numeral (single (numeral n)) m)

pa-suc-not-zero-instance :
  (n : ℕ) → PA-provable (¬ᶠ (sucᵗ (numeral n) ≈ zeroᵗ))
pa-suc-not-zero-instance n =
  pa-all-elim (numeral n) (axiom pa-suc-not-zero)

pa-add-zero-instance :
  (m : ℕ) → PA-provable ((numeral m +ᵗ zeroᵗ) ≈ numeral m)
pa-add-zero-instance m =
  pa-all-elim (numeral m) (axiom pa-add-zero)

pa-add-suc-instance :
  (m n : ℕ) →
  PA-provable
    ((numeral m +ᵗ sucᵗ (numeral n))
     ≈ sucᵗ (numeral m +ᵗ numeral n))
pa-add-suc-instance m n =
  pa-provable-cong
    (cong
      (λ u → (u +ᵗ sucᵗ (numeral n)) ≈ sucᵗ (u +ᵗ numeral n))
      (subst-wk-numeral m n))
    (pa-all-elim (numeral n)
      (pa-all-elim (numeral m) (axiom pa-add-suc)))

pa-mul-zero-instance :
  (m : ℕ) → PA-provable ((numeral m *ᵗ zeroᵗ) ≈ zeroᵗ)
pa-mul-zero-instance m =
  pa-all-elim (numeral m) (axiom pa-mul-zero)

pa-mul-suc-instance :
  (m n : ℕ) →
  PA-provable
    ((numeral m *ᵗ sucᵗ (numeral n))
     ≈ ((numeral m *ᵗ numeral n) +ᵗ numeral m))
pa-mul-suc-instance m n =
  pa-provable-cong
    (cong
      (λ u → (u *ᵗ sucᵗ (numeral n)) ≈ ((u *ᵗ numeral n) +ᵗ u))
      (subst-wk-numeral m n))
    (pa-all-elim (numeral n)
      (pa-all-elim (numeral m) (axiom pa-mul-suc)))

pa-add-computes-fromObjectLogic :
  PAObjectLogic →
  (m n : ℕ) →
  PA-provable ((numeral m +ᵗ numeral n) ≈ numeral (m + n))
pa-add-computes-fromObjectLogic logic m zero =
  pa-provable-cong
    (cong (λ k → (numeral m +ᵗ zeroᵗ) ≈ numeral k)
          (sym (+-zeroʳ m)))
    (pa-add-zero-instance m)
pa-add-computes-fromObjectLogic logic m (suc n) =
  pa-provable-cong
    (cong (λ k → (numeral m +ᵗ numeral (suc n)) ≈ numeral k)
          (sym (+-sucʳ m n)))
    (eq-trans-use logic
      (pa-add-suc-instance m n)
      (suc-cong-use logic (pa-add-computes-fromObjectLogic logic m n)))

pa-mul-computes-fromObjectLogic :
  PAObjectLogic →
  (m n : ℕ) →
  PA-provable ((numeral m *ᵗ numeral n) ≈ numeral (m * n))
pa-mul-computes-fromObjectLogic logic m zero =
  pa-provable-cong
    (cong (λ k → (numeral m *ᵗ zeroᵗ) ≈ numeral k)
          (sym (*-zeroʳ m)))
    (pa-mul-zero-instance m)
pa-mul-computes-fromObjectLogic logic m (suc n) =
  pa-provable-cong
    (cong (λ k → (numeral m *ᵗ numeral (suc n)) ≈ numeral k)
          (sym (*-sucʳ m n)))
    (eq-trans-use logic
      (eq-trans-use logic
        (pa-mul-suc-instance m n)
        (add-cong-use logic
          (pa-mul-computes-fromObjectLogic logic m n)
          (PAObjectLogic.eq-refl-PA logic (numeral m))))
      (pa-add-computes-fromObjectLogic logic (m * n) m))

paClosedArithmetic-fromObjectLogic :
  PAObjectLogic → PAClosedArithmetic
paClosedArithmetic-fromObjectLogic logic = record
  { pa-add-computes = pa-add-computes-fromObjectLogic logic
  ; pa-mul-computes = pa-mul-computes-fromObjectLogic logic
  ; pa-suc-not-zero-closed = pa-suc-not-zero-instance
  }

paProofInfrastructure-fromObjectLogic :
  PAObjectLogic → PAProofInfrastructure
paProofInfrastructure-fromObjectLogic logic = record
  { object-logic = logic
  ; closed-arithmetic = paClosedArithmetic-fromObjectLogic logic
  }
