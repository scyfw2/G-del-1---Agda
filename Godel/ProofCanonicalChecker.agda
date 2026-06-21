{-# OPTIONS --safe #-}

module Godel.ProofCanonicalChecker where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.CanonicalCoding
open import Godel.DecidableCoding
open import Godel.ProofSystem
open import Godel.PA
open import Godel.ProofCanonicalCoding

pattern p0 = zero
pattern p1 = suc p0
pattern p2 = suc p1
pattern p3 = suc p2
pattern p4 = suc p3
pattern p5 = suc p4
pattern p6 = suc p5
pattern p7 = suc p6
pattern p8 = suc p7
pattern p9 = suc p8
pattern p10 = suc p9
pattern p11 = suc p10
pattern p12 = suc p11
pattern p13 = suc p12
pattern p14 = suc p13
pattern p15 = suc p14
pattern p16 = suc p15
pattern p17 = suc p16
pattern p18 = suc p17
pattern p19 = suc p18
pattern p20 = suc p19
pattern p21 = suc p20
pattern p22 = suc p21
pattern p23 = suc p22
pattern p24 = suc p23
pattern p25 = suc p24
pattern p26 = suc p25
pattern p27 = suc p26
pattern p28 = suc p27
pattern p29 = suc p28
pattern p30 = suc p29
pattern p31 = suc p30
pattern p32 = suc p31
pattern p33 = suc p32
pattern p34 = suc p33
pattern p35 = suc p34
pattern p36 = suc p35
pattern p37 = suc p36
pattern p38 = suc p37

decodeCanonicalTerm : Code → Maybe Term
decodeCanonicalTerm c = decodeTerm (suc (codeSize c)) c

decodeCanonicalFormula : Code → Maybe Formula
decodeCanonicalFormula c = decodeFormula (suc (codeSize c)) c

decodeCanonicalTerm-roundTrip :
  (t : Term) →
  decodeCanonicalTerm (canonicalCodeTerm t) ≡ just t
decodeCanonicalTerm-roundTrip t =
  decodeTerm-roundTrip (codeSize (canonicalCodeTerm t)) t

decodeCanonicalFormula-roundTrip :
  (A : Formula) →
  decodeCanonicalFormula (canonicalCodeFormula A) ≡ just A
decodeCanonicalFormula-roundTrip A =
  decodeFormula-roundTrip (codeSize (canonicalCodeFormula A)) A

decodeCanonicalTerm-sound :
  (c : Code) → (t : Term) →
  decodeCanonicalTerm c ≡ just t →
  c ≡ canonicalCodeTerm t
decodeCanonicalTerm-sound c t =
  decodeTerm-sound (suc (codeSize c)) c t

decodeCanonicalFormula-sound :
  (c : Code) → (A : Formula) →
  decodeCanonicalFormula c ≡ just A →
  c ≡ canonicalCodeFormula A
decodeCanonicalFormula-sound c A =
  decodeFormula-sound (suc (codeSize c)) c A

neq→==ℕ-false :
  (m n : ℕ) →
  ¬ (m ≡ n) →
  m ==ℕ n ≡ false
neq→==ℕ-false m n neq with m ==ℕ n | inspect (_==ℕ_ m) n
... | true | [ eq ] = impossible (neq (==ℕ-sound m n eq))
  where
    impossible : ⊥ → true ≡ false
    impossible ()
... | false | [ eq ] = refl

just-injective : {A : Set} → {x y : A} → just x ≡ just y → x ≡ y
just-injective refl = refl

nothing≠just : {A B : Set} → {x : A} → nothing ≡ just x → B
nothing≠just ()

true≠false : true ≡ false → ⊥
true≠false ()

==ℕ-false→neq :
  (m n : ℕ) →
  m ==ℕ n ≡ false →
  ¬ (m ≡ n)
==ℕ-false→neq m n eq same =
  true≠false
    (trans
      (sym (==ℕ-refl m))
      (trans (cong (_==ℕ_ m) same) eq))

checkPAAxiomCode : Code → Maybe Formula
checkPAAxiomCode (node 0 []) =
  just (∀ᶠ (¬ᶠ (sucᵗ x₀ ≈ zeroᵗ)))
checkPAAxiomCode (node 1 []) =
  just (∀ᶠ (∀ᶠ ((sucᵗ x₁ ≈ sucᵗ x₀) ⇒ (x₁ ≈ x₀))))
checkPAAxiomCode (node 2 []) =
  just (∀ᶠ ((x₀ +ᵗ zeroᵗ) ≈ x₀))
checkPAAxiomCode (node 3 []) =
  just (∀ᶠ (∀ᶠ (((x₁ +ᵗ sucᵗ x₀) ≈ sucᵗ (x₁ +ᵗ x₀)))))
checkPAAxiomCode (node 4 []) =
  just (∀ᶠ ((x₀ *ᵗ zeroᵗ) ≈ zeroᵗ))
checkPAAxiomCode (node 5 []) =
  just (∀ᶠ (∀ᶠ (((x₁ *ᵗ sucᵗ x₀) ≈ ((x₁ *ᵗ x₀) +ᵗ x₁)))))
checkPAAxiomCode (node 6 (a ∷ [])) with decodeCanonicalFormula a
... | just A = just (induction A)
... | nothing = nothing
checkPAAxiomCode c = nothing

checkPAProofCode : Code → Maybe Formula
checkPAProofCode (node 0 (a ∷ [])) =
  checkPAAxiomCode a
checkPAProofCode (node 1 (a ∷ b ∷ []))
  with decodeCanonicalFormula a | decodeCanonicalFormula b
... | just A | just B = just (A ⇒ (B ⇒ A))
... | _ | _ = nothing
checkPAProofCode (node 2 (a ∷ b ∷ c ∷ []))
  with decodeCanonicalFormula a | decodeCanonicalFormula b | decodeCanonicalFormula c
... | just A | just B | just C =
  just ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)))
... | _ | _ | _ = nothing
checkPAProofCode (node 3 (a ∷ []))
  with decodeCanonicalFormula a
... | just A = just (A ∨ (¬ᶠ A))
... | nothing = nothing
checkPAProofCode (node 4 (p ∷ q ∷ []))
  with checkPAProofCode p | checkPAProofCode q
... | just (A ⇒ B) | just C with formulaEq A C
... | true = just B
... | false = nothing
checkPAProofCode (node 4 (p ∷ q ∷ []))
  | _ | _ = nothing
checkPAProofCode (node 5 (p ∷ []))
  with checkPAProofCode p
... | just A = just (∀ᶠ A)
... | nothing = nothing
checkPAProofCode (node 6 (a ∷ t ∷ []))
  with decodeCanonicalFormula a | decodeCanonicalTerm t
... | just A | just u = just ((∀ᶠ A) ⇒ subst0 u A)
... | _ | _ = nothing
checkPAProofCode (node 7 (a ∷ t ∷ []))
  with decodeCanonicalFormula a | decodeCanonicalTerm t
... | just A | just u = just (subst0 u A ⇒ ∃ᶠ A)
... | _ | _ = nothing
checkPAProofCode (node 8 (t ∷ []))
  with decodeCanonicalTerm t
... | just u = just (u ≈ u)
... | nothing = nothing
checkPAProofCode (node 9 (s ∷ t ∷ []))
  with decodeCanonicalTerm s | decodeCanonicalTerm t
... | just u | just v = just (u ≈ v ⇒ v ≈ u)
... | _ | _ = nothing
checkPAProofCode (node 10 (r ∷ s ∷ t ∷ []))
  with decodeCanonicalTerm r | decodeCanonicalTerm s | decodeCanonicalTerm t
... | just u | just v | just w = just (u ≈ v ⇒ (v ≈ w ⇒ u ≈ w))
... | _ | _ | _ = nothing
checkPAProofCode (node 11 (s ∷ t ∷ []))
  with decodeCanonicalTerm s | decodeCanonicalTerm t
... | just u | just v = just (u ≈ v ⇒ sucᵗ u ≈ sucᵗ v)
... | _ | _ = nothing
checkPAProofCode (node 12 (a ∷ b ∷ c ∷ d ∷ []))
  with decodeCanonicalTerm a | decodeCanonicalTerm b | decodeCanonicalTerm c | decodeCanonicalTerm d
... | just u | just v | just w | just x =
  just (u ≈ v ⇒ (w ≈ x ⇒ (u +ᵗ w) ≈ (v +ᵗ x)))
... | _ | _ | _ | _ = nothing
checkPAProofCode (node 13 (a ∷ b ∷ c ∷ d ∷ []))
  with decodeCanonicalTerm a | decodeCanonicalTerm b | decodeCanonicalTerm c | decodeCanonicalTerm d
... | just u | just v | just w | just x =
  just (u ≈ v ⇒ (w ≈ x ⇒ (u *ᵗ w) ≈ (v *ᵗ x)))
... | _ | _ | _ | _ = nothing
checkPAProofCode (node 14 (a ∷ b ∷ []))
  with decodeCanonicalFormula a | decodeCanonicalFormula b
... | just A | just B = just ((∀ᶠ (A ⇒ wkFormula B)) ⇒ (∃ᶠ A ⇒ B))
... | _ | _ = nothing
checkPAProofCode (node 15 (atom k ∷ i ∷ a ∷ []))
  with decodeCanonicalFormula i | decodeCanonicalFormula a
... | just I | just A = just (I ⇒ exists-prefix k A)
... | _ | _ = nothing
checkPAProofCode (node 16 (atom k ∷ a ∷ b ∷ c ∷ d ∷ []))
  with decodeCanonicalFormula a | decodeCanonicalFormula b
     | decodeCanonicalFormula c | decodeCanonicalFormula d
... | just A | just B | just C | just D =
  just ((A ⇒ (B ⇒ D)) ⇒ (exists-prefix k A ⇒ (exists-prefix k B ⇒ C)))
... | _ | _ | _ | _ = nothing
checkPAProofCode (node 17 (atom k ∷ e ∷ a ∷ b ∷ c ∷ d ∷ []))
  with decodeCanonicalFormula e | decodeCanonicalFormula a
     | decodeCanonicalFormula b | decodeCanonicalFormula c | decodeCanonicalFormula d
... | just E | just A | just B | just C | just D =
  just ((E ⇒ (A ⇒ B)) ⇒ (E ⇒ (exists-prefix k C ⇒ exists-prefix k D)))
... | _ | _ | _ | _ | _ = nothing
checkPAProofCode (node 18 (e ∷ e' ∷ a ∷ b ∷ []))
  with decodeCanonicalFormula e | decodeCanonicalFormula e'
     | decodeCanonicalFormula a | decodeCanonicalFormula b
... | just E | just E' | just A | just B =
  just ((E' ⇒ (A ⇒ B)) ⇒ (E ⇒ (A ⇒ B)))
... | _ | _ | _ | _ = nothing
checkPAProofCode (node 19 (a ∷ b ∷ []))
  with decodeCanonicalFormula a | decodeCanonicalFormula b
... | just A | just B = just (A ⇒ (B ⇒ (A ∧ B)))
... | _ | _ = nothing
checkPAProofCode (node 20 (a ∷ b ∷ []))
  with decodeCanonicalFormula a | decodeCanonicalFormula b
... | just A | just B = just ((A ∧ B) ⇒ A)
... | _ | _ = nothing
checkPAProofCode (node p21 (a ∷ b ∷ []))
  with decodeCanonicalFormula a | decodeCanonicalFormula b
... | just A | just B = just ((A ∧ B) ⇒ B)
... | _ | _ = nothing
checkPAProofCode (node p22 (a ∷ b ∷ []))
  with decodeCanonicalFormula a | decodeCanonicalFormula b
... | just A | just B = just (A ⇒ (A ∨ B))
... | _ | _ = nothing
checkPAProofCode (node p23 (a ∷ b ∷ []))
  with decodeCanonicalFormula a | decodeCanonicalFormula b
... | just A | just B = just (B ⇒ (A ∨ B))
... | _ | _ = nothing
checkPAProofCode (node p24 (y ∷ z ∷ c ∷ []))
  with decodeCanonicalTerm y | decodeCanonicalTerm z | decodeCanonicalTerm c
... | just u | just v | just w = just (u ≈ w ⇒ (v ≈ w ⇒ u ≈ v))
... | _ | _ | _ = nothing
checkPAProofCode (node p25 (a ∷ b ∷ c ∷ d ∷ e ∷ []))
  with decodeCanonicalFormula a | decodeCanonicalFormula b | decodeCanonicalFormula c
     | decodeCanonicalFormula d | decodeCanonicalFormula e
... | just A | just B | just C | just D | just E =
  just ((A ⇒ (C ⇒ E)) ⇒ ((A ∧ B) ⇒ ((C ∧ D) ⇒ E)))
... | _ | _ | _ | _ | _ = nothing
checkPAProofCode (node p26 (a ∷ b ∷ c ∷ d ∷ e ∷ []))
  with decodeCanonicalFormula a | decodeCanonicalFormula b | decodeCanonicalFormula c
     | decodeCanonicalFormula d | decodeCanonicalFormula e
... | just A | just B | just C | just D | just E =
  just ((B ⇒ (D ⇒ E)) ⇒ ((A ∧ B) ⇒ ((C ∧ D) ⇒ E)))
... | _ | _ | _ | _ | _ = nothing
checkPAProofCode (node p27 (a ∷ b ∷ c ∷ e ∷ []))
  with decodeCanonicalFormula a | decodeCanonicalFormula b
     | decodeCanonicalFormula c | decodeCanonicalFormula e
... | just A | just B | just C | just E =
  just ((A ⇒ (C ⇒ E)) ⇒ ((A ∧ B) ⇒ (C ⇒ E)))
... | _ | _ | _ | _ = nothing
checkPAProofCode (node p28 (a ∷ b ∷ c ∷ e ∷ []))
  with decodeCanonicalFormula a | decodeCanonicalFormula b
     | decodeCanonicalFormula c | decodeCanonicalFormula e
... | just A | just B | just C | just E =
  just ((B ⇒ (C ⇒ E)) ⇒ ((A ∧ B) ⇒ (C ⇒ E)))
... | _ | _ | _ | _ = nothing
checkPAProofCode (node p29 (a ∷ b ∷ c ∷ d ∷ []))
  with decodeCanonicalFormula a | decodeCanonicalFormula b
     | decodeCanonicalFormula c | decodeCanonicalFormula d
... | just A | just B | just C | just D =
  just ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ (B ⇒ D)) ⇒ (A ⇒ (B ⇒ (C ∧ D)))))
... | _ | _ | _ | _ = nothing
checkPAProofCode (node p30 (a ∷ b ∷ c ∷ d ∷ []))
  with decodeCanonicalFormula a | decodeCanonicalFormula b
     | decodeCanonicalFormula c | decodeCanonicalFormula d
... | just A | just B | just C | just D =
  just ((A ⇒ C) ⇒ ((B ⇒ D) ⇒ ((A ∧ B) ⇒ (C ∧ D))))
... | _ | _ | _ | _ = nothing
checkPAProofCode (node p31 (a ∷ b ∷ c ∷ []))
  with decodeCanonicalFormula a | decodeCanonicalFormula b | decodeCanonicalFormula c
... | just A | just B | just C = just ((A ⇒ C) ⇒ ((A ∧ B) ⇒ (C ∧ B)))
... | _ | _ | _ = nothing
checkPAProofCode (node p32 (e ∷ a ∷ b ∷ c ∷ d ∷ []))
  with decodeCanonicalFormula e | decodeCanonicalFormula a | decodeCanonicalFormula b
     | decodeCanonicalFormula c | decodeCanonicalFormula d
... | just E | just A | just B | just C | just D =
  just ((E ⇒ (A ⇒ C)) ⇒ ((E ⇒ (B ⇒ D)) ⇒ (E ⇒ ((A ∧ B) ⇒ (C ∧ D)))))
... | _ | _ | _ | _ | _ = nothing
checkPAProofCode (node p33 (e ∷ a ∷ b ∷ c ∷ []))
  with decodeCanonicalFormula e | decodeCanonicalFormula a
     | decodeCanonicalFormula b | decodeCanonicalFormula c
... | just E | just A | just B | just C =
  just ((E ⇒ (A ⇒ C)) ⇒ (E ⇒ ((A ∧ B) ⇒ (C ∧ B))))
... | _ | _ | _ | _ = nothing
checkPAProofCode (node p34 (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ []))
  with decodeCanonicalFormula a | decodeCanonicalFormula b | decodeCanonicalFormula c
     | decodeCanonicalFormula d | decodeCanonicalFormula e | decodeCanonicalFormula f
     | decodeCanonicalFormula g
... | just A | just B | just C | just D | just E | just F | just G =
  just
    ((A ⇒ (C ⇒ E)) ⇒
     ((E ⇒ (B ⇒ F)) ⇒
      ((F ⇒ (D ⇒ G)) ⇒
       ((A ∧ B) ⇒ ((C ∧ D) ⇒ G)))))
... | _ | _ | _ | _ | _ | _ | _ = nothing
checkPAProofCode (node p35 (a ∷ b ∷ y ∷ []))
  with decodeCanonicalTerm a | decodeCanonicalTerm b | decodeCanonicalTerm y
... | just u | just v | just w = just (u ≈ v ⇒ (w ≈ u ⇒ w ≈ v))
... | _ | _ | _ = nothing
checkPAProofCode (node p36 (a ∷ b ∷ y ∷ []))
  with decodeCanonicalTerm a | decodeCanonicalTerm b | decodeCanonicalTerm y
... | just u | just v | just w = just (u ≈ v ⇒ (w ≈ sucᵗ u ⇒ w ≈ sucᵗ v))
... | _ | _ | _ = nothing
checkPAProofCode (node p37 (atom m ∷ atom n ∷ [])) with m ==ℕ n
... | true = nothing
... | false = just (¬ᶠ (numeral m ≈ numeral n))
checkPAProofCode (node p38 (a ∷ b ∷ []))
  with decodeCanonicalFormula a | decodeCanonicalFormula b
... | just A | just B = just ((A ⇒ B) ⇒ (¬ᶠ B ⇒ ¬ᶠ A))
... | _ | _ = nothing
checkPAProofCode c = nothing

checkPAAxiomCode-complete :
  {A : Formula} →
  (a : PA A) →
  checkPAAxiomCode (canonicalPAAxiomCode a) ≡ just A
checkPAAxiomCode-complete pa-suc-not-zero = refl
checkPAAxiomCode-complete pa-suc-injective = refl
checkPAAxiomCode-complete pa-add-zero = refl
checkPAAxiomCode-complete pa-add-suc = refl
checkPAAxiomCode-complete pa-mul-zero = refl
checkPAAxiomCode-complete pa-mul-suc = refl
checkPAAxiomCode-complete (pa-induction A)
  rewrite decodeCanonicalFormula-roundTrip A = refl

checkPAProofCode-complete :
  {A : Formula} →
  (p : PA-provable A) →
  checkPAProofCode (canonicalDerivationCode canonicalPAAxiomCode p) ≡ just A
checkPAProofCode-complete (axiom a) =
  checkPAAxiomCode-complete a
checkPAProofCode-complete (hilbert-K {A} {B})
  rewrite decodeCanonicalFormula-roundTrip A
        | decodeCanonicalFormula-roundTrip B = refl
checkPAProofCode-complete (hilbert-S {A} {B} {C})
  rewrite decodeCanonicalFormula-roundTrip A
        | decodeCanonicalFormula-roundTrip B
        | decodeCanonicalFormula-roundTrip C = refl
checkPAProofCode-complete (excluded-middle {A})
  rewrite decodeCanonicalFormula-roundTrip A = refl
checkPAProofCode-complete (modus-ponens {A} {B} p q)
  rewrite checkPAProofCode-complete p
        | checkPAProofCode-complete q
        | formulaEq-refl A = refl
checkPAProofCode-complete (forall-generalize p)
  rewrite checkPAProofCode-complete p = refl
checkPAProofCode-complete (forall-eliminate {A} t)
  rewrite decodeCanonicalFormula-roundTrip A
        | decodeCanonicalTerm-roundTrip t = refl
checkPAProofCode-complete (exists-introduce {A} t)
  rewrite decodeCanonicalFormula-roundTrip A
        | decodeCanonicalTerm-roundTrip t = refl
checkPAProofCode-complete (eq-refl-rule t)
  rewrite decodeCanonicalTerm-roundTrip t = refl
checkPAProofCode-complete (eq-sym-rule {s} {t})
  rewrite decodeCanonicalTerm-roundTrip s
        | decodeCanonicalTerm-roundTrip t = refl
checkPAProofCode-complete (eq-trans-rule {r} {s} {t})
  rewrite decodeCanonicalTerm-roundTrip r
        | decodeCanonicalTerm-roundTrip s
        | decodeCanonicalTerm-roundTrip t = refl
checkPAProofCode-complete (suc-cong-rule {s} {t})
  rewrite decodeCanonicalTerm-roundTrip s
        | decodeCanonicalTerm-roundTrip t = refl
checkPAProofCode-complete (add-cong-rule {a} {b} {c} {d})
  rewrite decodeCanonicalTerm-roundTrip a
        | decodeCanonicalTerm-roundTrip b
        | decodeCanonicalTerm-roundTrip c
        | decodeCanonicalTerm-roundTrip d = refl
checkPAProofCode-complete (mul-cong-rule {a} {b} {c} {d})
  rewrite decodeCanonicalTerm-roundTrip a
        | decodeCanonicalTerm-roundTrip b
        | decodeCanonicalTerm-roundTrip c
        | decodeCanonicalTerm-roundTrip d = refl
checkPAProofCode-complete (exists-eliminate {A} {B})
  rewrite decodeCanonicalFormula-roundTrip A
        | decodeCanonicalFormula-roundTrip B = refl
checkPAProofCode-complete (exists-prefix-introduce-any k {I} {A})
  rewrite decodeCanonicalFormula-roundTrip I
        | decodeCanonicalFormula-roundTrip A = refl
checkPAProofCode-complete (exists-prefix-binary-lift k {A} {B} {C} {D})
  rewrite decodeCanonicalFormula-roundTrip A
        | decodeCanonicalFormula-roundTrip B
        | decodeCanonicalFormula-roundTrip C
        | decodeCanonicalFormula-roundTrip D = refl
checkPAProofCode-complete (exists-prefix-premise-map-any k {E} {A} {B} {C} {D})
  rewrite decodeCanonicalFormula-roundTrip E
        | decodeCanonicalFormula-roundTrip A
        | decodeCanonicalFormula-roundTrip B
        | decodeCanonicalFormula-roundTrip C
        | decodeCanonicalFormula-roundTrip D = refl
checkPAProofCode-complete (premise-change-any {E} {E'} {A} {B})
  rewrite decodeCanonicalFormula-roundTrip E
        | decodeCanonicalFormula-roundTrip E'
        | decodeCanonicalFormula-roundTrip A
        | decodeCanonicalFormula-roundTrip B = refl
checkPAProofCode-complete (and-introduce {A} {B})
  rewrite decodeCanonicalFormula-roundTrip A
        | decodeCanonicalFormula-roundTrip B = refl
checkPAProofCode-complete (and-elim-left {A} {B})
  rewrite decodeCanonicalFormula-roundTrip A
        | decodeCanonicalFormula-roundTrip B = refl
checkPAProofCode-complete (and-elim-right {A} {B})
  rewrite decodeCanonicalFormula-roundTrip A
        | decodeCanonicalFormula-roundTrip B = refl
checkPAProofCode-complete (or-intro-left {A} {B})
  rewrite decodeCanonicalFormula-roundTrip A
        | decodeCanonicalFormula-roundTrip B = refl
checkPAProofCode-complete (or-intro-right {A} {B})
  rewrite decodeCanonicalFormula-roundTrip A
        | decodeCanonicalFormula-roundTrip B = refl
checkPAProofCode-complete (eq-unique-value {y} {z} {c})
  rewrite decodeCanonicalTerm-roundTrip y
        | decodeCanonicalTerm-roundTrip z
        | decodeCanonicalTerm-roundTrip c = refl
checkPAProofCode-complete (and-left-imp {A} {B} {C} {D} {E})
  rewrite decodeCanonicalFormula-roundTrip A
        | decodeCanonicalFormula-roundTrip B
        | decodeCanonicalFormula-roundTrip C
        | decodeCanonicalFormula-roundTrip D
        | decodeCanonicalFormula-roundTrip E = refl
checkPAProofCode-complete (and-right-imp {A} {B} {C} {D} {E})
  rewrite decodeCanonicalFormula-roundTrip A
        | decodeCanonicalFormula-roundTrip B
        | decodeCanonicalFormula-roundTrip C
        | decodeCanonicalFormula-roundTrip D
        | decodeCanonicalFormula-roundTrip E = refl
checkPAProofCode-complete (and-left-imp1 {A} {B} {C} {E})
  rewrite decodeCanonicalFormula-roundTrip A
        | decodeCanonicalFormula-roundTrip B
        | decodeCanonicalFormula-roundTrip C
        | decodeCanonicalFormula-roundTrip E = refl
checkPAProofCode-complete (and-right-imp1 {A} {B} {C} {E})
  rewrite decodeCanonicalFormula-roundTrip A
        | decodeCanonicalFormula-roundTrip B
        | decodeCanonicalFormula-roundTrip C
        | decodeCanonicalFormula-roundTrip E = refl
checkPAProofCode-complete (imp-and-intro2 {A} {B} {C} {D})
  rewrite decodeCanonicalFormula-roundTrip A
        | decodeCanonicalFormula-roundTrip B
        | decodeCanonicalFormula-roundTrip C
        | decodeCanonicalFormula-roundTrip D = refl
checkPAProofCode-complete (and-both-map {A} {B} {C} {D})
  rewrite decodeCanonicalFormula-roundTrip A
        | decodeCanonicalFormula-roundTrip B
        | decodeCanonicalFormula-roundTrip C
        | decodeCanonicalFormula-roundTrip D = refl
checkPAProofCode-complete (and-left-map {A} {B} {C})
  rewrite decodeCanonicalFormula-roundTrip A
        | decodeCanonicalFormula-roundTrip B
        | decodeCanonicalFormula-roundTrip C = refl
checkPAProofCode-complete (premise-and-both-map {E} {A} {B} {C} {D})
  rewrite decodeCanonicalFormula-roundTrip E
        | decodeCanonicalFormula-roundTrip A
        | decodeCanonicalFormula-roundTrip B
        | decodeCanonicalFormula-roundTrip C
        | decodeCanonicalFormula-roundTrip D = refl
checkPAProofCode-complete (premise-and-left-map {E} {A} {B} {C})
  rewrite decodeCanonicalFormula-roundTrip E
        | decodeCanonicalFormula-roundTrip A
        | decodeCanonicalFormula-roundTrip B
        | decodeCanonicalFormula-roundTrip C = refl
checkPAProofCode-complete (body-unique-compose {A} {B} {C} {D} {E} {F} {G})
  rewrite decodeCanonicalFormula-roundTrip A
        | decodeCanonicalFormula-roundTrip B
        | decodeCanonicalFormula-roundTrip C
        | decodeCanonicalFormula-roundTrip D
        | decodeCanonicalFormula-roundTrip E
        | decodeCanonicalFormula-roundTrip F
        | decodeCanonicalFormula-roundTrip G = refl
checkPAProofCode-complete (eq-subst-right {a} {b} {y})
  rewrite decodeCanonicalTerm-roundTrip a
        | decodeCanonicalTerm-roundTrip b
        | decodeCanonicalTerm-roundTrip y = refl
checkPAProofCode-complete (eq-subst-suc-right {a} {b} {y})
  rewrite decodeCanonicalTerm-roundTrip a
        | decodeCanonicalTerm-roundTrip b
        | decodeCanonicalTerm-roundTrip y = refl
checkPAProofCode-complete (closed-numeral-neq m n neq)
  rewrite neq→==ℕ-false m n neq = refl
checkPAProofCode-complete (contradiction-to-neg {A} {B})
  rewrite decodeCanonicalFormula-roundTrip A
        | decodeCanonicalFormula-roundTrip B = refl

checkPAAxiomCode-sound :
  (c : Code) → {A : Formula} →
  checkPAAxiomCode c ≡ just A →
  PA A
checkPAAxiomCode-sound (node 0 []) eq =
  subst PA (just-injective eq) pa-suc-not-zero
checkPAAxiomCode-sound (node 1 []) eq =
  subst PA (just-injective eq) pa-suc-injective
checkPAAxiomCode-sound (node 2 []) eq =
  subst PA (just-injective eq) pa-add-zero
checkPAAxiomCode-sound (node 3 []) eq =
  subst PA (just-injective eq) pa-add-suc
checkPAAxiomCode-sound (node 4 []) eq =
  subst PA (just-injective eq) pa-mul-zero
checkPAAxiomCode-sound (node 5 []) eq =
  subst PA (just-injective eq) pa-mul-suc
checkPAAxiomCode-sound (node 6 (a ∷ [])) eq
  with decodeCanonicalFormula a
... | just A =
  subst PA (just-injective eq) (pa-induction A)
... | nothing = impossible eq
  where
    impossible : nothing ≡ just _ → PA _
    impossible ()
checkPAAxiomCode-sound (atom n) ()
checkPAAxiomCode-sound (node 0 (a ∷ cs)) ()
checkPAAxiomCode-sound (node 1 (a ∷ cs)) ()
checkPAAxiomCode-sound (node 2 (a ∷ cs)) ()
checkPAAxiomCode-sound (node 3 (a ∷ cs)) ()
checkPAAxiomCode-sound (node 4 (a ∷ cs)) ()
checkPAAxiomCode-sound (node 5 (a ∷ cs)) ()
checkPAAxiomCode-sound (node 6 []) ()
checkPAAxiomCode-sound (node 6 (a ∷ b ∷ cs)) ()
checkPAAxiomCode-sound (node (suc (suc (suc (suc (suc (suc (suc tag))))))) cs) ()

checkPAProofCode-sound :
  (c : Code) → {A : Formula} →
  checkPAProofCode c ≡ just A →
  PA-provable A
checkPAProofCode-sound (node 0 (a ∷ [])) eq =
  axiom (checkPAAxiomCode-sound a eq)
checkPAProofCode-sound (node 1 (a ∷ b ∷ [])) eq
  with decodeCanonicalFormula a | decodeCanonicalFormula b
... | just A | just B =
  subst PA-provable (just-injective eq) hilbert-K
... | just A | nothing = nothing≠just eq
... | nothing | mb = nothing≠just eq
checkPAProofCode-sound (node 2 (a ∷ b ∷ c ∷ [])) eq
  with decodeCanonicalFormula a | decodeCanonicalFormula b | decodeCanonicalFormula c
... | just A | just B | just C =
  subst PA-provable (just-injective eq) hilbert-S
... | just A | just B | nothing = nothing≠just eq
... | just A | nothing | mc = nothing≠just eq
... | nothing | mb | mc = nothing≠just eq
checkPAProofCode-sound (node 3 (a ∷ [])) eq
  with decodeCanonicalFormula a
... | just A =
  subst PA-provable (just-injective eq) excluded-middle
... | nothing = nothing≠just eq
checkPAProofCode-sound (node 4 (p ∷ q ∷ [])) eq
  with checkPAProofCode p | inspect checkPAProofCode p
     | checkPAProofCode q | inspect checkPAProofCode q
... | just (A ⇒ B) | [ p-eq ] | just C | [ q-eq ]
  with formulaEq A C | inspect (formulaEq A) C
... | true | [ formula-eq ] with eq
... | refl rewrite formulaEq-sound A C formula-eq =
  modus-ponens
    (checkPAProofCode-sound p p-eq)
    (checkPAProofCode-sound q q-eq)
checkPAProofCode-sound (node 4 (p ∷ q ∷ [])) eq
  | just (A ⇒ B) | [ p-eq ] | just C | [ q-eq ]
  | false | [ formula-eq ] = impossible eq
  where
    impossible : nothing ≡ just _ → PA-provable _
    impossible ()
checkPAProofCode-sound (node 4 (p ∷ q ∷ [])) eq
  | just ⊥ᶠ | [ p-eq ] | just C | [ q-eq ] = impossible eq
  where
    impossible : nothing ≡ just _ → PA-provable _
    impossible ()
checkPAProofCode-sound (node 4 (p ∷ q ∷ [])) eq
  | just (_ ≈ _) | [ p-eq ] | just C | [ q-eq ] = impossible eq
  where
    impossible : nothing ≡ just _ → PA-provable _
    impossible ()
checkPAProofCode-sound (node 4 (p ∷ q ∷ [])) eq
  | just (Rel r ts) | [ p-eq ] | just C | [ q-eq ] = impossible eq
  where
    impossible : nothing ≡ just _ → PA-provable _
    impossible ()
checkPAProofCode-sound (node 4 (p ∷ q ∷ [])) eq
  | just (_ ∧ _) | [ p-eq ] | just C | [ q-eq ] = impossible eq
  where
    impossible : nothing ≡ just _ → PA-provable _
    impossible ()
checkPAProofCode-sound (node 4 (p ∷ q ∷ [])) eq
  | just (_ ∨ _) | [ p-eq ] | just C | [ q-eq ] = impossible eq
  where
    impossible : nothing ≡ just _ → PA-provable _
    impossible ()
checkPAProofCode-sound (node 4 (p ∷ q ∷ [])) eq
  | just (¬ᶠ A) | [ p-eq ] | just C | [ q-eq ] = impossible eq
  where
    impossible : nothing ≡ just _ → PA-provable _
    impossible ()
checkPAProofCode-sound (node 4 (p ∷ q ∷ [])) eq
  | just (∀ᶠ A) | [ p-eq ] | just C | [ q-eq ] = impossible eq
  where
    impossible : nothing ≡ just _ → PA-provable _
    impossible ()
checkPAProofCode-sound (node 4 (p ∷ q ∷ [])) eq
  | just (∃ᶠ A) | [ p-eq ] | just C | [ q-eq ] = impossible eq
  where
    impossible : nothing ≡ just _ → PA-provable _
    impossible ()
checkPAProofCode-sound (node 4 (p ∷ q ∷ [])) eq
  | just (A ⇒ B) | [ p-eq ] | nothing | [ q-eq ] = nothing≠just eq
checkPAProofCode-sound (node 4 (p ∷ q ∷ [])) eq
  | just (u ≈ v) | [ p-eq ] | nothing | [ q-eq ] = nothing≠just eq
checkPAProofCode-sound (node 4 (p ∷ q ∷ [])) eq
  | just (Rel r ts) | [ p-eq ] | nothing | [ q-eq ] = nothing≠just eq
checkPAProofCode-sound (node 4 (p ∷ q ∷ [])) eq
  | just ⊥ᶠ | [ p-eq ] | nothing | [ q-eq ] = nothing≠just eq
checkPAProofCode-sound (node 4 (p ∷ q ∷ [])) eq
  | just (A ∧ B) | [ p-eq ] | nothing | [ q-eq ] = nothing≠just eq
checkPAProofCode-sound (node 4 (p ∷ q ∷ [])) eq
  | just (A ∨ B) | [ p-eq ] | nothing | [ q-eq ] = nothing≠just eq
checkPAProofCode-sound (node 4 (p ∷ q ∷ [])) eq
  | just (¬ᶠ A) | [ p-eq ] | nothing | [ q-eq ] = nothing≠just eq
checkPAProofCode-sound (node 4 (p ∷ q ∷ [])) eq
  | just (∀ᶠ A) | [ p-eq ] | nothing | [ q-eq ] = nothing≠just eq
checkPAProofCode-sound (node 4 (p ∷ q ∷ [])) eq
  | just (∃ᶠ A) | [ p-eq ] | nothing | [ q-eq ] = nothing≠just eq
checkPAProofCode-sound (node 4 (p ∷ q ∷ [])) eq
  | nothing | [ p-eq ] | mq | [ q-eq ] = nothing≠just eq
checkPAProofCode-sound (node 5 (p ∷ [])) eq
  with checkPAProofCode p | inspect checkPAProofCode p
... | just A | [ p-eq ] =
  subst PA-provable (just-injective eq)
    (forall-generalize (checkPAProofCode-sound p p-eq))
... | nothing | [ p-eq ] = impossible eq
  where
    impossible : nothing ≡ just _ → PA-provable _
    impossible ()
checkPAProofCode-sound (node 6 (a ∷ t ∷ [])) eq
  with decodeCanonicalFormula a | decodeCanonicalTerm t
... | just A | just u =
  subst PA-provable (just-injective eq) (forall-eliminate u)
... | just A | nothing = nothing≠just eq
... | nothing | mt = nothing≠just eq
checkPAProofCode-sound (node 7 (a ∷ t ∷ [])) eq
  with decodeCanonicalFormula a | decodeCanonicalTerm t
... | just A | just u =
  subst PA-provable (just-injective eq) (exists-introduce u)
... | just A | nothing = nothing≠just eq
... | nothing | mt = nothing≠just eq
checkPAProofCode-sound (node 8 (t ∷ [])) eq
  with decodeCanonicalTerm t
... | just u =
  subst PA-provable (just-injective eq) (eq-refl-rule u)
... | nothing = nothing≠just eq
checkPAProofCode-sound (node 9 (s ∷ t ∷ [])) eq
  with decodeCanonicalTerm s | decodeCanonicalTerm t
... | just u | just v =
  subst PA-provable (just-injective eq) eq-sym-rule
... | just u | nothing = nothing≠just eq
... | nothing | mt = nothing≠just eq
checkPAProofCode-sound (node 10 (r ∷ s ∷ t ∷ [])) eq
  with decodeCanonicalTerm r | decodeCanonicalTerm s | decodeCanonicalTerm t
... | just u | just v | just w =
  subst PA-provable (just-injective eq) eq-trans-rule
... | just u | just v | nothing = nothing≠just eq
... | just u | nothing | mw = nothing≠just eq
... | nothing | mv | mw = nothing≠just eq
checkPAProofCode-sound (node 11 (s ∷ t ∷ [])) eq
  with decodeCanonicalTerm s | decodeCanonicalTerm t
... | just u | just v =
  subst PA-provable (just-injective eq) suc-cong-rule
... | just u | nothing = nothing≠just eq
... | nothing | mt = nothing≠just eq
checkPAProofCode-sound (node 12 (a ∷ b ∷ c ∷ d ∷ [])) eq
  with decodeCanonicalTerm a | decodeCanonicalTerm b
     | decodeCanonicalTerm c | decodeCanonicalTerm d
... | just u | just v | just w | just x =
  subst PA-provable (just-injective eq) add-cong-rule
... | just u | just v | just w | nothing = nothing≠just eq
... | just u | just v | nothing | mx = nothing≠just eq
... | just u | nothing | mw | mx = nothing≠just eq
... | nothing | mv | mw | mx = nothing≠just eq
checkPAProofCode-sound (node 13 (a ∷ b ∷ c ∷ d ∷ [])) eq
  with decodeCanonicalTerm a | decodeCanonicalTerm b
     | decodeCanonicalTerm c | decodeCanonicalTerm d
... | just u | just v | just w | just x =
  subst PA-provable (just-injective eq) mul-cong-rule
... | just u | just v | just w | nothing = nothing≠just eq
... | just u | just v | nothing | mx = nothing≠just eq
... | just u | nothing | mw | mx = nothing≠just eq
... | nothing | mv | mw | mx = nothing≠just eq
checkPAProofCode-sound (node 14 (a ∷ b ∷ [])) eq
  with decodeCanonicalFormula a | decodeCanonicalFormula b
... | just A | just B =
  subst PA-provable (just-injective eq) exists-eliminate
... | just A | nothing = nothing≠just eq
... | nothing | mb = nothing≠just eq
checkPAProofCode-sound (node 15 (atom k ∷ i ∷ a ∷ [])) eq
  with decodeCanonicalFormula i | decodeCanonicalFormula a
... | just I | just A =
  subst PA-provable (just-injective eq) (exists-prefix-introduce-any k)
... | just I | nothing = nothing≠just eq
... | nothing | ma = nothing≠just eq
checkPAProofCode-sound (node 16 (atom k ∷ a ∷ b ∷ c ∷ d ∷ [])) eq
  with decodeCanonicalFormula a | decodeCanonicalFormula b
     | decodeCanonicalFormula c | decodeCanonicalFormula d
... | just A | just B | just C | just D =
  subst PA-provable (just-injective eq) (exists-prefix-binary-lift k)
... | just A | just B | just C | nothing = nothing≠just eq
... | just A | just B | nothing | md = nothing≠just eq
... | just A | nothing | mc | md = nothing≠just eq
... | nothing | mb | mc | md = nothing≠just eq
checkPAProofCode-sound (node 17 (atom k ∷ e ∷ a ∷ b ∷ c ∷ d ∷ [])) eq
  with decodeCanonicalFormula e | decodeCanonicalFormula a
     | decodeCanonicalFormula b | decodeCanonicalFormula c | decodeCanonicalFormula d
... | just E | just A | just B | just C | just D =
  subst PA-provable (just-injective eq) (exists-prefix-premise-map-any k)
... | just E | just A | just B | just C | nothing = nothing≠just eq
... | just E | just A | just B | nothing | md = nothing≠just eq
... | just E | just A | nothing | mc | md = nothing≠just eq
... | just E | nothing | mb | mc | md = nothing≠just eq
... | nothing | ma | mb | mc | md = nothing≠just eq
checkPAProofCode-sound (node 18 (e ∷ e' ∷ a ∷ b ∷ [])) eq
  with decodeCanonicalFormula e | decodeCanonicalFormula e'
     | decodeCanonicalFormula a | decodeCanonicalFormula b
... | just E | just E' | just A | just B =
  subst PA-provable (just-injective eq) premise-change-any
... | just E | just E' | just A | nothing = nothing≠just eq
... | just E | just E' | nothing | mb = nothing≠just eq
... | just E | nothing | ma | mb = nothing≠just eq
... | nothing | me' | ma | mb = nothing≠just eq
checkPAProofCode-sound (node 19 (a ∷ b ∷ [])) eq
  with decodeCanonicalFormula a | decodeCanonicalFormula b
... | just A | just B =
  subst PA-provable (just-injective eq) and-introduce
... | just A | nothing = nothing≠just eq
... | nothing | mb = nothing≠just eq
checkPAProofCode-sound (node 20 (a ∷ b ∷ [])) eq
  with decodeCanonicalFormula a | decodeCanonicalFormula b
... | just A | just B =
  subst PA-provable (just-injective eq) and-elim-left
... | just A | nothing = nothing≠just eq
... | nothing | mb = nothing≠just eq
checkPAProofCode-sound (node p21 (a ∷ b ∷ [])) eq
  with decodeCanonicalFormula a | decodeCanonicalFormula b
... | just A | just B =
  subst PA-provable (just-injective eq) and-elim-right
... | just A | nothing = nothing≠just eq
... | nothing | mb = nothing≠just eq
checkPAProofCode-sound (node p22 (a ∷ b ∷ [])) eq
  with decodeCanonicalFormula a | decodeCanonicalFormula b
... | just A | just B =
  subst PA-provable (just-injective eq) or-intro-left
... | just A | nothing = nothing≠just eq
... | nothing | mb = nothing≠just eq
checkPAProofCode-sound (node p23 (a ∷ b ∷ [])) eq
  with decodeCanonicalFormula a | decodeCanonicalFormula b
... | just A | just B =
  subst PA-provable (just-injective eq) or-intro-right
... | just A | nothing = nothing≠just eq
... | nothing | mb = nothing≠just eq
checkPAProofCode-sound (node p24 (y ∷ z ∷ c ∷ [])) eq
  with decodeCanonicalTerm y | decodeCanonicalTerm z | decodeCanonicalTerm c
... | just u | just v | just w =
  subst PA-provable (just-injective eq) eq-unique-value
... | just u | just v | nothing = nothing≠just eq
... | just u | nothing | mw = nothing≠just eq
... | nothing | mv | mw = nothing≠just eq
checkPAProofCode-sound (node p25 (a ∷ b ∷ c ∷ d ∷ e ∷ [])) eq
  with decodeCanonicalFormula a | decodeCanonicalFormula b | decodeCanonicalFormula c
     | decodeCanonicalFormula d | decodeCanonicalFormula e
... | just A | just B | just C | just D | just E =
  subst PA-provable (just-injective eq) and-left-imp
... | just A | just B | just C | just D | nothing = nothing≠just eq
... | just A | just B | just C | nothing | me = nothing≠just eq
... | just A | just B | nothing | md | me = nothing≠just eq
... | just A | nothing | mc | md | me = nothing≠just eq
... | nothing | mb | mc | md | me = nothing≠just eq
checkPAProofCode-sound (node p26 (a ∷ b ∷ c ∷ d ∷ e ∷ [])) eq
  with decodeCanonicalFormula a | decodeCanonicalFormula b | decodeCanonicalFormula c
     | decodeCanonicalFormula d | decodeCanonicalFormula e
... | just A | just B | just C | just D | just E =
  subst PA-provable (just-injective eq) and-right-imp
... | just A | just B | just C | just D | nothing = nothing≠just eq
... | just A | just B | just C | nothing | me = nothing≠just eq
... | just A | just B | nothing | md | me = nothing≠just eq
... | just A | nothing | mc | md | me = nothing≠just eq
... | nothing | mb | mc | md | me = nothing≠just eq
checkPAProofCode-sound (node p27 (a ∷ b ∷ c ∷ e ∷ [])) eq
  with decodeCanonicalFormula a | decodeCanonicalFormula b
     | decodeCanonicalFormula c | decodeCanonicalFormula e
... | just A | just B | just C | just E =
  subst PA-provable (just-injective eq) and-left-imp1
... | just A | just B | just C | nothing = nothing≠just eq
... | just A | just B | nothing | me = nothing≠just eq
... | just A | nothing | mc | me = nothing≠just eq
... | nothing | mb | mc | me = nothing≠just eq
checkPAProofCode-sound (node p28 (a ∷ b ∷ c ∷ e ∷ [])) eq
  with decodeCanonicalFormula a | decodeCanonicalFormula b
     | decodeCanonicalFormula c | decodeCanonicalFormula e
... | just A | just B | just C | just E =
  subst PA-provable (just-injective eq) and-right-imp1
... | just A | just B | just C | nothing = nothing≠just eq
... | just A | just B | nothing | me = nothing≠just eq
... | just A | nothing | mc | me = nothing≠just eq
... | nothing | mb | mc | me = nothing≠just eq
checkPAProofCode-sound (node p29 (a ∷ b ∷ c ∷ d ∷ [])) eq
  with decodeCanonicalFormula a | decodeCanonicalFormula b
     | decodeCanonicalFormula c | decodeCanonicalFormula d
... | just A | just B | just C | just D =
  subst PA-provable (just-injective eq) imp-and-intro2
... | just A | just B | just C | nothing = nothing≠just eq
... | just A | just B | nothing | md = nothing≠just eq
... | just A | nothing | mc | md = nothing≠just eq
... | nothing | mb | mc | md = nothing≠just eq
checkPAProofCode-sound (node p30 (a ∷ b ∷ c ∷ d ∷ [])) eq
  with decodeCanonicalFormula a | decodeCanonicalFormula b
     | decodeCanonicalFormula c | decodeCanonicalFormula d
... | just A | just B | just C | just D =
  subst PA-provable (just-injective eq) and-both-map
... | just A | just B | just C | nothing = nothing≠just eq
... | just A | just B | nothing | md = nothing≠just eq
... | just A | nothing | mc | md = nothing≠just eq
... | nothing | mb | mc | md = nothing≠just eq
checkPAProofCode-sound (node p31 (a ∷ b ∷ c ∷ [])) eq
  with decodeCanonicalFormula a | decodeCanonicalFormula b | decodeCanonicalFormula c
... | just A | just B | just C =
  subst PA-provable (just-injective eq) and-left-map
... | just A | just B | nothing = nothing≠just eq
... | just A | nothing | mc = nothing≠just eq
... | nothing | mb | mc = nothing≠just eq
checkPAProofCode-sound (node p32 (e ∷ a ∷ b ∷ c ∷ d ∷ [])) eq
  with decodeCanonicalFormula e | decodeCanonicalFormula a | decodeCanonicalFormula b
     | decodeCanonicalFormula c | decodeCanonicalFormula d
... | just E | just A | just B | just C | just D =
  subst PA-provable (just-injective eq) premise-and-both-map
... | just E | just A | just B | just C | nothing = nothing≠just eq
... | just E | just A | just B | nothing | md = nothing≠just eq
... | just E | just A | nothing | mc | md = nothing≠just eq
... | just E | nothing | mb | mc | md = nothing≠just eq
... | nothing | ma | mb | mc | md = nothing≠just eq
checkPAProofCode-sound (node p33 (e ∷ a ∷ b ∷ c ∷ [])) eq
  with decodeCanonicalFormula e | decodeCanonicalFormula a
     | decodeCanonicalFormula b | decodeCanonicalFormula c
... | just E | just A | just B | just C =
  subst PA-provable (just-injective eq) premise-and-left-map
... | just E | just A | just B | nothing = nothing≠just eq
... | just E | just A | nothing | mc = nothing≠just eq
... | just E | nothing | mb | mc = nothing≠just eq
... | nothing | ma | mb | mc = nothing≠just eq
checkPAProofCode-sound (node p34 (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ [])) eq
  with decodeCanonicalFormula a | decodeCanonicalFormula b | decodeCanonicalFormula c
     | decodeCanonicalFormula d | decodeCanonicalFormula e | decodeCanonicalFormula f
     | decodeCanonicalFormula g
... | just A | just B | just C | just D | just E | just F | just G =
  subst PA-provable (just-injective eq) body-unique-compose
... | just A | just B | just C | just D | just E | just F | nothing = nothing≠just eq
... | just A | just B | just C | just D | just E | nothing | mg = nothing≠just eq
... | just A | just B | just C | just D | nothing | mf | mg = nothing≠just eq
... | just A | just B | just C | nothing | me | mf | mg = nothing≠just eq
... | just A | just B | nothing | md | me | mf | mg = nothing≠just eq
... | just A | nothing | mc | md | me | mf | mg = nothing≠just eq
... | nothing | mb | mc | md | me | mf | mg = nothing≠just eq
checkPAProofCode-sound (node p35 (a ∷ b ∷ y ∷ [])) eq
  with decodeCanonicalTerm a | decodeCanonicalTerm b | decodeCanonicalTerm y
... | just u | just v | just w =
  subst PA-provable (just-injective eq) eq-subst-right
... | just u | just v | nothing = nothing≠just eq
... | just u | nothing | mw = nothing≠just eq
... | nothing | mv | mw = nothing≠just eq
checkPAProofCode-sound (node p36 (a ∷ b ∷ y ∷ [])) eq
  with decodeCanonicalTerm a | decodeCanonicalTerm b | decodeCanonicalTerm y
... | just u | just v | just w =
  subst PA-provable (just-injective eq) eq-subst-suc-right
... | just u | just v | nothing = nothing≠just eq
... | just u | nothing | mw = nothing≠just eq
... | nothing | mv | mw = nothing≠just eq
checkPAProofCode-sound (node p37 (atom m ∷ atom n ∷ [])) eq
  with m ==ℕ n | inspect (_==ℕ_ m) n
... | true | [ mn-eq ] = impossible eq
  where
    impossible : nothing ≡ just _ → PA-provable _
    impossible ()
... | false | [ mn-eq ] =
  subst PA-provable (just-injective eq)
    (closed-numeral-neq m n (==ℕ-false→neq m n mn-eq))
checkPAProofCode-sound (node p38 (a ∷ b ∷ [])) eq
  with decodeCanonicalFormula a | decodeCanonicalFormula b
... | just A | just B =
  subst PA-provable (just-injective eq) contradiction-to-neg
... | just A | nothing = nothing≠just eq
... | nothing | mb = nothing≠just eq
checkPAProofCode-sound (atom n) ()
checkPAProofCode-sound (node 0 []) ()
checkPAProofCode-sound (node 0 (a ∷ b ∷ cs)) ()
checkPAProofCode-sound (node 1 []) ()
checkPAProofCode-sound (node 1 (a ∷ [])) ()
checkPAProofCode-sound (node 1 (a ∷ b ∷ c ∷ cs)) ()
checkPAProofCode-sound (node 2 []) ()
checkPAProofCode-sound (node 2 (a ∷ [])) ()
checkPAProofCode-sound (node 2 (a ∷ b ∷ [])) ()
checkPAProofCode-sound (node 2 (a ∷ b ∷ c ∷ d ∷ cs)) ()
checkPAProofCode-sound (node 3 []) ()
checkPAProofCode-sound (node 3 (a ∷ b ∷ cs)) ()
checkPAProofCode-sound (node 4 []) ()
checkPAProofCode-sound (node 4 (p ∷ [])) ()
checkPAProofCode-sound (node 4 (p ∷ q ∷ r ∷ cs)) ()
checkPAProofCode-sound (node 5 []) ()
checkPAProofCode-sound (node 5 (p ∷ q ∷ cs)) ()
checkPAProofCode-sound (node 6 []) ()
checkPAProofCode-sound (node 6 (a ∷ [])) ()
checkPAProofCode-sound (node 6 (a ∷ t ∷ u ∷ cs)) ()
checkPAProofCode-sound (node 7 []) ()
checkPAProofCode-sound (node 7 (a ∷ [])) ()
checkPAProofCode-sound (node 7 (a ∷ t ∷ u ∷ cs)) ()
checkPAProofCode-sound (node 8 []) ()
checkPAProofCode-sound (node 8 (t ∷ u ∷ cs)) ()
checkPAProofCode-sound (node 9 []) ()
checkPAProofCode-sound (node 9 (s ∷ [])) ()
checkPAProofCode-sound (node 9 (s ∷ t ∷ u ∷ cs)) ()
checkPAProofCode-sound (node 10 []) ()
checkPAProofCode-sound (node 10 (r ∷ [])) ()
checkPAProofCode-sound (node 10 (r ∷ s ∷ [])) ()
checkPAProofCode-sound (node 10 (r ∷ s ∷ t ∷ u ∷ cs)) ()
checkPAProofCode-sound (node 11 []) ()
checkPAProofCode-sound (node 11 (s ∷ [])) ()
checkPAProofCode-sound (node 11 (s ∷ t ∷ u ∷ cs)) ()
checkPAProofCode-sound (node 12 []) ()
checkPAProofCode-sound (node 12 (a ∷ [])) ()
checkPAProofCode-sound (node 12 (a ∷ b ∷ [])) ()
checkPAProofCode-sound (node 12 (a ∷ b ∷ c ∷ [])) ()
checkPAProofCode-sound (node 12 (a ∷ b ∷ c ∷ d ∷ e ∷ cs)) ()
checkPAProofCode-sound (node 13 []) ()
checkPAProofCode-sound (node 13 (a ∷ [])) ()
checkPAProofCode-sound (node 13 (a ∷ b ∷ [])) ()
checkPAProofCode-sound (node 13 (a ∷ b ∷ c ∷ [])) ()
checkPAProofCode-sound (node 13 (a ∷ b ∷ c ∷ d ∷ e ∷ cs)) ()
checkPAProofCode-sound (node 14 []) ()
checkPAProofCode-sound (node 14 (a ∷ [])) ()
checkPAProofCode-sound (node 14 (a ∷ b ∷ c ∷ cs)) ()
checkPAProofCode-sound (node 15 []) ()
checkPAProofCode-sound (node 15 (atom k ∷ [])) ()
checkPAProofCode-sound (node 15 (atom k ∷ i ∷ [])) ()
checkPAProofCode-sound (node 15 (atom k ∷ i ∷ a ∷ b ∷ cs)) ()
checkPAProofCode-sound (node 15 (node tag ds ∷ cs)) ()
checkPAProofCode-sound (node 16 []) ()
checkPAProofCode-sound (node 16 (atom k ∷ [])) ()
checkPAProofCode-sound (node 16 (atom k ∷ a ∷ [])) ()
checkPAProofCode-sound (node 16 (atom k ∷ a ∷ b ∷ [])) ()
checkPAProofCode-sound (node 16 (atom k ∷ a ∷ b ∷ c ∷ [])) ()
checkPAProofCode-sound (node 16 (atom k ∷ a ∷ b ∷ c ∷ d ∷ e ∷ cs)) ()
checkPAProofCode-sound (node 16 (node tag ds ∷ cs)) ()
checkPAProofCode-sound (node 17 []) ()
checkPAProofCode-sound (node 17 (atom k ∷ [])) ()
checkPAProofCode-sound (node 17 (atom k ∷ e ∷ [])) ()
checkPAProofCode-sound (node 17 (atom k ∷ e ∷ a ∷ [])) ()
checkPAProofCode-sound (node 17 (atom k ∷ e ∷ a ∷ b ∷ [])) ()
checkPAProofCode-sound (node 17 (atom k ∷ e ∷ a ∷ b ∷ c ∷ [])) ()
checkPAProofCode-sound (node 17 (atom k ∷ e ∷ a ∷ b ∷ c ∷ d ∷ f ∷ cs)) ()
checkPAProofCode-sound (node 17 (node tag ds ∷ cs)) ()
checkPAProofCode-sound (node 18 []) ()
checkPAProofCode-sound (node 18 (e ∷ [])) ()
checkPAProofCode-sound (node 18 (e ∷ e' ∷ [])) ()
checkPAProofCode-sound (node 18 (e ∷ e' ∷ a ∷ [])) ()
checkPAProofCode-sound (node 18 (e ∷ e' ∷ a ∷ b ∷ c ∷ cs)) ()
checkPAProofCode-sound (node 19 []) ()
checkPAProofCode-sound (node 19 (a ∷ [])) ()
checkPAProofCode-sound (node 19 (a ∷ b ∷ c ∷ cs)) ()
checkPAProofCode-sound (node 20 []) ()
checkPAProofCode-sound (node 20 (a ∷ [])) ()
checkPAProofCode-sound (node 20 (a ∷ b ∷ c ∷ cs)) ()
checkPAProofCode-sound (node p21 []) ()
checkPAProofCode-sound (node p21 (a ∷ [])) ()
checkPAProofCode-sound (node p21 (a ∷ b ∷ c ∷ cs)) ()
checkPAProofCode-sound (node p22 []) ()
checkPAProofCode-sound (node p22 (a ∷ [])) ()
checkPAProofCode-sound (node p22 (a ∷ b ∷ c ∷ cs)) ()
checkPAProofCode-sound (node p23 []) ()
checkPAProofCode-sound (node p23 (a ∷ [])) ()
checkPAProofCode-sound (node p23 (a ∷ b ∷ c ∷ cs)) ()
checkPAProofCode-sound (node p24 []) ()
checkPAProofCode-sound (node p24 (y ∷ [])) ()
checkPAProofCode-sound (node p24 (y ∷ z ∷ [])) ()
checkPAProofCode-sound (node p24 (y ∷ z ∷ c ∷ d ∷ cs)) ()
checkPAProofCode-sound (node p25 []) ()
checkPAProofCode-sound (node p25 (a ∷ [])) ()
checkPAProofCode-sound (node p25 (a ∷ b ∷ [])) ()
checkPAProofCode-sound (node p25 (a ∷ b ∷ c ∷ [])) ()
checkPAProofCode-sound (node p25 (a ∷ b ∷ c ∷ d ∷ [])) ()
checkPAProofCode-sound (node p25 (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ cs)) ()
checkPAProofCode-sound (node p26 []) ()
checkPAProofCode-sound (node p26 (a ∷ [])) ()
checkPAProofCode-sound (node p26 (a ∷ b ∷ [])) ()
checkPAProofCode-sound (node p26 (a ∷ b ∷ c ∷ [])) ()
checkPAProofCode-sound (node p26 (a ∷ b ∷ c ∷ d ∷ [])) ()
checkPAProofCode-sound (node p26 (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ cs)) ()
checkPAProofCode-sound (node p27 []) ()
checkPAProofCode-sound (node p27 (a ∷ [])) ()
checkPAProofCode-sound (node p27 (a ∷ b ∷ [])) ()
checkPAProofCode-sound (node p27 (a ∷ b ∷ c ∷ [])) ()
checkPAProofCode-sound (node p27 (a ∷ b ∷ c ∷ e ∷ f ∷ cs)) ()
checkPAProofCode-sound (node p28 []) ()
checkPAProofCode-sound (node p28 (a ∷ [])) ()
checkPAProofCode-sound (node p28 (a ∷ b ∷ [])) ()
checkPAProofCode-sound (node p28 (a ∷ b ∷ c ∷ [])) ()
checkPAProofCode-sound (node p28 (a ∷ b ∷ c ∷ e ∷ f ∷ cs)) ()
checkPAProofCode-sound (node p29 []) ()
checkPAProofCode-sound (node p29 (a ∷ [])) ()
checkPAProofCode-sound (node p29 (a ∷ b ∷ [])) ()
checkPAProofCode-sound (node p29 (a ∷ b ∷ c ∷ [])) ()
checkPAProofCode-sound (node p29 (a ∷ b ∷ c ∷ d ∷ e ∷ cs)) ()
checkPAProofCode-sound (node p30 []) ()
checkPAProofCode-sound (node p30 (a ∷ [])) ()
checkPAProofCode-sound (node p30 (a ∷ b ∷ [])) ()
checkPAProofCode-sound (node p30 (a ∷ b ∷ c ∷ [])) ()
checkPAProofCode-sound (node p30 (a ∷ b ∷ c ∷ d ∷ e ∷ cs)) ()
checkPAProofCode-sound (node p31 []) ()
checkPAProofCode-sound (node p31 (a ∷ [])) ()
checkPAProofCode-sound (node p31 (a ∷ b ∷ [])) ()
checkPAProofCode-sound (node p31 (a ∷ b ∷ c ∷ d ∷ cs)) ()
checkPAProofCode-sound (node p32 []) ()
checkPAProofCode-sound (node p32 (e ∷ [])) ()
checkPAProofCode-sound (node p32 (e ∷ a ∷ [])) ()
checkPAProofCode-sound (node p32 (e ∷ a ∷ b ∷ [])) ()
checkPAProofCode-sound (node p32 (e ∷ a ∷ b ∷ c ∷ [])) ()
checkPAProofCode-sound (node p32 (e ∷ a ∷ b ∷ c ∷ d ∷ f ∷ cs)) ()
checkPAProofCode-sound (node p33 []) ()
checkPAProofCode-sound (node p33 (e ∷ [])) ()
checkPAProofCode-sound (node p33 (e ∷ a ∷ [])) ()
checkPAProofCode-sound (node p33 (e ∷ a ∷ b ∷ [])) ()
checkPAProofCode-sound (node p33 (e ∷ a ∷ b ∷ c ∷ d ∷ cs)) ()
checkPAProofCode-sound (node p34 []) ()
checkPAProofCode-sound (node p34 (a ∷ [])) ()
checkPAProofCode-sound (node p34 (a ∷ b ∷ [])) ()
checkPAProofCode-sound (node p34 (a ∷ b ∷ c ∷ [])) ()
checkPAProofCode-sound (node p34 (a ∷ b ∷ c ∷ d ∷ [])) ()
checkPAProofCode-sound (node p34 (a ∷ b ∷ c ∷ d ∷ e ∷ [])) ()
checkPAProofCode-sound (node p34 (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ [])) ()
checkPAProofCode-sound (node p34 (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ cs)) ()
checkPAProofCode-sound (node p35 []) ()
checkPAProofCode-sound (node p35 (a ∷ [])) ()
checkPAProofCode-sound (node p35 (a ∷ b ∷ [])) ()
checkPAProofCode-sound (node p35 (a ∷ b ∷ y ∷ z ∷ cs)) ()
checkPAProofCode-sound (node p36 []) ()
checkPAProofCode-sound (node p36 (a ∷ [])) ()
checkPAProofCode-sound (node p36 (a ∷ b ∷ [])) ()
checkPAProofCode-sound (node p36 (a ∷ b ∷ y ∷ z ∷ cs)) ()
checkPAProofCode-sound (node p37 []) ()
checkPAProofCode-sound (node p37 (atom m ∷ [])) ()
checkPAProofCode-sound (node p37 (atom m ∷ atom n ∷ c ∷ cs)) ()
checkPAProofCode-sound (node p37 (atom m ∷ node tag ds ∷ cs)) ()
checkPAProofCode-sound (node p37 (node tag ds ∷ cs)) ()
checkPAProofCode-sound (node p38 []) ()
checkPAProofCode-sound (node p38 (a ∷ [])) ()
checkPAProofCode-sound (node p38 (a ∷ b ∷ c ∷ cs)) ()
checkPAProofCode-sound (node (suc p38) cs) ()

decodeCanonicalPAProofCode-roundTrip :
  {A : Formula} →
  (p : PA-provable A) →
  decodeCode
    (suc (canonicalCodePAProof p))
    (canonicalCodePAProof p)
  ≡ just (canonicalDerivationCode canonicalPAAxiomCode p)
decodeCanonicalPAProofCode-roundTrip p
  with codeSize≤encodeCode (canonicalDerivationCode canonicalPAAxiomCode p)
... | extra ,Σ eq =
  subst
    (λ fuel →
      decodeCode
        (suc fuel)
        (canonicalCodePAProof p)
      ≡ just (canonicalDerivationCode canonicalPAAxiomCode p))
    (sym eq)
    (decodeCode-roundTrip-extra
      (canonicalDerivationCode canonicalPAAxiomCode p)
      extra)

checkCanonicalPAProofNat : ℕ → Maybe Formula
checkCanonicalPAProofNat proof-code
  with decodeCode (suc proof-code) proof-code
... | just c = checkPAProofCode c
... | nothing = nothing

ExecutableProofCodePA : ℕ → Formula → Set
ExecutableProofCodePA proof-code A =
  checkCanonicalPAProofNat proof-code ≡ just A

checkCanonicalPAProofNat-complete :
  {proof-code : ℕ} → {A : Formula} →
  CanonicalProofCodePA proof-code A →
  ExecutableProofCodePA proof-code A
checkCanonicalPAProofNat-complete (p ,Σ refl)
  rewrite decodeCanonicalPAProofCode-roundTrip p
        | checkPAProofCode-complete p = refl

checkCanonicalPAProofNat-sound :
  (proof-code : ℕ) → {A : Formula} →
  ExecutableProofCodePA proof-code A →
  PA-provable A
checkCanonicalPAProofNat-sound proof-code eq
  with decodeCode (suc proof-code) proof-code
... | just c =
  checkPAProofCode-sound c eq
... | nothing = nothing≠just eq

decodeCanonicalCodeNat-roundTrip :
  (c : Code) →
  decodeCode (suc (encodeCode c)) (encodeCode c) ≡ just c
decodeCanonicalCodeNat-roundTrip c with codeSize≤encodeCode c
... | extra ,Σ eq =
  subst
    (λ fuel → decodeCode (suc fuel) (encodeCode c) ≡ just c)
    (sym eq)
    (decodeCode-roundTrip-extra c extra)

DecodedExecutableProofCodePA : ℕ → Formula → Set
DecodedExecutableProofCodePA proof-code A =
  Σ Code
    (λ c →
      (proof-code ≡ encodeCode c) ×
      (checkPAProofCode c ≡ just A))

executableProofCodePA-to-decoded :
  (proof-code : ℕ) → {A : Formula} →
  ExecutableProofCodePA proof-code A →
  DecodedExecutableProofCodePA proof-code A
executableProofCodePA-to-decoded proof-code eq
  with decodeCode (suc proof-code) proof-code | inspect (decodeCode (suc proof-code)) proof-code
... | just c | [ code-eq ] =
  c ,Σ (decodeCode-sound (suc proof-code) proof-code c code-eq ,× eq)
... | nothing | [ code-eq ] = nothing≠just eq

decoded-to-executableProofCodePA :
  (proof-code : ℕ) → {A : Formula} →
  DecodedExecutableProofCodePA proof-code A →
  ExecutableProofCodePA proof-code A
decoded-to-executableProofCodePA .(encodeCode c) (c ,Σ (refl ,× check-eq))
  rewrite decodeCanonicalCodeNat-roundTrip c = check-eq
