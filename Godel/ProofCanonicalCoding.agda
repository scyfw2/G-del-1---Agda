{-# OPTIONS --safe #-}

module Godel.ProofCanonicalCoding where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.CanonicalCoding
open import Godel.ProofSystem
open import Godel.PA

-- Canonical, decodable proof-tree coding.
--
-- Godel.ProofCoding.codeDerivation is kept as the legacy proof code used by
-- the current theorem-facing ProofCodePA relation.  This module mirrors that
-- tree coding into CanonicalCoding.Code, so the future proof checker has a
-- structural code that can be decoded and round-tripped.

canonicalPAAxiomCode : {A : Formula} → PA A → Code
canonicalPAAxiomCode pa-suc-not-zero =
  node 0 []
canonicalPAAxiomCode pa-suc-injective =
  node 1 []
canonicalPAAxiomCode pa-add-zero =
  node 2 []
canonicalPAAxiomCode pa-add-suc =
  node 3 []
canonicalPAAxiomCode pa-mul-zero =
  node 4 []
canonicalPAAxiomCode pa-mul-suc =
  node 5 []
canonicalPAAxiomCode (pa-induction A) =
  node 6 (canonicalCodeFormula A ∷ [])

canonicalDerivationCode :
  {Ax : Formula → Set} →
  ({A : Formula} → Ax A → Code) →
  {A : Formula} →
  Derives Ax A →
  Code
canonicalDerivationCode axCode (axiom a) =
  node 0 (axCode a ∷ [])
canonicalDerivationCode axCode (hilbert-K {A} {B}) =
  node 1 (canonicalCodeFormula A ∷ canonicalCodeFormula B ∷ [])
canonicalDerivationCode axCode (hilbert-S {A} {B} {C}) =
  node 2 (canonicalCodeFormula A ∷ canonicalCodeFormula B ∷ canonicalCodeFormula C ∷ [])
canonicalDerivationCode axCode (excluded-middle {A}) =
  node 3 (canonicalCodeFormula A ∷ [])
canonicalDerivationCode axCode (modus-ponens p q) =
  node 4 (canonicalDerivationCode axCode p ∷ canonicalDerivationCode axCode q ∷ [])
canonicalDerivationCode axCode (forall-generalize p) =
  node 5 (canonicalDerivationCode axCode p ∷ [])
canonicalDerivationCode axCode (forall-eliminate {A} t) =
  node 6 (canonicalCodeFormula A ∷ canonicalCodeTerm t ∷ [])
canonicalDerivationCode axCode (exists-introduce {A} t) =
  node 7 (canonicalCodeFormula A ∷ canonicalCodeTerm t ∷ [])
canonicalDerivationCode axCode (eq-refl-rule t) =
  node 8 (canonicalCodeTerm t ∷ [])
canonicalDerivationCode axCode (eq-sym-rule {s} {t}) =
  node 9 (canonicalCodeTerm s ∷ canonicalCodeTerm t ∷ [])
canonicalDerivationCode axCode (eq-trans-rule {r} {s} {t}) =
  node 10 (canonicalCodeTerm r ∷ canonicalCodeTerm s ∷ canonicalCodeTerm t ∷ [])
canonicalDerivationCode axCode (suc-cong-rule {s} {t}) =
  node 11 (canonicalCodeTerm s ∷ canonicalCodeTerm t ∷ [])
canonicalDerivationCode axCode (add-cong-rule {a} {b} {c} {d}) =
  node 12
    (canonicalCodeTerm a ∷
     canonicalCodeTerm b ∷
     canonicalCodeTerm c ∷
     canonicalCodeTerm d ∷ [])
canonicalDerivationCode axCode (mul-cong-rule {a} {b} {c} {d}) =
  node 13
    (canonicalCodeTerm a ∷
     canonicalCodeTerm b ∷
     canonicalCodeTerm c ∷
     canonicalCodeTerm d ∷ [])
canonicalDerivationCode axCode (exists-eliminate {A} {B}) =
  node 14 (canonicalCodeFormula A ∷ canonicalCodeFormula B ∷ [])
canonicalDerivationCode axCode (exists-prefix-introduce-any k {I} {A}) =
  node 15 (atom k ∷ canonicalCodeFormula I ∷ canonicalCodeFormula A ∷ [])
canonicalDerivationCode axCode (exists-prefix-binary-lift k {A} {B} {C} {D}) =
  node 16
    (atom k ∷
     canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     canonicalCodeFormula C ∷
     canonicalCodeFormula D ∷ [])
canonicalDerivationCode axCode (exists-prefix-premise-map-any k {E} {A} {B} {C} {D}) =
  node 17
    (atom k ∷
     canonicalCodeFormula E ∷
     canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     canonicalCodeFormula C ∷
     canonicalCodeFormula D ∷ [])
canonicalDerivationCode axCode (premise-change-any {E} {E'} {A} {B}) =
  node 18
    (canonicalCodeFormula E ∷
     canonicalCodeFormula E' ∷
     canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷ [])
canonicalDerivationCode axCode (and-introduce {A} {B}) =
  node 19 (canonicalCodeFormula A ∷ canonicalCodeFormula B ∷ [])
canonicalDerivationCode axCode (and-elim-left {A} {B}) =
  node 20 (canonicalCodeFormula A ∷ canonicalCodeFormula B ∷ [])
canonicalDerivationCode axCode (and-elim-right {A} {B}) =
  node 21 (canonicalCodeFormula A ∷ canonicalCodeFormula B ∷ [])
canonicalDerivationCode axCode (or-intro-left {A} {B}) =
  node 22 (canonicalCodeFormula A ∷ canonicalCodeFormula B ∷ [])
canonicalDerivationCode axCode (or-intro-right {A} {B}) =
  node 23 (canonicalCodeFormula A ∷ canonicalCodeFormula B ∷ [])
canonicalDerivationCode axCode (eq-unique-value {y} {z} {c}) =
  node 24 (canonicalCodeTerm y ∷ canonicalCodeTerm z ∷ canonicalCodeTerm c ∷ [])
canonicalDerivationCode axCode (and-left-imp {A} {B} {C} {D} {E}) =
  node 25
    (canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     canonicalCodeFormula C ∷
     canonicalCodeFormula D ∷
     canonicalCodeFormula E ∷ [])
canonicalDerivationCode axCode (and-right-imp {A} {B} {C} {D} {E}) =
  node 26
    (canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     canonicalCodeFormula C ∷
     canonicalCodeFormula D ∷
     canonicalCodeFormula E ∷ [])
canonicalDerivationCode axCode (and-left-imp1 {A} {B} {C} {E}) =
  node 27
    (canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     canonicalCodeFormula C ∷
     canonicalCodeFormula E ∷ [])
canonicalDerivationCode axCode (and-right-imp1 {A} {B} {C} {E}) =
  node 28
    (canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     canonicalCodeFormula C ∷
     canonicalCodeFormula E ∷ [])
canonicalDerivationCode axCode (imp-and-intro2 {A} {B} {C} {D}) =
  node 29
    (canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     canonicalCodeFormula C ∷
     canonicalCodeFormula D ∷ [])
canonicalDerivationCode axCode (and-both-map {A} {B} {C} {D}) =
  node 30
    (canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     canonicalCodeFormula C ∷
     canonicalCodeFormula D ∷ [])
canonicalDerivationCode axCode (and-left-map {A} {B} {C}) =
  node 31 (canonicalCodeFormula A ∷ canonicalCodeFormula B ∷ canonicalCodeFormula C ∷ [])
canonicalDerivationCode axCode (premise-and-both-map {E} {A} {B} {C} {D}) =
  node 32
    (canonicalCodeFormula E ∷
     canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     canonicalCodeFormula C ∷
     canonicalCodeFormula D ∷ [])
canonicalDerivationCode axCode (premise-and-left-map {E} {A} {B} {C}) =
  node 33
    (canonicalCodeFormula E ∷
     canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     canonicalCodeFormula C ∷ [])
canonicalDerivationCode axCode (body-unique-compose {A} {B} {C} {D} {E} {F} {G}) =
  node 34
    (canonicalCodeFormula A ∷
     canonicalCodeFormula B ∷
     canonicalCodeFormula C ∷
     canonicalCodeFormula D ∷
     canonicalCodeFormula E ∷
     canonicalCodeFormula F ∷
     canonicalCodeFormula G ∷ [])
canonicalDerivationCode axCode (eq-subst-right {a} {b} {y}) =
  node 35 (canonicalCodeTerm a ∷ canonicalCodeTerm b ∷ canonicalCodeTerm y ∷ [])
canonicalDerivationCode axCode (eq-subst-suc-right {a} {b} {y}) =
  node 36 (canonicalCodeTerm a ∷ canonicalCodeTerm b ∷ canonicalCodeTerm y ∷ [])
canonicalDerivationCode axCode (closed-numeral-neq m n neq) =
  node 37 (atom m ∷ atom n ∷ [])
canonicalDerivationCode axCode (contradiction-to-neg {A} {B}) =
  node 38 (canonicalCodeFormula A ∷ canonicalCodeFormula B ∷ [])

canonicalCodePAProof : {A : Formula} → PA-provable A → ℕ
canonicalCodePAProof p =
  encodeCode (canonicalDerivationCode canonicalPAAxiomCode p)

canonicalPAProofCodeRoundTrip :
  {A : Formula} → (p : PA-provable A) →
  decodeCode
    (suc (codeSize (canonicalDerivationCode canonicalPAAxiomCode p)))
    (canonicalCodePAProof p)
  ≡ just (canonicalDerivationCode canonicalPAAxiomCode p)
canonicalPAProofCodeRoundTrip p =
  decodeCode-roundTrip (canonicalDerivationCode canonicalPAAxiomCode p)

-- Canonical analogue of ProofCoding.ProofCodePA.  It is intentionally a new
-- relation, so the theorem-facing legacy relation remains stable while proof
-- checking migrates to a decodable code.
CanonicalProofCodePA : ℕ → Formula → Set
CanonicalProofCodePA n A =
  Σ (PA-provable A) (λ p → n ≡ canonicalCodePAProof p)

canonicalProofCodePA-complete :
  {A : Formula} →
  PA-provable A →
  Σ ℕ (λ n → CanonicalProofCodePA n A)
canonicalProofCodePA-complete p =
  canonicalCodePAProof p ,Σ (p ,Σ refl)

canonicalProofCodePA-sound :
  {A : Formula} → {n : ℕ} →
  CanonicalProofCodePA n A →
  PA-provable A
canonicalProofCodePA-sound c = fstΣ c
