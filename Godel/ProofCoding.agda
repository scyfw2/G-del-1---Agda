{-# OPTIONS --safe #-}

module Godel.ProofCoding where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.Coding
open import Godel.ProofSystem
open import Godel.PA

-- More tags for proof/axiom coding.
fourteen fifteen sixteen seventeen eighteen nineteen twenty twentyone : ℕ
fourteen  = suc thirteen
fifteen   = suc fourteen
sixteen   = suc fifteen
seventeen = suc sixteen
eighteen  = suc seventeen
nineteen  = suc eighteen
twenty    = suc nineteen
twentyone = suc twenty

-- Codes for PA axiom evidence.
codePAAxiom : {A : Formula} → PA A → ℕ
codePAAxiom pa-suc-not-zero    = tag fourteen zero
codePAAxiom pa-suc-injective   = tag fifteen zero
codePAAxiom pa-add-zero        = tag sixteen zero
codePAAxiom pa-add-suc         = tag seventeen zero
codePAAxiom pa-mul-zero        = tag eighteen zero
codePAAxiom pa-mul-suc         = tag nineteen zero
codePAAxiom (pa-induction A)   = tag twenty (codeFormula A)

-- Generic proof-tree coding, assuming axiom evidence can be coded.
codeDerivation : {Ax : Formula → Set} →
                 ({A : Formula} → Ax A → ℕ) →
                 {A : Formula} → Derives Ax A → ℕ
codeDerivation axCode (axiom a) =
  tag zero (axCode a)
codeDerivation axCode (hilbert-K {A} {B}) =
  tag one (pair (codeFormula A) (codeFormula B))
codeDerivation axCode (hilbert-S {A} {B} {C}) =
  tag two (pair (codeFormula A) (pair (codeFormula B) (codeFormula C)))
codeDerivation axCode (excluded-middle {A}) =
  tag three (codeFormula A)
codeDerivation axCode (modus-ponens p q) =
  tag four (pair (codeDerivation axCode p) (codeDerivation axCode q))
codeDerivation axCode (forall-generalize p) =
  tag five (codeDerivation axCode p)
codeDerivation axCode (forall-eliminate {A} t) =
  tag six (pair (codeFormula A) (codeTerm t))
codeDerivation axCode (exists-introduce {A} t) =
  tag seven (pair (codeFormula A) (codeTerm t))
codeDerivation axCode (eq-refl-rule t) =
  tag eight (codeTerm t)
codeDerivation axCode (eq-sym-rule {s} {t}) =
  tag nine (pair (codeTerm s) (codeTerm t))
codeDerivation axCode (eq-trans-rule {r} {s} {t}) =
  tag ten (pair (codeTerm r) (pair (codeTerm s) (codeTerm t)))
codeDerivation axCode (suc-cong-rule {s} {t}) =
  tag eleven (pair (codeTerm s) (codeTerm t))
codeDerivation axCode (add-cong-rule {a} {b} {c} {d}) =
  tag twelve (pair (codeTerm a) (pair (codeTerm b) (pair (codeTerm c) (codeTerm d))))
codeDerivation axCode (mul-cong-rule {a} {b} {c} {d}) =
  tag thirteen (pair (codeTerm a) (pair (codeTerm b) (pair (codeTerm c) (codeTerm d))))
codeDerivation axCode (exists-eliminate {A} {B}) =
  tag twentyone (pair (codeFormula A) (codeFormula B))
codeDerivation axCode (and-introduce {A} {B}) =
  tag (suc twentyone) (pair (codeFormula A) (codeFormula B))
codeDerivation axCode (and-elim-left {A} {B}) =
  tag (suc (suc twentyone)) (pair (codeFormula A) (codeFormula B))
codeDerivation axCode (and-elim-right {A} {B}) =
  tag (suc (suc (suc twentyone))) (pair (codeFormula A) (codeFormula B))
codeDerivation axCode (or-intro-left {A} {B}) =
  tag (suc (suc (suc (suc twentyone)))) (pair (codeFormula A) (codeFormula B))
codeDerivation axCode (or-intro-right {A} {B}) =
  tag (suc (suc (suc (suc (suc twentyone))))) (pair (codeFormula A) (codeFormula B))
codeDerivation axCode (eq-unique-value {y} {z} {c}) =
  tag (suc (suc (suc (suc (suc (suc twentyone)))))) (pair (codeTerm y) (pair (codeTerm z) (codeTerm c)))
codeDerivation axCode (and-left-imp {A} {B} {C} {D} {E}) =
  tag (suc (suc (suc (suc (suc (suc (suc twentyone)))))))
      (pair (codeFormula A)
        (pair (codeFormula B)
          (pair (codeFormula C)
            (pair (codeFormula D) (codeFormula E)))))
codeDerivation axCode (closed-numeral-neq m n neq) =
  tag (suc (suc (suc (suc (suc (suc (suc (suc twentyone)))))))) (pair m n)

codePAProof : {A : Formula} → PA-provable A → ℕ
codePAProof = codeDerivation codePAAxiom

-- Concrete meta-level proof-code relation for PA proof trees.
-- n codes a proof of A iff there is a PA derivation p of A whose proof-tree
-- code is n.
ProofCodePA : ℕ → Formula → Set
ProofCodePA n A = Σ (PA-provable A) (λ p → n ≡ codePAProof p)

proofCodePA-complete : {A : Formula} → PA-provable A → Σ ℕ (λ n → ProofCodePA n A)
proofCodePA-complete p = codePAProof p ,Σ (p ,Σ refl)

proofCodePA-sound : {A : Formula} → {n : ℕ} → ProofCodePA n A → PA-provable A
proofCodePA-sound c = fstΣ c
