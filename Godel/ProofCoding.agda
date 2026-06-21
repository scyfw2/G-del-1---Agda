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

proofTagAfterTwentyone : ℕ → ℕ
proofTagAfterTwentyone zero = twentyone
proofTagAfterTwentyone (suc n) = suc (proofTagAfterTwentyone n)

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
codeDerivation axCode (exists-prefix-introduce-any k {I} {A}) =
  tag (proofTagAfterTwentyone 1)
      (pair k (pair (codeFormula I) (codeFormula A)))
codeDerivation axCode (exists-prefix-binary-lift k {A} {B} {C} {D}) =
  tag (proofTagAfterTwentyone 2)
      (pair k
        (pair (codeFormula A)
          (pair (codeFormula B)
            (pair (codeFormula C) (codeFormula D)))))
codeDerivation axCode (exists-prefix-premise-map-any k {E} {A} {B} {C} {D}) =
  tag (proofTagAfterTwentyone 3)
      (pair k
        (pair (codeFormula E)
          (pair (codeFormula A)
            (pair (codeFormula B)
              (pair (codeFormula C) (codeFormula D))))))
codeDerivation axCode (premise-change-any {E} {E'} {A} {B}) =
  tag (proofTagAfterTwentyone 4)
      (pair (codeFormula E)
        (pair (codeFormula E')
          (pair (codeFormula A) (codeFormula B))))
codeDerivation axCode (and-introduce {A} {B}) =
  tag (proofTagAfterTwentyone 5) (pair (codeFormula A) (codeFormula B))
codeDerivation axCode (and-elim-left {A} {B}) =
  tag (proofTagAfterTwentyone 6) (pair (codeFormula A) (codeFormula B))
codeDerivation axCode (and-elim-right {A} {B}) =
  tag (proofTagAfterTwentyone 7) (pair (codeFormula A) (codeFormula B))
codeDerivation axCode (or-intro-left {A} {B}) =
  tag (proofTagAfterTwentyone 8) (pair (codeFormula A) (codeFormula B))
codeDerivation axCode (or-intro-right {A} {B}) =
  tag (proofTagAfterTwentyone 9) (pair (codeFormula A) (codeFormula B))
codeDerivation axCode (eq-unique-value {y} {z} {c}) =
  tag (proofTagAfterTwentyone 10) (pair (codeTerm y) (pair (codeTerm z) (codeTerm c)))
codeDerivation axCode (and-left-imp {A} {B} {C} {D} {E}) =
  tag (proofTagAfterTwentyone 11)
      (pair (codeFormula A)
        (pair (codeFormula B)
          (pair (codeFormula C)
            (pair (codeFormula D) (codeFormula E)))))
codeDerivation axCode (and-right-imp {A} {B} {C} {D} {E}) =
  tag (proofTagAfterTwentyone 12)
      (pair (codeFormula A)
        (pair (codeFormula B)
          (pair (codeFormula C)
            (pair (codeFormula D) (codeFormula E)))))
codeDerivation axCode (and-left-imp1 {A} {B} {C} {E}) =
  tag (proofTagAfterTwentyone 13)
      (pair (codeFormula A)
        (pair (codeFormula B)
          (pair (codeFormula C) (codeFormula E))))
codeDerivation axCode (and-right-imp1 {A} {B} {C} {E}) =
  tag (proofTagAfterTwentyone 14)
      (pair (codeFormula A)
        (pair (codeFormula B)
          (pair (codeFormula C) (codeFormula E))))
codeDerivation axCode (imp-and-intro2 {A} {B} {C} {D}) =
  tag (proofTagAfterTwentyone 15)
      (pair (codeFormula A)
        (pair (codeFormula B)
          (pair (codeFormula C) (codeFormula D))))
codeDerivation axCode (and-both-map {A} {B} {C} {D}) =
  tag (proofTagAfterTwentyone 16)
      (pair (codeFormula A)
        (pair (codeFormula B)
          (pair (codeFormula C) (codeFormula D))))
codeDerivation axCode (and-left-map {A} {B} {C}) =
  tag (proofTagAfterTwentyone 17)
      (pair (codeFormula A)
        (pair (codeFormula B) (codeFormula C)))
codeDerivation axCode (premise-and-both-map {E} {A} {B} {C} {D}) =
  tag (proofTagAfterTwentyone 18)
      (pair (codeFormula E)
        (pair (codeFormula A)
          (pair (codeFormula B)
            (pair (codeFormula C) (codeFormula D)))))
codeDerivation axCode (premise-and-left-map {E} {A} {B} {C}) =
  tag (proofTagAfterTwentyone 19)
      (pair (codeFormula E)
        (pair (codeFormula A)
          (pair (codeFormula B) (codeFormula C))))
codeDerivation axCode (body-unique-compose {A} {B} {C} {D} {E} {F} {G}) =
  tag (proofTagAfterTwentyone 20)
      (pair (codeFormula A)
        (pair (codeFormula B)
          (pair (codeFormula C)
            (pair (codeFormula D)
              (pair (codeFormula E)
                (pair (codeFormula F) (codeFormula G)))))))
codeDerivation axCode (eq-subst-right {a} {b} {y}) =
  tag (proofTagAfterTwentyone 21)
      (pair (codeTerm a) (pair (codeTerm b) (codeTerm y)))
codeDerivation axCode (eq-subst-suc-right {a} {b} {y}) =
  tag (proofTagAfterTwentyone 22)
      (pair (codeTerm a) (pair (codeTerm b) (codeTerm y)))
codeDerivation axCode (closed-numeral-neq m n neq) =
  tag (proofTagAfterTwentyone 23) (pair m n)
codeDerivation axCode (contradiction-to-neg {A} {B}) =
  tag (proofTagAfterTwentyone 24)
      (pair (codeFormula A) (codeFormula B))

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
