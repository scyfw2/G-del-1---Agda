{-# OPTIONS --safe #-}

module Godel.PRGraphSubstitution where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.PrimitiveRecursive
open import Godel.PRSequenceCoding using (wkTermN; wkVecN; wkVec)

substVec : {n : ℕ} → Term → Vec Term n → Vec Term n
substVec t [] = []
substVec t (u ∷ us) =
  substTerm (single t) u ∷ substVec t us

substTermVec : {n : ℕ} → Sub → Vec Term n → Vec Term n
substTermVec σ [] = []
substTermVec σ (u ∷ us) =
  substTerm σ u ∷ substTermVec σ us

lookup-substTermVec :
  {n : ℕ} →
  (σ : Sub) → (i : Fin n) → (xs : Vec Term n) →
  lookup i (substTermVec σ xs) ≡ substTerm σ (lookup i xs)
lookup-substTermVec σ fzero (x ∷ xs) = refl
lookup-substTermVec σ (fsuc i) (x ∷ xs) =
  lookup-substTermVec σ i xs

extSubN : ℕ → Sub → Sub
extSubN zero σ = σ
extSubN (suc n) σ = extSubN n (extSub σ)

subst-extSub-wkTerm :
  (σ : Sub) → (t : Term) →
  substTerm (extSub σ) (wkTerm t) ≡ wkTerm (substTerm σ t)
subst-extSub-wkTerm σ (var x) = refl
subst-extSub-wkTerm σ zeroᵗ = refl
subst-extSub-wkTerm σ (sucᵗ t) =
  cong sucᵗ_ (subst-extSub-wkTerm σ t)
subst-extSub-wkTerm σ (t +ᵗ u)
  rewrite subst-extSub-wkTerm σ t
        | subst-extSub-wkTerm σ u = refl
subst-extSub-wkTerm σ (t *ᵗ u)
  rewrite subst-extSub-wkTerm σ t
        | subst-extSub-wkTerm σ u = refl

subst-extSubN-wkTermN :
  (k : ℕ) → (σ : Sub) → (t : Term) →
  substTerm (extSubN k σ) (wkTermN k t) ≡
  wkTermN k (substTerm σ t)
subst-extSubN-wkTermN zero σ t = refl
subst-extSubN-wkTermN (suc k) σ t
  rewrite subst-extSubN-wkTermN k (extSub σ) (wkTerm t)
        | subst-extSub-wkTerm σ t = refl

subst-extSubN-wkVecN :
  {n : ℕ} →
  (k : ℕ) → (σ : Sub) → (xs : Vec Term n) →
  substTermVec (extSubN k σ) (wkVecN k xs) ≡
  wkVecN k (substTermVec σ xs)
subst-extSubN-wkVecN k σ [] = refl
subst-extSubN-wkVecN k σ (x ∷ xs)
  rewrite subst-extSubN-wkTermN k σ x
        | subst-extSubN-wkVecN k σ xs = refl

extSubN-suc-var :
  (k : ℕ) → (σ : Sub) → (i : ℕ) →
  extSubN k (extSub σ) (suc i) ≡
  wkTerm (extSubN k σ i)
extSubN-suc-var zero σ i = refl
extSubN-suc-var (suc k) σ i =
  extSubN-suc-var k (extSub σ) i

extSubN-top-var :
  (k : ℕ) → (σ : Sub) →
  extSubN (suc k) σ k ≡ var k
extSubN-top-var zero σ = refl
extSubN-top-var (suc k) σ
  rewrite extSubN-suc-var (suc k) σ k
        | extSubN-top-var k σ = refl

subst0-wkTerm :
  (s t : Term) →
  substTerm (single s) (wkTerm t) ≡ t
subst0-wkTerm s (var x) = refl
subst0-wkTerm s zeroᵗ = refl
subst0-wkTerm s (sucᵗ t) =
  cong sucᵗ_ (subst0-wkTerm s t)
subst0-wkTerm s (t +ᵗ u)
  rewrite subst0-wkTerm s t
        | subst0-wkTerm s u = refl
subst0-wkTerm s (t *ᵗ u)
  rewrite subst0-wkTerm s t
        | subst0-wkTerm s u = refl

subst0-wkTerms :
  (s : Term) → (ts : List Term) →
  substTerms (single s) (renameTerms suc ts) ≡ ts
subst0-wkTerms s [] = refl
subst0-wkTerms s (t ∷ ts)
  rewrite subst0-wkTerm s t
        | subst0-wkTerms s ts = refl

subst0-wkTermN :
  (k : ℕ) → (s t : Term) →
  substTerm (single s) (wkTerm (wkTermN k t)) ≡ wkTermN k t
subst0-wkTermN k s t =
  subst0-wkTerm s (wkTermN k t)

subst0-wkVec :
  {n : ℕ} →
  (s : Term) → (xs : Vec Term n) →
  substVec s (wkVec xs) ≡ xs
subst0-wkVec s [] = refl
subst0-wkVec s (x ∷ xs)
  rewrite subst0-wkTerm s x
        | subst0-wkVec s xs = refl

substTermVec-single-wkVec :
  {n : ℕ} →
  (s : Term) → (xs : Vec Term n) →
  substTermVec (single s) (wkVec xs) ≡ xs
substTermVec-single-wkVec s [] = refl
substTermVec-single-wkVec s (x ∷ xs)
  rewrite subst0-wkTerm s x
        | substTermVec-single-wkVec s xs = refl

lookup-subst0-wkVec :
  {n : ℕ} →
  (s : Term) → (i : Fin n) → (xs : Vec Term n) →
  substTerm (single s) (lookup i (wkVec xs)) ≡ lookup i xs
lookup-subst0-wkVec s fzero (x ∷ xs) =
  subst0-wkTerm s x
lookup-subst0-wkVec s (fsuc i) (x ∷ xs) =
  lookup-subst0-wkVec s i xs
