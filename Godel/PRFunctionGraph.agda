{-# OPTIONS --safe #-}

module Godel.PRFunctionGraph where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.PRBooleanHelpers
open import Godel.PRArithmeticSemantics
open import Godel.PRVectorHelpers
  using (mapVec-mapFinVec; projFinVec; evalPRFs-projFinVec)
open import Godel.PRRepresentabilityFinal
  using (PARepresentsRelation; prrel-represented)

-- Turn a PR function into its numeric graph relation.  This is the reusable
-- bridge used by later parser/checker components: once a destructor is a PRF,
-- its graph is automatically a PRRel and hence PA-representable through the
-- final structured PR theorem.

initFinVec : {n : ℕ} → Vec (Fin (suc n)) n
initFinVec {zero} = []
initFinVec {suc n} = fzero ∷ mapVec fsuc initFinVec

lastFin : {n : ℕ} → Fin (suc n)
lastFin {zero} = fzero
lastFin {suc n} = fsuc lastFin

initProjVec : {n : ℕ} → Vec (PRF (suc n)) n
initProjVec {n} = projFinVec initFinVec

graphArgs : {n : ℕ} → Vec ℕ n → ℕ → Vec ℕ (suc n)
graphArgs [] y = y ∷ []
graphArgs (x ∷ xs) y = x ∷ graphArgs xs y

lookup-tail-map :
  {k n : ℕ} →
  (x : ℕ) → (tail : Vec ℕ n) →
  (is : Vec (Fin n) k) →
  mapVec (λ i → lookup i (x ∷ tail)) (mapVec fsuc is) ≡
  mapVec (λ i → lookup i tail) is
lookup-tail-map x tail [] = refl
lookup-tail-map x tail (i ∷ is)
  rewrite lookup-tail-map x tail is = refl

lookup-initFinVec :
  {n : ℕ} →
  (xs : Vec ℕ n) → (y : ℕ) →
  mapVec (λ i → lookup i (graphArgs xs y)) initFinVec ≡ xs
lookup-initFinVec [] y = refl
lookup-initFinVec (x ∷ xs) y
  rewrite lookup-tail-map x (graphArgs xs y) initFinVec
        | lookup-initFinVec xs y = refl

evalPRFs-initProjVec :
  {n : ℕ} →
  (xs : Vec ℕ n) → (y : ℕ) →
  evalPRFs initProjVec (graphArgs xs y) ≡ xs
evalPRFs-initProjVec xs y
  rewrite evalPRFs-projFinVec initFinVec (graphArgs xs y)
        | lookup-initFinVec xs y = refl

lookup-lastFin :
  {n : ℕ} →
  (xs : Vec ℕ n) → (y : ℕ) →
  lookup lastFin (graphArgs xs y) ≡ y
lookup-lastFin [] y = refl
lookup-lastFin (x ∷ xs) y = lookup-lastFin xs y

functionGraphF : {n : ℕ} → PRF n → PRF (suc n)
functionGraphF f =
  compF eqNatF
    (compF f initProjVec ∷
     projF lastFin ∷ [])

functionGraphRel : {n : ℕ} → PRF n → PRRel (suc n)
functionGraphRel f = rel (functionGraphF f)

functionGraphF-correct :
  {n : ℕ} → (f : PRF n) →
  (xs : Vec ℕ n) → (y : ℕ) →
  evalPRF (functionGraphF f) (graphArgs xs y) ≡
  eqNatNat (evalPRF f xs) y
functionGraphF-correct f xs y
  rewrite evalPRFs-initProjVec xs y
        | lookup-lastFin xs y
        | eqNatF-correct (evalPRF f xs) y = refl

mulNat-one-one-graph : mulNat (suc zero) (suc zero) ≡ suc zero
mulNat-one-one-graph = refl

eqNatNat-refl-graph : (n : ℕ) → eqNatNat n n ≡ suc zero
eqNatNat-refl-graph n
  rewrite lessEqNat-refl n
        | mulNat-one-one-graph = refl

eqNatNat-sound-graph :
  (m n : ℕ) →
  eqNatNat m n ≡ suc zero →
  m ≡ n
eqNatNat-sound-graph zero zero eq = refl
eqNatNat-sound-graph zero (suc n) ()
eqNatNat-sound-graph (suc m) zero ()
eqNatNat-sound-graph (suc m) (suc n) eq =
  cong suc (eqNatNat-sound-graph m n eq)

functionGraphRel-represented :
  {n : ℕ} → (f : PRF n) →
  PARepresentsRelation (functionGraphRel f)
functionGraphRel-represented f =
  prrel-represented (functionGraphRel f)

functionGraphRel-complete :
  {n : ℕ} → (f : PRF n) →
  (xs : Vec ℕ n) →
  PRRel-holds
    (functionGraphRel f)
    (graphArgs xs (evalPRF f xs))
functionGraphRel-complete f xs
  rewrite functionGraphF-correct f xs (evalPRF f xs)
        | eqNatNat-refl-graph (evalPRF f xs) = refl

functionGraphRel-sound :
  {n : ℕ} → (f : PRF n) →
  (xs : Vec ℕ n) → (y : ℕ) →
  PRRel-holds (functionGraphRel f) (graphArgs xs y) →
  y ≡ evalPRF f xs
functionGraphRel-sound f xs y holds =
  sym
    (eqNatNat-sound-graph
      (evalPRF f xs)
      y
      (trans (sym (functionGraphF-correct f xs y)) holds))
