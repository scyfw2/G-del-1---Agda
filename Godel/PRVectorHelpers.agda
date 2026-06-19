{-# OPTIONS --safe #-}

module Godel.PRVectorHelpers where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.PrimitiveRecursive

mapFinVec :
  {k n m : ℕ} →
  (Fin n → Fin m) →
  Vec (Fin n) k →
  Vec (Fin m) k
mapFinVec f [] = []
mapFinVec f (i ∷ is) = f i ∷ mapFinVec f is

finVec : {n : ℕ} → Vec (Fin n) n
finVec {zero} = []
finVec {suc n} = fzero ∷ mapFinVec fsuc finVec

projFinVec : {k m : ℕ} → Vec (Fin m) k → Vec (PRF m) k
projFinVec [] = []
projFinVec (i ∷ is) = projF i ∷ projFinVec is

projVec : {n : ℕ} → Vec (PRF n) n
projVec = projFinVec finVec

drop1FinVec : {n : ℕ} → Vec (Fin (suc n)) n
drop1FinVec = mapFinVec fsuc finVec

drop2FinVec : {n : ℕ} → Vec (Fin (suc (suc n))) n
drop2FinVec = mapFinVec (λ i → fsuc (fsuc i)) finVec

drop3FinVec : {n : ℕ} → Vec (Fin (suc (suc (suc n)))) n
drop3FinVec = mapFinVec (λ i → fsuc (fsuc (fsuc i))) finVec

drop1ProjVec : {n : ℕ} → Vec (PRF (suc n)) n
drop1ProjVec = projFinVec drop1FinVec

drop2ProjVec : {n : ℕ} → Vec (PRF (suc (suc n))) n
drop2ProjVec = projFinVec drop2FinVec

drop3ProjVec : {n : ℕ} → Vec (PRF (suc (suc (suc n)))) n
drop3ProjVec = projFinVec drop3FinVec

mapVec-mapFinVec :
  {A : Set} → {k n m : ℕ} →
  (f : Fin m → A) →
  (g : Fin n → Fin m) →
  (is : Vec (Fin n) k) →
  mapVec f (mapFinVec g is) ≡ mapVec (λ i → f (g i)) is
mapVec-mapFinVec f g [] = refl
mapVec-mapFinVec f g (i ∷ is)
  rewrite mapVec-mapFinVec f g is = refl

evalPRFs-projFinVec :
  {k m : ℕ} →
  (is : Vec (Fin m) k) →
  (xs : Vec ℕ m) →
  evalPRFs (projFinVec is) xs ≡ mapVec (λ i → lookup i xs) is
evalPRFs-projFinVec [] xs = refl
evalPRFs-projFinVec (i ∷ is) xs
  rewrite evalPRFs-projFinVec is xs = refl

lookup-finVec :
  {n : ℕ} →
  (xs : Vec ℕ n) →
  mapVec (λ i → lookup i xs) finVec ≡ xs
lookup-finVec [] = refl
lookup-finVec (x ∷ xs)
  rewrite mapVec-mapFinVec
            (λ i → lookup i (x ∷ xs))
            fsuc
            finVec
        | lookup-finVec xs = refl

evalPRFs-projVec :
  {n : ℕ} →
  (xs : Vec ℕ n) →
  evalPRFs projVec xs ≡ xs
evalPRFs-projVec xs
  rewrite evalPRFs-projFinVec finVec xs
        | lookup-finVec xs = refl

evalPRFs-drop1ProjVec :
  {n : ℕ} →
  (x : ℕ) →
  (xs : Vec ℕ n) →
  evalPRFs drop1ProjVec (x ∷ xs) ≡ xs
evalPRFs-drop1ProjVec x xs
  rewrite evalPRFs-projFinVec drop1FinVec (x ∷ xs)
        | mapVec-mapFinVec
            (λ i → lookup i (x ∷ xs))
            fsuc
            finVec
        | lookup-finVec xs = refl

evalPRFs-drop2ProjVec :
  {n : ℕ} →
  (x y : ℕ) →
  (xs : Vec ℕ n) →
  evalPRFs drop2ProjVec (x ∷ y ∷ xs) ≡ xs
evalPRFs-drop2ProjVec x y xs
  rewrite evalPRFs-projFinVec drop2FinVec (x ∷ y ∷ xs)
        | mapVec-mapFinVec
            (λ i → lookup i (x ∷ y ∷ xs))
            (λ i → fsuc (fsuc i))
            finVec
        | lookup-finVec xs = refl

evalPRFs-drop3ProjVec :
  {n : ℕ} →
  (w x y : ℕ) →
  (xs : Vec ℕ n) →
  evalPRFs drop3ProjVec (w ∷ x ∷ y ∷ xs) ≡ xs
evalPRFs-drop3ProjVec w x y xs
  rewrite evalPRFs-projFinVec drop3FinVec (w ∷ x ∷ y ∷ xs)
        | mapVec-mapFinVec
            (λ i → lookup i (w ∷ x ∷ y ∷ xs))
            (λ i → fsuc (fsuc (fsuc i)))
            finVec
        | lookup-finVec xs = refl
