{-# OPTIONS --safe #-}

module Godel.PrimitiveRecursive where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core

infixr 5 _∷_

data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (suc n)
  fsuc  : {n : ℕ} → Fin n → Fin (suc n)

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

lookup : {A : Set} → {n : ℕ} → Fin n → Vec A n → A
lookup fzero (x ∷ xs) = x
lookup (fsuc i) (x ∷ xs) = lookup i xs

mapVec : {A B : Set} → {n : ℕ} → (A → B) → Vec A n → Vec B n
mapVec f [] = []
mapVec f (x ∷ xs) = f x ∷ mapVec f xs

data PRF : ℕ → Set where
  zeroF : {n : ℕ} → PRF n
  sucF  : PRF (suc zero)
  projF : {n : ℕ} → Fin n → PRF n
  compF : {n m : ℕ} → PRF m → Vec (PRF n) m → PRF n
  precF : {n : ℕ} → PRF n → PRF (suc (suc n)) → PRF (suc n)

evalPRF : {n : ℕ} → PRF n → Vec ℕ n → ℕ
evalPRFs : {n m : ℕ} → Vec (PRF n) m → Vec ℕ n → Vec ℕ m
evalPrec : {n : ℕ} → PRF n → PRF (suc (suc n)) → ℕ → Vec ℕ n → ℕ

evalPRF zeroF xs = zero
evalPRF sucF (x ∷ []) = suc x
evalPRF (projF i) xs = lookup i xs
evalPRF (precF g h) (x ∷ xs) = evalPrec g h x xs
evalPRF (compF f gs) xs = evalPRF f (evalPRFs gs xs)

evalPRFs [] xs = []
evalPRFs (f ∷ fs) xs = evalPRF f xs ∷ evalPRFs fs xs

evalPrec g h zero xs = evalPRF g xs
evalPrec g h (suc n) xs =
  evalPRF h (n ∷ evalPrec g h n xs ∷ xs)

oneF : {n : ℕ} → PRF n
oneF = compF sucF (zeroF ∷ [])

record PRRel (n : ℕ) : Set where
  constructor rel
  field
    characteristic : PRF n

PRRel-holds : {n : ℕ} → PRRel n → Vec ℕ n → Set
PRRel-holds R xs = evalPRF (PRRel.characteristic R) xs ≡ suc zero
