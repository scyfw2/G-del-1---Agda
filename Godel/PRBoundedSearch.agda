{-# OPTIONS --safe #-}

module Godel.PRBoundedSearch where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.PrimitiveRecursive

constF : {n : ℕ} → ℕ → PRF n
constF zero = zeroF
constF (suc n) = compF sucF (constF n ∷ [])

twoF : {n : ℕ} → PRF n
twoF = constF (suc (suc zero))

threeF : {n : ℕ} → PRF n
threeF = constF (suc (suc (suc zero)))
