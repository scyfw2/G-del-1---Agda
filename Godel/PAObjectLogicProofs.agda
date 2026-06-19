{-# OPTIONS --safe #-}

module Godel.PAObjectLogicProofs where

open import Godel.PA
open import Godel.ProofSystem
open import Godel.PAObjectLogic
open import Godel.PAClosedArithmetic
open import Godel.PAClosedArithmeticProofs

paObjectLogic : PAObjectLogic
paObjectLogic = record
  { eq-refl-PA = eq-refl-rule
  ; eq-sym-PA = eq-sym-rule
  ; eq-trans-PA = eq-trans-rule
  ; suc-cong-PA = suc-cong-rule
  ; add-cong-PA = add-cong-rule
  ; mul-cong-PA = mul-cong-rule
  }

paProofInfrastructure : PAProofInfrastructure
paProofInfrastructure = paProofInfrastructure-fromObjectLogic paObjectLogic
