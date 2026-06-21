{-# OPTIONS --safe #-}

module Godel.CanonicalCodeNodeSemantics where

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.CanonicalCoding
  using
    ( Code
    ; atom
    ; node
    ; encodeCode
    ; encodeCodeListWithRest
    ; decodeCode
    ; decodeCode-sound
    ; decodeCode-roundTrip-extra
    ; codeSize
    ; codeSize≤encodeCode
    ; inspect
    ; [_]
    )
open import Godel.CanonicalCodeNodeTargets
  using
    ( NodeCodeNat
    )

parseNodeCodeFuel : ℕ → ℕ → Maybe (ℕ × ℕ)
parseNodeCodeFuel fuel input with decodeCode (suc fuel) input
... | just (node tag children) =
  just (tag ,× encodeCodeListWithRest children zero)
... | just (atom n) = nothing
... | nothing = nothing

parseNodeCode : ℕ → Maybe (ℕ × ℕ)
parseNodeCode input =
  parseNodeCodeFuel input input

parseNodeCode-canonical :
  (tag : ℕ) → (children : List Code) →
  parseNodeCode (encodeCode (node tag children)) ≡
  just (tag ,× encodeCodeListWithRest children zero)
parseNodeCode-canonical tag children
  with codeSize≤encodeCode (node tag children)
... | extra ,Σ eq =
  subst
    (λ fuel →
      parseNodeCodeFuel fuel (encodeCode (node tag children)) ≡
      just (tag ,× encodeCodeListWithRest children zero))
    (sym eq)
    step
  where
    step :
      parseNodeCodeFuel
        (codeSize (node tag children) + extra)
        (encodeCode (node tag children))
      ≡ just (tag ,× encodeCodeListWithRest children zero)
    step
      rewrite decodeCode-roundTrip-extra (node tag children) extra = refl

parseNodeCode-sound :
  (input tag children-code : ℕ) →
  parseNodeCode input ≡ just (tag ,× children-code) →
  NodeCodeNat input tag children-code
parseNodeCode-sound input tag children-code eq
  with decodeCode (suc input) input | inspect (decodeCode (suc input)) input
... | just (node parsed-tag children) | [ parse-eq ] with eq
... | refl =
  children ,Σ
    (decodeCode-sound
      (suc input)
      input
      (node parsed-tag children)
      parse-eq
     ,× refl)
parseNodeCode-sound input tag children-code ()
  | just (atom n) | [ parse-eq ]
parseNodeCode-sound input tag children-code ()
  | nothing | [ parse-eq ]
