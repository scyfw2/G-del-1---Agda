{-# OPTIONS --safe #-}

module Godel.SyntaxCodingPRConcrete where

open import Godel.SyntaxCodingPR
open import Godel.SyntaxCodingPRSoundness
open import Godel.SyntaxCodingPRInstances
import Godel.PACheckedGraphPRProofs as PRProofs

-- The concrete instance is intentionally deferred.  It must be rebuilt from
-- real numeric PR decoders now that evalPRF has no syntax-checker oracle.
record SyntaxCodingPRConcreteTarget : Set₁ where
  field
    syntax-coding-pr : SyntaxCodingPR
    soundness-target : SyntaxCodingPRSoundnessTarget
    instance-data    : SyntaxCodingPRInstanceData
    checked-inputs   : PRProofs.PACheckedGraphPRInputs
