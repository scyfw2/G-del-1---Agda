{-# OPTIONS --safe #-}

module Godel.CanonicalCodeParserSemantics where

open import Agda.Builtin.List using (List) renaming ([] to []ˡ; _∷_ to _∷ˡ_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Bool using (true; false)
open import Godel.Core
open import Godel.CanonicalCoding
  using
    ( Code
    ; encodeCode
    ; encodeCodeWithRest
    ; encodeCodeListWithRest
    ; decodeCodeWithRest
    ; decodeCodeWithRest-roundTrip
    ; decodeCodeWithRest-sound
    ; decodeCodeListWithRest
    ; decodeCodeListWithRest-roundTrip
    ; decodeCodeListWithRest-sound
    ; codeListSize
    ; codeSize
    ; codeSize+base≤encodeCodeWithRest
    ; codeListSize+base≤encodeCodeListWithRest
    ; ≤-refl
    ; ≤-zero
    ; +-zeroʳ
    ; inspect
    ; [_]
    )
open import Godel.DecidableCoding using (_==ℕ_; ==ℕ-refl; ==ℕ-sound)
open import Godel.CanonicalCodeParserTargets
  using
    ( CodeWithRestNat
    ; CodeSkipNat
    ; CodeListHeadNat
    ; CodeListTailNat
    ; CodeListLengthNat
    ; CodeListNthNat
    ; codeListLength
    ; codeListNthDefault
    ; codeListNthDefault-complete
    )

-- Executable meta-level semantics for the future numeric canonical-code-list
-- PR parser.  The actual PRF destructors will be proved against these
-- functions, while this module connects the functions back to the existing
-- existential parser targets.

parseCodeWithRestFuel : ℕ → ℕ → ℕ → Maybe ℕ
parseCodeWithRestFuel fuel input expected-rest
  with decodeCodeWithRest (suc fuel) input
... | just (code ,× rest) with rest ==ℕ expected-rest
... | true = just (encodeCode code)
... | false = nothing
parseCodeWithRestFuel fuel input expected-rest | nothing = nothing

parseCodeWithRest : ℕ → ℕ → Maybe ℕ
parseCodeWithRest input expected-rest =
  parseCodeWithRestFuel input input expected-rest

parseCodeWithRest-canonical :
  (code : Code) → (rest : ℕ) →
  parseCodeWithRest (encodeCodeWithRest code rest) rest ≡
  just (encodeCode code)
parseCodeWithRest-canonical code rest
  with codeSize+base≤encodeCodeWithRest
         code
         zero
         rest
         (≤-zero rest)
... | extra ,Σ eq =
  helper extra eq
  where
    helper :
      (extra : ℕ) →
      encodeCodeWithRest code rest ≡ codeSize code + zero + extra →
      parseCodeWithRest (encodeCodeWithRest code rest) rest ≡
      just (encodeCode code)
    helper extra eq
      rewrite +-zeroʳ (codeSize code) =
      subst
        (λ fuel →
          parseCodeWithRestFuel
            fuel
            (encodeCodeWithRest code rest)
            rest
          ≡ just (encodeCode code))
        (sym eq)
        step
      where
        step :
          parseCodeWithRestFuel
            (codeSize code + extra)
            (encodeCodeWithRest code rest)
            rest
          ≡
          just (encodeCode code)
        step
          rewrite decodeCodeWithRest-roundTrip code rest extra
                | ==ℕ-refl rest = refl

parseCodeWithRest-sound :
  (input code rest : ℕ) →
  parseCodeWithRest input rest ≡ just code →
  CodeWithRestNat input code rest
parseCodeWithRest-sound input code rest eq
  with decodeCodeWithRest (suc input) input
     | inspect (decodeCodeWithRest (suc input)) input
... | just (parsed ,× final-rest) | [ parse-eq ]
  with final-rest ==ℕ rest | inspect (_==ℕ_ final-rest) rest
... | true | [ rest-eq ] with eq
... | refl =
  parsed ,Σ
    (trans
      (decodeCodeWithRest-sound
        (suc input)
        input
        parsed
        final-rest
        parse-eq)
      (cong (encodeCodeWithRest parsed)
        (==ℕ-sound final-rest rest rest-eq))
     ,× refl)
parseCodeWithRest-sound input code rest ()
  | just (parsed ,× final-rest) | [ parse-eq ]
  | false | [ rest-eq ]
parseCodeWithRest-sound input code rest ()
  | nothing | [ parse-eq ]

parseCodeSkipFuel : ℕ → ℕ → Maybe ℕ
parseCodeSkipFuel fuel input
  with decodeCodeWithRest (suc fuel) input
... | just (code ,× rest) = just rest
... | nothing = nothing

parseCodeSkip : ℕ → Maybe ℕ
parseCodeSkip input =
  parseCodeSkipFuel input input

parseCodeSkip-canonical :
  (code : Code) → (rest : ℕ) →
  parseCodeSkip (encodeCodeWithRest code rest) ≡ just rest
parseCodeSkip-canonical code rest
  with codeSize+base≤encodeCodeWithRest
         code
         zero
         rest
         (≤-zero rest)
... | extra ,Σ eq =
  helper extra eq
  where
    helper :
      (extra : ℕ) →
      encodeCodeWithRest code rest ≡ codeSize code + zero + extra →
      parseCodeSkip (encodeCodeWithRest code rest) ≡ just rest
    helper extra eq
      rewrite +-zeroʳ (codeSize code) =
      subst
        (λ fuel →
          parseCodeSkipFuel
            fuel
            (encodeCodeWithRest code rest)
          ≡ just rest)
        (sym eq)
        step
      where
        step :
          parseCodeSkipFuel
            (codeSize code + extra)
            (encodeCodeWithRest code rest)
          ≡ just rest
        step
          rewrite decodeCodeWithRest-roundTrip code rest extra = refl

parseCodeSkip-sound :
  (input rest : ℕ) →
  parseCodeSkip input ≡ just rest →
  CodeSkipNat input rest
parseCodeSkip-sound input rest eq
  with decodeCodeWithRest (suc input) input
     | inspect (decodeCodeWithRest (suc input)) input
... | just (code ,× final-rest) | [ parse-eq ] with eq
... | refl =
  code ,Σ
    decodeCodeWithRest-sound
      (suc input)
      input
      code
      final-rest
      parse-eq
parseCodeSkip-sound input rest ()
  | nothing | [ parse-eq ]

parseCodeList : ℕ → Maybe (List Code × ℕ)
parseCodeList input =
  decodeCodeListWithRest (suc input) input

parseCodeList-canonical :
  (codes : List Code) →
  parseCodeList (encodeCodeListWithRest codes zero) ≡
  just (codes ,× zero)
parseCodeList-canonical codes
  with codeListSize+base≤encodeCodeListWithRest
         codes
         zero
         zero
         (≤-refl zero)
... | extra ,Σ eq =
  helper extra eq
  where
    helper :
      (extra : ℕ) →
      encodeCodeListWithRest codes zero ≡
      codeListSize codes + zero + extra →
      parseCodeList (encodeCodeListWithRest codes zero) ≡
      just (codes ,× zero)
    helper extra eq
      rewrite +-zeroʳ (codeListSize codes) =
      subst
        (λ fuel →
          decodeCodeListWithRest
            (suc fuel)
            (encodeCodeListWithRest codes zero)
          ≡ just (codes ,× zero))
        (sym eq)
        (decodeCodeListWithRest-roundTrip codes zero extra)

parseCodeListHead : ℕ → Maybe ℕ
parseCodeListHead input with parseCodeList input
... | just ((head ∷ˡ tail) ,× zero) = just (encodeCode head)
... | just (codes ,× suc rest) = nothing
... | just ([]ˡ ,× zero) = nothing
... | nothing = nothing

parseCodeListTail : ℕ → Maybe ℕ
parseCodeListTail input with parseCodeList input
... | just ((head ∷ˡ tail) ,× zero) =
  just (encodeCodeListWithRest tail zero)
... | just (codes ,× suc rest) = nothing
... | just ([]ˡ ,× zero) = nothing
... | nothing = nothing

parseCodeListLength : ℕ → Maybe ℕ
parseCodeListLength input with parseCodeList input
... | just (codes ,× zero) = just (codeListLength codes)
... | just (codes ,× suc rest) = nothing
... | nothing = nothing

parseCodeListNth : ℕ → ℕ → Maybe ℕ
parseCodeListNth input index with parseCodeList input
... | just (codes ,× zero) =
  just (codeListNthDefault codes index zero)
... | just (codes ,× suc rest) = nothing
... | nothing = nothing

parseCodeListHead-canonical :
  (head : Code) → (tail : List Code) →
  parseCodeListHead (encodeCodeListWithRest (head ∷ˡ tail) zero) ≡
  just (encodeCode head)
parseCodeListHead-canonical head tail
  rewrite parseCodeList-canonical (head ∷ˡ tail) = refl

parseCodeListTail-canonical :
  (head : Code) → (tail : List Code) →
  parseCodeListTail (encodeCodeListWithRest (head ∷ˡ tail) zero) ≡
  just (encodeCodeListWithRest tail zero)
parseCodeListTail-canonical head tail
  rewrite parseCodeList-canonical (head ∷ˡ tail) = refl

parseCodeListLength-canonical :
  (codes : List Code) →
  parseCodeListLength (encodeCodeListWithRest codes zero) ≡
  just (codeListLength codes)
parseCodeListLength-canonical codes
  rewrite parseCodeList-canonical codes = refl

parseCodeListNth-canonical :
  (codes : List Code) → (index : ℕ) →
  parseCodeListNth (encodeCodeListWithRest codes zero) index ≡
  just (codeListNthDefault codes index zero)
parseCodeListNth-canonical codes index
  rewrite parseCodeList-canonical codes = refl

parseCodeListHead-sound :
  (list-code head-code : ℕ) →
  parseCodeListHead list-code ≡ just head-code →
  CodeListHeadNat list-code head-code
parseCodeListHead-sound list-code head-code eq
  with parseCodeList list-code | inspect parseCodeList list-code
... | just ((head ∷ˡ tail) ,× zero) | [ parse-eq ] with eq
... | refl =
  head ,Σ
    (tail ,Σ
      (decodeCodeListWithRest-sound
        (suc list-code)
        list-code
        (head ∷ˡ tail)
        zero
        parse-eq
       ,× refl))
parseCodeListHead-sound list-code head-code ()
  | just ((head ∷ˡ tail) ,× suc rest) | [ parse-eq ]
parseCodeListHead-sound list-code head-code ()
  | just ([]ˡ ,× zero) | [ parse-eq ]
parseCodeListHead-sound list-code head-code ()
  | nothing | [ parse-eq ]

parseCodeListTail-sound :
  (list-code tail-code : ℕ) →
  parseCodeListTail list-code ≡ just tail-code →
  CodeListTailNat list-code tail-code
parseCodeListTail-sound list-code tail-code eq
  with parseCodeList list-code | inspect parseCodeList list-code
... | just ((head ∷ˡ tail) ,× zero) | [ parse-eq ] with eq
... | refl =
  head ,Σ
    (tail ,Σ
      (decodeCodeListWithRest-sound
        (suc list-code)
        list-code
        (head ∷ˡ tail)
        zero
        parse-eq
       ,× refl))
parseCodeListTail-sound list-code tail-code ()
  | just ((head ∷ˡ tail) ,× suc rest) | [ parse-eq ]
parseCodeListTail-sound list-code tail-code ()
  | just ([]ˡ ,× zero) | [ parse-eq ]
parseCodeListTail-sound list-code tail-code ()
  | nothing | [ parse-eq ]

parseCodeListLength-sound :
  (list-code len : ℕ) →
  parseCodeListLength list-code ≡ just len →
  CodeListLengthNat list-code len
parseCodeListLength-sound list-code len eq
  with parseCodeList list-code | inspect parseCodeList list-code
... | just (codes ,× zero) | [ parse-eq ] with eq
... | refl =
  codes ,Σ
    (decodeCodeListWithRest-sound
      (suc list-code)
      list-code
      codes
      zero
      parse-eq
     ,× refl)
parseCodeListLength-sound list-code len ()
  | just (codes ,× suc rest) | [ parse-eq ]
parseCodeListLength-sound list-code len ()
  | nothing | [ parse-eq ]

parseCodeListNth-sound :
  (list-code index nth-code : ℕ) →
  parseCodeListNth list-code index ≡ just nth-code →
  CodeListNthNat list-code index nth-code
parseCodeListNth-sound list-code index nth-code eq
  with parseCodeList list-code | inspect parseCodeList list-code
... | just (codes ,× zero) | [ parse-eq ] with eq
... | refl =
  codes ,Σ
    (decodeCodeListWithRest-sound
      (suc list-code)
      list-code
      codes
      zero
      parse-eq
     ,× codeListNthDefault-complete codes index)
parseCodeListNth-sound list-code index nth-code ()
  | just (codes ,× suc rest) | [ parse-eq ]
parseCodeListNth-sound list-code index nth-code ()
  | nothing | [ parse-eq ]
