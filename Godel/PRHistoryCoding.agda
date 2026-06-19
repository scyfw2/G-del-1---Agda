{-# OPTIONS --safe #-}

module Godel.PRHistoryCoding where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Godel.Core
open import Godel.PrimitiveRecursive
open import Godel.CanonicalCoding
  using
    ( Digit; d0; d1
    ; appendDigit; undigit; digitRest
    ; undigit-appendDigit
    ; encodeNatWithRest; decodeNatWithRest
    ; decodeNatWithRest-roundTrip
    ; +-assoc; +-zeroʳ; +-swap-mid
    )

appendHistory : List ℕ → ℕ → List ℕ
appendHistory [] y = y ∷ []
appendHistory (x ∷ xs) y = x ∷ appendHistory xs y

lastHistory :
  {n : ℕ} →
  PRF n →
  PRF (suc (suc n)) →
  ℕ →
  Vec ℕ n →
  ℕ
lastHistory g h zero xs = evalPRF g xs
lastHistory g h (suc k) xs =
  evalPRF h (k ∷ lastHistory g h k xs ∷ xs)

evalHistory :
  {n : ℕ} →
  PRF n →
  PRF (suc (suc n)) →
  ℕ →
  Vec ℕ n →
  List ℕ
evalHistory g h zero xs = evalPRF g xs ∷ []
evalHistory g h (suc k) xs =
  appendHistory
    (evalHistory g h k xs)
    (evalPRF h (k ∷ lastHistory g h k xs ∷ xs))

historyLength : List ℕ → ℕ
historyLength [] = zero
historyLength (x ∷ xs) = suc (historyLength xs)

historyNthDefault : List ℕ → ℕ → ℕ → ℕ
historyNthDefault [] k default = default
historyNthDefault (x ∷ xs) zero default = x
historyNthDefault (x ∷ xs) (suc k) default =
  historyNthDefault xs k default

encodeNatListWithRest : List ℕ → ℕ → ℕ
encodeNatListWithRest [] rest = appendDigit d0 rest
encodeNatListWithRest (x ∷ xs) rest =
  appendDigit d1 (encodeNatWithRest x (encodeNatListWithRest xs rest))

historyCode : List ℕ → ℕ
historyCode xs = encodeNatListWithRest xs zero

natListSize : List ℕ → ℕ
natListSize [] = zero
natListSize (x ∷ xs) = suc (x + natListSize xs)

decodeNatListWithFuel : ℕ → ℕ → Maybe (List ℕ × ℕ)
decodeNatListWithFuel zero input = nothing
decodeNatListWithFuel (suc fuel) input with undigit input
... | digitRest d0 rest = just ([] ,× rest)
... | digitRest d1 rest with decodeNatWithRest fuel rest
... | just (x ,× rest') with decodeNatListWithFuel fuel rest'
... | just (xs ,× final) = just ((x ∷ xs) ,× final)
... | nothing = nothing
decodeNatListWithFuel (suc fuel) input | digitRest d1 rest | nothing = nothing
decodeNatListWithFuel (suc fuel) input | digitRest _ rest = nothing

decodeNatListWithFuel-roundTrip :
  (xs : List ℕ) → (rest extra : ℕ) →
  decodeNatListWithFuel
    (suc (natListSize xs + extra))
    (encodeNatListWithRest xs rest)
  ≡ just (xs ,× rest)
decodeNatListWithFuel-roundTrip [] rest extra
  rewrite undigit-appendDigit d0 rest = refl
decodeNatListWithFuel-roundTrip (x ∷ xs) rest extra
  rewrite undigit-appendDigit d1
            (encodeNatWithRest x (encodeNatListWithRest xs rest))
        | +-assoc x (natListSize xs) extra
        | decodeNatWithRest-roundTrip
            x
            (encodeNatListWithRest xs rest)
            (natListSize xs + extra)
        | +-swap-mid x (natListSize xs) extra
        | decodeNatListWithFuel-roundTrip xs rest (x + extra) = refl

historyCode-roundTrip :
  (history : List ℕ) →
  decodeNatListWithFuel
    (suc (natListSize history))
    (historyCode history)
  ≡ just (history ,× zero)
historyCode-roundTrip history =
  subst
    (λ fuel →
      decodeNatListWithFuel (suc fuel) (historyCode history) ≡
      just (history ,× zero))
    (+-zeroʳ (natListSize history))
    (decodeNatListWithFuel-roundTrip history zero zero)

historyLength-append :
  (xs : List ℕ) → (y : ℕ) →
  historyLength (appendHistory xs y) ≡ suc (historyLength xs)
historyLength-append [] y = refl
historyLength-append (x ∷ xs) y =
  cong suc (historyLength-append xs y)

historyNthDefault-append-at-length :
  (xs : List ℕ) → (y default : ℕ) →
  historyNthDefault (appendHistory xs y) (historyLength xs) default ≡ y
historyNthDefault-append-at-length [] y default = refl
historyNthDefault-append-at-length (x ∷ xs) y default =
  historyNthDefault-append-at-length xs y default

lastHistory-evalPrec :
  {n : ℕ} →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (x : ℕ) →
  (xs : Vec ℕ n) →
  lastHistory g h x xs ≡ evalPrec g h x xs
lastHistory-evalPrec g h zero xs = refl
lastHistory-evalPrec g h (suc x) xs
  rewrite lastHistory-evalPrec g h x xs = refl

historyLength-evalHistory :
  {n : ℕ} →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (x : ℕ) →
  (xs : Vec ℕ n) →
  historyLength (evalHistory g h x xs) ≡ suc x
historyLength-evalHistory g h zero xs = refl
historyLength-evalHistory g h (suc x) xs
  rewrite historyLength-append (evalHistory g h x xs)
          (evalPRF h (x ∷ lastHistory g h x xs ∷ xs))
        | historyLength-evalHistory g h x xs = refl

historyNth-evalHistory-last :
  {n : ℕ} →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (x : ℕ) →
  (xs : Vec ℕ n) →
  historyNthDefault (evalHistory g h x xs) x zero ≡
  lastHistory g h x xs
historyNth-evalHistory-last g h zero xs = refl
historyNth-evalHistory-last g h (suc x) xs
  rewrite sym (historyLength-evalHistory g h x xs) =
  historyNthDefault-append-at-length
    (evalHistory g h x xs)
    (evalPRF h (x ∷ lastHistory g h x xs ∷ xs))
    zero
