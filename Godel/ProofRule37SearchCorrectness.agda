{-# OPTIONS --safe #-}

module Godel.ProofRule37SearchCorrectness where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.CanonicalCoding using (_≤_; ≤-refl; ≤-step; +-zeroʳ; +-sucʳ)
open import Godel.ProofRule37Search using (orNat; searchUpTo)

-- Generic meta-level facts about the bounded disjunction used by the rule-37
-- searcher.  The lemmas intentionally do not mention rule37WitnessF: the
-- concrete witness checker is large, and instantiating these facts directly
-- against it makes Agda normalize too much.  A later rule-37 proof module can
-- connect that checker through a small, named "witness hit" interface.

orNat-left-one : (right : ℕ) → orNat (suc zero) right ≡ suc zero
orNat-left-one right = refl

orNat-right-one : (left : ℕ) → orNat left (suc zero) ≡ suc zero
orNat-right-one zero = refl
orNat-right-one (suc left) = refl

NonzeroNat : ℕ → Set
NonzeroNat n = Σ ℕ (λ k → n ≡ suc k)

one-is-nonzero : {n : ℕ} → n ≡ suc zero → NonzeroNat n
one-is-nonzero eq = zero ,Σ eq

orNat-nonzero-sound :
  (left right : ℕ) →
  NonzeroNat (orNat left right) →
  NonzeroNat left ⊎ NonzeroNat right
orNat-nonzero-sound zero zero (k ,Σ ())
orNat-nonzero-sound (suc left) right nz =
  inj₁ (left ,Σ refl)
orNat-nonzero-sound zero (suc right) nz =
  inj₂ (right ,Σ refl)

searchUpTo-hit-exact :
  (P : ℕ → ℕ) →
  (n : ℕ) →
  P n ≡ suc zero →
  searchUpTo P n ≡ suc zero
searchUpTo-hit-exact P zero hit = hit
searchUpTo-hit-exact P (suc n) hit =
  subst
    (λ value →
      orNat (searchUpTo P n) value ≡ suc zero)
    (sym hit)
    (orNat-right-one (searchUpTo P n))

searchUpTo-hit-extra :
  (P : ℕ → ℕ) →
  (n extra : ℕ) →
  P n ≡ suc zero →
  searchUpTo P (n + extra) ≡ suc zero
searchUpTo-hit-extra P n zero hit
  rewrite +-zeroʳ n =
  searchUpTo-hit-exact P n hit
searchUpTo-hit-extra P n (suc extra) hit
  rewrite +-sucʳ n extra
        | searchUpTo-hit-extra P n extra hit
        | orNat-left-one (P (suc (n + extra))) =
  refl

searchUpTo-hit-bound :
  {P : ℕ → ℕ} →
  {n bound : ℕ} →
  n ≤ bound →
  P n ≡ suc zero →
  searchUpTo P bound ≡ suc zero
searchUpTo-hit-bound {P} {n} (extra ,Σ eq) hit =
  subst
    (λ b → searchUpTo P b ≡ suc zero)
    (sym eq)
    (searchUpTo-hit-extra P n extra hit)

SearchBoundedNonzero :
  (ℕ → ℕ) → ℕ → Set
SearchBoundedNonzero P bound =
  Σ ℕ
    (λ n →
      (n ≤ bound) ×
      NonzeroNat (P n))

searchUpTo-nonzero-sound :
  {P : ℕ → ℕ} →
  (bound : ℕ) →
  NonzeroNat (searchUpTo P bound) →
  SearchBoundedNonzero P bound
searchUpTo-nonzero-sound {P} zero nz =
  zero ,Σ (≤-refl zero ,× nz)
searchUpTo-nonzero-sound {P} (suc bound) nz
  with orNat-nonzero-sound
        (searchUpTo P bound)
        (P (suc bound))
        nz
... | inj₁ left-nz =
  let found = searchUpTo-nonzero-sound {P} bound left-nz in
  fstΣ found ,Σ
    (≤-step (fst (sndΣ found)) ,×
     snd (sndΣ found))
... | inj₂ right-nz =
  suc bound ,Σ (≤-refl (suc bound) ,× right-nz)

searchUpTo-sound-one :
  {P : ℕ → ℕ} →
  (bound : ℕ) →
  searchUpTo P bound ≡ suc zero →
  SearchBoundedNonzero P bound
searchUpTo-sound-one bound eq =
  searchUpTo-nonzero-sound bound (one-is-nonzero eq)

searchUpTo-cong :
  (P Q : ℕ → ℕ) →
  (bound : ℕ) →
  ((k : ℕ) → P k ≡ Q k) →
  searchUpTo P bound ≡ searchUpTo Q bound
searchUpTo-cong P Q zero pointwise =
  pointwise zero
searchUpTo-cong P Q (suc bound) pointwise
  rewrite searchUpTo-cong P Q bound pointwise
        | pointwise (suc bound) =
  refl

search2UpTo : (ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ
search2UpTo P outer-bound inner-bound =
  searchUpTo
    (λ outer → searchUpTo (P outer) inner-bound)
    outer-bound

Search2BoundedHit :
  (ℕ → ℕ → ℕ) → ℕ → ℕ → Set
Search2BoundedHit P outer-bound inner-bound =
  Σ ℕ
    (λ outer →
      Σ ℕ
        (λ inner →
          ((outer ≤ outer-bound) × (inner ≤ inner-bound)) ×
          (P outer inner ≡ suc zero)))

search2UpTo-hit-bound :
  {P : ℕ → ℕ → ℕ} →
  {outer-bound inner-bound : ℕ} →
  Search2BoundedHit P outer-bound inner-bound →
  search2UpTo P outer-bound inner-bound ≡ suc zero
search2UpTo-hit-bound
  {P}
  {outer-bound}
  {inner-bound}
  (outer ,Σ (inner ,Σ ((outer≤bound ,× inner≤bound) ,× hit))) =
  searchUpTo-hit-bound
    {P = λ current-outer → searchUpTo (P current-outer) inner-bound}
    outer≤bound
    (searchUpTo-hit-bound
      {P = P outer}
      inner≤bound
      hit)

Search2BoundedNonzero :
  (ℕ → ℕ → ℕ) → ℕ → ℕ → Set
Search2BoundedNonzero P outer-bound inner-bound =
  Σ ℕ
    (λ outer →
      Σ ℕ
        (λ inner →
          ((outer ≤ outer-bound) × (inner ≤ inner-bound)) ×
          NonzeroNat (P outer inner)))

search2UpTo-nonzero-sound :
  {P : ℕ → ℕ → ℕ} →
  (outer-bound inner-bound : ℕ) →
  NonzeroNat (search2UpTo P outer-bound inner-bound) →
  Search2BoundedNonzero P outer-bound inner-bound
search2UpTo-nonzero-sound {P} outer-bound inner-bound nz =
  let outer-found =
        searchUpTo-nonzero-sound
          {P = λ outer → searchUpTo (P outer) inner-bound}
          outer-bound
          nz
  in
  let inner-found =
        searchUpTo-nonzero-sound
          {P = P (fstΣ outer-found)}
          inner-bound
          (snd (sndΣ outer-found))
  in
  fstΣ outer-found ,Σ
    (fstΣ inner-found ,Σ
      ((fst (sndΣ outer-found) ,×
        fst (sndΣ inner-found))
       ,×
       snd (sndΣ inner-found)))

search2UpTo-sound-one :
  {P : ℕ → ℕ → ℕ} →
  (outer-bound inner-bound : ℕ) →
  search2UpTo P outer-bound inner-bound ≡ suc zero →
  Search2BoundedNonzero P outer-bound inner-bound
search2UpTo-sound-one outer-bound inner-bound eq =
  search2UpTo-nonzero-sound
    outer-bound
    inner-bound
    (one-is-nonzero eq)

search2UpTo-cong :
  (P Q : ℕ → ℕ → ℕ) →
  (outer-bound inner-bound : ℕ) →
  ((outer inner : ℕ) → P outer inner ≡ Q outer inner) →
  search2UpTo P outer-bound inner-bound ≡
  search2UpTo Q outer-bound inner-bound
search2UpTo-cong P Q outer-bound inner-bound pointwise =
  searchUpTo-cong
    (λ outer → searchUpTo (P outer) inner-bound)
    (λ outer → searchUpTo (Q outer) inner-bound)
    outer-bound
    (λ outer →
      searchUpTo-cong
        (P outer)
        (Q outer)
        inner-bound
        (pointwise outer))
