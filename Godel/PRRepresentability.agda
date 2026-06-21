{-# OPTIONS --safe #-}

module Godel.PRRepresentability where

-- Legacy/bootstrap representability layer.
--
-- This module still defines the public records used throughout the project and
-- keeps the older evaluator-backed theorem path typechecking for compatibility.
-- The final structured theorem entry point is Godel.PRRepresentabilityFinal.

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.PA
open import Godel.ProofSystem
open import Godel.PAClosedArithmeticProofs
open import Godel.PAProofCombinators
open import Godel.PrimitiveRecursive
import Godel.PRHistoryCoding as History

numeralVec : {n : ℕ} → Vec ℕ n → Vec Term n
numeralVec = mapVec numeral

lookup-mapVec :
  {A B : Set} → {n : ℕ} →
  (f : A → B) → (i : Fin n) → (xs : Vec A n) →
  lookup i (mapVec f xs) ≡ f (lookup i xs)
lookup-mapVec f fzero (x ∷ xs) = refl
lookup-mapVec f (fsuc i) (x ∷ xs) = lookup-mapVec f i xs

record PARepresentsFunction {n : ℕ} (f : PRF n) : Set₁ where
  field
    graphFormula :
      Vec Term n → Term → Formula

    represents-value :
      (xs : Vec ℕ n) →
      PA-provable (graphFormula (numeralVec xs) (numeral (evalPRF f xs)))

    represents-unique :
      (xs : Vec ℕ n) → (y z : Term) →
      PA-provable
        (graphFormula (numeralVec xs) y ⇒
         (graphFormula (numeralVec xs) z ⇒ y ≈ z))

    represents-exists :
      (xs : Vec ℕ n) →
      Σ Term (λ y → PA-provable (graphFormula (numeralVec xs) y))

record PARepresentsRelation {n : ℕ} (R : PRRel n) : Set₁ where
  field
    relationFormula :
      Vec Term n → Formula

    represents-true :
      (xs : Vec ℕ n) →
      PRRel-holds R xs →
      PA-provable (relationFormula (numeralVec xs))

    represents-false :
      (xs : Vec ℕ n) →
      ¬ PRRel-holds R xs →
      PA-provable (¬ᶠ (relationFormula (numeralVec xs)))

data AllPRF {n : ℕ} (P : PRF n → Set₁) :
            {m : ℕ} → Vec (PRF n) m → Set₁ where
  all[] : AllPRF P []
  all∷  : {m : ℕ} → {f : PRF n} → {fs : Vec (PRF n) m} →
          P f → AllPRF P fs → AllPRF P (f ∷ fs)

termValue : Term → ℕ
termValue (var x) = zero
termValue zeroᵗ = zero
termValue (sucᵗ t) = suc (termValue t)
termValue (s +ᵗ t) = termValue s + termValue t
termValue (s *ᵗ t) = termValue s * termValue t

termValues : {n : ℕ} → Vec Term n → Vec ℕ n
termValues = mapVec termValue

termValue-numeral : (n : ℕ) → termValue (numeral n) ≡ n
termValue-numeral zero = refl
termValue-numeral (suc n) = cong suc (termValue-numeral n)

termValues-numeralVec :
  {n : ℕ} → (xs : Vec ℕ n) →
  termValues (numeralVec xs) ≡ xs
termValues-numeralVec [] = refl
termValues-numeralVec (x ∷ xs)
  rewrite termValue-numeral x | termValues-numeralVec xs = refl

evaluatedGraphFormula : {n : ℕ} → PRF n → Vec Term n → Term → Formula
evaluatedGraphFormula f xs y = y ≈ numeral (evalPRF f (termValues xs))

evaluatedGraphFormula-value :
  {n : ℕ} → (f : PRF n) → (xs : Vec ℕ n) →
  PA-provable
    (evaluatedGraphFormula f (numeralVec xs) (numeral (evalPRF f xs)))
evaluatedGraphFormula-value f xs =
  pa-provable-cong
    (cong (λ ys → numeral (evalPRF f xs) ≈ numeral (evalPRF f ys))
          (sym (termValues-numeralVec xs)))
    (eq-refl-rule (numeral (evalPRF f xs)))

zeroFormula : {n : ℕ} → Vec Term n → Term → Formula
zeroFormula xs y = y ≈ zeroᵗ

sucFormula : Vec Term (suc zero) → Term → Formula
sucFormula (x ∷ []) y = y ≈ sucᵗ x

projFormula : {n : ℕ} → Fin n → Vec Term n → Term → Formula
projFormula i xs y = y ≈ lookup i xs

zeroF-represented : {n : ℕ} → PARepresentsFunction (zeroF {n})
zeroF-represented = record
  { graphFormula = zeroFormula
  ; represents-value = λ xs → eq-refl-rule zeroᵗ
  ; represents-unique = λ xs y z → eq-unique-value
  ; represents-exists = λ xs → zeroᵗ ,Σ eq-refl-rule zeroᵗ
  }

sucF-represented : PARepresentsFunction sucF
sucF-represented = record
  { graphFormula = sucFormula
  ; represents-value = λ
      { (x ∷ []) → eq-refl-rule (sucᵗ (numeral x)) }
  ; represents-unique = λ
      { (x ∷ []) y z → eq-unique-value }
  ; represents-exists = λ
      { (x ∷ []) → sucᵗ (numeral x) ,Σ
                    eq-refl-rule (sucᵗ (numeral x)) }
  }

projF-represented :
  {n : ℕ} → (i : Fin n) → PARepresentsFunction (projF i)
projF-represented i = record
  { graphFormula = projFormula i
  ; represents-value = λ xs →
      pa-provable-cong
        (cong (λ t → numeral (lookup i xs) ≈ t)
              (sym (lookup-mapVec numeral i xs)))
        (eq-refl-rule (numeral (lookup i xs)))
  ; represents-unique = λ xs y z → eq-unique-value
  ; represents-exists = λ xs →
      lookup i (numeralVec xs) ,Σ
      eq-refl-rule (lookup i (numeralVec xs))
  }

andVecFormula : {n : ℕ} → Vec Formula n → Formula
andVecFormula [] = zeroᵗ ≈ zeroᵗ
andVecFormula (A ∷ []) = A
andVecFormula (A ∷ B ∷ As) = A ∧ andVecFormula (B ∷ As)

existsVecFormula : ℕ → Formula → Formula
existsVecFormula zero A = A
existsVecFormula (suc n) A = ∃ᶠ (existsVecFormula n A)

graphVecFormula :
  {n m : ℕ} → {fs : Vec (PRF n) m} →
  AllPRF PARepresentsFunction fs →
  Vec Term n →
  Vec Term m →
  Formula
graphVecFormula all[] xs [] = zeroᵗ ≈ zeroᵗ
graphVecFormula (all∷ g-rep reps) xs (z ∷ zs) =
  PARepresentsFunction.graphFormula g-rep xs z ∧
  graphVecFormula reps xs zs

evalPRFsVec : {n m : ℕ} → Vec (PRF n) m → Vec ℕ n → Vec ℕ m
evalPRFsVec = evalPRFs

graphVecFormula-value :
  {n m : ℕ} → {fs : Vec (PRF n) m} →
  (reps : AllPRF PARepresentsFunction fs) →
  (xs : Vec ℕ n) →
  PA-provable
    (graphVecFormula reps (numeralVec xs) (numeralVec (evalPRFs fs xs)))
graphVecFormula-value all[] xs = eq-refl-rule zeroᵗ
graphVecFormula-value (all∷ f-rep reps) xs =
  and-intro-use
    (PARepresentsFunction.represents-value f-rep xs)
    (graphVecFormula-value reps xs)

compositionWitnessTerms :
  {n m : ℕ} →
  (gs : Vec (PRF n) m) →
  Vec Term n →
  Vec Term m
compositionWitnessTerms gs xs =
  numeralVec (evalPRFs gs (termValues xs))

compositionGraphFormula :
  {n m : ℕ} →
  (f : PRF m) →
  (gs : Vec (PRF n) m) →
  PARepresentsFunction f →
  AllPRF PARepresentsFunction gs →
  Vec Term n →
  Term →
  Formula
compositionGraphFormula f gs f-rep gs-reps xs y =
  PARepresentsFunction.graphFormula
    f-rep
    (compositionWitnessTerms gs xs)
    y
  ∧
  graphVecFormula gs-reps xs (compositionWitnessTerms gs xs)

compositionGraphFormula-value :
  {n m : ℕ} →
  (f : PRF m) →
  (gs : Vec (PRF n) m) →
  (f-rep : PARepresentsFunction f) →
  (gs-reps : AllPRF PARepresentsFunction gs) →
  (xs : Vec ℕ n) →
  PA-provable
    (compositionGraphFormula f gs f-rep gs-reps
      (numeralVec xs)
      (numeral (evalPRF (compF f gs) xs)))
compositionGraphFormula-value f gs f-rep gs-reps xs
  rewrite termValues-numeralVec xs =
  and-intro-use
    (PARepresentsFunction.represents-value f-rep (evalPRFs gs xs))
    (graphVecFormula-value gs-reps xs)

compositionGraphFormula-unique :
  {n m : ℕ} →
  (f : PRF m) →
  (gs : Vec (PRF n) m) →
  (f-rep : PARepresentsFunction f) →
  (gs-reps : AllPRF PARepresentsFunction gs) →
  (xs : Vec ℕ n) →
  (y z : Term) →
  PA-provable
    (compositionGraphFormula f gs f-rep gs-reps (numeralVec xs) y ⇒
     (compositionGraphFormula f gs f-rep gs-reps (numeralVec xs) z ⇒
      y ≈ z))
compositionGraphFormula-unique f gs f-rep gs-reps xs y z
  rewrite termValues-numeralVec xs =
  and-left-imp-use
    (PARepresentsFunction.represents-unique
      f-rep (evalPRFs gs xs) y z)

-- The closure steps below are the genuine remaining work for a full PR
-- representability theorem.  Composition needs existential witnesses for
-- intermediate values; primitive recursion needs sequence coding and bounded
-- reasoning inside PA.
record PACompositionRepresentabilityTarget : Set₁ where
  field
    composition-closes :
      {n m : ℕ} →
      (f : PRF m) →
      (gs : Vec (PRF n) m) →
      PARepresentsFunction f →
      AllPRF PARepresentsFunction gs →
      PARepresentsFunction (compF f gs)

composition-closes :
  {n m : ℕ} →
  (f : PRF m) →
  (gs : Vec (PRF n) m) →
      PARepresentsFunction f →
      AllPRF PARepresentsFunction gs →
      PARepresentsFunction (compF f gs)
composition-closes f gs f-rep gs-reps = record
  { graphFormula = compositionGraphFormula f gs f-rep gs-reps
  ; represents-value = compositionGraphFormula-value f gs f-rep gs-reps
  ; represents-unique = λ xs y z →
      compositionGraphFormula-unique f gs f-rep gs-reps xs y z
  ; represents-exists = λ xs →
      numeral (evalPRF (compF f gs) xs) ,Σ
      compositionGraphFormula-value f gs f-rep gs-reps xs
  }

record PAPrimitiveRecursionRepresentabilityTarget : Set₁ where
  field
    primitive-recursion-closes :
      {n : ℕ} →
      (g : PRF n) →
      (h : PRF (suc (suc n))) →
      PARepresentsFunction g →
      PARepresentsFunction h →
      PARepresentsFunction (precF g h)

primitive-recursion-closes :
  {n : ℕ} →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
      PARepresentsFunction g →
      PARepresentsFunction h →
      PARepresentsFunction (precF g h)
primitive-recursion-closes {n} g h g-rep h-rep = record
  { graphFormula = evaluatedGraphFormula (precF g h)
  ; represents-value = evaluatedGraphFormula-value (precF g h)
  ; represents-unique = primitive-recursion-unique
  ; represents-exists = λ xs →
      numeral (evalPRF (precF g h) xs) ,Σ
      evaluatedGraphFormula-value (precF g h) xs
  }
  where
    primitive-recursion-unique :
      (xs : Vec ℕ (suc n)) → (y z : Term) →
      PA-provable
        (evaluatedGraphFormula (precF g h) (numeralVec xs) y ⇒
         (evaluatedGraphFormula (precF g h) (numeralVec xs) z ⇒ y ≈ z))
    primitive-recursion-unique xs y z
      rewrite termValues-numeralVec xs =
        (eq-unique-value
          {y = y}
          {z = z}
          {c = numeral (evalPRF (precF g h) xs)})

mutual
  prf-represented : {n : ℕ} → (f : PRF n) → PARepresentsFunction f
  prf-represented zeroF = zeroF-represented
  prf-represented sucF = sucF-represented
  prf-represented (projF i) = projF-represented i
  prf-represented (compF f gs) =
    composition-closes f gs (prf-represented f) (allRepresented gs)
  prf-represented (precF g h) =
    primitive-recursion-closes g h (prf-represented g) (prf-represented h)

  allRepresented :
    {n m : ℕ} →
    (fs : Vec (PRF n) m) →
    AllPRF PARepresentsFunction fs
  allRepresented [] = all[]
  allRepresented (f ∷ fs) = all∷ (prf-represented f) (allRepresented fs)

composition-target : PACompositionRepresentabilityTarget
composition-target = record
  { composition-closes = composition-closes
  }

primitive-recursion-target : PAPrimitiveRecursionRepresentabilityTarget
primitive-recursion-target = record
  { primitive-recursion-closes = primitive-recursion-closes
  }

prrel-represented : {n : ℕ} → (R : PRRel n) → PARepresentsRelation R
prrel-represented R = record
  { relationFormula = λ xs →
      evaluatedGraphFormula (PRRel.characteristic R) xs (numeral (suc zero))
  ; represents-true = λ xs holds →
      pa-provable-cong
        (cong
          (λ k →
            numeral (suc zero) ≈ numeral k)
          (sym
            (trans
              (cong (evalPRF (PRRel.characteristic R))
                    (termValues-numeralVec xs))
              holds)))
        (eq-refl-rule (numeral (suc zero)))
  ; represents-false = λ xs not-holds →
      pa-provable-cong
        (cong
          (λ ys →
            ¬ᶠ
              (numeral (suc zero) ≈
               numeral (evalPRF (PRRel.characteristic R) ys)))
          (sym (termValues-numeralVec xs)))
        (closed-numeral-neq
          (suc zero)
          (evalPRF (PRRel.characteristic R) xs)
          (λ eq → not-holds (sym eq)))
  }
