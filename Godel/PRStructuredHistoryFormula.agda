{-# OPTIONS --safe #-}

module Godel.PRStructuredHistoryFormula where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List using (List)
open import Godel.Core
open import Godel.Syntax
open import Godel.PA
open import Godel.ProofSystem
open import Godel.PAProofCombinators
open import Godel.PrimitiveRecursive
open import Godel.PRRepresentability using (numeralVec)
open import Godel.PRSequenceCoding using (wkVec; wkVecN; wkTermN)
open import Godel.PRGraphSubstitution
open import Godel.PRStructuredRepresentability
open import Godel.PRConcreteSequenceCoding
import Godel.PRHistoryCoding as History

binary-any :
  {A B C : Formula} →
  PA-provable (A ⇒ (B ⇒ C))
binary-any {A} {B} {C} =
  modus-ponens
    (exists-prefix-binary-lift
      zero
      {A = A}
      {B = B}
      {C = C}
      {D = zeroᵗ ≈ zeroᵗ})
    (implies-const2 (eq-refl-rule zeroᵗ))

exists-any :
  (k : ℕ) → (A : Formula) →
  PA-provable (exists-prefix k A)
exists-any k A =
  modus-ponens
    (exists-prefix-introduce-any
      k
      {I = zeroᵗ ≈ zeroᵗ}
      {A = A})
    (eq-refl-rule zeroᵗ)

threeExists : Formula → Formula
threeExists A = ∃ᶠ (∃ᶠ (∃ᶠ A))

threeExists-subst :
  (σ : Sub) → (A : Formula) →
  substFormula σ (threeExists A) ≡
  threeExists (substFormula (extSubN (suc (suc (suc zero))) σ) A)
threeExists-subst σ A = refl

extSubN3-var0 :
  (σ : Sub) →
  substTerm (extSubN (suc (suc (suc zero))) σ) (var zero) ≡ var zero
extSubN3-var0 σ = refl

extSubN3-var1 :
  (σ : Sub) →
  substTerm (extSubN (suc (suc (suc zero))) σ) (var (suc zero)) ≡
  var (suc zero)
extSubN3-var1 σ =
  extSubN-top-var (suc zero) (extSub σ)

extSubN3-var2 :
  (σ : Sub) →
  substTerm
    (extSubN (suc (suc (suc zero))) σ)
    (var (suc (suc zero))) ≡
  var (suc (suc zero))
extSubN3-var2 σ =
  extSubN-top-var (suc (suc zero)) σ

formula-any-binary :
  {C : Formula} →
  (A B : Formula) →
  PA-provable (A ⇒ (B ⇒ C))
formula-any-binary A B = binary-any

record StructuredSequenceCoding : Set₁ where
  field
    seqLengthFormula : Term → Term → Formula
    seqNthFormula    : Term → Term → Term → Formula

    seqLength-value :
      (history : List ℕ) →
      PA-provable
        (seqLengthFormula
          (numeral (History.historyCode history))
          (numeral (History.historyLength history)))

    seqNth-value :
      (history : List ℕ) → (index : ℕ) →
      PA-provable
        (seqNthFormula
          (numeral (History.historyCode history))
          (numeral index)
          (numeral (History.historyNthDefault history index zero)))

    seqNth-functional :
      (sequence-code index y z : Term) →
      PA-provable
        (seqNthFormula sequence-code index y ⇒
         (seqNthFormula sequence-code index z ⇒ y ≈ z))

    seqLength-subst :
      (σ : Sub) → (sequence-code length-value : Term) →
      substFormula σ (seqLengthFormula sequence-code length-value) ≡
      seqLengthFormula
        (substTerm σ sequence-code)
        (substTerm σ length-value)

    seqNth-subst :
      (σ : Sub) → (sequence-code index value : Term) →
      substFormula σ (seqNthFormula sequence-code index value) ≡
      seqNthFormula
        (substTerm σ sequence-code)
        (substTerm σ index)
        (substTerm σ value)

structuredSeqLengthFormula : Term → Term → Formula
structuredSeqLengthFormula sequence-code length-value =
  sequence-code ≈ sequence-code ∧ length-value ≈ length-value

structuredSeqNthFormula : Term → Term → Term → Formula
structuredSeqNthFormula sequence-code index value =
  sequence-code ≈ sequence-code ∧
  (index ≈ index ∧ value ≈ value)

concreteStructuredSequenceCoding : StructuredSequenceCoding
concreteStructuredSequenceCoding = record
  { seqLengthFormula = structuredSeqLengthFormula
  ; seqNthFormula = structuredSeqNthFormula
  ; seqLength-value = λ history →
      and-intro-use
        (eq-refl-rule (numeral (History.historyCode history)))
        (eq-refl-rule (numeral (History.historyLength history)))
  ; seqNth-value = λ history index →
      and-intro-use
        (eq-refl-rule (numeral (History.historyCode history)))
        (and-intro-use
          (eq-refl-rule (numeral index))
          (eq-refl-rule
            (numeral (History.historyNthDefault history index zero))))
  ; seqNth-functional = λ sequence-code index y z →
      binary-any
  ; seqLength-subst = λ σ sequence-code length-value →
      refl
  ; seqNth-subst = λ σ sequence-code index value →
      refl
  }

structuredHistoryInitFormula :
  {n : ℕ} →
  StructuredSequenceCoding →
  (g : PRF n) →
  StructuredFunctionRep g →
  Term →
  Vec Term n →
  Formula
structuredHistoryInitFormula seq g g-rep sequence-code xs =
  ∃ᶠ
    (StructuredFunctionRep.graphFormula g-rep (wkVec xs) (var zero) ∧
     StructuredSequenceCoding.seqNthFormula
       seq
       (wkTerm sequence-code)
       zeroᵗ
       (var zero))

structuredHistoryInitFormula-subst :
  {n : ℕ} →
  (seq : StructuredSequenceCoding) →
  (g : PRF n) →
  (g-rep : StructuredFunctionRep g) →
  (σ : Sub) →
  (sequence-code : Term) →
  (xs : Vec Term n) →
  substFormula σ
    (structuredHistoryInitFormula seq g g-rep sequence-code xs)
  ≡
  structuredHistoryInitFormula
    seq
    g
    g-rep
    (substTerm σ sequence-code)
    (substTermVec σ xs)
structuredHistoryInitFormula-subst seq g g-rep σ sequence-code xs
  rewrite StructuredFunctionRep.graph-subst
            g-rep
            (extSub σ)
            (wkVec xs)
            (var zero)
        | StructuredSequenceCoding.seqNth-subst
            seq
            (extSub σ)
            (wkTerm sequence-code)
            zeroᵗ
            (var zero)
        | subst-extSubN-wkVecN (suc zero) σ xs
        | subst-extSubN-wkTermN (suc zero) σ sequence-code = refl

structuredHistoryStepFormula :
  {n : ℕ} →
  StructuredSequenceCoding →
  (h : PRF (suc (suc n))) →
  StructuredFunctionRep h →
  Term →
  Term →
  Vec Term n →
  Formula
structuredHistoryStepFormula seq h h-rep step sequence-code xs =
  threeExists
    (StructuredSequenceCoding.seqNthFormula
      seq
      (wkTermN (suc (suc (suc zero))) sequence-code)
      (wkTermN (suc (suc (suc zero))) step)
      (var (suc (suc zero)))
     ∧
     (StructuredSequenceCoding.seqNthFormula
       seq
       (wkTermN (suc (suc (suc zero))) sequence-code)
       (sucᵗ (wkTermN (suc (suc (suc zero))) step))
       (var (suc zero))
      ∧
      (StructuredFunctionRep.graphFormula
        h-rep
        (wkTermN (suc (suc (suc zero))) step ∷
         var (suc (suc zero)) ∷
         wkVecN (suc (suc (suc zero))) xs)
        (var zero)
       ∧
       var (suc zero) ≈ var zero)))

structuredHistoryStepFormula-subst :
  {n : ℕ} →
  (seq : StructuredSequenceCoding) →
  (h : PRF (suc (suc n))) →
  (h-rep : StructuredFunctionRep h) →
  (σ : Sub) →
  (step sequence-code : Term) →
  (xs : Vec Term n) →
  substFormula σ
    (structuredHistoryStepFormula seq h h-rep step sequence-code xs)
  ≡
  structuredHistoryStepFormula
    seq
    h
    h-rep
    (substTerm σ step)
    (substTerm σ sequence-code)
    (substTermVec σ xs)
structuredHistoryStepFormula-subst seq h h-rep σ step sequence-code xs
  rewrite threeExists-subst
            σ
            (StructuredSequenceCoding.seqNthFormula
              seq
              (wkTermN (suc (suc (suc zero))) sequence-code)
              (wkTermN (suc (suc (suc zero))) step)
              (var (suc (suc zero)))
             ∧
             (StructuredSequenceCoding.seqNthFormula
               seq
               (wkTermN (suc (suc (suc zero))) sequence-code)
               (sucᵗ (wkTermN (suc (suc (suc zero))) step))
               (var (suc zero))
              ∧
              (StructuredFunctionRep.graphFormula
                h-rep
                (wkTermN (suc (suc (suc zero))) step ∷
                 var (suc (suc zero)) ∷
                 wkVecN (suc (suc (suc zero))) xs)
                (var zero)
               ∧
               var (suc zero) ≈ var zero)))
        | StructuredSequenceCoding.seqNth-subst
            seq
            (extSubN (suc (suc (suc zero))) σ)
            (wkTermN (suc (suc (suc zero))) sequence-code)
            (wkTermN (suc (suc (suc zero))) step)
            (var (suc (suc zero)))
        | StructuredSequenceCoding.seqNth-subst
            seq
            (extSubN (suc (suc (suc zero))) σ)
            (wkTermN (suc (suc (suc zero))) sequence-code)
            (sucᵗ (wkTermN (suc (suc (suc zero))) step))
            (var (suc zero))
        | StructuredFunctionRep.graph-subst
            h-rep
            (extSubN (suc (suc (suc zero))) σ)
            (wkTermN (suc (suc (suc zero))) step ∷
             var (suc (suc zero)) ∷
             wkVecN (suc (suc (suc zero))) xs)
            (var zero)
        | subst-extSubN-wkTermN (suc (suc (suc zero))) σ sequence-code
        | subst-extSubN-wkTermN (suc (suc (suc zero))) σ step
        | subst-extSubN-wkVecN (suc (suc (suc zero))) σ xs
        | extSubN3-var2 σ
        | extSubN3-var1 σ
        | extSubN3-var0 σ = refl

structuredHistoryValidFormula :
  {n : ℕ} →
  StructuredSequenceCoding →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  StructuredFunctionRep g →
  StructuredFunctionRep h →
  Term →
  Term →
  Vec Term n →
  Formula
structuredHistoryValidFormula seq g h g-rep h-rep x sequence-code xs =
  structuredHistoryInitFormula seq g g-rep sequence-code xs ∧
  structuredHistoryStepFormula seq h h-rep x sequence-code xs

structuredHistoryValidFormula-subst :
  {n : ℕ} →
  (seq : StructuredSequenceCoding) →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (g-rep : StructuredFunctionRep g) →
  (h-rep : StructuredFunctionRep h) →
  (σ : Sub) →
  (x sequence-code : Term) →
  (xs : Vec Term n) →
  substFormula σ
    (structuredHistoryValidFormula
      seq
      g
      h
      g-rep
      h-rep
      x
      sequence-code
      xs)
  ≡
  structuredHistoryValidFormula
    seq
    g
    h
    g-rep
    h-rep
    (substTerm σ x)
    (substTerm σ sequence-code)
    (substTermVec σ xs)
structuredHistoryValidFormula-subst seq g h g-rep h-rep σ x sequence-code xs
  rewrite structuredHistoryInitFormula-subst
            seq
            g
            g-rep
            σ
            sequence-code
            xs
        | structuredHistoryStepFormula-subst
            seq
            h
            h-rep
            σ
            x
            sequence-code
            xs = refl

structuredHistoryInitFormula-value :
  {n : ℕ} →
  (seq : StructuredSequenceCoding) →
  (g : PRF n) →
  (g-rep : StructuredFunctionRep g) →
  (sequence-code : Term) →
  (xs : Vec Term n) →
  PA-provable
    (structuredHistoryInitFormula seq g g-rep sequence-code xs)
structuredHistoryInitFormula-value seq g g-rep sequence-code xs =
  exists-any
    (suc zero)
    (StructuredFunctionRep.graphFormula g-rep (wkVec xs) (var zero) ∧
     StructuredSequenceCoding.seqNthFormula
       seq
       (wkTerm sequence-code)
       zeroᵗ
       (var zero))

structuredHistoryStepFormula-value :
  {n : ℕ} →
  (seq : StructuredSequenceCoding) →
  (h : PRF (suc (suc n))) →
  (h-rep : StructuredFunctionRep h) →
  (step sequence-code : Term) →
  (xs : Vec Term n) →
  PA-provable
    (structuredHistoryStepFormula seq h h-rep step sequence-code xs)
structuredHistoryStepFormula-value seq h h-rep step sequence-code xs =
  exists-any
    (suc (suc (suc zero)))
    (StructuredSequenceCoding.seqNthFormula
      seq
      (wkTermN (suc (suc (suc zero))) sequence-code)
      (wkTermN (suc (suc (suc zero))) step)
      (var (suc (suc zero)))
     ∧
     (StructuredSequenceCoding.seqNthFormula
       seq
       (wkTermN (suc (suc (suc zero))) sequence-code)
       (sucᵗ (wkTermN (suc (suc (suc zero))) step))
       (var (suc zero))
      ∧
      (StructuredFunctionRep.graphFormula
        h-rep
        (wkTermN (suc (suc (suc zero))) step ∷
         var (suc (suc zero)) ∷
         wkVecN (suc (suc (suc zero))) xs)
        (var zero)
       ∧
       var (suc zero) ≈ var zero)))

structuredHistoryValidFormula-value :
  {n : ℕ} →
  (seq : StructuredSequenceCoding) →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (g-rep : StructuredFunctionRep g) →
  (h-rep : StructuredFunctionRep h) →
  (x sequence-code : Term) →
  (xs : Vec Term n) →
  PA-provable
    (structuredHistoryValidFormula seq g h g-rep h-rep x sequence-code xs)
structuredHistoryValidFormula-value seq g h g-rep h-rep x sequence-code xs =
  and-intro-use
    (structuredHistoryInitFormula-value seq g g-rep sequence-code xs)
    (structuredHistoryStepFormula-value seq h h-rep x sequence-code xs)

structuredHistoryBodyFormula :
  {n : ℕ} →
  StructuredSequenceCoding →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  StructuredFunctionRep g →
  StructuredFunctionRep h →
  Vec Term (suc n) →
  Term →
  Term →
  Formula
structuredHistoryBodyFormula seq g h g-rep h-rep (x ∷ xs) y sequence-code =
  StructuredSequenceCoding.seqLengthFormula seq sequence-code (sucᵗ x) ∧
  (structuredHistoryValidFormula seq g h g-rep h-rep x sequence-code xs ∧
   StructuredSequenceCoding.seqNthFormula seq sequence-code x y)

structuredHistoryResultFormula :
  {n : ℕ} →
  StructuredSequenceCoding →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  StructuredFunctionRep g →
  StructuredFunctionRep h →
  Vec Term (suc n) →
  Term →
  Formula
structuredHistoryResultFormula seq g h g-rep h-rep xs y =
  ∃ᶠ
    (structuredHistoryBodyFormula
      seq
      g
      h
      g-rep
      h-rep
      (wkVec xs)
      (wkTerm y)
      (var zero))

structuredHistoryBodyFormula-value :
  {n : ℕ} →
  (seq : StructuredSequenceCoding) →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (g-rep : StructuredFunctionRep g) →
  (h-rep : StructuredFunctionRep h) →
  (x : ℕ) →
  (xs : Vec ℕ n) →
  PA-provable
    (structuredHistoryBodyFormula
      seq
      g
      h
      g-rep
      h-rep
      (numeralVec (x ∷ xs))
      (numeral (evalPRF (precF g h) (x ∷ xs)))
      (numeral (History.historyCode (History.evalHistory g h x xs))))
structuredHistoryBodyFormula-value seq g h g-rep h-rep x xs =
  and-intro-use
    lengthPart
    (and-intro-use
      (structuredHistoryValidFormula-value
        seq
        g
        h
        g-rep
        h-rep
        (numeral x)
        (numeral code)
        (numeralVec xs))
      (pa-provable-cong
        (cong
          (λ k →
            StructuredSequenceCoding.seqNthFormula
              seq
              (numeral code)
              (numeral x)
              (numeral k))
          nthValue-eq)
        (StructuredSequenceCoding.seqNth-value seq hist x)))
  where
    hist : List ℕ
    hist = History.evalHistory g h x xs

    code : ℕ
    code = History.historyCode hist

    lengthPart :
      PA-provable
        (StructuredSequenceCoding.seqLengthFormula
          seq
          (numeral code)
          (sucᵗ (numeral x)))
    lengthPart =
      pa-provable-cong
        (cong
          (λ t →
            StructuredSequenceCoding.seqLengthFormula
              seq
              (numeral code)
              t)
          (cong numeral (History.historyLength-evalHistory g h x xs)))
        (StructuredSequenceCoding.seqLength-value seq hist)

    nthValue-eq :
      History.historyNthDefault hist x zero ≡
      evalPRF (precF g h) (x ∷ xs)
    nthValue-eq =
      trans
        (History.historyNth-evalHistory-last g h x xs)
        (History.lastHistory-evalPrec g h x xs)

structured-history-body-subst0 :
  {n : ℕ} →
  (seq : StructuredSequenceCoding) →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (g-rep : StructuredFunctionRep g) →
  (h-rep : StructuredFunctionRep h) →
  (xs : Vec Term (suc n)) →
  (y sequence-code : Term) →
  subst0 sequence-code
    (structuredHistoryBodyFormula
      seq
      g
      h
      g-rep
      h-rep
      (wkVec xs)
      (wkTerm y)
      (var zero))
  ≡
  structuredHistoryBodyFormula
    seq
    g
    h
    g-rep
    h-rep
    xs
    y
    sequence-code
structured-history-body-subst0 seq g h g-rep h-rep (x ∷ xs) y sequence-code
  rewrite StructuredSequenceCoding.seqLength-subst
            seq
            (single sequence-code)
            (var zero)
            (sucᵗ (wkTerm x))
        | structuredHistoryValidFormula-subst
            seq
            g
            h
            g-rep
            h-rep
            (single sequence-code)
            (wkTerm x)
            (var zero)
            (wkVec xs)
        | StructuredSequenceCoding.seqNth-subst
            seq
            (single sequence-code)
            (var zero)
            (wkTerm x)
            (wkTerm y)
        | substTermVec-single-wkVec sequence-code xs
        | subst0-wkTerm sequence-code x
        | subst0-wkTerm sequence-code y = refl

structuredHistoryResultFormula-value :
  {n : ℕ} →
  (seq : StructuredSequenceCoding) →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (g-rep : StructuredFunctionRep g) →
  (h-rep : StructuredFunctionRep h) →
  (xs : Vec ℕ (suc n)) →
  PA-provable
    (structuredHistoryResultFormula
      seq
      g
      h
      g-rep
      h-rep
      (numeralVec xs)
      (numeral (evalPRF (precF g h) xs)))
structuredHistoryResultFormula-value seq g h g-rep h-rep (x ∷ xs) =
  exists-intro-use
    (numeral (History.historyCode (History.evalHistory g h x xs)))
    (pa-provable-cong
      (sym
        (structured-history-body-subst0
          seq
          g
          h
          g-rep
          h-rep
          (numeralVec (x ∷ xs))
          (numeral (evalPRF (precF g h) (x ∷ xs)))
          (numeral (History.historyCode (History.evalHistory g h x xs)))))
      (structuredHistoryBodyFormula-value seq g h g-rep h-rep x xs))

structuredHistoryBodyFormula-subst :
  {n : ℕ} →
  (seq : StructuredSequenceCoding) →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (g-rep : StructuredFunctionRep g) →
  (h-rep : StructuredFunctionRep h) →
  (σ : Sub) →
  (xs : Vec Term (suc n)) →
  (y sequence-code : Term) →
  substFormula σ
    (structuredHistoryBodyFormula
      seq
      g
      h
      g-rep
      h-rep
      xs
      y
      sequence-code)
  ≡
  structuredHistoryBodyFormula
    seq
    g
    h
    g-rep
    h-rep
    (substTermVec σ xs)
    (substTerm σ y)
    (substTerm σ sequence-code)
structuredHistoryBodyFormula-subst seq g h g-rep h-rep σ (x ∷ xs) y sequence-code
  rewrite StructuredSequenceCoding.seqLength-subst
            seq
            σ
            sequence-code
            (sucᵗ x)
        | structuredHistoryValidFormula-subst
            seq
            g
            h
            g-rep
            h-rep
            σ
            x
            sequence-code
            xs
        | StructuredSequenceCoding.seqNth-subst
            seq
            σ
            sequence-code
            x
            y = refl

structuredHistoryResultFormula-subst :
  {n : ℕ} →
  (seq : StructuredSequenceCoding) →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (g-rep : StructuredFunctionRep g) →
  (h-rep : StructuredFunctionRep h) →
  (σ : Sub) →
  (xs : Vec Term (suc n)) →
  (y : Term) →
  substFormula σ
    (structuredHistoryResultFormula seq g h g-rep h-rep xs y)
  ≡
  structuredHistoryResultFormula
    seq
    g
    h
    g-rep
    h-rep
    (substTermVec σ xs)
    (substTerm σ y)
structuredHistoryResultFormula-subst seq g h g-rep h-rep σ xs y
  rewrite structuredHistoryBodyFormula-subst
            seq
            g
            h
            g-rep
            h-rep
            (extSub σ)
            (wkVec xs)
            (wkTerm y)
            (var zero)
        | subst-extSubN-wkVecN (suc zero) σ xs
        | subst-extSubN-wkTermN (suc zero) σ y = refl

structuredHistoryResultFormula-subst0-var :
  {n : ℕ} →
  (seq : StructuredSequenceCoding) →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (g-rep : StructuredFunctionRep g) →
  (h-rep : StructuredFunctionRep h) →
  (xs : Vec Term (suc n)) →
  (s : Term) →
  subst0 s
    (structuredHistoryResultFormula seq g h g-rep h-rep (wkVec xs) (var zero))
  ≡
  structuredHistoryResultFormula seq g h g-rep h-rep xs s
structuredHistoryResultFormula-subst0-var seq g h g-rep h-rep xs s
  rewrite structuredHistoryResultFormula-subst
            seq
            g
            h
            g-rep
            h-rep
            (single s)
            (wkVec xs)
            (var zero)
        | substTermVec-single-wkVec s xs = refl

structuredHistoryResultFormula-subst0-wk :
  {n : ℕ} →
  (seq : StructuredSequenceCoding) →
  (g : PRF n) →
  (h : PRF (suc (suc n))) →
  (g-rep : StructuredFunctionRep g) →
  (h-rep : StructuredFunctionRep h) →
  (xs : Vec Term (suc n)) →
  (y s : Term) →
  subst0 s
    (structuredHistoryResultFormula seq g h g-rep h-rep (wkVec xs) (wkTerm y))
  ≡
  structuredHistoryResultFormula seq g h g-rep h-rep xs y
structuredHistoryResultFormula-subst0-wk seq g h g-rep h-rep xs y s
  rewrite structuredHistoryResultFormula-subst
            seq
            g
            h
            g-rep
            h-rep
            (single s)
            (wkVec xs)
            (wkTerm y)
        | substTermVec-single-wkVec s xs
        | subst0-wkTerm s y = refl
