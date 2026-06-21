{-# OPTIONS --safe #-}

module Godel.PRStructuredRepresentability where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Godel.Core
open import Godel.Syntax
open import Godel.PA
open import Godel.ProofSystem
open import Godel.PAProofCombinators using (implies-refl; exists-intro-use)
open import Godel.PrimitiveRecursive
open import Godel.PRRepresentability
open import Godel.PRSequenceCoding using (wkVec; wkVecN; wkTermN)
open import Godel.PRGraphSubstitution

pa-provable-cong : {A B : Formula} → A ≡ B → PA-provable A → PA-provable B
pa-provable-cong eq p = subst PA-provable eq p

eqVecFormula : {n : ℕ} → Vec Term n → Vec Term n → Formula
eqVecFormula [] [] = zeroᵗ ≈ zeroᵗ
eqVecFormula (x ∷ []) (y ∷ []) = x ≈ y
eqVecFormula (x ∷ x₂ ∷ xs) (y ∷ y₂ ∷ ys) =
  x ≈ y ∧ eqVecFormula (x₂ ∷ xs) (y₂ ∷ ys)

ignore-input-congruence :
  {E G : Formula} →
  PA-provable (E ⇒ (G ⇒ G))
ignore-input-congruence {E} {G} =
  modus-ponens
    (hilbert-K {A = G ⇒ G} {B = E})
    implies-refl

implies-const :
  {A B : Formula} →
  PA-provable B →
  PA-provable (A ⇒ B)
implies-const {A} {B} p =
  modus-ponens (hilbert-K {A = B} {B = A}) p

implies-const2 :
  {A B C : Formula} →
  PA-provable C →
  PA-provable (A ⇒ (B ⇒ C))
implies-const2 p = implies-const (implies-const p)

record StructuredFunctionRep {n : ℕ} (f : PRF n) : Set₁ where
  field
    graphFormula :
      Vec Term n → Term → Formula

    represents-value :
      (xs : Vec ℕ n) →
      PA-provable (graphFormula (numeralVec xs) (numeral (evalPRF f xs)))

    represents-unique-terms :
      (xs : Vec Term n) → (y z : Term) →
      PA-provable
        (graphFormula xs y ⇒
         (graphFormula xs z ⇒ y ≈ z))

    represents-exists :
      (xs : Vec ℕ n) →
      Σ Term (λ y → PA-provable (graphFormula (numeralVec xs) y))

    graph-input-congruence :
      (xs ys : Vec Term n) → (y : Term) →
      PA-provable
        (eqVecFormula xs ys ⇒
         (graphFormula xs y ⇒ graphFormula ys y))

    graph-subst :
      (σ : Sub) → (xs : Vec Term n) → (y : Term) →
      substFormula σ (graphFormula xs y) ≡
      graphFormula (substTermVec σ xs) (substTerm σ y)

    graph-subst0-var :
      (xs : Vec Term n) → (s : Term) →
      subst0 s (graphFormula (wkVec xs) (var zero)) ≡
      graphFormula xs s

    graph-subst0-wk :
      (xs : Vec Term n) → (y s : Term) →
      subst0 s (graphFormula (wkVec xs) (wkTerm y)) ≡
      graphFormula xs y

structured->PARepresentsFunction :
  {n : ℕ} → {f : PRF n} →
  StructuredFunctionRep f →
  PARepresentsFunction f
structured->PARepresentsFunction rep = record
  { graphFormula = StructuredFunctionRep.graphFormula rep
  ; represents-value = StructuredFunctionRep.represents-value rep
  ; represents-unique = λ xs →
      StructuredFunctionRep.represents-unique-terms rep (numeralVec xs)
  ; represents-exists = StructuredFunctionRep.represents-exists rep
  }

structuredZeroFormula : {n : ℕ} → Vec Term n → Term → Formula
structuredZeroFormula xs y = y ≈ zeroᵗ

structuredSucFormula : Vec Term (suc zero) → Term → Formula
structuredSucFormula (x ∷ []) y = y ≈ sucᵗ x

structuredProjFormula : {n : ℕ} → Fin n → Vec Term n → Term → Formula
structuredProjFormula i xs y = y ≈ lookup i xs

zeroF-structured :
  {n : ℕ} → StructuredFunctionRep (zeroF {n})
zeroF-structured = record
  { graphFormula = structuredZeroFormula
  ; represents-value = λ xs → eq-refl-rule zeroᵗ
  ; represents-unique-terms = λ xs y z → eq-unique-value
  ; represents-exists = λ xs → zeroᵗ ,Σ eq-refl-rule zeroᵗ
  ; graph-input-congruence = λ xs ys y → ignore-input-congruence
  ; graph-subst = λ σ xs y → refl
  ; graph-subst0-var = λ xs s → refl
  ; graph-subst0-wk = λ xs y s →
      cong (λ t → t ≈ zeroᵗ) (subst0-wkTerm s y)
  }

sucF-structured : StructuredFunctionRep sucF
sucF-structured = record
  { graphFormula = structuredSucFormula
  ; represents-value = λ
      { (x ∷ []) → eq-refl-rule (sucᵗ (numeral x)) }
  ; represents-unique-terms = λ
      { (x ∷ []) y z → eq-unique-value }
  ; represents-exists = λ
      { (x ∷ []) →
          sucᵗ (numeral x) ,Σ
          eq-refl-rule (sucᵗ (numeral x)) }
  ; graph-input-congruence = λ
      { (x ∷ []) (x' ∷ []) y → eq-subst-suc-right }
  ; graph-subst = λ
      { σ (x ∷ []) y → refl }
  ; graph-subst0-var = λ
      { (x ∷ []) s →
          suc-subst-var-stable x s }
  ; graph-subst0-wk = λ
      { (x ∷ []) y s →
          suc-subst-stable x y s }
  }
  where
    suc-subst-var-stable :
      (x s : Term) →
      subst0 s (structuredSucFormula (wkVec (x ∷ [])) (var zero)) ≡
      structuredSucFormula (x ∷ []) s
    suc-subst-var-stable x s
      rewrite subst0-wkTerm s x = refl

    suc-subst-stable :
      (x y s : Term) →
      subst0 s (structuredSucFormula (wkVec (x ∷ [])) (wkTerm y)) ≡
      structuredSucFormula (x ∷ []) y
    suc-subst-stable x y s
      rewrite subst0-wkTerm s y
            | subst0-wkTerm s x = refl

projF-structured :
  {n : ℕ} → (i : Fin n) → StructuredFunctionRep (projF i)
projF-structured i = record
  { graphFormula = structuredProjFormula i
  ; represents-value = λ xs →
      pa-provable-cong
        (cong (λ t → numeral (lookup i xs) ≈ t)
              (sym (lookup-mapVec numeral i xs)))
        (eq-refl-rule (numeral (lookup i xs)))
  ; represents-unique-terms = λ xs y z → eq-unique-value
  ; represents-exists = λ xs →
      lookup i (numeralVec xs) ,Σ
      eq-refl-rule (lookup i (numeralVec xs))
  ; graph-input-congruence = λ xs ys y →
      proj-input-congruence i xs ys y
  ; graph-subst = λ σ xs y →
      proj-graph-subst σ i xs y
  ; graph-subst0-var = λ xs s →
      proj-subst-var-stable i xs s
  ; graph-subst0-wk = λ xs y s →
      proj-subst-stable i xs y s
  }
  where
    proj-input-congruence :
      {n : ℕ} →
      (i : Fin n) → (xs ys : Vec Term n) → (y : Term) →
      PA-provable
        (eqVecFormula xs ys ⇒
         (structuredProjFormula i xs y ⇒
          structuredProjFormula i ys y))
    proj-input-congruence fzero (x ∷ []) (x' ∷ []) y =
      eq-subst-right
    proj-input-congruence fzero (x ∷ x₂ ∷ xs) (x' ∷ x₂' ∷ ys) y =
      modus-ponens and-left-imp1 eq-subst-right
    proj-input-congruence (fsuc i) (x ∷ x₂ ∷ xs) (x' ∷ x₂' ∷ ys) y =
      modus-ponens
        and-right-imp1
        (proj-input-congruence i (x₂ ∷ xs) (x₂' ∷ ys) y)

    proj-graph-subst :
      {n : ℕ} →
      (σ : Sub) → (i : Fin n) → (xs : Vec Term n) → (y : Term) →
      substFormula σ (structuredProjFormula i xs y) ≡
      structuredProjFormula i (substTermVec σ xs) (substTerm σ y)
    proj-graph-subst σ i xs y
      rewrite lookup-substTermVec σ i xs = refl

    proj-subst-var-stable :
      {n : ℕ} →
      (i : Fin n) → (xs : Vec Term n) → (s : Term) →
      subst0 s (structuredProjFormula i (wkVec xs) (var zero)) ≡
      structuredProjFormula i xs s
    proj-subst-var-stable i xs s
      rewrite lookup-subst0-wkVec s i xs = refl

    proj-subst-stable :
      {n : ℕ} →
      (i : Fin n) → (xs : Vec Term n) → (y s : Term) →
      subst0 s (structuredProjFormula i (wkVec xs) (wkTerm y)) ≡
      structuredProjFormula i xs y
    proj-subst-stable i xs y s
      rewrite subst0-wkTerm s y
            | lookup-subst0-wkVec s i xs = refl

andVecFormulaStructured : {n : ℕ} → Vec Formula n → Formula
andVecFormulaStructured [] = zeroᵗ ≈ zeroᵗ
andVecFormulaStructured (A ∷ []) = A
andVecFormulaStructured (A ∷ B ∷ As) =
  A ∧ andVecFormulaStructured (B ∷ As)

existsVecFormulaStructured : ℕ → Formula → Formula
existsVecFormulaStructured = exists-prefix

subst-existsVecFormulaStructured :
  (k : ℕ) → (σ : Sub) → (A : Formula) →
  substFormula σ (existsVecFormulaStructured k A) ≡
  existsVecFormulaStructured k (substFormula (extSubN k σ) A)
subst-existsVecFormulaStructured zero σ A = refl
subst-existsVecFormulaStructured (suc k) σ A =
  cong ∃ᶠ (subst-existsVecFormulaStructured k (extSub σ) A)

instantiateExistsPrefix :
  {n : ℕ} →
  Vec Term n →
  Formula →
  Formula
instantiateExistsPrefix [] A = A
instantiateExistsPrefix (t ∷ ts) (∃ᶠ A) =
  instantiateExistsPrefix ts (subst0 t A)
instantiateExistsPrefix (t ∷ ts) (s ≈ u) = s ≈ u
instantiateExistsPrefix (t ∷ ts) (Rel r us) = Rel r us
instantiateExistsPrefix (t ∷ ts) ⊥ᶠ = ⊥ᶠ
instantiateExistsPrefix (t ∷ ts) (A ⇒ B) = A ⇒ B
instantiateExistsPrefix (t ∷ ts) (A ∧ B) = A ∧ B
instantiateExistsPrefix (t ∷ ts) (A ∨ B) = A ∨ B
instantiateExistsPrefix (t ∷ ts) (¬ᶠ A) = ¬ᶠ A
instantiateExistsPrefix (t ∷ ts) (∀ᶠ A) = ∀ᶠ A

existsPrefix-intro-use :
  {n : ℕ} →
  (ts : Vec Term n) →
  (A : Formula) →
  PA-provable (instantiateExistsPrefix ts A) →
  PA-provable A
existsPrefix-intro-use [] A p = p
existsPrefix-intro-use (t ∷ ts) (∃ᶠ A) p =
  exists-intro-use t
    (existsPrefix-intro-use ts (subst0 t A) p)
existsPrefix-intro-use (t ∷ ts) (s ≈ u) p = p
existsPrefix-intro-use (t ∷ ts) (Rel r us) p = p
existsPrefix-intro-use (t ∷ ts) ⊥ᶠ p = p
existsPrefix-intro-use (t ∷ ts) (A ⇒ B) p = p
existsPrefix-intro-use (t ∷ ts) (A ∧ B) p = p
existsPrefix-intro-use (t ∷ ts) (A ∨ B) p = p
existsPrefix-intro-use (t ∷ ts) (¬ᶠ A) p = p
existsPrefix-intro-use (t ∷ ts) (∀ᶠ A) p = p

-- In a body under n nested existentials, the witnesses are available as
-- variables n-1, ..., 0.  This matches outer-to-inner introduction order:
-- for ∃ z₀. ∃ z₁. Body, z₀ appears as var 1 and z₁ as var 0 in Body.
boundVarVec : (n : ℕ) → Vec Term n
boundVarVec zero = []
boundVarVec (suc n) = var n ∷ boundVarVec n

subst-extSubN-boundVarVec :
  (k : ℕ) → (σ : Sub) →
  substTermVec (extSubN k σ) (boundVarVec k) ≡
  boundVarVec k
subst-extSubN-boundVarVec zero σ = refl
subst-extSubN-boundVarVec (suc k) σ
  rewrite extSubN-top-var k σ
        | subst-extSubN-boundVarVec k (extSub σ) = refl

graphVecFormulaStructured :
  {n m : ℕ} → {fs : Vec (PRF n) m} →
  AllPRF StructuredFunctionRep fs →
  Vec Term n →
  Vec Term m →
  Formula
graphVecFormulaStructured all[] xs [] = zeroᵗ ≈ zeroᵗ
graphVecFormulaStructured (all∷ g-rep reps) xs (z ∷ zs) =
  StructuredFunctionRep.graphFormula g-rep xs z ∧
  graphVecFormulaStructured reps xs zs

graphVecFormulaStructured-value :
  {n m : ℕ} → {fs : Vec (PRF n) m} →
  (reps : AllPRF StructuredFunctionRep fs) →
  (xs : Vec ℕ n) →
  PA-provable
    (graphVecFormulaStructured
      reps
      (numeralVec xs)
      (numeralVec (evalPRFs fs xs)))
graphVecFormulaStructured-value all[] xs = eq-refl-rule zeroᵗ
graphVecFormulaStructured-value (all∷ f-rep reps) xs =
  modus-ponens
    (modus-ponens and-introduce
      (StructuredFunctionRep.represents-value f-rep xs))
    (graphVecFormulaStructured-value reps xs)

graphVecFormulaStructured-subst :
  {n m : ℕ} → {fs : Vec (PRF n) m} →
  (reps : AllPRF StructuredFunctionRep fs) →
  (σ : Sub) →
  (xs : Vec Term n) →
  (zs : Vec Term m) →
  substFormula σ (graphVecFormulaStructured reps xs zs) ≡
  graphVecFormulaStructured
    reps
    (substTermVec σ xs)
    (substTermVec σ zs)
graphVecFormulaStructured-subst all[] σ xs [] = refl
graphVecFormulaStructured-subst (all∷ f-rep reps) σ xs (z ∷ zs)
  rewrite StructuredFunctionRep.graph-subst f-rep σ xs z
        | graphVecFormulaStructured-subst reps σ xs zs = refl

graphVecFormulaStructured-eq :
  {n m : ℕ} → {fs : Vec (PRF n) m} →
  (reps : AllPRF StructuredFunctionRep fs) →
  (xs : Vec Term n) →
  (zs ws : Vec Term m) →
  PA-provable
    (graphVecFormulaStructured reps xs zs ⇒
     (graphVecFormulaStructured reps xs ws ⇒
      eqVecFormula zs ws))
graphVecFormulaStructured-eq all[] xs [] [] =
  implies-const2 (eq-refl-rule zeroᵗ)
graphVecFormulaStructured-eq (all∷ g-rep all[]) xs (z ∷ []) (w ∷ []) =
  modus-ponens
    and-left-imp
    (StructuredFunctionRep.represents-unique-terms g-rep xs z w)
graphVecFormulaStructured-eq
  (all∷ g-rep (all∷ h-rep reps))
  xs
  (z ∷ z₂ ∷ zs)
  (w ∷ w₂ ∷ ws) =
  modus-ponens
    (modus-ponens
      imp-and-intro2
      (modus-ponens
        and-left-imp
        (StructuredFunctionRep.represents-unique-terms g-rep xs z w)))
    (modus-ponens
      and-right-imp
      (graphVecFormulaStructured-eq
        (all∷ h-rep reps)
        xs
        (z₂ ∷ zs)
        (w₂ ∷ ws)))

graphVecFormulaStructured-input-congruence :
  {n m : ℕ} → {fs : Vec (PRF n) m} →
  (reps : AllPRF StructuredFunctionRep fs) →
  (xs ys : Vec Term n) →
  (zs : Vec Term m) →
  PA-provable
    (eqVecFormula xs ys ⇒
     (graphVecFormulaStructured reps xs zs ⇒
      graphVecFormulaStructured reps ys zs))
graphVecFormulaStructured-input-congruence all[] xs ys [] =
  ignore-input-congruence
graphVecFormulaStructured-input-congruence (all∷ g-rep reps) xs ys (z ∷ zs) =
  modus-ponens
    (modus-ponens
      premise-and-both-map
      (StructuredFunctionRep.graph-input-congruence g-rep xs ys z))
    (graphVecFormulaStructured-input-congruence reps xs ys zs)

compositionWitnessTermsStructured :
  {n m : ℕ} →
  (gs : Vec (PRF n) m) →
  Vec ℕ n →
  Vec Term m
compositionWitnessTermsStructured gs xs = numeralVec (evalPRFs gs xs)

compositionBodyFormula :
  {n m : ℕ} → {f : PRF m} → {gs : Vec (PRF n) m} →
  StructuredFunctionRep f →
  AllPRF StructuredFunctionRep gs →
  Vec Term n →
  Term →
  Formula
compositionBodyFormula f-rep gs-reps xs y =
  graphVecFormulaStructured gs-reps xs (boundVarVec _) ∧
  StructuredFunctionRep.graphFormula f-rep (boundVarVec _) y

compositionBodyFormula-subst :
  {n m : ℕ} → {f : PRF m} → {gs : Vec (PRF n) m} →
  (f-rep : StructuredFunctionRep f) →
  (gs-reps : AllPRF StructuredFunctionRep gs) →
  (σ : Sub) →
  (xs : Vec Term n) →
  (y : Term) →
  substFormula (extSubN m σ)
    (compositionBodyFormula
      f-rep
      gs-reps
      (wkVecN m xs)
      (wkTermN m y))
  ≡
  compositionBodyFormula
    f-rep
    gs-reps
    (wkVecN m (substTermVec σ xs))
    (wkTermN m (substTerm σ y))
compositionBodyFormula-subst {m = m} f-rep gs-reps σ xs y
  rewrite graphVecFormulaStructured-subst
            gs-reps
            (extSubN m σ)
            (wkVecN m xs)
            (boundVarVec m)
        | StructuredFunctionRep.graph-subst
            f-rep
            (extSubN m σ)
            (boundVarVec m)
            (wkTermN m y)
        | subst-extSubN-wkVecN m σ xs
        | subst-extSubN-boundVarVec m σ
        | subst-extSubN-wkTermN m σ y = refl

compositionBodyFormulaWith :
  {n m : ℕ} → {f : PRF m} → {gs : Vec (PRF n) m} →
  StructuredFunctionRep f →
  AllPRF StructuredFunctionRep gs →
  Vec Term n →
  Vec Term m →
  Term →
  Formula
compositionBodyFormulaWith f-rep gs-reps xs zs y =
  graphVecFormulaStructured gs-reps xs zs ∧
  StructuredFunctionRep.graphFormula f-rep zs y

compositionBodyFormulaWith-value :
  {n m : ℕ} → {f : PRF m} → {gs : Vec (PRF n) m} →
  (f-rep : StructuredFunctionRep f) →
  (gs-reps : AllPRF StructuredFunctionRep gs) →
  (xs : Vec ℕ n) →
  PA-provable
    (compositionBodyFormulaWith
      f-rep
      gs-reps
      (numeralVec xs)
      (numeralVec (evalPRFs gs xs))
      (numeral (evalPRF (compF f gs) xs)))
compositionBodyFormulaWith-value f-rep gs-reps xs =
  modus-ponens
    (modus-ponens and-introduce
      (graphVecFormulaStructured-value gs-reps xs))
    (StructuredFunctionRep.represents-value f-rep (evalPRFs _ xs))

compositionBodyFormulaWith-unique :
  {n m : ℕ} → {f : PRF m} → {gs : Vec (PRF n) m} →
  (f-rep : StructuredFunctionRep f) →
  (gs-reps : AllPRF StructuredFunctionRep gs) →
  (xs : Vec Term n) →
  (zs ws : Vec Term m) →
  (y z : Term) →
  PA-provable
    (compositionBodyFormulaWith f-rep gs-reps xs zs y ⇒
     (compositionBodyFormulaWith f-rep gs-reps xs ws z ⇒ y ≈ z))
compositionBodyFormulaWith-unique f-rep gs-reps xs zs ws y z =
  modus-ponens
    (modus-ponens
      (modus-ponens
        body-unique-compose
        (graphVecFormulaStructured-eq gs-reps xs zs ws))
      (StructuredFunctionRep.graph-input-congruence f-rep zs ws y))
    (StructuredFunctionRep.represents-unique-terms f-rep ws y z)

compositionBodyFormulaWith-input-congruence :
  {n m : ℕ} → {f : PRF m} → {gs : Vec (PRF n) m} →
  (f-rep : StructuredFunctionRep f) →
  (gs-reps : AllPRF StructuredFunctionRep gs) →
  (xs ys : Vec Term n) →
  (zs : Vec Term m) →
  (y : Term) →
  PA-provable
    (eqVecFormula xs ys ⇒
     (compositionBodyFormulaWith f-rep gs-reps xs zs y ⇒
      compositionBodyFormulaWith f-rep gs-reps ys zs y))
compositionBodyFormulaWith-input-congruence f-rep gs-reps xs ys zs y =
  modus-ponens
    premise-and-left-map
    (graphVecFormulaStructured-input-congruence gs-reps xs ys zs)

compositionGraphFormulaStructured :
  {n m : ℕ} → {f : PRF m} → {gs : Vec (PRF n) m} →
  StructuredFunctionRep f →
  AllPRF StructuredFunctionRep gs →
  Vec Term n →
  Term →
  Formula
compositionGraphFormulaStructured {m = m} f-rep gs-reps xs y =
  existsVecFormulaStructured m
    (compositionBodyFormula
      f-rep
      gs-reps
      (wkVecN m xs)
      (wkTermN m y))

compositionGraphFormulaStructured-subst :
  {n m : ℕ} → {f : PRF m} → {gs : Vec (PRF n) m} →
  (f-rep : StructuredFunctionRep f) →
  (gs-reps : AllPRF StructuredFunctionRep gs) →
  (σ : Sub) →
  (xs : Vec Term n) →
  (y : Term) →
  substFormula σ
    (compositionGraphFormulaStructured f-rep gs-reps xs y)
  ≡
  compositionGraphFormulaStructured
    f-rep
    gs-reps
    (substTermVec σ xs)
    (substTerm σ y)
compositionGraphFormulaStructured-subst {m = m} f-rep gs-reps σ xs y
  rewrite subst-existsVecFormulaStructured
            m
            σ
            (compositionBodyFormula
              f-rep
              gs-reps
              (wkVecN m xs)
              (wkTermN m y))
        | compositionBodyFormula-subst f-rep gs-reps σ xs y = refl

compositionGraphFormulaStructured-subst0-var :
  {n m : ℕ} → {f : PRF m} → {gs : Vec (PRF n) m} →
  (f-rep : StructuredFunctionRep f) →
  (gs-reps : AllPRF StructuredFunctionRep gs) →
  (xs : Vec Term n) →
  (s : Term) →
  subst0 s
    (compositionGraphFormulaStructured f-rep gs-reps (wkVec xs) (var zero))
  ≡
  compositionGraphFormulaStructured f-rep gs-reps xs s
compositionGraphFormulaStructured-subst0-var f-rep gs-reps xs s
  rewrite compositionGraphFormulaStructured-subst
            f-rep
            gs-reps
            (single s)
            (wkVec xs)
            (var zero)
        | substTermVec-single-wkVec s xs = refl

compositionGraphFormulaStructured-subst0-wk :
  {n m : ℕ} → {f : PRF m} → {gs : Vec (PRF n) m} →
  (f-rep : StructuredFunctionRep f) →
  (gs-reps : AllPRF StructuredFunctionRep gs) →
  (xs : Vec Term n) →
  (y s : Term) →
  subst0 s
    (compositionGraphFormulaStructured f-rep gs-reps (wkVec xs) (wkTerm y))
  ≡
  compositionGraphFormulaStructured f-rep gs-reps xs y
compositionGraphFormulaStructured-subst0-wk f-rep gs-reps xs y s
  rewrite compositionGraphFormulaStructured-subst
            f-rep
            gs-reps
            (single s)
            (wkVec xs)
            (wkTerm y)
        | substTermVec-single-wkVec s xs
        | subst0-wkTerm s y = refl

compositionGraphFormulaStructured-value :
  {n m : ℕ} → {f : PRF m} → {gs : Vec (PRF n) m} →
  (f-rep : StructuredFunctionRep f) →
  (gs-reps : AllPRF StructuredFunctionRep gs) →
  (xs : Vec ℕ n) →
  PA-provable
    (compositionGraphFormulaStructured
      f-rep
      gs-reps
      (numeralVec xs)
      (numeral (evalPRF (compF f gs) xs)))
compositionGraphFormulaStructured-value {m = m} f-rep gs-reps xs =
  modus-ponens
    (exists-prefix-introduce-any m)
    (compositionBodyFormulaWith-value f-rep gs-reps xs)

compositionGraphFormulaStructured-unique :
  {n m : ℕ} → {f : PRF m} → {gs : Vec (PRF n) m} →
  (f-rep : StructuredFunctionRep f) →
  (gs-reps : AllPRF StructuredFunctionRep gs) →
  (xs : Vec Term n) →
  (y z : Term) →
  PA-provable
    (compositionGraphFormulaStructured f-rep gs-reps xs y ⇒
     (compositionGraphFormulaStructured f-rep gs-reps xs z ⇒
      y ≈ z))
compositionGraphFormulaStructured-unique {m = m} f-rep gs-reps xs y z =
  modus-ponens
    (exists-prefix-binary-lift m)
    (compositionBodyFormulaWith-unique
      f-rep
      gs-reps
      (wkVecN m xs)
      (boundVarVec m)
      (boundVarVec m)
      (wkTermN m y)
      (wkTermN m z))

compositionGraphFormulaStructured-input-congruence :
  {n m : ℕ} → {f : PRF m} → {gs : Vec (PRF n) m} →
  (f-rep : StructuredFunctionRep f) →
  (gs-reps : AllPRF StructuredFunctionRep gs) →
  (xs ys : Vec Term n) →
  (y : Term) →
  PA-provable
    (eqVecFormula xs ys ⇒
     (compositionGraphFormulaStructured f-rep gs-reps xs y ⇒
      compositionGraphFormulaStructured f-rep gs-reps ys y))
compositionGraphFormulaStructured-input-congruence {m = m} f-rep gs-reps xs ys y =
  modus-ponens
    (exists-prefix-premise-map-any m)
    (modus-ponens
      premise-change-any
      (compositionBodyFormulaWith-input-congruence
        f-rep
        gs-reps
        (wkVecN m xs)
        (wkVecN m ys)
        (boundVarVec m)
        (wkTermN m y)))

record StructuredCompositionExistsLemmas
  {n m : ℕ}
  {f : PRF m}
  {gs : Vec (PRF n) m}
  (f-rep : StructuredFunctionRep f)
  (gs-reps : AllPRF StructuredFunctionRep gs) : Set₁ where
  field
    composition-value :
      (xs : Vec ℕ n) →
      PA-provable
        (compositionGraphFormulaStructured
          f-rep
          gs-reps
          (numeralVec xs)
          (numeral (evalPRF (compF f gs) xs)))

    composition-unique-terms :
      (xs : Vec Term n) → (y z : Term) →
      PA-provable
        (compositionGraphFormulaStructured f-rep gs-reps xs y ⇒
         (compositionGraphFormulaStructured f-rep gs-reps xs z ⇒
          y ≈ z))

    composition-input-congruence :
      (xs ys : Vec Term n) → (y : Term) →
      PA-provable
        (eqVecFormula xs ys ⇒
         (compositionGraphFormulaStructured f-rep gs-reps xs y ⇒
          compositionGraphFormulaStructured f-rep gs-reps ys y))

structured-composition-exists-lemmas :
  {n m : ℕ} → {f : PRF m} → {gs : Vec (PRF n) m} →
  (f-rep : StructuredFunctionRep f) →
  (gs-reps : AllPRF StructuredFunctionRep gs) →
  StructuredCompositionExistsLemmas f-rep gs-reps
structured-composition-exists-lemmas f-rep gs-reps = record
  { composition-value =
      compositionGraphFormulaStructured-value f-rep gs-reps
  ; composition-unique-terms =
      compositionGraphFormulaStructured-unique f-rep gs-reps
  ; composition-input-congruence =
      compositionGraphFormulaStructured-input-congruence f-rep gs-reps
  }

structured-composition-closes-from-lemmas :
  {n m : ℕ} →
  (f : PRF m) →
  (gs : Vec (PRF n) m) →
  (f-rep : StructuredFunctionRep f) →
  (gs-reps : AllPRF StructuredFunctionRep gs) →
  StructuredCompositionExistsLemmas f-rep gs-reps →
  StructuredFunctionRep (compF f gs)
structured-composition-closes-from-lemmas f gs f-rep gs-reps lemmas =
  record
    { graphFormula =
        compositionGraphFormulaStructured f-rep gs-reps
    ; represents-value =
        StructuredCompositionExistsLemmas.composition-value lemmas
    ; represents-unique-terms =
        StructuredCompositionExistsLemmas.composition-unique-terms lemmas
    ; represents-exists = λ xs →
        numeral (evalPRF (compF f gs) xs) ,Σ
        StructuredCompositionExistsLemmas.composition-value lemmas xs
    ; graph-input-congruence =
        StructuredCompositionExistsLemmas.composition-input-congruence lemmas
    ; graph-subst =
        compositionGraphFormulaStructured-subst f-rep gs-reps
    ; graph-subst0-var =
        compositionGraphFormulaStructured-subst0-var f-rep gs-reps
    ; graph-subst0-wk =
        compositionGraphFormulaStructured-subst0-wk f-rep gs-reps
    }

record StructuredCompositionRepresentabilityTarget : Set₁ where
  field
    structured-composition-closes :
      {n m : ℕ} →
      (f : PRF m) →
      (gs : Vec (PRF n) m) →
      StructuredFunctionRep f →
      AllPRF StructuredFunctionRep gs →
      StructuredFunctionRep (compF f gs)

structured-composition-closes :
  {n m : ℕ} →
  (f : PRF m) →
  (gs : Vec (PRF n) m) →
  StructuredFunctionRep f →
  AllPRF StructuredFunctionRep gs →
  StructuredFunctionRep (compF f gs)
structured-composition-closes f gs f-rep gs-reps =
  structured-composition-closes-from-lemmas
    f
    gs
    f-rep
    gs-reps
    (structured-composition-exists-lemmas f-rep gs-reps)

structured-composition-target : StructuredCompositionRepresentabilityTarget
structured-composition-target = record
  { structured-composition-closes = structured-composition-closes
  }
