# Proof Guide

This guide explains the proof architecture of `godel-agda-full`. It is written
for readers who already know enough Agda to follow records, modules, and proof
terms, and who want to understand how the incompleteness argument is assembled.

The project formalizes the main proof skeleton of Godel's first
incompleteness theorem. It does not yet contain full PA-level proofs of the
standard representability theorem or the diagonal lemma. Those deep ingredients
are exposed as record fields, so the core theorem can be checked independently
from the large arithmetization development.

## Current Status

The following parts are concrete Agda definitions or proofs:

- first-order arithmetic syntax, including terms, formulas, de Bruijn
  variables, renaming, substitution, and numerals;
- Godel coding functions for terms and formulas;
- a checked structural coding layer with decoders and round-trip lemmas;
- an object-language proof predicate shape, `ProofOf p A`;
- a Hilbert-style derivability relation;
- a small PA axiom schema and a concrete coding of PA proof trees;
- an abstract arithmetized-theory interface;
- the split between a full `DiagonalLemma` and the weaker
  `NoProofsFixedPoint` actually needed for the theorem;
- the conversion from a fixed point of `noProofsTemplate` to a
  `GödelSentence`;
- the original Godel incompleteness argument using consistency and
  omega-consistency;
- a Rosser-style abstract theorem.

The following parts are intentionally left as assumptions/interfaces:

- `PARepresentability`: PA represents the proof-code predicate and its
  negation for concrete numerals.
- `DiagonalLemma`: every one-variable formula has a fixed point in the theory.

Those two interfaces are the main remaining mathematical work if the goal is a
fully expanded PA formalization.

## Suggested Reading Order

1. `Godel.Syntax`

   Start here to understand the object language. `Term` and `Formula` define
   the syntax being encoded and reasoned about. The important infrastructure is
   `subst0`, `numeral`, and the convention that `Rel r ts` represents an
   arbitrary relation symbol applied to a list of terms.

2. `Godel.Coding`

   This module assigns natural-number codes to terms and formulas. The key
   bridge is:

   ```agda
   ⌜_⌝ᶠ : Formula → Term
   ⌜ A ⌝ᶠ = numeral (codeFormula A)
   ```

   It turns the meta-level code of a formula into an object-language numeral.
   The core template is:

   ```agda
   noProofsTemplate : Formula
   noProofsTemplate = ∀ᶠ (¬ᶠ (ProofRel (var zero) (var (suc zero))))
   ```

   Read this as a one-variable formula `x ↦ ∀p. ¬ Proof(p, x)`.

3. `Godel.ArithmetizedTheory`

   This record states what the theorem needs from a theory `T`. It includes
   derivability, modus ponens, universal elimination, proof-code soundness and
   completeness, representability of proof and non-proof facts, and one
   classical object-logic step.

   The important point is that `ArithmetizedTheory` is not PA itself. It is the
   abstract interface consumed by the incompleteness proof.

4. `Godel.CanonicalCoding`

   This module adds a structural canonical code type, a separate numeric
   base-4 digit-stream encoding for those codes, fuelled decoders, and
   round-trip lemmas such as:

   ```agda
   decodeFormula-roundTrip :
     (fuel : ℕ) → (A : Formula) →
     decodeFormula (suc fuel) (canonicalCodeFormula A) ≡ just A

   decodeCode-roundTrip :
     (c : Code) → decodeCode (suc (codeSize c)) (encodeCode c) ≡ just c

   decodeNatFormulaWithFuel-roundTrip :
     (A : Formula) →
     decodeNatFormulaWithFuel
       (suc (codeSize (canonicalCodeFormula A)))
       (canonicalNatFormula A)
       ≡ just A

   decodeNatFormula-roundTrip :
     (A : Formula) →
     decodeNatFormula (canonicalNatFormula A) ≡ just A
   ```

   It also defines `diagFormula`, `diagCode`, `DiagCode`, and `DiagRel` as early
   staging pieces for future diagonal/substitution representability work. This
   does not replace the numeric `codeFormula` used by the current theorem. The
   fuelled round-trip statements are the checked core; the unfuelled
   `decodeNatTerm` and `decodeNatFormula` wrappers now also have canonical
   round-trip proofs.

5. `Godel.DecidableCoding`

   This module defines small Boolean equality checkers for natural numbers,
   terms, term lists, and formulas:

   ```agda
   termEq : Term → Term → Bool
   formulaEq : Formula → Formula → Bool
   ```

   The key facts are reflexivity lemmas such as `termEq-refl` and
   `formulaEq-refl`, plus soundness lemmas such as `termEq-sound` and
   `formulaEq-sound`.  Reflexivity gives checked graph completeness; soundness
   lets a successful checker run recover propositional equality of decoded
   syntax.

6. `Godel.DiagonalCoding`

   This module turns the canonical numeric coding into explicit meta-level graph
   predicates:

   ```agda
   Subst0NatCode : ℕ → ℕ → ℕ → Set
   DiagNatCode   : ℕ → ℕ → Set
   ```

   It proves that the real syntax operations land in these graphs:

   ```agda
   subst0NatCode-complete :
     (A : Formula) → (t : Term) →
     Subst0NatCode
       (canonicalNatFormula A)
       (canonicalNatTerm t)
       (canonicalNatFormula (subst0 t A))

   diagNatCode-complete :
     (A : Formula) →
     DiagNatCode
       (canonicalNatFormula A)
       (canonicalNatFormula (diagFormula A))
   ```

   It also introduces `Subst0Rel` as an object-language relation wrapper for a
   future representability theorem. This still does not prove that PA represents
   substitution or diagonalization.

7. `Godel.ComputableGraphs`

   This module turns the graph specifications into Boolean checkers:

   ```agda
   subst0NatCode? : ℕ → ℕ → ℕ → Bool
   diagNatCode?   : ℕ → ℕ → Bool
   ```

   Their Set wrappers, `CheckedSubst0NatCode` and `CheckedDiagNatCode`, are the
   more concrete targets for a future PA representability proof.  The module
   proves that genuine syntax operations are accepted by these checkers, that
   successful checker runs decode to the intended syntax operation, and that
   checked graph facts imply the older Σ-style `Subst0NatCode` / `DiagNatCode`
   specifications.

8. `Godel.RepresentabilityTargets`

   This module packages the next target as records rather than PA proofs:

   ```agda
   Represents₂ T R F
   Represents₃ T R F

   DiagRepresentability T
   Subst0Representability T
   CheckedDiagRepresentability T
   CheckedSubst0Representability T
   ```

   The aggregate `PrePARepresentabilityData T` means that the substitution and
   diagonal graph representability targets have both been supplied for a theory
   `T`.  The checked aggregate `CheckedPrePARepresentabilityData T` is the
   recommended next PA-facing target because it is tied to executable Boolean
   graph checkers.

9. `Godel.NoProofsDiagonalization`

   This module names the noProofs-specific diagonal helper:

   ```text
   ψ(x) := noProofsTemplate(x) := ∀p. ¬ Proof(p,x)
   ```

   Its candidate sentence is `diagFormula ψ`.  The module proves this candidate
   lands in the canonical diagonal graph:

   ```agda
   noProofsCandidate-diagNatCode :
     DiagNatCode
       (canonicalNatFormula noProofsDiagonalTemplate)
       (canonicalNatFormula noProofsFixedPointCandidate)
   ```

   This is still a candidate-level scaffold; proving it is a real fixed point
   requires object-language use of `DiagRepresentability`.  A richer helper
   formula that mentions `DiagRel` directly is intentionally left to that later
   PA-facing stage, because expanding its old unary numeral code would be much
   too large for routine type checking.

10. `Godel.Diagonal`

   `FixedPoint T φ` packages a sentence `θ` together with proofs that `T`
   proves both directions of:

   ```text
   θ <-> φ(⌜θ⌝)
   ```

   `DiagonalLemma T` says that such a fixed point exists for every formula
   `φ`. Applying it to `noProofsTemplate` gives the usual self-referential
   Godel sentence shape.

   The weaker record `NoProofsFixedPoint T` keeps only the fixed point needed
   by the incompleteness proof:

   ```agda
   fixedPoint-noProofs : FixedPoint T noProofsTemplate
   ```

   A full `DiagonalLemma T` can be adapted into this weaker interface.

11. `Godel.Original`

   This is the main abstract theorem. Given an `ArithmetizedTheory T` and a
   `GödelSentence T`, it proves:

   ```agda
   first-incompleteness : Consistent T → OmegaConsistent T → Undecidable T G
   ```

   The proof has two halves:

   - `not-provable-G`: if `G` were provable, its proof would have a code `n`;
     representability would prove `ProofOf (numeral n) G`, while `G` itself
     yields that no such proof exists.
   - `not-provable-notG`: if `¬G` were provable, the theory would prove that
     some proof of `G` exists, but consistency gives a proof of non-proofhood
     for every numeral, contradicting omega-consistency.

12. `Godel.PAFirstIncompleteness`

   This module specializes the abstract theorem to PA, conditional on the two
   remaining PA-specific ingredients:

   ```agda
   record PAIncompletenessData : Set₁ where
     field
       repr : PARepresentability
       diagonal-lemma-PA : DiagonalLemma (PA-as-theory repr)
   ```

   Once those fields are supplied, `PA-first-incompleteness` follows by
   reusing the theorem from `Godel.Original`.

   The lighter record `PANoProofsIncompletenessData` accepts only a
   `NoProofsFixedPoint` instead of a full `DiagonalLemma`, and feeds the same
   abstract theorem through `PA-first-incompleteness-from-noProofs-fixedPoint`.

13. `Godel.PAObjectLogic`, `Godel.PAObjectLogicProofs`,
    `Godel.PAClosedArithmetic`, and `Godel.PAClosedArithmeticProofs`

   These modules name the PA-internal proof infrastructure needed before a real
   checked graph representability instance can be attempted.  `PAObjectLogic`
   packages equality reasoning and function congruence obligations such as
   reflexivity, symmetry, transitivity, successor congruence, addition
   congruence, and multiplication congruence.

   `Godel.ProofSystem` now includes equality-logic proof rules for those
   obligations, and `Godel.PAObjectLogicProofs` packages them as:

   ```agda
   paObjectLogic : PAObjectLogic
   ```

   `PAClosedArithmetic` packages closed numeral computations:

   ```agda
   pa-add-computes :
     (m n : ℕ) →
     PA-provable ((numeral m +ᵗ numeral n) ≈ numeral (m + n))

   pa-mul-computes :
     (m n : ℕ) →
     PA-provable ((numeral m *ᵗ numeral n) ≈ numeral (m * n))
   ```

   `Godel.PAClosedArithmeticProofs` uses the PA axioms together with a supplied
   `PAObjectLogic` record to build closed arithmetic, and
   `Godel.PAObjectLogicProofs` instantiates this path:

   ```agda
   paClosedArithmetic-fromObjectLogic :
     PAObjectLogic → PAClosedArithmetic

   paProofInfrastructure :
     PAProofInfrastructure
   ```

   So the PA object-logic layer is no longer just an interface; it has a
   concrete proof-system implementation.

14. `Godel.PARepresentabilityEntry`

   This is the first PA-facing entry layer for the checked graph work.  It
   defines proof obligations directly in terms of `PA-provable`:

   ```agda
   PACheckedGraphRepresentability : Set₁
   ```

   The adapter `pa-checked-graph-representability-as-prePA` turns those
   PA-specific obligations into the generic `CheckedPrePARepresentabilityData`
   interface for `PA-as-theory repr`.  The record
   `PANoProofsFixedPointEntryData` marks the next boundary: PA proof
   infrastructure, PA checked graph representability, and a noProofs fixed-point
   construction target.

15. `Godel.PACheckedGraphTargets`

   This module decomposes the PA checked graph obligation into smaller
   representability targets.  Instead of treating
   `PACheckedGraphRepresentability` as a black box, it introduces PA-facing
   helper relations for decoder graphs and formula equality:

   ```agda
   PADecodeRepresentability
   PAFormulaEqRepresentability
   PASubst0RepresentabilityTarget
   PADiagRepresentabilityTarget
   ```

   The aggregate `PACheckedGraphProofData` collects those targets together
   with `PAProofInfrastructure`.  The adapter
   `checkedGraphProofData-to-PARepresentability` shows that these smaller
   obligations are sufficient to assemble the original
   `PACheckedGraphRepresentability` interface.  The module still does not prove
   that PA satisfies any of the targets; it makes the next PA proof obligations
   explicit.

16. `Godel.PrimitiveRecursive`, `Godel.PRRepresentability`,
    `Godel.PRBooleanHelpers`, `Godel.PRBoundedSearch`,
    `Godel.PRDigitCoding`, `Godel.PRNatListDecoder`,
    `Godel.PRSequenceCoding`,
    `Godel.PRHistoryCoding`, `Godel.PRHistoryFormula`,
    `Godel.PRConcreteSequenceCoding`, `Godel.PRConcreteHistoryValid`,
    `Godel.CanonicalCodePR`,
    `Godel.SyntaxCodingPR`,
    `Godel.PACheckedGraphPRTargets`, and `Godel.PACheckedGraphPRProofs`

   These modules start the non-staging primitive-recursive route.  The project
   now has arity-indexed primitive recursive functions and relations:

   ```agda
   PRF   : ℕ → Set
   PRRel : ℕ → Set
   ```

   and an evaluator `evalPRF`.  The `PRF` data type now has only the minimal
   constructor basis `zeroF`, `sucF`, `projF`, `compF`, and `precF`; the
   evaluator has no special cases for syntax checkers.
   `Godel.PRRepresentability` defines what it means for PA to represent a PR
   function or relation, strengthens function
   representations with uniqueness and meta-level existence fields, and exposes
   `composition-closes`, `primitive-recursion-closes`, `prf-represented`, and
   `prrel-represented` through a structure-recursive entry point.  Composition
   graphs are no longer represented by directly evaluating `compF`; they are
   built from the graph of the outer function plus the graphs of the intermediate
   functions.  The new PA-facing primitive-recursion history entry is
   `Godel.PRHistoryFormula.historyResultFormula`, whose body explicitly names
   an existential history code together with `seqLength`, `history-valid`, and
   `seqNth` graph constraints.

   `Godel.PRBooleanHelpers` names basic PR helper functions such as addition,
   multiplication, predecessor, truncated subtraction, zero-test, comparison,
   Boolean negation, conjunction, disjunction, and conditionals.
   `Godel.PRArithmeticSemantics` proves their small-step meta semantics.
   `Godel.PRBoundedSearch`, `Godel.PRDigitCoding`,
   `Godel.PRDigitSemantics`, `Godel.PRNatListDecoder`,
   `Godel.PRNatListDigitStream`, and
   `Godel.PRNatListDecoderSemantics` start the concrete numeric decoder layer:
   constants, base-4 digit destructors, minimal-basis PRF candidates for
   `seqLengthF` and `seqNthF`, and evalPRF-to-meta correctness for those
   candidates.  The finite digit stream layer proves the code/digit
   correspondence, complete nonzero digit counting, and the bounded active
   scanner list induction used by `seqNth`.
   `Godel.PRHistoryCoding` remains meta-level: it defines `evalHistory`,
   `historyCode`, `historyLength`, and `historyNthDefault`.  The history code is
   now a canonical nat-list code with a fuelled round-trip decoder, replacing
   the earlier non-injective placeholder.
   `Godel.PRSequenceCoding` records the finite-sequence coding substrate still
   needed for a fully uniform primitive-recursion representability theorem,
   including correctness and substitution-stability obligations for the history
   formulas.
   `Godel.PRHistoryFormula` provides a history-backed closure bridge.  That
   bridge carries the new PA-history witness formula, while uniqueness is still
   supported by the evaluated graph conjunct until the sequence-coded history
   uniqueness proof is internalized.
   `Godel.PRVectorHelpers`, `Godel.PRHistoryValidCheckers`,
   `Godel.PRHistoryValidSemantics`, and `Godel.PRConcreteHistoryValid` continue
   that concrete history route.  The sequence candidates for length and nth are
   real minimal-basis PRFs with semantic mirror lemmas; both are proved correct
   for `historyCode`, so `Godel.PRConcreteSequenceCoding` exports an
   unconditional `concretePRSequenceCoding : PRSequenceCoding`.  The
   `history-validF` checker is now also a minimal-basis bounded-step checker:
   its semantic mirror proves agreement with `historyValidNat`, and real
   `evalHistory` values are accepted.  The remaining infrastructure work is the
   history-body substitution-stability obligation and the sequence-coded history
   uniqueness proof.
   `Godel.CanonicalCodePR` gives the canonical code tree/list helper entry
   points used by this route.

   `Godel.PACheckedGraphPRTargets` gives the final checked graph target shape
   for this route.  Instead of using bare uninterpreted `Rel` symbols, it is
   parameterized by concrete formula builders such as `DecodeTermFormula`,
   `FormulaEqFormula`, `Subst0Formula`, and `DiagFormula`.  The intended source
   of those formulas is the full PR representability theorem.

   `Godel.SyntaxCodingPR` states the precise bridge still needed between the
   executable Agda checkers and primitive-recursive relations.  The older
   `SyntaxCodingPRDerived` / `SyntaxCodingPRConcrete` files are kept in the
   repository as scaffolding, but they are no longer imported by
   `Godel.Everything`, because the old concrete checker route depended on
   special evaluator behavior.  Rebuilding that route from real numeric PR
   decoders is the next stage.

## Main Proof Path

The shortest path through the project is:

```text
noProofsTemplate
  -> canonical numeric coding
  -> decode round-trip
  -> checked Subst0NatCode / DiagNatCode Boolean graph targets
  -> checked Represents₂ / Represents₃ interfaces
  -> noProofsFixedPointCandidate
  -> PA-facing PACheckedGraphRepresentability obligations
  -> PA object logic / equality reasoning from proof-system rules
  -> PA closed numeral arithmetic from PA axioms
  -> decomposition into decode / formulaEq / subst0 / diag PA targets
  -> future minimal-basis SyntaxCodingPR checker instance
  -> SyntaxCodingPRInstances / PR checked graph packaging
  -> PA representations of those PR relations
  -> primitive-recursive formulas for decode / formulaEq / subst0 / diag
  -> PR checked graph representability target
  -> future bridge to CheckedPrePARepresentabilityData for PA
  -> PA noProofs fixed-point construction target
  -> DiagonalLemma.fixedPoint or NoProofsFixedPoint.fixedPoint-noProofs
  -> FixedPoint T noProofsTemplate
  -> fromFixedPoint
  -> GödelSentence T
  -> Original.Theorem.first-incompleteness
  -> Undecidable T G
```

The role of `fromFixedPoint` is small but important. A fixed point of
`noProofsTemplate` gives a sentence `θ` such that:

```text
θ <-> noProofsTemplate(⌜θ⌝)
```

The lemma `noProofsTemplate-subst0` identifies the substituted template with
`noProofs θ`. Therefore the fixed point becomes a `GödelSentence` with:

```agda
g→noProofs     : Provable (G ⇒ noProofs G)
notG→someProof : Provable ((¬ᶠ G) ⇒ someProof G)
```

These are exactly the two object-theory facts used by `Godel.Original`.

## Formalization Boundaries

The project deliberately separates the small, reusable proof skeleton from the
large arithmetization work.

`PARepresentability` is the promise that the chosen object-language predicate
`ProofRel` correctly represents the meta-level proof-code relation
`ProofCodePA`. Proving this for real PA requires a substantial development of
primitive recursive functions, coding, bounded reasoning, and PA proofs about
the proof checker.

`DiagonalLemma` is the promise that every one-variable formula has a fixed
point. Proving it inside PA requires formalizing enough syntax and substitution
coding for PA to reason about the diagonal/substitution function.

`NoProofsFixedPoint` is a deliberately weaker target: it asks only for the
fixed point of `noProofsTemplate`. The canonical and diagonal coding modules
make the next representability targets explicit, but they do not yet prove that
PA represents the diagonal/substitution graph. The checked graph layer narrows
the target further: PA should represent the Boolean checkers
`subst0NatCode?` and `diagNatCode?`, packaged as
`CheckedPrePARepresentabilityData`.  `Godel.PARepresentabilityEntry` moves this
from a generic theory target to explicit `PA-provable` obligations via
`PACheckedGraphRepresentability`.  `PAObjectLogic` names the PA-internal
equality reasoning needed to start such proofs, and `PAObjectLogicProofs`
constructs it from equality rules in the proof system.  Given that object
logic, `PAClosedArithmeticProofs` derives closed numeral arithmetic from the PA
axioms.

The project does not use staging graph axiom schemas as a substitute for
representability.  The older `DiagRel` / `Subst0Rel` wrappers remain useful as
scaffolding, but the non-staging route is now separated in
`PACheckedGraphPRTargets`: final PA graph proofs are built from concrete
arithmetical formulas generated by PR representability, not from uninterpreted
relation symbols.  The current PR layer keeps the `PRF` constructor set and
evaluator at the minimal basis and provides a structure-recursive
representability entry point for PR functions and relations.  The closure
formula layer now separates composition graphs from raw evaluator equations and
adds a PA-facing primitive-recursion history formula with an existential history
code, sequence-length graph, history-valid checker graph, and final `nth`
graph.  The current history-backed closure is intentionally a bridge: it
includes that PA-history formula but still uses the evaluated graph conjunct for
uniqueness.  The next proof step is to replace that remaining support with a
sequence-coded history uniqueness argument, starting from the now-complete
`seqLengthF` / `seqNthF` concrete sequence coding and the concrete
`history-validF` bounded-step checker.

The remaining large tasks are to rebuild the syntax checker PR instance without
evaluator special cases, connect the PR checked graph result to a noProofs fixed
point, and eventually discharge the proof predicate fields in
`PARepresentability`.

Because these are record fields rather than postulates, the checked theorem is
conditional and explicit: any future implementation must provide exactly these
pieces before obtaining the PA-level theorem.

## Checking

The whole project is checked through:

```bash
agda -i . Godel/Everything.agda
```

The newer no-proofs-specific entrypoints are additive; the full diagonal-lemma
entrypoints remain available.
