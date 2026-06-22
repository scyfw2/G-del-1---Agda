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
   function or relation and keeps the older evaluator-backed theorem path
   typechecking as a legacy/bootstrap bridge.  The final public boundary for the
   second step is now `Godel.PRRepresentabilityFinal`, which re-exports the core
   records and exposes the structured `prf-represented` / `prrel-represented`
   theorem path.

   `Godel.PRGraphSubstitution` and `Godel.PRStructuredRepresentability` start
   the binder-safe replacement route for this layer.  The new structured
   interface adds term-level uniqueness, graph-input congruence, general graph
   substitution, output-variable substitution stability, and a `graph-subst0-wk`
   field.  The zero, successor, and projection functions already have base
   instances for these fields, and the module now includes helper definitions
   for nested existential graph formulas.  Composition also has body-level
   value/uniqueness/input-congruence lemmas, unconditional graph-substitution
   lemmas, nested-exists lifting support, and the completed
   `structured-composition-closes` theorem.  Primitive recursion now has a
   parallel structured route through `Godel.PRStructuredHistoryFormula` and
   `Godel.PRHistoryUniqueness`.

   `Godel.PRBooleanHelpers` names basic PR helper functions such as addition,
   multiplication, predecessor, truncated subtraction, zero-test, comparison,
   Boolean negation, conjunction, disjunction, and conditionals.
   `Godel.PRArithmeticSemantics` proves their small-step meta semantics.
   `Godel.PRBoundedSearch`, `Godel.PRDigitCoding`,
   `Godel.PRDigitSemantics`, `Godel.PRNatListDecoder`,
   `Godel.PRNatListDigitStream`, and
   `Godel.PRNatListDecoderSemantics` start the concrete numeric decoder layer:
   constants, base-4 digit destructors, the base-4 `appendDigitF`
   constructor helper, minimal-basis PRF candidates for `seqLengthF` and
   `seqNthF`, and evalPRF-to-meta correctness for those candidates.  The
   finite digit stream layer proves the code/digit
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
   `Godel.PRHistoryFormula` provides the older history-backed closure bridge.
   That bridge carries the PA-history witness formula, while uniqueness is still
   supported by the evaluated graph conjunct for compatibility.
   `Godel.PRStructuredHistoryFormula` and `Godel.PRHistoryUniqueness` add the
   structured primitive-recursion route: the closure graph is a
   `structuredHistoryResultFormula`, the history-body substitution lemma is
   derived from stable formula substitution, and
   `structured-primitive-recursion-closes` no longer includes an
   `evaluatedGraphFormula` conjunct.  `Godel.PRStructuredTheorem` is the
   recommended theorem entry point: it combines the structured base cases,
   structured composition, and structured primitive recursion into
   `prf-represented` / `prrel-represented`.
   `Godel.PRRepresentabilityFinal` re-exports that theorem path together with
   the shared `PARepresentsFunction` / `PARepresentsRelation` records, and
   should be used by high-level PA checked graph modules.
   `Godel.PRVectorHelpers`, `Godel.PRHistoryValidCheckers`,
   `Godel.PRHistoryValidSemantics`, and `Godel.PRConcreteHistoryValid` continue
   that concrete history route.  The sequence candidates for length and nth are
   real minimal-basis PRFs with semantic mirror lemmas; both are proved correct
   for `historyCode`, so `Godel.PRConcreteSequenceCoding` exports an
   unconditional `concretePRSequenceCoding : PRSequenceCoding`.  The
   `history-validF` checker is now also a minimal-basis bounded-step checker:
   its semantic mirror proves agreement with `historyValidNat`, and real
   `evalHistory` values are accepted.  The structured primitive-recursion
   closure now has a dedicated theorem, and the history formula layer no longer
   uses the earlier `stableTrueFormula` shell.
   `Godel.CanonicalCodePR` gives the canonical code tree/list helper entry
   points used by this route.  The atom/node head-tag checkers are now real
   base-4 digit PRFs with head soundness and completeness lemmas.  The atom
   payload and node tag destructors are now prefix-nat decoder PRFs with
   eval-to-meta and canonical correctness lemmas.  The node-children destructor
   is now a prefix-nat rest extractor with canonical correctness.  The code-list
   nil/cons tag checkers are also real digit PRFs.  The same module now also has
   the first builder-side PRFs: `encodeNatWithRestF`, `atomCodeWithRestF`,
   `atomCodeF`, `nodeCodeWithRestF`, `numeralTermCodeWithRestF`, and closed
   numeral equality/inequality formula-code builders, with correctness against
   the canonical numeric encoding and PA representability through the final PR
   theorem.
   code-list head/tail/length/nth remain the next parsing-style proof-checker
   components.  The new
   `Godel.PRFunctionGraph` bridge turns any PRF destructor into a PR relation
   for its function graph, so these parser functions already have stable
   relation entry points once their PRF definitions are replaced.
   `Godel.CanonicalCodeParserTargets` fixes the numeric specifications for
   those parser components: code-with-rest decoding, skip-code parsing, list
   head/tail, list length, and list nth.  Future PRFs for `codeListHeadF`,
   `codeListTailF`, `codeListLengthF`, and `codeListNthF` should prove
   soundness/completeness against these targets.  The same module now packages
   code-with-rest, skip-code, and list parser obligations as
   `CanonicalCodeParserPR` and provides a `PRRepresentabilityFinal` adapter, so
   once the parser relations are implemented as PR relations, PA formulas for
   them are obtained through the final structured theorem.
   `Godel.CanonicalCodeParserSemantics` adds the executable meta-level mirror
   for those parser targets.  It defines Maybe-valued code-with-rest,
   skip-code, and list head/tail/length/nth parsers using `decodeCodeWithRest` and
   `decodeCodeListWithRest`, proves canonical completeness, and proves that
   successful parser results imply the corresponding target relation.  This is
   the semantic baseline for the later minimal-basis PRF parser implementation.
   `Godel.CanonicalCodeListLengthCheck` now packages the length branch of that
   baseline into a numeric checker.  It proves completeness, soundness, and
   nonzero-sound for `codeListLengthCheck`, and gives an adapter saying that
   any future PRF whose evaluator agrees with this checker immediately supplies
   `CodeListLengthNonzeroSound`.  This does not yet implement the minimal-basis
   `code-list-length-pr`; it makes the remaining obligation exactly the PRF
   evaluator-correctness theorem.
   `Godel.CanonicalCodeListLengthScanner` then narrows that evaluator target:
   it defines a scanner that skips encoded nat/code payloads and computes only
   the code-list length, proves agreement with `decodeCodeWithRest` /
   `decodeCodeListWithRest`, and derives `codeListLengthScannerCheck =
   codeListLengthCheck`.  The concrete minimal-basis PRF can now target this
   scanner instead of reconstructing `List Code`.  Its
   `CodeListLengthScannerPRCandidate` adapter makes the remaining theorem
   precise: prove a PRF evaluator equals `codeListLengthScannerCheck`.
   The Lean shadow module `LeanShadow.CodeListLengthStackMachineMini` now tests
   the intended next implementation shape: an encoded control stack with one
   transition per base-4 digit.  This is not a replacement proof for Agda's
   `code-list-length-pr`; it is a small executable guide for the PRF state
   machine that should be proved equal to the Agda scanner checker.  It now
   proves canonical completeness for encoded code lists: running the stack
   machine over `encodeCodeListWithRest codes []` returns `codes.length`.
   `Godel.CanonicalCodeListLengthStackMachine` ports that induction back to
   Agda at the explicit digit-stream level, giving the structure for the later
   numeric-state proof.  `Godel.CanonicalCodeListLengthNumericState` then
   ports the numeric-state bridge itself: encoded input rest, base-5 encoded
   stack, valid transition lemmas for root/nested/code/nat frames, and the
   prefix-length fuel induction over those valid transitions.  Running exactly
   the encoded nat/code/list prefix length leaves the suffix untouched.  The
   Lean shadow layer now also isolates the next evaluator target:
   `stateStepF` should correspond to a stable semantic step, `stepNumStable`,
   which agrees with the valid transitions but keeps the completed
   `(rest=0, stack=0, ok=true)` state fixed.  The Lean prototype now splits
   this target into branch-wise theorems for root/nested/code/nat, failure, and
   done states.  Agda now ports the effective branch bridge in
   `Godel.CanonicalCodeListLengthStateStepBranches`: the PRF evaluator for
   root/nested/code/nat valid branches is proved to produce the corresponding
   numeric stable transition.  Lean now also proves the next fuel layer:
   `runStateStepEvalFuel` consumes a canonical code-list prefix and then remains
   stable for arbitrary extra fuel after the completed state is reached.
   `LeanShadow.CodeListLengthNumericEvalMini` now proves the canonical bound
   `prefix length <= suc encoded-input`: the route is a `codeSize` /
   `codeListSize` bridge, first bounding digit length by syntax size and then
   showing the closed numeric code pays for `2 * codeListSize`.  This gives
   fixed-fuel `suc input` canonical completeness on the Lean side.
   `Godel.CanonicalCodeListLengthStatePRCompleteness` currently has the matching
   conditional Agda bridge; the next Agda task is to port the size-bound proof,
   then move on to arbitrary-input soundness.
   `Godel.CanonicalCodeListLengthStatePR` is the Agda PRF-side version of that
   guide: it defines `lengthScannerF : PRF 2`, with state encoded as the
   canonical nat-list `[rest, stack, len, ok]` and a base-5 control stack.  It
   already proves the state constructor/projection round-trip lemmas, plus
   evaluator correctness for `ifBoolF/ifEqF`, `mod5F/div5F`, `pushFrameF`, and
   the derived state fields.  `Godel.CanonicalCodeListLengthStateFuel` fixes the
   Agda runner and additivity lemma for that fuel induction.  The split modules
   `Godel.CanonicalCodeListLengthStateFuelNat`,
   `Godel.CanonicalCodeListLengthStateFuelCode`, and
   `Godel.CanonicalCodeListLengthStateFuelCodeList` prove the nat/code/list
   prefix induction on the Agda side: running `stateStepF` for exactly the
   current canonical prefix length leaves the suffix untouched.  The remaining
   theorem is the final equation from `lengthScannerF` to
   `codeListLengthScannerCheck`; once that is available, the existing candidate
   adapters close the code-list-length parser branch.  The failure-side branch
   facts needed for that theorem have now also been ported to Agda:
   `Godel.CanonicalCodeListLengthStateStepBranches` proves invalid
   root/nested/code/nat digits enter the failed state using selector-level
   lemmas, and `Godel.CanonicalCodeListLengthStateFuelFailure` proves failed
   and done states are fuel-stable while empty-stack/nonzero-rest states fail.
   The remaining task is to combine the canonical prefix theorem and these
   failure-side facts into the final all-input scanner evaluator equation.
   `Godel.CanonicalCodeNodeTargets` and `Godel.CanonicalCodeNodeSemantics`
   isolate the outer proof-tree branch parser: `NodeCodeNat input tag
   children-code` means that `input` is a canonical node with the given rule tag
   and children-list code.  The executable mirror uses `decodeCode`, accepts
   only nodes, and proves canonical completeness plus soundness back to that
   numeric target.  This is the first branch point for the future PR proof-step
   checker over rules `0` through `38`.
   `Godel.CanonicalCodeRawNodePR` adds the first concrete PR layer for that
   branch point.  Its `rawNodeCodePR` checks the raw node head and the
   `nodeTagF` / `nodeChildrenF` destructors, proving soundness/completeness and
   PA representability through the final PR theorem.  This layer is deliberately
   weaker than full `NodeCodeNat`: validating that the children-code is a
   canonical code list remains the job of the later list parser.
   `Godel.CanonicalCodeNodeParserFromListLength` closes the full node-parser
   target modulo that list parser: it combines node-builder equality with
   `code-list-length-pr`, and derives `CanonicalCodeNodeParserPR` whenever the
   code-list-length relation has nonzero soundness.
   `Godel.CanonicalCodeRawListPR` adds the analogous first branch layer for
   canonical code lists.  It exposes represented PR relations for nil and cons
   head digits, with canonical completeness and soundness back to the raw list
   head predicates.  The payload parser for code-list head, tail, length, and
   nth remains the next parser task.
   `Godel.CanonicalCodeRawAtomListPR` adds the first concrete payload branch:
   a cons list whose head is an atom.  It returns the canonical head atom code
   and tail list code, with soundness/completeness and PA representability.
   This is useful for proof-rule branches such as rule37 while the fully
   general code-list head parser remains future work.

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

The current bridge into that work starts with `Godel.ProofCanonicalCoding`,
which mirrors PA proof trees into decodable canonical `Code` values and proves
that `canonicalCodePAProof` round-trips through the canonical numeric decoder.
This gives the future proof checker a structural input code instead of relying
on the older non-decoding proof-tree number.

`Godel.ProofCanonicalChecker` then defines an executable checker over that
canonical proof-tree code.  Its numeric entry point is:

```agda
checkCanonicalPAProofNat : ℕ → Maybe Formula
```

and it proves the complete direction for real PA derivations:

```agda
checkCanonicalPAProofNat-complete :
  CanonicalProofCodePA proof-code A →
  checkCanonicalPAProofNat proof-code ≡ just A
```

It also proves the semantic soundness direction:

```agda
checkCanonicalPAProofNat-sound :
  checkCanonicalPAProofNat proof-code ≡ just A →
  PA-provable A
```

The named semantic relation for this executable checker is:

```agda
ExecutableProofCodePA proof-code A =
  checkCanonicalPAProofNat proof-code ≡ just A
```

The checker module also proves an equivalent decoded-code view:

```agda
DecodedExecutableProofCodePA proof-code A =
  Σ Code λ c →
    proof-code ≡ encodeCode c ×
    checkPAProofCode c ≡ just A
```

This is the better target for the next PR implementation step: first represent
canonical numeric code decoding, then represent the code-level proof-step
checker.

`Godel.ProofCheckingPRTargets` packages this as a fully numeric target:

```agda
ExecutableProofCodeNat : ℕ → ℕ → Set
DecodedExecutableProofCodeNat : ℕ → ℕ → Set
```

and provides adapters:

```agda
proofCheckingPRNat-to-ProofCheckingPR :
  ProofCheckingPRNat → ProofCheckingPR

proofCheckingPRDecodedNat-to-ProofCheckingPR :
  ProofCheckingPRDecodedNat → ProofCheckingPR
```

So the concrete PR implementation can focus on the numeric relation first, and
only then feed the result back into the theorem-facing bridge.

`Godel.ProofCheckingPRComponents` starts the concrete component library for this
target.  The first implemented piece is numeric/formula-code equality:

```agda
formulaCodeEqPR : PRRel 2
formulaCodeEqPR = rel eqNatF
```

with soundness and completeness against ordinary natural-number equality.  This
is small, but important: later proof-step checking repeatedly needs to compare
formula codes, tags, and child-code positions using actual minimal-basis PR
helpers rather than meta-level equality.  The component now also exports its PA
representability proof through `Godel.PRRepresentabilityFinal.prrel-represented`,
so it is already connected to the final structured PR theorem boundary.  The
same module now includes `tagEqPR expected`, a fixed-tag equality relation for
checking proof-rule node tags such as `0` through `38`; it also carries
soundness, completeness, and PA representability through the same final theorem
entry.  It also includes `zeroTestPR = rel isZeroF`, with soundness,
completeness, and PA representability for ordinary zero tests used by parser and
proof-step checker branches.  Boolean conjunction is represented by
`andPR = rel andF`; its soundness proof is exact for natural numbers, showing
that a successful conjunction result equal to `1` forces both inputs to be `1`.
Boolean disjunction is represented by `orPR = rel orF`; its specification is the
branching-friendly one: a successful result means at least one input is nonzero,
and either nonzero input is complete for the checker.
The same component module now also includes `natNeqPR`, a PR relation for
ordinary natural-number inequality.  This is the reusable piece needed by the
canonical proof checker rule for closed numeral inequality.

`Godel.ProofRuleFixedPair` adds another reusable proof-rule component:

```agda
fixedPairF : ℕ → ℕ → PRF 2
```

It checks that the input `(proof-code, formula-code)` is exactly a fixed pair
of expected numeric codes.  The module proves complete/sound facts for this
checker and obtains PA representability via `PRRepresentabilityFinal`.  This
component is intended for fixed axiom leaves and other proof-rule branches
whose result is a predetermined proof/formula code pair.

`Godel.ProofRuleFixedPairTarget` wraps that component at the rule-target level:
`ProofRuleFixedPairPR` records complete/sound obligations for a fixed pair,
`proofRuleFixedPairPR` supplies the canonical instance, and
`proofRuleFixedPairPARepresentability` connects it back to the final PR
representability theorem.

`Godel.ProofRuleFixedProof` specializes the same idea to already-known PA
proofs.  Given `p : PA-provable A`, it fixes the proof code to
`canonicalCodePAProof p` and the formula code to `canonicalNatFormula A`; a
successful PR check can then be converted back to
`DecodedExecutableProofCodeNat` and `ExecutableProofCodeNat`.  This is the
direct route for fixed PA axiom leaves and any future fixed derived-proof
leaves.

`Godel.ProofRuleFixedProofOr` adds the binary disjunction combinator for those
fixed leaves.  `fixedProofOrPR p q` is a `PRRel 2` whose complete/sound theorem
returns either the left fixed proof leaf or the right one, and it also has
decoded/executable adapters plus `PRRepresentabilityFinal` representability.
Concrete multi-axiom aggregation should use named or opaque expected-code
boundaries before composing many leaves, so Agda does not normalize several
large formula codes at once.

`Godel.ProofRuleFixedCodeLeaf` provides that expected-code boundary.  A
`FixedCodeLeafData` record stores the two numeric expected codes together with a
decoded checker witness for exactly that pair.  The module builds
`fixedCodeLeafPR`, proves complete/sound and decoded/executable adapters, and
also supplies `fixedCodeLeafOrPR` for binary OR composition.  This is the
preferred path for aggregating multiple fixed PA axiom leaves without forcing
Agda to expand large canonical formula-code expressions inside the branch tree.

`Godel.ProofRulePAAxiomLeaves` instantiates that boundary for the six
non-parameterized PA axioms: successor-not-zero, successor injectivity, the two
addition axioms, and the two multiplication axioms.  Each named leaf already has
a decoded checker witness and PA representability via `PRRepresentabilityFinal`.
The induction schema is intentionally kept separate because it carries a
formula parameter.

`Godel.ProofRulePAAxiomInduction` adds that parameterized PA axiom target.  It
covers the tag `0` proof-code shape `node 0 (node 6 (A-code) :: [])` and the
output formula code `canonicalNatFormula (induction A)`, with a decoded-checker
adapter ready for a future concrete PR branch.

Multi-leaf OR aggregation is also kept out of `ProofRulePAAxiomLeaves` until
the concrete expected-code constants are made opaque enough to avoid large
formula-code normalization.

`Godel.ProofRulePRDisjunction` is the generic relation-level OR combinator for
proof-rule branches.  It constructs `orProofRulePR left right` and proves PA
representability through the final PR theorem, while keeping decoded soundness
generic instead of specializing it to large concrete formula-code expressions.

`Godel.ProofRulePAAxiomPairs` uses that combinator to build the first aggregate
branch for the proof checker:

```agda
paFixedAxiomLeafPR : PRRel 2
```

This relation covers the six non-parameterized PA axiom leaves and is already
PA-represented by `paFixedAxiomLeafPR-represented`.  The decoded/executable
adapters remain available generically through the fixed-code leaf/or modules;
they are not yet specialized to the aggregate branch because that is where Agda
starts normalizing large canonical formula codes.

`Godel.ProofRuleHilbertK` is the first non-fixed proof-rule target boundary.
It names the semantic relation for tag `1`, `HilbertKRuleNat`: the proof code
must be the canonical code of `node 1 (A-code , B-code)` and the output formula
code must be `canonicalNatFormula (A => B => A)`.  The module proves this
target maps back to `DecodedExecutableProofCodeNat` and packages the future PR
checker branch as `ProofRuleHilbertKCheckingBranchData`, including the nonzero
soundness field required by the final OR tree.

`Godel.ProofRuleHilbertS` follows the same schema-target pattern for tag `2`.
Its target `HilbertSRuleNat` covers canonical proof codes
`node 2 (A-code , B-code , C-code)` and the output formula code
`canonicalNatFormula ((A => B => C) => (A => B) => A => C)`.

`Godel.ProofRuleExcludedMiddle` follows the same pattern for tag `3`.  Its
target `ExcludedMiddleRuleNat` covers canonical proof codes
`node 3 (A-code)` whose output formula code is
`canonicalNatFormula (A \/ not A)`, and it provides the corresponding
decoded-checker adapter and targeted branch data.

`Godel.ProofRuleRecursiveSchemas` adds the recursive proof-tree targets, tag
`4` (`modus-ponens`) and tag `5` (`forall-generalize`).  These targets describe
the child proof-code obligations using `checkPAProofCode`, so they are the
semantic boundary that a future concrete recursive PR checker must implement.
`Godel.ProofCheckingRecursiveBundle` packages them as `RecursiveTarget₂`.

`Godel.ProofRuleEqRefl` records the first term-decoder-style target boundary,
tag `8`.  `EqReflRuleNat` says the proof code is the canonical code of
`node 8 (term-code)` and the output formula code is
`canonicalNatFormula (t = t)`.  Like the formula-schema targets, it already
maps back to `DecodedExecutableProofCodeNat` and can enter the branch tree once
its concrete PR checker and nonzero soundness are supplied.

`Godel.ProofRuleEqualitySchemas` continues that term-decoder family.  It now
contains targets for tag `9` (`eq-sym-rule`) and tag `10`
(`eq-trans-rule`), plus the arithmetic congruence tags `11` through `13`.
These targets have decoded-checker adapters and branch data records ready for
future concrete PR checkers.

`Godel.ProofCheckingEqualityBundle` packages the equality-related targets into
a reusable targeted OR branch.  Given branch data for tag `8` through tag `13`,
it exports `proofCheckingEqualityBranch₆`, whose target `EqualityTarget₆` can
be attached to the main proof checker tree through `ProofCheckingBranch`'s
generic extension interface.

`Godel.ProofRuleEqualitySubstitution` adds the equality substitution/value
targets for tag `24` (`eq-unique-value`), tag `35` (`eq-subst-right`), and tag
`36` (`eq-subst-suc-right`).  `Godel.ProofCheckingEqualitySubstitutionBundle`
packages them as `EqualitySubstitutionTarget₃`, with decoded-checker adapters
and branch records ready for future concrete PR checkers.

`Godel.ProofRuleDerivedLogicalSchemas` covers the larger block of derived
logical helper rules, tag `25` through tag `34` plus tag `38`.  These include
the conjunction/implication map helpers, `body-unique-compose`, and
`contradiction-to-neg`.  `Godel.ProofCheckingDerivedLogicalBundle` packages the
eleven targets into `DerivedLogicalTarget₁₁`.

`Godel.ProofRuleLogicalConnectives` covers the simple logical connective
targets, tag `19` through tag `23`: conjunction introduction/projections and
disjunction introductions.  `Godel.ProofCheckingLogicalBundle` packages those
five targets into `LogicalTarget₅`, another reusable targeted branch family
for the eventual proof checker OR tree.

`Godel.ProofRuleSubstitutionSchemas` covers the formula/term substitution-style
targets, tag `6` and tag `7`: forall elimination and exists introduction.
`Godel.ProofCheckingSubstitutionBundle` packages them as `SubstitutionTarget₂`,
which is included in the current aggregate target slice.

`Godel.ProofRuleQuantifierSchemas` covers the quantifier/existential-prefix
schema targets, tag `14` through tag `18`: exists elimination, prefix
introduction/lifting/premise-map, and premise change.  `Godel.ProofCheckingQuantifierBundle`
packages these targets into `QuantifierTarget₅`, ready to be attached as
another branch family.

`Godel.ProofCheckingTargetOverview` names the current aggregate target slice.
`CurrentProofCheckingTarget` combines the fixed PA axiom leaves, parameterized
induction axiom, rule 37, Hilbert K/S, excluded middle, recursive proof-tree
rules, substitution-style rules, equality/congruence rules, equality
substitution/value rules, derived logical helper rules, quantifier schemas, and
logical connective rules.  This is still a partial checker target, but it is
the current landing zone for the eventual decoded coverage proof that will
produce `ProofCheckingPRDecodedNat` and then `ProofCheckingPR`.

`Godel.ProofCheckingTargetCoverage` starts that decoded coverage proof.  It is
parameterized over the fixed PA axiom leaves to avoid normalizing large
concrete axiom codes, and it provides branch-injection helpers plus the first
coverage lemmas that use canonical decoder no-junk: Hilbert K/S, excluded
middle, the PA induction axiom, forall/exists substitution, logical connective
rules, equality/congruence rules, equality substitution/value rules, derived
logical helper rules, and quantifier/existential-prefix rules.

`Godel.ProofRuleTargets` starts splitting the executable proof checker into
rule-level numeric targets.  The first extracted branch is rule `37`, closed
numeral inequality:

```agda
ClosedNumeralNeqRuleNat : ℕ → ℕ → Set
```

It records exactly the canonical proof-code shape `node 37 (atom m, atom n)`
and the expected formula code for `¬ (numeral m ≈ numeral n)`, together with
the semantic side condition `m ≠ n`.  The module proves that this target maps
back to `DecodedExecutableProofCodeNat`.  It also defines the first rule-level
proof-code builder:

```agda
closedNumeralNeqProofCodeF : PRF 2
```

and proves that it computes the canonical code of `node 37 (atom m, atom n)`.
That builder is already represented in PA through
`PRRepresentabilityFinal.prf-represented`.  The module also exposes
`rule37ChildrenCodePR`, a represented PR relation checking that a children-code
is exactly the canonical list `[atom m, atom n]`.  This is the intermediate
payload checker needed to replace the monolithic rule-37 proof-code equality by
an outer node parser plus a children payload branch.

`Godel.ProofRule37NodeChildren` takes that split one step further.  It combines
`CanonicalCodeRawNodePR.rawNodeCodePR` with `rule37ChildrenCodePR` into
`rule37NodeChildrenPR`, a represented PR relation for the tuple
`(proof-code, children-code, m, n)`.  The relation states that the proof-code is
a raw node tagged `37` whose children-code is exactly the two-atom payload
`[atom m, atom n]`.  This is now a usable concrete proof-code branch for rule
37, while the formula-code and `m != n` parts remain separate small branches.

`Godel.ProofRule37DecomposedWitness` packages the next branch layer.  It uses a
five-argument witness
`(m,n,proof-code,children-code,formula-code)`, combines
`rule37NodeChildrenPR` with the existing formula-code and `m != n` branches, and
exports `rule37DecomposedWitnessPR` with soundness, completeness, a canonical
witness constructor, and PA representability.  This is the parser-backed
replacement path for the old monolithic proof-code equality inside
`rule37WitnessPR`; the bounded-search nonzero-hit bridge is still a later step.

`Godel.ProofRule37ParserWitness` wraps that decomposed checker back into the
four-argument search shape `(m,n,proof-code,formula-code)`.  It computes
`nodeChildrenF proof-code` and feeds that children-code to
`rule37DecomposedWitnessF`, yielding `rule37ParserWitnessPR` with
soundness/completeness and PA representability.  This gives the search layer a
parser-backed witness relation without returning to the monolithic
`proof-code = closedNumeralNeqCode m n` branch.

`Godel.ProofRule37SearchSkeleton` abstracts the shared two-dimensional bounded
search pattern over an arbitrary four-argument hit PRF.  It proves the search
PRF agrees with the corresponding meta-level search while keeping the hit
checker opaque.

`Godel.ProofRule37ParserSearch` starts the matching bounded-search route.  It
defines `rule37ParserSearchF`, mirroring the older `rule37SearchF` but using
`rule37ParserWitnessF` as the searched predicate.  Its semantic correctness now
comes from the generic skeleton, so the module exports
`rule37ParserSearchSemantics` without normalizing the parser witness inside the
nested search.  The direct PA representability adapter is intentionally not
unfolded there yet.

`Godel.ProofRule37ParserSearchHit` provides that small hit interface.  Given a
`Rule37ParserSearchSemantics` proof, it turns bounded parser-witness hits into
`rule37ParserSearchF = 1`, and turns parser-search success back into a bounded
nonzero hit.  The concrete `rule37ParserSearchHitInterface` is definitionally
aligned with `rule37ParserSearchMMeta`, so the remaining work is now focused on
the bridge between `Rule37ParserWitnessExists` and bounded hits/nonzero hits.

`Godel.ProofRule37ParserBounds` fills the boundedness half of that bridge.  It
proves that `nodeChildrenF proof-code` is bounded by `proof-code`; combined
with the parsed children payload `[atom m, atom n]`, this gives
`rule37ParserWitness-bounds : Rule37ParserWitnessNat m n proof-code formula-code
→ (m ≤ proof-code) × (n ≤ proof-code)`.  `Godel.ProofRule37ParserSearchComplete`
then packages the complete direction: a parser witness supplies the searched
`m,n`, the bounds theorem supplies the search bounds, and
`rule37ParserWitness-complete` supplies the hit proof.

`Godel.ProofRule37ParserSearchSound` completes the sound direction without
putting the conversion back into the generic hit interface.  It defines a
direct bounded-nonzero predicate for `rule37ParserWitnessF`, obtains it from
`rule37ParserSearchF = 1`, and then uses the abstract
`rule37ParserWitness-nonzero-sound` theorem to recover
`Rule37ParserWitnessExists`.  `Godel.ProofRule37ParserSearchCorrect` packages
these two halves as `rule37ParserSearchCorrect`.  This closes the parser-search
layer, but it is still not the final `ProofRule37PR`: the raw parser witness
must still be bridged back to the canonical `ClosedNumeralNeqRuleNat` target.

`Godel.ProofRule37CanonicalBridge` records the shape of that final bridge.  It
first proves that canonical list codes at rest `0` are injective, using
`parseCodeList-canonical`.  Then it proves that a full
`NodeCodeNat proof-code 37 children-code` target, together with the children
payload `[atom m, atom n]`, reconstructs
`proof-code = closedNumeralNeqCode m n`; with the formula-code and inequality
branches, this yields `ClosedNumeralNeqRuleNat`.  This is deliberately stronger
than the raw parser witness: the final rule37 branch should use the canonical
node/list parser target rather than raw `nodeTagF/nodeChildrenF` destructors
alone.

`Godel.ProofRule37CanonicalWitness` packages that stronger target into a
search-facing form.  `Rule37CanonicalWitnessExists proof-code formula-code`
means there are `m,n` together with the canonical parser witness.  The module
proves both directions between this witness target and
`ClosedNumeralNeqRuleNat`, and defines
`ProofRule37CanonicalWitnessSearchPR`: once a PR relation is shown to search
exactly for canonical witnesses, `proofRule37PR-from-canonical-witness-search`
turns it into the final `ProofRule37PR` branch with a
`PRRepresentabilityFinal` adapter.  This is the next concrete target after the
raw parser-search route.

`Godel.ProofRule37CanonicalSearch` makes that target bounded and branch-facing.
It defines `Rule37CanonicalBoundedWitnessExists`, proves that a canonical parser
witness supplies the search bounds `m,n <= proof-code`, and implements
`rule37CanonicalWitnessF` plus `rule37CanonicalSearchF`.  Given a full
`CanonicalCodeNodeParserPR` with nonzero soundness for its characteristic PRF,
`proofRule37CanonicalBoundedSearchPR-from-node-parser` yields the bounded
canonical search record, and
`proofRule37CanonicalCheckingBranchData-from-node-parser` plugs it into
`ProofCheckingRule37Branch`.  The full node parser can now be derived from a
code-list-length parser, so the remaining concrete gap is narrower again:
implement `code-list-length-pr` and its nonzero-sound theorem.

`Godel.ProofRule37FromCodeListLength` closes that wiring explicitly.  Given a
`CanonicalCodeParserPR` plus `CodeListLengthNonzeroSound`, it builds the full
node-parser search data and then exports `ProofRule37CheckingBranchData`.  Thus
the path from list-length parser correctness to the rule37 branch of
`proofCodePAPR` is now a checked adapter rather than an informal next step.

`ProofRuleTargets` also imports the matching formula-code builder:

```agda
closedNumeralNeqFormulaCodeF : PRF 2
```

and records that it computes the canonical code of
`¬ (numeral m ≈ numeral n)`.  The full rule relation is still packaged as
`ProofRule37PR` with a `PRRepresentabilityFinal` adapter.  There is now also a
witness-carrying checker shape:

```agda
rule37WitnessPR : PRRel 4
```

which takes `(m,n,proof-code,formula-code)` and combines the proof-code,
formula-code, and `m ≠ n` checks.  This branch has now been factored into
small checker pieces: proof-code equality, formula-code equality, and natural
number inequality each have local correctness and sound/complete lemmas; the
raw `andF` layers use `Godel.PRBooleanSoundness.and-output-sound`; and the
combined witness checker has evaluator-level completeness.  The helper
`rule37WitnessF-sound-ones` also extracts the three branch facts from a
successful combined checker, and `rule37WitnessF-sound` converts those facts
back into `Rule37WitnessNat`.  The checker is already represented in PA by
`rule37WitnessPR-represented`, which is obtained from
`PRRepresentabilityFinal.prrel-represented`.  The module
`Godel.ProofRule37PRHolds` provides the `PRRel-holds` complete/sound wrapper:
it proves the inline relation `(rel rule37WitnessF)` first, then transports the
result across `rule37WitnessPR ≡ rel rule37WitnessF` to avoid a monolithic
normalization proof.  The same module defines:

```agda
Rule37WitnessExists : ℕ → ℕ → Set
```

and proves that this existential witness specification is equivalent to
`ClosedNumeralNeqRuleNat`.  This is the exact boundary for the next step:
turning “there exist witness numerals `m,n`” into a genuine binary `PRRel 2`
using a bounded witness-search checker.  The record
`ProofRule37WitnessSearchPR` captures that next checker precisely: provide a
binary PR relation equivalent to `Rule37WitnessExists`, and
`proofRule37PR-from-witness-search` turns it into the `ProofRule37PR` instance
needed by the rule-level proof checker route.

`Godel.ProofRule37Bounds` proves the coding-theoretic bound needed by that
search.  For a canonical rule-37 proof code
`closedNumeralNeqCode m n`, both payload witnesses are bounded by the code:
`m <= closedNumeralNeqCode m n` and `n <= closedNumeralNeqCode m n`.  The module
also transports these bounds across a proof-code equality
`proof-code = closedNumeralNeqCode m n`.  This proof is deliberately independent
of the large witness checker.

`Godel.ProofRule37Search` starts the concrete version of that next checker.  It
defines:

```agda
rule37SearchF : PRF 2
```

The function uses `proof-code` as a bound, searches all `m,n <= proof-code`,
and runs the four-argument witness checker `rule37WitnessF`.  The module proves
that `evalPRF rule37SearchF` agrees with a clean meta-level bounded search.
The remaining proof obligation is now sharply isolated as `Rule37SearchCorrect`:
show that this bounded search is complete and sound for `Rule37WitnessExists`.
Intuitively, the missing completeness ingredient is the bound lemma saying that
the witnesses `m,n` encoded in a canonical rule-37 proof code are no larger
than the proof code itself.

`Godel.ProofRule37SearchCorrectness` factors out the generic search fact needed
for that completeness proof: for any meta-level predicate `P : ℕ → ℕ`, if
`P n = 1` for some `n <= bound`, then `searchUpTo P bound = 1`.  It also proves
the corresponding theorem for the two-dimensional nested search used by rule
37.  The soundness direction is factored generically too: if a one-dimensional
or two-dimensional bounded search returns `1`, then some bounded searched point
has a nonzero predicate value.  This module deliberately stays independent of
the large `rule37WitnessF`, so it can be checked without forcing Agda to
normalize the whole witness checker.  The rule-37-specific work is to connect
these generic lemmas to a small named witness-hit interface.

`Godel.ProofRule37SearchHit` adds that small interface boundary.  It does not
claim the interface has been instantiated yet; instead it proves the useful
adapter theorem: once a `Rule37WitnessHitBridge` supplies a bounded hit
predicate aligned with `rule37SearchMMeta`, `rule37SearchF` is complete for the
given witness specification.  This keeps the bounded-search proof separate from
the heavy witness checker normalization problem.  The same module now has the
soundness-side bridge too: a `Rule37WitnessHitSoundBridge` turns bounded
nonzero hits back into the target witness specification and therefore yields
search soundness.

`Godel.ProofRule37SemanticHit` narrows the gap further.  Given a hit interface
and a small completeness field saying that `Rule37WitnessNat` makes the hit
predicate return `1`, it uses the rule-37 bound lemmas to turn
`ClosedNumeralNeqRuleNat` into a bounded hit and then derives
`rule37SearchF = 1`.  In other words, the remaining completeness work is now
focused on instantiating the hit predicate with the actual witness checker,
without reintroducing monolithic normalization.

`Godel.ProofRule37ActualHit` instantiates the hit interface with the real
`rule37WitnessValue` already used by `rule37SearchMMeta`.  The alignment with
the search meta function is definitional.  The module deliberately packages the
remaining expensive-looking proof as `Rule37ActualHitData`: prove only that
`Rule37WitnessNat` makes `rule37WitnessValue` return `1`, and the previously
factored adapters yield rule-37 search completeness for
`ClosedNumeralNeqRuleNat`.

`Godel.ProofRule37ActualSearch` packages the current rule-37 endpoint.  Given
`Rule37ActualSearchData`, it turns the concrete `rule37SearchPR` relation into
a full `ProofRule37PR` instance via `proofRule37PR-from-actual-search`.
Completeness is already routed through the actual-hit and bound adapters; the
remaining field is a structured soundness bridge
`Rule37WitnessHitSoundBridge ClosedNumeralNeqRuleNat`, rather than an opaque
whole-search soundness assumption.  The same module now also derives nonzero
search soundness from that bridge and packages the result as
`proofRule37CheckingBranchData-from-actual-search`, so actual search data can
enter the final proof-checker OR tree through `ProofCheckingRule37Branch`.

`Godel.ProofRule37ArgsHit` records an alternate args-based route for the
remaining proof.  Its hit value is defined with `rule37WitnessArgs`, matching
the existing complete/sound theorems for `rule37WitnessF` more directly.  The
module is currently a boundary record, not a completed proof: it names the
remaining alignment, completeness, and soundness fields and provides an adapter
from those fields to `ProofRule37PR`.  The record
`Rule37ArgsCheckingBranchData` adds the OR-tree-specific nonzero soundness
field and adapts the args route to `ProofRule37CheckingBranchData`.

The PA-facing target layer is `Godel.ProofCheckingPR`.  It fixes the shape of
the PR proof-checker target:

```agda
proofCodePAPR : PRRel 2
```

and records the sound/complete connection to `ExecutableProofCodePA`.  It also
shows how `Godel.PRRepresentabilityFinal.prrel-represented` will turn that
checker into PA true/false proofs.  The remaining concrete work is to unfold the
executable checker into a primitive-recursive relation and prove the bridge from
the canonical checker formula back to the legacy `ProofCodePA` / `ProofOf`
predicates used by the existing incompleteness theorem.  This bridge is
intentionally explicit: it does not assume that the old proof-code number and
the canonical proof-tree number are definitionally the same.

`Godel.ProofCheckingBranch` is the current branch-composition layer for that
checker.  It records the useful soundness shape for a proof-rule branch:
successful or nonzero hits must reconstruct a `DecodedExecutableProofCodeNat`.
Its `orProofCheckingBranchPR` combinator is the intended glue for the eventual
`proofCodePAPR` OR tree.  The targeted branch record additionally separates a
branch's semantic target from the PR relation and supplies the adapter to
`ProofCheckingPRDecodedNat` once the combined target is the full decoded
executable proof-code relation.  It also provides `fixedCodeLeafTargetedBranch`,
so fixed proof-code/formula-code leaves can enter the branch tree through the
opaque `FixedCodeLeafData` boundary.  When a combined target covers the full
decoded checker, `targetedProofCheckingBranch-covered-proofCheckingPR` sends it
straight to the theorem-facing `ProofCheckingPR` record.  Large fixed-code leaf
families should be aggregated only through those boundaries; otherwise Agda may
normalize several large proof/formula codes at once.  The generic
`ProofCheckingBranchExtensionData` record is the incremental form of the same
idea: combine an existing targeted branch with one more targeted branch family,
then supply coverage for the joined target.

`Godel.ProofCheckingFixedLeafBranches` is the parameterized aggregation layer
for those fixed leaves.  It builds targeted OR trees for two, four, or six
`FixedCodeLeafData` inputs without importing the concrete PA axiom constants.
This keeps the aggregation proof reusable and light: concrete axiom leaves can
be supplied later through opaque data boundaries.

`Godel.ProofCheckingRule37Branch` performs the analogous adapter step for rule
37.  A plain `ProofRule37PR` proves soundness only for hits equal to `1`; the
final OR tree also needs nonzero-hit soundness.  The record
`ProofRule37CheckingBranchData` names that extra obligation, and
`proofRule37TargetedBranch` turns it into a targeted branch for
`ClosedNumeralNeqRuleNat`.  Once the canonical witness search relation is
finished with nonzero soundness, it can enter the proof checker through this
adapter.

`Godel.ProofCheckingBranchBundle` is the next light aggregation step.  It
combines six opaque fixed-code leaves with the rule-37 targeted branch, then
offers adapters to `ProofCheckingPRDecodedNat` and `ProofCheckingPR` once a
caller supplies the remaining coverage proof for the decoded executable proof
checker.  This keeps concrete PA axiom constants outside the bundle, preserving
the performance boundary around large canonical proof/formula codes.  The
record `ProofCheckingFixedAndRule37Data` is the current endpoint for this
partial branch tree: its remaining coverage field is exactly what must be
expanded as more proof-rule branches are added.  The plus-data variant is
implemented through the generic extension interface, so new proof-rule tags can
be attached without reshaping the fixed+rule37 base.  The named
`ProofCheckingFixedRule37HilbertKData` and
`ProofCheckingFixedRule37HilbertKExcludedData` / `...ExcludedSData` bundles
attach the first three schema-style targets, `hilbert-K`, excluded middle, and
`hilbert-S`, to that base.

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
graph.  The older history-backed closure remains as a compatibility bridge, but
the structured route now exports `structured-primitive-recursion-closes` without
an evaluated graph conjunct.  `Godel.PRRepresentabilityFinal` is the final public
boundary for this second step; high-level checked graph modules should import it
instead of the legacy bridge.  The next proof refinement is to rebuild the syntax
checker PR instance and connect it to this final theorem boundary.

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
