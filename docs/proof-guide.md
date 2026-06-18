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
   ```

   It also defines `diagFormula`, `diagCode`, `DiagCode`, and `DiagRel` as early
   staging pieces for future diagonal/substitution representability work. This
   does not replace the numeric `codeFormula` used by the current theorem. The
   fuelled round-trip statements are the checked core; the unfuelled
   `decodeNatTerm` and `decodeNatFormula` wrappers are convenience entrypoints.

5. `Godel.DiagonalCoding`

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

6. `Godel.Diagonal`

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

7. `Godel.Original`

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

8. `Godel.PAFirstIncompleteness`

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

## Main Proof Path

The shortest path through the project is:

```text
noProofsTemplate
  -> canonical numeric coding
  -> Subst0NatCode / DiagNatCode as future representability targets
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
PA represents the diagonal/substitution graph.

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
