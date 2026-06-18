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
- an object-language proof predicate shape, `ProofOf p A`;
- a Hilbert-style derivability relation;
- a small PA axiom schema and a concrete coding of PA proof trees;
- an abstract arithmetized-theory interface;
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

4. `Godel.Diagonal`

   `FixedPoint T φ` packages a sentence `θ` together with proofs that `T`
   proves both directions of:

   ```text
   θ <-> φ(⌜θ⌝)
   ```

   `DiagonalLemma T` says that such a fixed point exists for every formula
   `φ`. Applying it to `noProofsTemplate` gives the usual self-referential
   Godel sentence shape.

5. `Godel.Original`

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

6. `Godel.PAFirstIncompleteness`

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

## Main Proof Path

The shortest path through the project is:

```text
noProofsTemplate
  -> DiagonalLemma.fixedPoint
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

Because these are record fields rather than postulates, the checked theorem is
conditional and explicit: any future implementation must provide exactly these
pieces before obtaining the PA-level theorem.

## Checking

The whole project is checked through:

```bash
agda -i . Godel/Everything.agda
```

This guide does not change the Agda API or theorem statements.
