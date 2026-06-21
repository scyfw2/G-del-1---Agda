import LeanShadow.DiagonalInterface

namespace LeanShadow

/-!
This is the high-level theorem already present abstractly on the Agda side:
once PA represents the proof predicate and the no-proofs fixed point exists,
the fixed point is undecidable under the chosen consistency hypothesis.
-/
axiom firstIncompletenessFromNoProofs :
  (rep : PARepresentsRelation2 ProofCodePANat) ->
  (fp : NoProofsFixedPoint rep) ->
  Consistent PA ->
  Undecidable PA fp.sentence

noncomputable def proofCodePA_PR_to_PA_representation
    (D : ProofCodePAPRData) :
    PARepresentsRelation2 ProofCodePANat :=
  paRepresentsProofCodePA D

noncomputable def proofCodePA_PR_to_noProofs_fixedPoint
    (D : ProofCodePAPRData) :
    NoProofsFixedPoint (proofCodePA_PR_to_PA_representation D) :=
  diagonalNoProofs (proofCodePA_PR_to_PA_representation D)

theorem proofCodePA_PR_to_first_incompleteness
    (D : ProofCodePAPRData) :
    Consistent PA -> exists G : Formula, Undecidable PA G := by
  intro hConsistent
  let rep := proofCodePA_PR_to_PA_representation D
  let fp := diagonalNoProofs rep
  exact Exists.intro fp.sentence
    (firstIncompletenessFromNoProofs rep fp hConsistent)

/-!
Same result, with the Gödel sentence exposed as the sentence of the no-proofs
fixed point generated from the PR proof-checker data.
-/
noncomputable def godelSentenceFromProofChecker (D : ProofCodePAPRData) : Formula :=
  (proofCodePA_PR_to_noProofs_fixedPoint D).sentence

theorem godelSentenceFromProofChecker_undecidable
    (D : ProofCodePAPRData) :
    Consistent PA ->
    Undecidable PA (godelSentenceFromProofChecker D) := by
  intro hConsistent
  unfold godelSentenceFromProofChecker
  exact
    firstIncompletenessFromNoProofs
      (proofCodePA_PR_to_PA_representation D)
      (proofCodePA_PR_to_noProofs_fixedPoint D)
      hConsistent

end LeanShadow
