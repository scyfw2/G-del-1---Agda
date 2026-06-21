import LeanShadow.PRRepresentabilityInterface

namespace LeanShadow

/-!
The theorem-facing proof predicate still talks about formulas, while the PR
checker talks about natural-number proof codes and formula codes.
-/

axiom ProofCodePA : Nat -> Formula -> Prop

def ProofCodePANat (proofCode formulaCodeNat : Nat) : Prop :=
  exists A : Formula,
    formulaCode A = formulaCodeNat /\ ProofCodePA proofCode A

structure ProofCodePAPRData where
  checker : Nat -> Nat -> Prop
  checkerPR : IsPRRel2 checker
  checkerComplete :
    forall {proofCode formulaCodeNat : Nat},
      ProofCodePANat proofCode formulaCodeNat ->
      checker proofCode formulaCodeNat
  checkerSound :
    forall {proofCode formulaCodeNat : Nat},
      checker proofCode formulaCodeNat ->
      ProofCodePANat proofCode formulaCodeNat

theorem proofCodePAIsPR (D : ProofCodePAPRData) :
    IsPRRel2 ProofCodePANat :=
  prRel2Extensional
    (R := D.checker)
    (S := ProofCodePANat)
    (by
      intro proofCode formulaCodeNat
      constructor
      · intro h
        exact D.checkerSound h
      · intro h
        exact D.checkerComplete h)
    D.checkerPR

noncomputable def paRepresentsProofCodePA (D : ProofCodePAPRData) :
    PARepresentsRelation2 ProofCodePANat :=
  paRepresentsAllPRRel2 ProofCodePANat (proofCodePAIsPR D)

end LeanShadow
