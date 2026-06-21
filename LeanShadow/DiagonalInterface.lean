import LeanShadow.ProofPredicateInterface

namespace LeanShadow

structure FixedPoint (T : Theory) (template : Formula -> Formula)
    (sentence : Formula) where
  forward : T.Provable (sentence ⇒ template sentence)
  backward : T.Provable (template sentence ⇒ sentence)

/-!
`noProofsTemplate rep A` is the formula saying, informally, that there is no
PA proof code for `A`.  Its concrete syntax is left abstract in this shadow
layer; Agda is responsible for the actual arithmetization.
-/
axiom noProofsTemplate :
  PARepresentsRelation2 ProofCodePANat -> Formula -> Formula

structure NoProofsFixedPoint
    (rep : PARepresentsRelation2 ProofCodePANat) where
  sentence : Formula
  fixed : FixedPoint PA (noProofsTemplate rep) sentence

axiom diagonalNoProofs :
  (rep : PARepresentsRelation2 ProofCodePANat) ->
  NoProofsFixedPoint rep

end LeanShadow
