import LeanShadow.Basic

namespace LeanShadow

/-!
PR-ness and PA representability are interfaces here.  In the Agda development,
the corresponding final entry is `Godel.PRRepresentabilityFinal`.
-/

class IsPRRel2 (R : Nat -> Nat -> Prop) : Prop where
  marker : True

structure PARepresentsRelation2 (R : Nat -> Nat -> Prop) where
  relationFormula : Term -> Term -> Formula
  representsTrue :
    forall {x y : Nat}, R x y ->
      PA.Provable (relationFormula (numeralTerm x) (numeralTerm y))
  representsFalse :
    forall (x y : Nat), Not (R x y) ->
      PA.Provable
        (Formula.neg (relationFormula (numeralTerm x) (numeralTerm y)))

axiom paRepresentsAllPRRel2 :
  (R : Nat -> Nat -> Prop) -> IsPRRel2 R -> PARepresentsRelation2 R

axiom prRel2Extensional :
  {R S : Nat -> Nat -> Prop} ->
  (forall x y, R x y <-> S x y) ->
  IsPRRel2 R ->
  IsPRRel2 S

end LeanShadow
