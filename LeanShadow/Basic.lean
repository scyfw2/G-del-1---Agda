namespace LeanShadow

/-!
This directory is a Lean shadow proof, not a translation of the Agda
formalization.  It keeps Agda-side low-level constructions behind explicit
interfaces, then checks the high-level dependency shape of the incompleteness
argument.
-/

inductive Term where
  | numeral : Nat -> Term
  | var : Nat -> Term
  | zero : Term
  | succ : Term -> Term
  | add : Term -> Term -> Term
  | mul : Term -> Term -> Term
deriving Repr, DecidableEq

inductive Formula where
  | atom : String -> List Term -> Formula
  | eq : Term -> Term -> Formula
  | imp : Formula -> Formula -> Formula
  | neg : Formula -> Formula
  | all : Formula -> Formula
  | ex : Formula -> Formula
deriving Repr

infix:60 " ≈ " => Formula.eq
infixr:55 " ⇒ " => Formula.imp
prefix:70 "¬ᶠ" => Formula.neg

structure Theory where
  Provable : Formula -> Prop

axiom PA : Theory

def Inconsistent (T : Theory) : Prop :=
  Exists fun A => T.Provable A /\ T.Provable (Formula.neg A)

def Consistent (T : Theory) : Prop :=
  Not (Inconsistent T)

def Undecidable (T : Theory) (A : Formula) : Prop :=
  Not (T.Provable A) /\ Not (T.Provable (Formula.neg A))

axiom formulaCode : Formula -> Nat

def numeralTerm (n : Nat) : Term :=
  Term.numeral n

end LeanShadow
