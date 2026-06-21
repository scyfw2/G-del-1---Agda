import LeanShadow.Basic

namespace LeanShadow.Rule37Mini

/-!
A deliberately small Lean prototype for the rule-37 shape.

This is not the Agda canonical base-4 code.  It keeps the relevant proof
obligations:

* parse a proof code as a tag carrying two witnesses `m,n`;
* check the formula code for `not (numeral m = numeral n)`;
* check `m != n`;
* turn an explicit witness checker into a two-argument bounded search checker.

The point is to test whether Lean can handle the parser/search proof pattern
comfortably before trying to port any real Agda encoding work.
-/

def pair (a b : Nat) : Nat :=
  2 ^ a * (2 * b + 1)

def fstAux : Nat -> Nat -> Nat
  | 0, _ => 0
  | Nat.succ fuel, x =>
      if x % 2 = 0 then
        Nat.succ (fstAux fuel (x / 2))
      else
        0

def fst (x : Nat) : Nat :=
  fstAux x x

def snd (x : Nat) : Nat :=
  ((x / (2 ^ fst x)) - 1) / 2

axiom fst_pair : forall a b : Nat, fst (pair a b) = a
axiom snd_pair : forall a b : Nat, snd (pair a b) = b
axiom pair_eta : forall x : Nat, pair (fst x) (snd x) = x
axiom pair_ext :
  forall {a b c d : Nat}, pair a b = pair c d -> a = c /\ b = d

def proofCode (m n : Nat) : Nat :=
  pair 37 (pair m n)

def formulaCode (m n : Nat) : Nat :=
  pair m n

def payloadM (proofCode : Nat) : Nat :=
  fst (snd proofCode)

def payloadN (proofCode : Nat) : Nat :=
  snd (snd proofCode)

def isRule37Node (proofCode : Nat) : Prop :=
  fst proofCode = 37

def formulaMatches (proofCode formulaCodeNat : Nat) : Prop :=
  formulaCodeNat = formulaCode (payloadM proofCode) (payloadN proofCode)

def witness (m n proofCodeNat formulaCodeNat : Nat) : Prop :=
  proofCodeNat = proofCode m n /\
  formulaCodeNat = formulaCode m n /\
  m ≠ n

def target (proofCode formulaCodeNat : Nat) : Prop :=
  exists m n, witness m n proofCode formulaCodeNat

def directChecker (proofCode formulaCodeNat : Nat) : Prop :=
  isRule37Node proofCode /\
  formulaMatches proofCode formulaCodeNat /\
  payloadM proofCode ≠ payloadN proofCode

theorem proofCode_payloadM (m n : Nat) :
    payloadM (proofCode m n) = m := by
  unfold payloadM proofCode
  rw [snd_pair 37 (pair m n), fst_pair m n]

theorem proofCode_payloadN (m n : Nat) :
    payloadN (proofCode m n) = n := by
  unfold payloadN proofCode
  rw [snd_pair 37 (pair m n), snd_pair m n]

theorem target_to_directChecker :
    target proofCodeNat formulaCodeNat ->
    directChecker proofCodeNat formulaCodeNat := by
  intro h
  rcases h with ⟨m, n, hProof, hFormula, hNeq⟩
  subst proofCodeNat
  subst formulaCodeNat
  constructor
  · unfold isRule37Node proofCode
    exact fst_pair 37 (pair m n)
  · constructor
    · unfold formulaMatches
      rw [proofCode_payloadM m n, proofCode_payloadN m n]
    · rw [proofCode_payloadM m n, proofCode_payloadN m n]
      exact hNeq

theorem directChecker_to_target :
    directChecker proofCodeNat formulaCodeNat ->
    target proofCodeNat formulaCodeNat := by
  intro h
  rcases h with ⟨hTag, hFormula, hNeq⟩
  refine ⟨payloadM proofCodeNat, payloadN proofCodeNat, ?_, hFormula, hNeq⟩
  unfold proofCode
  change proofCodeNat =
    pair 37 (pair (fst (snd proofCodeNat)) (snd (snd proofCodeNat)))
  have hPayload :
      snd proofCodeNat =
        pair (fst (snd proofCodeNat)) (snd (snd proofCodeNat)) := by
    exact Eq.symm (pair_eta (snd proofCodeNat))
  calc
    proofCodeNat = pair (fst proofCodeNat) (snd proofCodeNat) := by
      exact Eq.symm (pair_eta proofCodeNat)
    _ = pair 37 (snd proofCodeNat) := by rw [hTag]
    _ = pair 37 (pair (fst (snd proofCodeNat)) (snd (snd proofCodeNat))) := by
      exact congrArg (fun x => pair 37 x) hPayload

def witnessBool (m n proofCodeNat formulaCodeNat : Nat) : Bool :=
  proofCodeNat == proofCode m n &&
  formulaCodeNat == formulaCode m n &&
  decide (m ≠ n)

def searchM (bound n proofCodeNat formulaCodeNat : Nat) : Bool :=
  match bound with
  | 0 => witnessBool 0 n proofCodeNat formulaCodeNat
  | Nat.succ b =>
      witnessBool (Nat.succ b) n proofCodeNat formulaCodeNat ||
      searchM b n proofCodeNat formulaCodeNat

def searchMN (boundM boundN proofCodeNat formulaCodeNat : Nat) : Bool :=
  match boundN with
  | 0 => searchM boundM 0 proofCodeNat formulaCodeNat
  | Nat.succ b =>
      searchM boundM (Nat.succ b) proofCodeNat formulaCodeNat ||
      searchMN boundM b proofCodeNat formulaCodeNat

theorem witnessBool_complete
    {m n proofCodeNat formulaCodeNat : Nat} :
    witness m n proofCodeNat formulaCodeNat ->
    witnessBool m n proofCodeNat formulaCodeNat = true := by
  intro h
  rcases h with ⟨hProof, hFormula, hNeq⟩
  unfold witnessBool
  subst proofCodeNat
  subst formulaCodeNat
  simp [hNeq]

theorem witnessBool_sound
    {m n proofCodeNat formulaCodeNat : Nat} :
    witnessBool m n proofCodeNat formulaCodeNat = true ->
    witness m n proofCodeNat formulaCodeNat := by
  intro h
  unfold witnessBool at h
  simp at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem searchM_complete
    {m n bound proofCodeNat formulaCodeNat : Nat} :
    m <= bound ->
    witness m n proofCodeNat formulaCodeNat ->
    searchM bound n proofCodeNat formulaCodeNat = true := by
  intro hLe hWitness
  induction bound with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero hLe
      subst m
      unfold searchM
      exact witnessBool_complete hWitness
  | succ b ih =>
      unfold searchM
      by_cases hTop : m = Nat.succ b
      · subst m
        simp [witnessBool_complete hWitness]
      · have hLeB : m <= b := Nat.le_of_lt_succ
          (Nat.lt_of_le_of_ne hLe hTop)
        have hSearch := ih hLeB
        simp [hSearch]

theorem searchMN_complete
    {m n boundM boundN proofCodeNat formulaCodeNat : Nat} :
    m <= boundM ->
    n <= boundN ->
    witness m n proofCodeNat formulaCodeNat ->
    searchMN boundM boundN proofCodeNat formulaCodeNat = true := by
  intro hm hn hWitness
  induction boundN with
  | zero =>
      have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
      subst n
      unfold searchMN
      exact searchM_complete hm hWitness
  | succ b ih =>
      unfold searchMN
      by_cases hTop : n = Nat.succ b
      · subst n
        simp [searchM_complete hm hWitness]
      · have hLeB : n <= b := Nat.le_of_lt_succ
          (Nat.lt_of_le_of_ne hn hTop)
        have hSearch := ih hLeB
        simp [hSearch]

theorem searchM_sound
    {bound n proofCodeNat formulaCodeNat : Nat} :
    searchM bound n proofCodeNat formulaCodeNat = true ->
    exists m, m <= bound /\ witness m n proofCodeNat formulaCodeNat := by
  intro h
  induction bound with
  | zero =>
      unfold searchM at h
      exact ⟨0, Nat.le_refl 0, witnessBool_sound h⟩
  | succ b ih =>
      unfold searchM at h
      simp only [Bool.or_eq_true] at h
      cases h with
      | inl hit =>
          exact ⟨Nat.succ b, Nat.le_refl (Nat.succ b), witnessBool_sound hit⟩
      | inr rest =>
          rcases ih rest with ⟨m, hm, hw⟩
          exact ⟨m, Nat.le_trans hm (Nat.le_succ b), hw⟩

theorem searchMN_sound
    {boundM boundN proofCodeNat formulaCodeNat : Nat} :
    searchMN boundM boundN proofCodeNat formulaCodeNat = true ->
    exists m n,
      m <= boundM /\ n <= boundN /\ witness m n proofCodeNat formulaCodeNat := by
  intro h
  induction boundN with
  | zero =>
      unfold searchMN at h
      rcases searchM_sound h with ⟨m, hm, hw⟩
      exact ⟨m, 0, hm, Nat.le_refl 0, hw⟩
  | succ b ih =>
      unfold searchMN at h
      simp only [Bool.or_eq_true] at h
      cases h with
      | inl hit =>
          rcases searchM_sound hit with ⟨m, hm, hw⟩
          exact ⟨m, Nat.succ b, hm, Nat.le_refl (Nat.succ b), hw⟩
      | inr rest =>
          rcases ih rest with ⟨m, n, hm, hn, hw⟩
          exact ⟨m, n, hm, Nat.le_trans hn (Nat.le_succ b), hw⟩

def boundedRule37Search (proofCodeNat formulaCodeNat : Nat) : Bool :=
  searchMN proofCodeNat proofCodeNat proofCodeNat formulaCodeNat

axiom witnessBound :
  forall {m n proofCodeNat formulaCodeNat : Nat},
    witness m n proofCodeNat formulaCodeNat ->
    m <= proofCodeNat /\ n <= proofCodeNat

theorem boundedRule37Search_complete
    {proofCodeNat formulaCodeNat : Nat} :
    target proofCodeNat formulaCodeNat ->
    boundedRule37Search proofCodeNat formulaCodeNat = true := by
  intro h
  rcases h with ⟨m, n, hw⟩
  rcases witnessBound hw with ⟨hm, hn⟩
  exact searchMN_complete hm hn hw

theorem boundedRule37Search_sound
    {proofCodeNat formulaCodeNat : Nat} :
    boundedRule37Search proofCodeNat formulaCodeNat = true ->
    target proofCodeNat formulaCodeNat := by
  intro h
  rcases searchMN_sound h with ⟨m, n, _hm, _hn, hw⟩
  exact ⟨m, n, hw⟩

end LeanShadow.Rule37Mini
