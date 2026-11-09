/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Security.StateRestorationBudget
import ArkLibTest.Interaction.Core.Oracle
import ArkLibTest.Data.OracleComp.AddProgram

/-! A two-round state-restoration client with round errors `1/8` and `1/16`. Each round sends a
`Fin 8` oracle; the challenges are drawn from `Fin 8` and `Fin 16`. The verifier accepts when the
first or the second challenge is `0`, returning the second message as the claim and as its output
oracle. The adversary queries a second-round key twice before selecting its transcript, so the
restored execution is charged at most `2 * (1/8) + (1/8 + 1/16) = 7/16`.

A knowledge state function extracts by adding both messages to the output witness. Its message
stages are measured by one charged addition each and its challenge stages are uncharged, so every
extraction costs two additions. -/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp OracleSpec AddProgramTest
open Interaction.Core.StateRestoration
open Interaction.Core.OracleTests (emptyFamily)

namespace Interaction.Core.StateRestorationBudgetTests

/-- A sent `Fin 8` answers its single query with itself. -/
@[instance_reducible] def messageInterface : OracleInterface (Fin 8) where
  Query := Unit
  toOC := { spec := fun _ => Fin 8, impl := fun _ => do return (← read) }

/-- The first round: a `Fin 8` oracle message and a `Fin 8` challenge. -/
@[implicit_reducible] def firstRound : Round where
  Message := Fin 8
  Challenge := Fin 8
  interface := messageInterface
  sampleChallenge := inferInstance

/-- The second round: a `Fin 8` oracle message and a `Fin 16` challenge. -/
@[implicit_reducible] def secondRound : Round where
  Message := Fin 8
  Challenge := Fin 16
  interface := messageInterface
  sampleChallenge := inferInstance

@[implicit_reducible] def rounds : List Round := [firstRound, secondRound]

/-- The first round's local error is `1/8`, the second's `1/16`. -/
noncomputable def errors : RoundErrors rounds := fun j : Fin 2 => if j = 0 then 1 / 8 else 1 / 16

/-- The output is one `Fin 8` oracle. -/
@[instance_reducible] def outputFamily : OracleFamily PUnit (fun _ => Fin 8) :=
  singletonFamily messageInterface

/-- The input statement: a number with no input oracles. -/
abbrev Stmt : Type := Nat × (∀ i : PEmpty.{1}, (PEmpty.elim i : Type))

/-- The statement `z` with no input oracles. -/
def stmt (z : Nat) : Stmt := (z, fun i => PEmpty.elim i)

/-- Statements are equal when their numbers are; there are no input oracles. -/
instance : DecidableEq Stmt := fun a b =>
  decidable_of_iff (a.1 = b.1) ⟨fun h => Prod.ext h (funext fun i => i.elim), congrArg Prod.fst⟩

/-- Second-round keys have decidable equality. -/
instance lateKeyDecidableEq : DecidableEq ((Stmt × Fin 8 × Unit) ⊕ (Fin 8 × Unit × Empty)) :=
  inferInstance

instance : DecidableEq (Key Stmt Unit rounds) :=
  inferInstanceAs (DecidableEq ((Stmt × Fin 8 × Unit) ⊕
    (Fin 8 × Unit × ((Stmt × Fin 8 × Unit) ⊕ (Fin 8 × Unit × Empty)))))

/-- The shape of every completed transcript. -/
abbrev shape : Path (protocol rounds) := ⟨⟨⟩, ⟨⟨⟩, ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩⟩⟩

/-- Accept when either challenge is `0`, reading the second payload as the claim. The output
oracle is the second payload. -/
def verifier : OracleVerifier []ₒ (protocol rounds) Nat (Fin 8) emptyFamily outputFamily where
  decide _ p v :=
    if (show Fin 8 from v.1.2.1) = 0 ∨ (show Fin 16 from v.1.2.2.2.1) = 0 then
      liftM (([]ₒ + (sumFamily emptyFamily (pathFamily (protocol rounds) p)).spec).query
        (.inr ⟨.inr (.inr (.inl ⟨⟩)), ()⟩))
    else failure
  outputMap _ p _ :=
    OracleMap.embedding (sumFamily emptyFamily (pathFamily (protocol rounds) p))
      (fun _ => .inr (.inr (.inl ⟨⟩)))

/-- The transcript with messages 5 and 7 and challenges `first` and `second`. -/
def path (first : Fin 8) (second : Fin 16) : PathAlong oracleSig (protocol rounds) :=
  ⟨(5 : Fin 8), ⟨first, ⟨(7 : Fin 8), ⟨second, ⟨⟩⟩⟩⟩⟩

def messages : Messages Unit rounds := ⟨(5 : Fin 8), (), (7 : Fin 8), (), PUnit.unit⟩

/-- The second-round key below first message 5 and input 0. -/
def lateKey : Key Stmt Unit rounds :=
  Key.later (5 : Fin 8) () (Key.here (stmt 0) (7 : Fin 8) ())

/-- Query the later round first, twice, before completing the selected transcript. -/
def adversary : OracleComp (oracleSpec Stmt Unit rounds) (Stmt × Messages Unit rounds × Nat) := do
  let _ ← liftM ((oracleSpec Stmt Unit rounds).query lateKey)
  let _ ← liftM ((oracleSpec Stmt Unit rounds).query lateKey)
  pure ⟨stmt 0, messages, 6⟩

/-- The transcript with messages `m₁`, `m₂` and challenges `c₁`, `c₂`. -/
def transcript (m₁ : Fin 8) (c₁ : Fin 8) (m₂ : Fin 8) (c₂ : Fin 16) :
    PathAlong oracleSig (protocol rounds) :=
  ⟨m₁, ⟨c₁, ⟨m₂, ⟨c₂, ⟨⟩⟩⟩⟩⟩

-- Row 4 (StateRestorationBudget L182, observation): on every transcript, the closed observation
-- returns the second message as the claim and its output oracle when a challenge is `0`, and
-- rejects otherwise.
theorem observation (z : Stmt) (m₁ c₁ m₂ : Fin 8) (c₂ : Fin 16) :
    closedTerminalObservation verifier z (transcript m₁ c₁ m₂ c₂) =
      if c₁ = 0 ∨ c₂ = 0 then some (m₂, fun _ => m₂) else none := by
  simp only [closedTerminalObservation, terminalObservation, OracleVerifier.decideWith, verifier,
    transcript]
  by_cases accepted : c₁ = 0 ∨ c₂ = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true accepted)]
    split
    · rfl
    · contradiction
  · rw [ite_eq_right_of_eq_false _ _ (eq_false accepted)]
    split
    · contradiction
    · rfl

-- Row 13 (StateRestorationBudget L305): the observation values on an accepting and a rejecting
-- path.
/-- info: some (7, 7) -/
#guard_msgs in
#eval (closedTerminalObservation verifier (stmt 0) (path 0 1)).map
  (fun claim => ((claim.1 : Nat), (claim.2 ⟨⟩ : Nat)))

/-- info: none -/
#guard_msgs in
#eval (closedTerminalObservation verifier (stmt 0) (path 1 1)).map
  (fun claim => ((claim.1 : Nat), (claim.2 ⟨⟩ : Nat)))

-- Row 6 (StateRestorationBudget L235, queryBound): the adversary makes two queries.
theorem queryBound : IsTotalQueryBound adversary 2 := by
  unfold adversary
  rw [isTotalQueryBound_query_bind_iff]
  refine ⟨by decide, fun _ => ?_⟩
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun _ => trivial⟩

-- Row 8 (StateRestorationBudget L246, max_errors): the largest round error is `1/8`.
theorem max_errors : Finset.univ.sup errors = (1 / 8 : ENNReal) := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j _
    fin_cases j <;> norm_num [errors]
  · exact Finset.le_sup (f := errors) (Finset.mem_univ (0 : Fin 2))

-- Row 9 (StateRestorationBudget L253, sum_errors): the round errors sum to `3/16`.
theorem sum_errors : (∑ j, errors j) = (3 / 16 : ENNReal) := by
  change (∑ j : Fin 2, errors j) = _
  rw [Fin.sum_univ_two]
  change (1 / 8 : ENNReal) + 1 / 16 = 3 / 16
  have equality : (1 / 8 : NNReal) + 1 / 16 = 3 / 16 := by norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_div (by norm_num : (8 : NNReal) ≠ 0),
    ENNReal.coe_div (by norm_num : (16 : NNReal) ≠ 0), ENNReal.coe_ofNat, ENNReal.coe_one] using
    congrArg (fun x : NNReal => (x : ENNReal)) equality

-- Row 10, cost half (StateRestorationBudget L261, actual_nonuniform_game_bound): the restored
-- execution is charged at most `7/16` on every branch, the budget the frozen game bound uses.
theorem restoredExecution_charge :
    WorstCaseCostBound (restoredExecution rounds adversary)
      (⟨keyError errors⟩ : CostModel (oracleSpec Stmt Unit rounds) ENNReal) (7 / 16) := by
  have general := restoredExecution_round_cost rounds errors adversary 2 queryBound
  have budget : (2 : Nat) * Finset.univ.sup errors + ∑ j, errors j = (7 / 16 : ENNReal) := by
    rw [max_errors, sum_errors]
    have equality : (2 : NNReal) * (1 / 8) + 3 / 16 = 7 / 16 := by norm_num
    simpa only [Nat.cast_ofNat, ENNReal.coe_add, ENNReal.coe_mul,
      ENNReal.coe_div (by norm_num : (8 : NNReal) ≠ 0),
      ENNReal.coe_div (by norm_num : (16 : NNReal) ≠ 0),
      ENNReal.coe_ofNat, ENNReal.coe_one] using
      congrArg (fun x : NNReal => (x : ENNReal)) equality
  rwa [budget] at general

-- The second-round key is charged the second round's error, which is its challenge node's.
example : keyError errors lateKey = 1 / 16 := by
  change errors (1 : Fin 2) = 1 / 16
  simp [errors]

example : keyError errors lateKey = roundEps errors (keyNode lateKey) :=
  keyError_eq_roundEps errors lateKey

-- Row 11 (StateRestorationBudget L284): `7/16` is strictly below the uniform bound
-- `(2 + rounds.length) * (1/8)`.
example : (7 / 16 : ENNReal) < (2 + rounds.length) * (1 / 8) := by
  have better : (7 / 16 : NNReal) < 4 * (1 / 8) := by norm_num
  have coefficient : (2 : ENNReal) + rounds.length = 4 := by norm_num [rounds]
  rw [coefficient]
  simpa only [ENNReal.coe_mul, ENNReal.coe_div (by norm_num : (8 : NNReal) ≠ 0),
    ENNReal.coe_div (by norm_num : (16 : NNReal) ≠ 0), ENNReal.coe_ofNat, ENNReal.coe_one]
    using ENNReal.coe_lt_coe.mpr better


/-! ### The knowledge state function -/

/-- The input relation: the witness is at most the input number. -/
def Rin (z : Stmt) (w : Nat) : Prop := w ≤ z.1

/-- A valid output: a challenge is `0` and the witness is at most the second message. -/
def valid (_ : Stmt) (tr : PathAlong oracleSig (protocol rounds)) (w : Nat) : Prop :=
  ((show Fin 8 from tr.2.1) = 0 ∨ (show Fin 16 from tr.2.2.2.1) = 0) ∧
    w ≤ (show Fin 8 from tr.2.2.1).val

/-- Before any move a witness is at most the input; after the first message no witness is known;
after the first challenge `c₁` a witness is known when `c₁` is `0`; after the second challenge a
witness is known when a challenge is `0` and it is at most the second message. Extraction adds the
message at each message step and copies the witness otherwise. -/
def knowledge : KnowledgeStateFunction oracleSig (protocol rounds) Stmt (fun _ => Nat) Nat
    (fun _ => True) Rin valid where
  Witness _ _ := Nat
  toFun sp history z w := match sp, history with
    | .root _, _ => w ≤ z.1
    | .down _ (.root _), _ => False
    | .down _ (.down _ (.root _)), history => (show Fin 8 from history.2.1.1) = 0
    | .down _ (.down _ (.down _ (.root _))), history => (show Fin 8 from history.2.1.1) = 0
    | .down _ (.down _ (.down _ (.down _ _))), history =>
      ((show Fin 8 from history.2.1.1) = 0 ∨ (show Fin 16 from history.2.2.2.1.1) = 0) ∧
        w ≤ (show Fin 8 from history.2.2.1.1).val
  extractRoot _ w := w
  extractStep sp _ _ x w := by
    cases sp with
    | root => exact w + (show Fin 8 from x).val
    | down _ tail =>
      cases tail with
      | root => exact w
      | down _ tail =>
        cases tail with
        | root => exact w + (show Fin 8 from x).val
        | down _ tail =>
          cases tail with
          | root => exact w
          | down _ tail => cases tail
  extractLeaf _ _ _ w := w
  root _ _ _ h := h
  send sp _ _ h _ _ hw := by
    cases sp with
    | root => exact hw.elim
    | down _ tail =>
      cases tail with
      | root => cases h
      | down _ tail =>
        cases tail with
        | root => exact hw
        | down _ tail =>
          cases tail with
          | root => cases h
          | down _ tail => cases tail
  leaf sp history _ _ hvalid := by
    cases sp with
    | down _ tail =>
      cases tail with
      | down _ tail =>
        cases tail with
        | down _ tail =>
          cases tail with
          | down _ tail =>
            cases tail
            rcases history with ⟨⟨m₁, ⟨⟩⟩, ⟨⟨c₁, ⟨⟩⟩, ⟨⟨m₂, ⟨⟩⟩, ⟨⟨c₂, ⟨⟩⟩, ⟨⟩⟩⟩⟩⟩
            exact hvalid

/-- The full moves after the first message `m₁` and the first challenge `c₁`. -/
abbrev middleMoves (m₁ c₁ : Fin 8) :
    PrefixMoves oracleSig (s := protocol rounds) (.down ⟨⟩ (.down ⟨⟩ (.root _))) :=
  ⟨⟨m₁, rfl⟩, ⟨⟨c₁, rfl⟩, ⟨⟩⟩⟩

/-- The full moves after the messages `m₁`, `m₂` and the first challenge `c₁`. -/
abbrev lateMoves (m₁ c₁ m₂ : Fin 8) :
    PrefixMoves oracleSig (s := protocol rounds) (.down ⟨⟩ (.down ⟨⟩ (.down ⟨⟩ (.root _)))) :=
  ⟨⟨m₁, rfl⟩, ⟨⟨c₁, rfl⟩, ⟨⟨m₂, rfl⟩, ⟨⟩⟩⟩⟩

-- Row 1 (StateRestorationBudget L91, preserving): the send law at both messages, the only prover
-- moves. No witness is known after the first message; at the second message the state after the
-- message implies the state before it on the extracted witness.
theorem preserving :
    (∀ (z : Stmt) (m₁ : Fin 8) (w : Nat),
      ¬ knowledge.toFun (.down ⟨⟩ (.root _)) ⟨⟨m₁, rfl⟩, ⟨⟩⟩ z w) ∧
    ∀ (z : Stmt) (m₁ c₁ m₂ : Fin 8) (w : Nat),
      knowledge.toFun _ (lateMoves m₁ c₁ m₂) z w →
        knowledge.toFun _ (middleMoves m₁ c₁) z
          (knowledge.extractStep _ (middleMoves m₁ c₁) z m₂ w) :=
  ⟨fun _ _ _ => id, fun _ _ _ _ _ known => known⟩

/-- The receiver cursor at the first challenge, below the first message. -/
abbrev firstChallenge : Cursor.Spine (protocol rounds)
    (.liftBind (OraclePos.challenge (Fin 8)) (fun _ => protocol [secondRound])) :=
  .down ⟨⟩ (.root _)

/-- The receiver cursor at the second challenge, below the first round and the second message. -/
abbrev secondChallenge : Cursor.Spine (protocol rounds)
    (.liftBind (OraclePos.challenge (Fin 16)) (fun _ => protocol [])) :=
  .down ⟨⟩ (.down ⟨⟩ (.down ⟨⟩ (.root _)))

theorem uniform_zero_eight : 𝒟[($ᵗ Fin 8 : ProbComp (Fin 8))] {0} = 1 / 8 := by
  rw [SampleableType.evalDist_uniformSample_singleton, one_div]
  simp

theorem uniform_zero_sixteen : 𝒟[($ᵗ Fin 16 : ProbComp (Fin 16))] {0} = 1 / 16 := by
  rw [SampleableType.evalDist_uniformSample_singleton, one_div]
  simp

-- Row 2 (StateRestorationBudget L104, bounded): the state function is locally bounded by the
-- round errors, `1/8` at the first challenge and `1/16` at the second.
theorem bounded : knowledge.LocallyBounded (uniformDraw rounds) (roundEps errors) := by
  intro z _ a next sp h history
  cases sp with
  | root => cases h
  | down _ tail =>
    cases tail with
    | root =>
      rcases history with ⟨⟨m₁, ⟨⟩⟩, ⟨⟩⟩
      have hset : knowledge.badChallenge firstChallenge ⟨⟨m₁, rfl⟩, ⟨⟩⟩ z =
          ({(0 : Fin 8)} : Set (Fin 8)) := by
        ext c
        constructor
        · rintro ⟨_, _, known⟩
          exact known
        · intro isZero
          exact ⟨(0 : Nat), id, isZero⟩
      have hsample : sampleAt oracleSig (uniformDraw rounds) firstChallenge rfl = ($ᵗ Fin 8) :=
        sampleAt_keySpine (Key.here (Salt := Unit) z m₁ ())
      have eighth : (letI : MeasurableSpace (Move oracleSig (OraclePos.challenge (Fin 8))) := ⊤
          𝒟[sampleAt oracleSig (uniformDraw rounds) firstChallenge rfl]
            (knowledge.badChallenge firstChallenge ⟨⟨m₁, rfl⟩, ⟨⟩⟩ z)) = 1 / 8 := by
        simp only
        rw [hsample, hset]
        exact uniform_zero_eight
      exact eighth.le
    | down _ tail =>
      cases tail with
      | root => cases h
      | down _ tail =>
        cases tail with
        | root =>
          rcases history with ⟨⟨m₁, ⟨⟩⟩, ⟨⟨c₁, ⟨⟩⟩, ⟨⟨m₂, ⟨⟩⟩, ⟨⟩⟩⟩⟩
          have hsubset : knowledge.badChallenge secondChallenge (lateMoves m₁ c₁ m₂) z ⊆
              ({(0 : Fin 16)} : Set (Fin 16)) := by
            rintro c ⟨_, notZero, known | known, _⟩
            · exact (notZero known).elim
            · exact known
          have hsample : sampleAt oracleSig (uniformDraw rounds) secondChallenge rfl =
              ($ᵗ Fin 16) :=
            sampleAt_keySpine (Key.later (Salt := Unit) (round := firstRound) m₁ ()
              (Key.here z m₂ ()))
          have sixteenth :
              (letI : MeasurableSpace (Move oracleSig (OraclePos.challenge (Fin 16))) := ⊤
              𝒟[sampleAt oracleSig (uniformDraw rounds) secondChallenge rfl]
                (knowledge.badChallenge secondChallenge (lateMoves m₁ c₁ m₂) z)) ≤ 1 / 16 := by
            rw [hsample, ← uniform_zero_sixteen]
            exact MeasureTheory.measure_mono hsubset
          exact sixteenth
        | down _ tail => cases tail

-- Row 3 (StateRestorationBudget L176, inputLaw): the root state is the input relation.
theorem inputLaw (z : Stmt) (w : Nat) : knowledge.toFun (.root _) ⟨⟩ z w ↔ Rin z w := Iff.rfl

/-- The oracle output relation: the witness is at most the output oracle's data. -/
def oracleRout (_ : Stmt) (_ : PathAlong oracleSig (protocol rounds))
    (claim : Fin 8 × (PUnit.{1} → Fin 8)) (w : Nat) : Prop :=
  w ≤ (claim.2 ⟨⟩).val

-- Row 5 (StateRestorationBudget L198, outputLaw): on every transcript, the terminal state on the
-- terminal witness is an accepted closed claim related to the witness.
theorem outputLaw (z : Stmt) (tr : PathAlong oracleSig (protocol rounds)) (w : Nat) :
    knowledge.toFun (completeSpine oracleSig tr) (completeMoves oracleSig tr) z
      (knowledge.terminalWitness z tr w) ↔
      ∃ claim, closedTerminalObservation verifier z tr = some claim ∧ oracleRout z tr claim w := by
  rcases tr with ⟨m₁, ⟨c₁, ⟨m₂, ⟨c₂, ⟨⟩⟩⟩⟩⟩
  change Fin 8 at m₁ c₁ m₂
  change Fin 16 at c₂
  change ((c₁ = 0 ∨ c₂ = 0) ∧ w ≤ m₂.val) ↔
    ∃ claim, closedTerminalObservation verifier z (transcript m₁ c₁ m₂ c₂) = some claim ∧ _
  rw [observation]
  by_cases accepted : c₁ = 0 ∨ c₂ = 0
  · simp [accepted, oracleRout]
  · simp [accepted]

theorem closedOutputLaw (z : Stmt) (tr : PathAlong oracleSig (protocol rounds))
    (claim : Fin 8 × (PUnit.{1} → Fin 8)) (w : Nat)
    (accepted : closedTerminalObservation verifier z tr = some claim)
    (related : oracleRout z tr claim w) : valid z tr w := by
  have known := (outputLaw z tr w).mpr ⟨claim, accepted, related⟩
  rcases tr with ⟨m₁, ⟨c₁, ⟨m₂, ⟨c₂, ⟨⟩⟩⟩⟩⟩
  exact known

-- Row 7 (StateRestorationBudget L242): extraction along the path from output witness 6 is
-- `6 + 7 + 5`, on every challenge.
example (first : Fin 8) (second : Fin 16) :
    knowledge.extractAlong (stmt 0) (path first second) 6 = 18 := rfl

-- Row 14 (StateRestorationBudget L308): the extracted input witness.
/-- info: 18 -/
#guard_msgs in
#eval knowledge.extractAlong (stmt 0) (path 0 1) 6

/-- The closed knowledge error is at most `7/16`. -/
theorem budget_value :
    (2 : Nat) * Finset.univ.sup errors + ∑ j, errors j = (7 / 16 : ENNReal) := by
  rw [max_errors, sum_errors]
  have equality : (2 : NNReal) * (1 / 8) + 3 / 16 = 7 / 16 := by norm_num
  simpa only [Nat.cast_ofNat, ENNReal.coe_add, ENNReal.coe_mul,
    ENNReal.coe_div (by norm_num : (8 : NNReal) ≠ 0),
    ENNReal.coe_div (by norm_num : (16 : NNReal) ≠ 0),
    ENNReal.coe_ofNat, ENNReal.coe_one] using
    congrArg (fun x : NNReal => (x : ENNReal)) equality

-- Row 10 (StateRestorationBudget L261, actual_nonuniform_game_bound): the closed game has
-- knowledge error at most `2 * (1/8) + (1/8 + 1/16) = 7/16` for the two-query adversary.
theorem actual_nonuniform_game_bound :
    Pr{let result ← (simulateQ randomOracle (closedVerificationGame verifier adversary)).run' ∅}[
      True ∧ (∃ claim, result.2.2.1 = some claim ∧ oracleRout result.1 result.2.1 claim
        result.2.2.2) ∧
      ¬ Rin result.1 (knowledge.extractAlong result.1 result.2.1 result.2.2.2)] ≤ 7 / 16 := by
  have general := stateRestoration_oracle_knowledge_soundness_nonuniform verifier oracleRout
    knowledge (fun _ _ w => w) closedOutputLaw errors bounded adversary 2 queryBound
  rwa [budget_value] at general

-- Row 12 (StateRestorationBudget L292): the bad event is reachable: on `path 0 1` the claim is
-- accepted and related to witness 6, and extraction from input 0 fails.
example : ∃ claim, closedTerminalObservation verifier (stmt 0) (path 0 1) = some claim ∧
    oracleRout (stmt 0) (path 0 1) claim 6 ∧
    ¬ Rin (stmt 0) (knowledge.extractAlong (stmt 0) (path 0 1) 6) := by
  refine ⟨((7 : Fin 8), fun _ => (7 : Fin 8)), ?_, ?_, ?_⟩
  · rw [show path 0 1 = transcript 5 0 7 1 from rfl, observation]
    simp
  · change 6 ≤ 7
    omega
  · change ¬ (18 ≤ 0)
    omega

/-! ### Measured extraction -/

section Measured

/-- The message stages add the actual oracle message to the later witness with one charged
addition; the challenge stages copy the witness uncharged. -/
def stages : knowledge.MeasuredStages (Unit → Nat) where
  root _ := BudgetedProgram.ofFun _
  step z _ _ sp history := by
    cases sp with
    | root =>
      exact ⟨addCountProgram fun x : knowledge.StageInput (.root _) history =>
          (x.2, (show Fin 8 from x.1).val), 1, addCountProgram_realizes _,
        addCountProgram_costAtMost_one _⟩
    | down _ tail =>
      cases tail with
      | root => exact BudgetedProgram.ofFun _
      | down _ tail =>
        cases tail with
        | root =>
          exact ⟨addCountProgram fun x : knowledge.StageInput _ history =>
              (x.2, (show Fin 8 from x.1).val), 1, addCountProgram_realizes _,
            addCountProgram_costAtMost_one _⟩
        | down _ tail =>
          cases tail with
          | root => exact BudgetedProgram.ofFun _
          | down _ tail => cases tail
  leaf _ _ _ := BudgetedProgram.ofFun _

-- Row 15 (StateRestorationBudget L338): the challenge stage maps copy the witness, at both
-- challenges and on every prefix.
example (z : Stmt) (m₁ c₁ m₂ : Fin 8) (c₂ : Fin 16) (w : Nat) :
    knowledge.stageMap z firstChallenge ⟨⟨m₁, rfl⟩, ⟨⟩⟩ ⟨c₁, w⟩ = w ∧
      knowledge.stageMap z secondChallenge (lateMoves m₁ c₁ m₂) ⟨c₂, w⟩ = w :=
  ⟨rfl, rfl⟩

-- The message stage maps add the message.
example (z : Stmt) (m₁ c₁ m₂ : Fin 8) (w : Nat) :
    knowledge.stageMap z (.root _) ⟨⟩ ⟨m₁, w⟩ = w + m₁.val ∧
      knowledge.stageMap z _ (middleMoves m₁ c₁) ⟨m₂, w⟩ = w + m₂.val :=
  ⟨rfl, rfl⟩

-- Row 16 (StateRestorationBudget L353): the stage budgets are one, zero, one and zero along every
-- prefix, and the root and leaf stages are uncharged.
example (z : Stmt) (m₁ c₁ m₂ : Fin 8) :
    (stages.step z (.root _) ⟨⟩).budget = 1 ∧
      (stages.step z firstChallenge ⟨⟨m₁, rfl⟩, ⟨⟩⟩).budget = 0 ∧
      (stages.step z _ (middleMoves m₁ c₁)).budget = 1 ∧
      (stages.step z secondChallenge (lateMoves m₁ c₁ m₂)).budget = 0 ∧
      (stages.root z).budget = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

-- Row 17 (StateRestorationBudget L360, stages_budgetAtMost_one): every step stage costs at most
-- one addition; the root and leaf stages cost none.
theorem stages_budgetAtMost_one : stages.BudgetAtMost 0 1 0 where
  root _ := le_rfl
  step _ _ _ sp _ := by
    cases sp with
    | root => exact le_rfl
    | down _ tail =>
      cases tail with
      | root => exact fun _ => Nat.zero_le 1
      | down _ tail =>
        cases tail with
        | root => exact le_rfl
        | down _ tail =>
          cases tail with
          | root => exact fun _ => Nat.zero_le 1
          | down _ tail => cases tail
  leaf _ _ _ := le_rfl

-- Row 18 (StateRestorationBudget L365, stages_protocolBudgetAtMost): each round has one charged
-- message stage and an uncharged challenge stage, at every statement.
theorem stages_protocolBudgetAtMost (z : Stmt) : stages.ProtocolBudgetAtMost z 0 1 0 0 where
  root := le_rfl
  step sp _ := by
    cases sp with
    | root => exact le_rfl
    | down _ tail =>
      cases tail with
      | root => exact le_rfl
      | down _ tail =>
        cases tail with
        | root => exact le_rfl
        | down _ tail =>
          cases tail with
          | root => exact le_rfl
          | down _ tail => cases tail
  leaf _ _ := le_rfl

-- Row 19 (StateRestorationBudget L369): the common stage bound gives the coarser protocol bound
-- with equal message and challenge budgets, on every statement and transcript.
example (z : Stmt) (tr : PathAlong oracleSig (protocol rounds)) :
    (stages.programAlong z tr).program.CostAtMost
      (0 + rounds.length • ((1 : Unit → Nat) + 1) + 0) :=
  stages.programAlong_costAtMost_protocol (stages_budgetAtMost_one.protocolBudgetAtMost z) tr

-- Row 20 (StateRestorationBudget L381, extractionProgram_budget): the composed program has
-- budget two on every statement and transcript.
theorem extractionProgram_budget (z : Stmt) (tr : PathAlong oracleSig (protocol rounds)) :
    (stages.programAlong z tr).budget = 2 := rfl

-- Row 21 (StateRestorationBudget L385, extractionProgram_costAtMost): every execution of the
-- composed program costs at most two, on every statement and transcript.
theorem extractionProgram_costAtMost (z : Stmt) (tr : PathAlong oracleSig (protocol rounds)) :
    (stages.programAlong z tr).program.CostAtMost 2 := by
  simpa only [extractionProgram_budget] using (stages.programAlong z tr).costAtMost

-- Row 22 (StateRestorationBudget L390): the composed program returns the extracted witness.
example (z : Stmt) (tr : PathAlong oracleSig (protocol rounds)) (w : Nat) :
    (stages.programAlong z tr).program.run w = knowledge.extractAlong z tr w :=
  stages.run_programAlong z tr w

-- Row 23 (StateRestorationBudget L396, extractionProgram_run_inputWitness): on every transcript
-- the composed run adds both messages to the output witness.
theorem extractionProgram_run (z : Stmt) (m₁ c₁ m₂ : Fin 8) (c₂ : Fin 16) (w : Nat) :
    (stages.programAlong z (transcript m₁ c₁ m₂ c₂)).program.run w = w + m₂.val + m₁.val :=
  stages.run_programAlong z _ w

/-- The extracted witness and the recorded count of the composed program. -/
def extractionObservation (z : Stmt) (tr : PathAlong oracleSig (protocol rounds)) (w : Nat) :
    Nat × Nat :=
  let program := (stages.programAlong z tr).program
  (simulateQ ((program.answer (program.view w)).withAddCost program.cost)
    (program.program (program.view w))).runAdd.run.map id (fun count => count ())

-- Row 24 (StateRestorationBudget L410, extractionObservation_cost): every run records the two
-- message additions.
theorem extractionObservation_cost (z : Stmt) (tr : PathAlong oracleSig (protocol rounds))
    (w : Nat) : (extractionObservation z tr w).2 = 2 := by
  rcases tr with ⟨m₁, ⟨c₁, ⟨m₂, ⟨c₂, ⟨⟩⟩⟩⟩⟩
  rfl

-- Row 25 (StateRestorationBudget L417, extractionObservation_result): erasing the recorded cost
-- returns the extracted witness.
theorem extractionObservation_result (z : Stmt) (tr : PathAlong oracleSig (protocol rounds))
    (w : Nat) : (extractionObservation z tr w).1 = knowledge.extractAlong z tr w := by
  rcases tr with ⟨m₁, ⟨c₁, ⟨m₂, ⟨c₂, ⟨⟩⟩⟩⟩⟩
  rfl

/-- The protocol after the first message: the first challenge, then the second round. -/
abbrev afterFirst : OracleProtocol :=
  .liftBind (OraclePos.challenge firstRound.Challenge) (fun _ => protocol [secondRound])

/-- The root cursor of the protocol. -/
abbrev start : Cursor.Spine (protocol rounds) (protocol rounds) := .root _

-- Row 26 (StateRestorationBudget L424, extractionProgram_writer): on every transcript the writer
-- run from the root executes the rest of the transcript before the first message stage.
theorem extractionProgram_writer (z : Stmt) (m₁ : Fin 8) (tr : PathAlong oracleSig afterFirst) :
    let suffix := stages.programFrom z _ (PrefixMoves.snoc oracleSig start ⟨⟩ m₁) tr
    let first := (stages.step z start ⟨⟩).program.contramap
      (fun w : knowledge.Witness _ (PrefixMoves.snoc oracleSig start ⟨⟩ m₁) =>
        (⟨m₁, w⟩ : knowledge.StageInput start ⟨⟩))
    let full := stages.programFrom z start ⟨⟩ ⟨m₁, tr⟩
    ∀ view : suffix.program.View,
      simulateQ ((full.program.answer view).withAddCost full.program.cost)
          (full.program.program view) =
        (do
          let w ← simulateQ ((suffix.program.answer view).withAddCost suffix.program.cost)
            (suffix.program.program view)
          simulateQ ((first.answer (first.view w)).withAddCost first.cost)
            (first.program (first.view w))) := by
  intro suffix first full view
  exact MeasuredProgram.simulateQ_withAddCost_comp first suffix.program view

/-- Checks the composed extraction run and the charges of both message stages. -/
def checkExtractionObservation : IO Unit := do
  let observed := extractionObservation (stmt 0) (path 0 1) 6
  unless observed == (18, 2) do
    throw (IO.userError s!"Unexpected composed extraction result or instruction count: {observed}")
  IO.println "Composed extraction returns witness 18 with two charged additions."

-- Row 27 (StateRestorationBudget L451): the executed observation.
/-- info: Composed extraction returns witness 18 with two charged additions. -/
#guard_msgs in
#eval checkExtractionObservation

-- Row 28 (StateRestorationBudget L455): extraction along a transcript applies the first message's
-- stage map to the witness extracted from the rest, on every transcript.
example (z : Stmt) (m₁ : Fin 8) (tr : PathAlong oracleSig afterFirst) (w : Nat) :
    knowledge.extractAlong z ⟨m₁, tr⟩ w = knowledge.extractRoot z (knowledge.stageMap z start ⟨⟩
      ⟨m₁, knowledge.extractFrom z _ (PrefixMoves.snoc oracleSig start ⟨⟩ m₁) tr w⟩) :=
  congrArg (knowledge.extractRoot z) (knowledge.extractFrom_eq_stageMap z start ⟨⟩ m₁ tr w)

/-- The knowledge state function with its measured stages. -/
def measured : MeasuredKnowledgeStateFunction Unit oracleSig (protocol rounds) Stmt (fun _ => Nat)
    Nat (fun _ => True) Rin valid :=
  { knowledge with stages := stages }

-- Row 29 (StateRestorationBudget L470): the measured state function's underlying state function
-- is the named one.
example : measured.toKnowledgeStateFunction = knowledge := rfl

-- Row 30 (StateRestorationBudget L473): the measured program returns the extracted witness.
example (z : Stmt) (tr : PathAlong oracleSig (protocol rounds)) (w : Nat) :
    (measured.stages.programAlong z tr).program.run w = knowledge.extractAlong z tr w :=
  measured.stages.run_programAlong z tr w

-- Row 31 (StateRestorationBudget L482): the packaged measured theorem gives the closed-game bound
-- and a complete-path instruction bound from the local stage budgets.
example :
    Pr{let result ← (simulateQ randomOracle (closedVerificationGame verifier adversary)).run' ∅}[
      True ∧ (∃ claim, result.2.2.1 = some claim ∧ oracleRout result.1 result.2.1 claim
        result.2.2.2) ∧
      ¬ Rin result.1 (measured.extractAlong result.1 result.2.1 result.2.2.2)] ≤
      2 * Finset.univ.sup errors + ∑ j, errors j ∧
    ∀ z, True → ∀ tr,
      (∀ w, (measured.stages.programAlong z tr).program.run w = measured.extractAlong z tr w) ∧
      (measured.stages.programAlong z tr).program.CostAtMost 2 :=
  MeasuredKnowledgeStateFunction.stateRestoration_oracle_knowledge_soundness_nonuniform verifier
    oracleRout measured (fun _ _ w => w) closedOutputLaw errors bounded (fun _ => 0) (fun _ => 1)
    (fun _ => 0) (fun _ => 0) (fun z _ => stages_protocolBudgetAtMost z) adversary 2 queryBound

-- Row 32 (StateRestorationBudget L502): the same state function has the closed-game bound `7/16`
-- and extraction cost at most two, with the event stated on the composed program's run.
example :
    Pr{let result ← (simulateQ randomOracle (closedVerificationGame verifier adversary)).run' ∅}[
      True ∧ (∃ claim, result.2.2.1 = some claim ∧ oracleRout result.1 result.2.1 claim
        result.2.2.2) ∧
      ¬ Rin result.1 ((stages.programAlong result.1 result.2.1).program.run result.2.2.2)] ≤
      7 / 16 ∧
    ∀ z tr, (stages.programAlong z tr).program.CostAtMost 2 := by
  constructor
  · simpa only [stages.run_programAlong] using actual_nonuniform_game_bound
  · exact extractionProgram_costAtMost

end Measured

end Interaction.Core.StateRestorationBudgetTests
