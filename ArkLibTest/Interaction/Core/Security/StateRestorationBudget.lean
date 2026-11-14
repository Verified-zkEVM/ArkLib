/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Security.StateRestorationBudget
import ArkLibTest.Interaction.Core.Security.StateRestoration
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
def firstRound : Round where
  Message := Fin 8
  Challenge := Fin 8
  interface := messageInterface
  sampleChallenge := inferInstance

/-- The second round: a `Fin 8` oracle message and a `Fin 16` challenge. -/
def secondRound : Round where
  Message := Fin 8
  Challenge := Fin 16
  interface := messageInterface
  sampleChallenge := inferInstance

/-- The protocol has the rounds `firstRound` and `secondRound`. -/
def rounds : List Round := [firstRound, secondRound]

/-- The first round's local error is `1/8`, the second's `1/16`. -/
noncomputable def errors : RoundErrors rounds :=
    fun j : Fin 2 => if j.val = 0 then 1 / 8 else 1 / 16

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

/-- Keys have decidable equality: a key is a first-round triple or a first message and salt above a
second-round key. -/
instance : DecidableEq (Key Stmt Unit rounds) :=
  inferInstanceAs (DecidableEq ((Stmt × Fin 8 × Unit) ⊕
    (Fin 8 × Unit × ((Stmt × Fin 8 × Unit) ⊕ (Fin 8 × Unit × Empty)))))

/-- The shape of every completed transcript. -/
abbrev shape : Path (protocol rounds) := ⟨⟨⟩, ⟨⟨⟩, ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩⟩⟩

/-- Accept when either challenge is `0`, reading the second payload as the claim. The output
oracle is the second payload. -/
def verifier : OracleVerifier.{0, 0, 0, 0, 0, 0, 0} []ₒ (protocol rounds) Nat (fun _ => Fin 8)
    emptyFamily
    (fun _ => outputFamily) where
  decide _ p v :=
    if (show Fin 8 from v.1.2.1) = 0 ∨ (show Fin 16 from v.1.2.2.2.1) = 0 then
      pathLift []ₒ emptyFamily (s := protocol rounds) p ⟨.inr (.inl ⟨⟩), ()⟩
    else failure
  outputMap _ p _ :=
    (OracleMap.embedding (pathFamily (protocol rounds) p)
      (fun _ => .inr (.inl ⟨⟩))).comp (OracleMap.snd _ _)

/-- The transcript with messages 5 and 7 and challenges `first` and `second`. -/
def path (first : Fin 8) (second : Fin 16) : PathAlong oracleSig (protocol rounds) :=
  ⟨(5 : Fin 8), ⟨first, ⟨(7 : Fin 8), ⟨second, ⟨⟩⟩⟩⟩⟩

/-- The selected messages 5 and 7, each with salt `()`. -/
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

-- Row 4 (StateRestorationBudget L182, observation).
/-- On every transcript, the closed observation returns the second message as the claim and its
output oracle when a challenge is `0`, and rejects otherwise. -/
theorem observation (z : Stmt) (m₁ c₁ m₂ : Fin 8) (c₂ : Fin 16) :
    closedTerminalObservation verifier z (transcript m₁ c₁ m₂ c₂) =
      if c₁ = 0 ∨ c₂ = 0 then some (m₂, fun _ => m₂) else none := by
  have view_condition :
      ((show Fin 8 from (toView (protocol rounds) (transcript m₁ c₁ m₂ c₂)).1.2.1) = 0 ∨
        (show Fin 16 from (toView (protocol rounds) (transcript m₁ c₁ m₂ c₂)).1.2.2.2.1) = 0) ↔
        (c₁ = 0 ∨ c₂ = 0) := Iff.rfl
  simp only [closedTerminalObservation, terminalObservation, OracleVerifier.decideWith, verifier,
    view_condition]
  unfold OptionT.run
  by_cases accepted : c₁ = 0 ∨ c₂ = 0
  · erw [ite_eq_left accepted, ite_eq_left accepted]
    rfl
  · erw [ite_eq_right accepted, ite_eq_right accepted]
    rfl

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

-- Row 6 (StateRestorationBudget L235, queryBound).
/-- The adversary makes two queries. -/
theorem queryBound : IsTotalQueryBound adversary 2 := by
  unfold adversary
  rw [isTotalQueryBound_query_bind_iff]
  refine ⟨by decide, fun _ => ?_⟩
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun _ => trivial⟩

-- Row 8 (StateRestorationBudget L246, max_errors).
/-- The largest round error is `1/8`. -/
theorem max_errors : Finset.univ.sup errors = (1 / 8 : ENNReal) := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j _
    fin_cases j <;> norm_num [errors]
  · exact Finset.le_sup (f := errors) (Finset.mem_univ (0 : Fin 2))

-- Row 9 (StateRestorationBudget L253, sum_errors).
/-- The round errors sum to `3/16`. -/
theorem sum_errors : (∑ j, errors j) = (3 / 16 : ENNReal) := by
  refine (Fin.sum_univ_two (fun j : Fin 2 => errors j)).trans ?_
  change (1 / 8 : ENNReal) + 1 / 16 = 3 / 16
  have equality : (1 / 8 : NNReal) + 1 / 16 = 3 / 16 := by norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_div (by norm_num : (8 : NNReal) ≠ 0),
    ENNReal.coe_div (by norm_num : (16 : NNReal) ≠ 0), ENNReal.coe_ofNat, ENNReal.coe_one] using
    congrArg (fun x : NNReal => (x : ENNReal)) equality

-- Row 10, cost half (StateRestorationBudget L261, actual_nonuniform_game_bound).
/-- The restored execution is charged at most `7/16` on every branch, the budget the frozen game
bound uses. -/
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
def knowledge : KnowledgeStateFunction.{0, 0, 0, 0, 1, 0} oracleSig (protocol rounds) Stmt
    (fun _ _ => Nat) (fun _ => Nat) (fun _ => True) Rin valid where
  Witness _ {_} _ _ := Nat
  toFun z {_} sp history w := match sp, history with
    | .root _, _ => w ≤ z.1
    | .down _ (.root _), _ => False
    | .down _ (.down _ (.root _)), history => (show Fin 8 from history.2.1.1) = 0
    | .down _ (.down _ (.down _ (.root _))), history => (show Fin 8 from history.2.1.1) = 0
    | .down _ (.down _ (.down _ (.down _ _))), history =>
      ((show Fin 8 from history.2.1.1) = 0 ∨ (show Fin 16 from history.2.2.2.1.1) = 0) ∧
        w ≤ (show Fin 8 from history.2.2.1.1).val
  extractRoot _ w := w
  extractStep _ {_ _} sp _ x w := by
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

-- Row 1 (StateRestorationBudget L91, preserving).
/-- The send law at both messages, the only prover moves. No witness is known after the first
message; at the second message the state after the message implies the state before it on the
extracted witness. -/
theorem preserving :
    (∀ (z : Stmt) (m₁ : Fin 8) (w : Nat),
      ¬ knowledge.toFun z (.down ⟨⟩ (.root _)) ⟨⟨m₁, rfl⟩, ⟨⟩⟩ w) ∧
    ∀ (z : Stmt) (m₁ c₁ m₂ : Fin 8) (w : Nat),
      knowledge.toFun z _ (lateMoves m₁ c₁ m₂) w →
        knowledge.toFun z _ (middleMoves m₁ c₁)
          (knowledge.extractStep z _ (middleMoves m₁ c₁) m₂ w) :=
  ⟨fun _ _ _ => id, fun _ _ _ _ _ known => known⟩

/-- The receiver cursor at the first challenge, below the first message. -/
abbrev firstChallenge : Cursor.Spine (protocol rounds)
    (.liftBind (OraclePos.challenge (Fin 8)) (fun _ => protocol [secondRound])) :=
  .down ⟨⟩ (.root _)

/-- The receiver cursor at the second challenge, below the first round and the second message. -/
abbrev secondChallenge : Cursor.Spine (protocol rounds)
    (.liftBind (OraclePos.challenge (Fin 16)) (fun _ => protocol [])) :=
  .down ⟨⟩ (.down ⟨⟩ (.down ⟨⟩ (.root _)))

/-- The uniform `Fin 8` is `0` with probability `1/8`. -/
theorem uniform_zero_eight : 𝒟[($ᵗ Fin 8 : ProbComp (Fin 8))] {0} = 1 / 8 := by
  rw [SampleableType.evalDist_uniformSample_singleton, one_div]
  simp

/-- The uniform `Fin 16` is `0` with probability `1/16`. -/
theorem uniform_zero_sixteen : 𝒟[($ᵗ Fin 16 : ProbComp (Fin 16))] {0} = 1 / 16 := by
  rw [SampleableType.evalDist_uniformSample_singleton, one_div]
  simp

-- Row 2 (StateRestorationBudget L104, bounded).
/-- The state function is locally bounded by the round errors, `1/8` at the first challenge and
`1/16` at the second. -/
theorem bounded : knowledge.LocallyBoundedOfNodes (uniformDraw rounds) (roundEps errors) := by
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

-- Row 3 (StateRestorationBudget L176, inputLaw).
/-- The root state is the input relation. -/
theorem inputLaw (z : Stmt) (w : Nat) : knowledge.toFun z (.root _) ⟨⟩ w ↔ Rin z w := Iff.rfl

/-- The oracle output relation: the witness is at most the output oracle's data. -/
def oracleRout (_ : Stmt) (_ : PathAlong oracleSig (protocol rounds))
    (claim : Fin 8 × (PUnit.{1} → Fin 8)) (w : Nat) : Prop :=
  w ≤ (claim.2 ⟨⟩).val

-- Row 5 (StateRestorationBudget L198, outputLaw).
/-- On every transcript, the terminal state on the terminal witness is an accepted closed claim
related to the witness. -/
theorem outputLaw (z : Stmt) (tr : PathAlong oracleSig (protocol rounds)) (w : Nat) :
    knowledge.toFun z (completeSpine oracleSig tr) (completeMoves oracleSig tr)
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

/-- An accepted closed claim related to the witness is a valid output. -/
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

-- Additional evaluation of row 7 (StateRestorationBudget L242): the extracted input witness.
/-- info: 18 -/
#guard_msgs in
#eval knowledge.extractAlong (stmt 0) (path 0 1) 6

/-- The nonuniform error budget, twice the largest round error plus their sum, is `7/16`. -/
theorem budget_value :
    (2 : Nat) * Finset.univ.sup errors + ∑ j, errors j = (7 / 16 : ENNReal) := by
  rw [max_errors, sum_errors]
  have equality : (2 : NNReal) * (1 / 8) + 3 / 16 = 7 / 16 := by norm_num
  simpa only [Nat.cast_ofNat, ENNReal.coe_add, ENNReal.coe_mul,
    ENNReal.coe_div (by norm_num : (8 : NNReal) ≠ 0),
    ENNReal.coe_div (by norm_num : (16 : NNReal) ≠ 0),
    ENNReal.coe_ofNat, ENNReal.coe_one] using
    congrArg (fun x : NNReal => (x : ENNReal)) equality

-- Row 10 (StateRestorationBudget L261, actual_nonuniform_game_bound).
/-- The closed game has knowledge error at most `2 * (1/8) + (1/8 + 1/16) = 7/16` for the two-query
adversary. -/
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
  step z {_ _} sp history := by
    cases sp with
    | root =>
      exact ⟨addCountProgram fun x : knowledge.StageInput z (.root _) history =>
          (x.2, (show Fin 8 from x.1).val), 1, addCountProgram_realizes _,
        addCountProgram_costAtMost_one _⟩
    | down _ tail =>
      cases tail with
      | root => exact BudgetedProgram.ofFun _
      | down _ tail =>
        cases tail with
        | root =>
          exact ⟨addCountProgram fun x : knowledge.StageInput z _ history =>
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

-- Row 17 (StateRestorationBudget L360, stages_budgetAtMost_one).
/-- Every step stage costs at most one addition; the root and leaf stages cost none. -/
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

-- Row 18 (StateRestorationBudget L365, stages_protocolBudgetAtMost).
/-- Each round has one charged message stage and an uncharged challenge stage, at every
statement. -/
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

-- Row 20 (StateRestorationBudget L381, extractionProgram_budget).
/-- The composed program has budget two on every statement and transcript. -/
theorem extractionProgram_budget (z : Stmt) (tr : PathAlong oracleSig (protocol rounds)) :
    (stages.programAlong z tr).budget = 2 := rfl

-- Row 21 (StateRestorationBudget L385, extractionProgram_costAtMost).
/-- Every execution of the composed program costs at most two, on every statement and transcript. -/
theorem extractionProgram_costAtMost (z : Stmt) (tr : PathAlong oracleSig (protocol rounds)) :
    (stages.programAlong z tr).program.CostAtMost 2 := by
  simpa only [extractionProgram_budget] using (stages.programAlong z tr).costAtMost

-- Row 22 (StateRestorationBudget L390): the composed program returns the extracted witness.
example (z : Stmt) (tr : PathAlong oracleSig (protocol rounds)) (w : Nat) :
    (stages.programAlong z tr).program.run w = knowledge.extractAlong z tr w :=
  stages.run_programAlong z tr w

-- Row 23 (StateRestorationBudget L396, extractionProgram_run_inputWitness).
/-- On every transcript the composed run adds both messages to the output witness. -/
theorem extractionProgram_run (z : Stmt) (m₁ c₁ m₂ : Fin 8) (c₂ : Fin 16) (w : Nat) :
    (stages.programAlong z (transcript m₁ c₁ m₂ c₂)).program.run w = w + m₂.val + m₁.val :=
  stages.run_programAlong z _ w

/-- The extracted witness and the recorded count of the composed program. -/
def extractionObservation (z : Stmt) (tr : PathAlong oracleSig (protocol rounds)) (w : Nat) :
    Nat × Nat :=
  let program := (stages.programAlong z tr).program
  (simulateQ ((program.answer (program.view w)).withAddCost program.cost)
    (program.program (program.view w))).runAdd.run.map id (fun count => count ())

-- Row 24 (StateRestorationBudget L410, extractionObservation_cost).
/-- Every run records the two message additions. -/
theorem extractionObservation_cost (z : Stmt) (tr : PathAlong oracleSig (protocol rounds))
    (w : Nat) : (extractionObservation z tr w).2 = 2 := by
  rcases tr with ⟨m₁, ⟨c₁, ⟨m₂, ⟨c₂, ⟨⟩⟩⟩⟩⟩
  rfl

-- Row 25 (StateRestorationBudget L417, extractionObservation_result).
/-- Erasing the recorded cost returns the extracted witness. -/
theorem extractionObservation_result (z : Stmt) (tr : PathAlong oracleSig (protocol rounds))
    (w : Nat) : (extractionObservation z tr w).1 = knowledge.extractAlong z tr w := by
  rcases tr with ⟨m₁, ⟨c₁, ⟨m₂, ⟨c₂, ⟨⟩⟩⟩⟩⟩
  rfl

/-- The protocol after the first message: the first challenge, then the second round. -/
abbrev afterFirst : OracleProtocol :=
  .liftBind (OraclePos.challenge firstRound.Challenge) (fun _ => protocol [secondRound])

/-- The root cursor of the protocol. -/
abbrev start : Cursor.Spine (protocol rounds) (protocol rounds) := .root _

-- Row 26 (StateRestorationBudget L424, extractionProgram_writer).
/-- On every transcript the writer run from the root executes the rest of the transcript before the
first message stage. -/
theorem extractionProgram_writer (z : Stmt) (m₁ : Fin 8) (tr : PathAlong oracleSig afterFirst) :
    let suffix := stages.programFrom z _ (PrefixMoves.snoc oracleSig start ⟨⟩ m₁) tr
    let first := (stages.step z start ⟨⟩).program.contramap
      (fun w : knowledge.Witness z _ (PrefixMoves.snoc oracleSig start ⟨⟩ m₁) =>
        (⟨m₁, w⟩ : knowledge.StageInput z start ⟨⟩))
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
def measured : MeasuredKnowledgeStateFunction Unit oracleSig (protocol rounds) Stmt (fun _ _ => Nat)
    (fun _ => Nat) (fun _ => True) Rin valid :=
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

/-! ### Dependent-output games with a public selector -/

/-- Per-round bounds accept a terminal carrier in `Type 1` with small intermediate witnesses. -/
def largeTerminalKnowledge :
    KnowledgeStateFunction.{0, 0, 0, 1, 1, 0} oracleSig (protocol rounds) Stmt
      (fun _ _ => ULift.{1} Nat) (fun _ => Nat) (fun _ => True)
      (fun z w => ∃ v, Rin z v ∧ v = w) (fun z tr w => valid z tr w.down) :=
  knowledge.comap id (fun _ w => w) (fun _ _ (w : ULift.{1} Nat) => w.down)
    (fun _ _ _ h => h)

/-- A large read-out witness does not change the adaptive adversary's per-round error bound. -/
example :
    Pr{let r ← (simulateQ randomOracle (restoredExecution rounds adversary)).run' ∅}[
      True ∧ valid r.1 r.2.1 r.2.2 ∧
        ¬ (∃ v, Rin r.1 v ∧ v = largeTerminalKnowledge.extractAlong r.1 r.2.1 ⟨r.2.2⟩)] ≤
      2 * Finset.univ.sup errors + ∑ j, errors j :=
  restoredExecution_knowledge_soundness_nonuniform largeTerminalKnowledge errors
    (fun z hz => bounded z hz) (fun _ _ w => ⟨w⟩) adversary 2 queryBound

namespace PublicSelection
open Interaction.Core.StateRestorationTests
  (SelectedValue selectedValue selectedPayload selectedFamily)

/-- A prover-authored selector precedes the original two restoration rounds. -/
abbrev selectedProtocol : OracleProtocol := .liftBind (.message Bool) fun _ => protocol rounds

/-- Query the second payload and return it in the authored carrier. -/
def readSelected (b : Bool) (p : Path (protocol rounds)) :
    OptionT (OracleComp ([]ₒ + (pathResources emptyFamily (protocol rounds) p).spec))
      (SelectedValue b) := do
  let m ← pathLift []ₒ emptyFamily (s := protocol rounds) p ⟨.inr (.inl ⟨⟩), ()⟩
  pure (selectedPayload b m)

/-- The frozen output-oracle family routes the second payload without changing its carrier. -/
def selectedMap (_b : Bool) (p : Path (protocol rounds)) :
    OracleMap (pathResources emptyFamily (protocol rounds) p) outputFamily :=
  (OracleMap.embedding (pathFamily (protocol rounds) p)
    (fun _ => .inr (.inl ⟨⟩))).comp (OracleMap.snd _ _)

/-- Carrier selection is fixed by the authored bit; acceptance still reads both challenges. -/
def suffixVerifier (b : Bool) : OracleVerifier.{0, 0, 0, 0, 0, 0, 0} []ₒ (protocol rounds) Nat
    (fun _ => SelectedValue b) emptyFamily (fun _ => selectedFamily b) where
  decide _ p v :=
    if (show Fin 8 from v.1.2.1) = 0 ∨ (show Fin 16 from v.1.2.2.2.1) = 0 then
      readSelected b p else failure
  outputMap _ p _ := selectedMap b p

/-- The full verifier has a path-dependent statement and the original output oracle. -/
def verifier : OracleVerifier.{0, 0, 0, 0, 0, 0, 0} []ₒ selectedProtocol Nat (fun p =>
    SelectedValue p.1)
    emptyFamily (fun p => selectedFamily p.1) where
  decide _ p v :=
    if (show Fin 8 from v.1.2.2.1) = 0 ∨ (show Fin 16 from v.1.2.2.2.2.1) = 0 then
      readSelected p.1 p.2 else failure
  outputMap _ p _ := selectedMap p.1 p.2

/-- The authored bit is retained alongside every original message and challenge. -/
def selectedTranscript (b : Bool) (m₁ c₁ m₂ : Fin 8) (c₂ : Fin 16) :
    PathAlong oracleSig selectedProtocol := ⟨b, transcript m₁ c₁ m₂ c₂⟩

/-- The accepted statement and its oracle retain the original second-payload value. -/
def returnedClaim (b : Bool) (m : Fin 8) : SelectedValue b × (PUnit.{1} → Fin 8) :=
  (selectedPayload b m, fun _ => m)

/-- All frozen observation quantifiers and the challenge-based acceptance condition are retained. -/
theorem observation (b : Bool) (z : Stmt) (m₁ c₁ m₂ : Fin 8) (c₂ : Fin 16) :
    closedTerminalObservation verifier z (selectedTranscript b m₁ c₁ m₂ c₂) =
      if c₁ = 0 ∨ c₂ = 0 then some (returnedClaim b m₂) else none := by
  simp only [closedTerminalObservation, terminalObservation, OracleVerifier.decideWith, verifier,
    selectedTranscript, transcript]
  by_cases accepted : c₁ = 0 ∨ c₂ = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true accepted)]
    split
    · cases b <;> rfl
    · contradiction
  · rw [ite_eq_right_of_eq_false _ _ (eq_false accepted)]
    split
    · contradiction
    · rfl

/-- The full selected observation equals that of the suffix at the same authored bit. -/
theorem observation_prepend (b : Bool) (z : Stmt)
    (tr : PathAlong oracleSig (protocol rounds)) :
    closedTerminalObservation verifier z ⟨b, tr⟩ =
      closedTerminalObservation (suffixVerifier b) z tr := by
  cases b <;> kernel_rfl

/-- The relation reads the selected output oracle's numerical payload. -/
def relation (b : Bool) (_ : Stmt) (_ : PathAlong oracleSig (protocol rounds))
    (claim : SelectedValue b × (PUnit.{1} → Fin 8)) (w : Nat) : Prop :=
  w ≤ (claim.2 ⟨⟩).val

/-- The selected suffix has exactly the terminal-state equivalence of the frozen game. -/
theorem outputLaw (b : Bool) (z : Stmt) (tr : PathAlong oracleSig (protocol rounds)) (w : Nat) :
    valid z tr w ↔ ∃ claim, closedTerminalObservation (suffixVerifier b) z tr = some claim ∧
      relation b z tr claim w := by
  rcases tr with ⟨m₁, ⟨c₁, ⟨m₂, ⟨c₂, ⟨⟩⟩⟩⟩⟩
  change Fin 8 at m₁ c₁ m₂
  change Fin 16 at c₂
  have obs : closedTerminalObservation (suffixVerifier b) z (transcript m₁ c₁ m₂ c₂) =
      if c₁ = 0 ∨ c₂ = 0 then some (returnedClaim b m₂) else none :=
    observation b z m₁ c₁ m₂ c₂
  change ((c₁ = 0 ∨ c₂ = 0) ∧ w ≤ m₂.val) ↔ _
  erw [obs]
  by_cases accepted : c₁ = 0 ∨ c₂ = 0
  · cases b <;> simp [accepted, relation, returnedClaim, selectedPayload]
  · simp [accepted]

/-- The accepted selected claim supplies the terminal state used in the error theorem. -/
theorem closedOutputLaw (b : Bool) (z : Stmt)
    (tr : PathAlong oracleSig (protocol rounds))
    (claim : SelectedValue b × (PUnit.{1} → Fin 8)) (w : Nat)
    (accepted : closedTerminalObservation (suffixVerifier b) z tr = some claim)
    (related : relation b z tr claim w) : valid z tr w :=
  (outputLaw b z tr w).mpr ⟨claim, accepted, related⟩

/-- Restore the original adversary and evaluate the full dependent verifier after the selector. -/
def game (b : Bool) : OracleComp (oracleSpec Stmt Unit rounds)
    (Stmt × (tr : PathAlong oracleSig selectedProtocol) ×
      Option (SelectedValue tr.1 × (PUnit.{1} → Fin 8)) × Nat) :=
  (fun r => ⟨r.1, ⟨b, r.2.1⟩, closedTerminalObservation verifier r.1 ⟨b, r.2.1⟩, r.2.2⟩) <$>
    restoredExecution rounds adversary

/-- The dependent game retains the sharper error seven sixteenths and the original adversary. -/
theorem actual_nonuniform_game_bound (b : Bool) :
    Pr{let r ← (simulateQ randomOracle (game b)).run' ∅}[
      True ∧ (∃ claim, r.2.2.1 = some claim ∧
        r.2.2.2 ≤ (claim.2 ⟨⟩).val) ∧
      ¬ Rin r.1 (knowledge.extractAlong r.1 r.2.1.2 r.2.2.2)] ≤ 7 / 16 := by
  have h := StateRestoration.stateRestoration_oracle_knowledge_soundness_nonuniform
    (suffixVerifier b) (relation b) knowledge (fun _ _ w => w) (closedOutputLaw b)
    errors bounded adversary 2 queryBound
  erw [closedVerificationGame_eq, simulateQ_map, StateT.run'_map', prEvent_map] at h
  calc
    _ ≤ 2 * Finset.univ.sup errors + ∑ j, errors j := by
      erw [game, simulateQ_map, StateT.run'_map', prEvent_map]
      simp only [relation, Nat.cast_ofNat] at h
      apply le_trans (le_of_eq ?_) h
      congr 1
    _ = 7 / 16 := budget_value

/-- The prover sends its authored selector and the original salted-message selection. -/
def selectedProver (b : Bool) (ms : Messages Unit rounds) :
    Prover oracleSig []ₒ selectedProtocol (fun _ => PUnit.{1}) :=
  pure ⟨b, scriptedProver rounds ms⟩

/-- All full-protocol challenge queries are answered from the original recorded suffix. -/
def selectedAnswers (tr : PathAlong oracleSig (protocol rounds)) :
    QueryImpl ([]ₒ + challengeSpec oracleSig selectedProtocol) Id
  | .inl q => q.elim
  | .inr ⟨.inl _, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, n⟩, h⟩ => recordedChallenges rounds tr ⟨n, h⟩

/-- The selected interaction returns every recorded challenge and both authored messages. -/
theorem selectedInteraction_eq (b : Bool) (ms : Messages Unit rounds)
    (tr : PathAlong oracleSig (protocol rounds)) (carried : MatchesMessages rounds ms tr) :
    evalWithAnswerFn (selectedAnswers tr)
      (TwoParty.Lens.run selectedProtocol
        ((selectedProver b ms).simulate (fun q =>
          liftM (([]ₒ + challengeSpec oracleSig selectedProtocol).query (.inl q))))
        (sampler oracleSig selectedProtocol (fun c =>
          liftM (([]ₒ + challengeSpec oracleSig selectedProtocol).query (.inr c))))) =
      ⟨⟨b, tr⟩, ⟨⟩, ⟨⟩⟩ := by
  rcases tr with ⟨m₁, ⟨c₁, ⟨m₂, ⟨c₂, ⟨⟩⟩⟩⟩⟩
  rcases ms with ⟨n₁, s₁, n₂, s₂, ⟨⟩⟩
  rcases carried with ⟨rfl, rfl, _⟩
  kernel_rfl

/-- Evaluate the selected verifier's terminal action on the actual interaction result. -/
def finishSelected (z : Stmt)
    (answers : QueryImpl ([]ₒ + challengeSpec oracleSig selectedProtocol) Id)
    (r : (_ : PathAlong oracleSig selectedProtocol) × PUnit.{1} × PUnit.{1}) :
    Observation oracleSig selectedProtocol (fun _ => PUnit.{1})
      (OracleVerifier.Output (fun p => SelectedValue p.1) (fun _ (_ : PUnit.{1}) => Fin 8)) :=
  let p := projectPathAlong oracleSig selectedProtocol r.1
  let view := toView selectedProtocol r.1
  let resources : (pathResources emptyFamily selectedProtocol p).Data :=
    (z.2, payloads selectedProtocol r.1)
  let verdict := evalWithAnswerFn answers (simulateQ
    (QueryImpl.addLift
      (((QueryImpl.id' ([]ₒ + challengeSpec oracleSig selectedProtocol)).restrictLeft) :
        QueryImpl []ₒ (OracleComp ([]ₒ + challengeSpec oracleSig selectedProtocol)))
      ((pathResources emptyFamily selectedProtocol p).answer resources))
    (verifier.decide z.1 p view).run)
  ⟨r.1, r.2.1, verdict.map fun t => (t, (verifier.outputMap z.1 p view).f resources)⟩

/-- With no ambient queries, finalization is the full verifier's closed observation. -/
theorem finishSelected_eq (z : Stmt)
    (answers : QueryImpl ([]ₒ + challengeSpec oracleSig selectedProtocol) Id)
    (r : (_ : PathAlong oracleSig selectedProtocol) × PUnit.{1} × PUnit.{1}) :
    finishSelected z answers r =
      ⟨r.1, r.2.1, closedTerminalObservation verifier z r.1⟩ := by
  simp only [finishSelected, evalWithAnswerFn_simulateQ, closedTerminalObservation,
    terminalObservation, OracleVerifier.decideWith]
  congr 4
  funext q
  rcases q with q | q
  · exact q.elim
  · rfl

/-- Authored selection followed by the real parties returns the full dependent observation. -/
theorem run_selectedProver (b : Bool) (z : Stmt) (ms : Messages Unit rounds)
    (tr : PathAlong oracleSig (protocol rounds)) (carried : MatchesMessages rounds ms tr) :
    evalWithAnswerFn (selectedAnswers tr) (verifier.run z.1 z.2 (selectedProver b ms)) =
      ⟨⟨b, tr⟩, ⟨⟩, closedTerminalObservation verifier z ⟨b, tr⟩⟩ := by
  have h := (congrArg (finishSelected z (selectedAnswers tr))
    (selectedInteraction_eq b ms tr carried)).trans (finishSelected_eq _ _ _)
  simp only [OracleVerifier.run_eq, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  dsimp only [finishSelected] at h
  exact h

/-- Every table gives the same full transcript and observation in the dependent game. -/
theorem game_eval (b : Bool) (table : Table Stmt Unit rounds) :
    evalWithAnswerFn (QueryImpl.ofFn table) (game b) =
      let tr := completedPath rounds (stmt 0) messages table
      ⟨stmt 0, ⟨b, tr⟩, closedTerminalObservation verifier (stmt 0) ⟨b, tr⟩, 6⟩ := by
  erw [game, evalWithAnswerFn_map, restoredExecution_eval]
  rfl

/-- The adaptive, repeated-query game agrees with an actual selected-party replay. -/
theorem game_eval_run (b : Bool) (table : Table Stmt Unit rounds) :
    let result := evalWithAnswerFn (QueryImpl.ofFn table) (game b)
    evalWithAnswerFn (selectedAnswers result.2.1.2)
      (verifier.run 0 (stmt 0).2 (selectedProver b messages)) =
        ⟨result.2.1, ⟨⟩, result.2.2.1⟩ := by
  erw [game_eval]
  exact run_selectedProver b (stmt 0) messages _
    (completedPath_matchesMessages rounds _ _ table)

/-- The packaged measured theorem applies to the full dependent-output game and exact programs. -/
theorem measured_game_bound (b : Bool) :
    Pr{let r ← (simulateQ randomOracle (game b)).run' ∅}[
      True ∧ (∃ claim, r.2.2.1 = some claim ∧ r.2.2.2 ≤ (claim.2 ⟨⟩).val) ∧
      ¬ Rin r.1 (measured.extractAlong r.1 r.2.1.2 r.2.2.2)] ≤
      2 * Finset.univ.sup errors + ∑ j, errors j ∧
    ∀ z, True → ∀ tr,
      (∀ w, (measured.stages.programAlong z tr).program.run w = measured.extractAlong z tr w) ∧
      (measured.stages.programAlong z tr).program.CostAtMost 2 := by
  have h := MeasuredKnowledgeStateFunction.stateRestoration_oracle_knowledge_soundness_nonuniform
    (suffixVerifier b) (relation b) measured (fun _ _ w => w) (closedOutputLaw b)
    errors bounded (fun _ => 0) (fun _ => 1) (fun _ => 0) (fun _ => 0)
    (fun z _ => stages_protocolBudgetAtMost z) adversary 2 queryBound
  constructor
  · have hp := h.1
    erw [closedVerificationGame_eq, simulateQ_map, StateT.run'_map', prEvent_map] at hp
    erw [game, simulateQ_map, StateT.run'_map', prEvent_map]
    simp only [relation, Nat.cast_ofNat] at hp
    apply le_trans (le_of_eq ?_) hp
    congr 1
  · exact h.2

/-- The game event uses the actual measured program's result, retaining cost two and error 7/16. -/
theorem program_run_game_bound (b : Bool) :
    Pr{let r ← (simulateQ randomOracle (game b)).run' ∅}[
      True ∧ (∃ claim, r.2.2.1 = some claim ∧ r.2.2.2 ≤ (claim.2 ⟨⟩).val) ∧
      ¬ Rin r.1 ((stages.programAlong r.1 r.2.1.2).program.run r.2.2.2)] ≤ 7 / 16 ∧
    ∀ z tr, (stages.programAlong z tr).program.CostAtMost 2 := by
  constructor
  · simpa only [stages.run_programAlong] using actual_nonuniform_game_bound b
  · exact extractionProgram_costAtMost

/-- The accepting frozen execution still extracts eighteen from the supplied witness six. -/
example (b : Bool) : ∃ claim,
    closedTerminalObservation verifier (stmt 0) (selectedTranscript b 5 0 7 1) = some claim ∧
    6 ≤ (claim.2 ⟨⟩).val ∧ ¬ Rin (stmt 0)
      (knowledge.extractAlong (stmt 0) (path 0 1) 6) := by
  refine ⟨returnedClaim b 7, ?_, ?_, ?_⟩
  · have obs := observation b (stmt 0) 5 0 7 1
    erw [ite_eq_left (Or.inl rfl)] at obs
    exact obs
  · cases b <;> decide
  · change ¬ (18 : Nat) ≤ 0
    omega

/-- info: some (7, 7) -/
#guard_msgs in
#eval (closedTerminalObservation verifier (stmt 0) (selectedTranscript false 5 0 7 1)).map
  (fun claim => (selectedValue false claim.1, (claim.2 ⟨⟩).val))

/-- info: none -/
#guard_msgs in
#eval (closedTerminalObservation verifier (stmt 0) (selectedTranscript true 5 1 7 1)).map
  (fun claim => (selectedValue true claim.1, (claim.2 ⟨⟩).val))

end PublicSelection

end Interaction.Core.StateRestorationBudgetTests

run_cmd do
  for decl in [``KnowledgeStateFunction.MeasuredStages.programAlong_budget_le_protocol_zero,
      ``Interaction.Core.StateRestorationBudgetTests.PublicSelection.observation,
      ``Interaction.Core.StateRestorationBudgetTests.PublicSelection.outputLaw,
      ``Interaction.Core.StateRestorationBudgetTests.PublicSelection.actual_nonuniform_game_bound,
      ``Interaction.Core.StateRestorationBudgetTests.PublicSelection.run_selectedProver,
      ``Interaction.Core.StateRestorationBudgetTests.PublicSelection.game_eval_run,
      ``Interaction.Core.StateRestorationBudgetTests.PublicSelection.measured_game_bound,
      ``Interaction.Core.StateRestorationBudgetTests.PublicSelection.program_run_game_bound] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"
