/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Stages
import ArkLibTest.Interaction.Core.Oracle.CompositionExample

/-!
# A fold of three heterogeneous oracle stages

The first two stages are the prefix and suffix of the composition example, closed with their
prover and verifier. The first stage reads the input oracle, decides its parity and exports the
input plus 11. The second stage takes the `Bool` statement, lets the prover choose a `Nat` or a
`Bool` message, and exports the parity of what it read. The third stage takes the `Nat`
statement and the `Bool` oracle, draws a challenge through an ambient event, checks the prover's
response, and exports the negation of the `Bool` oracle. Each stage changes the statement type,
the oracle data type and the private type.

A stateful logger detects reordered, duplicated or skipped effects. The fold decides each stage
before the next one starts, so its history is `[0, 1, 2, 3, 4, 5, 6]`. The binary composition of
the first two stages runs both interactions before either decision, with history `[0, 2, 1, 3]`.
-/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp Interaction.Core.CompositionExampleTests

namespace Interaction.Core.StagesExampleTests

/-! ## The frozen fold laws at closed stages

Each frozen law of the ordered execution is an instance of a law of `foldStages`, for every family
of closed stages. -/

section FrozenLaws

universe u

variable {ι : Type u} {ambient : OracleSpec.{u, u} ι}

-- The frozen zero law.
example (I : Fin 1 → StageInterface.{u})
    (stages : (i : Fin 0) → ClosedStage ambient (I i.castSucc) (I i.succ))
    (input : (I ⟨0, Nat.zero_lt_succ _⟩).State) :
    ClosedStage.runStages 0 I stages input = pure (some input) :=
  foldStages_zero _ _ _

-- The frozen successor law.
example (n : Nat) (I : Fin (n + 2) → StageInterface.{u})
    (stages : (i : Fin (n + 1)) → ClosedStage ambient (I i.castSucc) (I i.succ))
    (input : (I ⟨0, Nat.zero_lt_succ _⟩).State) :
    ClosedStage.runStages (n + 1) I stages input =
      ((stages ⟨0, Nat.zero_lt_succ _⟩).run input >>= fun r =>
        r.elim (pure none)
          (ClosedStage.runStages n (fun i => I i.succ) (fun i => stages i.succ))) :=
  foldStages_succ _ _ _ _

-- The frozen successor-on-reject law.
example (n : Nat) (I : Fin (n + 2) → StageInterface.{u})
    (stages : (i : Fin (n + 1)) → ClosedStage ambient (I i.castSucc) (I i.succ))
    (input : (I ⟨0, Nat.zero_lt_succ _⟩).State)
    (h : (stages ⟨0, Nat.zero_lt_succ _⟩).run input = pure none) :
    ClosedStage.runStages (n + 1) I stages input = pure none :=
  foldStages_succ_of_reject _ _ _ _ h

-- The frozen split law, with the frozen cast along `m + n = n + m`.
example (m n : Nat) (I : Fin (n + m + 1) → StageInterface.{u})
    (stages : (i : Fin (n + m)) → ClosedStage ambient (I i.castSucc) (I i.succ))
    (input : (I ⟨0, Nat.zero_lt_succ _⟩).State) :
    ClosedStage.runStages (n + m) I stages input =
      (ClosedStage.runStages m (fun i => I ⟨i.val, by omega⟩)
          (fun i => stages ⟨i.val, by omega⟩) input >>= fun mid =>
        Option.elim mid (pure none) fun (value : (I ⟨m, by omega⟩).State) =>
          cast (congrArg (fun j : Fin (n + m + 1) => OracleComp ambient (Option (I j).State))
            (Fin.ext (Nat.add_comm m n) : (⟨m + n, by omega⟩ : Fin (n + m + 1)) =
              Fin.last (n + m)))
            (ClosedStage.runStages n (fun i => I ⟨m + i.val, by omega⟩)
              (fun i => stages ⟨m + i.val, by omega⟩) value)) :=
  foldStages_split m n (n + m) (Nat.add_comm m n) (fun i => (I i).State) (fun i => (stages i).run)
    input

-- The frozen deterministic invariant law.
example (n : Nat) (I : Fin (n + 1) → StageInterface.{u})
    (stages : (i : Fin n) → ClosedStage ambient (I i.castSucc) (I i.succ))
    (Inv : (i : Fin (n + 1)) → (I i).State → Prop)
    (preserves : ∀ (i : Fin n) (input : (I i.castSucc).State), Inv i.castSucc input →
      ∃ output, (stages i).run input = pure (some output) ∧ Inv i.succ output)
    (input : (I ⟨0, Nat.zero_lt_succ _⟩).State) (hinput : Inv ⟨0, Nat.zero_lt_succ _⟩ input) :
    ∃ output, ClosedStage.runStages n I stages input = pure (some output) ∧
      Inv (Fin.last n) output :=
  foldStages_preserves n _ _ Inv preserves input hinput

-- The frozen support invariant law.
example (n : Nat) (I : Fin (n + 1) → StageInterface.{u})
    (stages : (i : Fin n) → ClosedStage ambient (I i.castSucc) (I i.succ))
    (Inv : (i : Fin (n + 1)) → (I i).State → Prop)
    (preserves : ∀ (i : Fin n) (input : (I i.castSucc).State), Inv i.castSucc input →
      ∀ result ∈ support ((stages i).run input),
        ∃ output, result = some output ∧ Inv i.succ output)
    (input : (I ⟨0, Nat.zero_lt_succ _⟩).State) (hinput : Inv ⟨0, Nat.zero_lt_succ _⟩ input) :
    ∀ result ∈ support (ClosedStage.runStages n I stages input),
      ∃ output, result = some output ∧ Inv (Fin.last n) output :=
  foldStages_preserves_support n _ _ Inv preserves input hinput

-- The frozen almost-sure invariant law.
example [ambient.AnswerMeasure] (n : Nat) (I : Fin (n + 1) → StageInterface.{u})
    [∀ i, MeasurableSpace (I i).State] [∀ i, DiscreteMeasurableSpace (I i).State]
    (stages : (i : Fin n) → ClosedStage ambient (I i.castSucc) (I i.succ))
    (Inv : (i : Fin (n + 1)) → (I i).State → Prop)
    (preserves : ∀ (i : Fin n) (input : (I i.castSucc).State), Inv i.castSucc input →
      𝒟[(stages i).run input] {result | ∃ output, result = some output ∧ Inv i.succ output} = 1)
    (input : (I ⟨0, Nat.zero_lt_succ _⟩).State) (hinput : Inv ⟨0, Nat.zero_lt_succ _⟩ input) :
    𝒟[ClosedStage.runStages n I stages input]
      {result | ∃ output, result = some output ∧ Inv (Fin.last n) output} = 1 :=
  foldStages_preserves_measure n _ _ Inv preserves input hinput

end FrozenLaws

/-- The input claim: no statement, one natural-number oracle, and a natural-number private
value. -/
abbrev inputInterface : StageInterface where
  Stmt := Unit
  Index := Unit
  Data := fun _ => Nat
  oracles := naturals
  Private := Nat

/-- After the first stage: a `Bool` statement, the exported natural-number oracle, and a
natural-number private value. -/
abbrev parityInterface : StageInterface where
  Stmt := Bool
  Index := Unit
  Data := fun _ => Nat
  oracles := naturals
  Private := Nat

/-- After the second stage: a `Nat` statement, a `Bool` oracle, and two natural numbers. -/
abbrev valueInterface : StageInterface where
  Stmt := Nat
  Index := Unit
  Data := fun _ => Bool
  oracles := booleans
  Private := Nat × Nat

/-- After the third stage: a pair statement, a `Bool` oracle, and three natural numbers. -/
abbrev finalInterface : StageInterface where
  Stmt := Bool × Nat
  Index := Unit
  Data := fun _ => Bool
  oracles := booleans
  Private := Nat × Nat × Nat

/-- The first stage: no interaction, the prover records 0, the decision records 1. The prover
passes on its hidden value plus 1. -/
def firstStage (accept : Bool) : ClosedStage ambient inputInterface parityInterface where
  protocol _ := done
  draw _ c := c.val.elim
  Out _ _ := Nat × Bool
  prover claim hidden := firstProver (claim.2 () % 2 == 0) hidden
  verifier _ := firstVerifier accept
  nextPrivate _ _ _ out := out.1

/-- The second stage has only message nodes. -/
theorem branchProtocol_noChallenge : ChallengeNode oracleSig branchProtocol → False := by
  rintro ⟨n, h⟩
  rcases n with _ | ⟨b, n⟩
  · exact nomatch h
  · cases b <;> rcases n with _ | ⟨_, n⟩
    all_goals exact nomatch h

/-- The second stage: the prover's first slot records 2 and sends the input statement as its
branch, the decision records 3. The prover keeps its hidden value and its successor. -/
def secondStage : ClosedStage ambient parityInterface valueInterface where
  protocol _ := branchProtocol
  draw _ c := (branchProtocol_noChallenge c).elim
  Out _ _ := Nat × Nat
  prover claim hidden := Strategy.joinSlot (seam (hidden, claim.1))
  verifier _ := secondVerifier
  nextPrivate _ _ _ out := out

/-- A challenge, then the prover's response. -/
@[instance_reducible] def responseProtocol : OracleProtocol :=
  .liftBind (.challenge Nat) (fun _ => .liftBind (.message Nat) (fun _ => .pure ⟨⟩))

/-- The challenge draw records 5 and answers 9. -/
def responseDraw : (c : ChallengeNode oracleSig responseProtocol) →
    OracleComp ambient (challengeSpec oracleSig responseProtocol c)
  | ⟨.inl _, _⟩ => do
    liftM (ambient.query 5)
    pure (9 : Nat)
  | ⟨.inr ⟨_, .inl _⟩, h⟩ => nomatch h
  | ⟨.inr ⟨_, .inr ⟨_, n⟩⟩, _⟩ => n.elim

/-- The decision resources on a path of `responseProtocol`. -/
abbrev responseResources (p : Path responseProtocol) :=
  sumFamily booleans (pathFamily responseProtocol p)

/-- Export the negation of the `Bool` input oracle. -/
def negate (p : Path responseProtocol) : OracleMap (responseResources p) booleans where
  f x _ := !(show Bool from x (.inl ()))
  impl _ := do
    let b : Bool ← liftM ((responseResources p).spec.query ⟨.inl (), ()⟩)
    pure !b
  law _ _ := by
    simp only [simulateQ_bind]
    rfl

/-- The decision records 6, reads the input oracle, and accepts the oracle answer with the
statement plus the response if the response is the challenge plus 1. -/
def responseVerifier : OracleVerifier ambient responseProtocol Nat (fun _ => Bool × Nat) booleans
    (fun _ => booleans) where
  decide stmt p v := OptionT.mk do
    let _ ← liftM ((ambient + (responseResources p).spec).query (.inl 6))
    let b : Bool ← liftM ((ambient + (responseResources p).spec).query (.inr ⟨.inl (), ()⟩))
    let challenge : Nat := v.val.1
    let response : Nat := v.val.2.1
    pure (if response = challenge + 1 then some (b, stmt + response) else none)
  outputMap _ p _ := negate p

/-- The prover records 4, answers the challenge with its successor, and adds the challenge to its
private memory. -/
def responseProver (memory : Nat × Nat) :
    Prover oracleSig ambient responseProtocol (fun _ => Nat × Nat × Nat) := do
  liftM (ambient.query 4)
  pure fun (challenge : Nat) => pure ⟨challenge + 1, pure (memory.1, memory.2, challenge)⟩

/-- The third stage: it samples a challenge, unlike the first two. -/
def thirdStage : ClosedStage ambient valueInterface finalInterface where
  protocol _ := responseProtocol
  draw _ := responseDraw
  Out _ _ := Nat × Nat × Nat
  prover _ memory := responseProver memory
  verifier _ := responseVerifier
  nextPrivate _ _ _ out := out

-- CompositionExample 1, restated: the normal form of the first stage, for every verdict, input
-- data and hidden value.
/-- The first stage records 0 and 1, then accepts the input's parity with the input plus 11. -/
theorem firstStage_run (accept : Bool) (answers : ∀ _ : Unit, Nat) (hidden : Nat) :
    (firstStage accept).run (((), answers), hidden) = (do
      liftM (ambient.query 0)
      liftM (ambient.query 1)
      pure (if accept then some ((answers () % 2 == 0, fun _ => answers () + 11), hidden + 1)
        else none)) := by
  cases accept <;> rfl

-- CompositionExample 2, restated: the normal form of the second stage on both message types, for
-- every input statement, input data and hidden value.
/-- The second stage records 2 and 3, then accepts the message value plus the input. -/
theorem secondStage_run (choice : Bool) (answers : ∀ _ : Unit, Nat) (hidden : Nat) :
    secondStage.run ((choice, answers), hidden) = (do
      liftM (ambient.query 2)
      liftM (ambient.query 3)
      pure (some (((if choice then hidden else if decide (hidden > 0) then 100 else 200) +
          answers (), fun _ => answers () % 2 == 0), (hidden, hidden + 1)))) := by
  cases choice <;> rfl

/-- The third stage records 4, 5 and 6, then accepts the input oracle with the statement plus the
response 10. -/
theorem thirdStage_run (value : Nat) (answers : ∀ _ : Unit, Bool) (memory : Nat × Nat) :
    thirdStage.run ((value, answers), memory) = (do
      liftM (ambient.query 4)
      liftM (ambient.query 5)
      liftM (ambient.query 6)
      pure (some (((answers (), value + 10), fun _ => !answers ()),
        (memory.1, memory.2, 9)))) := rfl

/-- The interfaces at the four stage boundaries. -/
@[reducible] def interfaces (i : Fin 4) : StageInterface :=
  match i.val with
  | 0 => inputInterface
  | 1 => parityInterface
  | 2 => valueInterface
  | _ => finalInterface

/-- The three stages, indexed by their position. -/
def stages (accept : Bool) :
    (i : Fin 3) → ClosedStage ambient (interfaces i.castSucc) (interfaces i.succ) :=
  Fin.cons (firstStage accept) (Fin.cons secondStage (Fin.cons thirdStage fun i => Fin.elim0 i))

/-- The first stage of the family. -/
@[simp] theorem stages_zero (accept : Bool) : stages accept 0 = firstStage accept := rfl

/-- The second stage of the family. -/
@[simp] theorem stages_one (accept : Bool) : stages accept 1 = secondStage := rfl

/-- The third stage of the family. -/
@[simp] theorem stages_two (accept : Bool) : stages accept 2 = thirdStage := rfl

/-- Log each ambient event. -/
def logger : QueryImpl ambient (StateM (List Nat))
  | tag => modify (· ++ [tag])

/-! ## The frozen two-stage family -/

/-- The boundary interfaces of the first two stages. -/
abbrev twoInterfaces (i : Fin 3) : StageInterface := interfaces i.castSucc

/-- The first two stages, as a family of their own. -/
def twoStages (accept : Bool) :
    (i : Fin 2) → ClosedStage ambient (twoInterfaces i.castSucc) (twoInterfaces i.succ) :=
  Fin.cons (firstStage accept) (Fin.cons secondStage fun i => Fin.elim0 i)

-- CompositionExample 3, restated: the family resolves its first index.
/-- The first stage of the two-stage family. -/
@[simp] theorem twoStages_zero (accept : Bool) : twoStages accept 0 = firstStage accept := rfl

-- CompositionExample 4, restated: the family resolves its second index.
/-- The second stage of the two-stage family. -/
@[simp] theorem twoStages_one (accept : Bool) : twoStages accept 1 = secondStage := rfl

/-- The fold of the first two stages. -/
def runTwo (accept : Bool) :=
  ClosedStage.runStages 2 twoInterfaces (twoStages accept)

-- CompositionExample 5, restated: the fold runs the second stage only after the first accepts.
/-- The fold of the two-stage family, resolved into its two stage runs. -/
theorem run_two (accept : Bool) (input : inputInterface.State) :
    runTwo accept input =
      ((firstStage accept).run input >>= fun r => r.elim (pure none) secondStage.run) := by
  rw [runTwo, ClosedStage.runStages, foldStages_succ]
  refine bind_congr fun r => ?_
  cases r with
  | none => rfl
  | some mid =>
    simp only [Option.elim]
    exact foldStages_one _ _ _

/-- The claim and private output after the first two stages, with the history. -/
def observedTwo (accept : Bool) (answer hidden : Nat) : Option valueInterface.State × List Nat :=
  (simulateQ logger (runTwo accept (((), fun _ => answer), hidden))).run []

-- CompositionExample 6, restated: the normal form of the accepted two-stage fold, for every input
-- and hidden value. Each stage decides before the next one starts.
/-- The accepted fold of the two stages. -/
theorem observedTwo_true (answer hidden : Nat) :
    observedTwo true answer hidden =
      (some (((if answer % 2 == 0 then hidden + 1
          else if decide (hidden + 1 > 0) then 100 else 200) + (answer + 11),
          fun _ => (answer + 11) % 2 == 0), (hidden + 1, hidden + 1 + 1)), [0, 1, 2, 3]) := by
  unfold observedTwo
  rw [run_two, firstStage_run]
  simp only [bind_assoc, LawfulMonad.pure_bind, ↓reduceIte, Option.elim]
  rw [secondStage_run]
  rfl

-- CompositionExample 7, restated: every effect runs exactly once, in the order `[0, 1, 2, 3]`.
-- The binary composition of the same two stages gives `[0, 2, 1, 3]` instead, because it runs
-- both interactions before either decision.
example : (observedTwo true 7 40).2 = [0, 1, 2, 3] := by rw [observedTwo_true]

-- CompositionExample 8, restated: the odd input selects the `Bool` branch; the statement is 100
-- plus the exported 7 + 11.
example : (observedTwo true 7 40).1.map (·.1.1) = some 118 := by
  rw [observedTwo_true]
  rfl

-- CompositionExample 9, restated: the even input selects the `Nat` branch; the statement is the
-- hidden value 41 plus the exported 20 + 11.
example : (observedTwo true 20 40).1.map (·.1.1) = some 72 := by
  rw [observedTwo_true]
  rfl

-- CompositionExample 10, restated: the exported Boolean oracle is the parity of the exported 18.
example : (observedTwo true 7 40).1.map (·.1.2 ()) = some true := by
  rw [observedTwo_true]
  rfl

-- CompositionExample 11, restated: changing the input changes the final oracle.
example : (observedTwo true 20 40).1.map (·.1.2 ()) = some false := by
  rw [observedTwo_true]
  rfl

-- CompositionExample 12, restated: the private outputs cross the handoff, distinct from the
-- public statements.
example : (observedTwo true 7 40).1.map Prod.snd = some (41, 42) := by
  rw [observedTwo_true]
  rfl

-- CompositionExample 13, restated: a rejecting first stage yields no claim and runs neither of
-- the second stage's events 2 and 3.
example : observedTwo false 7 40 = (none, [0, 1]) := rfl

/-! ## Three heterogeneous stages

The third stage samples a challenge and changes all three types again. -/

/-- The fold of the three stages. -/
def run (accept : Bool) :=
  ClosedStage.runStages 3 interfaces (stages accept)

/-- The fold of the three-stage family, resolved into its three stage runs. -/
theorem run_three (accept : Bool) (input : inputInterface.State) :
    run accept input = ((firstStage accept).run input >>= fun r =>
      r.elim (pure none) fun mid => secondStage.run mid >>= fun r =>
        r.elim (pure none) thirdStage.run) := by
  rw [run, ClosedStage.runStages, foldStages_succ]
  refine bind_congr fun r => ?_
  cases r with
  | none => rfl
  | some mid =>
    simp only [Option.elim]
    rw [foldStages_succ]
    refine bind_congr fun r => ?_
    cases r with
    | none => rfl
    | some value =>
      simp only [Option.elim]
      exact foldStages_one _ _ _

-- The split law at this family: the first stage, then the fold of the other two.
example (accept : Bool) (input : inputInterface.State) :=
  foldStages_add 1 2 (fun i => (interfaces i).State) (fun i => (stages accept i).run) input

/-- The final claim and private output of the fold, with the history. -/
def observed (accept : Bool) (answer hidden : Nat) : Option finalInterface.State × List Nat :=
  (simulateQ logger (run accept (((), fun _ => answer), hidden))).run []

/-- The final statement, the final oracle's answer, the private output, and the history. -/
def summary (accept : Bool) (answer hidden : Nat) :
    Option ((Bool × Nat) × Bool × (Nat × Nat × Nat)) × List Nat :=
  let z := observed accept answer hidden
  (z.1.map fun s => (s.1.1, s.1.2 (), s.2), z.2)

/-- The accepted fold of the three stages, for every input and hidden value. Every effect runs
once, each stage deciding before the next one starts. -/
theorem observed_true (answer hidden : Nat) :
    observed true answer hidden =
      (some ((((answer + 11) % 2 == 0,
          (if answer % 2 == 0 then hidden + 1
            else if decide (hidden + 1 > 0) then 100 else 200) + (answer + 11) + 10),
          fun _ => !((answer + 11) % 2 == 0)), (hidden + 1, hidden + 1 + 1, 9)),
        [0, 1, 2, 3, 4, 5, 6]) := by
  unfold observed
  rw [run_three, firstStage_run]
  simp only [bind_assoc, LawfulMonad.pure_bind, ↓reduceIte, Option.elim]
  rw [secondStage_run]
  simp only [bind_assoc, LawfulMonad.pure_bind]
  rw [thirdStage_run]
  rfl

-- The history: the prover's event 4 precedes the challenge draw 5, then the decision's event 6.
example : (observed true 7 40).2 = [0, 1, 2, 3, 4, 5, 6] := by rw [observed_true]

-- On the odd input, the second statement is 100 plus the exported 18, and the third stage adds
-- the response 10. The final oracle negates the parity of 18.
example : summary true 7 40 = (some ((true, 128), false, (41, 42, 9)), [0, 1, 2, 3, 4, 5, 6]) :=
  rfl

-- On the even input, the second statement is the hidden value 41 plus the exported 31.
example : summary true 20 40 = (some ((false, 82), true, (41, 42, 9)), [0, 1, 2, 3, 4, 5, 6]) :=
  rfl

-- A rejecting first stage skips both later stages.
example : observed false 7 40 = (none, [0, 1]) := rfl

run_cmd do
  for hidden in [0, 40] do
    unless summary true 7 hidden ==
        (some ((true, 100 + 18 + 10), false, (hidden + 1, hidden + 2, 9)),
          [0, 1, 2, 3, 4, 5, 6]) do
      throwError "the accepted odd-input fold is wrong: {summary true 7 hidden}"
    unless summary true 20 hidden ==
        (some ((false, hidden + 1 + 31 + 10), true, (hidden + 1, hidden + 2, 9)),
          [0, 1, 2, 3, 4, 5, 6]) do
      throwError "the accepted even-input fold is wrong: {summary true 20 hidden}"
    unless summary false 7 hidden == (none, [0, 1]) do
      throwError "the rejected fold is wrong: {summary false 7 hidden}"

end Interaction.Core.StagesExampleTests
