/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.StateRestorationOracle
public import VCVio.EvalDist.Monad.Option

/-!
# State-restoration knowledge soundness with pre-sampled private coins

Both actual native restoration games satisfy the same `(Q + rounds.length) * error` bound
when the adversary's private coins are sampled before the fresh cached game.
The possibly failing coin author runs independently before a fresh empty cached game.
For each returned coin, the deterministic native adversary adapts to all oracle answers
and obeys an all-branch query bound. This is a random-tape-family theorem: it does not
assert equivalence with arbitrary interleaved coin/oracle effects.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.Security.StateRestoration

universe w

variable {Input Salt W : Type} {rounds : List Round}

/-- Average actual native restoration soundness over independent, possibly failing private coins.
Every fixed-coin adversary may adapt to all oracle responses and has the same all-branch bound. -/
theorem stateRestoration_knowledge_soundness_privateCoins
    [DecidableEq Input] [DecidableEq Salt]
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input) (error : ENNReal)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol rounds).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z) (protocol rounds).roles
      (uniformSchedule error rounds))
    (initial : PFunctor) (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Out : Input → (protocol rounds).tree.BranchPath → Type)
    (terminal : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol rounds).tree
        (protocol rounds).oracles initial p)) (Out z p))
    (Rin : (z : Input) → (state z).Witness → Prop)
    (Rout : (z : Input) → (p : (protocol rounds).tree.BranchPath) → Out z p → W → Prop)
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W ≃ ((extractor z).terminalState path).Witness)
    (inputLaw : ∀ z witness, (state z).holds witness ↔ Rin z witness)
    (outputLaw : ∀ z path witness,
      ((extractor z).terminalState path).holds (terminalWitness z path witness) ↔
        Rout z path.toBranchPath (terminalObservation initial impl Out terminal z path) witness)
    {Coins : Type} (coins : OptionT ProbComp Coins)
    (adversary : Coins →
      OracleComp (oracleSpec Input Salt rounds) (Input × Messages Salt rounds × W))
    (Q : ℕ) (queryBound : ∀ c, IsTotalQueryBound (adversary c) Q) :
    Pr{let result ← (coins >>= fun c => OptionT.lift
        ((simulateQ randomOracle
          (verificationGame initial impl Out terminal (adversary c))).run' ∅))}[
      result.1 ∈ Z ∧ Rout result.1 result.2.1.toBranchPath result.2.2.1 result.2.2.2 ∧
      ¬ Rin result.1 (extractInputWitness state extractor terminalWitness
        result.1 result.2.1 result.2.2.2)] ≤ (Q + rounds.length) * error := by
  apply prEvent_bind_le_of_forall_le
  intro c
  rw [OptionT.prEvent_lift]
  exact stateRestoration_knowledge_soundness state extractor Z error preserving bounded
    initial impl Out terminal Rin Rout terminalWitness inputLaw outputLaw
    (adversary c) Q (queryBound c)


/-- The private-coins extension for actual closed oracle outputs, with rejection unsuccessful.
The relation observes the same run's closed behavior. Coin failure contributes missing mass. -/
theorem stateRestoration_oracle_knowledge_soundness_privateCoins
    [DecidableEq Input] [DecidableEq Salt]
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input) (error : ENNReal)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol rounds).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z) (protocol rounds).roles
      (uniformSchedule error rounds))
    (initial : PFunctor) (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Stmt : Input → (protocol rounds).tree.BranchPath → Type)
    {Idx : Input → (protocol rounds).tree.BranchPath → Type}
    {Realization : (z : Input) → (p : (protocol rounds).tree.BranchPath) → Idx z p → Type}
    (family : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleFamily (Idx z p) (Realization z p))
    (terminal : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol rounds).tree
        (protocol rounds).oracles initial p)) (OracleOutput initial Stmt family z p))
    (Rin : (z : Input) → (state z).Witness → Prop)
    (Rout : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      ClosedClaim (Stmt z p) (family z p) → W → Prop)
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W ≃ ((extractor z).terminalState path).Witness)
    (inputLaw : ∀ z witness, (state z).holds witness ↔ Rin z witness)
    (outputLaw : ∀ z path witness,
      ((extractor z).terminalState path).holds (terminalWitness z path witness) ↔
        ∃ claim, closedTerminalObservation initial impl Stmt family terminal z path = some claim ∧
          Rout z path.toBranchPath claim witness)
    {Coins : Type} (coins : OptionT ProbComp Coins)
    (adversary : Coins →
      OracleComp (oracleSpec Input Salt rounds) (Input × Messages Salt rounds × W))
    (Q : ℕ) (queryBound : ∀ c, IsTotalQueryBound (adversary c) Q) :
    Pr{let result ← (coins >>= fun c => OptionT.lift
        ((simulateQ randomOracle
          (closedVerificationGame initial impl Stmt family terminal (adversary c))).run' ∅))}[
      result.1 ∈ Z ∧
      (∃ claim, result.2.2.1 = some claim ∧
        Rout result.1 result.2.1.toBranchPath claim result.2.2.2) ∧
      ¬ Rin result.1 (extractInputWitness state extractor terminalWitness
        result.1 result.2.1 result.2.2.2)] ≤ (Q + rounds.length) * error := by
  apply prEvent_bind_le_of_forall_le
  intro c
  rw [OptionT.prEvent_lift]
  exact stateRestoration_oracle_knowledge_soundness state extractor Z error preserving bounded
    initial impl Stmt family terminal Rin Rout terminalWitness inputLaw outputLaw
    (adversary c) Q (queryBound c)


end Interaction.Oracle.Security.StateRestoration
