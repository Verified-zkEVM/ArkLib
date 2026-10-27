/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.SamplingResources
import ArkLibTest.ProofSystem.Sumcheck.Interaction.Resources
import Lean.Compiler.IR

/-! # Actual phased verifier queries stay separate from private prover sampler queries -/

open Interaction.Oracle OracleComp OracleSpec CompPoly
open Lean Elab Command
open Sumcheck.Interaction
namespace NativeSamplingResourcesTests
open TerminalCheckTest NativeResourcesTests

/-- Three primitive queries per verifier draw, even though only one challenge is returned. -/
def noisyDraw : OracleComp ambientSpec F :=
  (fun values : Vector F 3 => values.get 0) <$>
    Vector.ofFnM (fun _ : Fin 3 => event 1)

/-- Private queries deliberately include the same sampler index used by the verifier. -/
def noisyProver (q : Sumcheck.Impl.Representation.Message F 1) :
    Prover.Strategy ambientSpec (Computable.protocol F 1 1).tree
      (Computable.protocol F 1 1).roles Private := do
  let _ ← event 1
  let secret ← event 0
  return ⟨q, fun
    | none => do
      let _ ← event 1
      let trailing ← event 2
      return Vector.replicate q.val.val.size (secret + trailing)
    | some r => do
      let _ ← event 1
      let trailing ← event 2
      return Vector.replicate (q.val.val.size + 1) (secret + trailing + r)⟩

abbrev OneResult := PhasedResult ambientSpec (Computable.protocol F 1 1).tree
  (Computable.protocol F 1 1).roles (Computable.protocol F 1 1).oracles
  inputSpec.toPFunctor Private (fun _ => Bool)

def oneRun (q : Sumcheck.Impl.Representation.Message F 1) : OracleComp ambientSpec OneResult :=
  executeStrategiesPhased ambientSpec (Computable.protocol F 1 1).tree
    (Computable.protocol F 1 1).roles (Computable.protocol F 1 1).oracles
    inputSpec.toPFunctor inputImpl (noisyProver q)
    (Computable.verifierWithFinalCheck F 1 1 ambientSpec noisyDraw [0, 1] 1 0 rfl
      inputSpec.toPFunctor originalView initial)

def summarizeOne (result : OneResult × List Nat) :
    Bool × Nat × Nat × Nat × Nat × List Nat × List Nat × List Nat :=
  (result.1.verifierOut,
    WorldSegments.queryCount .verifier (Computable.protocol F 1 1).roles result.1.world,
    WorldSegments.queryCount .prover (Computable.protocol F 1 1).roles result.1.world,
    (Computable.Resources.pathUsage 1 1 result.1.path).roundSamples,
    result.1.sourceLog.length, result.1.proverOut.toList.map ZMod.val,
    result.1.world.flatten.map fun entry => entry.1.val, result.2)

def oneSummary (q : Sumcheck.Impl.Representation.Message F 1) :=
  summarizeOne ((simulateQ logger (oneRun q)).run [])

abbrev ManyResult := PhasedResult ambientSpec (Computable.protocol F 1 2).tree
  (Computable.protocol F 1 2).roles (Computable.protocol F 1 2).oracles
  inputSpec.toPFunctor (fun _ => F) (fun _ => Bool)

def twoRun (second : Sumcheck.Impl.Representation.Message F 1) :
    OracleComp ambientSpec ManyResult :=
  executeStrategiesPhased ambientSpec (Computable.protocol F 1 2).tree
    (Computable.protocol F 1 2).roles (Computable.protocol F 1 2).oracles
    inputSpec.toPFunctor inputImpl (twoProver second)
    (Computable.verifierWithFinalCheck F 2 1 ambientSpec noisyDraw [0, 1] 2 0 rfl
      inputSpec.toPFunctor constantView ⟨0, Fin.elim0⟩)

def summarizeTwo (result : ManyResult × List Nat) : Bool × Nat × Nat × Nat × Nat × List Nat :=
  (result.1.verifierOut,
    WorldSegments.queryCount .verifier (Computable.protocol F 1 2).roles result.1.world,
    WorldSegments.queryCount .prover (Computable.protocol F 1 2).roles result.1.world,
    (Computable.Resources.pathUsage 1 2 result.1.path).roundSamples,
    result.1.sourceLog.length, result.2)

def twoSummary (q : Sumcheck.Impl.Representation.Message F 1) :=
  summarizeTwo ((simulateQ logger (twoRun q)).run [])

abbrev ZeroResult := PhasedResult ambientSpec (Computable.protocol F 1 0).tree
  (Computable.protocol F 1 0).roles (Computable.protocol F 1 0).oracles
  inputSpec.toPFunctor (fun _ => F) (fun _ => Bool)

def zeroRun (target : F) : OracleComp ambientSpec ZeroResult :=
  executeStrategiesPhased ambientSpec (Computable.protocol F 1 0).tree
    (Computable.protocol F 1 0).roles (Computable.protocol F 1 0).oracles
    inputSpec.toPFunctor inputImpl (OutP := fun _ => F) (9 : F)
    (Computable.verifierWithFinalCheck F 1 1 ambientSpec noisyDraw [0, 1] 0 1 rfl
      inputSpec.toPFunctor originalView ⟨target, fun _ => 3⟩)

def summarizeZero (result : ZeroResult × List Nat) : Bool × Nat × Nat × Nat × List Nat :=
  (result.1.verifierOut,
    WorldSegments.queryCount .verifier (Computable.protocol F 1 0).roles result.1.world,
    WorldSegments.queryCount .prover (Computable.protocol F 1 0).roles result.1.world,
    result.1.sourceLog.length, result.2)

def zeroSummary (target : F) := summarizeZero ((simulateQ logger (zeroRun target)).run [])

theorem noisyDraw_log_length (result : F × QueryLog ambientSpec)
    (member : result ∈ support noisyDraw.withQueryLog) : result.2.length = 3 := by
  rw [noisyDraw, OracleComp.withQueryLog_map, support_map] at member
  obtain ⟨values, hv, rfl⟩ := member
  have hs : ∀ value ∈ support (event 1).withQueryLog, value.2.length = 1 := by
    intro value hvalue
    simp only [event, OracleComp.withQueryLog_query, support_bind,
      support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hvalue
    obtain ⟨answer, _, rfl⟩ := hvalue
    rfl
  exact OracleComp.withQueryLog_ofFnM_const_length (event 1) 1 3 hs values hv

/-- The theorem applies to the actual complete endpoint and its dependent private output. -/
theorem one_contract (q : Sumcheck.Impl.Representation.Message F 1) :
    ∀ result ∈ support (oneRun q),
      WorldSegments.queryCount .verifier (Computable.protocol F 1 1).roles result.world =
        3 * (Computable.Resources.pathUsage 1 1 result.path).roundSamples :=
  Computable.SamplingResources.phased_verifier_queries 1 1 ambientSpec noisyDraw 3
    noisyDraw_log_length 1 0 rfl inputSpec.toPFunctor originalView initial inputImpl (noisyProver q)

/-- Native message extensions and a later public abort preserve the same sampling attribution. -/
theorem two_contract (q : Sumcheck.Impl.Representation.Message F 1) :
    ∀ result ∈ support (twoRun q),
      WorldSegments.queryCount .verifier (Computable.protocol F 1 2).roles result.world =
        3 * (Computable.Resources.pathUsage 1 2 result.path).roundSamples :=
  Computable.SamplingResources.phased_verifier_queries 2 1 ambientSpec noisyDraw 3
    noisyDraw_log_length 2 0 rfl inputSpec.toPFunctor constantView ⟨0, Fin.elim0⟩
      inputImpl (twoProver q)

/-- Zero-round authentication has no verifier ambient query, on acceptance or rejection. -/
theorem zero_contract (target : F) :
    ∀ result ∈ support (zeroRun target),
      WorldSegments.queryCount .verifier (Computable.protocol F 1 0).roles result.world =
        3 * (Computable.Resources.pathUsage 1 0 result.path).roundSamples :=
  Computable.SamplingResources.phased_verifier_queries 1 1 ambientSpec noisyDraw 3
    noisyDraw_log_length 0 1 rfl inputSpec.toPFunctor originalView ⟨target, fun _ => 3⟩
      inputImpl (OutP := fun _ => F) (9 : F)

def check : IO Unit := do
  let full := [1, 0, 1, 1, 1, 1, 2]
  unless oneSummary (affine 2 (-1)) ==
      (true, 3, 4, 1, 5, [15, 15, 15], full, full) do
    throw (IO.userError "verifier-only count included the prover's same-index sampler queries")
  unless oneSummary (affine 0 0) == (false, 3, 4, 1, 5, [15], full, full) do
    throw (IO.userError "final rejection changed the passed-round count or skipped authentication")
  unless oneSummary (affine 0 1) ==
      (false, 0, 4, 0, 2, [12], [1, 0, 1, 2], [1, 0, 1, 2]) do
    throw (IO.userError "public abort changed draws, private response effects or source reads")
  unless twoSummary (affine 0 11) ==
      (true, 6, 3, 2, 6, [0, 1, 1, 1, 2, 1, 1, 1, 0]) do
    throw (IO.userError "two native passes lost exact draw-program fanout or phase order")
  unless twoSummary (affine 0 1) == (false, 3, 3, 1, 5, [0, 1, 1, 1, 2, 0]) do
    throw (IO.userError "second-round abort charged an unreached draw or lost private effects")
  unless zeroSummary 5 == (true, 0, 0, 2, []) &&
      zeroSummary 0 == (false, 0, 0, 2, []) do
    throw (IO.userError "zero-round source fanout was incorrectly priced as ambient sampling")

run_cmd do
  match (← liftIO check.toBaseIO) with
  | .ok () => pure ()
  | .error e => throwError e.toString
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``WorldSegments.queryCount_done, ``WorldSegments.queryCount_public_sender,
      ``WorldSegments.queryCount_public_receiver, ``WorldSegments.queryCount_oracle,
      ``Computable.SamplingResources.phased_verifier_queries, ``noisyDraw_log_length,
      ``one_contract, ``two_contract, ``zero_contract] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected phased sampling axiom: {name}"
  for name in #[``WorldSegments.queryCount, ``noisyDraw, ``noisyProver, ``oneRun,
      ``oneSummary, ``twoRun, ``twoSummary, ``zeroRun, ``zeroSummary] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing executable phased sampling caller IR: {name}"
  logInfo "actual phased verifier/private query attribution, abort and authentication checks passed"

end NativeSamplingResourcesTests
