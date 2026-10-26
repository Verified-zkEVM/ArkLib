/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Interaction.SamplingResources
import ArkLibTest.ProofSystem.Logup.Interaction.LoggedPrefix
import ArkLibTest.ProofSystem.Logup.Interaction.MeasuredRuntime
import Lean.Compiler.IR

/-! # Actual verifier sampling phases and complete honest primitive logs -/

open Interaction Interaction.Oracle OracleComp OracleSpec CompPoly
open Logup.Interaction Logup.Interaction.SamplingResources
namespace LogupSamplingResourcesTests
namespace Weighted
open LogupRuntimeFixture

/-- All five private calls deliberately share the alpha sampler's query index. -/
def prover (h : E) (q : Message) :
    Prover.Strategy ambientSpec combined.tree combined.roles LoggedPrefixTests.Weighted.Output :=
  Interaction.StrategyOver.TwoParty.Focal.mapOutput
    (fun path value => LoggedPrefixTests.Weighted.pack
      (TypeTree.ExecutionPath.ofTypeTreePath path) value)
    (LogupRuntimeFixture.prover (fun _ => event 0) h q)

abbrev Result := PhasedResult ambientSpec combined.tree combined.roles combined.oracles access
  LoggedPrefixTests.Weighted.Output (fun _ => Bool)

def run (h : E) (q : Message) : OracleComp ambientSpec Result :=
  executeStrategiesPhased ambientSpec combined.tree combined.roles combined.oracles access impl
    (prover h q) (verifier embedding 1 2 2 cfg ambientSpec
      (event 0) jointDraw (event 7) access view)

def summarize (result : Result × List Nat) :
    Bool × Nat × Nat × Nat × Nat × List Nat × List Nat :=
  (result.1.verifierOut, WorldSegments.queryCount .verifier combined.roles result.1.world,
    WorldSegments.queryCount .prover combined.roles result.1.world,
    (Sumcheck.Interaction.Computable.Resources.pathUsage 4 1 result.1.path.2.2.2).roundSamples,
    result.1.sourceLog.length, result.1.world.flatten.map (fun entry => entry.1.val), result.2)

def summary (h : E) (q : Message) := summarize ((simulateQ logger (run h q)).run [])

theorem event_length (i : Fin 9) (result : E × QueryLog ambientSpec)
    (member : result ∈ support (event i).withQueryLog) : result.2.length = 1 := by
  simp only [event, OracleComp.withQueryLog_query, support_bind,
    support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at member
  obtain ⟨answer, _, rfl⟩ := member
  rfl

theorem joint_length (result : ((Fin 1 → E) × (Fin 1 → E)) × QueryLog ambientSpec)
    (member : result ∈ support jointDraw.withQueryLog) : result.2.length = 2 := by
  simp only [jointDraw, withQueryLog_bind, withQueryLog_pure, map_bind, map_pure] at member
  obtain ⟨z, hz, member⟩ := OracleComp.mem_support_bind_peel _ _ member
  obtain ⟨lambda, hlambda, member⟩ := OracleComp.mem_support_bind_peel _ _ member
  have heq := OracleComp.eq_of_mem_support_pure _ member
  subst result
  simp only [Prod.map, id_eq, List.length_append, List.length_nil, Nat.add_zero]
  rw [event_length 3 z hz, event_length 4 lambda hlambda]

theorem contract (h : E) (q : Message) :
    ∀ result ∈ support (run h q),
      WorldSegments.queryCount .verifier combined.roles result.world =
        1 + 2 + (Sumcheck.Interaction.Computable.Resources.pathUsage 4 1
          result.path.2.2.2).roundSamples := by
  intro result hresult
  have law := phased_verifier_queries embedding 1 2 2 cfg ambientSpec
    (event 0) jointDraw (event 7) 1 2 1 (event_length 0) joint_length (event_length 7)
    access view impl (prover h q) result hresult
  change WorldSegments.queryCount .verifier combined.roles result.world = _ at law
  simpa only [Nat.one_mul, Nat.reduceAdd] using law


/-- A native round can complete even when its draw program has no primitive query. -/
def pureRun : OracleComp ambientSpec Result :=
  executeStrategiesPhased ambientSpec combined.tree combined.roles combined.oracles access impl
    (prover 0 (affine 0 0)) (verifier embedding 1 2 2 cfg ambientSpec
      (pure 2) (pure (fun _ => 3, fun _ => 4)) (pure 5) access view)

def pureSummary := summarize ((simulateQ logger pureRun).run [])
end Weighted

namespace Zero
open LogupRuntimeFixture
abbrev combined := ZeroRound.combined
abbrev Result := PhasedResult ambientSpec combined.tree combined.roles combined.oracles
  ZeroRound.access (fun _ => E) (fun _ => Bool)

def run (h : E) : OracleComp ambientSpec Result := executeStrategiesPhased ambientSpec
  combined.tree combined.roles combined.oracles ZeroRound.access ZeroRound.impl
  (ZeroRound.prover h) (verifier embedding 0 2 2 ZeroRound.cfg ambientSpec
    (event 0) ZeroRound.jointDraw (event 7) ZeroRound.access ZeroRound.view)

def summarize (result : Result × List Nat) : Bool × Nat × Nat × Nat × List Nat :=
  (result.1.verifierOut, WorldSegments.queryCount .verifier combined.roles result.1.world,
    WorldSegments.queryCount .prover combined.roles result.1.world,
    result.1.sourceLog.length, result.2)
def summary (h : E) := summarize ((simulateQ logger (run h)).run [])

theorem joint_length (result : ((Fin 0 → E) × (Fin 1 → E)) × QueryLog ambientSpec)
    (member : result ∈ support ZeroRound.jointDraw.withQueryLog) : result.2.length = 1 := by
  simp only [ZeroRound.jointDraw, withQueryLog_bind, withQueryLog_pure, map_pure] at member
  obtain ⟨lambda, hlambda, member⟩ := OracleComp.mem_support_bind_peel _ _ member
  have heq := OracleComp.eq_of_mem_support_pure _ member
  subst result
  simpa only [Prod.map, id_eq, List.append_nil] using Weighted.event_length 4 lambda hlambda

theorem contract (h : E) : ∀ result ∈ support (run h),
    WorldSegments.queryCount .verifier combined.roles result.world = 2 := by
  intro result hresult
  have law := phased_verifier_queries embedding 0 2 2 ZeroRound.cfg ambientSpec
    (event 0) ZeroRound.jointDraw (event 7) 1 1 1
    (Weighted.event_length 0) joint_length (Weighted.event_length 7)
    ZeroRound.access ZeroRound.view ZeroRound.impl (ZeroRound.prover h) result hresult
  change WorldSegments.queryCount .verifier combined.roles result.world = _ at law
  simpa only [Sumcheck.Interaction.Computable.Resources.pathUsage, Nat.mul_zero,
    Nat.add_zero, Nat.reduceAdd] using law

end Zero

namespace Uniform
open LogupMeasuredRuntime.Uniform
abbrev ScalarProtocol := Logup.Lookup.protocol f 1 0 1 1
abbrev TupleProtocol := Logup.Lookup.Tuple.protocol f 1 0 1 1
abbrev ScalarResult := PhasedResult unifSpec ScalarProtocol.tree ScalarProtocol.roles
  ScalarProtocol.oracles scalarAccess (fun _ => Unit) (fun _ => Bool)
abbrev TupleResult := PhasedResult unifSpec TupleProtocol.tree TupleProtocol.roles
  TupleProtocol.oracles tupleAccess (fun _ => Unit) (fun _ => Bool)

def scalarRun : ProbComp ScalarResult := executeStrategiesPhased unifSpec ScalarProtocol.tree
  ScalarProtocol.roles ScalarProtocol.oracles scalarAccess scalarImpl
  (Logup.Lookup.Honest.prover f cfg data indices unifSpec)
  (Logup.Lookup.verifier f 1 0 1 1 cfg unifSpec ($ᵗ E)
    ($ᵗ ((Fin 1 → E) × (Fin 1 → E))) ($ᵗ E) scalarAccess (VirtualOracle.id _))

def tupleRun : ProbComp TupleResult := executeStrategiesPhased unifSpec TupleProtocol.tree
  TupleProtocol.roles TupleProtocol.oracles tupleAccess tupleImpl
  (Logup.Lookup.Tuple.Honest.prover f cfg prepared indices unifSpec)
  (Logup.Lookup.Tuple.verifier f 1 0 1 2 1 cfg unifSpec ($ᵗ E) ($ᵗ E)
    ($ᵗ ((Fin 1 → E) × (Fin 1 → E))) ($ᵗ E) tupleAccess (VirtualOracle.id _))

def scalarSummarize (result : ScalarResult × List Nat) : Bool × Nat × Nat × Nat :=
  (result.1.verifierOut, WorldSegments.queryCount .verifier ScalarProtocol.roles result.1.world,
    WorldSegments.queryCount .prover ScalarProtocol.roles result.1.world, result.2.length)
def tupleSummarize (result : TupleResult × List Nat) : Bool × Nat × Nat × Nat :=
  (result.1.verifierOut, WorldSegments.queryCount .verifier TupleProtocol.roles result.1.world,
    WorldSegments.queryCount .prover TupleProtocol.roles result.1.world, result.2.length)
def scalarSummary := scalarSummarize ((simulateQ zeroTrace scalarRun).run [])
def tupleSummary := tupleSummarize ((simulateQ zeroTrace tupleRun).run [])

/-- The named scalar default's actual primitive log is bounded for every supported output. -/
theorem scalar_bound : ∀ result ∈ support scalar.withQueryLog, result.2.length ≤ 24 := by
  intro result hresult
  obtain ⟨phase, _, _, count⟩ := scalar_uniformExecute_default_queries f 1 0 1 1 cfg data indices
    6 KoalaBear.Ext6.uniformSample_log_length scalarAccess (VirtualOracle.id _) scalarImpl
    result hresult
  have bounds := Sumcheck.Interaction.Computable.Resources.pathUsage_bounds 3 1
    phase.path.2.2.2.2
  change result.2.length = 6 * (3 + _) at count
  simp only [Nat.reduceAdd] at count
  omega

/-- The extra tuple beta draw contributes six actual base-field primitive queries. -/
theorem tuple_bound : ∀ result ∈ support tuple.withQueryLog, result.2.length ≤ 30 := by
  intro result hresult
  obtain ⟨phase, _, _, count⟩ := tuple_uniformExecute_default_queries f cfg prepared indices
    6 KoalaBear.Ext6.uniformSample_log_length tupleAccess (VirtualOracle.id _) tupleImpl
    result hresult
  have bounds := Sumcheck.Interaction.Computable.Resources.pathUsage_bounds 3 1
    phase.path.2.2.2.2.2
  change result.2.length = 6 * (4 + _) at count
  simp only [Nat.reduceAdd] at count
  omega
end Uniform

/-- Verifier-party queries stay separate from same-index private calls and public abort. -/
def checkWeighted : IO Unit := do
  let full := [0, 0, 0, 3, 4, 0, 0, 7, 0]
  let abort := [0, 0, 0, 3, 4, 0, 0, 0]
  let zero := LogupRuntimeFixture.affine 0 0
  unless Weighted.summary 0 zero == (true, 4, 5, 1, 8, full, full) &&
      Weighted.summary 1 zero == (false, 4, 5, 1, 8, full, full) do
    throw (IO.userError "terminal Bool changed verifier/private phase attribution")
  unless Weighted.summary 0 (LogupRuntimeFixture.affine 0 1) ==
      (false, 3, 5, 0, 2, abort, abort) do
    throw (IO.userError "public abort charged an unreached round draw")
  unless Zero.summary 0 == (true, 2, 3, 5, [0, 1, 2, 4, 5]) &&
      Zero.summary 1 == (false, 2, 3, 5, [0, 1, 2, 4, 5]) do
    throw (IO.userError "zero native rounds erased the actual alpha/joint sampler phases")
  unless Weighted.pureSummary == (true, 0, 5, 1, 8, [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]) do
    throw (IO.userError "draw-program invocation count was mistaken for primitive queries")

/-- The selected defaults attain the proved bounds with actual six-limb uniform samplers. -/
def checkUniform : IO Unit := do
  unless Uniform.scalarSummary == (true, 24, 0, 24) &&
      Uniform.tupleSummary == (true, 30, 0, 30) do
    throw (IO.userError "selected uniform/default primitive count or private-empty transfer failed")

open Lean Elab Command in
run_cmd do
  liftIO checkWeighted
  liftIO checkUniform
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Weighted.contract, ``Zero.contract, ``Uniform.scalar_bound, ``Uniform.tuple_bound,
      ``phased_verifier_queries, ``scalar_phased_verifier_queries, ``tuple_phased_verifier_queries,
      ``uniform_phased_verifier_queries, ``scalar_uniform_phased_verifier_queries,
      ``tuple_uniform_phased_verifier_queries, ``execute_world_eq, ``scalar_execute_world_eq,
      ``tuple_execute_world_eq, ``uniformExecute_default_queries,
      ``scalar_uniformExecute_default_queries, ``tuple_uniformExecute_default_queries] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected actual LogUp sampler resource axiom: {name}"
  for name in #[``Weighted.run, ``Weighted.pureRun, ``Uniform.scalarRun, ``Uniform.tupleRun] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing actual LogUp phased sampler caller IR: {name}"
  logInfo "actual complete LogUp phases, same-index private queries and selected24/30 limbs passed"
end LogupSamplingResourcesTests
