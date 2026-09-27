/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Prefix
import ArkLib.Data.OracleComp.QueryBounds
import ArkLibTest.Interaction.Oracle.RuntimeSoundness

/-!
# Query certificates for the native hidden-bit experiment

These certificates describe the same exported resource and native experiment as the runtime
soundness test. Access, initialization, source charges, and chronological ambient costs are
separate from its honest closed-claim relation and averaged security premise.
-/

namespace Interaction.Oracle.RuntimeQueryBoundsTest

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal
open _root_.Interaction.Oracle.TypeTree
open RuntimeSoundnessTest

noncomputable section

/-- Canonical available resources come from the actual native prefix path. -/
abbrev resourcePrefix (boundary : Boundary) :=
  ExecutionPrefix.ofExecutionPath (ExecutionPath.ofTypeTreePath boundary.1)

abbrev sourceName (boundary : Boundary) (query : Unit) :=
  (resourcePrefix boundary).queryName firstProtocol.oracles inputSpec.toPFunctor
    (ExecutionPrefix.includeQueryAlong (resourcePrefix boundary).cursor.spine
      firstProtocol.oracles inputSpec.toPFunctor query)

abbrev sourceAllowed (boundary : Boundary) (query : Unit) : Prop :=
  ∃ index : ((resourcePrefix boundary).availableContext inputSpec.toPFunctor.A).Index,
    ((resourcePrefix boundary).availableContext inputSpec.toPFunctor.A).name index =
      sourceName boundary query

def inputCost : CostModel inputSpec Nat := ⟨fun _ => 2⟩
def ambientCost : CostModel ambient Nat := ⟨fun query => if query then 3 else 1⟩
def importCost : CostModel coinSpec Nat := ⟨fun _ => 1⟩

/-- The exact capability authored in `firstVerifier` can query the canonical initial source. -/
lemma exported_certificate (boundary : Boundary) :
    AllQueriesSatisfy (exported.query ⟨(), ()⟩) (sourceAllowed boundary) ∧
    WorstCaseCostBound (exported.query ⟨(), ()⟩) inputCost 2 := by
  constructor
  · apply (allQueriesSatisfy_query_iff () _).mpr
    exact (resourcePrefix boundary).queryName_available firstProtocol.oracles inputSpec.toPFunctor
      (ExecutionPrefix.includeQueryAlong (resourcePrefix boundary).cursor.spine
        firstProtocol.oracles inputSpec.toPFunctor ())
  · exact worstCaseCostBound_query () inputCost

lemma source_name (boundary : Boundary) : sourceName boundary () = Sum.inl () :=
  (resourcePrefix boundary).queryName_include firstProtocol.oracles inputSpec.toPFunctor ()

/-- `firstVerifier` really returns this authored query view after its harmless dummy query. -/
lemma first_returns_exported :
    (fun result => result.2.oracles.query ⟨(), ()⟩) <$> firstVerifier = (do
      let _ : Bool ← liftM ((ambient + inputSpec).query (.inl false))
      return exported.query ⟨(), ()⟩) := by
  rfl

/-- Select the existing staged terminal action after the public guess is received. -/
def suffixAction (guess : Bool) :
    OracleComp (ambient + family.spec) (Option (OpenClaim family.spec Bool family)) :=
  secondVerifier ⟨(), PUnit.unit⟩ () guess >>= id

lemma suffixAction_eq (guess : Bool) : suffixAction guess = (do
    let pad : Bool ← liftM ((ambient + family.spec).query (.inr ⟨(), ()⟩))
    let hidden : Bool ← liftM ((ambient + family.spec).query (.inl true))
    return some ⟨hidden ^^ pad, ⟨fun _ => pure (guess ^^ pad)⟩⟩) := by
  rfl

def suffixCost : CostModel (ambient + family.spec) Nat := ⟨fun query => match query with
  | .inl request => ambientCost.queryCost request
  | .inr _ => 2⟩

/-- Ambient revelation is an explicit permission, while export permission follows its raw query. -/
abbrev suffixAllowed (boundary : Boundary) : (ambient + family.spec).Domain → Prop
  | .inl request => request = true
  | .inr query => AllQueriesSatisfy (exported.query query) (sourceAllowed boundary)

lemma suffix_access (boundary : Boundary) (guess : Bool) :
    AllQueriesSatisfy (suffixAction guess) (suffixAllowed boundary) := by
  rw [suffixAction_eq]
  apply allQueriesSatisfy_bind
  · apply (allQueriesSatisfy_query_iff (spec := ambient + family.spec)
      (.inr ⟨(), ()⟩) (suffixAllowed boundary)).mpr
    exact (exported_certificate boundary).1
  · intro pad
    apply allQueriesSatisfy_bind
    · exact (allQueriesSatisfy_query_iff (spec := ambient + family.spec)
        (.inl true) (suffixAllowed boundary)).mpr rfl
    · intro hidden
      exact allQueriesSatisfy_pure _ _

/-- The actual suffix asks one exported query costing two, then one ambient query costing three. -/
lemma suffix_budget (guess : Bool) : WorstCaseCostBound (suffixAction guess) suffixCost 5 := by
  rw [suffixAction_eq]
  exact worstCaseCostBound_bind _ _ suffixCost 2 3
    (worstCaseCostBound_query (.inr ⟨(), ()⟩) suffixCost)
    (fun _ => worstCaseCostBound_bind _ _ suffixCost 3 0
      (worstCaseCostBound_query (.inl true) suffixCost)
      (fun _ => by
        intro result member
        simp only [instrumentedRun, simulateQ_pure,
          WriterT.run_pure, mem_support_pure_iff] at member
        subst result
        exact le_rfl))


def rawCost : CostModel (ambient + inputSpec) Nat := ⟨fun query => match query with
  | .inl request => ambientCost.queryCost request
  | .inr _ => 2⟩

/-- The declared source substitution uses the exact authored export returned by the prefix. -/
abbrev routedSuffix (guess : Bool) := Verifier.routeProgram ambient family.spec.toPFunctor
  inputSpec.toPFunctor exported.query (suffixAction guess)

lemma routed_suffix_budget (guess : Bool) :
    WorstCaseCostBound (routedSuffix guess) rawCost 5 := by
  apply worstCaseCostBound_simulateQ _ (suffixAction guess) suffixCost rawCost 5
    (suffix_budget guess)
  intro query
  cases query with
  | inl request =>
    change WorstCaseCostBound (liftM ((ambient + inputSpec).query (.inl request))) rawCost
      (ambientCost.queryCost request)
    exact worstCaseCostBound_query (.inl request) rawCost
  | inr query =>
    cases query with
    | mk index subquery =>
      cases index
      cases subquery
      change WorstCaseCostBound (liftM ((ambient + inputSpec).query (.inr ()))) rawCost 2
      exact worstCaseCostBound_query (.inr ()) rawCost

abbrev rawAllowed (boundary : Boundary) : (ambient + inputSpec).Domain → Prop
  | .inl request => request = true
  | .inr query => sourceAllowed boundary query

lemma routed_suffix_access (boundary : Boundary) (guess : Bool) :
    AllQueriesSatisfy (routedSuffix guess) (rawAllowed boundary) := by
  apply allQueriesSatisfy_simulateQ _ (suffixAction guess) (suffixAllowed boundary)
    (rawAllowed boundary) (suffix_access boundary guess)
  intro query permission
  cases query with
  | inl request =>
    exact (allQueriesSatisfy_query_iff (spec := ambient + inputSpec)
      (.inl request) (rawAllowed boundary)).mpr permission
  | inr query =>
    cases query with
    | mk index subquery =>
      cases index
      cases subquery
      have allowed := (exported_certificate boundary).1
      apply (allQueriesSatisfy_query_iff (spec := ambient + inputSpec)
        (.inr ()) (rawAllowed boundary)).mpr
      exact (allQueriesSatisfy_query_iff () (sourceAllowed boundary)).mp allowed

/-- Charge the actual chronological ambient query list, retaining its answers separately. -/
def ambientCharge (history : OracleSpec.QueryLog ambient) : Nat :=
  (history.map fun entry => ambientCost.queryCost entry.1).sum

lemma actual_history (guess : Bool) (secret : Nat) :
    (fun result => (result.state, result.trace, ambientCharge result.trace)) <$>
      runtime.run (prefixProgram (prover guess secret) >>= nextProgram) =
    (fun hidden => ((hidden, 2),
      ([⟨false, false⟩, ⟨true, hidden⟩] : OracleSpec.QueryLog ambient), 4)) <$>
      (coinSpec.query () : OracleComp coinSpec Bool) := by
  have history := run_history (prefixProgram (prover guess secret) >>= nextProgram)
    (fun hidden => ((hidden, 2),
      ([⟨false, false⟩, ⟨true, hidden⟩] : OracleSpec.QueryLog ambient)))
    (fun hidden => final_history guess hidden secret)
  have charged := congrArg (fun program =>
    (fun result => (result.1, result.2, ambientCharge result.2)) <$> program) history
  simpa [Functor.map_map, ambientCharge, ambientCost] using charged

/-- The query-informed prover remains permitted, and its actual ambient cost increases to seven. -/
lemma informed_actual_history (secret : Nat) :
    (fun result => (result.state, result.trace, ambientCharge result.trace)) <$>
      runtime.run (prefixProgram (informedProver secret) >>= nextProgram) =
    (fun hidden => ((hidden, 3),
      ([⟨false, false⟩, ⟨true, hidden⟩, ⟨true, hidden⟩] : OracleSpec.QueryLog ambient), 7)) <$>
      (coinSpec.query () : OracleComp coinSpec Bool) := by
  have history := run_history (prefixProgram (informedProver secret) >>= nextProgram)
    (fun hidden => ((hidden, 3),
      ([⟨false, false⟩, ⟨true, hidden⟩, ⟨true, hidden⟩] : OracleSpec.QueryLog ambient)))
    (fun hidden => informed_final_history hidden secret)
  have charged := congrArg (fun program =>
    (fun result => (result.1, result.2, ambientCharge result.2)) <$> program) history
  simpa [Functor.map_map, ambientCharge, ambientCost] using charged

/-- Initialization samples the retained bit once through the declared import. -/
lemma setup_budget : WorstCaseCostBound runtime.setup importCost 1 := by
  exact worstCaseCostBound_bind _ _ importCost 1 0
    (worstCaseCostBound_query () importCost)
    (fun _ => by
      intro result member
      simp only [instrumentedRun, simulateQ_pure, WriterT.run_pure, mem_support_pure_iff] at member
      subst result
      exact le_rfl)

/-- Pure observation of the existing native split retains state and chronological ambient cost. -/
lemma native_split_history
    (native : Prover.Strategy ambient combined.tree combined.roles (fun _ => Nat)) :
    (fun result => (result.state, result.trace, ambientCharge result.trace)) <$>
      executeStrategiesWithRuntime runtime inputImpl native verifier =
    (fun result => (result.state, result.trace, ambientCharge result.trace)) <$>
      runtime.run (prefixProgram native >>= nextProgram) := by
  have paired := executeStrategiesWithRuntime_appendExported_closedResult ambient
    firstProtocol.tree (fun _ => secondProtocol.tree)
    firstProtocol.roles (fun _ => secondProtocol.roles)
    firstProtocol.oracles (fun _ => secondProtocol.oracles) inputSpec.toPFunctor inputImpl
    (fun _ => Unit) (fun _ _ => Bool) (fun _ => family)
    (fun _ => Bool) (fun _ _ => Bool) (fun _ => family) (fun _ => Nat)
    native firstVerifier secondVerifier runtime
  have observed := congrArg (fun program =>
    (fun result => (result.2.1, result.2.2, ambientCharge result.2.2)) <$> program) paired
  simp only [Functor.map_map] at observed
  delta nextProgram
  simpa only [verifier, prefixProgram, map_eq_pure_bind] using observed

/-- The direct native logged runtime retains exactly this charged ambient history. -/
lemma native_actual_history (guess : Bool) (secret : Nat) :
    (fun result => (result.state, result.trace, ambientCharge result.trace)) <$>
      executeStrategiesWithRuntime runtime inputImpl (prover guess secret) verifier =
    (fun hidden => ((hidden, 2),
      ([⟨false, false⟩, ⟨true, hidden⟩] : OracleSpec.QueryLog ambient), 4)) <$>
      (coinSpec.query () : OracleComp coinSpec Bool) :=
  (native_split_history (prover guess secret)).trans (actual_history guess secret)

lemma informed_native_history (secret : Nat) :
    (fun result => (result.state, result.trace, ambientCharge result.trace)) <$>
      executeStrategiesWithRuntime runtime inputImpl (informedProver secret) verifier =
    (fun hidden => ((hidden, 3),
      ([⟨false, false⟩, ⟨true, hidden⟩, ⟨true, hidden⟩] : OracleSpec.QueryLog ambient), 7)) <$>
      (coinSpec.query () : OracleComp coinSpec Bool) :=
  (native_split_history (informedProver secret)).trans (informed_actual_history secret)

/-- Cost reflection through a pure history observation proves the actual import budget. -/
lemma native_import_budget (guess : Bool) (secret : Nat) :
    WorstCaseCostBound
      (executeStrategiesWithRuntime runtime inputImpl (prover guess secret) verifier)
      importCost 1 := by
  apply (worstCaseCostBound_map_iff _
    (fun result => (result.state, result.trace, ambientCharge result.trace)) importCost 1).mp
  rw [native_actual_history]
  apply (worstCaseCostBound_map_iff _ _ importCost 1).mpr
  exact worstCaseCostBound_query () importCost

/-- Resource and cost certificates accompany the same fixed native guessing prover's half bound.
They are properties of this exact experiment; they do not establish security for arbitrary provers.
The verifier returns the certified export, and hidden state is used only analytically by the runtime
history observation. `TruthFinal` and the actual integrated success premise remain unchanged. -/
theorem fixed_native_resource_bounds (guess : Bool) (secret : Nat) :
    ((fun result => result.2.oracles.query ⟨(), ()⟩) <$> firstVerifier = (do
      let _ : Bool ← liftM ((ambient + inputSpec).query (.inl false))
      return exported.query ⟨(), ()⟩)) ∧
    (∀ boundary : Boundary,
      sourceName boundary () = Sum.inl () ∧
      AllQueriesSatisfy (exported.query ⟨(), ()⟩) (sourceAllowed boundary) ∧
      WorstCaseCostBound (exported.query ⟨(), ()⟩) inputCost 2 ∧
      AllQueriesSatisfy (routedSuffix guess) (rawAllowed boundary) ∧
      WorstCaseCostBound (routedSuffix guess) rawCost 5) ∧
    WorstCaseCostBound
      (executeStrategiesWithRuntime runtime inputImpl (prover guess secret) verifier) importCost 1 ∧
    ((fun result => (result.state, result.trace, ambientCharge result.trace)) <$>
      executeStrategiesWithRuntime runtime inputImpl (prover guess secret) verifier =
      (fun hidden => ((hidden, 2),
        ([⟨false, false⟩, ⟨true, hidden⟩] : OracleSpec.QueryLog ambient), 4)) <$>
        (coinSpec.query () : OracleComp coinSpec Bool)) ∧
    Pr{let result ← (executeStrategiesWithRuntime runtime inputImpl
      (prover guess secret) verifier)}[
      result.output.core.closed.map (TruthFinal result.output.core.path.toBranchPath) = some True] ≤
      (2 : ENNReal)⁻¹ := by
  refine ⟨first_returns_exported, ?_, native_import_budget guess secret,
    native_actual_history guess secret,
    guess_bound guess secret⟩
  intro boundary
  exact ⟨source_name boundary, (exported_certificate boundary).1,
    (exported_certificate boundary).2, routed_suffix_access boundary guess,
    routed_suffix_budget guess⟩

/-- A permitted query-informed native prover has real ambient cost seven and success one.
These access/cost observations do not repair its failed averaged half-error premise. -/
theorem informed_cost_does_not_give_half (secret : Nat) :
    ((fun result => (result.state, result.trace, ambientCharge result.trace)) <$>
      executeStrategiesWithRuntime runtime inputImpl (informedProver secret) verifier =
      (fun hidden => ((hidden, 3),
        ([⟨false, false⟩, ⟨true, hidden⟩, ⟨true, hidden⟩] : OracleSpec.QueryLog ambient), 7)) <$>
        (coinSpec.query () : OracleComp coinSpec Bool)) ∧
    Pr{let result ← (executeStrategiesWithRuntime runtime inputImpl
      (informedProver secret) verifier)}[
      result.output.core.closed.map (TruthFinal result.output.core.path.toBranchPath) = some True] =
      1 :=
  ⟨informed_native_history secret, informed_success secret⟩

end
end Interaction.Oracle.RuntimeQueryBoundsTest
