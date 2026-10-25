/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Lookup.Tuple.ArithmeticResources
import ArkLibTest.ProofSystem.Logup.Lookup.ArithmeticProver
import ArkLibTest.ProofSystem.Logup.Lookup.Tuple.ArithmeticProver
import Lean.Compiler.IR

/-! # Actual retained scalar continuation and tuple compression-prefix resource bounds -/

open Interaction.Oracle OracleComp OracleSpec CompPoly
namespace FrontendResourcesTests
abbrev kinds := [ArithmeticCostKind.add, .sub, .mul, .inv, .eq, .coefficientRead, .nodeRead,
  .valueRead, .metadata]

namespace Scalar
open LogupScalarHonestTest.Small
def handler : QueryImpl ambient Id := fun _ => 0
def joint : (Fin 1 → F) × (Fin 3 → F) := ((fun _ => 2), ![4, 9, 6])
def sent (witness : Vector (Fin 4) 2) :=
  simulateQ handler (Logup.Lookup.Honest.prover f cfg data witness ambient)
def costed (witness : Vector (Fin 4) 2) (alpha : F) (choice : Option F) :=
  Logup.Prover.Honest.Accounting.observeProver ambient handler
    (Logup.Prover.Honest.Accounting.proverWith
      Logup.Prover.Honest.Accounting.costInterpreter Logup.Prover.Honest.Accounting.cost_erases
      (· + ·) 0
      f cfg.weighted (Logup.Lookup.weightedData data (sent witness).1) ambient)
    alpha joint #v[choice]

theorem coordinate (witness : Vector (Fin 4) 2) (alpha : F) (choice : Option F)
    (kind : ArithmeticCostKind) :
    (costed witness alpha choice).2.2 kind ≤ 1012 * 2 ^ 1 * (1 + 2) * 1 :=
  Logup.Lookup.Honest.Resources.observed_prover_cost_le
    f cfg data witness ambient handler alpha joint #v[choice] kind

theorem total (witness : Vector (Fin 4) 2) (alpha : F) (choice : Option F) :
    (kinds.map (costed witness alpha choice).2.2).sum ≤ 9108 * 2 ^ 1 * (1 + 2) * 1 :=
  Logup.Lookup.Honest.Resources.observed_prover_total_cost_le
    f cfg data witness ambient handler alpha joint #v[choice]

theorem actual_continuation (witness : Vector (Fin 4) 2) :
    (sent witness).2 =
      Logup.Prover.Honest.prover f cfg.weighted
        (Logup.Lookup.weightedData data (sent witness).1) ambient :=
  Logup.Lookup.Honest.Resources.prover_continuation_eq f cfg data witness ambient handler
end Scalar

namespace Tuple
open LogupTupleHonestTest.Small
theorem coordinate (beta alpha : F) (choice : Option F) (kind : ArithmeticCostKind) :
    (LogupTupleDefaultTest.Small.profiled beta alpha choice).2.2.2 kind ≤
      Logup.Lookup.Tuple.compressionCost 1 1 3 2 kind + 1012 * 2 ^ 1 * (1 + 3) * 1 :=
  Logup.Lookup.Tuple.Honest.Accounting.Resources.observed_prover_cost_le f cfg prepared indices
    ambient (LogupTupleDefaultTest.Small.handler beta alpha) beta alpha
    LogupTupleDefaultTest.Small.fixedJoint #v[choice] kind

theorem total (beta alpha : F) (choice : Option F) :
    (kinds.map (LogupTupleDefaultTest.Small.profiled beta alpha choice).2.2.2).sum ≤
      ((1 + 3) * 2 ^ 1) * (3 * 2 + 3) + 2 * 1 * 2 ^ 1 + 4 * 3 * 2 ^ 1 +
        9108 * 2 ^ 1 * (1 + 3) * 1 :=
  Logup.Lookup.Tuple.Honest.Accounting.Resources.observed_prover_total_cost_le f cfg prepared
    indices ambient (LogupTupleDefaultTest.Small.handler beta alpha) beta alpha
    LogupTupleDefaultTest.Small.fixedJoint #v[choice]
end Tuple

open Lean Elab Command in
run_cmd do
  for witness in [LogupScalarHonestTest.Small.indices, #v[0, 1]] do
    let mu : Vector (CMlPolynomialEval LogupScalarHonestTest.Small.F 1) 2 :=
      (Scalar.sent witness).1
    unless mu == Logup.Lookup.multiplicities witness do
      throwError "scalar resources lost the actual retained histogram"
    for alpha in [(0 : LogupScalarHonestTest.Small.F), 2, 5] do
      for choice in [none, some 5] do
        let measured := Scalar.costed witness alpha choice
        for kind in kinds do
          unless measured.2.2 kind ≤ 1012 * 2 * 3 do
            throwError "scalar actual stopped/pole continuation exceeded its coordinate envelope"
        unless (kinds.map measured.2.2).sum ≤ 9108 * 2 * 3 do
          throwError "scalar actual continuation exceeded its nine-kind total envelope"
  for beta in [(0 : LogupTupleHonestTest.Small.F), 1] do
    for alpha in [(0 : LogupTupleHonestTest.Small.F), 2, 5] do
      for choice in [none, some 5] do
        let measured := LogupTupleDefaultTest.Small.profiled beta alpha choice
        for kind in kinds do
          unless measured.2.2.2 kind ≤
              Logup.Lookup.Tuple.compressionCost 1 1 3 2 kind + 1012 * 2 * 4 do
            throwError "tuple actual stopped/pole observation lost its compression prefix"
        unless (kinds.map measured.2.2.2).sum ≤ 100 + 9108 * 2 * 4 do
          throwError "tuple actual nine-kind observation exceeded cache plus weighted envelope"
  unless (kinds.map (Logup.Lookup.Tuple.compressionCost 1 1 3 2)).sum == 100 &&
      (kinds.map (Logup.Lookup.Tuple.compressionCost 2 1 3 2)).sum == 200 do
    throwError "exact nine-kind compression total changed"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Logup.Lookup.Honest.Resources.multiplicities_dimensions,
      ``Logup.Lookup.Honest.Resources.prover_continuation_eq,
      ``Logup.Lookup.Honest.Resources.profile_erases_continuation,
      ``Logup.Lookup.Honest.Resources.observed_prover_cost_le,
      ``Logup.Lookup.Honest.Resources.observed_prover_total_cost_le,
      ``Logup.Lookup.Tuple.Honest.Accounting.Resources.observe_recordedProver_eq,
      ``Logup.Lookup.Tuple.Honest.Accounting.Resources.observed_prover_cost_le,
      ``Logup.Lookup.Tuple.Honest.Accounting.Resources.compressionCost_total,
      ``Logup.Lookup.Tuple.Honest.Accounting.Resources.observed_prover_total_cost_le,
      ``Scalar.coordinate, ``Scalar.total, ``Scalar.actual_continuation,
      ``Tuple.coordinate, ``Tuple.total] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected frontend actual-resource axioms: {name}"
  for name in #[``Scalar.sent, ``Scalar.costed] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "actual retained-sender resource fixture lost executable IR"
  logInfo "scalar retained-mu and tuple cache-prefix actual observations: poles/stops/all9 passed"

end FrontendResourcesTests
