/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Logup.Lookup.Tuple.ArithmeticCompression
public import ArkLib.ProofSystem.Logup.Lookup.Tuple.Prover
public import ArkLib.ProofSystem.Logup.Prover.ArithmeticStrategy
public import ArkLib.ProofSystem.Logup.Prover.ArithmeticLedger

-- The erasure proof unfolds the defining output map and paired strategy shape.
import all PolyFun.Interaction.Basic.StrategyOver
import all PolyFun.Interaction.TwoParty.Strategy

/-!
# Default tuple prover with eager beta compression

Compute the base histogram once before beta, then execute the selected compression program and
delegate to the weighted Unit driver on cached value/weight getters. The same prefix control also
admits the existing arithmetic-profile and weighted-call interpretations. Its observer follows the
actual sent histogram, beta response, helpers and optional native choices.

The compression profile is a separate initial annotation for the weighted call ledger. Base casts,
opaque embeddings, natural-number work, source backends, storage and machine costs retain their
separate boundaries. Correctness equality to the explicit-builder strategy transfers no cost bound.
-/

@[expose] public section

open Interaction.Oracle OracleComp OracleSpec CompPoly
namespace Logup.Lookup.Tuple.Honest
variable {B E : Type} [CommRing B] [Field E] [DecidableEq E]
variable {b W n M P ell : Nat} {schema : TaggedTuple.Schema B b W}
variable {layout : ProviderLayout b P}

namespace Accounting
variable {C : Type}

@[no_expose] private def prefixWith
    (runCache : OracleComp (ArithmeticSpec E)
      (Vector (Vector (CMlPolynomialEval E n) (M + P)) 2) →
      Vector (Vector (CMlPolynomialEval E n) (M + P)) 2 × C)
    (run : Logup.Prover.Honest.Accounting.Interpreter E E C (M + P) ((M + P) ⌈/⌉ ell))
    (law : Logup.Prover.Honest.Accounting.Erases run) (combine : C → C → C) (initial : C)
    (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (prepared : PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    {ι : Type} (ambient : OracleSpec ι) :
    Prover.Strategy ambient (protocol f n M P ell).tree (protocol f n M P ell).roles
      (fun _ => C) :=
  let mu := multiplicities (B := B) (n := n) (P := P) indices
  pure ⟨mu, fun beta => pure (
    let cache := runCache (compressedTablesProgram f prepared beta mu)
    Logup.Prover.Honest.Accounting.proverWith run law combine (combine initial cache.2)
      (RingHom.id E) cfg.weighted (compressedData cache.1) ambient)⟩

/-- Follow the actual sender and beta response, then the existing weighted control observer. -/
def observeProver {ι : Type} (ambient : OracleSpec ι) (handler : QueryImpl ambient Id)
    (f : B →+* E)
    (strategy : Prover.Strategy ambient (protocol f n M P ell).tree
      (protocol f n M P ell).roles (fun _ => C))
    (beta alpha : E) (joint : (Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E))
    (choices : Vector (Option E) n) :
    Vector (CMlPolynomialEval B n) P ×
      Vector (CMlPolynomialEval E n) ((M + P) ⌈/⌉ ell) ×
      List (Sumcheck.Impl.Representation.Message E (ell + 2)) × C :=
  let sent := simulateQ handler strategy
  let continuation := simulateQ handler (sent.2 beta)
  (sent.1, Logup.Prover.Honest.Accounting.observeProver ambient handler continuation
    alpha joint choices)

private theorem observe_prefixWith
    (runCache : OracleComp (ArithmeticSpec E)
      (Vector (Vector (CMlPolynomialEval E n) (M + P)) 2) →
      Vector (Vector (CMlPolynomialEval E n) (M + P)) 2 × C)
    (run : Logup.Prover.Honest.Accounting.Interpreter E E C (M + P) ((M + P) ⌈/⌉ ell))
    (law : Logup.Prover.Honest.Accounting.Erases run) (combine : C → C → C) (initial : C)
    (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (prepared : PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    {ι : Type} (ambient : OracleSpec ι) (handler : QueryImpl ambient Id)
    (beta alpha : E) (joint : (Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E))
    (choices : Vector (Option E) n) :
    observeProver ambient handler f
      (prefixWith runCache run law combine initial f cfg prepared indices ambient)
      beta alpha joint choices =
    let mu := multiplicities (B := B) (n := n) (P := P) indices
    let cache := runCache (compressedTablesProgram f prepared beta mu)
    (mu, Logup.Prover.Honest.Accounting.observeProver ambient handler
      (Logup.Prover.Honest.Accounting.proverWith run law combine (combine initial cache.2)
        (RingHom.id E) cfg.weighted (compressedData cache.1) ambient) alpha joint choices) := rfl

end Accounting

/-- Send the base histogram, materialize both E-table families after beta, then run the measured
weighted Unit driver on their getters. -/
@[no_expose] def prover (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (prepared : PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    {ι : Type} (ambient : OracleSpec ι) :
    Prover.Strategy ambient (protocol f n M P ell).tree (protocol f n M P ell).roles
      (fun _ => Unit) :=
  Accounting.prefixWith (fun program => (simulateQ arithmeticAnswer program, ()))
    Logup.Prover.Honest.Accounting.unitInterpreter Logup.Prover.Honest.Accounting.unit_erases
    (fun _ _ => ()) () f cfg prepared indices ambient

/-- The ordinary beta response executes the literal selected cache program once before returning
the actual weighted default strategy. -/
theorem prover_eq_sender_beta_cache (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (prepared : PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) {ι : Type} (ambient : OracleSpec ι) :
    prover f cfg prepared indices ambient =
      let mu := multiplicities (B := B) (n := n) (P := P) indices
      pure ⟨mu, fun beta => pure (
        let cache := simulateQ arithmeticAnswer (compressedTablesProgram f prepared beta mu)
        Logup.Prover.Honest.prover (RingHom.id E) cfg.weighted
          (compressedData cache) ambient)⟩ := by
  rfl

/-- The actual cached default equals the existing explicit-builder correctness strategy. -/
theorem prover_eq_proverWith (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (prepared : PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) {ι : Type} (ambient : OracleSpec ι) :
    prover f cfg prepared indices ambient = proverWith f cfg prepared indices ambient
      (Logup.Prover.Honest.pureBuilder cfg.weighted.groups cfg.weighted.length_group_le) := by
  simp only [prover, Accounting.prefixWith, proverWith]
  congr 1
  congr 1
  funext beta
  change E at beta
  congr 1
  change Logup.Prover.Honest.prover (RingHom.id E) cfg.weighted
    (compressedData (simulateQ arithmeticAnswer (compressedTablesProgram f prepared beta
      (multiplicities (B := B) (n := n) (P := P) indices)))) ambient = _
  rw [simulateQ_compressedTablesProgram, Logup.Prover.Honest.prover_eq_honestWith]

namespace Accounting

set_option backward.isDefEq.respectTransparency false in
private theorem prefixWith_erases_unit {C : Type}
    (runCache : OracleComp (ArithmeticSpec E)
      (Vector (Vector (CMlPolynomialEval E n) (M + P)) 2) →
      Vector (Vector (CMlPolynomialEval E n) (M + P)) 2 × C)
    (hcache : ∀ program, (runCache program).1 = simulateQ arithmeticAnswer program)
    (run : Logup.Prover.Honest.Accounting.Interpreter E E C (M + P) ((M + P) ⌈/⌉ ell))
    (law : Logup.Prover.Honest.Accounting.Erases run) (combine : C → C → C) (initial : C)
    (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (prepared : PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) {ι : Type} (ambient : OracleSpec ι) :
    Interaction.StrategyOver.TwoParty.Focal.mapOutput (fun _ _ => ())
      (prefixWith runCache run law combine initial f cfg prepared indices ambient) =
      prover f cfg prepared indices ambient := by
  simp only [prover, prefixWith,
    Interaction.StrategyOver.TwoParty.Focal.mapOutput, Interaction.ShapeOver.mapOutput,
    Interaction.ShapeOver.TwoParty.pairedTypeTree, Interaction.ShapeOver.TwoParty.paired,
    PFunctor.Lens.id, protocol, Protocol.oracleWith, Protocol.public, Protocol.tree, Protocol.roles,
    Protocol.oracles, TypeTree.public, TypeTree.oracle, TypeTree.toTypeTree,
    PFunctor.FreeM.mapLens, TypeTree.runtimeLens, TypeTree.RoleDecoration.toTypeTreeRoles, map_pure]
  congr 1
  congr 1
  funext beta
  change E at beta
  congr 1
  change Interaction.StrategyOver.TwoParty.Focal.mapOutput (fun _ _ => ())
    (Logup.Prover.Honest.Accounting.proverWith run law combine _ (RingHom.id E) cfg.weighted
      (compressedData (runCache (compressedTablesProgram f prepared beta
        (multiplicities (B := B) (n := n) (P := P) indices))).1) ambient) = _
  rw [Logup.Prover.Honest.Accounting.proverWith_erases_unit, hcache]

/-- Interpret the literal beta cache program and weighted calls with their request profiles. -/
@[no_expose] def profiledProver (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (prepared : PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) {ι : Type} (ambient : OracleSpec ι) :
    Prover.Strategy ambient (protocol f n M P ell).tree (protocol f n M P ell).roles
      (fun _ => ArithmeticCost) :=
  prefixWith profileArithmetic Logup.Prover.Honest.Accounting.costInterpreter
    Logup.Prover.Honest.Accounting.cost_erases (· + ·) 0 f cfg prepared indices ambient

/-- Execute the same cache program and record the existing weighted calls with their cached data. -/
@[no_expose] def recordedProver (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (prepared : PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) {ι : Type} (ambient : OracleSpec ι) :
    Prover.Strategy ambient (protocol f n M P ell).tree (protocol f n M P ell).roles
      (fun _ => List (Logup.Prover.Honest.Accounting.Call E E (M + P) ((M + P) ⌈/⌉ ell))) :=
  prefixWith (fun program => (simulateQ arithmeticAnswer program, []))
    Logup.Prover.Honest.Accounting.callInterpreter Logup.Prover.Honest.Accounting.call_erases
    (· ++ ·) [] f cfg prepared indices ambient

/-- Forgetting measured annotations recovers the actual ordinary tuple default. -/
theorem profiledProver_erases (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (prepared : PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) {ι : Type} (ambient : OracleSpec ι) :
    Interaction.StrategyOver.TwoParty.Focal.mapOutput (fun _ _ => ())
      (profiledProver f cfg prepared indices ambient) = prover f cfg prepared indices ambient :=
  prefixWith_erases_unit profileArithmetic (fun program => profileArithmetic_fst program)
    Logup.Prover.Honest.Accounting.costInterpreter Logup.Prover.Honest.Accounting.cost_erases
    (· + ·) 0 f cfg prepared indices ambient

/-- Forgetting recorded weighted calls recovers the same ordinary tuple default. -/
theorem recordedProver_erases (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (prepared : PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) {ι : Type} (ambient : OracleSpec ι) :
    Interaction.StrategyOver.TwoParty.Focal.mapOutput (fun _ _ => ())
      (recordedProver f cfg prepared indices ambient) = prover f cfg prepared indices ambient :=
  prefixWith_erases_unit (fun program => (simulateQ arithmeticAnswer program, [])) (fun _ => rfl)
    Logup.Prover.Honest.Accounting.callInterpreter Logup.Prover.Honest.Accounting.call_erases
    (· ++ ·) [] f cfg prepared indices ambient

/-- The complete actual profile is compression plus charges for the same recorded weighted calls,
with exactly the same sent histogram, helpers and coefficient messages. -/
theorem observe_profiledProver_eq_compression_add_charges
    (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (prepared : PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    {ι : Type} (ambient : OracleSpec ι) (handler : QueryImpl ambient Id)
    (beta alpha : E) (joint : (Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E))
    (choices : Vector (Option E) n) :
    observeProver ambient handler f (profiledProver f cfg prepared indices ambient)
      beta alpha joint choices =
    let observed := observeProver ambient handler f (recordedProver f cfg prepared indices ambient)
      beta alpha joint choices
    (observed.1, observed.2.1, observed.2.2.1,
      compressionCost n M P W + Logup.Prover.Honest.Accounting.charges observed.2.2.2) := by
  rw [profiledProver, recordedProver,
    observe_prefixWith (law := Logup.Prover.Honest.Accounting.cost_erases),
    observe_prefixWith (law := Logup.Prover.Honest.Accounting.call_erases)]
  simp only [zero_add, List.nil_append, profileArithmetic_fst]
  have h := congrArg
    (fun observed => (multiplicities (B := B) (n := n) (P := P) indices, observed))
    (Logup.Prover.Honest.Accounting.prover_cost_eq_initial_add_charges
      (RingHom.id E) cfg.weighted
      (compressedData (simulateQ arithmeticAnswer (compressedTablesProgram f prepared beta
        (multiplicities (B := B) (n := n) (P := P) indices))))
      ambient handler alpha joint choices
      (profileArithmetic (compressedTablesProgram f prepared beta
        (multiplicities (B := B) (n := n) (P := P) indices))).2)
  simpa only [profileArithmetic_compressedTablesProgram] using h

end Accounting
end Logup.Lookup.Tuple.Honest
