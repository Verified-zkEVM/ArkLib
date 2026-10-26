/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Logup.Lookup.ArithmeticProver
public import ArkLib.ProofSystem.Logup.Prover.ArithmeticResources

/-!
# Resource corollaries for the actual scalar lookup default

The actual sender computes one histogram and retains its base multiplicities. Its continuation
is the selected weighted Unit driver on those same multiplicities. The existing weighted Cost
interpretation erases to that actual continuation, and its observer supplies the request bound.
No alternative scalar strategy, cost interpreter or execution-equality premise is introduced.

Write N=2^n,T=M+P,D=TN. Before alpha, the actual histogram has PN natural counters and consumes
MN supplied indices through MN increment sites; its multiplicity constructor has PN Nat-to-B
cast sites and P output tables of N cells. These are structural loop sites and dimensions, not
a Nat bit-operation or allocator theorem. Preparation visits D original base value cells and PN
retained multiplicity cells; synthetic weights have MN base-one entries and PN base-negation
sites. Mapping the value and weight families has 2D base-to-extension embedding sites. Opaque
embedding/primitive implementations, base signing/casts, supplying data/getters, source backends,
public sampling, annotation bookkeeping, storage/bytes and machine work remain separate from the
private ArithmeticSpec request profile. The geometric envelope is per coordinate; the nine-kind
sum has its separate explicit constant.
-/

@[expose] public section
open Interaction.Oracle OracleComp OracleSpec CompPoly
open scoped BigOperators
namespace Logup.Lookup.Honest.Resources

/-- The actual histogram and cast multiplicities have the stated index/table dimensions. -/
theorem multiplicities_dimensions {B : Type} [NatCast B] {n M P : Nat}
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) :
    indices.toArray.size = M * 2 ^ n ∧
      (Vector.histogram indices).toArray.size = P * 2 ^ n ∧
      (multiplicities (B := B) (n := n) (P := P) indices).toArray.size = P ∧
      (∑ p : Fin P,
        ((multiplicities (B := B) (n := n) (P := P) indices)[p.val]).toArray.size) = P * 2 ^ n := by
  simp

variable {B E : Type} [CommRing B] [Field E] [DecidableEq E] {n M P ell : Nat}

/-- The actual scalar sender retains the weighted Unit continuation on its actual sent mu. -/
theorem prover_continuation_eq (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (data : Logup.Lookup.Data B n M P)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) :
    let sent := simulateQ handler (Logup.Lookup.Honest.prover f cfg data indices ambient)
    sent.2 = Logup.Prover.Honest.prover f cfg.weighted (weightedData data sent.1) ambient := by
  rfl

/-- The existing Cost selection refines that exact retained continuation after output erasure. -/
theorem profile_erases_continuation (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (data : Logup.Lookup.Data B n M P)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) :
    let sent := simulateQ handler (Logup.Lookup.Honest.prover f cfg data indices ambient)
    Interaction.StrategyOver.TwoParty.Focal.mapOutput (fun _ _ => ())
      (Logup.Prover.Honest.Accounting.proverWith
        Logup.Prover.Honest.Accounting.costInterpreter Logup.Prover.Honest.Accounting.cost_erases
        (· + ·) 0 f cfg.weighted (weightedData data sent.1) ambient) = sent.2 := by
  dsimp only
  rw [Logup.Prover.Honest.Accounting.proverWith_erases_unit]
  rfl

/-- Each actual weighted request coordinate, with the actual retained mu, obeys 1012NTell. -/
theorem observed_prover_cost_le (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (data : Logup.Lookup.Data B n M P)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) (alpha : E)
    (joint : (Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E))
    (choices : Vector (Option E) n) (kind : ArithmeticCostKind) :
    let sent := simulateQ handler (Logup.Lookup.Honest.prover f cfg data indices ambient)
    (Logup.Prover.Honest.Accounting.observeProver ambient handler
      (Logup.Prover.Honest.Accounting.proverWith
        Logup.Prover.Honest.Accounting.costInterpreter Logup.Prover.Honest.Accounting.cost_erases
        (· + ·) 0 f cfg.weighted (weightedData data sent.1) ambient)
      alpha joint choices).2.2 kind ≤ 1012 * 2 ^ n * (M + P) * ell := by
  exact Logup.Prover.Honest.Accounting.Resources.observed_prover_cost_le_geometric
    f cfg.weighted _ ambient handler alpha joint choices kind

/-- The same actual retained continuation has a nine-coordinate total bound 9108NTell. -/
theorem observed_prover_total_cost_le (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (data : Logup.Lookup.Data B n M P)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) (alpha : E)
    (joint : (Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E))
    (choices : Vector (Option E) n) :
    let sent := simulateQ handler (Logup.Lookup.Honest.prover f cfg data indices ambient)
    let cost := (Logup.Prover.Honest.Accounting.observeProver ambient handler
      (Logup.Prover.Honest.Accounting.proverWith
        Logup.Prover.Honest.Accounting.costInterpreter Logup.Prover.Honest.Accounting.cost_erases
        (· + ·) 0 f cfg.weighted (weightedData data sent.1) ambient)
      alpha joint choices).2.2
    ([ArithmeticCostKind.add, .sub, .mul, .inv, .eq, .coefficientRead, .nodeRead,
      .valueRead, .metadata].map cost).sum ≤ 9108 * 2 ^ n * (M + P) * ell := by
  exact Logup.Prover.Honest.Accounting.Resources.observed_prover_total_cost_le
    f cfg.weighted _ ambient handler alpha joint choices

end Logup.Lookup.Honest.Resources
