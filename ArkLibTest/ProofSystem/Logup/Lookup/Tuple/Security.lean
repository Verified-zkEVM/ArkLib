/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Logup.Lookup.Tuple.Security
import ArkLibTest.ProofSystem.Logup.Lookup.Tuple.Fixture
import Lean.Compiler.IR

/-! # Whole native tuple endpoint bound on genuinely false semantic lookup membership -/

open _root_.Interaction.Oracle OracleComp OracleSpec CompPoly Logup.Lookup Logup.Lookup.Tuple
open scoped ProbabilityTheory ENNReal
open Lean Elab Command
namespace LogupTupleSecurityTest
open LogupTupleProtocolFixture

theorem distinct_keys : prepared.occurringKeys.card = 3 := by decide

theorem bound {OutP : combined.tree.ExecutionPath → Type}
    (prover : Prover.Strategy unifSpec combined.tree combined.roles OutP) :
    Pr{let accepted ←
      Tuple.uniformExecute f 1 1 2 2 1 cfg access view impl prover}[accepted = true] ≤
      (14 : ℝ≥0∞) / 17 := by
  have h := Tuple.uniformExecute_soundness f 1 1 2 2 1 cfg prepared access view impl realizes
    prover false_lookup
  simpa only [distinct_keys, Nat.reduceSub, Nat.reducePow, Nat.reduceAdd, Nat.reduceMul,
    Nat.cast_ofNat, ZMod.card] using h

theorem bound_lt_one : (14 : ℝ≥0∞) / 17 < 1 := by
  simpa only [ENNReal.div_self (a := (17 : ℝ≥0∞)) (by norm_num) (by norm_num)] using
    ENNReal.div_lt_div_right (c := (17 : ℝ≥0∞)) (by norm_num) (by norm_num)
      (show (14 : ℝ≥0∞) < 17 by norm_num)

-- An ordinary malicious whole strategy; the bound quantifies over all others as well.
def zeroNative {ι : Type} (ambient : OracleSpec ι) (deg : Nat) :
    (count : Nat) →
      Prover.Strategy ambient (Sumcheck.Interaction.Computable.protocol F deg count).tree
        (Sumcheck.Interaction.Computable.protocol F deg count).roles (fun _ => Nat)
  | 0 => (7 : Nat)
  | count + 1 => pure ⟨(⟨0, by simp⟩ : Sumcheck.Impl.Representation.Message F deg),
      fun choice => match choice with
      | none => pure (7 : Nat)
      | some _ => pure (zeroNative ambient deg count)⟩

def zeroWeighted {ι : Type} (ambient : OracleSpec ι) :
    Prover.Strategy ambient (Logup.Interaction.protocol F 1 3 1).tree
      (Logup.Interaction.protocol F 1 3 1).roles (fun _ => Nat) :=
  fun _ => pure (pure ⟨Vector.replicate 3 #v[0, 0], fun _ => pure (zeroNative ambient 3 1)⟩)
def zeroWhole : Prover.Strategy unifSpec combined.tree combined.roles (fun _ => Nat) :=
  pure ⟨mu, fun (_ : F) => pure (zeroWeighted unifSpec)⟩
def uniformEndpoint : ProbComp Bool :=
  Tuple.uniformExecute f 1 1 2 2 1 cfg access view impl zeroWhole

theorem actual_uniform_bound :
    Pr{let accepted ← uniformEndpoint}[accepted = true] ≤ (14 : ℝ≥0∞) / 17 := bound zeroWhole

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Tuple.uniformExecute_soundness, ``distinct_keys, ``bound, ``bound_lt_one,
      ``actual_uniform_bound] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "tuple whole program security has an unexpected axiom: {name}"
  for name in #[``uniformEndpoint, ``zeroNative, ``zeroWeighted, ``zeroWhole] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing actual named tuple endpoint caller IR: {name}"
end LogupTupleSecurityTest
