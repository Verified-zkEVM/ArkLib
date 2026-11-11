/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Core.MessageEquivalence

/-! # Executable interpreted messages and effect-preserving transport -/

namespace Sumcheck.Core.InterpretedTest
open PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle OracleComp
  OracleSpec Interpreted

/-- A coefficient-pair message evaluated directly over the natural numbers. -/
def evaluate (msg : ℕ × ℕ) (r : ℕ) : ℕ := msg.1 * r + msg.2

/-- The verifier queries the message at both declared domain points, then at the challenge. -/
def checks : RoundChecks ℕ (fun _ => ℕ) := fun _ target r => OptionT.mk do
  let a ← liftM ((ℕ →ₒ ℕ).query 0)
  let b ← liftM ((ℕ →ₒ ℕ).query 1)
  if a + b = target then
    let value ← liftM ((ℕ →ₒ ℕ).query r)
    return some value
  else return none

/-- A concrete native prover with an explicit pure challenge-response slot and private output. -/
def prover : Focal oracleSig Id (Interpreted.protocol ℕ (ℕ × ℕ) evaluate 1) (fun _ => ℕ) :=
  show Id ((_msg : ℕ × ℕ) × Id (ℕ →
    Focal oracleSig Id (Interpreted.protocol ℕ (ℕ × ℕ) evaluate 0) (fun _ => ℕ))) from
    pure ⟨(3, 1), pure fun r => pure (r + 50)⟩

/-- The actual deterministic native run uses challenge `2` and retains original data `11`. -/
def runExample : ℕ × Option (ℕ × ℕ) :=
  execute (pure 2 : Id ℕ) checks id 1 5 11 prover

/-- The executable run accepts evaluation `7` and keeps its private output and original data. -/
example : runExample = (52, some (7, 11)) := rfl

#eval runExample

/-- Interpreting coefficient pairs as evaluation functions preserves the actual native run. -/
example :
    execute (pure 2 : Id ℕ) checks id 1 5 11
      (transportProver (evaluateN := fun (f : ℕ → ℕ) r => f r) evaluate 1 prover) =
      execute (pure 2 : Id ℕ) checks id 1 5 11 prover :=
  execute_transport (pure 2 : Id ℕ) checks id evaluate (fun _ _ => rfl) 1 5 11 prover

run_cmd
  for decl in [``Sumcheck.Core.Interpreted.run_transport,
      ``Sumcheck.Core.Interpreted.execute_eq_verifier,
      ``Sumcheck.Core.Interpreted.execute_transport,
      ``Sumcheck.Core.Interpreted.verifier_polynomial] do
    for ax in ← Lean.collectAxioms decl do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "unexpected axiom {ax} in {decl}"

end Sumcheck.Core.InterpretedTest
