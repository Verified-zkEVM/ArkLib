/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
import ArkLib.ProofSystem.ConstraintSystem.Basic
import Clean.Circuit.Foundations

/-!
# Clean ↔ ArkLib Bridge via ConstraintSystem

This module bridges Clean's `FormalCircuit` to ArkLib's `ConstraintSystem` and
`BehavioralContract` abstractions, transferring circuit-level security guarantees
(soundness and completeness) to ArkLib's universal constraint system interface.

A Clean `FormalCircuit F Input Output` maps to:
- A `ConstraintSystem` where `satisfies` checks input consistency (`eval env inputVar = inp`)
  and circuit constraint satisfaction (`ConstraintsHold`).
- A `BehavioralContract` where `Assumptions` and `Spec` are transferred directly from the
  circuit, with soundness proved via `original_soundness` and completeness via
  `original_completeness`.

## Main definitions

- `Clean.toConstraintSystem`: wraps a `FormalCircuit` as a `ConstraintSystem`
- `Clean.toBehavioralContract`: wraps a `FormalCircuit` as a `BehavioralContract`,
  transferring both Clean security properties

## Dependencies

Targets upstream [Verified-zkEVM/clean](https://github.com/Verified-zkEVM/clean) at pinned
commit `4a013fed` (post toolchain-bump-v4.28 merge via clean#357).
-/

open Circuit

namespace Clean.Bridge

variable {F : Type} [Field F]
  {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]

/-- The canonical variable encoding for the input type, starting at offset 0. -/
abbrev canonicalInputVar (Input : TypeMap) (F : Type) [Field F] [ProvableType Input] :
    Var Input F :=
  varFromOffset Input 0

/-- A Clean `FormalCircuit` viewed as an ArkLib `ConstraintSystem`.

The single index `Unit` reflects that one circuit is one constraint system (no size family).
The in-the-clear statement `Stmt` carries the public input. The oracle statement `OStmt`
carries the committed output — the prover commits to an output value and the constraint
system verifies consistency. `satisfies` checks input encoding, circuit constraints, and
output consistency. -/
def toConstraintSystem (circuit : FormalCircuit F Input Output) :
    ConstraintSystem where
  Index := Unit
  Stmt := fun _ => Input F
  OStmt := fun _ => Output F
  Wit := fun _ => Environment F
  satisfies := fun _ inp out env =>
    eval env (canonicalInputVar Input F) = inp ∧
    ConstraintsHold env
      (circuit.main (canonicalInputVar Input F) |>.operations 0) ∧
    eval env (circuit.output (canonicalInputVar Input F) 0) = out

/-- A Clean `FormalCircuit` viewed as an ArkLib `BehavioralContract`.

- **Soundness**: Clean's `original_soundness` guarantees that if assumptions hold and
  constraints are satisfied, the circuit output satisfies `Spec`.
- **Completeness**: Clean's `original_completeness` guarantees that if assumptions hold
  and a witness environment exists (encoding the input with valid local witnesses),
  constraints are satisfied and the output meets the spec.

The output lives in `OStmt` (oracle/committed statement) rather than `Stmt`, reflecting
ZK semantics: the prover commits to the output, and completeness existentially quantifies
over it.

The `hWitGen` parameter asserts that for every input satisfying `Assumptions`, there exists
an environment encoding that input and using the circuit's local witness generators. This
is guaranteed by Clean's circuit construction (witness generators are deterministic functions
over the input), but is not directly exported as an existence theorem in Clean's API. -/
noncomputable def toBehavioralContract (circuit : FormalCircuit F Input Output)
    (hWitGen : ∀ inp, circuit.Assumptions inp → ∃ env : Environment F,
        eval env (canonicalInputVar Input F) = inp ∧
        env.UsesLocalWitnesses 0
          (circuit.main (canonicalInputVar Input F) |>.operations 0)) :
    ConstraintSystem.BehavioralContract (toConstraintSystem circuit) () where
  Assumptions := fun inp => circuit.Assumptions inp
  Spec := fun inp env =>
    circuit.Spec inp (eval env (circuit.output (canonicalInputVar Input F) 0))
  soundness := fun inp _ env hAssume ⟨hEval, hConstr, _⟩ =>
    circuit.original_soundness 0 env (canonicalInputVar Input F) inp hEval hAssume hConstr
  completeness := fun inp hAssume => by
    obtain ⟨env, hEval, hLocalWit⟩ := hWitGen inp hAssume
    have hConstr := circuit.original_completeness 0 env
      (canonicalInputVar Input F) inp hEval hAssume hLocalWit
    have hSpec := circuit.original_soundness 0 env
      (canonicalInputVar Input F) inp hEval hAssume hConstr
    exact ⟨eval env (circuit.output (canonicalInputVar Input F) 0), env,
      ⟨hEval, hConstr, rfl⟩, hSpec⟩

end Clean.Bridge
