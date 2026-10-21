/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Oracle.Virtual
import ArkLib.ProofSystem.ToyProblem.Spec.SimplifiedIOR

/-! Acceptance of existing two-query virtual output programs by the derived-interface API. -/

open Interaction.Oracle OracleSpec

namespace Interaction.Oracle.VirtualTest

variable {ι F A : Type} [Fintype ι] [Field F] [AddCommGroup A] [Module F A]
  [DecidableEq ι] [Fintype A] [DecidableEq A]

/-- The existing toy protocol's explicit output interface. -/
def toyFamily : OracleFamily (Fin 1) (ToyProblem.SimplifiedIOR.OutputOracleStatement ι A) :=
  ⟨inferInstance⟩

/-- Reuse the existing output simulation without adding any stored denotation. -/
def toyVirtual (challenges : (ToyProblem.SimplifiedIOR.pSpec (F := F)).Challenges) :
    VirtualOracle
      ([]ₒ + ([ToyProblem.Spec.OracleStatement ι A]ₒ +
        [(ToyProblem.SimplifiedIOR.pSpec (F := F)).Message]ₒ))
      (toyFamily (ι := ι) (A := A)) :=
  let legacy := ToyProblem.SimplifiedIOR.outputSimulation (ι := ι) (F := F) (A := A)
  .ofQuery (legacy.simulateOutputQuery challenges)

example (challenges : (ToyProblem.SimplifiedIOR.pSpec (F := F)).Challenges)
    (impl : QueryImpl
      ([]ₒ + ([ToyProblem.Spec.OracleStatement ι A]ₒ +
        [(ToyProblem.SimplifiedIOR.pSpec (F := F)).Message]ₒ)) Id)
    (q : (toyFamily (ι := ι) (A := A)).spec.Domain) :
    (toyVirtual (ι := ι) (A := A) challenges).eval impl q =
      simulateQ impl
        (OracleOutputSimulation.simulateOutputQuery
          (ToyProblem.SimplifiedIOR.outputSimulation (ι := ι) (F := F) (A := A))
          challenges q) := rfl

/-- A scalar interface whose only query reveals its natural-number realization. -/
def scalarFamily : OracleFamily Unit (fun _ => Nat) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- Both source queries matter, with different coefficients. -/
def weightedQueries : VirtualOracle (Bool →ₒ Nat) scalarFamily where
  query _ := do
    let x : Nat ← liftM ((Bool →ₒ Nat).query false)
    let y : Nat ← liftM ((Bool →ₒ Nat).query true)
    return 2 * x + y

/-- The downstream program consumes the derived scalar and a separate suffix source. -/
def withSuffix : VirtualOracle (scalarFamily.spec + (Unit →ₒ Nat)) scalarFamily where
  query _ := do
    let x : Nat ← liftM ((scalarFamily.spec + (Unit →ₒ Nat)).query (.inl ⟨(), ()⟩))
    let y : Nat ← liftM ((scalarFamily.spec + (Unit →ₒ Nat)).query (.inr ()))
    return 10 * x + y

/-- Substitution preserves both upstream query routes and the distinct suffix answer. -/
example : (weightedQueries.substWithSuffix (Unit →ₒ Nat) withSuffix).eval
    (QueryImpl.add (fun bit => if bit then 7 else 3) (fun _ => 5)) ⟨(), ()⟩ = (135 : Nat) := rfl

/-- Reindexing interface types does not identify independently supplied realizations. -/
example :
    let repeated := scalarFamily.reindex (fun _ : Bool => ())
    let behavior := repeated.behaviorOfRealizations (fun bit => (if bit then 7 else 3 : Nat))
    (behavior ⟨false, ()⟩, behavior ⟨true, ()⟩) = ((3 : Nat), (7 : Nat)) := rfl

end Interaction.Oracle.VirtualTest
