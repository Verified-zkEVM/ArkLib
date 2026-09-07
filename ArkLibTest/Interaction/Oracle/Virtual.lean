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

end Interaction.Oracle.VirtualTest
