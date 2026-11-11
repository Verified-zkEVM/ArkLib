/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Oracle.ResourceOps
import ArkLib.ProofSystem.ToyProblem.Spec.SimplifiedIOR

/-!
# Derived oracles as oracle maps

A derived scalar oracle combines two source queries. Composing it with a map that also reads a
separate suffix oracle keeps both source routes and the suffix answer. Reindexing an interface
family does not identify independently supplied realizations.
-/

open Interaction.Core Interaction.Oracle OracleComp OracleSpec

namespace Interaction.Core.VirtualTests

section ToyProblem

variable {ι F A : Type} [Fintype ι] [Field F] [AddCommGroup A] [Module F A]
    [DecidableEq ι] [Fintype A] [DecidableEq A]

/-- Reuse the toy protocol's simulation for every pure handler of its input specification. -/
def toyMap (challenges : (ToyProblem.SimplifiedIOR.pSpec (F := F)).Challenges) :=
  OracleMap.ofQuery
    (Resources.ofSpec ([]ₒ + ([ToyProblem.Spec.OracleStatement ι A]ₒ +
      [(ToyProblem.SimplifiedIOR.pSpec (F := F)).Message]ₒ)))
    ([ToyProblem.SimplifiedIOR.OutputOracleStatement ι A]ₒ)
    (ToyProblem.SimplifiedIOR.outputSimulation.simulateOutputQuery challenges)

-- Virtual V1: arbitrary pure handlers remain arbitrary; no materialized input data is assumed.
/-- The output behavior agrees with the original toy simulation on every query and handler. -/
example (challenges : (ToyProblem.SimplifiedIOR.pSpec (F := F)).Challenges)
    (impl : QueryImpl
      ([]ₒ + ([ToyProblem.Spec.OracleStatement ι A]ₒ +
        [(ToyProblem.SimplifiedIOR.pSpec (F := F)).Message]ₒ)) Id)
    (q : [ToyProblem.SimplifiedIOR.OutputOracleStatement ι A]ₒ.Domain) :
    (toyMap (ι := ι) (A := A) challenges).f impl q =
      simulateQ impl (ToyProblem.SimplifiedIOR.outputSimulation.simulateOutputQuery challenges q) :=
  rfl

end ToyProblem

/-- A scalar interface whose only query reveals its natural-number realization. -/
@[instance_reducible] def scalarFamily : OracleFamily Unit (fun _ => Nat) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- Two scalar source slots. -/
@[instance_reducible] def source : OracleFamily Bool (fun _ => Nat) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- The separate suffix oracle. -/
@[instance_reducible] def suffix : OracleFamily Unit (fun _ => Nat) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- Both source queries matter, with different coefficients. -/
def weightedQueries : OracleMap source scalarFamily where
  f x _ := 2 * x false + x true
  impl _ := do
    let x : Nat ← liftM (source.spec.query ⟨false, ()⟩)
    let y : Nat ← liftM (source.spec.query ⟨true, ()⟩)
    pure (2 * x + y)
  law _ _ := rfl

/-- The downstream map consumes the derived scalar and the suffix oracle. -/
def withSuffix : OracleMap (sumFamily scalarFamily (suffix.reindex id)) scalarFamily where
  f x _ := 10 * (show Nat from x (.inl ())) + (show Nat from x (.inr ()))
  impl _ := do
    let x : Nat ← liftM ((sumFamily scalarFamily (suffix.reindex id)).spec.query ⟨.inl (), ()⟩)
    let y : Nat ← liftM ((sumFamily scalarFamily (suffix.reindex id)).spec.query ⟨.inr (), ()⟩)
    pure (10 * x + y)
  law _ _ := rfl

/-- Substitute the derived scalar, and pass the suffix oracle through unchanged. -/
def substituted : OracleMap (sumFamily source suffix) scalarFamily :=
  withSuffix.comp (weightedQueries.sum (OracleMap.embedding suffix id))

/-- Source slot `false` holds 3, slot `true` holds 7, and the suffix holds 5. -/
def data : ∀ k, (sumFamily source suffix).Realization k :=
  sumData (fun bit => if bit then 7 else 3) (fun _ => 5)

-- Virtual V2, restated: the frozen `substWithSuffix` becomes `OracleMap.comp` with
-- `OracleMap.sum` of the derived map and the identity embedding of the suffix; the map also
-- supplies the materialized data. Both the simulated query and the data give
-- `10 * (2 * 3 + 7) + 5 = 135`. Not weaker.
example : simulateQ ((sumFamily source suffix).behaviorOfRealizations data)
    (substituted.impl ⟨(), ()⟩) = (135 : Nat) := rfl

example : substituted.f data () = 135 := rfl

-- Virtual V3: unchanged, since its providers (`OracleFamily.reindex`, `behaviorOfRealizations`)
-- are outside the frozen interaction layer and remain available.
/-- Reindexing interface types does not identify independently supplied realizations. -/
example :
    let repeated := scalarFamily.reindex (fun _ : Bool => ())
    let behavior := repeated.behaviorOfRealizations (fun bit => (if bit then 7 else 3 : Nat))
    (behavior ⟨false, ()⟩, behavior ⟨true, ()⟩) = ((3 : Nat), (7 : Nat)) := rfl

end Interaction.Core.VirtualTests
