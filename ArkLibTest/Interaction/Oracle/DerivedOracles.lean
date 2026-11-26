/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.OracleVerifier
import ArkLib.Relation.OracleBundle
import ArkLib.ProofSystem.ToyProblem.Spec.SimplifiedIOR

/-!
# Derived oracles as oracle maps

A derived scalar oracle combines two source queries. Composing it with a map that also reads a
separate suffix oracle keeps both source routes and the suffix answer. Reindexing an indexed
bundle does not identify independently supplied data.
-/

open Interaction Interaction.Oracle OracleComp OracleSpec

namespace Interaction.DerivedOraclesTests

section ToyProblem

variable {ι F A : Type} [Fintype ι] [Field F] [AddCommGroup A] [Module F A]
    [DecidableEq ι] [Fintype A] [DecidableEq A]

/-- Reuse the toy protocol's simulation for every pure handler of its input specification. -/
def toyMap (challenges : (ToyProblem.SimplifiedIOR.pSpec (F := F)).Challenges) :=
  OracleMap.ofImpl
    (OracleBundle.ofSpec ([]ₒ + ([ToyProblem.Spec.OracleStatement ι A]ₒ +
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

/-- A scalar oracle whose only query reveals its natural-number data. -/
abbrev scalarSlot (_ : Unit) : OracleBundle := OracleBundle.of Nat OracleInterface.instDefault

/-- A scalar source oracle at each Boolean index. -/
abbrev sourceSlot (_ : Bool) : OracleBundle := OracleBundle.of Nat OracleInterface.instDefault

/-- The scalar oracle of the suffix. -/
abbrev suffixSlot (_ : Unit) : OracleBundle := OracleBundle.of Nat OracleInterface.instDefault

/-- One scalar oracle. -/
def scalarFamily : OracleBundle := OracleBundle.indexed scalarSlot

/-- Two scalar source oracles. -/
def source : OracleBundle := OracleBundle.indexed sourceSlot

/-- The separate suffix oracle. -/
def suffix : OracleBundle := OracleBundle.indexed suffixSlot

/-- Both source queries matter, with different coefficients. -/
def weightedQueries : OracleMap source scalarFamily where
  f x _ := 2 * x false + x true
  impl _ := do
    let x : Nat ← liftM (source.spec.query ⟨false, ()⟩)
    let y : Nat ← liftM (source.spec.query ⟨true, ()⟩)
    pure (2 * x + y)
  law _ _ := rfl

/-- The downstream map consumes the derived scalar and the suffix oracle. -/
def withSuffix : OracleMap
    (scalarFamily.sum (OracleBundle.indexed (suffixSlot ∘ id)))
    scalarFamily where
  f x _ := 10 * (show Nat from x.1 ()) + (show Nat from x.2 ())
  impl _ := do
    let x : Nat ← liftM ((scalarFamily.sum
      (OracleBundle.indexed (suffixSlot ∘ id))).spec.query (.inl ⟨(), ()⟩))
    let y : Nat ← liftM ((scalarFamily.sum
      (OracleBundle.indexed (suffixSlot ∘ id))).spec.query (.inr ⟨(), ()⟩))
    pure (10 * x + y)
  law _ _ := rfl

/-- Substitute the derived scalar, and pass the suffix oracle through unchanged. -/
def substituted :
    OracleMap (source.sum suffix) scalarFamily :=
  withSuffix.comp (weightedQueries.par (OracleMap.reindex suffixSlot id))

/-- Source oracle `false` holds 3, oracle `true` holds 7, and the suffix holds 5. -/
def data : (source.sum suffix).Data :=
  (fun bit => if bit then 7 else 3, fun _ => 5)

-- Virtual V2, restated: the old-layer `substWithSuffix` becomes `OracleMap.comp` with
-- `OracleMap.par` of the derived map and the identity reindexing of the suffix; the map also
-- supplies the materialized data. Both the simulated query and the data give
-- `10 * (2 * 3 + 7) + 5 = 135`. Not weaker.
example :
    simulateQ ((source.sum suffix).answer data)
      (substituted.impl ⟨(), ()⟩) = (135 : Nat) := rfl

example : substituted.f data () = 135 := rfl

-- Virtual V3, restated: reindexing is the indexed bundle of the renamed slots, and the bundle's
-- `answer` reads its data.
/-- Reindexing oracle slots does not identify independently supplied data. -/
example :
    let repeated := OracleBundle.indexed (scalarSlot ∘ fun _ : Bool => ())
    let behavior := repeated.answer (fun bit => (if bit then 7 else 3 : Nat))
    (behavior ⟨false, ()⟩, behavior ⟨true, ()⟩) = ((3 : Nat), (7 : Nat)) := rfl

end Interaction.DerivedOraclesTests
