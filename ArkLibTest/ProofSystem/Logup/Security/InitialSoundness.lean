/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Logup.Security.InitialSoundness
import Mathlib.Algebra.Field.ZMod
import Lean.Compiler.IR

/-! # Initial-relation analysis against actual retained sources -/

open Interaction.Oracle OracleComp OracleSpec CompPoly
open Logup.Interaction
open scoped BigOperators ProbabilityTheory ENNReal

namespace LogupInitialTest

abbrev F := ZMod 17
instance : Fact (Nat.Prime 17) := ⟨by decide⟩

namespace ZeroRows

def cfg : Config 0 1 1 := (Config.create? 0 1 1).get (by decide)
def data (i : Fin 2 × Fin 1) : CMlPolynomialEval F 0 := if i.1 = 0 then #v[0] else #v[1]
def helpers : Vector (CMlPolynomialEval F 0) 1 := #v[#v[0]]
abbrev access := (inputFamily (RingHom.id F) 0 1).spec.toPFunctor
def impl : QueryImpl (ofPFunctor access) Id :=
  (inputFamily (RingHom.id F) 0 1).behaviorOfRealizations data
def view : VirtualOracle (ofPFunctor access) (inputFamily (RingHom.id F) 0 1) :=
  VirtualOracle.id _
theorem realizes : view.eval impl =
    (inputFamily (RingHom.id F) 0 1).behaviorOfRealizations data := VirtualOracle.eval_id impl

/-- The fixed polynomial is one, so even the alpha0 denominator pole is not a bad root. -/
theorem numerator_one : clearedBalancePolynomial (RingHom.id F) data = 1 := by
  have hocc : ((Finset.univ : Finset (Fin 0 → Fin 2)).product
      (Finset.univ : Finset (Fin 1))) = {(Fin.elim0, 0)} := by decide
  rw [clearedBalancePolynomial, hocc, PartialFractions.clearedNumerator]
  simp [data]

theorem fixed_alpha_bound :
    Pr{let joint ← $ᵗ ((Fin 0 → F) × (Fin ((1 : Nat) ⌈/⌉ 1) → F))}[
      Sumcheck.Interaction.MultivariateRound.closedRelation F 0 3 (boolEmbedding F) 0
        ⟨⟨0, Fin.elim0⟩,
          (qView (RingHom.id F) 0 1 ((1 : Nat) ⌈/⌉ 1)
            cfg.groups 0 joint.1 joint.2 1 access view).eval
            (Access.extendImpl access (helperInterface (E := F) 0 ((1 : Nat) ⌈/⌉ 1))
              impl helpers)⟩] ≤
      (17 : ℝ≥0∞)⁻¹ := by
  simpa only [Nat.reduceAdd, Nat.cast_zero, ENNReal.zero_div, zero_add,
    ZMod.card, Nat.cast_ofNat] using
    prob_initial_relation_le cfg (RingHom.id F) data 0 (by simp [numerator_one])
      access view impl realizes helpers

example : (17 : ℝ≥0∞)⁻¹ < 1 := by norm_num

def queried (lambda : F) : F :=
  simulateQ (Access.extendImpl access (helperInterface (E := F) 0 1) impl helpers)
    (queryQ (RingHom.id F) 0 1 1 cfg.groups 0 Fin.elim0 (fun _ ↦ lambda)
      access view Fin.elim0)

end ZeroRows

namespace ResidualTable

def cfg : Config 1 1 1 := (Config.create? 1 1 1).get (by decide)
def data (i : Fin 2 × Fin 1) : CMlPolynomialEval F 1 :=
  if i.1 = 0 then #v[0,1] else #v[1,1]
def helpers : Vector (CMlPolynomialEval F 1) 1 := #v[#v[0,1]]
abbrev access := (inputFamily (RingHom.id F) 1 1).spec.toPFunctor
def impl : QueryImpl (ofPFunctor access) Id :=
  (inputFamily (RingHom.id F) 1 1).behaviorOfRealizations data
def view : VirtualOracle (ofPFunctor access) (inputFamily (RingHom.id F) 1 1) :=
  VirtualOracle.id _

def queried (x : F) : F :=
  simulateQ (Access.extendImpl access (helperInterface (E := F) 1 1) impl helpers)
    (queryQ (RingHom.id F) 1 1 1 cfg.groups 0 (fun _ ↦ 2) (fun _ ↦ 1)
      access view (fun _ ↦ x))

-- The raw residual is -X²-1; its table MLE is -X-1. They differ at the field point2.
def rawResidual (x : F) : F :=
  Logup.groupResidual cfg.groups[0] 0 (fun _ ↦ x) (fun _ ↦ 1) x
def interpolatedResidual (x : F) : F :=
  (1-x) * residualTable cfg (RingHom.id F) 0 data helpers 0 (fun _ ↦ 0) +
    x * residualTable cfg (RingHom.id F) 0 data helpers 0 (fun _ ↦ 1)

example : rawResidual 2 = 12 := by decide
example : interpolatedResidual 2 = 14 := by decide
example : rawResidual 2 ≠ interpolatedResidual 2 := by decide

end ResidualTable

open Lean Elab Command

run_cmd do
  let roots := (List.finRange 17).filter fun i ↦ ZeroRows.queried (i.val : F) == 0
  unless roots.length == 1 do throwError "pole-safe initial event has wrong root count"
  unless (List.finRange 17).all (fun i ↦ ZeroRows.queried (i.val : F) == -(i.val : F)) do
    throwError "actual zero-row Q is not minus lambda"
  unless helperTotal ResidualTable.helpers == 1 do throwError "wrong helper total"
  unless ResidualTable.queried 0 + ResidualTable.queried 1 == 15 do
    throwError "actual Boolean Q sum changed"
  unless helperTotal ResidualTable.helpers + ResidualTable.interpolatedResidual 2 == 15 do
    throwError "residual TABLE interpolation fails actual Boolean Q sum"
  unless helperTotal ResidualTable.helpers + ResidualTable.rawResidual 2 == 13 do
    throwError "raw residual counterexample unexpectedly agrees with table MLE"

run_cmd do
  for name in #[``helperTotal, ``residualTable, ``ZeroRows.queried,
      ``ResidualTable.queried, ``ResidualTable.interpolatedResidual] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing initial-analysis caller IR: {name}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``clearedBalancePolynomial_eq_zero_iff, ``natDegree_clearedBalancePolynomial_le,
      ``total_or_residual_ne_zero, ``sum_qPolynomial, ``initial_relation_iff,
      ``prob_initial_relation_le, ``ZeroRows.realizes, ``ZeroRows.numerator_one,
      ``ZeroRows.fixed_alpha_bound] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected initial-analysis axiom in `{name}`"

end LogupInitialTest
