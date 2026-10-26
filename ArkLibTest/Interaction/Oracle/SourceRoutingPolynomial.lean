/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.Interaction.Oracle.SourceRouting
import ArkLib.ProofSystem.Sumcheck.Interaction.MultivariateRound
import Mathlib.Data.ZMod.Basic
import Lean.Compiler.IR

/-!
# Executable composition through a mathematical polynomial interface

The polynomial family describes the exported interface; no polynomial realization is constructed.
An actual terminal query of the composed verifier reduces to the original source query. External
caller IR gates and a concrete ordered-query observation exercise the descriptor erasure chain.
-/

namespace Interaction.Oracle.SourceRoutingPolynomialTest

open OracleComp OracleSpec
open Sumcheck.Interaction

variable (R : Type) [CommSemiring R] (n deg : ℕ)
variable {ι : Type} (ambient : OracleSpec ι)

local notation "family" => MultivariateRound.polynomialFamily R n deg

abbrev inputSpec : OracleSpec (Fin n → R) := (Fin n → R) →ₒ R

/-- The exported polynomial's answer is supplied by the retained input source. -/
def view : VirtualOracle (ofPFunctor (inputSpec R n).toPFunctor) family :=
  ⟨fun query => liftM ((inputSpec R n).query query.2)⟩

/-- A value-returning prefix exports a query program without executing it. -/
def first : Verifier.Fragment ambient .done PUnit.unit PUnit.unit
    (inputSpec R n).toPFunctor (fun _ =>
      OpenClaim (ofPFunctor (inputSpec R n).toPFunctor) Unit family) :=
  ⟨(), view R n deg⟩

/-- A suffix retains exactly the exported evaluation interface. -/
def second (_ : TypeTree.done.BranchPath) (_ : Unit) :
    Verifier.Strategy ambient .done PUnit.unit PUnit.unit (family).spec.toPFunctor
      (fun _ => Option (OpenClaim (ofPFunctor (family).spec.toPFunctor) Unit family)) :=
  pure (some ⟨(), VirtualOracle.id family⟩)

/-- Mathematical realization descriptors stay outside the executable composition. -/
def composed : Verifier.Strategy ambient .done PUnit.unit PUnit.unit
    (inputSpec R n).toPFunctor (fun _ =>
      Option (OpenClaim (ofPFunctor (inputSpec R n).toPFunctor) Unit family)) :=
  Verifier.appendExported ambient .done (fun _ => .done)
    PUnit.unit (fun _ => PUnit.unit) PUnit.unit (fun _ => PUnit.unit)
    (inputSpec R n).toPFunctor (fun _ => Unit)
    (fun _ => Sumcheck.Spec.OracleStatement R n deg) (fun _ => family)
    (fun _ => Unit) (fun _ => Sumcheck.Spec.OracleStatement R n deg) (fun _ => family)
    (first R n deg ambient) (second R n deg ambient)

/-- Execute the composed verifier's terminal action, then query its actual returned view. -/
def queryComposed (point : Fin n → R) :
    OracleComp (ambient + ofPFunctor (inputSpec R n).toPFunctor) R := do
  let result ← composed R n deg ambient
  match result with
  | none => return 0
  | some claim => liftM (claim.oracles.query ⟨(), point⟩)

/-- The composed terminal query is the same source program as the original input query. -/
theorem queryComposed_eq (point : Fin n → R) :
    queryComposed R n deg ambient point =
      liftM ((inputSpec R n).query point) := by
  rfl

abbrev F := ZMod 17
abbrev emptyAmbient : OracleSpec Empty := Empty →ₒ F

/-- Answer and record the source point requested by the composed verifier. -/
def record : QueryImpl (emptyAmbient + ofPFunctor (inputSpec F 1).toPFunctor)
    (StateM (List F)) := fun query =>
  match query with
  | .inl impossible => nomatch impossible
  | .inr point => do
    let x : F := point 0
    modify (· ++ [x])
    return (2 * x + 1 : F)

/-- The observation comes from interpreting the actual composed terminal source program. -/
def observed : F × List F :=
  (simulateQ record (queryComposed F 1 1 emptyAmbient (fun _ => 3))).run []

example : observed = (7, [3]) := by
  unfold observed
  rw [queryComposed_eq]
  rfl

#eval observed

open Lean Elab Command

run_cmd do
  for name in #[``view, ``first, ``second, ``composed, ``queryComposed, ``observed] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "expected compiler IR for `{name}`"

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← collectAxioms ``queryComposed_eq
  unless axioms.all allowed.contains do
    throwError "queryComposed_eq depends on unexpected axioms: {axioms}"

end Interaction.Oracle.SourceRoutingPolynomialTest
