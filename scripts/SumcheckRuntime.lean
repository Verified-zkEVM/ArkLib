/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.Computable
import Mathlib.Algebra.Field.ZMod

/-!
# Compiled native Sumcheck checks

The sent polynomials are CompPoly coefficient arrays. These checks run ordinary native strategies
through the shared executor and observe continuation effects, rejection, and the retained original
oracle. The fixed challenge handler is a deterministic test fixture, not a randomness generator.
-/

namespace SumcheckRuntime

open OracleComp OracleSpec Interaction.Oracle
open Sumcheck.Interaction

abbrev F := ZMod 17

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- Construct a two-coefficient array, trimming a zero leading coefficient. -/
def affine (a b : F) : Sumcheck.Impl.Representation.Message F 1 :=
  ⟨CompPoly.CPolynomial.ofArray #[b, a], by
    have hsize := CompPoly.CPolynomial.Raw.Trim.size_le_size (#[b, a] : Array F)
    change (CompPoly.CPolynomial.ofArray #[b, a]).val.size ≤ 2 at hsize
    generalize h : (CompPoly.CPolynomial.ofArray #[b, a]).val.size = size at *
    cases size with
    | zero => simp [CompPoly.CPolynomial.degree, h]
    | succ size =>
        simp only [CompPoly.CPolynomial.degree, h]
        exact_mod_cast (show size ≤ 1 by omega)⟩

abbrev events : OracleSpec (Fin 4) := Fin 4 →ₒ F

def event (i : Fin 4) : OracleComp events F := liftM (events.query i)

/-- The second message depends on both private samples and the first public challenge. -/
def lastProver (a b r : F) : Prover.Strategy events (Computable.protocol F 1 1).tree
    (Computable.protocol F 1 1).roles (fun _ => Unit) := by
  refine pure ⟨affine (b + a) (a * r + 1), ?_⟩
  intro choice
  cases choice <;> exact do
    let _ ← event 3
    return ()

/-- Private memory is captured in the native continuation, with effects on either public branch. -/
def adaptive : Prover.Strategy events (Computable.protocol F 1 2).tree
    (Computable.protocol F 1 2).roles (fun _ => Unit) := by
  refine do
    let a ← event 0
    return ⟨affine a 1, ?_⟩
  intro choice
  cases choice with
  | none => exact do
      let _ ← event 2
      return ()
  | some r => exact do
      let b ← event 2
      return lastProver a b r

def original : (MultivariateRound.polynomialFamily F 2 1).Behavior := fun _ => (0 : F)

def initial : Sumcheck.Spec.StatementRound F 2 0 := ⟨1, Fin.elim0⟩

def record : QueryImpl events (StateM (List (Fin 4))) := fun i => do
  modify (fun seen => seen ++ [i])
  return ![7, 3, 5, 11] i

def run (domain : List F) :=
  Computable.execute F 2 1 events (event 1) domain 2 0 (by decide)
    (MultivariateRound.polynomialFamily F 2 1).spec.toPFunctor
    (VirtualOracle.id (MultivariateRound.polynomialFamily F 2 1))
    initial original adaptive

/-- Observe the scalar output and the original oracle separately from verifier acceptance. -/
def observe (domain : List F) : Option (F × F × F × F) × List (Fin 4) :=
  (simulateQ record ((fun result => result.map fun claim =>
    (claim.stmt.target, claim.stmt.challenges ⟨0, by decide⟩, claim.stmt.challenges ⟨1, by decide⟩,
      claim.oracles ⟨(), claim.stmt.challenges⟩)) <$> run domain)).run []

def check (label : String) (ok : Unit → Bool) : IO Unit := do
  unless ok () do throw (IO.userError s!"Sumcheck runtime check failed: {label}")
  IO.println s!"ok: {label}"

def runChecks : IO Unit := do
  check "Horner evaluation, including trimmed zero leading coefficient" fun _ =>
    Sumcheck.Impl.Representation.evaluate F 1 (affine 7 1) 3 == 5 &&
    Sumcheck.Impl.Representation.evaluate F 1 (affine 0 4) 9 == 4
  check "two rounds preserve private memory and effect order" fun _ =>
    observe [0] == (some (7, 3, 3, 0), [0, 1, 2, 1, 3])
  check "public abort runs the prover response and stops before the challenge" fun _ =>
    observe [] == (none, [0, 2])

end SumcheckRuntime

def main : IO Unit := SumcheckRuntime.runChecks
