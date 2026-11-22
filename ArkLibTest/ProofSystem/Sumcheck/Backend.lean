/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Message.Quadratic
import ArkLib.ProofSystem.Sumcheck.Prover.Enumeration
import ArkLib.ProofSystem.Sumcheck.Source
import Mathlib.Algebra.Field.ZMod

/-!
# Neutral Sumcheck backend acceptance tests

The operations below execute on coefficient arrays and compressed pairs. The examples connect
the proof-only models to the legacy sum check and to the Boolean quadratic sum law.
-/

namespace Sumcheck.BackendTest

open Polynomial

abbrev F := ZMod 7

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The uncompressed message `1 + 2X`. -/
def affine : Impl.Representation.Message F 1 :=
  ⟨CompPoly.CPolynomial.ofArray (#[1, 2] : Array F), by
    have hsize := CompPoly.CPolynomial.Raw.Trim.size_le_size (#[1, 2] : Array F)
    change (CompPoly.CPolynomial.ofArray (#[1, 2] : Array F)).val.size ≤ 2 at hsize
    generalize h : (CompPoly.CPolynomial.ofArray (#[1, 2] : Array F)).val.size = size at *
    cases size with
    | zero => simp [CompPoly.CPolynomial.degree, h]
    | succ size =>
        simp only [CompPoly.CPolynomial.degree, h]
        exact_mod_cast (show size ≤ 1 by omega)⟩

/-- info: (2, true, false, true) -/
#guard_msgs in
#eval let ops := compOps (d := 1) ({0, 1} : Finset F)
  (ops.evaluate 4 affine 4, ops.accept 4 affine, ops.accept 5 affine,
    (compOps (d := 1) (∅ : Finset F)).accept 0 affine)

-- With claim 4 and coefficients (1, 2), the missing linear coefficient is zero.
-- Changing the claim to 5 changes that coefficient to one.
/-- info: (5, true, 1, true) -/
#guard_msgs in
#eval let ops := quadraticOps (R := F)
  (ops.evaluate 4 (1, 2) 3, ops.accept 4 (1, 2),
    ops.evaluate 5 (1, 2) 3, ops.accept 5 (1, 2))

/-- The polynomial `x + 2y + 3`, constructed without a Mathlib interpretation. -/
def inputPoly : CPoly.CMvPolynomial 2 F :=
  CPoly.CMvPolynomial.X 0 + CPoly.CMvPolynomial.C 2 * CPoly.CMvPolynomial.X 1 +
    CPoly.CMvPolynomial.C 3

theorem inputPoly_degree : ∀ j, inputPoly.degreeOf j ≤ 1 := by
  intro j
  rw [congrFun (CPoly.degreeOf_equiv (S := F) (p := inputPoly)) j]
  change (CPoly.polyRingEquiv (n := 2) (R := F) inputPoly).degreeOf j ≤ 1
  simp only [inputPoly, map_add, map_mul, CPoly.coe_polyRingEquiv,
    CPoly.CMvPolynomial.fromCMvPolynomial_X, CPoly.CMvPolynomial.fromCMvPolynomial_C]
  have hx (i : Fin 2) : (MvPolynomial.X i : MvPolynomial (Fin 2) F).degreeOf j ≤ 1 := by
    simp only [MvPolynomial.degreeOf_X]
    split <;> omega
  refine (MvPolynomial.degreeOf_add_le j _ _).trans (max_le ?_ ?_)
  · exact (MvPolynomial.degreeOf_add_le j _ _).trans
      (max_le (hx 0) ((MvPolynomial.degreeOf_C_mul_le _ j (2 : F)).trans (hx 1)))
  · simp

def booleanDomain : Fin 2 ↪ F := ⟨fun i => (i.val : F), by decide⟩

def initial : EnumerationState F 2 1 2 :=
  ⟨0, rfl, inputPoly, inputPoly_degree, Fin.elim0⟩

/-- Two messages and both folds: `2x + 1`, then `2y` after the challenge `x = 4`. -/
def enumerationObservations : F × Bool × F × Bool × F := Id.run do
  let prover := enumerationOps booleanDomain
  let ops := compOps (d := 1) (Finset.univ.map booleanDomain)
  let first := prover.message initial
  let next := prover.fold initial 4
  let second := prover.message next
  let last := prover.fold next 3
  return (ops.evaluate 4 first 4, ops.accept 4 first,
    ops.evaluate 2 second 3, ops.accept 2 second,
    last.poly.eval (last.challenges ∘ Fin.cast (by have := last.finish; omega)))

/-- info: (2, true, 6, true, 6) -/
#guard_msgs in
#eval enumerationObservations

-- This is exactly the sum condition guarded by `Spec.SingleRound.verifier`:
-- the domain is `univ.map D`, and the received bounded polynomial is evaluated on it.
example {R : Type} [CommRing R] [DecidableEq R] {d m : ℕ}
    (D : Fin m ↪ R) (c : R) (p : R⦃≤ d⦄[X]) :
    (plainOps (Finset.univ.map D) (fun q : R⦃≤ d⦄[X] => q.val.eval)).accept c p = true ↔
      ∑ x ∈ Finset.univ.map D, p.val.eval x = c :=
  (identityModel (d := d) (Finset.univ.map D)).accept_iff c p

-- No field structure or assumption on the characteristic is required.
example {R : Type} [CommRing R] [DecidableEq R] [Nontrivial R] (c : R) (m : R × R) :
    (quadraticOps (R := R)).accept c m = true ↔
      ∑ x ∈ ({0, 1} : Finset R), (quadratic c m).val.eval x = c :=
  (quadraticModel (R := R)).accept_iff c m

example {R : Type} [CommRing R] [DecidableEq R] [Nontrivial R] (c : R) (m : R × R) :
    (quadratic c m).val.eval 0 + (quadratic c m).val.eval 1 = c := by
  simpa only [quadraticModel, Finset.sum_pair (zero_ne_one : (0 : R) ≠ 1)] using
    ((quadraticModel (R := R)).accept_iff c m).mp rfl

/-- info: 'Sumcheck.enumerationModel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms enumerationModel

/--
info: 'Sumcheck.enumeration_honest_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms enumeration_honest_step

end Sumcheck.BackendTest
