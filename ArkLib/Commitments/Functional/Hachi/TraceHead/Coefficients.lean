/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Commitments.Functional.Hachi.EvalSplit
import Mathlib.LinearAlgebra.Pi

/-!
# Packing monomial coefficients along the final variables

The retained variables come first and the packed variables last. Indices use the existing
little-endian `Hachi.splitEquiv`; this is coefficient packing, not Boolean-table packing.
-/

open CompPoly

namespace ArkLib.Lattices.Hachi.TraceHead

variable {B A : Type*} [CommRing B] [CommRing A] [Algebra B A] {n t : ℕ}
variable (e : (Fin (2 ^ t) → B) ≃ₗ[B] A)

/-- Pack each vector of coefficients in the final `t` variables. -/
def packCoefficients (f : CMlPolynomial B (n + t)) : CMlPolynomial A n :=
  Vector.ofFn fun i => e (fun j => f.get (splitEquiv n t (j, i)))

/-- Decode each ring coefficient in its actual packing coordinates. -/
def unpackCoefficients (F : CMlPolynomial A n) : CMlPolynomial B (n + t) :=
  Vector.ofFn fun k => e.symm (F.get ((splitEquiv n t).symm k).2)
    ((splitEquiv n t).symm k).1

/-- Packing and then decoding recovers every monomial coefficient. -/
@[simp] theorem unpack_packCoefficients (f : CMlPolynomial B (n + t)) :
    unpackCoefficients e (packCoefficients e f) = f := by
  apply Vector.ext
  intro i hi
  simp [unpackCoefficients, packCoefficients]
  rfl

/-- Decoding and then packing recovers the actual ring polynomial. -/
@[simp] theorem pack_unpackCoefficients (F : CMlPolynomial A n) :
    packCoefficients e (unpackCoefficients e F) = F := by
  apply Vector.ext
  intro i hi
  simp [unpackCoefficients, packCoefficients]
  rfl

/-- A ring homomorphism transports the monomial basis coefficient by coefficient. -/
theorem monomialBasis_map {C : Type*} [CommSemiring C] (g : B →+* C)
    (x : Vector B n) (i : Fin (2 ^ n)) :
    (CMlPolynomial.monomialBasis (x.map g)).get i =
      g ((CMlPolynomial.monomialBasis x).get i) := by
  simp only [monomialBasis_get, map_prod, Vector.get_map]
  apply Finset.prod_congr rfl
  intro j _
  split <;> simp_all

/-- Coordinates of the packed polynomial evaluated at an embedded retained point. -/
theorem packCoefficients_eval (f : CMlPolynomial B (n + t)) (x : Vector B n) :
    (packCoefficients e f).eval (x.map (algebraMap B A)) =
      e (fun j => ∑ i : Fin (2 ^ n),
        (CMlPolynomial.monomialBasis x).get i * f.get (splitEquiv n t (j, i))) := by
  rw [CMlPolynomial.eval, Vector.dotProduct_eq_root_dotProduct]
  change (∑ i, (packCoefficients e f).get i *
    (CMlPolynomial.monomialBasis (x.map (algebraMap B A))).get i) = _
  have hfun : (fun j => ∑ i : Fin (2 ^ n),
        (CMlPolynomial.monomialBasis x).get i * f.get (splitEquiv n t (j, i))) =
      ∑ i : Fin (2 ^ n), (CMlPolynomial.monomialBasis x).get i •
        (fun j => f.get (splitEquiv n t (j, i))) := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, Algebra.smul_def, monomialBasis_map]
  simp only [packCoefficients, Vector.get_ofFn]
  exact mul_comm _ _

/-- The scalar polynomial evaluation is the inner product of the decoded ring evaluation
and the monomial basis at the packed suffix. -/
theorem unpackCoefficients_eval (F : CMlPolynomial A n) (x : Vector B n)
    (xp : Vector B t) :
    (unpackCoefficients e F).eval (x ++ xp) =
      ∑ j, e.symm (F.eval (x.map (algebraMap B A))) j *
        (CMlPolynomial.monomialBasis xp).get j := by
  have hcoords := congrArg e.symm (packCoefficients_eval e (unpackCoefficients e F) x)
  rw [pack_unpackCoefficients, LinearEquiv.symm_apply_apply] at hcoords
  rw [hcoords, ← evalSplit_eq_eval]
  simp only [evalSplit, splitForm, dot_eq_sum, matVecMul_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [toMatrix]
  ring

/-- Decoding a coefficient polynomial gives its actual monomial matrix contraction.
This identity concerns coefficients, before choosing any observation of the packed ring. -/
theorem unpackCoefficients_eval_components (F : CMlPolynomial A n) (x : Vector B n)
    (xp : Vector B t) :
    (unpackCoefficients e F).eval (x ++ xp) =
      ∑ j, (∑ i, (CMlPolynomial.monomialBasis x).get i * e.symm (F.get i) j) *
        (CMlPolynomial.monomialBasis xp).get j := by
  rw [← evalSplit_eq_eval]
  simp only [evalSplit, splitForm, dot_eq_sum, matVecMul_apply, Finset.mul_sum,
    Finset.sum_mul, toMatrix, unpackCoefficients, Vector.get_ofFn,
    Equiv.symm_apply_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

end ArkLib.Lattices.Hachi.TraceHead
