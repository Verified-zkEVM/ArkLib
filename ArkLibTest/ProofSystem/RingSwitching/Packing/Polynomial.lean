/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.Polynomial
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.ZMod.Basic

/-!
# Packing one-variable multilinears over a ring with zero divisors

Two `ZMod 6` components are packed into `(ZMod 6)²`, while openings live in the independent
rank-three algebra `(ZMod 6)³`. Packed and unpacked coefficients and evaluations are compared
with hand-computed values; at the packed point `(2, 3)` the zero divisors annihilate both slopes.
-/

noncomputable section

namespace RingSwitching.Packing.Tests

open MvPolynomial Module

/-- Packing rank two and opening rank three over the ring `ZMod 6`. -/
abbrev productData : PackingData (ZMod 6) where
  P := Fin 2 → ZMod 6
  E := Fin 3 → ZMod 6
  ιP := Fin 2
  ιE := Fin 3
  packBasis := Pi.basisFun _ _
  openBasis := Pi.basisFun _ _

/-- The affine one-variable multilinear `a + b * X₀`. -/
def affine {R : Type} [CommRing R] (a b : R) : R⦃≤ 1⦄[X Fin 1] :=
  ⟨monomial 0 a + monomial (Finsupp.single 0 1) b, by
    rw [mem_restrictDegree]
    intro s hs i
    rcases Finset.mem_union.mp (support_add hs) with h | h <;>
      rw [Finset.mem_singleton.mp (support_monomial_subset h)] <;> fin_cases i <;> simp⟩

/-- Coefficients of an affine multilinear. -/
theorem affine_coeff {R : Type} [CommRing R] (a b : R) (d : Fin 1 →₀ ℕ) :
    (affine a b).val.coeff d =
      (if (0 : Fin 1 →₀ ℕ) = d then a else 0) + if Finsupp.single 0 1 = d then b else 0 := by
  simp [affine, coeff_monomial]

/-- Evaluation of an affine multilinear. -/
theorem affine_eval {R : Type} [CommRing R] (a b : R) (x : Fin 1 → R) :
    (affine a b).val.eval x = a + b * x 0 := by
  simp [affine, eval_monomial]

/-- Algebra evaluation of an affine multilinear. -/
theorem affine_aeval {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (a b : R)
    (x : Fin 1 → A) :
    aeval x (affine a b).val = algebraMap R A a + algebraMap R A b * x 0 := by
  simp [affine, aeval_monomial]

/-- Two base components whose linear coefficients are the zero divisors `3` and `2`. -/
def components : Fin 2 → (ZMod 6)⦃≤ 1⦄[X Fin 1] := ![affine 1 3, affine 4 2]

/-- The hand-packed polynomial `(1, 4) + (3, 2) * X₀` over `(ZMod 6)²`. -/
def packed : productData.P⦃≤ 1⦄[X Fin 1] := affine ![1, 4] ![3, 2]

/-- The constant and linear exponents of one variable are distinct. -/
theorem zero_ne_single : (0 : Fin 1 →₀ ℕ) ≠ Finsupp.single 0 1 :=
  (Finsupp.single_ne_zero.mpr one_ne_zero).symm

/-- The linear coefficient of the packed polynomial collects the component slopes. -/
theorem packedMLE_coeff_linear :
    (productData.packedMLE components).val.coeff (Finsupp.single 0 1) = ![3, 2] := by
  rw [productData.packedMLE_val, coeff_sum]
  funext j
  fin_cases j <;> simp [components, coeff_map, affine_coeff, zero_ne_single, Pi.single_apply]

/-- The constant coefficient of the packed polynomial collects the component intercepts. -/
theorem packedMLE_coeff_const :
    (productData.packedMLE components).val.coeff 0 = ![1, 4] := by
  rw [productData.packedMLE_val, coeff_sum]
  funext j
  fin_cases j <;> simp [components, coeff_map, affine_coeff, zero_ne_single.symm, Pi.single_apply]

/-- At the zero-divisor point `(2, 3)` both slopes are annihilated: `3 * 2 = 2 * 3 = 0`. -/
theorem packedMLE_eval_zeroDivisor :
    (productData.packedMLE components).val.eval (fun _ => ![2, 3]) = ![1, 4] := by
  rw [productData.packedMLE_eval]
  funext j
  fin_cases j <;> simp +decide [components, affine_aeval, Fin.sum_univ_two]

/-- At the unit point the packed polynomial is not its constant term. -/
theorem packedMLE_eval_one :
    (productData.packedMLE components).val.eval (fun _ => 1) = ![4, 0] := by
  rw [productData.packedMLE_eval]
  funext j
  fin_cases j <;> simp +decide [components, affine_aeval, Fin.sum_univ_two]

/-- Unpacking the hand-packed polynomial reads the second slope `2`. -/
theorem unpack_coeff_linear :
    (productData.unpack packed 1).val.coeff (Finsupp.single 0 1) = 2 := by
  rw [productData.unpack_coeff]
  simp [packed, affine_coeff, zero_ne_single]

/-- Packing the two components gives the hand-packed polynomial, coefficient by coefficient. -/
theorem packedMLE_components : productData.packedMLE components = packed := by
  refine Subtype.ext (MvPolynomial.ext _ _ fun d => ?_)
  rw [productData.packedMLE_val, coeff_sum]
  funext j
  fin_cases j <;> simp [components, packed, coeff_map, affine_coeff, Pi.single_apply] <;>
    split_ifs <;> rfl

/-- Unpacking the hand-packed polynomial gives the two components, coefficient by coefficient. -/
theorem unpack_packed : productData.unpack packed = components := by
  funext i
  refine Subtype.ext (MvPolynomial.ext _ _ fun d => ?_)
  rw [productData.unpack_coeff]
  fin_cases i <;> simp [components, packed, affine_coeff] <;> split_ifs <;> rfl

/-- The first unpacked component evaluates as `1 + 3 * 5 = 4` in `ZMod 6`. -/
theorem unpack_eval :
    (productData.unpack packed 0).val.eval (fun _ => 5) = 4 := by
  rw [unpack_packed]
  change (affine 1 3).val.eval _ = _
  rw [affine_eval]
  decide

end RingSwitching.Packing.Tests

end
