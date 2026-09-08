/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.MvPolynomial.Multilinear
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Splitting a multilinear Boolean table into coordinate blocks

The first block indexes the component family; each component retains the second block. The
construction and evaluation identity hold over commutative rings, including rings with zero
divisors. Exchanging the blocks is an explicit variable permutation.
-/

noncomputable section

namespace MvPolynomial

variable {R : Type*} [CommRing R] (k m : ℕ)

/-- Casts of appended Boolean blocks agree with appended casts. -/
theorem cast_append_bool (v : Fin k → Fin 2) (y : Fin m → Fin 2) :
    (fun i => ((Fin.append v y i : Fin 2) : R)) =
      Fin.append (v : Fin k → R) (y : Fin m → R) := by
  funext i
  exact Fin.addCases (fun j => by simp) (fun j => by simp) i

/-- The components obtained by fixing the first Boolean coordinate block. -/
def splitFirst (p : R⦃≤ 1⦄[X Fin (k + m)]) (v : Fin k → Fin 2) : R⦃≤ 1⦄[X Fin m] :=
  ⟨MLE (fun y => eval ((Fin.append v y) : Fin (k + m) → R) p.val), MLE_mem_restrictDegree _⟩

/-- Assemble the original Boolean table with the component index in its first block. -/
def joinFirst (ps : (Fin k → Fin 2) → R⦃≤ 1⦄[X Fin m]) : R⦃≤ 1⦄[X Fin (k + m)] :=
  ⟨MLE (fun z => eval ((fun i => z (Fin.natAdd k i)) : Fin m → R)
    (ps (fun i => z (Fin.castAdd m i))).val), MLE_mem_restrictDegree _⟩

@[simp]
theorem splitFirst_eval (p : R⦃≤ 1⦄[X Fin (k + m)]) (v : Fin k → Fin 2)
    (y : Fin m → Fin 2) :
    eval (y : Fin m → R) (splitFirst k m p v).val =
      eval ((Fin.append v y) : Fin (k + m) → R) p.val :=
  MLE_eval_zeroOne _ _

@[simp]
theorem splitFirst_joinFirst (ps : (Fin k → Fin 2) → R⦃≤ 1⦄[X Fin m]) :
    splitFirst k m (joinFirst k m ps) = ps := by
  funext v
  apply Subtype.ext
  apply eq_of_degreeOf_le_one_of_eval_zeroOne_eq _ _
    ((mem_restrictDegree_iff_degreeOf_le _ _).mp (splitFirst k m _ v).property)
    ((mem_restrictDegree_iff_degreeOf_le _ _).mp (ps v).property)
  intro y
  rw [splitFirst_eval]
  rw [← cast_append_bool]
  simp only [joinFirst, MLE_eval_zeroOne, Fin.append_left, Fin.append_right]

@[simp]
theorem joinFirst_splitFirst (p : R⦃≤ 1⦄[X Fin (k + m)]) :
    joinFirst k m (splitFirst k m p) = p := by
  apply Subtype.ext
  apply eq_of_degreeOf_le_one_of_eval_zeroOne_eq _ _
    ((mem_restrictDegree_iff_degreeOf_le _ _).mp (joinFirst k m _).property)
    ((mem_restrictDegree_iff_degreeOf_le _ _).mp p.property)
  intro z
  simp only [joinFirst, MLE_eval_zeroOne, splitFirst_eval]
  exact congrArg (fun r => eval r p.val)
    (Fin.append_castAdd_natAdd (f := fun i => ((z i : Fin 2) : R)))

/-- Splitting preserves the full Boolean table, with no field assumptions. -/
def splitFirstEquiv : R⦃≤ 1⦄[X Fin (k + m)] ≃ ((Fin k → Fin 2) → R⦃≤ 1⦄[X Fin m]) where
  toFun := splitFirst k m
  invFun := joinFirst k m
  left_inv := joinFirst_splitFirst k m
  right_inv := splitFirst_joinFirst k m

/-- Evaluation separates the packed prefix from the retained suffix. -/
theorem aeval_append_splitFirst {E : Type*} [CommRing E] [Algebra R E]
    (p : R⦃≤ 1⦄[X Fin (k + m)]) (rlo : Fin k → E) (rhi : Fin m → E) :
    aeval (Fin.append rlo rhi) p.val =
      ∑ v : Fin k → Fin 2, eqTilde (v : Fin k → E) rlo *
        aeval rhi (splitFirst k m p v).val := by
  rw [aeval_multilinear_eq_sum_eqTilde p.property]
  rw [← (Fin.appendEquiv k m).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.appendEquiv_apply]
  simp_rw [aeval_multilinear_eq_sum_eqTilde (splitFirst k m p _).property,
    splitFirst_eval, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun y _ => ?_
  rw [cast_append_bool (R := E), eqTilde_append, cast_append_bool (R := R)]
  exact mul_assoc _ _ _

/-- The components obtained by fixing the final Boolean block. -/
def splitLast (p : R⦃≤ 1⦄[X Fin (m + k)]) (v : Fin k → Fin 2) : R⦃≤ 1⦄[X Fin m] :=
  ⟨MLE (fun y => eval ((Fin.append y v) : Fin (m + k) → R) p.val), MLE_mem_restrictDegree _⟩

/-- Assemble the original Boolean table with the component index in its final block. -/
def joinLast (ps : (Fin k → Fin 2) → R⦃≤ 1⦄[X Fin m]) : R⦃≤ 1⦄[X Fin (m + k)] :=
  ⟨MLE (fun z => eval ((fun i => z (Fin.castAdd k i)) : Fin m → R)
    (ps (fun i => z (Fin.natAdd m i))).val), MLE_mem_restrictDegree _⟩

@[simp]
theorem splitLast_eval (p : R⦃≤ 1⦄[X Fin (m + k)]) (v : Fin k → Fin 2)
    (y : Fin m → Fin 2) :
    eval (y : Fin m → R) (splitLast k m p v).val =
      eval ((Fin.append y v) : Fin (m + k) → R) p.val :=
  MLE_eval_zeroOne _ _

@[simp]
theorem splitLast_joinLast (ps : (Fin k → Fin 2) → R⦃≤ 1⦄[X Fin m]) :
    splitLast k m (joinLast k m ps) = ps := by
  funext v
  apply Subtype.ext
  apply eq_of_degreeOf_le_one_of_eval_zeroOne_eq _ _
    ((mem_restrictDegree_iff_degreeOf_le _ _).mp (splitLast k m _ v).property)
    ((mem_restrictDegree_iff_degreeOf_le _ _).mp (ps v).property)
  intro y
  rw [splitLast_eval]
  rw [← cast_append_bool]
  simp only [joinLast, MLE_eval_zeroOne, Fin.append_left, Fin.append_right]

@[simp]
theorem joinLast_splitLast (p : R⦃≤ 1⦄[X Fin (m + k)]) :
    joinLast k m (splitLast k m p) = p := by
  apply Subtype.ext
  apply eq_of_degreeOf_le_one_of_eval_zeroOne_eq _ _
    ((mem_restrictDegree_iff_degreeOf_le _ _).mp (joinLast k m _).property)
    ((mem_restrictDegree_iff_degreeOf_le _ _).mp p.property)
  intro z
  simp only [joinLast, MLE_eval_zeroOne, splitLast_eval]
  exact congrArg (fun r => eval r p.val)
    (Fin.append_castAdd_natAdd (f := fun i => ((z i : Fin 2) : R)))

/-- Splitting the final Boolean block preserves the original polynomial. -/
def splitLastEquiv : R⦃≤ 1⦄[X Fin (m + k)] ≃ ((Fin k → Fin 2) → R⦃≤ 1⦄[X Fin m]) where
  toFun := splitLast k m
  invFun := joinLast k m
  left_inv := joinLast_splitLast k m
  right_inv := splitLast_joinLast k m

/-- Evaluation separates the retained prefix from the packed suffix. -/
theorem aeval_append_splitLast {E : Type*} [CommRing E] [Algebra R E]
    (p : R⦃≤ 1⦄[X Fin (m + k)]) (rhi : Fin m → E) (rlo : Fin k → E) :
    aeval (Fin.append rhi rlo) p.val =
      ∑ v : Fin k → Fin 2, eqTilde (v : Fin k → E) rlo *
        aeval rhi (splitLast k m p v).val := by
  rw [aeval_multilinear_eq_sum_eqTilde p.property]
  rw [← (Fin.appendEquiv m k).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.appendEquiv_apply]
  rw [Finset.sum_comm]
  simp_rw [aeval_multilinear_eq_sum_eqTilde (splitLast k m p _).property,
    splitLast_eval, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun y _ => ?_
  rw [cast_append_bool (R := E), eqTilde_append, cast_append_bool (R := R)]
  ring

end MvPolynomial

end
