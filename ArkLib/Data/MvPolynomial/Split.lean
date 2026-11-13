/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.Data.Fin.Basic
public import ArkLib.Data.MvPolynomial.Multilinear

/-!
# Splitting a multilinear Boolean table into coordinate blocks

The first block indexes the component family; each component retains the second block. The
construction and evaluation identity hold over commutative rings, including rings with zero
divisors. `splitLast` is the same construction with the component index in the last block.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

variable {R : Type*} [CommRing R] (k m : ℕ)

/-- Casting an appended Boolean tuple casts each block. -/
private theorem cast_append (v : Fin k → Fin 2) (y : Fin m → Fin 2) :
    (fun i => ((Fin.append v y i : Fin 2) : R)) =
      Fin.append (v : Fin k → R) (y : Fin m → R) :=
  (Fin.append_comp fun b : Fin 2 => (b : R)).symm

/-- The components obtained by fixing the first Boolean coordinate block. -/
def splitFirst (p : R⦃≤ 1⦄[X Fin (k + m)]) (v : Fin k → Fin 2) : R⦃≤ 1⦄[X Fin m] :=
  ⟨MLE (fun y => eval ((Fin.append v y) : Fin (k + m) → R) p.val), MLE_mem_restrictDegree _⟩

/-- Assemble the original Boolean table with the component index in its first block. -/
def joinFirst (ps : (Fin k → Fin 2) → R⦃≤ 1⦄[X Fin m]) : R⦃≤ 1⦄[X Fin (k + m)] :=
  ⟨MLE (fun z => eval ((fun i => z (Fin.natAdd k i)) : Fin m → R)
    (ps (fun i => z (Fin.castAdd m i))).val), MLE_mem_restrictDegree _⟩

/-- Each component evaluates the original polynomial with the first block fixed. -/
@[simp]
theorem splitFirst_eval (p : R⦃≤ 1⦄[X Fin (k + m)]) (v : Fin k → Fin 2)
    (y : Fin m → Fin 2) :
    eval (y : Fin m → R) (splitFirst k m p v).val =
      eval ((Fin.append v y) : Fin (k + m) → R) p.val :=
  MLE_eval_zeroOne _ _

/-- Splitting an assembled table recovers its components. -/
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
  rw [← cast_append]
  simp only [joinFirst, MLE_eval_zeroOne, Fin.append_left, Fin.append_right]

/-- Assembling the components of a polynomial recovers the polynomial. -/
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
  rw [cast_append (R := E), eqTilde_append, cast_append (R := R)]
  exact mul_assoc _ _ _

/-- The components obtained by fixing the final Boolean block. -/
def splitLast (p : R⦃≤ 1⦄[X Fin (m + k)]) (v : Fin k → Fin 2) : R⦃≤ 1⦄[X Fin m] :=
  ⟨MLE (fun y => eval ((Fin.append y v) : Fin (m + k) → R) p.val), MLE_mem_restrictDegree _⟩

/-- Assemble the original Boolean table with the component index in its final block. -/
def joinLast (ps : (Fin k → Fin 2) → R⦃≤ 1⦄[X Fin m]) : R⦃≤ 1⦄[X Fin (m + k)] :=
  ⟨MLE (fun z => eval ((fun i => z (Fin.castAdd k i)) : Fin m → R)
    (ps (fun i => z (Fin.natAdd m i))).val), MLE_mem_restrictDegree _⟩

/-- Each component evaluates the original polynomial with the last block fixed. -/
@[simp]
theorem splitLast_eval (p : R⦃≤ 1⦄[X Fin (m + k)]) (v : Fin k → Fin 2)
    (y : Fin m → Fin 2) :
    eval (y : Fin m → R) (splitLast k m p v).val =
      eval ((Fin.append y v) : Fin (m + k) → R) p.val :=
  MLE_eval_zeroOne _ _

/-- Splitting an assembled table recovers its components. -/
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
  rw [← cast_append]
  simp only [joinLast, MLE_eval_zeroOne, Fin.append_left, Fin.append_right]

/-- Assembling the components of a polynomial recovers the polynomial. -/
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
  rw [cast_append (R := E), eqTilde_append, cast_append (R := R)]
  ring

private theorem finFunctionFinEquiv_ones (n : ℕ) :
    (finFunctionFinEquiv (fun _ : Fin n => (1 : Fin 2))).val = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [finFunctionFinEquiv_apply, Fin.sum_univ_castSucc]
    simp only [Fin.val_one, one_mul, Fin.val_castSucc, Fin.val_last]
    have hs : (∑ i : Fin n, 2 ^ i.val) = 2 ^ n - 1 := by
      simpa [finFunctionFinEquiv_apply] using ih
    rw [hs, pow_succ]
    have := Nat.one_le_pow n 2 (by decide)
    omega

private theorem finFunctionFinEquiv_append_ones (u : Fin k → Fin 2) :
    (finFunctionFinEquiv (Fin.append u (fun _ : Fin m => (1 : Fin 2)))).val =
      2 ^ (k + m) - 2 ^ k + (finFunctionFinEquiv u).val := by
  rw [finFunctionFinEquiv_apply, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Fin.val_one, one_mul,
    Fin.val_castAdd, Fin.val_natAdd, pow_add]
  simp_rw [← Finset.mul_sum]
  have hs : (∑ i : Fin m, 2 ^ i.val) = 2 ^ m - 1 := by
    simpa [finFunctionFinEquiv_apply] using finFunctionFinEquiv_ones m
  rw [hs]
  change (finFunctionFinEquiv u).val + 2 ^ k * (2 ^ m - 1) = _
  have he : 2 ^ k * (2 ^ m - 1) = 2 ^ k * 2 ^ m - 2 ^ k := by
    rw [Nat.mul_sub_left_distrib, mul_one]
  rw [he]
  omega

/-- A final block of `2^k` consecutive entries occupies the all-one high-coordinate block.
Its multilinear extension uses the low coordinates and the product of the high coordinates. -/
theorem MLE'_append_suffix_eval (x : Fin (2 ^ (k + m) - 2 ^ k) → R)
    (w : Fin (2 ^ k) → R) (r : Fin (k + m) → R) :
    eval r (MLE' (Fin.append x w ∘ Fin.cast (Nat.sub_add_cancel
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.le_add_right k m))).symm)) =
      (∑ j : Fin (2 ^ (k + m) - 2 ^ k),
        eqTilde (finFunctionFinEquiv.symm (Fin.castLE (Nat.sub_le _ _) j) :
          Fin (k + m) → R) r * x j) +
      (∏ i : Fin m, r (Fin.natAdd k i)) *
        eval (fun i : Fin k => r (Fin.castAdd m i)) (MLE' w) := by
  have hpow : 2 ^ k ≤ 2 ^ (k + m) :=
    Nat.pow_le_pow_right (by decide) (Nat.le_add_right k m)
  rw [MLE'_eval, ← (finCongr (Nat.sub_add_cancel hpow)).sum_comp, Fin.sum_univ_add]
  simp only [Function.comp_apply, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self,
    Fin.append_left, Fin.append_right]
  congr 1
  have hbits (j : Fin (2 ^ k)) :
      finFunctionFinEquiv.symm
        (Fin.cast (Nat.sub_add_cancel hpow) (Fin.natAdd (2 ^ (k + m) - 2 ^ k) j)) =
        Fin.append (finFunctionFinEquiv.symm j) (fun _ : Fin m => (1 : Fin 2)) := by
    apply finFunctionFinEquiv.injective
    apply Fin.ext
    simp only [Equiv.apply_symm_apply, Fin.val_cast, Fin.val_natAdd]
    rw [finFunctionFinEquiv_append_ones, Equiv.apply_symm_apply]
  simp_rw [hbits]
  rw [MLE'_eval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hcast : (fun i => ((Fin.append (finFunctionFinEquiv.symm j)
      (fun _ : Fin m => (1 : Fin 2)) i : Fin 2) : R)) =
      Fin.append (finFunctionFinEquiv.symm j : Fin k → R) (fun _ : Fin m => (1 : R)) := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp
  rw [hcast, ← Fin.append_castAdd_natAdd (f := r), eqTilde_append]
  simp only [eqTilde_eq_prod, one_mul, sub_self, zero_mul, add_zero,
    Fin.append_left, Fin.append_right]
  ring

end MvPolynomial

end
