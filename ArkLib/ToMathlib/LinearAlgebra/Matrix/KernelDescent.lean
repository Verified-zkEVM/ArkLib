/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Data.Matrix.Mul

/-!
# Kernel vectors descend along coefficient maps

Let `A` be a matrix over a field `K` and `f : K →+* S` a ring homomorphism.

A kernel vector of the mapped matrix with a nonzero coordinate `j` gives one of `A` over `K`.

Otherwise the coordinate `j` is a combination of the rows of `A`, and that identity maps to `S`.

## Main statements

* `Matrix.exists_mulVec_eq_zero_apply_ne_zero_of_map`: the descent of a kernel vector.
-/

@[expose] public section

namespace Matrix

/-- A kernel vector of `A.map f` with a nonzero coordinate `j` gives one of `A` over `K`. -/
theorem exists_mulVec_eq_zero_apply_ne_zero_of_map {m n K S : Type*} [Finite m] [Fintype n]
    [Field K] [CommRing S] (f : K →+* S) (A : Matrix m n K) {c : n → S}
    (hc : A.map f *ᵥ c = 0) {j : n} (hj : c j ≠ 0) :
    ∃ c' : n → K, A *ᵥ c' = 0 ∧ c' j ≠ 0 := by
  classical
  have := Fintype.ofFinite m
  by_contra! hcon
  -- The coordinate `j` vanishes on the kernel of `A`, so it is a combination `y` of the rows.
  have hmem : LinearMap.proj (R := K) (φ := fun _ : n ↦ K) j ∈
      (Matrix.mulVecLin A).ker.dualAnnihilator :=
    (Submodule.mem_dualAnnihilator _).2 fun w hw ↦ hcon w hw
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
  obtain ⟨h, hh⟩ := hmem
  set y : m → K := fun k ↦ h (Pi.single k 1)
  have hw : y ᵥ* A = Pi.single j 1 := by
    ext l
    have := LinearMap.congr_fun hh (Pi.single l 1)
    simp only [LinearMap.dualMap_apply, mulVecLin_apply, mulVec_single_one,
      LinearMap.proj_apply] at this
    rw [LinearMap.pi_apply_eq_sum_univ] at this
    rw [show (Pi.single j (1 : K) : n → K) l = (Pi.single l (1 : K) : n → K) j by
      simp [Pi.single_apply, eq_comm], ← this, vecMul, dotProduct]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hs : (fun i ↦ if k = i then (1 : K) else 0) = Pi.single k 1 := by
      funext i; simp [Pi.single_apply, eq_comm]
    simp only [y, smul_eq_mul, col_apply, hs, mul_comm]
  -- The same combination of the mapped rows reads off `c j`, which is therefore zero.
  have hmap : (fun k ↦ f (y k)) ᵥ* A.map f = fun l ↦ f ((y ᵥ* A) l) := by
    ext l
    simp [vecMul, dotProduct, map_sum]
  apply hj
  have := congrArg (dotProduct (fun k ↦ f (y k))) hc
  rw [dotProduct_mulVec, hmap, hw, dotProduct_zero] at this
  simpa [dotProduct, Pi.single_apply] using this

end Matrix
