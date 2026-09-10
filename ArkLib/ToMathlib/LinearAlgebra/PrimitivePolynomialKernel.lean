/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.LinearAlgebra.PolynomialKernelHeight
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Primitive polynomial kernel vectors

This file normalizes a nonzero polynomial kernel vector by the greatest common divisor of its
coordinates. The normalized vector remains in the same kernel, its coordinate degrees do not
increase, and its coordinates generate the unit ideal. Consequently, after any field extension,
the coordinates cannot vanish simultaneously at any point.
-/

@[expose] public section

open Polynomial

namespace Matrix

variable {F : Type*} [Field F]

/-- Primitive normalization also preserves every coordinate that was already zero.  This
stronger form is the common normalization core for uniform and shifted degree bounds. -/
theorem exists_primitive_kernel_vector_preserving_zero {m N : ℕ}
    (M : Matrix (Fin m) (Fin N) F[X])
    (v : Fin N → F[X]) (hv : v ≠ 0) (hMv : M *ᵥ v = 0) :
    ∃ u : Fin N → F[X],
      u ≠ 0 ∧ M *ᵥ u = 0 ∧
        (∀ j, (u j).natDegree ≤ (v j).natDegree) ∧
          (∀ j, v j = 0 → u j = 0) ∧
          Ideal.span (Set.range u) = ⊤ ∧
            ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
              (fun j ↦ (u j).eval₂ ι z) ≠ 0 := by
  classical
  have hv_exists : ∃ j, v j ≠ 0 := by
    by_contra h
    apply hv
    funext j
    exact not_ne_iff.mp (not_exists.mp h j)
  obtain ⟨j₀, hj₀⟩ := hv_exists
  let g : F[X] := Finset.univ.gcd v
  let u : Fin N → F[X] := fun j ↦ v j / g
  have hg : g ≠ 0 := by
    exact Finset.gcd_ne_zero_iff.mpr ⟨j₀, Finset.mem_univ j₀, hj₀⟩
  have hgrecon (j : Fin N) : g * u j = v j := by
    exact EuclideanDomain.mul_div_cancel' hg (Finset.gcd_dvd (Finset.mem_univ j))
  have hu : u ≠ 0 := by
    intro hu_zero
    have hj := hgrecon j₀
    rw [congrFun hu_zero j₀, Pi.zero_apply, mul_zero] at hj
    exact hj₀ hj.symm
  have hu_degree (j : Fin N) : (u j).natDegree ≤ (v j).natDegree := by
    by_cases huj : u j = 0
    · simp [huj]
    · rw [← hgrecon j, Polynomial.natDegree_mul hg huj]
      omega
  have hu_zero (j : Fin N) (hvj : v j = 0) : u j = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hg
    rw [hgrecon j, hvj]
  have hMu : M *ᵥ u = 0 := by
    funext i
    apply (mul_eq_zero.mp ?_).resolve_left hg
    calc
      g * (M *ᵥ u) i = ∑ j, g * (M i j * u j) := by
        simp [Matrix.mulVec, dotProduct, Finset.mul_sum]
      _ = ∑ j, M i j * v j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← hgrecon j]
        ac_rfl
      _ = (M *ᵥ v) i := by rfl
      _ = 0 := congrFun hMv i
  have hu_gcd : Finset.univ.gcd u = 1 := by
    simpa [u, g] using
      (Finset.gcd_div_eq_one (s := Finset.univ) (f := v) (i := j₀)
        (Finset.mem_univ j₀) hj₀)
  obtain ⟨c, hc⟩ := Finset.gcd_eq_sum_mul Finset.univ u
  have hu_span : Ideal.span (Set.range u) = ⊤ := by
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]
    refine ⟨c, ?_⟩
    calc
      ∑ j, c j * u j = ∑ j, u j * c j := by
        apply Finset.sum_congr rfl
        intro j _
        exact mul_comm _ _
      _ = Finset.univ.gcd u := hc.symm
      _ = 1 := hu_gcd
  refine ⟨u, hu, hMu, hu_degree, hu_zero, hu_span, ?_⟩
  intro E _ ι z hzero
  have hbezout : ∑ j, c j * u j = 1 := by
    calc
      ∑ j, c j * u j = ∑ j, u j * c j := by
        apply Finset.sum_congr rfl
        intro j _
        exact mul_comm _ _
      _ = Finset.univ.gcd u := hc.symm
      _ = 1 := hu_gcd
  have heval := congrArg (Polynomial.eval₂RingHom ι z) hbezout
  have hj (j : Fin N) : (u j).eval₂ ι z = 0 := congrFun hzero j
  simp [hj] at heval

/-- Dividing a nonzero polynomial kernel vector by the gcd of its coordinates produces a
primitive kernel vector. The coordinate degrees do not increase. -/
theorem exists_primitive_kernel_vector {m N : ℕ} (M : Matrix (Fin m) (Fin N) F[X])
    (v : Fin N → F[X]) (hv : v ≠ 0) (hMv : M *ᵥ v = 0) :
    ∃ u : Fin N → F[X],
      u ≠ 0 ∧ M *ᵥ u = 0 ∧
        (∀ j, (u j).natDegree ≤ (v j).natDegree) ∧
          Ideal.span (Set.range u) = ⊤ ∧
            ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
              (fun j ↦ (u j).eval₂ ι z) ≠ 0 := by
  obtain ⟨u, hu, hMu, hu_degree, _, hu_span, hu_no_common_zero⟩ :=
    exists_primitive_kernel_vector_preserving_zero M v hv hMv
  exact ⟨u, hu, hMu, hu_degree, hu_span, hu_no_common_zero⟩

/-- Row-count polynomial kernel height with primitive coordinates. -/
theorem exists_primitive_ne_zero_mulVec_eq_zero_natDegree_le {n N b : ℕ}
    (M : Matrix (Fin n) (Fin N) F[X]) (hdeg : ∀ i j, (M i j).natDegree ≤ b)
    (hN : n < N) :
    ∃ v : Fin N → F[X],
      v ≠ 0 ∧ M *ᵥ v = 0 ∧
        (∀ j, (v j).natDegree ≤ n * b / (N - n)) ∧
          Ideal.span (Set.range v) = ⊤ ∧
            ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
              (fun j ↦ (v j).eval₂ ι z) ≠ 0 := by
  obtain ⟨v, hv, hMv, hv_degree⟩ :=
    exists_ne_zero_mulVec_eq_zero_natDegree_le M hdeg hN
  obtain ⟨u, hu, hMu, hu_degree, hu_span, hu_no_common_zero⟩ :=
    exists_primitive_kernel_vector M v hv hMv
  exact ⟨u, hu, hMu, fun j ↦ (hu_degree j).trans (hv_degree j), hu_span,
    hu_no_common_zero⟩

/-- Intrinsic-rank polynomial kernel height with primitive coordinates. The rank is measured
after mapping the polynomial matrix into the rational function field. -/
theorem exists_primitive_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_eq {m N b s : ℕ}
    (M : Matrix (Fin m) (Fin N) F[X]) (hdeg : ∀ i j, (M i j).natDegree ≤ b)
    (hrank : (M.map (algebraMap F[X] (RatFunc F))).rank = s) (hs : s < N) :
    ∃ v : Fin N → F[X],
      v ≠ 0 ∧ M *ᵥ v = 0 ∧
        (∀ j, (v j).natDegree ≤ s * b / (N - s)) ∧
          Ideal.span (Set.range v) = ⊤ ∧
            ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
              (fun j ↦ (v j).eval₂ ι z) ≠ 0 := by
  obtain ⟨v, hv, hMv, hv_degree⟩ :=
    exists_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_eq M hdeg hrank hs
  obtain ⟨u, hu, hMu, hu_degree, hu_span, hu_no_common_zero⟩ :=
    exists_primitive_kernel_vector M v hv hMv
  exact ⟨u, hu, hMu, fun j ↦ (hu_degree j).trans (hv_degree j), hu_span,
    hu_no_common_zero⟩

end Matrix
