/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.LinearAlgebra.PolynomialKernelHeight
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Acceptance client for polynomial kernel height

The first examples use non-`Fin` index types and a nonconstant matrix. They check both the
generalized index interface and the strict `degreeLT` contract of the principal theorem.

The remaining examples use the rank over `RatFunc F`, as the Reed–Solomon interpolation consumers
do. They start from `rank ≤ r` and `r < N` with `Fin N` columns and obtain the natural-degree
bound `r * b / (N - r)` with no separate monotonicity argument. They also recover the primitive
statements of the source revision, including the clause that the coordinates have no common root
`z` in any field extension `ι : F →+* E`, from the gcd normalization and
`Ideal.comp_ne_zero_of_span_range_eq_top`.
-/

open Polynomial

namespace Matrix

private noncomputable def kernelHeightCanary : Matrix Unit Bool ℚ[X] :=
  fun _ j ↦ if j then X else 1

/-- The one-by-two matrix `[1, X]` has a nonzero kernel vector of coordinate degree below two. -/
example :
    ∃ v : Bool → ℚ[X],
      v ≠ 0 ∧ kernelHeightCanary *ᵥ v = 0 ∧ ∀ j, v j ∈ Polynomial.degreeLT ℚ 2 := by
  have hdegree : ∀ i j, (kernelHeightCanary i j).natDegree ≤ 1 := by
    intro i j
    cases j <;> simp [kernelHeightCanary]
  simpa using exists_ne_zero_mulVec_eq_zero_degreeLT kernelHeightCanary hdegree (by decide)

/-- The empty-row boundary still produces a nonzero constant kernel vector. -/
example {F : Type*} [Field F] (M : Matrix Empty Unit F[X]) :
    ∃ v : Unit → F[X],
      v ≠ 0 ∧ M *ᵥ v = 0 ∧ ∀ j, v j ∈ Polynomial.degreeLT F 1 := by
  have hdegree : ∀ i j, (M i j).natDegree ≤ 0 := by
    intro i
    exact Empty.elim i
  simpa using
    exists_ne_zero_mulVec_eq_zero_degreeLT (b := 0) M hdegree (by decide)

/-- Specializing the generalized index types to `Fin` recovers the immutable source statement
without changing its hypotheses, degree formula, or quantifier order. -/
example {F : Type*} [Field F] {n N b : ℕ}
    (M : Matrix (Fin n) (Fin N) F[X]) (hdeg : ∀ i j, (M i j).natDegree ≤ b)
    (hN : n < N) :
    ∃ v : Fin N → F[X],
      v ≠ 0 ∧ M *ᵥ v = 0 ∧ ∀ j, (v j).natDegree ≤ n * b / (N - n) := by
  simpa using exists_ne_zero_mulVec_eq_zero_natDegree_le M hdeg (by simpa using hN)

/-- The consumer shape: rank at most `r` over `RatFunc F`, `r < N`, and `Fin N` columns give a
primitive kernel vector with natural degrees at most `r * b / (N - r)` whose coordinates have no
common root in any field extension. -/
example {F : Type*} [Field F] {m N b r : ℕ} (M : Matrix (Fin m) (Fin N) F[X])
    (hdeg : ∀ i j, (M i j).natDegree ≤ b)
    (hrank : (M.map (algebraMap F[X] (RatFunc F))).rank ≤ r) (hrN : r < N) :
    ∃ v : Fin N → F[X],
      v ≠ 0 ∧ M *ᵥ v = 0 ∧ (∀ j, (v j).natDegree ≤ r * b / (N - r)) ∧
        Ideal.span (Set.range v) = ⊤ ∧
          ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E), (fun j ↦ (v j).eval₂ ι z) ≠ 0 := by
  obtain ⟨v, hv, hMv, hvdegree, hspan⟩ :=
    exists_primitive_ne_zero_mulVec_eq_zero_degreeLT_of_rank_le M hdeg _
      (IsFractionRing.injective F[X] (RatFunc F)) hrank (by simpa using hrN)
  refine ⟨v, hv, hMv, fun j ↦ ?_, hspan, fun ι z ↦ ?_⟩
  · exact natDegree_le_of_mem_degreeLT_succ (by simpa using hvdegree j)
  · exact Ideal.comp_ne_zero_of_span_range_eq_top hspan (eval₂RingHom ι z)

/-- The source statement with the exact rank `s` follows by weakening `hrank` to `≤`. -/
example {F : Type*} [Field F] {m N b s : ℕ} (M : Matrix (Fin m) (Fin N) F[X])
    (hdeg : ∀ i j, (M i j).natDegree ≤ b)
    (hrank : (M.map (algebraMap F[X] (RatFunc F))).rank = s) (hs : s < N) :
    ∃ v : Fin N → F[X], v ≠ 0 ∧ M *ᵥ v = 0 ∧ ∀ j, (v j).natDegree ≤ s * b / (N - s) := by
  simpa using exists_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_le M hdeg _
    (IsFractionRing.injective F[X] (RatFunc F)) hrank.le (by simpa using hs)

/-- The source row-count primitive statement is the rank form with `s := n`, where
`Matrix.rank_le_card_height` bounds the rank by the number of rows. -/
example {F : Type*} [Field F] {n N b : ℕ} (M : Matrix (Fin n) (Fin N) F[X])
    (hdeg : ∀ i j, (M i j).natDegree ≤ b) (hN : n < N) :
    ∃ v : Fin N → F[X],
      v ≠ 0 ∧ M *ᵥ v = 0 ∧ (∀ j, (v j).natDegree ≤ n * b / (N - n)) ∧
        Ideal.span (Set.range v) = ⊤ ∧
          ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E), (fun j ↦ (v j).eval₂ ι z) ≠ 0 := by
  have hrank : (M.map (algebraMap F[X] (RatFunc F))).rank ≤ n := by
    simpa using (M.map (algebraMap F[X] (RatFunc F))).rank_le_card_height
  obtain ⟨v, hv, hMv, hvdegree, hspan⟩ :=
    exists_primitive_ne_zero_mulVec_eq_zero_degreeLT_of_rank_le M hdeg _
      (IsFractionRing.injective F[X] (RatFunc F)) hrank (by simpa using hN)
  refine ⟨v, hv, hMv, fun j ↦ ?_, hspan, fun ι z ↦ ?_⟩
  · exact natDegree_le_of_mem_degreeLT_succ (by simpa using hvdegree j)
  · exact Ideal.comp_ne_zero_of_span_range_eq_top hspan (eval₂RingHom ι z)

/-- The source's zero-preserving normalization follows from `v = g • u`: a zero coordinate of `v`
is a zero coordinate of `u`, and a nonzero coordinate of `v` is a multiple of the coordinate of
`u`, so its natural degree does not drop below that of `u`. -/
example {F : Type*} [Field F] {m N : ℕ} (M : Matrix (Fin m) (Fin N) F[X])
    (v : Fin N → F[X]) (hv : v ≠ 0) (hMv : M *ᵥ v = 0) :
    ∃ u : Fin N → F[X],
      u ≠ 0 ∧ M *ᵥ u = 0 ∧ (∀ j, (u j).natDegree ≤ (v j).natDegree) ∧
        (∀ j, v j = 0 → u j = 0) ∧ Ideal.span (Set.range u) = ⊤ ∧
          ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E), (fun j ↦ (u j).eval₂ ι z) ≠ 0 := by
  classical
  obtain ⟨g, u, hg, rfl, hu, hMu, hspan⟩ := M.exists_primitive_kernel_vector_eq_smul hv hMv
  have hzero : ∀ j, g * u j = 0 → u j = 0 := fun j hj ↦ (mul_eq_zero.mp hj).resolve_left hg
  refine ⟨u, hu, hMu, fun j ↦ ?_, fun j hj ↦ hzero j hj, hspan, fun ι z ↦
    Ideal.comp_ne_zero_of_span_range_eq_top hspan (eval₂RingHom ι z)⟩
  change (u j).natDegree ≤ (g * u j).natDegree
  by_cases hj : g * u j = 0
  · simp [hzero j hj]
  · exact natDegree_le_of_dvd (dvd_mul_left _ _) hj

/-- Normalization keeps a separate strict degree budget for each coordinate
(`Matrix.exists_primitive_kernel_vector_degreeLT`), which recovers the source's shifted-degree
primitive statement. -/
example {F : Type*} [Field F] {rows cols : ℕ} (M : Matrix (Fin rows) (Fin cols) F[X])
    (slots : Fin cols → ℕ) (v : Fin cols → F[X]) (hv : v ≠ 0) (hMv : M *ᵥ v = 0)
    (hvdegree : ∀ j, v j ∈ degreeLT F (slots j)) :
    ∃ u : Fin cols → F[X], u ≠ 0 ∧ M *ᵥ u = 0 ∧ (∀ j, u j ∈ degreeLT F (slots j)) ∧
      Ideal.span (Set.range u) = ⊤ ∧
        ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E), (fun j ↦ (u j).eval₂ ι z) ≠ 0 := by
  obtain ⟨u, hu, hMu, hudegree, hspan⟩ :=
    exists_primitive_kernel_vector_degreeLT M slots hv hMv hvdegree
  exact ⟨u, hu, hMu, hudegree, hspan, fun ι z ↦
    Ideal.comp_ne_zero_of_span_range_eq_top hspan (eval₂RingHom ι z)⟩

end Matrix

/--
info: 'Matrix.exists_ne_zero_mulVec_eq_zero_degreeLT' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_ne_zero_mulVec_eq_zero_degreeLT

/--
info: 'Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le

/--
info: 'Matrix.exists_ne_zero_mulVec_eq_zero_degreeLT_of_rank_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_ne_zero_mulVec_eq_zero_degreeLT_of_rank_le

/--
info: 'Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_le

/--
info: 'Matrix.exists_primitive_ne_zero_mulVec_eq_zero_degreeLT_of_rank_le' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_primitive_ne_zero_mulVec_eq_zero_degreeLT_of_rank_le
