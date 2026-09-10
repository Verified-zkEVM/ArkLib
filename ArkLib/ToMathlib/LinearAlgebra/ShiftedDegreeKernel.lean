/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.LinearAlgebra.PrimitivePolynomialKernel

/-!
# Polynomial kernel vectors with shifted row and column degrees

A polynomial matrix arising from a graded map has a degree attached to every source column and
every target row. An entry from column `j` to row `i` has degree at most the difference of these
weights, and it is zero when that difference is negative. At height `h`, column `j` therefore
contributes `h + 1 - columnWeight j` unknown coefficients, while row `i` imposes only
`h + 1 - rowWeight i` equations.

This file turns a strict surplus of these truncated coefficient counts into a nonzero polynomial
kernel vector. The proof retains the forced-zero condition explicitly; assigning natural degree
zero to a forbidden entry would incorrectly treat a nonzero constant as admissible. Primitive
normalization preserves every individual coordinate bound and makes specialization nonzero over
all field extensions.
-/

@[expose] public section

open Polynomial
open scoped BigOperators

namespace Matrix

variable {F : Type*} [Field F]

/-- A strict shifted coefficient-slot surplus gives a nonzero polynomial kernel vector.

The first entry condition handles nonnegative weight differences. The second condition records
that entries of negative shifted degree are genuinely zero. All slot counts use natural
subtraction, so source columns and target rows above `h` are inactive. -/
theorem exists_ne_zero_mulVec_eq_zero_shifted_degreeLT {rows cols : ℕ}
    (M : Matrix (Fin rows) (Fin cols) F[X]) (rowWeight : Fin rows → ℕ)
    (columnWeight : Fin cols → ℕ) (h : ℕ)
    (hdegree : ∀ i j, rowWeight i ≤ columnWeight j →
      (M i j).natDegree ≤ columnWeight j - rowWeight i)
    (hzero : ∀ i j, columnWeight j < rowWeight i → M i j = 0)
    (hsurplus : Finset.univ.sum (fun i : Fin rows ↦ h + 1 - rowWeight i) <
      Finset.univ.sum (fun j : Fin cols ↦ h + 1 - columnWeight j)) :
    ∃ v : Fin cols → F[X], v ≠ 0 ∧ M *ᵥ v = 0 ∧
      ∀ j, v j ∈ Polynomial.degreeLT F (h + 1 - columnWeight j) := by
  classical
  let columnSlots := fun j ↦ h + 1 - columnWeight j
  let rowSlots := fun i ↦ h + 1 - rowWeight i
  let decode (j : Fin cols) : (Fin (columnSlots j) → F) →ₗ[F] F[X] :=
    (Polynomial.degreeLT F (columnSlots j)).subtype ∘ₗ
      (Polynomial.degreeLTEquiv F (columnSlots j)).symm.toLinearMap
  let decodeVec : (∀ j, Fin (columnSlots j) → F) →ₗ[F] (Fin cols → F[X]) :=
    LinearMap.pi fun j ↦ decode j ∘ₗ LinearMap.proj j
  let takeCoeffs : (Fin rows → F[X]) →ₗ[F] (∀ i, Fin (rowSlots i) → F) :=
    LinearMap.pi fun i ↦ LinearMap.pi fun k ↦
      Polynomial.lcoeff F k ∘ₗ LinearMap.proj i
  let coefficientMap : (∀ j, Fin (columnSlots j) → F) →ₗ[F]
      (∀ i, Fin (rowSlots i) → F) :=
    takeCoeffs ∘ₗ (M.mulVecLin.restrictScalars F) ∘ₗ decodeVec
  have hdim : Module.finrank F (∀ i, Fin (rowSlots i) → F) <
      Module.finrank F (∀ j, Fin (columnSlots j) → F) := by
    simpa [Module.finrank_pi_fintype, rowSlots, columnSlots] using hsurplus
  obtain ⟨c, hc, hcne⟩ := (LinearMap.ker coefficientMap).ne_bot_iff.mp
    (coefficientMap.ker_ne_bot_of_finrank_lt hdim)
  let v : Fin cols → F[X] := fun j ↦ decode j (c j)
  have hvdegree (j : Fin cols) : v j ∈ Polynomial.degreeLT F (columnSlots j) :=
    ((Polynomial.degreeLTEquiv F (columnSlots j)).symm (c j)).property
  have hvzero (j : Fin cols) (hj : h < columnWeight j) : v j = 0 := by
    have hslots : columnSlots j = 0 := by dsimp [columnSlots]; omega
    have hv := hvdegree j
    rw [hslots] at hv
    apply Polynomial.ext
    intro k
    exact (Polynomial.degree_lt_iff_coeff_zero _ 0).mp
      (Polynomial.mem_degreeLT.mp hv) k (Nat.zero_le _)
  have hproduct (i : Fin rows) (j : Fin cols) (hi : rowWeight i ≤ h) :
      (M i j * v j).natDegree ≤ h - rowWeight i := by
    by_cases hij : rowWeight i ≤ columnWeight j
    · by_cases hj : columnWeight j ≤ h
      · have hslots : columnSlots j = (h - columnWeight j) + 1 := by
          dsimp [columnSlots]
          omega
        have hv : (v j).natDegree ≤ h - columnWeight j := by
          have hv' := hvdegree j
          rw [hslots, Polynomial.degreeLT_succ_eq_degreeLE] at hv'
          exact Polynomial.natDegree_le_of_degree_le (Polynomial.mem_degreeLE.mp hv')
        exact (Polynomial.natDegree_mul_le_of_le (hdegree i j hij) hv).trans (by omega)
      · simp [hvzero j (Nat.lt_of_not_ge hj)]
    · simp [hzero i j (Nat.lt_of_not_ge hij)]
  have hmulVec_degreeLT (i : Fin rows) :
      (M *ᵥ v) i ∈ Polynomial.degreeLT F (rowSlots i) := by
    by_cases hi : rowWeight i ≤ h
    · have hslots : rowSlots i = (h - rowWeight i) + 1 := by
        dsimp [rowSlots]
        omega
      rw [hslots, Polynomial.degreeLT_succ_eq_degreeLE]
      apply Polynomial.mem_degreeLE.mpr
      exact Polynomial.degree_le_natDegree.trans <| WithBot.coe_le_coe.mpr
        (Polynomial.natDegree_sum_le_of_forall_le Finset.univ _ fun j _ ↦ hproduct i j hi)
    · have hrow : h < rowWeight i := Nat.lt_of_not_ge hi
      have hsum : (M *ᵥ v) i = 0 := by
        change ∑ j, M i j * v j = 0
        apply Finset.sum_eq_zero
        intro j _
        by_cases hj : columnWeight j ≤ h
        · simp [hzero i j (hj.trans_lt hrow)]
        · simp [hvzero j (Nat.lt_of_not_ge hj)]
      simp [hsum]
  have hmulVec : M *ᵥ v = 0 := by
    funext i
    apply Polynomial.ext
    intro k
    by_cases hk : k < rowSlots i
    · let k' : Fin (rowSlots i) := ⟨k, hk⟩
      have hcoefficient := congrFun (congrFun (LinearMap.mem_ker.mp hc) i) k'
      have hdecodeVec : decodeVec c = v := by ext j; rfl
      simp only [coefficientMap, LinearMap.comp_apply] at hcoefficient
      rw [hdecodeVec] at hcoefficient
      simpa [takeCoeffs, k'] using hcoefficient
    · simp only [Pi.zero_apply, coeff_zero]
      exact (Polynomial.degree_lt_iff_coeff_zero _ _).mp
        (Polynomial.mem_degreeLT.mp (hmulVec_degreeLT i)) k (Nat.le_of_not_gt hk)
  have hvne : v ≠ 0 := by
    intro hv
    apply hcne
    have hdecode (j : Fin cols) : Function.Injective (decode j) := by
      intro x y hxy
      apply (Polynomial.degreeLTEquiv F (columnSlots j)).symm.injective
      apply Subtype.ext
      exact hxy
    funext j
    apply hdecode j
    simpa [v] using congrFun hv j
  exact ⟨v, hvne, hmulVec, hvdegree⟩

/-- Primitive normalization of a bounded kernel vector preserves zero-width as well as
positive degree slots. This form records membership in each possibly different `degreeLT`
subspace and derives from the shared gcd normalization theorem. -/
theorem exists_primitive_kernel_vector_degreeLT {rows cols : ℕ}
    (M : Matrix (Fin rows) (Fin cols) F[X]) (slots : Fin cols → ℕ)
    (v : Fin cols → F[X]) (hv : v ≠ 0) (hMv : M *ᵥ v = 0)
    (hvdegree : ∀ j, v j ∈ Polynomial.degreeLT F (slots j)) :
    ∃ u : Fin cols → F[X], u ≠ 0 ∧ M *ᵥ u = 0 ∧
      (∀ j, u j ∈ Polynomial.degreeLT F (slots j)) ∧
      Ideal.span (Set.range u) = ⊤ ∧
      ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
        (fun j ↦ (u j).eval₂ ι z) ≠ 0 := by
  obtain ⟨u, hu, hMu, hu_natDegree, hu_zero, hu_span, hu_specialize⟩ :=
    exists_primitive_kernel_vector_preserving_zero M v hv hMv
  refine ⟨u, hu, hMu, ?_, hu_span, hu_specialize⟩
  intro j
  by_cases hvj : v j = 0
  · simp [hu_zero j hvj]
  by_cases huj : u j = 0
  · simp [huj]
  apply Polynomial.mem_degreeLT.mpr
  rw [← Polynomial.natDegree_lt_iff_degree_lt huj]
  exact (hu_natDegree j).trans_lt <|
    (Polynomial.natDegree_lt_iff_degree_lt hvj).mpr
      (Polynomial.mem_degreeLT.mp (hvdegree j))

/-- Primitive normalization preserves all shifted coordinate budgets and prevents simultaneous
vanishing after specialization over any field extension. -/
theorem exists_primitive_mulVec_eq_zero_of_shifted_surplus {rows cols : ℕ}
    (M : Matrix (Fin rows) (Fin cols) F[X]) (rowWeight : Fin rows → ℕ)
    (columnWeight : Fin cols → ℕ) (h : ℕ)
    (hdegree : ∀ i j, rowWeight i ≤ columnWeight j →
      (M i j).natDegree ≤ columnWeight j - rowWeight i)
    (hzero : ∀ i j, columnWeight j < rowWeight i → M i j = 0)
    (hsurplus : Finset.univ.sum (fun i : Fin rows ↦ h + 1 - rowWeight i) <
      Finset.univ.sum (fun j : Fin cols ↦ h + 1 - columnWeight j)) :
    ∃ v : Fin cols → F[X], v ≠ 0 ∧ M *ᵥ v = 0 ∧
      (∀ j, v j ∈ Polynomial.degreeLT F (h + 1 - columnWeight j)) ∧
      Ideal.span (Set.range v) = ⊤ ∧
      ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
        (fun j ↦ (v j).eval₂ ι z) ≠ 0 := by
  obtain ⟨v, hv, hMv, hvdegree⟩ :=
    exists_ne_zero_mulVec_eq_zero_shifted_degreeLT M rowWeight columnWeight h
      hdegree hzero hsurplus
  exact exists_primitive_kernel_vector_degreeLT M
    (fun j ↦ h + 1 - columnWeight j) v hv hMv hvdegree

end Matrix
