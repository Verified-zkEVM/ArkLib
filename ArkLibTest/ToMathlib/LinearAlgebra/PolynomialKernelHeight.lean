/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.LinearAlgebra.PolynomialKernelHeight

/-!
# Acceptance client for uniform polynomial kernel height

The example uses non-`Fin` index types and a nonconstant matrix. It checks both the generalized
index interface and the strict `degreeLT` contract of the principal theorem.
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
