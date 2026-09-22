/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.MvPolynomial.MonomialMap

/-!
# Acceptance tests for monomial maps

The examples compute the monomial map and the point of monomial values on small exponent sets,
state the linear lift of a polynomial supported on `S` together with its vanishing at
corresponding points, and show that surjectivity, injectivity on points, and the degree bound
need their hypotheses.
-/

open MvPolynomial

open scoped Pointwise

namespace MonomialMapTest

/-- The monomial map of `{2 • e₀}` sends its variable to `X 0 ^ 2`. -/
example : monomialMap ℚ ({Finsupp.single (0 : Fin 1) 2} : Set (Fin 1 →₀ ℕ))
    (X ⟨_, rfl⟩) = X 0 ^ 2 := by
  rw [monomialMap_X, X_pow_eq_monomial]

/-- The point of monomial values of `{e₀ + e₁}` at `x` is `x 0 * x 1`. -/
example (x : Fin 2 → ℚ) :
    monomialPoint ({Finsupp.single 0 1 + Finsupp.single 1 1} : Set (Fin 2 →₀ ℕ)) x ⟨_, rfl⟩ =
      x 0 * x 1 := by
  rw [monomialPoint_apply, Finsupp.prod_add_index' (by simp) (by simp [pow_add])]
  simp

/-- The linear lift of a polynomial supported on `S` has total degree at most `1`, and vanishes
at the point of monomial values of `x` exactly when the polynomial vanishes at `x`. -/
example {τ : Type*} {S : Set (τ →₀ ℕ)} (x : τ → ℚ) (q : MvPolynomial τ ℚ)
    (hq : q ∈ restrictSupport ℚ S) :
    (monomialLift q hq).totalDegree ≤ 1 ∧
      (aeval (monomialPoint S x) (monomialLift q hq) = 0 ↔ aeval x q = 0) := by
  rw [aeval_monomialPoint, monomialMap_monomialLift]
  exact ⟨totalDegree_monomialLift_le_one q hq, Iff.rfl⟩

/-- `monomialMap_surjective` needs the exponents `Finsupp.single i 1`: the monomial map of the
empty set is not surjective, since evaluation at the points `0` and `1` factors through the empty
point of monomial values. -/
example : ¬Function.Surjective (monomialMap ℚ (∅ : Set (Fin 1 →₀ ℕ))) := by
  intro h
  obtain ⟨P, hP⟩ := h (X 0)
  have h0 := aeval_monomialPoint (fun _ ↦ (0 : ℚ)) P
  have h1 := aeval_monomialPoint (fun _ ↦ (1 : ℚ)) P
  rw [hP, aeval_X] at h0 h1
  have hpt : monomialPoint (∅ : Set (Fin 1 →₀ ℕ)) (fun _ ↦ (0 : ℚ)) =
      monomialPoint ∅ fun _ ↦ 1 := funext fun m ↦ m.2.elim
  rw [hpt, h1] at h0
  exact one_ne_zero h0

/-- `monomialPoint_injective` needs the exponents `Finsupp.single i 1`: on the empty set of
exponents every point has the same point of monomial values. -/
example : ¬Function.Injective (monomialPoint (E := ℚ) (∅ : Set (Fin 1 →₀ ℕ))) := by
  intro h
  have := congrFun (h (a₁ := fun _ ↦ 0) (a₂ := fun _ ↦ 1) (funext fun m ↦ m.2.elim)) 0
  exact zero_ne_one this

/-- `monomialMap_mem_restrictSupport_nsmul` needs `0 ∈ S`: for `S = {e₀}` the constant `1` has
total degree `0 ≤ 1`, but its image `1` is not supported on `1 • S = S`. -/
example : ¬monomialMap ℚ ({Finsupp.single (0 : Fin 1) 1} : Set (Fin 1 →₀ ℕ)) 1 ∈
    restrictSupport ℚ (1 • ({Finsupp.single (0 : Fin 1) 1} : Set (Fin 1 →₀ ℕ))) := by
  rw [map_one, one_smul, ← C_1, ← monomial_zero', monomial_mem_restrictSupport]
  simp [eq_comm]

end MonomialMapTest
