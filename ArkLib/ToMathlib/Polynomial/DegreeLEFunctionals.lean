/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.ToMathlib.LinearAlgebra.FiniteDimensional
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Finitely many functionals cut out a space of bounded-degree polynomials

Let `V` be a space of polynomials of degree at most `N` over a field.
Finitely many linear functionals on all polynomials vanish on `V`.
Among polynomials of degree at most `N`, they vanish only on `V`.

The functionals read the first `N + 1` coefficients.
They then take coordinates in a basis of the quotient by the image of `V`.

## Main statements

* `Polynomial.exists_list_linearMap_of_le_degreeLE`: such functionals exist.
-/

@[expose] public section

namespace Polynomial

/-- Let `V` be a space of polynomials of degree at most `N` over a field `E`.
A finite list of linear functionals vanishes on `V`.
A polynomial of degree at most `N` on which they all vanish lies in `V`. -/
theorem exists_list_linearMap_of_le_degreeLE {E : Type*} [Field E] {N : ℕ}
    {V : Submodule E E[X]} (hV : V ≤ degreeLE E N) :
    ∃ l : List (E[X] →ₗ[E] E), (∀ Λ ∈ l, ∀ v ∈ V, Λ v = 0) ∧
      ∀ H : E[X], H.degree ≤ N → (∀ Λ ∈ l, Λ H = 0) → H ∈ V := by
  let c : E[X] →ₗ[E] (Fin (N + 1) → E) := LinearMap.pi fun i ↦ lcoeff E i
  have hc : Set.InjOn c (degreeLE E N) := by
    intro P hP Q hQ hPQ
    have hPdeg := mem_degreeLE.mp hP
    have hQdeg := mem_degreeLE.mp hQ
    ext n
    by_cases hn : n ≤ N
    · exact congrFun hPQ ⟨n, Nat.lt_succ_of_le hn⟩
    · rw [coeff_eq_zero_of_degree_lt (hPdeg.trans_lt (by exact_mod_cast not_le.mp hn)),
        coeff_eq_zero_of_degree_lt (hQdeg.trans_lt (by exact_mod_cast not_le.mp hn))]
  simpa only [SetLike.mem_coe, mem_degreeLE] using
    Submodule.exists_list_linearMap_of_injOn hV c hc

end Polynomial
