/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
  -- The first `N + 1` coefficients, then the quotient by the image of `V`.
  set c : E[X] →ₗ[E] (Fin (N + 1) → E) := LinearMap.pi fun i ↦ lcoeff E i
  set W := V.map c
  set b := Module.finBasis E ((Fin (N + 1) → E) ⧸ W)
  refine ⟨List.ofFn fun j ↦ (b.coord j).comp (W.mkQ.comp c), ?_, fun H hH hl ↦ ?_⟩
  · intro Λ hΛ v hv
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hΛ
    simp [(Submodule.Quotient.mk_eq_zero W).mpr (Submodule.mem_map_of_mem hv)]
  · have hq : W.mkQ (c H) = 0 := b.forall_coord_eq_zero_iff.mp fun j ↦
      hl _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
    obtain ⟨v, hv, hvH⟩ := Submodule.mem_map.mp ((Submodule.Quotient.mk_eq_zero W).mp hq)
    have hvN : v.degree ≤ N := mem_degreeLE.mp (hV hv)
    convert hv using 1
    ext n
    by_cases hn : n ≤ N
    · exact (congrFun hvH ⟨n, Nat.lt_succ_of_le hn⟩).symm
    · rw [coeff_eq_zero_of_degree_lt (hH.trans_lt (by exact_mod_cast not_le.mp hn)),
        coeff_eq_zero_of_degree_lt (hvN.trans_lt (by exact_mod_cast not_le.mp hn))]

end Polynomial
