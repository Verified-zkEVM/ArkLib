/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Coordinates
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Triangular support at derivative order zero

When the derivative order is zero, the local constraint map has only the variables `T` and `E`.
Every supported monomial satisfies `E ≤ T < m`, so the image lies in a finite-dimensional space
with at most `m * (m + 1) / 2` coordinates. This file gives the exponent set and the resulting
rank bounds for the unrestricted local map and for any restriction of its domain.

## Main statements

* `zeroOrderLocalExponents` and `mem_zeroOrderLocalExponents`: the triangular exponent set.
* `range_localConstraintAt_zeroOrder_le`: the local constraint image is supported on that set.
* `finrank_range_localConstraintAt_zeroOrder_le`: the triangular rank bound.

## References

* [DKT26]
* [BCPZZ26]
-/

@[expose] public section

open MvPolynomial PolynomialDifferential
open scoped BigOperators Pointwise

namespace ReedSolomon.HiddenDerivative

noncomputable section

variable {R : Type*} [CommRing R]

/-- The local exponent with `T` exponent `t` and `E` exponent `b` at derivative order zero. -/
def zeroOrderLocalExponent (t b : ℕ) : LocalVariable 0 →₀ ℕ :=
  Finsupp.single (localT 0) t + Finsupp.single (localE 0) b

/-- An exponent at derivative order zero is determined by its `T` and `E` exponents. -/
theorem zeroOrderLocalExponent_reconstruct (e : LocalVariable 0 →₀ ℕ) :
    zeroOrderLocalExponent (e (localT 0)) (e (localE 0)) = e := by
  ext v
  cases v with
  | none => simp [zeroOrderLocalExponent, localT, localE, localAux]
  | some v =>
    cases v with
    | none => simp [zeroOrderLocalExponent, localT, localE, localAux]
    | some j => exact Fin.elim0 j

/-- Exponents `T^t E^b` with `b ≤ t < m`. -/
def zeroOrderLocalExponents (m : ℕ) : Finset (LocalVariable 0 →₀ ℕ) :=
  Finset.univ.image fun p : Σ t : Fin m, Fin (t.val + 1) =>
    zeroOrderLocalExponent p.1.val p.2.val

/-- Membership in `zeroOrderLocalExponents m` is exactly `E ≤ T < m`. -/
theorem mem_zeroOrderLocalExponents (m : ℕ) (e : LocalVariable 0 →₀ ℕ) :
    e ∈ zeroOrderLocalExponents m ↔
      e (localE 0) ≤ e (localT 0) ∧ e (localT 0) < m := by
  constructor
  · intro he
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
    simpa [zeroOrderLocalExponent, localT, localE, localAux] using
      And.intro (Nat.le_of_lt_succ p.2.isLt) p.1.isLt
  · rintro ⟨hle, hlt⟩
    exact Finset.mem_image.mpr
      ⟨⟨⟨_, hlt⟩, ⟨_, Nat.lt_succ_of_le hle⟩⟩, Finset.mem_univ _,
        zeroOrderLocalExponent_reconstruct e⟩

/-- Every supported monomial of an order-zero local constraint has `E ≤ T < m`. -/
theorem localConstraintAt_zeroOrder_support (m : ℕ) (center received : R)
    (Q : DifferentialPolynomial R 0) (e : LocalVariable 0 →₀ ℕ)
    (he : e ∈ (localConstraintAt (d := 0) m center received Q).support) :
    e (localE 0) ≤ e (localT 0) ∧ e (localT 0) < m := by
  obtain ⟨hc, hs⟩ := mem_support_of_mem_support_localConstraintAt he
  refine ⟨localE_le_localT_of_mem_support center received Q hs, ?_⟩
  rw [localContactOrder_eq] at hc
  simpa [localT] using hc

/-- The order-zero constraint image is supported on the triangular exponent set. -/
theorem range_localConstraintAt_zeroOrder_le (m : ℕ) (center received : R) :
    (localConstraintAt (d := 0) m center received).range ≤
      MvPolynomial.restrictSupport R
        (zeroOrderLocalExponents m : Set (LocalVariable 0 →₀ ℕ)) := by
  rintro P ⟨Q, rfl⟩
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro e he
  exact (mem_zeroOrderLocalExponents m e).mpr
    (localConstraintAt_zeroOrder_support m center received Q e he)

/-- The range of the order-zero local constraint map is finite-dimensional. -/
theorem finite_range_localConstraintAt_zeroOrder {F : Type*} [Field F]
    (m : ℕ) (center received : F) :
    Module.Finite F (localConstraintAt (d := 0) m center received).range := by
  let s := zeroOrderLocalExponents m
  let V := MvPolynomial.restrictSupport F (s : Set (LocalVariable 0 →₀ ℕ))
  let b := MvPolynomial.basisRestrictSupport (R := F)
    (s : Set (LocalVariable 0 →₀ ℕ))
  let _ : Module.Finite F V := Module.Finite.of_basis b
  exact Submodule.finiteDimensional_of_le (range_localConstraintAt_zeroOrder_le m center received)

private theorem card_zeroOrderIndex (m : ℕ) :
    Fintype.card (Σ t : Fin m, Fin (t.val + 1)) = m * (m + 1) / 2 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [show (∑ t : Fin m, (t.val + 1)) = ∑ t ∈ Finset.range m, (t + 1) from
    Fin.sum_univ_eq_sum_range (fun t ↦ t + 1) m]
  have hsum := Finset.sum_range_id_mul_two m
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
    mul_one]
  have hm : m * (m - 1) + 2 * m = m * (m + 1) := by
    cases m with
    | zero => rfl
    | succ m => simp; ring
  omega

/-- The triangular exponent set has at most `m * (m + 1) / 2` elements. -/
theorem card_zeroOrderLocalExponents_le (m : ℕ) :
    (zeroOrderLocalExponents m).card ≤ m * (m + 1) / 2 := by
  exact (Finset.card_image_le).trans (by rw [Finset.card_univ, card_zeroOrderIndex])

/-- The order-zero local constraint map has rank at most `m * (m + 1) / 2`. -/
theorem finrank_range_localConstraintAt_zeroOrder_le {F : Type*} [Field F]
    (m : ℕ) (center received : F) :
    Module.finrank F (localConstraintAt (d := 0) m center received).range ≤
      m * (m + 1) / 2 := by
  let s := zeroOrderLocalExponents m
  let V := MvPolynomial.restrictSupport F (s : Set (LocalVariable 0 →₀ ℕ))
  let b := MvPolynomial.basisRestrictSupport (R := F)
    (s : Set (LocalVariable 0 →₀ ℕ))
  let _ : Module.Finite F V := Module.Finite.of_basis b
  let _ := finite_range_localConstraintAt_zeroOrder m center received
  have hdim : Module.finrank F V = s.card := by
    rw [← Fintype.card_coe]
    exact Module.finrank_eq_card_basis b
  exact (Submodule.finrank_mono (range_localConstraintAt_zeroOrder_le m center received)).trans
    (hdim.le.trans (card_zeroOrderLocalExponents_le m))

/-- Restricting the source of the order-zero local constraint map preserves the triangular rank
bound. -/
theorem finrank_range_localConstraintAt_zeroOrder_domRestrict_le {F : Type*} [Field F]
    (m : ℕ) (center received : F) (S : Submodule F (DifferentialPolynomial F 0)) :
    Module.finrank F ((localConstraintAt (d := 0) m center received).domRestrict S).range ≤
      m * (m + 1) / 2 := by
  let _ := finite_range_localConstraintAt_zeroOrder m center received
  have h : ((localConstraintAt (d := 0) m center received).domRestrict S).range ≤
      (localConstraintAt (d := 0) m center received).range := by
    rintro P ⟨Q, rfl⟩
    exact ⟨Q.val, rfl⟩
  exact (Submodule.finrank_mono h).trans
    (finrank_range_localConstraintAt_zeroOrder_le m center received)

end
end ReedSolomon.HiddenDerivative
