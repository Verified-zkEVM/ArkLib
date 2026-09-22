/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.BaseChange
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.FieldTheory.Finite.Extension

/-!
# Acceptance tests for changing the coefficient ring

Let `E₄ = FiniteField.Extension (ZMod 2) 2 2`, the field with four elements.

* Naturality: for `Q = X + Y₀` and `P = X + 1` over `ZMod 2`, both sides of
  `map_differentialSpecialization` are `1`, since `X + (X + 1) = 1` in characteristic two.
* Injectivity is needed in `jetDegree_map_eq`: `ℤ →+* ZMod 2` sends `2 * Y₀` to `0`.
* `JetDegreeCastsNeZero` fails for `Y₀ ^ 2` over `ZMod 2` and still fails over `E₄`.
* The cardinality comparison is strict for the zero equation with `D = 0`: `2` constant solutions
  over `ZMod 2` and `4` over `E₄`.
* For an algebra map of fields, the comparison with a finite extension, its form with an explicit
  bound, and its `Finset` form follow from the theorems. Mathlib's `FiniteField.Extension`
  supplies extensions of every large enough size with the base characteristic.
-/

open Polynomial PolynomialDifferential

private abbrev E₄ := FiniteField.Extension (ZMod 2) 2 2

/-- Mathlib's degree-two extension of `ZMod 2` has four elements and characteristic two. -/
example : Nat.card E₄ = 4 ∧ ringChar E₄ = 2 := by
  refine ⟨by rw [FiniteField.natCard_extension, Nat.card_zmod]; norm_num, ?_⟩
  rw [← Algebra.ringChar_eq (ZMod 2) E₄, ZMod.ringChar_zmod_n]

/-- For every bound there is a positive degree whose extension has
more elements than the bound, namely `Nat.log q bound + 1`. -/
example {k : Type*} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] [CharP k p] (bound : ℕ) :
    bound < Nat.card (FiniteField.Extension k p (Nat.log (Nat.card k) bound + 1)) := by
  rw [FiniteField.natCard_extension]
  exact Nat.lt_pow_succ_log_self Finite.one_lt_card bound

/-- An extension keeps the characteristic of its base field. -/
example {k : Type*} [Field k] [Finite k] (p n : ℕ) [Fact p.Prime] [CharP k p] [NeZero n] :
    CharP (FiniteField.Extension k p n) p :=
  charP_of_injective_algebraMap (algebraMap k _).injective p

/-- Naturality at `Q = X + Y₀` and `P = X + 1`: both sides are `1`. -/
example :
    let f := algebraMap (ZMod 2) E₄
    let Q : DifferentialPolynomial (ZMod 2) 0 :=
      MvPolynomial.X none + MvPolynomial.X (some 0)
    let P : (ZMod 2)[X] := X + 1
    (differentialSpecialization Q P).map f = 1 ∧
      (differentialSpecialization Q P).map f =
        differentialSpecialization (MvPolynomial.map f Q) (P.map f) := by
  intro f Q P
  refine ⟨?_, map_differentialSpecialization f Q P⟩
  have h2 : (X + (X + 1) : (ZMod 2)[X]) = 1 := by
    rw [← add_assoc, ← two_mul, show (2 : (ZMod 2)[X]) = C 2 from rfl,
      show (2 : ZMod 2) = 0 by decide, C_0, zero_mul, zero_add]
  simp [Q, P, differentialSpecialization, differentialSpecializationHom, h2]

/-- Injectivity is needed in `jetDegree_map_eq`: over `ℤ`, `2 * Y₀` has jet degree `1`, and its
image over `ZMod 2` is `0`, of jet degree `0`. -/
example :
    let Q : DifferentialPolynomial ℤ 0 := 2 * MvPolynomial.X (some 0)
    jetDegree Q 0 = 1 ∧ jetDegree (MvPolynomial.map (Int.castRingHom (ZMod 2)) Q) 0 = 0 := by
  intro Q
  have hmap : MvPolynomial.map (Int.castRingHom (ZMod 2)) Q = 0 := by
    simp [Q, CharTwo.two_eq_zero]
  refine ⟨?_, by rw [hmap]; simp [jetDegree]⟩
  simp only [Q, jetDegree]
  rw [show (2 : DifferentialPolynomial ℤ 0) = MvPolynomial.C 2 from rfl,
    MvPolynomial.degreeOf_C_mul _ _ (mem_nonZeroDivisors_of_ne_zero (by decide)),
    MvPolynomial.degreeOf_X_self]

/-- `JetDegreeCastsNeZero` for `Y₀ ^ 2` fails over `ZMod 2` because `(2 : ZMod 2) = 0`, and the
extension to `E₄` does not repair it. -/
example : ¬ JetDegreeCastsNeZero
    (MvPolynomial.map (algebraMap (ZMod 2) E₄)
      (MvPolynomial.X (some 0) ^ 2 : DifferentialPolynomial (ZMod 2) 0)) 0 := by
  rw [jetDegreeCastsNeZero_map_iff (algebraMap (ZMod 2) E₄).injective]
  intro h
  exact h 2 (by decide) (by simp [jetDegree]) (by decide)

/-- The zero equation has `q ^ (D + 1)` solutions of degree at most `D` over a finite field with
`q` elements. -/
private theorem natCard_boundedSolution_zero {F : Type*} [Field F] (d D : ℕ) :
    Nat.card (BoundedSolution (0 : DifferentialPolynomial F d) D) = Nat.card F ^ (D + 1) := by
  let e : BoundedSolution (0 : DifferentialPolynomial F d) D ≃ Polynomial.degreeLT F (D + 1) :=
    { toFun := fun P ↦ P.1
      invFun := fun P ↦ ⟨P, map_zero (differentialSpecializationHom (d := d) (P : F[X]))⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [Nat.card_congr (e.trans (Polynomial.degreeLTEquiv F (D + 1)).toEquiv), Nat.card_fun,
    Nat.card_fin]

/-- The comparison is strict for the zero equation with `D = 0`: `2 < 4`. -/
example :
    Nat.card (BoundedSolution (0 : DifferentialPolynomial (ZMod 2) 0) 0) = 2 ∧
      Nat.card (BoundedSolution (MvPolynomial.map (algebraMap (ZMod 2) E₄)
        (0 : DifferentialPolynomial (ZMod 2) 0)) 0) = 4 := by
  rw [map_zero, natCard_boundedSolution_zero, natCard_boundedSolution_zero,
    FiniteField.natCard_extension, Nat.card_zmod]
  exact ⟨rfl, rfl⟩

/-- Over a finite field the bounded solutions carry a `Fintype` instance through
`BoundedSolution.instFinite`. -/
example (Q : DifferentialPolynomial (ZMod 2) 1) : Nonempty (Fintype (BoundedSolution Q 3)) :=
  ⟨Fintype.ofFinite _⟩

/-- For an algebra map of fields with `E` finite, the root count over `F` is at most the root count
over `E`, and hence at most any bound on the latter. -/
example {F E : Type*} [Field F] [Field E] [Algebra F E] [Finite E] {d : ℕ}
    (Q : DifferentialPolynomial F d) (D bound : ℕ)
    (hbound : Nat.card (BoundedSolution (MvPolynomial.map (algebraMap F E) Q) D) ≤ bound) :
    Nat.card (BoundedSolution Q D) ≤
        Nat.card (BoundedSolution (MvPolynomial.map (algebraMap F E) Q) D) ∧
      Nat.card (BoundedSolution Q D) ≤ bound :=
  have h := BoundedSolution.natCard_le_natCard_map (algebraMap F E).injective Q D
  ⟨h, h.trans hbound⟩

/-- The `Finset` form of the comparison, without finiteness of either field. -/
example {F E : Type*} [Field F] [Field E] [Algebra F E] {d : ℕ}
    (Q : DifferentialPolynomial F d) (D : ℕ) (base : Finset (BoundedSolution Q D))
    (extension : Finset (BoundedSolution (MvPolynomial.map (algebraMap F E) Q) D))
    (hmaps : ∀ P ∈ base, P.map (algebraMap F E) ∈ extension) :
    base.card ≤ extension.card :=
  Finset.card_le_card_of_injOn _ hmaps
    (BoundedSolution.map_injective (algebraMap F E).injective).injOn
