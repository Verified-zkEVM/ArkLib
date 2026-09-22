/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ReceivedCurve
import ArkLibTest.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ConstraintMatrix
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Received-curve interpolation acceptance tests

The source-shaped statements follow from the general ones: for `n` points and a rank bound
`n * r₀` after `F[X] → RatFunc F`, a received line has a primitive interpolant of challenge degree
at most `n * r₀ * ν / (N - n * r₀)` in the kernel of the constraint matrix, nonzero after every
evaluation `eval₂ ι z` into a field; for a received curve the rank bound may be stated on the
supported rows. With one point `(0, 1)` and the single column `Y₀`, the rank bound `s = 1` holds
but only the zero interpolant satisfies the constraints, so `s < card κ` is needed.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped Polynomial Matrix

namespace ReceivedCurveTest

open ConstraintMatrixTest

/-- The received line `f + Z g` evaluates to `f + z g`. -/
example (f g z : ℚ) : (receivedLine f g).eval z = f + z * g := by
  rw [receivedLine, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_C]

/-- The received line theorem in its source form: rank bound `n * r₀` after `F[X] → RatFunc F`,
kernel conjunct, and nonvanishing after every evaluation into a field. -/
example {F : Type*} [Field F] {d n N : ℕ} (m ν r₀ : ℕ) (centers f g : Fin n → F)
    (columns : Fin N → SourceColumn d) (hcolumns : Function.Injective columns)
    (hy₀ : ∀ j, (columns j).y₀ ≤ ν)
    (hrank : ((localConstraintMatrix m (fun i => Polynomial.C (centers i))
      (fun i => receivedLine (f i) (g i)) columns).map (algebraMap F[X] (RatFunc F))).rank ≤
        n * r₀)
    (hN : n * r₀ < N) :
    ∃ v : Fin N → F[X], v ≠ 0 ∧
      localConstraintMatrix m (fun i => Polynomial.C (centers i))
        (fun i => receivedLine (f i) (g i)) columns *ᵥ v = 0 ∧
      (∀ j, (v j).natDegree ≤ n * r₀ * ν / (N - n * r₀)) ∧
      Ideal.span (Set.range v) = ⊤ ∧
      (∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
        MvPolynomial.map (Polynomial.eval₂RingHom ι z) (SourceColumn.interpolant columns v) ≠
          0) ∧
      ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i)) (receivedLine (f i) (g i))
        (SourceColumn.interpolant columns v) := by
  obtain ⟨v, hv, hdeg, hspan, hmap, hloc⟩ :=
    exists_primitive_receivedLine_interpolant_of_rank_le m ν centers f g columns hcolumns hy₀
      (algebraMap F[X] (RatFunc F)) (IsFractionRing.injective F[X] (RatFunc F)) hrank
      (by simpa using hN)
  exact ⟨v, hv, (localConstraintMatrix_mulVec_eq_zero_iff m _ _ columns v).mpr hloc,
    by simpa using hdeg, hspan, fun ι z => hmap _, hloc⟩

/-- The received curve theorem in its source form, with the rank bound on the supported rows. -/
example {F : Type*} [Field F] {d n N : ℕ} (m ℓ ν r : ℕ) (centers : Fin n → F)
    (w : Fin n → F[X]) (hw : ∀ i, (w i).natDegree ≤ ℓ) (columns : Fin N → SourceColumn d)
    (hcolumns : Function.Injective columns) (hy₀ : ∀ j, (columns j).y₀ ≤ ν)
    (hrank : ((supportedLocalConstraintMatrix m (fun i => Polynomial.C (centers i)) w
      columns).map (algebraMap F[X] (RatFunc F))).rank ≤ r) (hrN : r < N) :
    ∃ v : Fin N → F[X], v ≠ 0 ∧
      (∀ j, (v j).natDegree ≤ r * (ℓ * ν) / (N - r)) ∧
      Ideal.span (Set.range v) = ⊤ ∧
      (∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
        MvPolynomial.map (Polynomial.eval₂RingHom ι z) (SourceColumn.interpolant columns v) ≠
          0) ∧
      ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i)) (w i)
        (SourceColumn.interpolant columns v) := by
  obtain ⟨v, hv, hdeg, hspan, hmap, hloc⟩ :=
    exists_primitive_interpolant_of_rank_le m ℓ ν centers w hw columns hcolumns hy₀
      (algebraMap F[X] (RatFunc F)) (IsFractionRing.injective F[X] (RatFunc F))
      ((rank_map_supportedLocalConstraintMatrix _ m _ w columns).symm.le.trans hrank)
      (by simpa using hrN)
  exact ⟨v, hv, by simpa using hdeg, hspan, fun ι z => hmap _, hloc⟩

/-- With one point `(0, 1)` and the single column `Y₀`, only the zero coefficient vector
satisfies the local constraints of multiplicity `1`. -/
theorem eq_zero_of_satisfiesLocalConstraints (v : Fin 1 → ℚ[X])
    (hv : ∀ i, SatisfiesLocalConstraints 1 ((fun _ : Fin 1 => Polynomial.C (0 : ℚ)) i)
      ((fun _ : Fin 1 => receivedLine (1 : ℚ) 0) i) (SourceColumn.interpolant colY v)) :
    v = 0 := by
  have h := congrFun ((localConstraintMatrix_mulVec_eq_zero_iff 1
    (fun _ : Fin 1 => Polynomial.C (0 : ℚ)) (fun _ => receivedLine (1 : ℚ) 0) colY v).mpr hv)
    row₀
  have hr : receivedLine (1 : ℚ) 0 = 1 := by simp [receivedLine]
  simp only [map_zero, hr, Matrix.mulVec, dotProduct, Fin.sum_univ_one, entry_row₀, one_mul,
    Pi.zero_apply] at h
  funext j
  fin_cases j
  exact h

/-- `s < card κ` is needed: with one point `(0, 1)` and the single column `Y₀`, the rank bound
`s = 1 = card κ` holds, but no nonzero coefficient vector satisfies the constraints. -/
example : ((localConstraintMatrix 1 (fun _ : Fin 1 => Polynomial.C (0 : ℚ))
      (fun _ => receivedLine 1 0) colY).map (algebraMap ℚ[X] (RatFunc ℚ))).rank ≤ 1 ∧
    ¬ ∃ v : Fin 1 → ℚ[X], v ≠ 0 ∧ ∀ _ : Fin 1, SatisfiesLocalConstraints 1 (Polynomial.C 0)
      (receivedLine 1 0) (SourceColumn.interpolant colY v) :=
  ⟨(Matrix.rank_le_card_width _).trans_eq (Fintype.card_fin 1),
    fun ⟨v, hv, hloc⟩ => hv (eq_zero_of_satisfiesLocalConstraints v hloc)⟩

end ReceivedCurveTest
