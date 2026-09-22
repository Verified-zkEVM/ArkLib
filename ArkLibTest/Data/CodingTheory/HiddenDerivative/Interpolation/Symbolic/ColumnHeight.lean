/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ColumnHeight
import ArkLibTest.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ReceivedCurve

/-!
# Column-height interpolation acceptance tests

The source-shaped received-line statement follows from the general one: for `n` points and a rank
bound `n * r` after `F[X] → RatFunc F` with `n * r * (h + 1) < ∑_j (h + 1 - y₀(j))`, there is a
primitive interpolant in the kernel of the constraint matrix with every coefficient of challenge
degree at most `h`, nonzero after every evaluation into a field. For a received curve, a column
with `ℓ * y₀ > h` gets the coefficient zero. With one point `(0, 1)`, the single column `Y₀` and
`h = 1`, the rank bound `s = 1` fails the surplus inequality and no nonzero interpolant exists,
so the surplus hypothesis is needed.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped Polynomial Matrix

namespace ColumnHeightTest

open ConstraintMatrixTest ReceivedCurveTest

/-- The received line column-height theorem in its source form. -/
example {F : Type*} [Field F] {d n N : ℕ} (m r h : ℕ) (centers f g : Fin n → F)
    (columns : Fin N → SourceColumn d) (hcolumns : Function.Injective columns)
    (hrank : ((localConstraintMatrix m (fun i => Polynomial.C (centers i))
      (fun i => receivedLine (f i) (g i)) columns).map (algebraMap F[X] (RatFunc F))).rank ≤
        n * r)
    (hheight : n * r * (h + 1) < ∑ j, (h + 1 - (columns j).y₀)) :
    ∃ v : Fin N → F[X], v ≠ 0 ∧
      localConstraintMatrix m (fun i => Polynomial.C (centers i))
        (fun i => receivedLine (f i) (g i)) columns *ᵥ v = 0 ∧
      (∀ j, (v j).natDegree ≤ h) ∧ Ideal.span (Set.range v) = ⊤ ∧
      (∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
        MvPolynomial.map (Polynomial.eval₂RingHom ι z) (SourceColumn.interpolant columns v) ≠
          0) ∧
      ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i)) (receivedLine (f i) (g i))
        (SourceColumn.interpolant columns v) := by
  obtain ⟨v, hv, hdeg, hspan, hmap, hloc⟩ :=
    exists_primitive_receivedLine_interpolant_of_column_height m h centers f g columns hcolumns
      (algebraMap F[X] (RatFunc F)) (IsFractionRing.injective F[X] (RatFunc F)) hrank hheight
  exact ⟨v, hv, (localConstraintMatrix_mulVec_eq_zero_iff m _ _ columns v).mpr hloc,
    fun j => Polynomial.natDegree_le_of_mem_degreeLT_succ
      (Polynomial.degreeLT_mono (Nat.sub_le _ _) (hdeg j)), hspan, fun ι z => hmap _, hloc⟩

/-- For a received curve, a column with `ℓ * y₀ > h` gets the coefficient zero. -/
example {F : Type*} [Field F] {d n N : ℕ} (m ℓ h : ℕ) (centers : Fin n → F)
    (w : Fin n → F[X]) (hw : ∀ i, (w i).natDegree ≤ ℓ) (columns : Fin N → SourceColumn d)
    (hcolumns : Function.Injective columns) {s : ℕ}
    (hrank : ((localConstraintMatrix m (fun i => Polynomial.C (centers i)) w columns).map
      (algebraMap F[X] (RatFunc F))).rank ≤ s)
    (hsurplus : s * (h + 1) < ∑ j, (h + 1 - ℓ * (columns j).y₀)) :
    ∃ v : Fin N → F[X], v ≠ 0 ∧ (∀ j, h < ℓ * (columns j).y₀ → v j = 0) ∧
      (∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
        MvPolynomial.map (Polynomial.eval₂RingHom ι z) (SourceColumn.interpolant columns v) ≠
          0) ∧
      ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i)) (w i)
        (SourceColumn.interpolant columns v) := by
  obtain ⟨v, hv, hdeg, -, hmap, hloc⟩ :=
    exists_primitive_interpolant_of_column_height m ℓ h centers w hw columns hcolumns
      (algebraMap F[X] (RatFunc F)) (IsFractionRing.injective F[X] (RatFunc F)) hrank hsurplus
  refine ⟨v, hv, fun j hj => ?_, fun ι z => hmap _, hloc⟩
  have := hdeg j
  rwa [Nat.sub_eq_zero_of_le hj, Polynomial.degreeLT_zero, Submodule.mem_bot] at this

/-- The surplus hypothesis is needed: with one point `(0, 1)`, the single column `Y₀` and
`h = 1`, the rank bound `s = 1` holds, the surplus `1 * (1 + 1) < 1 + 1 - 1 * 1` fails, and no
nonzero coefficient vector satisfies the constraints. -/
example : ((localConstraintMatrix 1 (fun _ : Fin 1 => Polynomial.C (0 : ℚ))
      (fun _ => receivedLine 1 0) colY).map (algebraMap ℚ[X] (RatFunc ℚ))).rank ≤ 1 ∧
    ¬ 1 * (1 + 1) < ∑ j, (1 + 1 - 1 * (colY j).y₀) ∧
    ¬ ∃ v : Fin 1 → ℚ[X], v ≠ 0 ∧ ∀ _ : Fin 1, SatisfiesLocalConstraints 1 (Polynomial.C 0)
      (receivedLine 1 0) (SourceColumn.interpolant colY v) :=
  ⟨(Matrix.rank_le_card_width _).trans_eq (Fintype.card_fin 1), by simp [colY],
    fun ⟨v, hv, hloc⟩ => hv (eq_zero_of_satisfiesLocalConstraints v hloc)⟩

end ColumnHeightTest
