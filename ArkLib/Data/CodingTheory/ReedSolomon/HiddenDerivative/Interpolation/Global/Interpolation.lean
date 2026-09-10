/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Justin Thaler
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.ConstraintMap
public import ArkLib.ToMathlib.LinearAlgebra.FiniteDimensional
/-!
# A nonzero global hidden-derivative interpolant

This file extracts a nonzero polynomial satisfying every local interpolation constraint from a
strict comparison between the exact interpolation dimension and the rank of the global constraint
map.  The rank comparison is an explicit premise: its eventual proof is the separate local-rank
and uniform-parameter analysis.

The global constraint map has finite-dimensional domain but an infinite-dimensional polynomial
codomain.  Accordingly, the proof uses rank-nullity with the map's finite-dimensional range and
does not assume that the codomain is finite-dimensional.
-/

@[expose] public section

open PolynomialDifferential


noncomputable section

open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

variable {F : Type*} [Field F]
variable {D A d m M W : ℕ}
variable {ι : Type*} [Fintype ι]

/-! ### From local ranks to the global rank -/

/-- Passing from exact interpolation-space elements to their canonical coefficients does not
change the range of a local constraint map. -/
theorem range_exact_coefficient_local_constraint_at_eq
    (hdD : d < D) (center received : F) :
    (exactCoefficientLocalConstraintAt (D := D) (A := A) (M := M) (W := W)
      hdD m center received).range =
      (exactLocalConstraintAt (D := D) (A := A) (M := M) (W := W)
        hdD m center received).range := by
  rw [exactCoefficientLocalConstraintAt, exactInterpolationCoefficientEvaluator,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]
  rfl

/-- The rank of the global product constraint map is at most the sum of the ranks of its local
components.  Each component rank is stated on `exactLocalConstraintAt`, which is the interface
supplied by the local-rank analysis. -/
theorem finrank_range_global_exact_coefficient_constraint_map_le_sum_local
    (hdD : d < D) (centers received : ι → F) :
    Module.finrank F
        (globalExactCoefficientConstraintMap (D := D) (A := A) (m := m) (M := M) (W := W)
          hdD centers received).range ≤
      ∑ i, Module.finrank F
        (exactLocalConstraintAt (D := D) (A := A) (M := M) (W := W)
          hdD m (centers i) (received i)).range := by
  let φ := fun i ↦
    exactCoefficientLocalConstraintAt (D := D) (A := A) (M := M) (W := W)
      hdD m (centers i) (received i)
  let Φ := globalExactCoefficientConstraintMap
    (D := D) (A := A) (m := m) (M := M) (W := W) hdD centers received
  let includeRange : Φ.range →ₗ[F] (∀ i, (φ i).range) := {
    toFun y i := ⟨y.1 i, by
      rcases y.2 with ⟨v, hv⟩
      refine ⟨v, ?_⟩
      rw [← hv]
      rfl⟩
    map_add' x y := by
      ext i
      rfl
    map_smul' a x := by
      ext i
      rfl
  }
  have hinjective : Function.Injective includeRange := by
    intro x y hxy
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun hxy i)
  calc
    Module.finrank F Φ.range ≤ Module.finrank F (∀ i, (φ i).range) :=
      LinearMap.finrank_le_finrank_of_injective hinjective
    _ = ∑ i, Module.finrank F (φ i).range := Module.finrank_pi_fintype F
    _ = ∑ i, Module.finrank F
        (exactLocalConstraintAt (D := D) (A := A) (M := M) (W := W)
          hdD m (centers i) (received i)).range := by
      apply Finset.sum_congr rfl
      intro i _
      change Module.finrank F
        (exactCoefficientLocalConstraintAt (D := D) (A := A) (M := M) (W := W)
          hdD m (centers i) (received i)).range = _
      rw [range_exact_coefficient_local_constraint_at_eq]

/-! ### Nonzero kernel extraction -/

/-- A strict rank-versus-dimension comparison gives a nonzero exact coefficient vector in the
kernel of the global constraint map.  This coefficient-level form is the direct rank-nullity
interface for later checked linear solvers. -/
theorem exists_nonzero_global_interpolation_coefficients_of_rank_lt
    (hdD : d < D) (centers received : ι → F)
    (hrank : Module.finrank F
        (globalExactCoefficientConstraintMap (D := D) (A := A) (m := m) (M := M) (W := W)
          hdD centers received).range <
      Module.finrank F (exactInterpolationSpace F D A d m M W hdD)) :
    ∃ v : ExactInterpolationCoefficients F D A d m M W hdD,
      v ≠ 0 ∧
        globalExactCoefficientConstraintMap (D := D) (A := A) (m := m) (M := M) (W := W)
          hdD centers received v = 0 := by
  let Φ := globalExactCoefficientConstraintMap
    (D := D) (A := A) (m := m) (M := M) (W := W) hdD centers received
  change Module.finrank F Φ.range <
    Module.finrank F (exactInterpolationSpace F D A d m M W hdD) at hrank
  have hcoeff : Module.finrank F
      (ExactInterpolationCoefficients F D A d m M W hdD) =
      Module.finrank F (exactInterpolationSpace F D A d m M W hdD) :=
    LinearEquiv.finrank_eq (exactInterpolationPolynomial hdD)
  have hnull := LinearMap.finrank_range_add_finrank_ker Φ
  have hkerpos : 0 < Module.finrank F Φ.ker := by
    rw [← hcoeff] at hrank
    omega
  have hker : Φ.ker ≠ ⊥ := by
    intro h
    rw [h] at hkerpos
    simp at hkerpos
  obtain ⟨v, hvker, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨v, hv0, LinearMap.mem_ker.mp hvker⟩

/-- If the exact global constraint rank is strictly smaller than the exact interpolation
dimension, there is a nonzero polynomial in the exact interpolation space satisfying every local
constraint. The rank premise separates linear-algebraic existence from the local rank estimates. -/
theorem exists_nonzero_global_interpolant_of_rank_lt
    (hdD : d < D) (centers received : ι → F)
    (hrank : Module.finrank F
        (globalExactCoefficientConstraintMap (D := D) (A := A) (m := m) (M := M) (W := W)
          hdD centers received).range <
      Module.finrank F (exactInterpolationSpace F D A d m M W hdD)) :
    ∃ Q : DifferentialPolynomial F d,
      Q ≠ 0 ∧
        Q ∈ exactInterpolationSpace F D A d m M W hdD ∧
        ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q := by
  obtain ⟨v, hv0, hvker⟩ :=
    exists_nonzero_global_interpolation_coefficients_of_rank_lt hdD centers received hrank
  let Qs : exactInterpolationSpace F D A d m M W hdD :=
    exactInterpolationPolynomial hdD v
  refine ⟨Qs, ?_, Qs.property, ?_⟩
  · intro hQ
    have hQs : Qs = 0 := by
      apply Subtype.ext
      simpa using hQ
    apply hv0
    have hrepr := congrArg
      (exactInterpolationRepr (F := F) (D := D) (A := A) (d := d) (m := m)
        (M := M) (W := W) hdD) hQs
    simpa [Qs] using hrepr
  · intro i
    have hi := congrFun hvker i
    simpa [SatisfiesLocalConstraints, exactCoefficientLocalConstraintAt,
      exactInterpolationCoefficientEvaluator, Qs] using hi

/-- Convenience form for rank certificates: an explicit upper bound on the exact global rank,
together with strict inequality from that bound to the exact interpolation dimension, produces
the global interpolant. -/
theorem exists_nonzero_global_interpolant_of_rank_le
    (hdD : d < D) (centers received : ι → F) (rankBound : ℕ)
    (hrank : Module.finrank F
        (globalExactCoefficientConstraintMap (D := D) (A := A) (m := m) (M := M) (W := W)
          hdD centers received).range ≤ rankBound)
    (hdim : rankBound <
      Module.finrank F (exactInterpolationSpace F D A d m M W hdD)) :
    ∃ Q : DifferentialPolynomial F d,
      Q ≠ 0 ∧
        Q ∈ exactInterpolationSpace F D A d m M W hdD ∧
        ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q := by
  exact exists_nonzero_global_interpolant_of_rank_lt hdD centers received (hrank.trans_lt hdim)

/-- A strict comparison between the sum of the actual local ranks and the exact interpolation
dimension is sufficient for global interpolation. -/
theorem exists_nonzero_global_interpolant_of_local_rank_sum_lt
    (hdD : d < D) (centers received : ι → F)
    (hdim : (∑ i, Module.finrank F
        (exactLocalConstraintAt (D := D) (A := A) (M := M) (W := W)
          hdD m (centers i) (received i)).range) <
      Module.finrank F (exactInterpolationSpace F D A d m M W hdD)) :
    ∃ Q : DifferentialPolynomial F d,
      Q ≠ 0 ∧
        Q ∈ exactInterpolationSpace F D A d m M W hdD ∧
        ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q := by
  exact exists_nonzero_global_interpolant_of_rank_le hdD centers received _
    (finrank_range_global_exact_coefficient_constraint_map_le_sum_local hdD centers received)
    hdim

/-- Per-index upper bounds on the exact local ranks produce a global interpolant when their sum
is strictly below the exact interpolation dimension. This combines pointwise rank estimates
with the global rank-nullity argument. -/
theorem exists_nonzero_global_interpolant_of_local_rank_bounds
    (hdD : d < D) (centers received : ι → F) (rankBound : ι → ℕ)
    (hrank : ∀ i, Module.finrank F
        (exactLocalConstraintAt (D := D) (A := A) (M := M) (W := W)
          hdD m (centers i) (received i)).range ≤ rankBound i)
    (hdim : (∑ i, rankBound i) <
      Module.finrank F (exactInterpolationSpace F D A d m M W hdD)) :
    ∃ Q : DifferentialPolynomial F d,
      Q ≠ 0 ∧
        Q ∈ exactInterpolationSpace F D A d m M W hdD ∧
        ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q := by
  apply exists_nonzero_global_interpolant_of_local_rank_sum_lt hdD centers received
  exact (Finset.sum_le_sum fun i _ ↦ hrank i).trans_lt hdim

/-- Uniform local rank bounds give the familiar `card × bound` global dimension criterion. -/
theorem exists_nonzero_global_interpolant_of_uniform_local_rank_bound
    (hdD : d < D) (centers received : ι → F) (rankBound : ℕ)
    (hrank : ∀ i, Module.finrank F
        (exactLocalConstraintAt (D := D) (A := A) (M := M) (W := W)
          hdD m (centers i) (received i)).range ≤ rankBound)
    (hdim : Fintype.card ι * rankBound <
      Module.finrank F (exactInterpolationSpace F D A d m M W hdD)) :
    ∃ Q : DifferentialPolynomial F d,
      Q ≠ 0 ∧
        Q ∈ exactInterpolationSpace F D A d m M W hdD ∧
        ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q := by
  apply exists_nonzero_global_interpolant_of_local_rank_bounds hdD centers received
    (fun _ ↦ rankBound) hrank
  simpa using hdim

end ReedSolomon.HiddenDerivative
