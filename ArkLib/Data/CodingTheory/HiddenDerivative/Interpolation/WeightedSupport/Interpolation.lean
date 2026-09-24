/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.LocalRank
public import ArkLib.ToMathlib.LinearAlgebra.FiniteDimensional

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.Soundness
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Margin

/-!
# A nonzero interpolant from a weighted-support surplus

Over a field, the local constraint map of order `m` at each received point, restricted to the
weighted support space, has rank at most `localResidualCoordinateBudget d m W ⌈L / D⌉₊`
(`finrank_weightedSupportLocalConstraint_le`). The product of these maps over a finite index type
`ι` therefore has rank at most `card ι` times that budget. If this is below the number of
weighted-support exponents, which is the dimension of the space, some nonzero member of the space
satisfies every local constraint. The rank bound holds in every characteristic, and no
independence of the constraints is assumed. A quantitative dimension margin and a symbolic kernel
also give an interpolant with the jet and weighted-degree bounds used by the decoder.

## Main statements

* `weightedSupportGlobalConstraint`, `finrank_weightedSupportGlobalConstraint_le`: the product map
  and its rank bound.
* `exists_nonzero_weightedSupport_interpolant`: a nonzero interpolant in the weighted support
  space.
* `exists_nonzero_exact_interpolant_of_weightedSupport_surplus`: the same interpolant in the exact
  interpolation space, when `L ≤ m A` and `L ≤ D M`.
* `exists_weightedSupport_interpolant_of_fixed_margin`: a nonzero interpolant with degree bounds
  from a strict dimension margin.

## References

* [DKT26]
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] {D d m W : ℕ} {L : ℝ}

/-- The local constraint maps of order `m` at the points `(centers i, received i)`, as one linear
map from the weighted support space to `ι → LocalPolynomial F d`. -/
def weightedSupportGlobalConstraint (hD : 0 < D) (centers received : ι → F) :
    weightedSupportSpace F D d W L hD →ₗ[F] (ι → LocalPolynomial F d) :=
  LinearMap.pi fun i => weightedSupportLocalConstraint m hD (centers i) (received i)

/-- For `0 < d` and `0 < D`, the product map has rank at most
`card ι * localResidualCoordinateBudget d m W ⌈L / D⌉₊`. The codomain `LocalPolynomial F d` is
infinite-dimensional; only the ranges of the local maps are finite-dimensional. -/
theorem finrank_weightedSupportGlobalConstraint_le (hd : 0 < d) (hD : 0 < D)
    (centers received : ι → F) :
    Module.finrank F (LinearMap.range (weightedSupportGlobalConstraint (d := d) (m := m)
      (W := W) (L := L) hD centers received)) ≤
        Fintype.card ι * localResidualCoordinateBudget d m W ⌈L / D⌉₊ := by
  refine (LinearMap.finrank_range_pi_le_sum _).trans ?_
  refine (Finset.sum_le_sum fun i _ => finrank_weightedSupportLocalConstraint_le hd hD
    (centers i) (received i)).trans ?_
  simp

/-- For `0 < d` and `0 < D`, if `card ι * localResidualCoordinateBudget d m W ⌈L / D⌉₊` is less
than the number of weighted-support exponents, then some nonzero `Q` in the weighted support space
satisfies the local constraints of order `m` at every `(centers i, received i)`. The
hypothesis `hdim` is the dimension surplus: the space has dimension equal to the number of
exponents (`finrank_weightedSupportSpace_eq_card`), and the product map has smaller rank. -/
theorem exists_nonzero_weightedSupport_interpolant (hd : 0 < d) (hD : 0 < D)
    (centers received : ι → F)
    (hdim : Fintype.card ι * localResidualCoordinateBudget d m W ⌈L / D⌉₊ <
      (weightedSupportExponents D d W L hD).card) :
    ∃ Q : DifferentialPolynomial F d, Q ≠ 0 ∧ Q ∈ weightedSupportSpace F D d W L hD ∧
      ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q := by
  obtain ⟨v, hv0, hv⟩ := LinearMap.exists_ne_zero_map_eq_zero_of_finrank_range_lt
    ((finrank_weightedSupportGlobalConstraint_le (m := m) hd hD centers received).trans_lt
      (by simpa [finrank_weightedSupportSpace_eq_card hD] using hdim))
  exact ⟨v.1, fun h => hv0 (Subtype.ext h), v.2, fun i => congrFun hv i⟩

/-- Under the hypotheses of `exists_nonzero_weightedSupport_interpolant`, and `d < D`,
`L ≤ m A` and `L ≤ D M`, the nonzero interpolant lies in `exactInterpolationSpace F D A d m M W`.
The two cutoff hypotheses are those of `weightedSupportSpace_le_exactInterpolationSpace`: the
first bounds the specialization weight, the second the first-derivative exponent. -/
theorem exists_nonzero_exact_interpolant_of_weightedSupport_surplus {A M : ℕ}
    (hd : 0 < d) (hD : 0 < D) (hdD : d < D) (centers received : ι → F)
    (hL : L ≤ (m * A : ℕ)) (hcap : L ≤ (D : ℝ) * M)
    (hdim : Fintype.card ι * localResidualCoordinateBudget d m W ⌈L / D⌉₊ <
      (weightedSupportExponents D d W L hD).card) :
    ∃ Q : DifferentialPolynomial F d, Q ≠ 0 ∧ Q ∈ exactInterpolationSpace F D A d m M W hdD ∧
      ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q := by
  obtain ⟨Q, hQ0, hQ, hQlocal⟩ :=
    exists_nonzero_weightedSupport_interpolant hd hD centers received hdim
  exact ⟨Q, hQ0, weightedSupportSpace_le_exactInterpolationSpace hD hdD hL hcap hQ, hQlocal⟩

open Polynomial
open SymbolicReceivedInterpolation
open WeightedSupportParameters

/-- A strict dimension margin gives a nonzero interpolant in the weighted-support space that
satisfies all local constraints and both decoder degree bounds. -/
theorem exists_weightedSupport_interpolant_of_fixed_margin
    {n A : ℕ} {g : ℝ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hD : 0 < D) (hm : 0 < m) (hA : 0 < A) (hg : g ≤ 1)
    (hcut : (D : ℝ) * m * (1 + g) ≤ (m * A : ℕ))
    (hmargin : (543 / 500 : ℝ) * n *
      Module.finrank F (LinearMap.range
        (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
          (L := (D : ℝ) * m * (1 + g)) m hD 0 0)) <
      Module.finrank F (weightedSupportSpace F D d W
        ((D : ℝ) * m * (1 + g)) hD)) :
    ∃ Q : DifferentialPolynomial F d,
      Q ≠ 0 ∧
      Q ∈ weightedSupportSpace F D d W ((D : ℝ) * m * (1 + g)) hD ∧
      (∀ i, SatisfiesLocalConstraints m (domain i) (received i) Q) ∧
      jetTotalDegree Q < 2 * m ∧
      differentialWeightedDegree D Q < m * A := by
  let ν := 2 * m - 1
  have hν : 0 < ν := by dsimp only [ν]; omega
  have hy₀ : ∀ u, WeightedSupportEligible D d W
      ((D : ℝ) * m * (1 + g)) u → u (some 0) ≤ ν := by
    intro u hu
    exact y₀_le_two_mul_sub_one_of_eligible hD hg hu
  obtain ⟨v, _hv, _hkernel, _hdegree, _hheight, _hprimitive, hnozero,
      hconstraints, hsupport⟩ :=
    exists_symbolic_weightedSupport_interpolant_of_fixed_margin
      hD hν (fun i ↦ domain i) received (fun _ ↦ 0) hy₀ hmargin
  let columns := weightedSupportColumns
    (d := d) (W := W) (L := (D : ℝ) * m * (1 + g)) hD
  let φ : F[X] →+* F := Polynomial.eval₂RingHom (RingHom.id F) 0
  let Q : DifferentialPolynomial F d :=
    MvPolynomial.map φ (SourceColumn.interpolant columns v)
  have hQ0 : Q ≠ 0 := by
    simpa only [Q, φ] using hnozero (RingHom.id F) 0
  have hQsupport :
      Q ∈ weightedSupportSpace F D d W ((D : ℝ) * m * (1 + g)) hD := by
    simpa only [Q, φ, columns] using
      map_interpolant_mem_weightedSupportSpace hD columns hsupport v (RingHom.id F) 0
  have hQlocal : ∀ i, SatisfiesLocalConstraints m (domain i) (received i) Q := by
    intro i
    have hi := SatisfiesLocalConstraints.map φ m (Polynomial.C (domain i))
      (receivedLine (received i) 0) (SourceColumn.interpolant columns v) (hconstraints i)
    change SatisfiesLocalConstraints m
      (φ (Polynomial.C (domain i))) (φ (receivedLine (received i) 0)) Q at hi
    convert hi using 1 <;> simp [φ, receivedLine]
  have hdecoder := decoder_bounds_of_mem_weightedSupportSpace hm hA
    (by
      have hnonneg : (0 : ℝ) ≤ (D : ℝ) * m := by positivity
      calc
        (D : ℝ) * m * (1 + g) ≤ (D : ℝ) * m * 2 :=
          mul_le_mul_of_nonneg_left (by linarith) hnonneg
        _ = (D : ℝ) * (2 * m) := by ring)
    hcut hQsupport
  exact ⟨Q, hQ0, hQsupport, hQlocal, hdecoder.1, hdecoder.2⟩

end ReedSolomon.HiddenDerivative
