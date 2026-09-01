/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Extraction
import ArkLib.Data.Polynomial.RationalFunctions
import ArkLib.Data.Polynomial.Trivariate

/-!
# ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Agreement

Definitions and results for this component of ArkLib.
-/

namespace ProximityGap

open Polynomial Polynomial.Bivariate NNReal Finset Function ProbabilityTheory Code Trivariate
open scoped BigOperators LinearCode

universe u v w k l

section BCIKS20ProximityGapSection5

variable {F : Type} [Field F] [DecidableEq F] [Finite F]
variable {n : ℕ}
variable {m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}

open Trivariate in
open Bivariate in
/-- Claim 5.7 of [BCIKS20]. -/
lemma exists_factors_with_large_common_root_set (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
  ∃ R H, R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose ∧
    Irreducible H ∧ 0 < H.natDegree ∧ H ∣ Trivariate.evalAtX x₀ R ∧
    (Trivariate.evalAtX x₀ R).Separable ∧
    #(@Set.toFinset _ { z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ |
        letI Pz := Pz z.2
        (Trivariate.evalAtZ z.1 R).eval Pz = 0 ∧
        (Bivariate.evalX z.1 H).eval (Pz.eval x₀) = 0} (Fintype.ofFinite _))
    ≥ #(coeffs_of_close_proximity k ωs δ u₀ u₁) / Trivariate.degreeInY Q
    ∧ #(coeffs_of_close_proximity k ωs δ u₀ u₁) / Trivariate.degreeInY Q >
      2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q := by sorry

/-- Claim 5.7 establishes existens of a polynomial `R`. his is the extraction of this polynomial. -/
noncomputable def R (δ : ℚ) (x₀ : F) (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) : F[Z][X][Y] :=
 (exists_factors_with_large_common_root_set k δ x₀ h_gs).choose

/-- Claim 5.7 establishes existens of a polynomial `H`. This is the extraction of this polynomial.
-/
noncomputable def H (δ : ℚ) (x₀ : F) (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) : F[Z][X] :=
(exists_factors_with_large_common_root_set k δ x₀ h_gs).choose_spec.choose

/-- An important property of the polynomial `H` extracted from Claim 5.7 is that it is irreducible.
-/
lemma irreducible_H (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) : Irreducible (H k δ x₀ h_gs) :=
  (exists_factors_with_large_common_root_set k δ x₀ h_gs).choose_spec.choose_spec.2.1

/-- The factor `H` extracted from Claim 5.7 has positive degree in the `Y` variable, matching the
Appendix A hypotheses needed for the function field construction. -/
lemma natDegree_H_pos (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    0 < (H k δ x₀ h_gs).natDegree :=
  (exists_factors_with_large_common_root_set k δ x₀ h_gs).choose_spec.choose_spec.2.2.1

/-- The extracted `H` divides `R(x₀, Y, Z)`, as required for the Hensel setup in Claim A.2. -/
lemma H_dvd_evalX_R (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    H k δ x₀ h_gs ∣ Trivariate.evalAtX x₀ (R k δ x₀ h_gs) :=
  (exists_factors_with_large_common_root_set k δ x₀ h_gs).choose_spec.choose_spec.2.2.2.1

/-- The specialization `R(x₀, Y, Z)` is separable in `Y`, as required for Claim A.2. -/
lemma evalX_R_separable (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    (Trivariate.evalAtX x₀ (R k δ x₀ h_gs)).Separable :=
  (exists_factors_with_large_common_root_set k δ x₀ h_gs).choose_spec.choose_spec.2.2.2.2.1

open RationalFunctions.HenselNumerators in
/-- The Claim A.2 hypotheses satisfied by the `R,H` pair extracted from Claim 5.7.

Note for Claims 5.8/5.10: this supplies the *qualitative* half of Claim A.2 (existence and
uniqueness of the Hensel lift, regularity of the numerators), which is all that
`RationalFunctions.HenselNumerators.exists_hensel_numerator_sequence` and hence `alpha`/`gamma`
need. The **weight** bounds additionally require `2 ≤ Trivariate.degreeInY R`, and that side
condition cannot be obtained from Claim 5.7:

* `R` is an arbitrary irreducible factor of `Q` at that point, and `deg_Y R = 1` is precisely what
  §5 sets out to prove ("our goal will be to show that `Q` has a factor of the form `Y - P(X, Z)`
  … and in fact `R` is this factor", [BCIKS20] Appendix A preamble).
* The hypothesis is load-bearing, not an artefact of the formalization: for `deg_Y R = 1` the
  bound `Λ(ξ) ≤ (d-1)(D - dH + 1) = 0` of `xi_weight_le` is false.  Take
  `R = (1+Z)Y + 1 + ZX`, `x₀ = 0`, `H = (1+Z)Y + 1`; then `D = 2` and
  `ξ = W^{d-2}ζ = ζ = 1 + Z` has `Λ(ξ) = 1 > 0`.

So §5 has to case-split on `deg_Y R`.  In the `= 1` branch the Hensel machinery is not needed at
all: `R = R₁·Y + R₀` has the single rational root `γ = -R₀/R₁`, and Claim 5.9's conclusion should
be reached directly.  The `≥ 2` branch is the one that consumes the weight bounds. -/
lemma hensel_lift_hypotheses (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    Hypotheses x₀ (R k δ x₀ h_gs) (H k δ x₀ h_gs) :=
  ⟨H_dvd_evalX_R k h_gs, evalX_R_separable k h_gs⟩

open RationalFunctions.HenselNumerators in
/-- Claim 5.8 from [BCIKS20].
States that the approximate solution is actually a solution. This version of the claim is stated in
terms of coefficients. -/
lemma approximate_solution_is_exact_solution_coeffs
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) : ∀ t > k,
    alpha'
      x₀
      (R k δ x₀ h_gs)
      (irreducible_H k h_gs)
      (natDegree_H_pos k h_gs)
      (hensel_lift_hypotheses k h_gs)
      t
    =
    (0 : RationalFunctions.𝕃 (H k δ x₀ h_gs)) := by sorry

open RationalFunctions.HenselNumerators in
/-- Claim 5.8 from [BCIKS20].
States that the approximate solution is actually a solution.
This version is in terms of polynomials.
-/
lemma approximate_solution_is_exact_solution_coeffs'
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    gamma' x₀ (R k δ x₀ h_gs) (irreducible_H k h_gs) (natDegree_H_pos k h_gs)
        (hensel_lift_hypotheses k h_gs) =
        PowerSeries.mk (fun t =>
          if t > k
          then (0 : RationalFunctions.𝕃 (H k δ x₀ h_gs))
          else PowerSeries.coeff t
            (gamma'
              x₀
              (R k (x₀ := x₀) (δ := δ) h_gs)
              (irreducible_H k h_gs)
              (natDegree_H_pos k h_gs)
              (hensel_lift_hypotheses k h_gs))) := by
   sorry

open RationalFunctions.HenselNumerators in
/-- Claim 5.9 from [BCIKS20].
States that the solution `γ` is linear in the variable `Z`. -/
lemma solution_gamma_is_linear_in_Z
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
  ∃ (v₀ v₁ : F[X]),
    gamma' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
      (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
      (hensel_lift_hypotheses k (x₀ := x₀) (δ := δ) h_gs) =
        RationalFunctions.polyToPowerSeries𝕃 _
          (
            (Polynomial.map Polynomial.C v₀) +
            (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)
          ) := by sorry

/-- The linear represenation of the solution `γ` extracted from Claim 5.9. -/
noncomputable def P (δ : ℚ) (x₀ : F) (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) : F[Z][X] :=
  let v₀ := Classical.choose (solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs)
  let v₁ := Classical.choose
    (Classical.choose_spec <| solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs)
  (
    (Polynomial.map Polynomial.C v₀) +
    (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)
  )

open RationalFunctions.HenselNumerators in
/-- The extracted `P` from Claim 5.9 equals `γ`. -/
lemma gamma_eq_P (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    gamma' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
    (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
    (hensel_lift_hypotheses k (x₀ := x₀) (δ := δ) h_gs) =
  RationalFunctions.polyToPowerSeries𝕃 _
    (P k δ x₀ h_gs) :=
  Classical.choose_spec
    (Classical.choose_spec (solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs))

/-- The set `S'_x` from [BCIKS20] (just before Claim 5.10). The set of all `z ∈ S'` such that
`w(x,z)` matches `P_z(x)`. -/
noncomputable def matching_set_at_x
    (δ : ℚ)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (x : Fin n) : Finset F := @Set.toFinset _ {z : F | ∃ h : z ∈ matching_set k ωs δ u₀ u₁ h_gs,
    u₀ x + z * u₁ x =
      (Pz (matching_set_is_a_sub_of_coeffs_of_close_proximity k h_gs h)).eval (ωs x)}
    (Fintype.ofFinite _)

/-- Claim 5.10 of [BCIKS20].
Needed to prove Claim 5.9. This claim states that `γ(x) = w(x,Z)` if the cardinality `|S'_x|` is big
enough. -/
lemma solution_gamma_matches_word_if_subset_large
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    {x : Fin n}
    {D : ℕ}
    (hD : D ≥ Bivariate.totalDegree (H k δ x₀ h_gs))
    (hx : (matching_set_at_x k δ h_gs x).card >
      (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Trivariate.degreeInY <| R k δ x₀ h_gs)
        * D) : (P k δ x₀ h_gs).eval (Polynomial.C (ωs x)) =
      (Polynomial.C <| u₀ x) + u₁ x • Polynomial.X := by sorry

/-- Claim 5.11 from [BCIKS20].
There exists a set of points `{x₀,...,x_{k+1}}` such that the sets S_{x_j} satisfy the condition in
Claim 5.10. -/
lemma exists_points_with_large_matching_subset
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    {x : Fin n}
    {D : ℕ}
    (hD : D ≥ Bivariate.totalDegree (H k δ x₀ h_gs)) :
  ∃ Dtop : Finset (Fin n),
    Dtop.card = k + 1 ∧
    ∀ x ∈ Dtop,
      (matching_set_at_x k δ h_gs x).card >
        (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Trivariate.degreeInY <| R k δ x₀ h_gs)
        * D := by sorry

end BCIKS20ProximityGapSection5

end ProximityGap
