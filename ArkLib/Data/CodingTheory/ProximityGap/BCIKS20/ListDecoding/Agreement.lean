/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Extraction
import ArkLib.Data.Polynomial.RationalFunctions
import ArkLib.Data.Polynomial.Trivariate

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
/-- The technical inputs to Claim 5.7 that are not contained in `ModifiedGuruswami`.

`regime` restores the standing §5 numerical assumptions.  `specializations_separable` says that
the chosen `x₀` is good in the sense of Claim 5.6, at the fraction-field level actually used by
Hensel lifting.  `positive_pair_for_every_z` is the content-factor bridge required by the present
Claim 5.7 cardinality: every `z ∈ S` must be covered by a positive-`Y`-degree pair.  A future proof
may instead remove the finite content-root exceptional set and weaken the cardinality conclusion;
until that loss is quantified, keeping the bridge explicit is preferable to deriving it from the
stronger and unintended ring-level `Polynomial.Separable` predicate. -/
structure Claim57Assumptions (x₀ : F) (δ : ℚ)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) : Prop where
  regime : Section5Regime m n k ωs Q u₀ u₁ δ h_gs
  specializations_separable : ∀ R : F[Z][X][Y],
    R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
      (u₀ := u₀) (u₁ := u₁) h_gs →
    ((Bivariate.evalX (Polynomial.C x₀) R).map
      (ToRatFunc.univPolyHom (F := F))).Separable
  positive_pair_for_every_z :
    ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∃ R H,
        (R, H) ∈ pg_positiveDegreePairs (m := m) (n := n) (k := k) (ωs := ωs)
          (Q := Q) (u₀ := u₀) (u₁ := u₁) x₀ h_gs ∧
        let P : F[X] := Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
        (pg_eval_on_Z (F := F) R z.1).eval P = 0 ∧
          (Bivariate.evalX z.1 H).eval (P.eval x₀) = 0

/-- Claim 5.7 of [BCIKS20].

The separability conjunct is separability of `R(x₀,·,Z)` **over the fraction field** `F(Z)`, which
is what the paper means by "separable in `Y`" and exactly what the Hensel setup consumes
(`RationalFunctions.HenselNumerators.Hypotheses`).  It is not `Polynomial.Separable` over `F[Z]`:
that is `IsCoprime f f.derivative` in the ambient ring, so over a non-field base it forces the
discriminant to be a unit, and it fails for genuine factors at legitimate Claim 5.6 points — over
`𝔽₅`, `R = Z·Y² + Z·Y + (Z + X)` at `x₀ = 0` gives `R(0, Y, Z) = Z·(Y² + Y + 1)`, which shares the
factor `Z` with its `Y`-derivative.

The content-factor and good-specialization obligations are supplied explicitly by
`Claim57Assumptions`; see its docstring. -/
lemma exists_factors_with_large_common_root_set (δ : ℚ) (x₀ : F)
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  (h57 : Claim57Assumptions k x₀ δ h_gs) :
  ∃ R H,
    R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
      (u₀ := u₀) (u₁ := u₁) h_gs ∧
    H ∈ pg_positiveDegreeFactors (Bivariate.evalX (Polynomial.C x₀) R) ∧
    ((Bivariate.evalX (Polynomial.C x₀) R).map
      (ToRatFunc.univPolyHom (F := F))).Separable ∧
    (#(@Set.toFinset _ { z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ |
        letI Pz := Pz z.2
        (Trivariate.eval_on_Z R z.1).eval Pz = 0 ∧
        (Bivariate.evalX z.1 H).eval (Pz.eval x₀) = 0} (Fintype.ofFinite _)) : ℝ)
      ≥ (#(coeffs_of_close_proximity k ωs δ u₀ u₁) : ℝ) / Bivariate.natDegreeY Q ∧
    (#(coeffs_of_close_proximity k ωs δ u₀ u₁) : ℝ) / Bivariate.natDegreeY Q >
      2 * D_Y Q * (D_Y Q + 1) * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q := by sorry

/-- The polynomial `R` extracted from Claim 5.7. -/
noncomputable def R (δ : ℚ) (x₀ : F) (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (h57 : Claim57Assumptions k x₀ δ h_gs) : F[Z][X][Y] :=
 (exists_factors_with_large_common_root_set k δ x₀ h_gs h57).choose

/-- The polynomial `H` extracted from Claim 5.7. -/
noncomputable def H (δ : ℚ) (x₀ : F) (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (h57 : Claim57Assumptions k x₀ δ h_gs) : F[Z][X] :=
(exists_factors_with_large_common_root_set k δ x₀ h_gs h57).choose_spec.choose

/-- An important property of the polynomial `H` extracted from Claim 5.7 is that it is irreducible.
-/
lemma irreducible_H (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (h57 : Claim57Assumptions k x₀ δ h_gs) : Irreducible (H k δ x₀ h_gs h57) := by
  have hmem :=
    (exists_factors_with_large_common_root_set k δ x₀ h_gs h57).choose_spec.choose_spec.2.1
  simp only [pg_positiveDegreeFactors] at hmem
  exact UniqueFactorizationMonoid.irreducible_of_normalized_factor
    (a := Bivariate.evalX (Polynomial.C x₀) (R k δ x₀ h_gs h57))
    (H k δ x₀ h_gs h57) (Multiset.mem_filter.mp hmem).1

/-- The factor `H` extracted from Claim 5.7 has positive degree in the `Y` variable, matching the
Appendix A hypotheses needed for the function field construction. -/
lemma natDegree_H_pos (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (h57 : Claim57Assumptions k x₀ δ h_gs) :
    0 < (H k δ x₀ h_gs h57).natDegree :=
  pg_natDegree_pos_of_mem_positiveDegreeFactors
    (exists_factors_with_large_common_root_set k δ x₀ h_gs h57).choose_spec.choose_spec.2.1

/-- The extracted `H` divides `R(x₀, Y, Z)`, as required for the Hensel setup in Claim A.2. -/
lemma H_dvd_evalX_R (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (h57 : Claim57Assumptions k x₀ δ h_gs) :
    H k δ x₀ h_gs h57 ∣ Bivariate.evalX (Polynomial.C x₀) (R k δ x₀ h_gs h57) :=
  by
    apply UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors
    have hmem :=
      (exists_factors_with_large_common_root_set k δ x₀ h_gs h57).choose_spec.choose_spec.2.1
    simp only [pg_positiveDegreeFactors] at hmem
    exact (Multiset.mem_filter.mp hmem).1

/-- The specialization `R(x₀, Y, Z)` is separable in `Y` over `F(Z)`, as required for Claim A.2. -/
lemma evalX_R_separable_over_ratFunc (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (h57 : Claim57Assumptions k x₀ δ h_gs) :
    ((Bivariate.evalX (Polynomial.C x₀) (R k δ x₀ h_gs h57)).map
      (ToRatFunc.univPolyHom (F := F))).Separable :=
  (exists_factors_with_large_common_root_set k δ x₀ h_gs h57).choose_spec.choose_spec.2.2.1

open RationalFunctions.HenselNumerators in
/-- The Claim A.2 hypotheses satisfied by the `R,H` pair extracted from Claim 5.7.

Note for Claims 5.8/5.10: this supplies the *qualitative* half of Claim A.2 (existence and
uniqueness of the Hensel lift, regularity of the numerators), which is all that
`RationalFunctions.HenselNumerators.exists_hensel_numerator_sequence` and hence `alpha`/`gamma`
need.  The **weight** bounds additionally require `2 ≤ Bivariate.natDegreeY R`, and that side
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
lemma hensel_lift_hypotheses (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (h57 : Claim57Assumptions k x₀ δ h_gs) :
    Hypotheses x₀ (R k δ x₀ h_gs h57) (H k δ x₀ h_gs h57) :=
  ⟨H_dvd_evalX_R k h_gs h57, evalX_R_separable_over_ratFunc k h_gs h57⟩

open RationalFunctions.HenselNumerators in
/-- Claim 5.8 from [BCIKS20].
States that the approximate solution is actually a solution. This version of the claim is stated in
terms of coefficients.

This is the branch of the §5 argument that genuinely needs the Appendix A weight machinery.  If
the selected factor has `Y`-degree one, the desired rational root is available directly and this
branch should be bypassed.  The two total-degree hypotheses record the factor bounds required by
the weight lemmas; they are not consequences of `ModifiedGuruswami`'s interface alone. -/
lemma approximate_solution_is_exact_solution_coeffs
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (h57 : Claim57Assumptions k x₀ δ h_gs)
    (_hR_degree_at_least_two : 2 ≤ Bivariate.natDegreeY (R k δ x₀ h_gs h57))
    (_hR_totalDegree_le : Bivariate.totalDegree (R k δ x₀ h_gs h57) ≤ D_YZ Q)
    (_hH_totalDegree_le : Bivariate.totalDegree (H k δ x₀ h_gs h57) ≤ D_YZ Q)
    : ∀ t > k,
    alpha'
      x₀
      (R k δ x₀ h_gs h57)
      (irreducible_H k h_gs h57)
      (natDegree_H_pos k h_gs h57)
      (hensel_lift_hypotheses k h_gs h57)
      t
    =
    (0 : RationalFunctions.𝕃 (H k δ x₀ h_gs h57))
    := by sorry

open RationalFunctions.HenselNumerators in
/-- Claim 5.8 from [BCIKS20].
States that the approximate solution is actually a solution.
This version is in terms of polynomials.
-/
lemma approximate_solution_is_exact_solution_coeffs'
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (h57 : Claim57Assumptions k x₀ δ h_gs)
    (_hR_degree_at_least_two : 2 ≤ Bivariate.natDegreeY (R k δ x₀ h_gs h57))
    (_hR_totalDegree_le : Bivariate.totalDegree (R k δ x₀ h_gs h57) ≤ D_YZ Q)
    (_hH_totalDegree_le : Bivariate.totalDegree (H k δ x₀ h_gs h57) ≤ D_YZ Q)
    :
    gamma' x₀ (R k δ x₀ h_gs h57) (irreducible_H k h_gs h57)
        (natDegree_H_pos k h_gs h57) (hensel_lift_hypotheses k h_gs h57) =
        PowerSeries.mk (fun t =>
          if t > k
          then (0 : RationalFunctions.𝕃 (H k δ x₀ h_gs h57))
          else PowerSeries.coeff t
            (gamma'
              x₀
              (R k (x₀ := x₀) (δ := δ) h_gs h57)
              (irreducible_H k h_gs h57)
              (natDegree_H_pos k h_gs h57)
              (hensel_lift_hypotheses k h_gs h57))) := by
   sorry

open RationalFunctions.HenselNumerators in
/-- Claim 5.9 from [BCIKS20].
States that the solution `γ` is linear in the variable `Z`. -/
lemma solution_gamma_is_linear_in_Z
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (h57 : Claim57Assumptions k x₀ δ h_gs)
    (_hR_degree_at_least_two : 2 ≤ Bivariate.natDegreeY (R k δ x₀ h_gs h57))
    (_hR_totalDegree_le : Bivariate.totalDegree (R k δ x₀ h_gs h57) ≤ D_YZ Q)
    (_hH_totalDegree_le : Bivariate.totalDegree (H k δ x₀ h_gs h57) ≤ D_YZ Q)
    :
  ∃ (v₀ v₁ : F[X]),
    gamma' x₀ (R k δ x₀ h_gs h57)
      (irreducible_H k (x₀ := x₀) (δ := δ) h_gs h57)
      (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs h57)
      (hensel_lift_hypotheses k (x₀ := x₀) (δ := δ) h_gs h57) =
        RationalFunctions.polyToPowerSeries𝕃 _
          (
            (Polynomial.map Polynomial.C v₀) +
            (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)
          ) := by sorry

/-- The linear representation of the solution `γ` extracted from Claim 5.9. -/
noncomputable def P (δ : ℚ) (x₀ : F) (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (h57 : Claim57Assumptions k x₀ δ h_gs)
    (hR_degree_at_least_two : 2 ≤ Bivariate.natDegreeY (R k δ x₀ h_gs h57))
    (hR_totalDegree_le : Bivariate.totalDegree (R k δ x₀ h_gs h57) ≤ D_YZ Q)
    (hH_totalDegree_le : Bivariate.totalDegree (H k δ x₀ h_gs h57) ≤ D_YZ Q) : F[Z][X] :=
  let v₀ := Classical.choose
    (solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs h57
      hR_degree_at_least_two hR_totalDegree_le hH_totalDegree_le)
  let v₁ := Classical.choose
    (Classical.choose_spec <|
      solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs h57
        hR_degree_at_least_two hR_totalDegree_le hH_totalDegree_le)
  (
    (Polynomial.map Polynomial.C v₀) +
    (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)
  )

open RationalFunctions.HenselNumerators in
/-- The extracted `P` from Claim 5.9 equals `γ`. -/
lemma gamma_eq_P (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (h57 : Claim57Assumptions k x₀ δ h_gs)
    (hR_degree_at_least_two : 2 ≤ Bivariate.natDegreeY (R k δ x₀ h_gs h57))
    (hR_totalDegree_le : Bivariate.totalDegree (R k δ x₀ h_gs h57) ≤ D_YZ Q)
    (hH_totalDegree_le : Bivariate.totalDegree (H k δ x₀ h_gs h57) ≤ D_YZ Q) :
  gamma' x₀ (R k δ x₀ h_gs h57)
    (irreducible_H k (x₀ := x₀) (δ := δ) h_gs h57)
    (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs h57)
    (hensel_lift_hypotheses k (x₀ := x₀) (δ := δ) h_gs h57) =
  RationalFunctions.polyToPowerSeries𝕃 _
    (P k δ x₀ h_gs h57 hR_degree_at_least_two hR_totalDegree_le hH_totalDegree_le) :=
  Classical.choose_spec
    (Classical.choose_spec
      (solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs h57
        hR_degree_at_least_two hR_totalDegree_le hH_totalDegree_le))

/-- The set `S'_x` from [BCIKS20] (just before Claim 5.10). The set of all `z ∈ S'` such that
`w(x,z)` matches `P_z(x)`. -/
noncomputable def matching_set_at_x
    (δ : ℚ)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (h57 : Claim57Assumptions k x₀ δ h_gs)
    (x : Fin n)
    : Finset F := @Set.toFinset _ {z : F |
      ∃ h : z ∈ matching_set k ωs δ u₀ u₁ h_gs h57.regime,
    u₀ x + z * u₁ x =
      (Pz (matching_set_is_a_sub_of_coeffs_of_close_proximity k h_gs h57.regime h)).eval (ωs x)}
    (Fintype.ofFinite _)

/-- Claim 5.10 of [BCIKS20].
Needed to prove Claim 5.9. This claim states that `γ(x) = w(x,Z)` if the cardinality `|S'_x|` is big
enough.

The threshold carries `dY + 1` where the paper writes `dY`.  This is the conservative bound
currently supplied by the repaired Appendix A estimate: the paper reaches
`|S'_x| > (2k+1)·dH·dY·D ≥ dH·Λ(β̃(x))` from Claim A.2's `Λ(βₜ) ≤ (2t+1)·dY·D`, and that bound is
short as a proof after adding the content charge.  The available proved bound is
`(2t+1)·(dY+1)·D` (`numeratorShapeSharpContent_le_loose`).  This statement uses that sufficient
threshold without asserting that the extra `+1` is mathematically necessary. -/
lemma solution_gamma_matches_word_if_subset_large
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (h57 : Claim57Assumptions k x₀ δ h_gs)
    (hR_degree_at_least_two : 2 ≤ Bivariate.natDegreeY (R k δ x₀ h_gs h57))
    (hR_totalDegree_le : Bivariate.totalDegree (R k δ x₀ h_gs h57) ≤ D_YZ Q)
    (hH_totalDegree_le : Bivariate.totalDegree (H k δ x₀ h_gs h57) ≤ D_YZ Q)
    {x : Fin n}
    (hx : (matching_set_at_x k δ h_gs h57 x).card >
      (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs h57)
        * (Bivariate.natDegreeY (R k δ x₀ h_gs h57) + 1)
        * D_YZ Q)
    : (P k δ x₀ h_gs h57 hR_degree_at_least_two hR_totalDegree_le
        hH_totalDegree_le).eval (Polynomial.C (ωs x)) =
      (Polynomial.C <| u₀ x) + u₁ x • Polynomial.X
    := by sorry

/-- Claim 5.11 from [BCIKS20].
There exists a set of points `{x₀,...,x_{k+1}}` such that the sets S_{x_j} satisfy the condition in
Claim 5.10. -/
lemma exists_points_with_large_matching_subset
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (h57 : Claim57Assumptions k x₀ δ h_gs)
    (_hR_degree_at_least_two : 2 ≤ Bivariate.natDegreeY (R k δ x₀ h_gs h57))
    (_hR_totalDegree_le : Bivariate.totalDegree (R k δ x₀ h_gs h57) ≤ D_YZ Q)
    (_hH_totalDegree_le : Bivariate.totalDegree (H k δ x₀ h_gs h57) ≤ D_YZ Q) :
  ∃ Dtop : Finset (Fin n),
    Dtop.card = k + 1 ∧
    ∀ x ∈ Dtop,
      (matching_set_at_x k δ h_gs h57 x).card >
        (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs h57)
        * (Bivariate.natDegreeY (R k δ x₀ h_gs h57) + 1)
        * D_YZ Q := by sorry

end BCIKS20ProximityGapSection5

end ProximityGap
