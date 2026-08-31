/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.JointAgreement
import ArkLib.Data.CodingTheory.ReedSolomon

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory
open scoped BigOperators LinearCode ProbabilityTheory
open Code

section CoreResults

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]


omit [DecidableEq ι] in
/-- Theorem 1.5 (Correlated agreement for low-degree parameterised curves) in [BCIKS20].

Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and a curve passing through words `u₀, ..., uκ`, such that
the probability that a random point on the curve is `δ`-close to the Reed-Solomon code
is greater than `k * ε`. Then, the words `u₀, ..., uκ` have correlated agreement.

This statement is restricted to the proven open Johnson/Guruswami-Sudan regime
`0 < δ < 1 - √ρ`. It does not encode the separate capacity-regime extension proposed as
Conjecture 8.4 of [BCIKS20]. -/
theorem correlatedAgreement_affine_curves {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδ_pos : 0 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  sorry

end CoreResults

section BCIKS20ProximityGapSection6

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The parameters for which the curve points are `δ`-close to a set `V`
(typically, a linear code). This is the set `S` from the proximity gap paper. -/
noncomputable def coeffs_of_close_proximity_curve {l : ℕ}
    (δ : ℝ≥0) (u : Fin l → Fin n → F) (V : Finset (Fin n → F)) : Finset F :=
  have : Fintype { z | δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z, V) ≤ δ } := by
    infer_instance
  @Set.toFinset _ { z | δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z, V) ≤ δ } this

/-- The degree-one case of Theorem 6.1 in [BCIKS20].

This bridges the polynomial-curve presentation to the existing kernel-checked affine-line
unique-decoding theorem. More than `n` close parameters force every point on the line to be
close, and the two line coefficients jointly agree with Reed-Solomon codewords. -/
theorem large_agreement_set_on_line_implies_correlated_agreement {deg : ℕ}
    {domain : Fin n ↪ F}
    {δ : ℝ≥0}
    (hδ : δ ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code domain deg : Set (Fin n → F)))
    (u : Fin 2 → Fin n → F)
    (hS : n < (coeffs_of_close_proximity_curve (F := F) δ u
      (ReedSolomon.toFinset domain deg)).card) :
    coeffs_of_close_proximity_curve (F := F) δ u
        (ReedSolomon.toFinset domain deg) = Finset.univ ∧
      ∃ v : Fin 2 → Fin n → F,
        (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
        (∀ z,
          δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z,
            Curve.polynomialCurveEval (F := F) (A := F) v z) ≤ δ) ∧
        ({ x : Fin n | ∃ i, u i x ≠ v i x } : Finset _).card ≤ δ * n := by
  classical
  have hcoeffs_eq :
      coeffs_of_close_proximity_curve (F := F) δ u
          (ReedSolomon.toFinset domain deg) =
        RS_goodCoeffs (deg := deg) (domain := domain) u δ := by
    ext z
    simp [coeffs_of_close_proximity_curve, RS_goodCoeffs, Curve.polynomialCurveEval,
      Fin.sum_univ_two, ReedSolomon.toFinset]
  have hgood : (RS_goodCoeffs (deg := deg) (domain := domain) u δ).card > n := by
    simpa [hcoeffs_eq] using hS
  have hja := RS_jointAgreement_of_goodCoeffs_card_gt
    (deg := deg) (domain := domain) (δ := δ) hδ u (by simpa using hgood)
  rcases hja with ⟨S, hS_card, v, hv⟩
  have hcurve_close (z : F) :
      δᵣ(Curve.polynomialCurveEval u z, Curve.polynomialCurveEval v z) ≤ δ := by
    rw [Code.relCloseToWord_iff_exists_agreementCols]
    refine ⟨S, ?_, ?_⟩
    · exact (Code.relDist_floor_bound_iff_complement_bound
        (Fintype.card (Fin n)) S.card δ).2 hS_card
    · intro x
      constructor
      · intro hx
        simp only [Curve.polynomialCurveEval, Finset.sum_apply]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Pi.smul_apply]
        have hix := (hv i).2 hx
        exact congrArg (z ^ (i : ℕ) • ·) (Finset.mem_filter.mp hix).2.symm
      · intro hne hx
        exact hne (by
          simp only [Curve.polynomialCurveEval, Finset.sum_apply]
          apply Finset.sum_congr rfl
          intro i _
          simp only [Pi.smul_apply]
          have hix := (hv i).2 hx
          exact congrArg (z ^ (i : ℕ) • ·) (Finset.mem_filter.mp hix).2.symm)
  have hcurve_mem (z : F) : Curve.polynomialCurveEval v z ∈ ReedSolomon.code domain deg := by
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (hv i).1
  have hcoeffs_univ : coeffs_of_close_proximity_curve (F := F) δ u
      (ReedSolomon.toFinset domain deg) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro z
    simp only [coeffs_of_close_proximity_curve, Set.mem_toFinset, Set.mem_ofPred_eq]
    have hcode := Code.relDistFromCode_le_relDist_to_mem
      (u := Curve.polynomialCurveEval u z)
      (C := (ReedSolomon.code domain deg : Set (Fin n → F)))
      (v := Curve.polynomialCurveEval v z) (hcurve_mem z)
    have : δᵣ(Curve.polynomialCurveEval u z,
        (ReedSolomon.code domain deg : Set (Fin n → F))) ≤ δ :=
      le_trans hcode (by exact_mod_cast hcurve_close z)
    simpa [ReedSolomon.toFinset] using this
  have hbad_subset :
      ({x : Fin n | ∃ i, u i x ≠ v i x} : Finset _) ⊆
        Finset.univ.filter (fun x => x ∉ S) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hxS
    rcases Finset.mem_filter.mp hx with ⟨_, i, hui⟩
    have hix := (hv i).2 hxS
    exact hui (Finset.mem_filter.mp hix).2.symm
  have hcomplement_card :
      (Finset.univ.filter (fun x : Fin n => x ∉ S)).card = n - S.card := by
    have hpartition : S.card + (Finset.univ.filter (fun x : Fin n => x ∉ S)).card = n := by
      simpa using (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n))) (p := fun x => x ∈ S))
    omega
  have hS_nat : n - Nat.floor (δ * n) ≤ S.card :=
    (Code.relDist_floor_bound_iff_complement_bound n S.card δ).2 (by simpa using hS_card)
  have hbad_nat : ({x : Fin n | ∃ i, u i x ≠ v i x} : Finset _).card ≤
      Nat.floor (δ * n) := by
    have hcard := Finset.card_le_card hbad_subset
    rw [hcomplement_card] at hcard
    omega
  refine ⟨hcoeffs_univ, v, fun i => (hv i).1, hcurve_close, ?_⟩
  exact_mod_cast le_trans (by exact_mod_cast hbad_nat) (Nat.floor_le (by positivity))

/-- Theorem 6.1 of [BCIKS20], in the unique-decoding regime.

For `l + 1` words, if more than `n * l` parameters give a curve point `δ`-close to the
fixed Reed-Solomon code, then every parameter is close. Moreover, the curve is close to
a curve whose coefficients are Reed-Solomon codewords, and the two coefficient stacks
differ on at most `δ * n` coordinates.

The Reed-Solomon code and its actual relative unique-decoding radius are explicit here.
They are load-bearing assumptions: replacing the code by an arbitrary finite set and
leaving the rate unconstrained makes the statement false. -/
theorem large_agreement_set_on_curve_implies_correlated_agreement {l deg : ℕ}
    (hdeg_pos : 0 < deg)
    (hdeg_le : deg ≤ n)
    {domain : Fin n ↪ F}
    {δ : ℝ≥0}
    (hδ : δ ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code domain deg : Set (Fin n → F)))
    {u : Fin (l + 1) → Fin n → F}
    (hS : n * l < (coeffs_of_close_proximity_curve (F := F) δ u
      (ReedSolomon.toFinset domain deg)).card) :
    coeffs_of_close_proximity_curve (F := F) δ u
        (ReedSolomon.toFinset domain deg) = Finset.univ ∧
      ∃ v : Fin (l + 1) → Fin n → F,
        (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
        (∀ z,
          δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z,
            Curve.polynomialCurveEval (F := F) (A := F) v z) ≤ δ) ∧
        ({ x : Fin n | ∃ i, u i x ≠ v i x } : Finset _).card ≤ δ * n := by
  sorry

/-- The distance bound from [BCIKS20]. -/
noncomputable def δ₀ (rho : ℝ) (m : ℕ) : ℝ :=
  1 - Real.sqrt rho - Real.sqrt rho / (2 * m)

/-- Theorem 6.2 of [BCIKS20], strictly within the Johnson/Guruswami-Sudan regime.

If the set of points on the curve defined by `u` close to the fixed Reed-Solomon code has at least
`((1 + 1 / (2 * m)) ^ 7 * m ^ 7) / (3 * (Real.rpow rho (3 / 2 : ℚ))) * n ^ 2 * l + 1`
points, then there exist Reed-Solomon codewords `v` that are `(1 - δ) * n` close to `u`.

Here `rho` is the actual rate of `ReedSolomon.code domain deg`; it is not a free
parameter. The theorem does not assert the capacity-regime Conjecture 8.4 of [BCIKS20]. -/
theorem large_agreement_set_on_curve_implies_correlated_agreement' {l deg : ℕ}
    (hdeg_pos : 0 < deg)
    (hdeg_le : deg ≤ n)
    {domain : Fin n ↪ F}
    {m : ℕ}
    {δ : ℝ≥0}
    (hm : 3 ≤ m)
    (hδ : (δ : ℝ) ≤ δ₀ (((LinearCode.rate (ReedSolomon.code domain deg) : ℚ≥0) : ℝ)) m)
    {u : Fin (l + 1) → Fin n → F}
    (hS : ((1 + 1 / (2 * m)) ^ 7 * m ^ 7) /
        (3 * Real.rpow ((LinearCode.rate (ReedSolomon.code domain deg) : ℚ≥0) : ℝ)
          (3 / 2 : ℚ)) * n ^ 2 * l <
      (coeffs_of_close_proximity_curve (F := F) δ u
        (ReedSolomon.toFinset domain deg)).card) :
    ∃ v : Fin (l + 1) → Fin n → F,
      (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
      (1 - δ) * n ≤ ({ x : Fin n | ∀ i, u i x = v i x } : Finset _).card := by
  sorry

end BCIKS20ProximityGapSection6

end ProximityGap
