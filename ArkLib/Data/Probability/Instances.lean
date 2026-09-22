/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Katerina Hristova,
         Ilia Vlasov, Aristotle (Harmonic)
-/
module

public import ArkLib.Data.Probability.Uniform
public import ArkLib.Data.MvPolynomial.Degrees
public import ArkLib.Data.MvPolynomial.SchwartzZippelCounting
public import CompPoly.Data.Fin.BigOperators

/-! # Probability bounds for finite uniform samples

ArkLib's specialized counting arguments are exposed here over VCVio's native `ProbComp`
uniform sampler. Generic event algebra, counting formulas, transport along equivalences, and product
sampling are provided by `SampleableType.NativeMeasure`.
-/

@[expose] public section

open ProbabilityTheory Filter NNReal Finset Function Real
open scoped BigOperators ProbabilityTheory ENNReal NNReal

namespace Probability

/-! ## Polynomial identity bounds -/

/-- **Schwartz-Zippel**, in probability form at an arbitrary degree bound: for a nonzero
`n`-variate polynomial `P` of total degree at most `d` over a finite domain `R`,

  `Pr{r ← $ᵗ R^n}[eval r P = 0] ≤ d / |R|`.
-/
lemma prob_schwartz_zippel_mv_polynomial_of_totalDegree_le
    {R : Type} [CommRing R] [IsDomain R] [Fintype R] [SampleableType R]
    {n d : ℕ}
    (P : MvPolynomial (Fin n) R) (h_nonzero : P ≠ 0) (h_deg : P.totalDegree ≤ d) :
    Pr{let r ← $ᵗ (Fin n → R)}[MvPolynomial.eval r P = 0] ≤
      (d : ℝ≥0∞) / Fintype.card R := open scoped Classical in by
  let : Field R := @Fintype.fieldOfDomain R _ _ (Classical.decEq R) _
  exact prob_eval_zero_univ_le_div P h_nonzero h_deg

/-- The `d := n` specialization of
`prob_schwartz_zippel_mv_polynomial_of_totalDegree_le`. -/
lemma prob_schwartz_zippel_mv_polynomial
    {R : Type} [CommRing R] [IsDomain R] [Fintype R] [SampleableType R]
    {n : ℕ}
    (P : MvPolynomial (Fin n) R) (h_nonzero : P ≠ 0) (h_deg : P.totalDegree ≤ n) :
    Pr{let r ← $ᵗ (Fin n → R)}[MvPolynomial.eval r P = 0] ≤
      (n : ℝ≥0∞) / Fintype.card R :=
  prob_schwartz_zippel_mv_polynomial_of_totalDegree_le P h_nonzero h_deg

/-- The polynomial identity lemma in individual-degree form. -/
lemma prob_polynomial_identity_le
    {R : Type} [CommRing R] [IsDomain R] [Fintype R] [SampleableType R]
    {m d : ℕ} (P : MvPolynomial (Fin m) R)
    (h_nonzero : P ≠ 0) (h_indiv_deg : ∀ i, P.degreeOf i < d) :
    Pr{let r ← $ᵗ (Fin m → R)}[MvPolynomial.eval r P = 0] ≤
      (m * (d - 1) : ℕ) / (Fintype.card R : ℝ≥0∞) := by
  have h_total_deg : P.totalDegree ≤ m * (d - 1) :=
    MvPolynomial.totalDegree_le_of_degreeOf_lt P h_indiv_deg
  exact prob_schwartz_zippel_mv_polynomial_of_totalDegree_le P h_nonzero h_total_deg

/-! ## Linear collision bounds -/

/-- A nonzero `F`-linear form vanishes with probability exactly `1 / |F|`. -/
theorem prob_dotProduct_eq_zero_eq_inv_card
    {F : Type} [Field F] [Fintype F] [SampleableType F] {k : ℕ}
    (d : Fin k → F) (hd : d ≠ 0) :
    Pr{let v ← $ᵗ (Fin k → F)}[(∑ j, d j * v j) = 0] =
      (Fintype.card F : ℝ≥0∞)⁻¹ := open scoped Classical in by
  let p : (Fin k → F) → Prop := fun v ↦ ∑ j, d j * v j = 0
  let decP : DecidablePred p := fun _ ↦ Classical.propDecidable _
  change Pr{let v ← $ᵗ (Fin k → F)}[p v] = (Fintype.card F : ℝ≥0∞)⁻¹
  set L : (Fin k → F) →ₗ[F] F := ∑ j, d j • LinearMap.proj j with hL
  have hLapply : ∀ v, L v = ∑ j, d j * v j := by
    intro v
    simp only [hL, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, smul_eq_mul]
  obtain ⟨j₀, hj₀⟩ : ∃ j, d j ≠ 0 := by
    by_contra h
    exact hd (funext fun j ↦ not_not.mp (fun hj ↦ h ⟨j, hj⟩))
  have hsurj : Function.Surjective L := by
    intro c
    refine ⟨Pi.single j₀ (c / d j₀), ?_⟩
    rw [hLapply, Finset.sum_eq_single j₀]
    · rw [Pi.single_eq_same, mul_div_cancel₀ _ hj₀]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j₀) h
  have hquot : Nat.card ((Fin k → F) ⧸ LinearMap.ker L) = Fintype.card F := by
    rw [Nat.card_congr (L.quotKerEquivOfSurjective hsurj).toEquiv, Nat.card_eq_fintype_card]
  let fintypeKer : Fintype (LinearMap.ker L) := Fintype.ofFinite _
  have hcard : Fintype.card (Fin k → F) =
      @Fintype.card (LinearMap.ker L) fintypeKer * Fintype.card F := by
    have h := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker L)
    rw [hquot] at h
    rw [← Nat.card_eq_fintype_card,
      ← @Nat.card_eq_fintype_card (LinearMap.ker L) fintypeKer]
    exact h
  have hfilter :
      (@Finset.filter (Fin k → F) p decP Finset.univ).card =
        @Fintype.card (LinearMap.ker L) fintypeKer := by
    let fintypeP : Fintype {v // p v} := Fintype.ofFinite _
    rw [@Fintype.card_congr _ _ fintypeKer fintypeP
      (Equiv.subtypeEquivRight (fun x ↦ by
      rw [LinearMap.mem_ker, hLapply])),
      @Fintype.card_subtype _ _ p fintypeP decP]
  rw [@SampleableType.prEvent_uniformSample _ _ _ p decP, hfilter, hcard]
  push_cast
  have hkne : (@Fintype.card (LinearMap.ker L) fintypeKer : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true]
  have hF : (Fintype.card F : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true]
  rw [eq_comm, ← one_div,
    ENNReal.div_eq_div_iff (mul_ne_zero hkne hF)
      (ENNReal.mul_ne_top (by simp) (by simp)) hF (by simp)]
  ring

/-- `≤`-form of `prob_dotProduct_eq_zero_eq_inv_card`. -/
theorem prob_dotProduct_eq_zero_le
    {F : Type} [Field F] [Fintype F] [SampleableType F] {k : ℕ}
    (d : Fin k → F) (hd : d ≠ 0) :
    Pr{let v ← $ᵗ (Fin k → F)}[(∑ j, d j * v j) = 0] ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ :=
  le_of_eq (prob_dotProduct_eq_zero_eq_inv_card d hd)

/-! ## Product membership bounds -/

/-- For a uniformly random `xs : Fin t → ι`, the probability that every coordinate lands in
`A` is `(|A| / |ι|) ^ t`. -/
theorem prob_uniform_pi_mem_finset_eq
    {ι : Type} [Fintype ι] [SampleableType ι] (A : Finset ι) (t : ℕ) :
    Pr{let xs ← $ᵗ (Fin t → ι)}[∀ i, xs i ∈ A] =
      ((A.card : ℝ≥0∞) / Fintype.card ι) ^ t := open scoped Classical in by
  let p : (Fin t → ι) → Prop := fun xs ↦ ∀ i, xs i ∈ A
  let decP : DecidablePred p := fun _ ↦ Classical.propDecidable _
  change Pr{let xs ← $ᵗ (Fin t → ι)}[p xs] = _
  rw [@SampleableType.prEvent_uniformSample _ _ _ p decP]
  have hfilter : @Finset.filter (Fin t → ι) p decP Finset.univ =
      Fintype.piFinset (fun _ : Fin t ↦ A) := by
    ext xs
    simp [p, Fintype.mem_piFinset]
  rw [hfilter, Fintype.card_piFinset]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_fun]
  push_cast
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_pow, ENNReal.inv_pow]

/-- `≤`-form of `prob_uniform_pi_mem_finset_eq`. -/
theorem prob_uniform_pi_mem_finset_le
    {ι : Type} [Fintype ι] [SampleableType ι] (A : Finset ι) (t : ℕ) :
    Pr{let xs ← $ᵗ (Fin t → ι)}[∀ i, xs i ∈ A] ≤
      ((A.card : ℝ≥0∞) / Fintype.card ι) ^ t :=
  le_of_eq (prob_uniform_pi_mem_finset_eq A t)

end Probability
