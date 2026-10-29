/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Katerina Hristova,
  Ilia Vlasov, Aristotle (Harmonic), Alexander Hicks
-/
module

public import ArkLib.Data.Probability.Uniform
public import ArkLib.Data.MvPolynomial.Degrees
public import ArkLib.Data.MvPolynomial.SchwartzZippelCounting
public import CompPoly.Data.Fin.BigOperators

/-! # Probability bounds for finite uniform samples

ArkLib's specialized counting arguments are exposed here over VCVio's native `ProbComp`
uniform sampler. Generic event algebra, counting formulas, transport along equivalences, and product
sampling are provided by `SampleableType.Measure`.
-/

@[expose] public section

open ProbabilityTheory Filter NNReal Finset Function Real
open scoped BigOperators ProbabilityTheory ENNReal NNReal

namespace Probability

/-! ## Polynomial identity bounds -/

/-- **Schwartz-Zippel**, in probability form at an arbitrary degree bound: for a nonzero
`n`-variate polynomial `P` of total degree at most `d` over a finite domain `R`,

  `Pr{let r ← $ᵗ R^n}[eval r P = 0] ≤ d / |R|`.
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

/-- Scalar-challenge form of the polynomial root bound for one variable. -/
lemma prob_schwartz_zippel_single_variable
    {R : Type} [CommRing R] [NoZeroDivisors R] [Fintype R] [SampleableType R]
    (p : MvPolynomial (Fin 1) R) {d : ℕ} (hne : p ≠ 0) (hdeg : p.totalDegree ≤ d) :
    Pr{let γ ← $ᵗ R}[MvPolynomial.eval (fun _ : Fin 1 => γ) p = 0] ≤
      (d : ℝ≥0∞) / Fintype.card R := by
  have : Nontrivial R := by
    by_contra h
    have : Subsingleton R := not_nontrivial_iff_subsingleton.mp h
    exact hne (Subsingleton.elim _ _)
  have : IsDomain R := NoZeroDivisors.to_isDomain R
  exact (SampleableType.prEvent_uniformSample_equiv (Equiv.funUnique (Fin 1) R).symm
    (fun r => MvPolynomial.eval r p = 0)).trans_le
      (prob_schwartz_zippel_mv_polynomial_of_totalDegree_le p hne hdeg)

/-- Two distinct univariate polynomials of degree at most `d` agree at a uniform point with
probability at most `d / |R|`: their difference has at most `d` roots. -/
lemma prob_polynomial_eval_eq_le
    {R : Type} [CommRing R] [NoZeroDivisors R] [Fintype R] [SampleableType R]
    {d : ℕ} {p q : Polynomial R} (hne : p ≠ q) (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) :
    Pr{let γ ← $ᵗ R}[p.eval γ = q.eval γ] ≤ (d : ℝ≥0∞) / Fintype.card R := by
  classical
  have : Nontrivial R := by
    by_contra h
    have : Subsingleton R := not_nontrivial_iff_subsingleton.mp h
    exact hne (Subsingleton.elim _ _)
  have : IsDomain R := NoZeroDivisors.to_isDomain R
  rw [SampleableType.prEvent_uniformSample]
  gcongr
  have hr : p - q ≠ 0 := sub_ne_zero.mpr hne
  refine (Polynomial.card_le_degree_of_subset_roots (p := p - q) fun γ hγ => ?_).trans
    ((Polynomial.natDegree_sub_le _ _).trans (max_le hp hq))
  exact (Polynomial.mem_roots hr).mpr (by
    simpa [sub_eq_zero] using (Finset.mem_filter.mp hγ).2)

/-- Distinct degree-bounded polynomials agree with probability at most `d / |R|`.
The NNReal presentation is convenient for protocol error bounds. -/
lemma prob_degreeLE_eval_eq_le
    {R : Type} [CommRing R] [NoZeroDivisors R] [Fintype R] [SampleableType R]
    {d : ℕ} {p q : Polynomial.degreeLE R d} (hne : p ≠ q) :
    Pr{let c ← $ᵗ R}[p.val.eval c = q.val.eval c] ≤
      (((d : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞) := by
  rw [ENNReal.coe_div (by simp), ENNReal.coe_natCast, ENNReal.coe_natCast]
  exact prob_polynomial_eval_eq_le (fun h => hne (Subtype.ext h))
    (Polynomial.natDegree_le_of_degree_le (Polynomial.mem_degreeLE.mp p.property))
    (Polynomial.natDegree_le_of_degree_le (Polynomial.mem_degreeLE.mp q.property))

/-- Degree-bounded polynomials with unequal sums on a finite set agree at a uniform point
with probability at most `d / |R|`, including over finite semiring domains. -/
lemma prob_agreement_of_sum_ne
    {R : Type} [CommSemiring R] [IsDomain R] [Fintype R] [SampleableType R]
    {d : ℕ} (S : Finset R) (p q : Polynomial.degreeLE R d)
    (hne : (∑ x ∈ S, p.val.eval x) ≠ ∑ x ∈ S, q.val.eval x) :
    Pr{let r ← $ᵗ R}[p.val.eval r = q.val.eval r] ≤
      (((d : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞) := by
  classical
  have hex : ∃ r : R, p.val.eval r ≠ q.val.eval r := by
    by_contra h
    push Not at h
    exact hne (Finset.sum_congr rfl (fun x _ => h x))
  have hsplit : (∃ a : R, a + 1 = 0) ∨ ∀ a : R, a = 0 ∨ a = 1 := by
    let s : R := ∑ x : R, x
    have hs (a : R) (ha : a ≠ 0) : a * s = s := by
      rw [show a * s = ∑ x : R, a * x by simp [s, mul_sum]]
      exact Fintype.sum_bijective (a * ·)
        ⟨fun _ _ h => mul_left_cancel₀ ha h,
          Finite.surjective_of_injective (fun _ _ h => mul_left_cancel₀ ha h)⟩
        (a * ·) id (fun _ => rfl)
    by_cases hz : s = 0
    · left
      refine ⟨∑ x ∈ (univ : Finset R).erase 1, x, ?_⟩
      rw [sum_erase_add _ _ (mem_univ 1)]
      exact hz
    · right
      intro a
      by_cases ha : a = 0
      · exact Or.inl ha
      · exact Or.inr (mul_right_cancel₀ hz (by simpa using hs a ha))
  rcases hsplit with ⟨a, ha⟩ | hb
  · let : CommRing R :=
      { (inferInstance : CommSemiring R) with
        neg x := a * x
        zsmul := @zsmulRec R _ _ ⟨fun x => a * x⟩ (fun n x => n • x)
        zsmul_zero' x := zero_nsmul x
        zsmul_succ' n x := by
          change (n + 1) • x = n • x + x
          simpa only [add_comm] using succ_nsmul' x n
        neg_add_cancel x := by
          change a * x + x = 0
          calc
            a * x + x = (a + 1) * x := by rw [add_mul, one_mul]
            _ = 0 := by rw [ha, zero_mul] }
    apply prob_degreeLE_eval_eq_le
    intro h
    subst q
    exact hne rfl
  · by_cases hd : d = 0
    · subst d
      have hp : p.val = Polynomial.C (p.val.coeff 0) :=
        Polynomial.eq_C_of_degree_le_zero (Polynomial.mem_degreeLE.mp p.property)
      have hq : q.val = Polynomial.C (q.val.coeff 0) :=
        Polynomial.eq_C_of_degree_le_zero (Polynomial.mem_degreeLE.mp q.property)
      have hz : Pr{let r ← $ᵗ R}[p.val.eval r = q.val.eval r] = 0 := by
        apply prEvent_eq_zero_of_forall_not
        intro r hr
        obtain ⟨s, hs⟩ := hex
        apply hs
        rw [hp, hq, Polynomial.eval_C, Polynomial.eval_C] at hr ⊢
        exact hr
      exact hz.le.trans zero_le
    · have hu : (univ : Finset R) = {0, 1} := by
        ext x
        simp only [mem_univ, mem_insert, mem_singleton, true_iff]
        exact hb x
      have hc : Fintype.card R = 2 := by
        rw [← card_univ, hu]
        simp [zero_ne_one]
      obtain ⟨r, hr⟩ := hex
      have hsub : univ.filter (fun x => p.val.eval x = q.val.eval x) ⊆ univ.erase r := by
        intro x hx
        refine mem_erase.mpr ⟨?_, mem_univ _⟩
        intro hxr
        subst x
        exact hr (mem_filter.mp hx).2
      have hcard : (univ.filter (fun x => p.val.eval x = q.val.eval x)).card ≤ d := by
        calc
          _ ≤ (univ.erase r).card := card_le_card hsub
          _ = Fintype.card R - 1 := by rw [card_erase_of_mem (mem_univ r), card_univ]
          _ ≤ d := by omega
      rw [SampleableType.prEvent_uniformSample]
      rw [ENNReal.coe_div (by simp), ENNReal.coe_natCast, ENNReal.coe_natCast]
      gcongr

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
    {ι F : Type} [Fintype ι] [Field F] [Fintype F]
    [SampleableType F] [SampleableType (ι → F)]
    (d : ι → F) (hd : d ≠ 0) :
    Pr{let v ← $ᵗ (ι → F)}[(∑ j, d j * v j) = 0] =
      (Fintype.card F : ℝ≥0∞)⁻¹ := by
  classical
  let p : (ι → F) → Prop := fun v ↦ ∑ j, d j * v j = 0
  let decP : DecidablePred p := fun _ ↦ Classical.propDecidable _
  change Pr{let v ← $ᵗ (ι → F)}[p v] = (Fintype.card F : ℝ≥0∞)⁻¹
  set L : (ι → F) →ₗ[F] F := ∑ j, d j • LinearMap.proj j with hL
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
  have hquot : Nat.card ((ι → F) ⧸ LinearMap.ker L) = Fintype.card F := by
    rw [Nat.card_congr (L.quotKerEquivOfSurjective hsurj).toEquiv, Nat.card_eq_fintype_card]
  let fintypeKer : Fintype (LinearMap.ker L) := Fintype.ofFinite _
  have hcard : Fintype.card (ι → F) =
      @Fintype.card (LinearMap.ker L) fintypeKer * Fintype.card F := by
    have h := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker L)
    rw [hquot] at h
    rw [← Nat.card_eq_fintype_card,
      ← @Nat.card_eq_fintype_card (LinearMap.ker L) fintypeKer]
    exact h
  have hfilter :
      (@Finset.filter (ι → F) p decP Finset.univ).card =
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
    {ι F : Type} [Fintype ι] [Field F] [Fintype F]
    [SampleableType F] [SampleableType (ι → F)]
    (d : ι → F) (hd : d ≠ 0) :
    Pr{let v ← $ᵗ (ι → F)}[(∑ j, d j * v j) = 0] ≤
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
