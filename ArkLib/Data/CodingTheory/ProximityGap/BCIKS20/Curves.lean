/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound
public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.JointAgreement
public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.CurveBWMatrix
public import ArkLib.Data.CodingTheory.ReedSolomon
public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.CurveBridge
public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.CurveExplicit
public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.JohnsonComparison
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.Johnson.LegacyComparison

/-!
# ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves

Polynomial received curves satisfy correlated agreement throughout the open Johnson radius.
The unique-decoding proof uses a Berlekamp–Welch matrix; the Johnson proof uses ordinary
exact power agreement and finite comparisons with the original BCIKS20 error budgets.
-/

@[expose] public section

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory
open scoped BigOperators LinearCode ProbabilityTheory
open Code

/-- The Johnson exact-power exceptional set fits the original BCIKS20 curve error budget.
This is the non-unique-decoding branch; its message dimension is positive and its radius lies
strictly below the Johnson threshold. -/
theorem exists_curve_exactPowerAgreement_johnson_budget
    {ι F : Type} [Fintype ι] [Nonempty ι] [Field F] [Fintype F] [DecidableEq F]
    {deg k : ℕ} (domain : ι ↪ F) (δ : ℝ≥0) (hdeg_pos : 0 < deg)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hUD : ¬ δ ≤ Code.relativeUniqueDecodingRadius
      (C := (ReedSolomon.code domain deg : Set (ι → F))))
    (u : Fin (k + 1) → ι → F) :
    ∃ E : Finset F,
      (E.card : ℝ) ≤ (k : ℝ) * (errorBound δ deg domain : ℝ) * Fintype.card F ∧
      ∀ z ∉ E, ∀ P : Polynomial F, P.degree < deg →
        ⌈(Fintype.card ι : ℝ) * (1 - (δ : ℝ))⌉₊ ≤
          (ReedSolomon.polynomialAgreementSet domain
            (ReedSolomon.powerBatchedWord u z) P).card →
        ReedSolomon.HasExactPowerAgreement domain u (RingHom.id F) deg z P := by
  classical
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  have hproper : deg < Fintype.card ι := by
    by_contra h
    have hfull : Fintype.card ι ≤ deg := by omega
    have hrate : LinearCode.rate (ReedSolomon.code domain deg) = 1 := by
      rw [ReedSolomon.rateOfLinearCode_eq_min_div, min_eq_right hfull]
      exact div_self (by exact_mod_cast hn.ne')
    simp [ReedSolomon.sqrtRate, hrate] at hδ
  let : NeZero deg := ⟨hdeg_pos.ne'⟩
  have hrate : (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) =
      (deg : ℝ≥0) / Fintype.card ι := by
    rw [ReedSolomon.rateOfLinearCode_eq_div hproper.le]
    simp [NNRat.cast_div, NNRat.cast_natCast]
  have hJ : δ ∈ Set.Ioo
      ((1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2)
      (1 - NNReal.sqrt (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) := by
    refine ⟨?_, hδ⟩
    rw [hrate]
    rwa [ReedSolomon.relativeUniqueDecodingRadius_RS_eq hproper.le, not_le] at hUD
  let s : ℝ := ReedSolomon.sqrtRate deg domain
  have hs0 : 0 < s := ReedSolomon.sqrtRate_pos hdeg_pos
  have hs : s = Real.sqrt ((deg : ℝ) / Fintype.card ι) := by
    simp only [s, hrate, Real.coe_sqrt, NNReal.coe_div, NNReal.coe_natCast]
  have hδR : (δ : ℝ) < 1 - s := by
    have h := NNReal.coe_lt_coe.mpr hδ
    rwa [NNReal.coe_sub (ReedSolomon.sqrtRate_le_one deg domain), NNReal.coe_one] at h
  let b : ℝ := min (1 - s - δ) (s / 20)
  have hb : 0 < b := lt_min (by linarith) (by positivity)
  have hbRate : b ≤ Real.sqrt ((deg : ℝ) / Fintype.card ι) / 20 := by
    rw [← hs]
    exact min_le_right _ _
  have herr : (errorBound δ deg domain : ℝ) =
      (deg : ℝ) ^ 2 / ((2 * b) ^ 7 * Fintype.card F) := by
    rw [errorBound_eq_johnson hJ]
    change ((deg ^ 2 : ℝ≥0) : ℝ) / _ = _
    simp [b, s, NNReal.coe_sub hδ.le,
      NNReal.coe_sub (ReedSolomon.sqrtRate_le_one deg domain)]
  let A := ⌈(Fintype.card ι : ℝ) * (1 - (δ : ℝ))⌉₊
  let B : ℝ := (k : ℝ) * ((deg : ℝ) ^ 2 / (2 * b) ^ 7)
  have hexact : ∃ E : Finset F, (E.card : ℝ) ≤ B ∧
      ∀ z ∉ E, ∀ P : Polynomial F, P.degree < deg →
        A ≤ (ReedSolomon.polynomialAgreementSet domain
          (ReedSolomon.powerBatchedWord u z) P).card →
        ReedSolomon.HasExactPowerAgreement domain u (RingHom.id F) deg z P := by
    obtain ⟨D, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hdeg_pos.ne'
    by_cases hD : D = 0
    · subst D
      obtain ⟨E, hE, hgood⟩ := ReedSolomon.uniformExactPowerAgreement_constantCode domain u A
      refine ⟨E, ?_, hgood⟩
      have hc := ReedSolomon.HiddenDerivative.choose_two_le_bciks hn hb
        (by simpa using hbRate)
      have hE' : (E.card : ℝ) ≤ k * (Fintype.card ι).choose 2 := by
        exact_mod_cast hE.trans (Nat.div_le_self _ _)
      exact hE'.trans (by simpa [B] using mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg k))
    · let eta : ℝ := 1 - δ - Real.sqrt
          (ReedSolomon.HiddenDerivative.johnsonRhoMinus (Fintype.card ι) D)
      have hDpos : 1 ≤ D := by omega
      have hDn : D ≤ Fintype.card ι - 2 := by omega
      have hsmall : Real.sqrt
          (ReedSolomon.HiddenDerivative.johnsonRhoMinus (Fintype.card ι) D) ≤ s := by
        rw [hs]
        apply Real.sqrt_le_sqrt
        unfold ReedSolomon.HiddenDerivative.johnsonRhoMinus
        gcongr
        exact_mod_cast Nat.le_succ D
      have hbeta : b ≤ eta := by
        have := min_le_left (1 - s - (δ : ℝ)) (s / 20)
        dsimp only [b, eta] at *
        linarith
      have heta : 0 < eta := hb.trans_le hbeta
      have ha : ReedSolomon.HiddenDerivative.johnsonAgreement (Fintype.card ι) D eta =
          1 - δ := by
        unfold ReedSolomon.HiddenDerivative.johnsonAgreement eta
        ring
      have hthreshold : ReedSolomon.HiddenDerivative.johnsonAgreement
          (Fintype.card ι) D eta * Fintype.card ι ≤ A := by
        rw [ha, mul_comm]
        exact Nat.le_ceil _
      have hAn : A ≤ Fintype.card ι := by
        apply Nat.ceil_le.mpr
        exact mul_le_of_le_one_right (Nat.cast_nonneg _) (sub_le_self _ δ.coe_nonneg)
      obtain ⟨E, hE, hgood⟩ := exists_johnson_curve_exactPowerAgreement_of_fintype
        domain u hDpos hDn heta hthreshold hAn
      refine ⟨E, ?_, hgood⟩
      have hc := ReedSolomon.HiddenDerivative.two_mul_johnsonExceptionCount_le_bciks
        hDpos hDn heta hthreshold hb hbeta (by simpa using hbRate)
      have hh := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg k)
      dsimp [B]
      push_cast
      nlinarith only [hE, hh]
  obtain ⟨E, hE, hgood⟩ := hexact
  refine ⟨E, hE.trans ?_, hgood⟩
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [herr]
  dsimp only [B]
  apply le_of_eq
  field_simp


section BCIKS20ProximityGapSection6

variable {F : Type} [Field F] [Fintype F] [sampleF : SampleableType F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The parameters for which the curve points are `δ`-close to a set `V`
(typically, a linear code). This is the set `S` from the proximity gap paper. -/
noncomputable def coeffs_of_close_proximity_curve {l : ℕ}
    (δ : ℝ≥0) (u : Fin l → Fin n → F) (V : Finset (Fin n → F)) : Finset F :=
  have : Fintype { z | δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z, V) ≤ δ } := by
    infer_instance
  @Set.toFinset _ { z | δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z, V) ≤ δ } this

omit [SampleableType F] in
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

omit [SampleableType F] in
open CurveBW in
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
  classical
  have : NeZero deg := ⟨by omega⟩
  set S : Finset F := coeffs_of_close_proximity_curve (F := F) δ u
    (ReedSolomon.toFinset domain deg) with hSdef
  set e : ℕ := Nat.floor (δ * n) with he
  have hset : (ReedSolomon.toFinset domain deg : Set (Fin n → F)) =
      (ReedSolomon.code domain deg : Set (Fin n → F)) := by
    simp [ReedSolomon.toFinset, ReedSolomon.RScodeSet]
  have hSmem : ∀ z : F, z ∈ S ↔ δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z,
      (ReedSolomon.code domain deg : Set (Fin n → F))) ≤ δ := by
    intro z
    simp only [S, coeffs_of_close_proximity_curve, Set.mem_toFinset, Set.mem_ofPred_eq, hset]
  have hScard : l * n < S.card := by
    rw [hSdef]
    simpa [Nat.mul_comm] using hS
  have hSpos : 0 < S.card := lt_of_le_of_lt (Nat.zero_le _) hScard
  -- arithmetic consequences of the unique decoding radius
  have hBW : 2 * e < n - deg + 1 := by
    simpa [e] using RS_BW_bound_of_le_relUDR (deg := deg) (domain := domain) (δ := δ)
      (by simpa using hdeg_le) hδ
  have he2 : 2 * e + deg ≤ n := by omega
  have he1 : e + 1 ≤ n := by
    simpa [e] using
      (RS_floor_mul_card_ι_add_one_le_card_ι_of_le_relUDR (deg := deg) (domain := domain)
        (δ := δ) (by simpa using hdeg_le) hδ)
  have hcardn : e + deg ≤ n := by
    simpa [e] using
      (RS_floor_mul_card_ι_add_deg_le_card_ι_of_le_relUDR (deg := deg) (domain := domain)
        (δ := δ) (by simpa using hdeg_le) hδ)
  -- Step 1: all maximal minors of the symbolic curve BW matrix vanish.
  have hdets : ∀ r : Fin ((e + 1) + (e + deg)) → Fin n,
      Matrix.det ((curveBWMatrix (l := l) e deg domain u).submatrix r id) = 0 := by
    intro r
    have h := curveBWMatrix_det_submatrix_eq_zero (l := l) (deg := deg) (domain := domain)
      (δ := δ) (u := u) (S := S) hdeg_pos (by simpa [e] using he1) hScard
      (fun z hz => (hSmem z).1 hz) r
    simpa [e] using h
  -- Step 2: a kernel vector over `F[Y]` with controlled degrees.
  obtain ⟨a, b, ha0, hadeg, hbdeg, hker⟩ :=
    exists_kernelVec_curveBWMatrix (l := l) (deg := deg) (domain := domain) (u := u) e
      hcardn he1 hdets
  -- Step 3: the column relations.
  have hcol : ∀ x : Fin n, Polynomial.Bivariate.evalX (domain x) (bivariateOf b) =
      curveParamPoly u x * Polynomial.Bivariate.evalX (domain x) (bivariateOf a) :=
    (curveBivariate_column (l := l) (e := e) (deg := deg) (domain := domain) (u := u) (a := a)
      (b := b) ((mulVec_curveBWMatrix_eq_zero_iff e deg domain u a b).1 hker))
  -- Step 4: the nearest codeword data at every good parameter.
  have qexists : ∀ z ∈ S, ∃ p : Polynomial F × Finset (Fin n), p.1.natDegree < deg ∧
      p.2.card ≤ e ∧ ∀ x, x ∉ p.2 → (curveParamPoly u x).eval z = p.1.eval (domain x) := by
    intro z hz
    obtain ⟨q, B, h1, h2, h3⟩ :=
      exists_close_poly (deg := deg) (domain := domain) (δ := δ) ((hSmem z).1 hz)
    exact ⟨(q, B), h1, by simpa [e] using h2, fun x hx => by
      rw [curveParamPoly_eval]; exact h3 x hx⟩
  let qfun : F → Polynomial F := fun z =>
    if h : z ∈ S then (Classical.choose (qexists z h)).1 else 0
  let Bfun : F → Finset (Fin n) := fun z =>
    if h : z ∈ S then (Classical.choose (qexists z h)).2 else ∅
  have qfun_spec : ∀ z (hz : z ∈ S), (qfun z).natDegree < deg ∧ (Bfun z).card ≤ e ∧
      ∀ x, x ∉ Bfun z → (curveParamPoly u x).eval z = (qfun z).eval (domain x) := by
    intro z hz
    have := Classical.choose_spec (qexists z hz)
    simpa [qfun, Bfun, dite_eq_left hz] using this
  have hrow : ∀ z ∈ S, Polynomial.Bivariate.evalY z (bivariateOf b) =
      qfun z * Polynomial.Bivariate.evalY z (bivariateOf a) := by
    intro z hz
    exact curveBivariate_row (e := e) (l := l) hdeg_pos hcol (q := qfun z) (B := Bfun z)
      (z := z) (qfun_spec z hz).1 (qfun_spec z hz).2.1 he2 (qfun_spec z hz).2.2
  -- Step 5: Polishchuk–Spielman.
  have hA_ne : bivariateOf a ≠ 0 := bivariateOf_ne_zero ha0
  have hdegXA : Polynomial.Bivariate.degreeX (bivariateOf a) ≤ e := by
    have h := degreeX_bivariateOf_le (m := e + 1) a
    simpa using h
  have hdegYA : Polynomial.Bivariate.natDegreeY (bivariateOf a) ≤ l * e :=
    natDegreeY_bivariateOf_le (d := l * e) a hadeg
  have hdegXB : Polynomial.Bivariate.degreeX (bivariateOf b) ≤ e + deg - 1 := by
    have h := degreeX_bivariateOf_le (m := e + deg) b
    omega
  have hdegYB : Polynomial.Bivariate.natDegreeY (bivariateOf b) ≤ l * (e + 1) :=
    natDegreeY_bivariateOf_le (d := l * (e + 1)) b hbdeg
  have hnpos : 0 < n := NeZero.pos n
  let P_x : Finset F := Finset.univ.map domain
  let P_y : Finset F := S
  have hPxcard : ((⟨n, hnpos⟩ : ℕ+) : ℕ) ≤ P_x.card := by simp [P_x]
  have hPycard : ((⟨S.card, hSpos⟩ : ℕ+) : ℕ) ≤ P_y.card := by simp [P_y]
  have hPxne : Nonempty P_x := Finset.Nonempty.to_subtype
    (Finset.card_pos.1 (lt_of_lt_of_le (PNat.pos ⟨n, hnpos⟩) hPxcard))
  let quot_x : F → Polynomial F := fun z => qfun z
  let quot_y : F → Polynomial F := fun x => curveParamPoly u (Function.invFun domain x)
  have hPyn : Nonempty P_y := Finset.Nonempty.to_subtype
    (Finset.card_pos.1 (lt_of_lt_of_le (PNat.pos ⟨S.card, hSpos⟩) hPycard))
  have hquot_x : ∀ y ∈ P_y, (quot_x y).natDegree ≤ (e + deg - 1 - e) ∧
      Polynomial.Bivariate.evalY y (bivariateOf b) =
        (quot_x y) * Polynomial.Bivariate.evalY y (bivariateOf a) := by
    intro y hy
    have hysz : y ∈ S := by simpa [P_y] using hy
    refine ⟨?_, hrow y hysz⟩
    change (qfun y).natDegree ≤ e + deg - 1 - e
    have h1 := (qfun_spec y hysz).1
    omega
  have hquot_y : ∀ x ∈ P_x, (quot_y x).natDegree ≤ (l * (e + 1) - l * e) ∧
      Polynomial.Bivariate.evalX x (bivariateOf b) =
        (quot_y x) * Polynomial.Bivariate.evalX x (bivariateOf a) := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hx
    have hinv : Function.invFun domain (domain i) = i := Function.leftInverse_invFun
      domain.injective i
    have hqy : quot_y (domain i) = curveParamPoly u i := by simp [quot_y, hinv]
    refine ⟨?_, ?_⟩
    · rw [hqy, Nat.mul_succ, Nat.add_sub_cancel_left]
      exact curveParamPoly_natDegree_le u i
    · rw [hqy]
      exact hcol i
  have hle1 : (1 : ℚ) > ((e + deg - 1 : ℕ) : ℚ) / ((⟨n, hnpos⟩ : ℕ+) : ℚ) +
      ((l * (e + 1) : ℕ) : ℚ) / ((⟨S.card, hSpos⟩ : ℕ+) : ℚ) := by
    have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hnpos
    have hSq : (0 : ℚ) < (S.card : ℚ) := by exact_mod_cast hSpos
    change (1 : ℚ) > ((e + deg - 1 : ℕ) : ℚ) / (n : ℚ) +
      ((l * (e + 1) : ℕ) : ℚ) / (S.card : ℚ)
    have hA : ((e + deg - 1 : ℕ) : ℚ) / (n : ℚ) ≤ ((n - e - 1 : ℕ) : ℚ) / (n : ℚ) := by
      refine div_le_div_of_nonneg_right ?_ (le_of_lt hnq)
      exact_mod_cast (show e + deg - 1 ≤ n - e - 1 by omega)
    have hB : ((l * (e + 1) : ℕ) : ℚ) / (S.card : ℚ) < ((e + 1 : ℕ) : ℚ) / (n : ℚ) := by
      rw [div_lt_div_iff₀ hSq hnq]
      have hmul : l * (e + 1) * n < (e + 1) * S.card := by
        rw [show l * (e + 1) * n = (e + 1) * (l * n) by ring]
        exact Nat.mul_lt_mul_of_pos_left hScard (by omega)
      have h1 : ((l * (e + 1) : ℕ) : ℚ) * (n : ℚ) = ((l * (e + 1) * n : ℕ) : ℚ) := by
        push_cast; ring
      have h2 : ((e + 1 : ℕ) : ℚ) * (S.card : ℚ) = ((e + 1) * S.card : ℕ) := by
        push_cast; ring
      rw [h1, h2]
      exact_mod_cast hmul
    have hC : ((n - e - 1 : ℕ) : ℚ) / (n : ℚ) + ((e + 1 : ℕ) : ℚ) / (n : ℚ) = 1 := by
      rw [← add_div]
      have h0 : ((n - e - 1 : ℕ) : ℚ) + ((e + 1 : ℕ) : ℚ) = (n : ℚ) := by
        have h1 : n - e - 1 + (e + 1) = n := by omega
        conv_rhs => rw [← h1, Nat.cast_add]
      rw [h0, div_self (ne_of_gt hnq)]
    linarith
  have hbx_ge : e + deg - 1 ≥ e := by omega
  have hby_ge : l * (e + 1) ≥ l * e := Nat.mul_le_mul_left l (by omega)
  obtain ⟨P, hBA, hPdegX, hPdegY, ⟨Q_x, hQx_card, hQx_sub, hQx_eval⟩, _⟩ :=
    polishchuk_spielman (a_x := e) (a_y := l * e) (b_x := e + deg - 1) (b_y := l * (e + 1))
      (n_x := ⟨n, hnpos⟩) (n_y := ⟨S.card, hSpos⟩)
      (h_bx_ge_ax := hbx_ge) (h_by_ge_ay := hby_ge)
      (A := bivariateOf a) (B := bivariateOf b) hA_ne hdegXA hdegXB hdegYA hdegYB
      P_x P_y quot_x quot_y hPxcard hPycard hquot_x hquot_y hle1
  -- Step 6: read off the code words.
  let J : Finset (Fin n) := Q_x.preimage domain domain.injective.injOn
  have hJcard : n - e ≤ J.card := by
    have himg : J.map domain = Q_x := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_map.1 hx with ⟨i, hi, rfl⟩
        exact Finset.mem_preimage.1 hi
      · intro hx
        rcases Finset.mem_map.1 (hQx_sub hx) with ⟨i, -, rfl⟩
        exact Finset.mem_map.2 ⟨i, Finset.mem_preimage.2 hx, rfl⟩
    have hcard_eq : J.card = Q_x.card := by
      calc J.card = (J.map domain).card := by simp
        _ = Q_x.card := by rw [himg]
    have hQx' : n - e ≤ Q_x.card := by simpa using hQx_card
    omega
  have hPdegX' : Polynomial.Bivariate.degreeX P ≤ deg - 1 := by
    have h1 : e + deg - 1 - e = deg - 1 := by omega
    rw [← h1]
    exact hPdegX
  let v : Fin (l + 1) → Fin n → F := fun i j => (P.coeff (i : ℕ)).eval (domain j)
  have hv_mem : ∀ i, v i ∈ ReedSolomon.code domain deg := by
    intro i
    have hcoeff_deg : (P.coeff (i : ℕ)).natDegree < deg := by
      have h1 : (P.coeff (i : ℕ)).natDegree ≤ deg - 1 :=
        (Polynomial.Bivariate.coeff_natDegree_le_degreeX P (i : ℕ)).trans hPdegX'
      omega
    exact ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval (P.coeff (i : ℕ))
      hcoeff_deg (fun j => rfl)
  have hJagree : ∀ j ∈ J, ∀ i, u i j = v i j := by
    intro j hj i
    have hx : domain j ∈ Q_x := Finset.mem_preimage.1 hj
    have hev : Polynomial.Bivariate.evalX (domain j) P = curveParamPoly u j := by
      have h1 := hQx_eval (domain j) hx
      have h2 : quot_y (domain j) = curveParamPoly u j := by
        simp [quot_y, Function.leftInverse_invFun domain.injective j]
      rwa [h2] at h1
    have hcoeff := congrArg (fun p : Polynomial F => p.coeff (i : ℕ)) hev
    rw [Polynomial.Bivariate.evalX_eq_map, Polynomial.coeff_map, Polynomial.coe_evalRingHom]
      at hcoeff
    have hc : (curveParamPoly u j).coeff (i : ℕ) = u i j := by
      rw [curveParamPoly, Polynomial.finsetSum_coeff]
      rw [Finset.sum_eq_single (s := Finset.univ) i]
      · rw [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial, ite_eq_left rfl]
      · intro t _ ht
        rw [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial, ite_eq_right]
        intro h
        exact ht (Fin.ext h)
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [hc] at hcoeff
    exact hcoeff.symm
  have hagree_all : ∀ j ∈ J, ∀ z : F,
      Curve.polynomialCurveEval (F := F) (A := F) u z j =
        Curve.polynomialCurveEval (F := F) (A := F) v z j := by
    intro j hj z
    simp only [Curve.polynomialCurveEval, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [hJagree j hj i]
  have hcurve_mem : ∀ z : F, Curve.polynomialCurveEval (F := F) (A := F) v z ∈
      ReedSolomon.code domain deg := by
    intro z
    have hmem : Curve.polynomialCurveEval (F := F) (A := F) v z =
        ∑ i : Fin (l + 1), z ^ (i : ℕ) • v i := rfl
    rw [hmem]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hv_mem i)
  have hcurve_close : ∀ z : F,
      δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z,
        Curve.polynomialCurveEval (F := F) (A := F) v z) ≤ δ := by
    intro z
    rw [Code.relCloseToWord_iff_exists_agreementCols]
    refine ⟨J, ?_, ?_⟩
    · have h1 : Nat.floor (δ * ↑(Fintype.card (Fin n))) = e := by
        rw [he]
        congr 1
        simp
      rw [h1]
      simpa using hJcard
    · intro colIdx
      constructor
      · intro hcol
        exact hagree_all colIdx hcol z
      · intro hne hcol
        exact hne (hagree_all colIdx hcol z)
  refine ⟨?_, v, hv_mem, hcurve_close, ?_⟩
  · apply Finset.eq_univ_of_forall
    intro z
    rw [hSmem z]
    have hcode := Code.relDistFromCode_le_relDist_to_mem
      (u := Curve.polynomialCurveEval (F := F) (A := F) u z)
      (C := (ReedSolomon.code domain deg : Set (Fin n → F)))
      (v := Curve.polynomialCurveEval (F := F) (A := F) v z) (hcurve_mem z)
    exact le_trans hcode (by exact_mod_cast hcurve_close z)
  · have hbad_subset : ({ x : Fin n | ∃ i, u i x ≠ v i x } : Finset _) ⊆
        (Finset.univ : Finset (Fin n)) \ J := by
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      rintro hxJ
      obtain ⟨i, hi⟩ := Finset.mem_filter.1 hx |>.2
      exact hi (hJagree x hxJ i)
    have hbad_card : ({ x : Fin n | ∃ i, u i x ≠ v i x } : Finset _).card ≤ e := by
      have h1 := Finset.card_le_card hbad_subset
      have h2 : ((Finset.univ : Finset (Fin n)) \ J).card = n - J.card := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
      rw [h2] at h1
      omega
    calc (({ x : Fin n | ∃ i, u i x ≠ v i x } : Finset _).card : ℝ≥0)
        ≤ (e : ℝ≥0) := by exact_mod_cast hbad_card
      _ ≤ δ * n := by
          rw [he]
          exact Nat.floor_le (by positivity)

omit [DecidableEq F] in
/-- Uniform sampling turns a strict probability bound into a strict cardinality bound. -/
private theorem card_filter_gt_of_prob_gt (P : F → Prop) [DecidablePred P] (B : ℝ)
    (hp : ENNReal.ofReal (B / Fintype.card F) < Pr{let z ← $ᵗ F}[P z]) :
    B < ((Finset.univ.filter P).card : ℝ) := by
  classical
  by_contra h
  have hc : ((Finset.univ.filter P).card : ℝ) ≤ B := le_of_not_gt h
  apply (not_lt_of_ge ?_) hp
  rw [SampleableType.prEvent_uniformSample]
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_div_of_pos hq]
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hc hq.le)

omit [Fintype F] [SampleableType F] in
/-- A close parameter with exact power agreement yields a common agreement set for all
coefficient words. -/
private theorem jointAgreement_of_exact_curve
    {ι : Type} [Fintype ι] [Nonempty ι] {deg l : ℕ} (domain : ι ↪ F)
    (u : Fin (l + 1) → ι → F) (δ : ℝ≥0) (hδ : δ ≤ 1) (z : F)
    (hz : δᵣ(ReedSolomon.powerBatchedWord u z,
      (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ)
    (hgood : ∀ P : Polynomial F, P.degree < deg →
      ⌈(Fintype.card ι : ℝ) * (1 - (δ : ℝ))⌉₊ ≤
        (ReedSolomon.polynomialAgreementSet domain (ReedSolomon.powerBatchedWord u z) P).card →
      ReedSolomon.HasExactPowerAgreement domain u (RingHom.id F) deg z P) :
    Code.jointAgreement (ReedSolomon.code domain deg) δ u := by
  classical
  obtain ⟨c, hc, hclose⟩ :=
    (Code.relCloseToCode_iff_relCloseToCodeword_of_minDist _ δ).mp hz
  obtain ⟨P, hP, hPc⟩ := ReedSolomon.mem_code_iff_eval.mp hc
  obtain ⟨S, hS, hagree⟩ := (Code.relCloseToWord_iff_exists_agreementCols _ _ _).mp hclose
  have hSNN := (Code.relDist_floor_bound_iff_complement_bound _ _ _).mp hS
  have hSR : (Fintype.card ι : ℝ) * (1 - (δ : ℝ)) ≤ S.card := by
    have hh := NNReal.coe_le_coe.mpr hSNN
    rw [NNReal.coe_mul, NNReal.coe_sub hδ] at hh
    push_cast at hh
    nlinarith only [hh]
  have hsub : S ⊆ ReedSolomon.polynomialAgreementSet domain
      (ReedSolomon.powerBatchedWord u z) P := by
    intro i hi
    rw [ReedSolomon.mem_polynomialAgreementSet]
    exact (hPc i).trans ((hagree i).1 hi).symm
  have hA := (Nat.ceil_le.mpr hSR).trans (Finset.card_le_card hsub)
  obtain ⟨polys, hpolys, _, hset⟩ :=
    (ReedSolomon.hasExactPowerAgreement_id_iff _ _ _ _ _).mp (hgood P hP hA)
  refine ⟨S, hSNN, fun t ↦ ReedSolomon.evalOnPoints domain (polys t), fun t ↦ ⟨?_, ?_⟩⟩
  · exact ReedSolomon.mem_code_iff_eval.mpr ⟨polys t, hpolys t, fun i ↦ rfl⟩
  · intro i hi
    have hi' := hsub hi
    rw [hset, ReedSolomon.mem_commonCurveAgreementSet] at hi'
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi' t⟩

/-- The distance bound from [BCIKS20]. -/
noncomputable def δ₀ (rho : ℝ) (m : ℕ) : ℝ :=
  1 - Real.sqrt rho - Real.sqrt rho / (2 * m)

omit sampleF in
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
  classical
  have hn : 0 < n := NeZero.pos n
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hs : (ReedSolomon.sqrtRate deg domain : ℝ) =
      Real.sqrt ((LinearCode.rate (ReedSolomon.code domain deg) : ℚ≥0) : ℝ) := by
    simp only [ReedSolomon.sqrtRate, Real.coe_sqrt]
    rfl
  have hspos : 0 < (ReedSolomon.sqrtRate deg domain : ℝ) :=
    ReedSolomon.sqrtRate_pos hdeg_pos
  have hδ' : (δ : ℝ) ≤ 1 - (1 + 1 / (2 * (m : ℝ))) *
      (ReedSolomon.sqrtRate deg domain : ℝ) := by
    rw [hs]
    unfold δ₀ at hδ
    convert hδ using 1
    ring
  have hproper : deg < n := by
    by_contra h
    have hfull : n ≤ deg := by omega
    have hrate : LinearCode.rate (ReedSolomon.code domain deg) = 1 := by
      rw [ReedSolomon.rateOfLinearCode_eq_min_div]
      simp only [Fintype.card_fin, min_eq_right hfull]
      exact div_self (by exact_mod_cast hn.ne')
    have hsone : (ReedSolomon.sqrtRate deg domain : ℝ) = 1 := by
      simp [ReedSolomon.sqrtRate, hrate]
    rw [hsone] at hδ'
    have := δ.coe_nonneg
    have hfrac : 0 < 1 / (2 * (m : ℝ)) := by positivity
    linarith
  obtain ⟨E, hE, hgood⟩ := exists_curve_exactPowerAgreement_explicit_budget
    deg domain l m (δ : ℝ) hdeg_pos (by simpa using hproper) hm δ.coe_nonneg hδ' u
  have hsmall : (E.card : ℝ) <
      (coeffs_of_close_proximity_curve (F := F) δ u
        (ReedSolomon.toFinset domain deg)).card := by
    apply hE.trans_lt
    convert hS using 1
    rw [Fintype.card_fin, hs,
      ReedSolomon.HiddenDerivative.sqrt_cube_eq_rpow_three_halves (by positivity),
      ReedSolomon.HiddenDerivative.legacy_shift_pow_seven m (by omega)]
    norm_num
    ring
  obtain ⟨z, hz, hzE⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show E.card < (coeffs_of_close_proximity_curve (F := F) δ u
      (ReedSolomon.toFinset domain deg)).card by exact_mod_cast hsmall)
  have hclose : δᵣ(ReedSolomon.powerBatchedWord u z,
      (ReedSolomon.code domain deg : Set (Fin n → F))) ≤ δ := by
    have hword : ReedSolomon.powerBatchedWord u z = Curve.polynomialCurveEval u z := by
      funext i
      simp [ReedSolomon.powerBatchedWord, Curve.polynomialCurveEval]
    rw [hword]
    simpa [coeffs_of_close_proximity_curve, ReedSolomon.toFinset,
      ReedSolomon.RScodeSet] using hz
  have hδone : δ ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    have hnonneg : 0 ≤ (1 + 1 / (2 * (m : ℝ))) *
        (ReedSolomon.sqrtRate deg domain : ℝ) := by positivity
    norm_num only [NNReal.coe_one]
    linarith
  obtain ⟨S, hSsize, v, hv⟩ := jointAgreement_of_exact_curve domain u δ hδone z hclose
    (hgood z hzE)
  refine ⟨v, fun i ↦ (hv i).1, ?_⟩
  have hsub : S ⊆ ({x : Fin n | ∀ i, u i x = v i x} : Finset _) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    exact (Finset.mem_filter.mp ((hv i).2 hx)).2.symm
  have hSsize' : (1 - δ) * n ≤ (S.card : ℝ≥0) := by simpa using hSsize
  exact hSsize'.trans (by exact_mod_cast Finset.card_le_card hsub)


end BCIKS20ProximityGapSection6

section CoreResults

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [SampleableType F] [DecidableEq F]


omit [DecidableEq ι] in
private theorem unique_curve_ca {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hdeg : 0 < deg) (hdeg_le : deg ≤ Fintype.card ι)
    (hUD : δ ≤ Code.relativeUniqueDecodingRadius (ReedSolomon.code domain deg : Set (ι → F)))
    (u : Fin (k + 1) → ι → F)
    (hprob : Pr{let z ← $ᵗ F}[δᵣ(∑ t : Fin (k + 1), z ^ (t : ℕ) • u t,
      (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ] > k * errorBound δ deg domain) :
    Code.jointAgreement (ReedSolomon.code domain deg) δ u := by
  classical
  let n := Fintype.card ι
  let e : Fin n ≃ ι := (Fintype.equivFin ι).symm
  let domain' := e.toEmbedding.trans domain
  let u' : Fin (k + 1) → Fin n → F := fun t ↦ u t ∘ e
  let : NeZero n := ⟨Fintype.card_ne_zero⟩
  let : NeZero deg := ⟨hdeg.ne'⟩
  have hUD' : δ ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code domain' deg : Set (Fin n → F)) := by
    rw [ReedSolomon.relativeUniqueDecodingRadius_RS_eq (by simpa [n] using hdeg_le)]
    rw [ReedSolomon.relativeUniqueDecodingRadius_RS_eq hdeg_le] at hUD
    simpa [n] using hUD
  let P : F → Prop := fun z ↦ δᵣ(∑ t : Fin (k + 1), z ^ (t : ℕ) • u t,
    (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ
  have hnumeric : ENNReal.ofReal ((k : ℝ) * n / Fintype.card F) <
      Pr{let z ← $ᵗ F}[P z] := by
    have herror : ENNReal.ofReal ((k : ℝ) * n / Fintype.card F) =
        (k : ENNReal) * (errorBound δ deg domain : ENNReal) := by
      rw [errorBound_eq_n_div_q_of_le_relUDR hUD,
        ENNReal.ofReal_div_of_pos (by exact_mod_cast Fintype.card_pos (α := F)),
        ENNReal.ofReal_mul (Nat.cast_nonneg k)]
      simp [n, div_eq_mul_inv, mul_assoc]
    rw [herror]
    exact hprob
  have hcount : n * k < (Finset.univ.filter P).card := by
    have hh := card_filter_gt_of_prob_gt P ((k : ℝ) * n) hnumeric
    have hh' : ((n * k : ℕ) : ℝ) < ((Finset.univ.filter P).card : ℝ) := by
      simpa [Nat.cast_mul, mul_comm] using hh
    exact_mod_cast hh'
  have hcurve (z : F) : Curve.polynomialCurveEval u' z =
      (∑ t : Fin (k + 1), z ^ (t : ℕ) • u t) ∘ e := by
    ext i
    simp [Curve.polynomialCurveEval, u']
  have hcoeff : coeffs_of_close_proximity_curve (F := F) δ u'
      (ReedSolomon.toFinset domain' deg) = Finset.univ.filter P := by
    ext z
    simp only [coeffs_of_close_proximity_curve, Set.mem_toFinset, Set.mem_ofPred_eq,
      Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [ReedSolomon.toFinset, ReedSolomon.RScodeSet, Set.coe_toFinset]
    rw [hcurve]
    exact relCloseToCode_comp_equiv e domain deg _ δ
  obtain ⟨_, v, hv, _, hbad⟩ := large_agreement_set_on_curve_implies_correlated_agreement
    hdeg (by simpa [n] using hdeg_le) hUD' (u := u') (by rwa [hcoeff])
  apply jointAgreement_of_comp_equiv e domain deg u δ
  let bad : Finset (Fin n) := {x | ∃ t, u' t x ≠ v t x}
  refine ⟨badᶜ, ?_, v, fun t ↦ ⟨hv t, ?_⟩⟩
  · apply (Code.relDist_floor_bound_iff_complement_bound _ _ _).mp
    simp only [Finset.card_compl, Fintype.card_fin]
    exact Nat.sub_le_sub_left (Nat.le_floor hbad) n
  · intro i hi
    have hi' : ¬ ∃ t, u' t i ≠ v t i := by simpa [bad] using hi
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, (not_ne_iff.mp fun h ↦ hi' ⟨t, h⟩).symm⟩

omit [DecidableEq ι] in
/-- Theorem 1.5 (Correlated agreement for low-degree parameterised curves) in [BCIKS20].

Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and a curve passing through words `u₀, ..., uκ`, such that
the probability that a random point on the curve is `δ`-close to the Reed-Solomon code
is greater than `k * ε`. Then, the words `u₀, ..., uκ` have correlated agreement.

A positive message dimension is required: the zero code does not satisfy this bound.
This statement is restricted to the proven open Johnson regime
`0 < δ < 1 - √ρ`. It does not encode the separate capacity-regime extension proposed as
Conjecture 8.4 of [BCIKS20]. -/
theorem correlatedAgreement_affine_curves {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hdeg_pos : 0 < deg)
    (hδ_pos : 0 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  intro u hprob
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  have hproper : deg < Fintype.card ι := by
    by_contra h
    have hfull : Fintype.card ι ≤ deg := by omega
    have hrate : LinearCode.rate (ReedSolomon.code domain deg) = 1 := by
      rw [ReedSolomon.rateOfLinearCode_eq_min_div, min_eq_right hfull]
      exact div_self (by exact_mod_cast hn.ne')
    have hsone : ReedSolomon.sqrtRate deg domain = 1 := by
      simp [ReedSolomon.sqrtRate, hrate]
    rw [hsone, tsub_self] at hδ
    exact (lt_irrefl 0) (hδ_pos.trans hδ)
  have hδone : δ ≤ 1 := hδ.le.trans tsub_le_self
  by_cases hUD : δ ≤ Code.relativeUniqueDecodingRadius
      (C := (ReedSolomon.code domain deg : Set (ι → F)))
  · exact unique_curve_ca hdeg_pos hproper.le hUD u hprob
  obtain ⟨E, hE, hgood⟩ := exists_curve_exactPowerAgreement_johnson_budget
    domain δ hdeg_pos hδ hUD u
  let B : ℝ := (k : ℝ) * (errorBound δ deg domain : ℝ) * Fintype.card F
  let P : F → Prop := fun z ↦ δᵣ(ReedSolomon.powerBatchedWord u z,
    (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ
  have hword (z : F) : ReedSolomon.powerBatchedWord u z =
      ∑ i : Fin (k + 1), z ^ (i : ℕ) • u i := by
    funext i
    simp [ReedSolomon.powerBatchedWord]
  have hp : ENNReal.ofReal (B / Fintype.card F) < Pr{let z ← $ᵗ F}[P z] := by
    have heq : ENNReal.ofReal (B / Fintype.card F) =
        ((k * errorBound δ deg domain : ℝ≥0) : ENNReal) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      congr 1
      simp only [NNReal.coe_mul, NNReal.coe_natCast]
      dsimp [B]
      have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      field_simp
    rw [heq]
    simpa [P, hword] using hprob
  have hcard := card_filter_gt_of_prob_gt P B hp
  have hlt : E.card < (Finset.univ.filter P).card := by exact_mod_cast hE.trans_lt hcard
  obtain ⟨z, hz, hzE⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact jointAgreement_of_exact_curve domain u δ hδone z (Finset.mem_filter.mp hz).2
    (hgood z hzE)


end CoreResults


end ProximityGap
