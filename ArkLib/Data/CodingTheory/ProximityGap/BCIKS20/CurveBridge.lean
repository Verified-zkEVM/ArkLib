/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.JohnsonBridge
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Curves
public import ArkLib.Data.CodingTheory.ProximityGenerator.ExceptionalSet

/-!
# Exact polynomial-curve agreement on finite coordinate types

Coordinate reindexing transports the Johnson curve theorem from `Fin n` to any finite domain.
-/

@[expose] public section

namespace ProximityGap

open Polynomial ReedSolomon ReedSolomon.HiddenDerivative NNReal Code

/-- Exact power agreement is invariant under a bijection of coordinates. -/
theorem hasExactPowerAgreement_of_comp_equiv
    {ι κ F : Type} [Fintype ι] [Fintype κ] [Field F] [DecidableEq F]
    (e : κ ≃ ι) (domain : ι ↪ F) {ℓ k : ℕ} (w : Fin (ℓ + 1) → ι → F)
    (z : F) (Q : F[X])
    (h : HasExactPowerAgreement (e.toEmbedding.trans domain) (fun t ↦ w t ∘ e)
      (RingHom.id F) k z Q) :
    HasExactPowerAgreement domain w (RingHom.id F) k z Q := by
  classical
  obtain ⟨P, hP, heq, hset⟩ := (hasExactPowerAgreement_id_iff _ _ _ _ _).mp h
  refine (hasExactPowerAgreement_id_iff _ _ _ _ _).mpr ⟨P, hP, heq, ?_⟩
  ext i
  have hi := congrArg (e.symm i ∈ ·) hset
  simpa [mem_polynomialAgreementSet, commonCurveAgreementSet, powerBatchedWord] using hi

/-- The Johnson curve exception bound on an arbitrary finite evaluation domain. -/
theorem exists_johnson_curve_exactPowerAgreement_of_fintype
    {ι F : Type} [Fintype ι] [Field F] [decF : DecidableEq F]
    {D A ℓ : ℕ} {eta : ℝ}
    (domain : ι ↪ F) (values : Fin (ℓ + 1) → ι → F)
    (hD : 1 ≤ D) (hDn : D ≤ Fintype.card ι - 2) (heta : 0 < eta)
    (hthreshold : johnsonAgreement (Fintype.card ι) D eta * Fintype.card ι ≤ A)
    (hAn : A ≤ Fintype.card ι) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ 2 * ℓ *
        johnsonExceptionCount (Fintype.card ι) D A eta ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) (D + 1) z P := by
  have hdec : (fun a b : F ↦ Classical.propDecidable (a = b)) = decF := Subsingleton.elim _ _
  cases hdec
  classical
  let e := (Fintype.equivFin ι).symm
  obtain ⟨ex, hcard, hgood⟩ := exists_johnson_curve_exactPowerAgreement
    (e.toEmbedding.trans domain) (fun t ↦ values t ∘ e) hD hDn heta hthreshold hAn
  refine ⟨ex, hcard, fun z hz P hP hA ↦ ?_⟩
  apply hasExactPowerAgreement_of_comp_equiv e domain values z P
  apply hgood z hz P hP
  change A ≤ (polynomialAgreementSet (e.toEmbedding.trans domain)
    (powerBatchedWord values z ∘ e) P).card
  rwa [polynomialAgreementSet_card_comp_equiv]

open CoreDefinitions in
/-- A uniform exact-power exceptional set controls every subset in the MCA event at once.
The coefficient codewords retain the candidate's full agreement set, so restricting to an MCA
witness set introduces no union bound. -/
theorem mcaError_powers_le_of_exactPowerAgreement
    {ι F : Type} [Fintype ι] [Field F] [Fintype F] [SampleableType F]
    [DecidableEq F] (k : ℕ) (D : ι ↪ F) (d A : ℕ) (B radius : ℝ)
    (hthreshold : A ≤ ⌈(Fintype.card ι : ℝ) * (1 - radius)⌉₊)
    (h : ∀ U : Fin (d + 1) → ι → F, ∃ E : Finset F, (E.card : ℝ) ≤ B ∧
      ∀ z ∉ E, ∀ P : Polynomial F, P.degree < k →
        A ≤ (ReedSolomon.polynomialAgreementSet D (ReedSolomon.powerBatchedWord U z) P).card →
        ReedSolomon.HasExactPowerAgreement D U (RingHom.id F) k z P) :
    mcaError (univariatePowersGenerator F d) (ReedSolomon.code D k) radius ≤
      ENNReal.ofReal (B / Fintype.card F) := by
  classical
  apply mcaError_le_of_exists_exceptional_set
  intro U
  obtain ⟨E, hE, hgood⟩ := h U
  refine ⟨E, hE, fun z hz hbad ↦ ?_⟩
  have hnot : ¬ Code.IsProjectionBad (univariatePowersGenerator F d)
      (ReedSolomon.code D k) A z U := by
    apply Code.not_isProjectionBad_of_forall_hasExactAgreement
    intro c hc T hT hcT
    obtain ⟨P, hP, hPc⟩ := ReedSolomon.mem_code_iff_eval.mp hc
    have hc_eq : c = ReedSolomon.evalOnPoints D P := by
      funext i
      simp [ReedSolomon.evalOnPoints, hPc]
    subst c
    apply (ReedSolomon.hasExactPowerAgreement_id_iff_hasExactAgreement D U hP).mp
    apply hgood z hz P hP
    refine hT.trans (Finset.card_le_card fun i hi ↦ ?_)
    rw [ReedSolomon.mem_polynomialAgreementSet]
    simpa [ReedSolomon.evalOnPoints, ReedSolomon.powerBatchedWord] using hcT i hi
  obtain ⟨T, hT, hmem⟩ := (isMCA_iff_isProjectionBad _ _ _ _ _).mp hbad
  exact hnot ⟨T, hthreshold.trans hT, hmem⟩


/-- Reindexing preserves proximity to the Reed–Solomon code. -/
theorem relCloseToCode_comp_equiv
    {ι κ F : Type} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ] [Field F] [DecidableEq F]
    (e : κ ≃ ι) (domain : ι ↪ F) (k : ℕ) (w : ι → F) (δ : ℝ≥0) :
    Code.relDistFromCode (w ∘ e) (code (e.toEmbedding.trans domain) k) ≤ δ ↔
      Code.relDistFromCode w (code domain k) ≤ δ := by
  classical
  rw [Code.relCloseToCode_iff_relCloseToCodeword_of_minDist,
    Code.relCloseToCode_iff_relCloseToCodeword_of_minDist]
  constructor
  · rintro ⟨v, hv, hclose⟩
    change v ∈ code (e.toEmbedding.trans domain) k at hv
    refine ⟨v ∘ e.symm, ?_, ?_⟩
    · apply (mem_code_comp_equiv e domain k (v ∘ e.symm)).mp
      simpa only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] using hv
    · have heq : Code.relHammingDist w (v ∘ e.symm) =
          Code.relHammingDist (w ∘ e) v := by
        simpa only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using
          relHammingDist_comp_equiv e.symm (w ∘ e) v
      rwa [heq]
  · rintro ⟨v, hv, hclose⟩
    exact ⟨v ∘ e, (mem_code_comp_equiv e domain k v).mpr hv,
      by rwa [relHammingDist_comp_equiv]⟩

/-- A common agreement set transports along a bijection of coordinates. -/
theorem jointAgreement_of_comp_equiv
    {ι κ F : Type} [Fintype ι] [Fintype κ] [Field F] [DecidableEq F]
    {τ : Type} (e : κ ≃ ι) (domain : ι ↪ F) (k : ℕ)
    (w : τ → ι → F) (δ : ℝ≥0)
    (h : jointAgreement (C := code (e.toEmbedding.trans domain) k)
      (W := fun t ↦ w t ∘ e) δ) :
    jointAgreement (C := code domain k) (W := w) δ := by
  classical
  obtain ⟨S, hS, v, hv⟩ := h
  refine ⟨S.map e.toEmbedding, ?_, fun t ↦ v t ∘ e.symm, fun t ↦ ⟨?_, ?_⟩⟩
  · simpa only [Finset.card_map, Fintype.card_congr e] using hS
  · apply (mem_code_comp_equiv e domain k (v t ∘ e.symm)).mp
    have hmem : v t ∈ code (e.toEmbedding.trans domain) k := (hv t).1
    simpa only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] using hmem
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    have hj' := (Finset.mem_filter.mp ((hv t).2 hj)).2
    simpa using hj'


/-- For a fixed tuple of message polynomials, at most `ℓ * |ι|` challenges can have agreement
beyond the common coefficient agreement set. -/
theorem exists_exceptional_exactPowerAgreement_of_polynomials
    {ι F : Type} [Fintype ι] [Field F] [DecidableEq F]
    {ℓ k : ℕ} (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F)
    (P : Fin (ℓ + 1) → F[X]) (hP : ∀ t, (P t).degree < k) :
    ∃ E : Finset F, E.card ≤ ℓ * Fintype.card ι ∧
      ∀ z ∉ E, HasExactPowerAgreement domain w (RingHom.id F) k z
        (Polynomial.powerBatch P z) := by
  classical
  let diff : ι → F[X] := fun i ↦ powerBatchedCoordinate (fun t ↦ (P t).eval (domain i) - w t i)
  let E := Finset.univ.biUnion (fun i ↦ (diff i).roots.toFinset)
  have heval (i : ι) (z : F) : (diff i).eval z =
      (Polynomial.powerBatch P z).eval (domain i) - powerBatchedWord w z i := by
    simp only [diff, powerBatchedCoordinate_eval, Polynomial.powerBatch_eval,
      powerBatchedWord, mul_sub, Finset.sum_sub_distrib]
  refine ⟨E, ?_, fun z hz ↦ ?_⟩
  · calc
      E.card ≤ ∑ i : ι, (diff i).roots.toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ _i : ι, ℓ := Finset.sum_le_sum fun i _ ↦
        (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans
          (powerBatchedCoordinate_natDegree_le _))
      _ = ℓ * Fintype.card ι := by simp [Nat.mul_comm]
  · refine (hasExactPowerAgreement_id_iff _ _ _ _ _).mpr ⟨P, hP, rfl, ?_⟩
    apply Finset.Subset.antisymm ?_
      (fun i hi ↦ by
        rw [mem_polynomialAgreementSet, Polynomial.powerBatch_eval]
        apply Finset.sum_congr rfl
        intro t _
        rw [(mem_commonCurveAgreementSet domain w P i).mp hi t])
    intro i hi
    have hzero : diff i = 0 := by
      by_contra hne
      apply hz
      apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_univ i, ?_⟩
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot.def, heval]
      exact sub_eq_zero.mpr ((mem_polynomialAgreementSet _ _ _ _).mp hi)
    have heq : (fun t ↦ (P t).eval (domain i) - w t i) = 0 := by
      exact (powerBatchedCoordinate_eq_zero_iff _).mp hzero
    simp only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
    intro t
    exact sub_eq_zero.mp (congrFun heq t)


/-- The rounded integer agreement threshold is exactly the relative-distance condition. -/
theorem ceil_le_polynomialAgreementSet_card_iff
    {ι F : Type} [Fintype ι] [Nonempty ι] [Field F] [DecidableEq F]
    (domain : ι ↪ F) (w : ι → F) (P : F[X]) (δ : ℝ≥0) (hδ : δ ≤ 1) :
    ⌈(Fintype.card ι : ℝ) * (1 - (δ : ℝ))⌉₊ ≤ (polynomialAgreementSet domain w P).card ↔
      (Code.relHammingDist w (evalOnPoints domain P) : ℝ≥0) ≤ δ := by
  classical
  rw [Nat.ceil_le, Code.relCloseToWord_iff_exists_agreementCols]
  have hcast (S : Finset ι) :
      (Fintype.card ι : ℝ) * (1 - (δ : ℝ)) ≤ S.card ↔
        (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ S.card := by
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_sub hδ]
    push_cast
    rw [mul_comm]
  constructor
  · intro h
    refine ⟨polynomialAgreementSet domain w P,
      (Code.relDist_floor_bound_iff_complement_bound _ _ _).mpr ((hcast _).mp h), ?_⟩
    intro i
    constructor
    · intro hi
      exact ((mem_polynomialAgreementSet _ _ _ _).mp hi).symm
    · intro hne hi
      exact hne ((mem_polynomialAgreementSet _ _ _ _).mp hi).symm
  · rintro ⟨S, hS, hagree⟩
    have hsub : S ⊆ polynomialAgreementSet domain w P := by
      intro i hi
      exact (mem_polynomialAgreementSet _ _ _ _).mpr ((hagree i).1 hi).symm
    exact ((hcast _).mpr ((Code.relDist_floor_bound_iff_complement_bound _ _ _).mp hS)).trans
      (by exact_mod_cast Finset.card_le_card hsub)

end ProximityGap
