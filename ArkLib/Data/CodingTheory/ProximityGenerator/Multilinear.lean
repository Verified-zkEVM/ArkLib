/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ProximityGenerator.MultilinearBasic
public import ArkLib.Data.CodingTheory.ProximityGenerator.TensorGenerator
public import ArkLib.Data.CodingTheory.ProximityGenerator.MCAGenerator
public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.EpsCa
public import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.JohnsonMca

/-!
# Multilinear monomial generators

Iterated tensor products of `(1,rᵢ)` generate the squarefree monomial basis.
The tensor MCA bound costs `t` times the affine-line MCA error.
For Reed–Solomon codes the unique-decoding bound gives `t * n / |F|`.
The proved Gao–Kopparty–Lovett 1.5-Johnson bound supplies an additional regime through
`caError_multilinearBatch_le_johnson`. Both are instances of the pointwise MCA transport.
-/

@[expose] public section

namespace CoreDefinitions

open scoped NNReal ENNReal ProbabilityTheory
open OracleComp

variable {F ι A : Type} [Field F] [Fintype F] [SampleableType F]
variable [Fintype ι] [AddCommMonoid A] [Module F A]

/-- Tensor MCA bound for the monomial basis; each step uses the proved tensor union bound. -/
theorem isMCAGenerator_multilinear (MC : ModuleCode ι F A)
    (ε : unitInterval → ℝ≥0) (h : IsMCAGenerator (AffineLineGenerator F) ε MC) (t : ℕ) :
    IsMCAGenerator (multilinearGenerator F t) (t • ε) MC := by
  induction t with
  | zero =>
    intro δ
    simp only [zero_smul, Pi.zero_apply, ENNReal.coe_zero]
    apply iSup_le
    intro U
    apply le_of_eq
    apply prEvent_eq_zero_of_forall_mem_support
    intro x _ hx
    obtain ⟨T, _, hmem, j, hj⟩ := hx
    have hj0 : j = 0 := Fin.eq_zero j
    subst j
    exact hj (by simpa [multilinearGenerator, LinearCode.projectedWord] using hmem)
  | succ t ih =>
    have ht := LinearTransformations.isMCAGenerator_tensorGenerator_tight MC
      (AffineLineGenerator F) ε h (multilinearGenerator F t) (t • ε) ih
    have hr := LinearTransformations.isMCAGenerator_reindex MC _ _ ht
      (Fin.consEquiv (fun _ : Fin (t + 1) => F)).symm (multilinearIndex t)
    rw [show ε + t • ε = (t + 1) • ε by rw [add_comm, add_nsmul, one_nsmul]] at hr
    exact hr

end CoreDefinitions

namespace ProximityGap

open CoreDefinitions
open scoped NNReal ENNReal

variable {F ι : Type} [Field F] [Fintype F] [SampleableType F] [DecidableEq F]
variable [Fintype ι] [Nonempty ι]

omit [Field F] [Fintype F] [SampleableType F] in
/-- A relative unique-decoding radius is at most one. -/
lemma relativeUniqueDecodingRadius_le_one (C : Set (ι → F)) :
    Code.relativeUniqueDecodingRadius C ≤ 1 := by
  have hn : (0 : ℝ≥0) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold Code.relativeUniqueDecodingRadius
  apply (div_le_one hn).mpr
  calc
    ((Code.dist C : ℝ≥0) - 1) / 2 ≤ (Code.dist C : ℝ≥0) - 1 :=
      div_le_self (by positivity) (by norm_num)
    _ ≤ Code.dist C := tsub_le_self
    _ ≤ Fintype.card ι := by exact_mod_cast Code.dist_le_card C

/-- Multilinear batching in the unique-decoding regime, using the proved affine-line
MCA estimate. The resulting error is `t * n / |F|`; no Johnson-range MCA
estimate is assumed. -/
theorem caError_multilinear_le (t : ℕ) {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδ_pos : 0 < δ)
    (hδ : δ ≤ Code.relativeUniqueDecodingRadius (ReedSolomon.code domain deg).carrier) :
    caError (multilinearGenerator F t) (ReedSolomon.code domain deg).carrier δ δ ≤
      ((t * (Fintype.card ι / Fintype.card F) : ℝ≥0) : ENNReal) := by
  let C := ReedSolomon.code domain deg
  let ε : unitInterval → ℝ≥0 := fun r => (mcaError (AffineLineGenerator F) C r).toNNReal
  have hline : IsMCAGenerator (AffineLineGenerator F) ε C := by
    intro r
    exact (ENNReal.coe_toNNReal (mcaError_ne_top _ _ _)).ge
  have ht := isMCAGenerator_multilinear C ε hline t
    ⟨δ, by exact_mod_cast δ.coe_nonneg,
      by exact_mod_cast hδ.trans (relativeUniqueDecodingRadius_le_one _)⟩
  apply (caError_le_mcaError _ C δ).trans (ht.trans _)
  simp only [Pi.smul_apply, nsmul_eq_mul, ENNReal.coe_mul, ENNReal.coe_natCast]
  apply mul_le_mul' le_rfl
  dsimp [ε]
  rw [ENNReal.coe_toNNReal (mcaError_ne_top _ _ _)]
  exact rs_mcaError_le_of_le_relUDR hδ_pos hδ

/-- Any proved affine-line MCA bound transports to multilinear batching, with one
copy of the error per tensor factor. -/
theorem caError_multilinearBatch_le_of_mca (t : ℕ) (C : LinearCode ι F)
    (δ ε₀ : ℝ≥0) (hδ : δ ≤ 1)
    (hε : mcaError (AffineLineGenerator F) C δ ≤ ε₀) :
    caError (multilinearBatchGenerator F t) C.carrier δ δ ≤ (t * ε₀ : ℝ≥0) := by
  let ε : unitInterval → ℝ≥0 := fun r => (mcaError (AffineLineGenerator F) C r).toNNReal
  have hline : IsMCAGenerator (AffineLineGenerator F) ε C := by
    intro r
    exact (ENNReal.coe_toNNReal (mcaError_ne_top _ _ _)).ge
  have ht := LinearTransformations.isMCAGenerator_reindex C _ _
    (isMCAGenerator_multilinear C ε hline t) (Equiv.refl (Fin t → F))
    (finCongr (Nat.sub_add_cancel (Nat.one_le_two_pow)).symm)
  have hb := ht ⟨δ, by exact_mod_cast δ.coe_nonneg, by exact_mod_cast hδ⟩
  apply (caError_le_mcaError _ C δ).trans (hb.trans _)
  simp only [Pi.smul_apply, nsmul_eq_mul, ENNReal.coe_mul, ENNReal.coe_natCast]
  apply mul_le_mul' le_rfl
  dsimp [ε]
  rw [ENNReal.coe_toNNReal (mcaError_ne_top _ _ _)]
  exact hε

/-- The proved Gao–Kopparty–Lovett affine-line MCA error, as a nonnegative bound.
Its hypotheses and 1.5-Johnson radius are supplied by `caError_multilinearBatch_le_johnson`. -/
noncomputable def affineLineMcaJohnsonError (N q : ℕ) (δ_min η : ℝ≥0) : ℝ≥0 :=
  (((((N : ℝ) + 6) / η
    + 2 / ((η : ℝ) *
        ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3)
          - (1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 2)))) / q)).toNNReal

/-- Multilinear batching below the proved 1.5-Johnson radius, for any linear code.
This uses the Gao–Kopparty–Lovett bound, not the separate Reed–Solomon Johnson conjecture. -/
theorem caError_multilinearBatch_le_johnson (t : ℕ) (C : LinearCode ι F)
    (δ_min η δ : ℝ≥0)
    (hdist : (δ_min : ℝ) = (Code.minDist C.carrier : ℝ) / Fintype.card ι)
    (hη : 0 < η) (hη_lt : η < δ_min) (hδ_pos : 0 < δ)
    (hδ : (δ : ℝ) ≤ 1 - (1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3)) :
    caError (multilinearBatchGenerator F t) C.carrier δ δ ≤
      (t * affineLineMcaJohnsonError (Fintype.card ι) (Fintype.card F) δ_min η : ℝ≥0) := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hmin : (δ_min : ℝ) ≤ 1 := by
    rw [hdist]
    apply (div_le_one hn).mpr
    rw [← Code.dist_eq_minDist]
    exact_mod_cast Code.dist_le_card C.carrier
  have hx : 0 ≤ 1 - (δ_min : ℝ) + (η : ℝ) := by positivity
  have hδone : δ ≤ 1 := by
    exact_mod_cast hδ.trans (sub_le_self _ (Real.rpow_nonneg hx _))
  apply caError_multilinearBatch_le_of_mca t C δ _ hδone
  simpa only [affineLineMcaJohnsonError, ENNReal.coe_toNNReal, ENNReal.ofReal] using
    CodingTheory.linear_mcaError_le_one_point_five_johnson C δ_min η δ
      hdist hη hη_lt hδ_pos hδ

/-- The unique-decoding bound in the `m + 1` indexing used by Batched FRI. -/
theorem caError_multilinearBatch_le (t : ℕ) {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδ_pos : 0 < δ)
    (hδ : δ ≤ Code.relativeUniqueDecodingRadius (ReedSolomon.code domain deg).carrier) :
    caError (multilinearBatchGenerator F t) (ReedSolomon.code domain deg).carrier δ δ ≤
      ((t * (Fintype.card ι / Fintype.card F) : ℝ≥0) : ENNReal) := by
  exact caError_multilinearBatch_le_of_mca t _ δ _
    (hδ.trans (relativeUniqueDecodingRadius_le_one _))
    (rs_mcaError_le_of_le_relUDR hδ_pos hδ)

end ProximityGap
