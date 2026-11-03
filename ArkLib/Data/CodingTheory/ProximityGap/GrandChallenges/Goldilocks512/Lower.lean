/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Ngo
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.CurveCertificate
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.Certificates
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.CurveMCA
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine
public import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges
public import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges.Goldilocks512.Arithmetic
public import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AgreementBounds
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.CodewordBound
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Safe-side grand-challenge witnesses for `RS[512, 128]` over Goldilocks cubic fields

Let `F` be a field of characteristic `p = 2 ^ 64 - 2 ^ 32 + 1` (the Goldilocks prime) with
`|F| = p ^ 3`, and let `domain : Fin 512 ↪ F` be any evaluation domain. For the Reed--Solomon
code `RS[F, domain, 128]` (rate `1/4`) at threshold `ε* = 2⁻¹²⁸`, this file constructs

* `mcaLowerWitness`: a `McaLowerWitness` at `δ = 273/512`;
* `listLowerWitness`: a `ListLowerWitness` at `δ = 273/512` for every interleaving `m ≥ 1`.

Agreement `239 = 512 - 273` is beyond the Johnson agreement `512 · √(1/4) = 256`.

## Proof outline

Both witnesses apply the first-order hidden-derivative certificate theorem
`exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount` with explicit parameters
`(m, M, μ, h)`; the required slot inequality is checked in `Goldilocks512.Arithmetic`.

* List decoding, `(546, 260, 1020, 10 ^ 9)`: the squarefree agreement bound gives at most
  `399 224 017` degree-`< 128` polynomials agreeing with any word on `239` points. The interleaved
  bound packs each column into the rational function field `F(Z)`
  (`ReedSolomon.Lambda_interleaved_le_ratFunc`), where the same scalar bound applies, so every
  interleaving has `Λ ≤ 399 224 017`, below `p ³ / 2 ¹²⁸`.
* Mutual correlated agreement, `(609, 280, 1148, 271 081)`: the retained squarefree line-agreement
  envelope gives at most `968 363 869 378 722 615` exceptional line parameters, below
  `p ³ / 2 ¹²⁸`.

The contribution here is the choice of parameters and the packaging; the mathematics is that of
the cited papers as already formalized in ArkLib.

## References

* [DKT26] for first-order hidden-derivative certificates and the squarefree bounds;
* [ABF26] for the grand-challenge formulation.
-/

@[expose] public section

open Polynomial ReedSolomon ReedSolomon.HiddenDerivative
open scoped NNReal

namespace ProximityGap.GrandChallenges.Goldilocks512

/-- The Goldilocks prime `2 ^ 64 - 2 ^ 32 + 1`. -/
def goldilocks : ℕ := 2 ^ 64 - 2 ^ 32 + 1

theorem sumRange_eq (N : ℕ) (f : ℕ → ℕ) :
    Arithmetic.sumRange N f = ∑ i ∈ Finset.range N, f i := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Finset.sum_range_succ, ← ih]; rfl

theorem height_eq (D A m M μ ℓ h : ℕ) :
    firstOrderCurveShiftedHeightSlotCount D A m M μ ℓ h =
      Arithmetic.heightSlotCount D A m M μ ℓ h := by
  simp only [firstOrderCurveShiftedHeightSlotCount, Arithmetic.heightSlotCount, sumRange_eq]

theorem row_eq (D A m M μ n ℓ h : ℕ) :
    firstOrderCurveShiftedRowSlotBound D A m M μ n ℓ h =
      Arithmetic.rowSlotBound D A m M μ n ℓ h := by
  simp only [firstOrderCurveShiftedRowSlotBound, Arithmetic.rowSlotBound,
    firstOrderGradedRankBound, Arithmetic.gradedRankBound, firstOrderGradedSourceCount,
    Arithmetic.gradedSourceCount, sumRange_eq]

/-- The slot inequality for the mutual-correlated-agreement parameters. -/
theorem mca_hheight :
    firstOrderCurveShiftedRowSlotBound 127 239 609 280 1148 512 1 271081 <
      firstOrderCurveShiftedHeightSlotCount 127 239 609 280 1148 1 271081 := by
  rw [row_eq, height_eq]
  exact Arithmetic.mca_cert

/-- The slot inequality for the list-decoding parameters. -/
theorem lst_hheight :
    firstOrderCurveShiftedRowSlotBound 127 239 546 260 1020 512 1 (10 ^ 9) <
      firstOrderCurveShiftedHeightSlotCount 127 239 546 260 1020 1 (10 ^ 9) := by
  rw [row_eq, height_eq]
  exact Arithmetic.lst_cert

universe u

/-- Over a field of Goldilocks characteristic, at most `399 224 017` polynomials of degree
`< 128` agree with a fixed word on at least `239` of `512` points. -/
theorem list_239 {F : Type u} [Field F] [DecidableEq F] (hp : ringChar F = goldilocks)
    (domain : Fin 512 ↪ F) (received : Fin 512 → F) (S : Finset F[X])
    (hS : ∀ P ∈ S, P.degree < 128 ∧
      239 ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    S.card ≤ 399224017 := by
  obtain ⟨cert⟩ := exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
    (F := F) (D := 127) (A := 239) (m := 546) (M := 260) (μ := 1020) (k := 128) (h := 10 ^ 9)
    (by norm_num) (by norm_num) (by norm_num) domain received (fun _ ↦ 0) lst_hheight
  have hchar : ringChar F = 0 ∨ max (128 - 1) 260 < ringChar F :=
    Or.inr (by rw [hp]; norm_num [goldilocks])
  have hcard := FirstOrder.Squarefree.firstOrder_finite_agreement_solutions_card_le_squarefree
    domain received _ cert (by norm_num) (by norm_num) (by norm_num) (by norm_num) hchar S
    (fun P hP ↦ ⟨(hS P hP).1, by convert (hS P hP).2⟩)
  have hval :
      ((firstOrderCurveFiberStageOne 128 1020 260 (regularTaylorExponent (128 - 1)) : ℕ) : ℝ) *
        ((512 - 128 + 1 : ℕ) : ℝ) / ((239 - 128 + 1 : ℕ) : ℝ) +
        (FirstOrder.Squarefree.ordinaryDegreeEnvelope 1020 260 : ℝ) = 798448035 / 2 := by
    have h1 :
        firstOrderCurveFiberStageOne 128 1020 260 (regularTaylorExponent (128 - 1)) =
          116003560 := by
      decide
    have h2 : FirstOrder.Squarefree.ordinaryDegreeEnvelope 1020 260 = 461780 := by decide
    rw [h1, h2]
    norm_num
  rw [hval] at hcard
  have : (S.card : ℝ) < 399224018 := by linarith
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)

/-- Over a field of Goldilocks characteristic, on every line `f + z • g`, outside at most
`968 363 869 378 722 615` exceptional `z`, every polynomial of degree `< 128` agreeing with the line
on at least `239` points has an exact correlated pair. -/
theorem mca_239 {F : Type u} [Field F] [DecidableEq F] (hp : ringChar F = goldilocks)
    (domain : Fin 512 ↪ F) (f g : Fin 512 → F) :
    ∃ exceptional : Finset F, (exceptional.card : ℝ) ≤ 968363869378722615 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < 128 →
        239 ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) 128 z P := by
  obtain ⟨cert⟩ := exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
    (F := F) (D := 127) (A := 239) (m := 609) (M := 280) (μ := 1148) (k := 128) (h := 271081)
    (by norm_num) (by norm_num) (by norm_num) domain f g mca_hheight
  have hchar : ringChar F = 0 ∨ max (128 - 1) 280 < ringChar F :=
    Or.inr (by rw [hp]; norm_num [goldilocks])
  obtain ⟨ex, hcard, hgood⟩ :=
    FirstOrder.Squarefree.exists_baseExceptional_retainedSquarefreeLineAgreement_of_certificate
      (E := AlgebraicClosure F) domain f g (algebraMap F (AlgebraicClosure F)) _ cert
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hchar
  refine ⟨ex, hcard.trans ?_, hgood⟩
  simp only [FirstOrder.Squarefree.retainedSquarefreeLineAgreementEnvelope,
    FirstOrder.Squarefree.retainedOrdinaryCurveAgreementCharge, agreementIncidenceRatio]
  norm_num

theorem mca_eps_lt : 968363869378722615 * 2 ^ 128 < goldilocks ^ 3 := by
  decide +kernel

theorem interleaved_numeric : 399224017 * 2 ^ 128 < goldilocks ^ 3 := by
  decide +kernel

/-- `mca_239` as a `LineExactAgreementBound`. -/
theorem lineExact_239 {F : Type} [Field F] [DecidableEq F] (hp : ringChar F = goldilocks)
    (domain : Fin 512 ↪ F) :
    LineExactAgreementBound domain 128 239 968363869378722615 := by
  intro f g
  obtain ⟨ex, hc, hg⟩ := mca_239 hp domain f g
  refine ⟨ex, hc, ?_⟩
  intro z hz P hP hA
  obtain ⟨pair, h0, h1, heq, hset⟩ := hg z hz P hP hA
  exact ⟨pair.1, pair.2, h0, h1, by simpa [correlatedPairSpecialization] using heq,
    by simpa using hset⟩

/-- Safe-side witness for the mutual-correlated-agreement grand challenge: for a field of
Goldilocks characteristic with `p ^ 3` elements and any `512`-point domain, `RS[F, domain, 128]`
has affine-line MCA error at most `2⁻¹²⁸` at `δ = 273/512`.

It is `noncomputable` because the witness carries real-valued error bounds. -/
noncomputable def mcaLowerWitness {F : Type} [Field F] [Fintype F] [SampleableType F]
    [DecidableEq F] (hp : ringChar F = goldilocks) (hcard : Fintype.card F = goldilocks ^ 3)
    (domain : Fin 512 ↪ F) :
    McaLowerWitness (ReedSolomon.code domain 128) (1 / 2 ^ 128) :=
  McaLowerWitness.ofLe (δ := 273 / 512) (by rw [← NNReal.coe_le_coe]; push_cast; norm_num) (by
    refine (mcaError_affineLine_le_of_exactAgreement domain _ (lineExact_239 hp domain)
      _ ?_).trans ?_
    · simp only [Fintype.card_fin]
      norm_num
    · rw [hcard]
      have hG0 : 0 < goldilocks ^ 3 := by unfold goldilocks; norm_num
      have hG : (0 : ℝ) < ((goldilocks ^ 3 : ℕ) : ℝ) := by exact_mod_cast hG0
      have h : ((968363869378722615 * 2 ^ 128 : ℕ) : ℝ) < ((goldilocks ^ 3 : ℕ) : ℝ) := by
        exact_mod_cast mca_eps_lt
      have key : (968363869378722615 : ℝ) / ((goldilocks ^ 3 : ℕ) : ℝ) ≤
          (((1 / 2 ^ 128 : ℝ≥0)) : ℝ) := by
        push_cast at h hG ⊢
        rw [div_le_div_iff₀ hG (by positivity)]
        linarith
      exact (ENNReal.ofReal_le_ofReal key).trans_eq ENNReal.ofReal_coe_nnreal)

open Classical in
/-- The list size of `RS[F, domain, 128]` at `δ = 273/512` is at most `399 224 017`. -/
theorem lambda_rs_le {F : Type} [Field F] (hp : ringChar F = goldilocks)
    (domain : Fin 512 ↪ F) :
    Code.Lambda (ReedSolomon.code domain 128 : Set (Fin 512 → F)) (273 / 512) ≤
      ((399224017 : ℕ) : ℕ∞) := by
  have hrad : capacityRadius (111 / 512) (Fintype.card (Fin 512)) 128 = 273 / 512 := by
    simp only [capacityRadius, Fintype.card_fin]; norm_num
  have hthr : capacityAgreementThreshold (111 / 512) (Fintype.card (Fin 512)) 128 = 239 := by
    simp only [capacityAgreementThreshold, Fintype.card_fin]; norm_num
  rw [← hrad]
  refine lambda_le_of_forall_agreeingPolynomials_encard_le (by norm_num) (by simp) _ ?_
  intro received
  rw [hthr]
  refine (agreeingPolynomials_encard_le_closePolynomialSet domain received).trans ?_
  have hfin := closePolynomialSet_finite domain received (show 128 ≤ 239 by norm_num)
  rw [Set.encard_le_coe_iff_finite_ncard_le]
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact list_239 hp domain received hfin.toFinset (fun P hP ↦ by
    have h := hfin.mem_toFinset.mp hP
    exact ⟨h.1, by simpa [polynomialAgreementSet] using h.2⟩)

open Classical in
/-- For every `m`, the `m`-fold interleaving of `RS[F, domain, 128]` has list size at most
`399 224 017` at `δ = 273/512`. Packing each column into `F(Z)` embeds the interleaved list into
a list of the scalar code over `F(Z)` (`ReedSolomon.Lambda_interleaved_le_ratFunc`), and
`lambda_rs_le` applies there because `F(Z)` has the same characteristic. -/
theorem lambda_interleaved_le {F : Type} [Field F] (hp : ringChar F = goldilocks)
    (domain : Fin 512 ↪ F) (m : ℕ) :
    Code.Lambda ((ReedSolomon.code domain 128 : Set (Fin 512 → F)) ^⋈ (Fin m)) (273 / 512) ≤
      ((399224017 : ℕ) : ℕ∞) := by
  have : CharP F goldilocks := by rw [← hp]; exact ringChar.charP F
  have : CharP (RatFunc F) goldilocks :=
    charP_of_injective_algebraMap (algebraMap F (RatFunc F)).injective goldilocks
  exact (ReedSolomon.Lambda_interleaved_le_ratFunc domain 128 m (273 / 512)).trans
    (lambda_rs_le (ringChar.eq (RatFunc F) goldilocks) _)

/-- Safe-side witness for the list-decoding grand challenge: for every `m ≥ 1`, the `m`-fold
interleaving of `RS[F, domain, 128]` has list size at most `2⁻¹²⁸ · |F|` at `δ = 273/512`
when `F` has Goldilocks characteristic and `p ^ 3` elements.

It is `noncomputable` because the witness carries real-valued error bounds. -/
noncomputable def listLowerWitness {F : Type} [Field F] [Fintype F] [SampleableType F]
    [DecidableEq F] (hp : ringChar F = goldilocks) (hcard : Fintype.card F = goldilocks ^ 3)
    (domain : Fin 512 ↪ F) (m : ℕ) (_hm : 1 ≤ m) :
    ListLowerWitness (ReedSolomon.code domain 128 : Set (Fin 512 → F)) m (1 / 2 ^ 128) :=
  ListLowerWitness.ofLe (δ := 273 / 512) (by rw [← NNReal.coe_le_coe]; push_cast; norm_num) (by
    have hδ : ((273 / 512 : ℝ≥0) : ℝ) = 273 / 512 := by push_cast; ring
    rw [hδ, hcard]
    have hI := lambda_interleaved_le hp domain m
    calc ((Code.Lambda ((ReedSolomon.code domain 128 : Set (Fin 512 → F)) ^⋈ (Fin m))
            (273 / 512) : ℕ∞) : ENNReal)
        ≤ (((399224017 : ℕ) : ℕ∞) : ENNReal) := by exact_mod_cast hI
      _ = ((399224017 : ℕ) : ENNReal) := by simp
      _ ≤ ((1 / 2 ^ 128 : ℝ≥0) : ENNReal) * ((goldilocks ^ 3 : ℕ) : ENNReal) := by
        rw [← ENNReal.coe_natCast, ← ENNReal.coe_natCast (goldilocks ^ 3), ← ENNReal.coe_mul,
          ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
        have h := (Nat.cast_lt (α := ℝ)).mpr interleaved_numeric
        push_cast at h ⊢
        linarith)

end ProximityGap.GrandChallenges.Goldilocks512
