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
public import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AgreementBounds
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.CodewordBound
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.CosetList
public import ArkLib.Data.CodingTheory.ListDecodability.SymbolMap
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Certificate witnesses for the grand challenges

This file turns first-order hidden-derivative certificates and the coset construction into the
one-sided witnesses of `ProximityGap.GrandChallenges`, for any field and any `(n, k, A)`.

## Main results

* `lineExactAgreementBound_of_heightSlotCount`: certificate parameters satisfying the slot
  inequality give an exact-agreement bound on every line.
* `McaLowerWitness.ofLineExactAgreement`: such a bound below `ε* · |F|` gives a safe MCA witness.
* `lambda_interleaved_le_of_heightSlotCount`: certificate parameters bound the list size of
  `RS[n, k]` for every interleaving width.
* `ListUpperWitness.ofCosetList`: on the domain of powers of a primitive `n`-th root of unity, the
  coset list of `ReedSolomon.CosetList.exists_le_encard_closeCodewordsRel` gives an unsafe list
  witness.

## Instantiating over a field

To certify `RS[n, k]` over a field `F` at threshold `ε*`:

1. Safe side. Choose an agreement threshold `A` with `k ≤ A ≤ n` and first-order certificate
   parameters `(m, M, μ, h)`, and check the slot inequality
   `firstOrderCurveShiftedRowSlotBound (k - 1) A m M μ n 1 h <
     firstOrderCurveShiftedHeightSlotCount (k - 1) A m M μ 1 h`.
   It is a closed computation on natural numbers. Small instances close it by `decide`. For
   large ones, `scripts/grand_challenges/gen_slot_arithmetic.py` generates a module that proves
   it, in exactly this form, by checking blocks of the sums with `decide +kernel` over the
   restatements of `GrandChallenges.SlotArithmetic`. Then
   `lineExactAgreementBound_of_heightSlotCount` gives a line bound `B`, and
   `McaLowerWitness.ofLineExactAgreement` gives the witness once `B ≤ ε* · |F|`.
   `lambda_interleaved_le_of_heightSlotCount` does the same for list decoding, for every
   interleaving width.
2. Unsafe side. On the domain of powers of a primitive `n`-th root of unity, the coset
   construction gives a list of size `⌊C(n/s - 1, r) / (n/s)⌋`, hence a `ListUpperWitness` once
   `ε* · |F|` is smaller (`ListUpperWitness.ofCosetList`). For a `McaUpperWitness`, the
   list-to-correlated-agreement transfer `CodingTheory.rs_Lambda_extended_le_of_epsCa` turns the
   list into a lower bound on the correlated-agreement error. No generic theorem packages this
   step yet; `Goldilocks512.epsCa_gt` carries it out for `n = 512`.
3. Field facts. Only `ringChar F`, `|F|` and, for the unsafe side, a primitive `n`-th root of
   unity enter. For a concrete field, prove them once: for example `GaloisField p d` with a
   primality certificate for `p`.

Worked example: `RS[512, 128]` at `ε* = 2⁻¹²⁸` over a field with `p ^ 3` elements,
`p = 2 ^ 64 - 2 ^ 32 + 1`, is safe at `δ = 273/512` with `A = 239` and parameters
`(609, 280, 1148, 271081)` (MCA) and `(546, 260, 1020, 10 ^ 9)` (list decoding), and unsafe at
`δ = 377/512` with `s = 4`, `r = 33`. The modules `GrandChallenges.Goldilocks512.*` carry it out.

## References

* [DKT26] for first-order hidden-derivative certificates and the squarefree bounds;
* [Kin26] for the coset construction on multiplicative subgroups;
* [ABF26] for the grand-challenge formulation.
-/

@[expose] public section

open Polynomial ReedSolomon ReedSolomon.HiddenDerivative
open scoped NNReal

namespace ProximityGap.GrandChallenges

/-- First-order certificate parameters `(m, M, μ, h)` that satisfy the slot inequality give an
exact-agreement bound on every line, over any field whose characteristic is `0` or exceeds
`max (k - 1) M`. -/
theorem lineExactAgreementBound_of_heightSlotCount {F : Type} [Field F] [DecidableEq F]
    {n k A m M μ h : ℕ} (domain : Fin n ↪ F)
    (hk : 2 ≤ k) (hkA : k ≤ A) (hAn : A ≤ n) (hM : 1 ≤ M) (hMμ : M ≤ μ) (hbudget : 0 < m * A)
    (hheight : firstOrderCurveShiftedRowSlotBound (k - 1) A m M μ n 1 h <
      firstOrderCurveShiftedHeightSlotCount (k - 1) A m M μ 1 h)
    (hchar : ringChar F = 0 ∨ max (k - 1) M < ringChar F) :
    LineExactAgreementBound domain k A
      (FirstOrder.Squarefree.retainedSquarefreeLineAgreementEnvelope
        (agreementIncidenceRatio n (k - 1) A) n (k - 1) μ M h) := by
  intro f g
  obtain ⟨cert⟩ := exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
    (F := F) (D := k - 1) (A := A) (m := m) (M := M) (μ := μ) (k := k) (h := h)
    (by omega) hbudget (by omega) domain f g hheight
  obtain ⟨ex, hcard, hgood⟩ :=
    FirstOrder.Squarefree.exists_baseExceptional_retainedSquarefreeLineAgreement_of_certificate
      (E := AlgebraicClosure F) domain f g (algebraMap F (AlgebraicClosure F)) _ cert
      hk hkA hAn hM hMμ hchar
  refine ⟨ex, hcard, fun z hz P hP hA ↦ ?_⟩
  obtain ⟨pair, h0, h1, heq, hset⟩ := hgood z hz P hP hA
  exact ⟨pair.1, pair.2, h0, h1, by simpa [correlatedPairSpecialization] using heq,
    by simpa using hset⟩

/-- A line exact-agreement bound `B` with `B ≤ ε* · |F|` gives a safe MCA witness at every
radius `δ` whose agreement threshold `⌈n (1 - δ)⌉` is at least `A`. -/
noncomputable def McaLowerWitness.ofLineExactAgreement {ι F : Type} [Fintype ι] [Nonempty ι]
    [Field F] [Fintype F] [SampleableType F] [DecidableEq F] {k A : ℕ} (domain : ι ↪ F)
    {B : ℝ} {ε_star δ : ℝ≥0} (hline : LineExactAgreementBound domain k A B) (hδ : δ ≤ 1)
    (hA : A ≤ ⌈(Fintype.card ι : ℝ) * (1 - δ)⌉₊) (hB : B ≤ ε_star * Fintype.card F) :
    McaLowerWitness (ReedSolomon.code domain k) ε_star :=
  McaLowerWitness.ofLe hδ ((mcaError_affineLine_le_of_exactAgreement domain B hline δ hA).trans
    (by
      rw [ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top, ENNReal.coe_toReal,
        div_le_iff₀ (by exact_mod_cast Fintype.card_pos)]
      exact hB))

/-- First-order certificate parameters that satisfy the slot inequality bound the list of
`RS[n, k]` at agreement threshold `A`, for every interleaving width, over any field whose
characteristic is `0` or exceeds `max (k - 1) M`. Packing columns into `F(Z)` keeps the
characteristic, so the scalar certificate applies there. -/
theorem lambda_interleaved_le_of_heightSlotCount {F : Type} [Field F] {n k m M μ h : ℕ}
    (η : ℝ) (hη : 0 ≤ η) (hn : 0 < n) (domain : Fin n ↪ F) (t L : ℕ)
    (hk : 2 ≤ k) (hkA : k ≤ capacityAgreementThreshold η n k)
    (hAn : capacityAgreementThreshold η n k ≤ n) (hMμ : M ≤ μ)
    (hbudget : 0 < m * capacityAgreementThreshold η n k)
    (hheight : firstOrderCurveShiftedRowSlotBound (k - 1) (capacityAgreementThreshold η n k)
        m M μ n 1 h <
      firstOrderCurveShiftedHeightSlotCount (k - 1) (capacityAgreementThreshold η n k) m M μ 1 h)
    (hchar : ringChar F = 0 ∨ max (k - 1) M < ringChar F)
    (hL : (firstOrderCurveFiberStageOne k μ M (regularTaylorExponent (k - 1)) : ℝ) *
        ((n - k + 1 : ℕ) : ℝ) / (capacityAgreementThreshold η n k - k + 1 : ℕ) +
        FirstOrder.Squarefree.ordinaryDegreeEnvelope μ M < L + 1) :
    Code.Lambda ((ReedSolomon.code domain k : Set (Fin n → F)) ^⋈ (Fin t))
      (capacityRadius η n k) ≤ (L : ℕ∞) := by
  classical
  set A := capacityAgreementThreshold η n k with hA
  let K := RatFunc F
  have hcharK : ringChar K = 0 ∨ max (k - 1) M < ringChar K := by
    have : CharP F (ringChar F) := ringChar.charP F
    have : CharP K (ringChar F) :=
      charP_of_injective_algebraMap (algebraMap F K).injective _
    rwa [ringChar.eq K (ringChar F)]
  refine (ReedSolomon.Lambda_interleaved_le_ratFunc domain k t _).trans ?_
  set dK : Fin n ↪ K := domain.trans ⟨algebraMap F K, (algebraMap F K).injective⟩
  have key := lambda_le_of_forall_agreeingPolynomials_encard_le (domain := dK) (messageDim := k)
    hη (by simpa using hn) (L : ℕ∞) ?_
  · simpa only [Fintype.card_fin] using key
  intro received
  simp only [Fintype.card_fin]
  refine (agreeingPolynomials_encard_le_closePolynomialSet dK received).trans ?_
  have hfin := closePolynomialSet_finite dK received hkA
  rw [Set.encard_le_coe_iff_finite_ncard_le]
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  obtain ⟨cert⟩ := exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
    (F := K) (D := k - 1) (A := A) (m := m) (M := M) (μ := μ) (k := k) (h := h)
    (by omega) hbudget (by omega) dK received (fun _ ↦ 0) hheight
  have hS := FirstOrder.Squarefree.firstOrder_finite_agreement_solutions_card_le_squarefree
    dK received _ cert hk hkA hAn hMμ hcharK hfin.toFinset (fun P hP ↦ by
      have hP' := hfin.mem_toFinset.mp hP
      exact ⟨hP'.1, by simpa [polynomialAgreementSet] using hP'.2⟩)
  have : (hfin.toFinset.card : ℝ) < L + 1 := hS.trans_lt hL
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)

/-- On the domain of powers of a primitive `n`-th root of unity, the coset list of
`ReedSolomon.CosetList.exists_le_encard_closeCodewordsRel` gives an unsafe list witness for every
interleaving width `m ≥ 1`, at the radius `δ = (n - (s r + s - 1)) / n`, once `ε* · |F|` is below
`⌊C(n/s - 1, r) / (n/s)⌋`.

It is `noncomputable` because the received word is chosen by `Classical.choose`. -/
noncomputable def ListUpperWitness.ofCosetList {F : Type} [Field F] [Fintype F]
    [SampleableType F] [DecidableEq F] {ω : F} {n s r k : ℕ} (hω : IsPrimitiveRoot ω n)
    (hsn : s ∣ n) (hr : 1 ≤ r) (hdeg : s * (r - 1) ≤ k) {ε_star δ : ℝ≥0}
    (hδ : (δ : ℝ) = ((n : ℝ) - (s * r + s - 1 : ℕ)) / n) (m : ℕ) (hm : 1 ≤ m)
    (hnum : (ε_star : ENNReal) * (Fintype.card F : ENNReal) <
      ((Nat.choose (n / s - 1) r / (n / s) : ℕ) : ENNReal)) :
    ListUpperWitness (ReedSolomon.code (primitiveRootDomain hω) k : Set (Fin n → F)) m
      ε_star :=
  ListUpperWitness.ofEncardGt (δ := δ) (by
      rw [← NNReal.coe_le_coe, hδ, NNReal.coe_one]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [div_le_one (by exact_mod_cast hn)]
        linarith [(Nat.cast_nonneg (s * r + s - 1) : (0 : ℝ) ≤ _)])
    ((fun (a : F) (_ : Fin m) ↦ a) ∘
      (CosetList.exists_le_encard_closeCodewordsRel hω hsn hr hdeg).choose) (by
      rw [hδ]
      have he : Function.Injective (fun (a : F) (_ : Fin m) ↦ a) :=
        fun a b h ↦ congrFun h ⟨0, by omega⟩
      have hCD : ∀ c ∈ (ReedSolomon.code (primitiveRootDomain hω) k : Set (Fin n → F)),
          (fun (a : F) (_ : Fin m) ↦ a) ∘ c ∈
            ((ReedSolomon.code (primitiveRootDomain hω) k : Set (Fin n → F)) ^⋈ (Fin m)) := by
        intro c hc j; exact hc
      have hle := (CosetList.exists_le_encard_closeCodewordsRel hω hsn hr hdeg).choose_spec.trans
        (Code.encard_closeCodewordsRel_le_of_injective_comp he hCD
          (CosetList.exists_le_encard_closeCodewordsRel hω hsn hr hdeg).choose _)
      calc (ε_star : ENNReal) * (Fintype.card F : ENNReal)
          < ((Nat.choose (n / s - 1) r / (n / s) : ℕ) : ENNReal) := hnum
        _ = (((Nat.choose (n / s - 1) r / (n / s) : ℕ) : ℕ∞) : ENNReal) :=
          (ENat.toENNReal_coe _).symm
        _ ≤ _ := by exact_mod_cast hle)

end ProximityGap.GrandChallenges
