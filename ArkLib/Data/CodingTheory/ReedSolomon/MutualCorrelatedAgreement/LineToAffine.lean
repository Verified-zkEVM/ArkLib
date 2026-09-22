/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ProximityGenerator.AffineGenerator
public import ArkLib.Data.CodingTheory.ProximityGenerator.Interleaving
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FullAgreement

/-!
# Exact line agreement bounds affine mutual correlated agreement

Fix a Reed–Solomon code of message length `k` on an evaluation domain `domain : ι ↪ F` over a
finite field. `LineExactAgreementBound domain k A B` says: for every pair of received words
`f g`, one set of at most `B` challenges is chosen before the challenge and the candidate, outside
which every polynomial `P` of degree below `k` with at least `A` agreements with `f + z • g` is
`P₀ + C z * P₁` for polynomials of degree below `k` whose common agreement set with `(f, g)` is the
agreement set of `P`.

Such a bound controls the MCA bad events of the affine line and affine space generators at every
radius whose integer agreement threshold `⌈|ι| · (1 - radius)⌉₊` is at least `A`: at most `B` line
challenges are bad, the line MCA error is at most `B / |F|`, and the affine space MCA error is at
most `B / (|F| - 1)` in every dimension.

## Main definitions

* `ReedSolomon.LineExactAgreementBound`: the uniform exact-agreement bound for lines.

## Main statements

* `ReedSolomon.LineExactAgreementBound.exists_forall_not_isProjectionBad`: outside the exceptional
  set no line challenge is projection-bad at threshold `A`.
* `ReedSolomon.affineLine_bad_set_card_le_of_exactAgreement`: at most `B` bad line challenges.
* `ReedSolomon.mcaError_affineLine_le_of_exactAgreement`,
  `ReedSolomon.mcaError_affineLine_le_min_one_of_exactAgreement`: the line MCA error.
* `ReedSolomon.affineSpace_bad_density_le_of_exactAgreement`,
  `ReedSolomon.mcaError_affineSpace_le_of_exactAgreement`: the affine space MCA error.
* `ReedSolomon.exists_affine_exceptionalSet_full_agreement_of_exactLine`: outside an affine
  exceptional set of density at most `B / (|F| - 1)`, every close polynomial decomposes with
  exact agreement.

## References

Ported from `Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/LineToAffine.lean` at ArkLib
revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`. Throughout, the coordinate type `Fin n` is
generalized to any finite type `ι`, and the unused `[Fintype F]` is dropped from
`LineExactAgreementBound`.

* `LineExactAgreementBound` and `LineExactAgreementBound.mono` have the source statements.
* `LineExactAgreementBound.exists_forall_not_isProjectionBad` is new. It derives the absence of
  projection-badness from `Code.not_isProjectionBad_of_forall_hasExactAgreement`.
* `affineLine_bad_set_card_le_of_exactAgreement` has the source statement. The source unpacked
  the MCA event by hand; here it is `CoreDefinitions.isMCA_iff_isProjectionBad` at a threshold at
  least `A`.
* `mcaError_affineLine_le_of_exactAgreement` and `mcaError_affineLine_le_min_one_of_exactAgreement`
  have the source statements; the first is `CoreDefinitions.mcaError_le_ofReal_of_forall_card_le`.
* `affineSpace_bad_density_le_of_exactAgreement`, `mcaError_affineSpace_le_of_exactAgreement` and
  `exists_affine_exceptionalSet_full_agreement_of_exactLine` drop the source's hypothesis `1 ≤ s`:
  in dimension `0` no seed is bad. The first two specialize
  `AffineMCAMain.card_filter_isMCA_affineSpaceGenerator_div_le` and
  `AffineMCAMain.mcaError_affineSpaceGenerator_le_of_forall_card_le`, which hold for every module
  code. The third keeps the source's hypothesis `k ≤ |ι| · (1 - radius)`, which
  `exists_polynomials_full_agreement_of_not_isMCA` needs for uniqueness of interpolation.

Deferred: the providers of `LineExactAgreementBound` (the capacity, Johnson, first-order and
polynomial-curve theorems of the source) and the interleaved consumer
`mcaError_interleaved_le_of_exactAgreement`.
-/

@[expose] public section

namespace ReedSolomon

noncomputable section

open Polynomial CoreDefinitions LinearCode

/-- **Uniform exact agreement for lines.** For every pair of received words `f g : ι → F`, some
set `exceptional` of at most `B` challenges is chosen, such that for every challenge
`z ∉ exceptional` and every polynomial `P` of degree below `k` with at least `A` agreements with
`i ↦ f i + z * g i`, there are `P₀ P₁` of degree below `k` with `P = P₀ + C z * P₁` whose common
agreement set with `(f, g)` equals the agreement set of `P`.

The exceptional set depends on `f` and `g` but not on `z` or `P`. The bound `B` is real so that
providers can state it as a formula in `|ι|`; only `⌊B⌋₊` matters. -/
def LineExactAgreementBound {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι]
    (domain : ι ↪ F) (k A : ℕ) (B : ℝ) : Prop :=
  ∀ f g : ι → F, ∃ exceptional : Finset F, (exceptional.card : ℝ) ≤ B ∧
    ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
      A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
      ∃ P₀ P₁ : F[X], P₀.degree < k ∧ P₁.degree < k ∧ P = P₀ + C z * P₁ ∧
        polynomialAgreementSet domain (fun i ↦ f i + z * g i) P =
          commonPolynomialAgreementSet domain f g P₀ P₁

/-- A larger exceptional-set budget `B' ≥ B` preserves the bound. -/
theorem LineExactAgreementBound.mono {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι]
    {domain : ι ↪ F} {k A : ℕ} {B B' : ℝ} (h : LineExactAgreementBound domain k A B)
    (hBB' : B ≤ B') : LineExactAgreementBound domain k A B' := fun f g ↦
  (h f g).imp fun _ hex ↦ ⟨hex.1.trans hBB', hex.2⟩

variable {F ι : Type} [Field F] [DecidableEq F] [Fintype ι]

/-- **No projection-bad line challenge outside the exceptional set.** Under
`LineExactAgreementBound domain k A B`, for every pair `U : Fin 2 → ι → F` of words there is a
set of at most `B` challenges outside which no challenge is projection-bad for the affine line
generator and the Reed–Solomon code at threshold `A`.

A codeword agreeing with `U 0 + z • U 1` on `A` coordinates is the evaluation of a polynomial `P`
of degree below `k` with at least `A` agreements. The decomposition `P = P₀ + C z * P₁` with exact
agreement gives exact agreement of the codeword in the sense of `Code.HasExactAgreement`, and
`Code.not_isProjectionBad_of_forall_hasExactAgreement` concludes. -/
theorem LineExactAgreementBound.exists_forall_not_isProjectionBad {domain : ι ↪ F} {k A : ℕ}
    {B : ℝ} (hline : LineExactAgreementBound domain k A B) (U : Fin 2 → ι → F) :
    ∃ exceptional : Finset F, (exceptional.card : ℝ) ≤ B ∧ ∀ z ∉ exceptional,
      ¬ Code.IsProjectionBad (AffineLineGenerator F) (code domain k) A z U := by
  obtain ⟨exceptional, hcard, hexact⟩ := hline (U 0) (U 1)
  refine ⟨exceptional, hcard, fun z hz ↦ Code.not_isProjectionBad_of_forall_hasExactAgreement ?_⟩
  intro c hc T hT hcT
  obtain ⟨P, hP, hPc⟩ := mem_code_iff_eval.mp hc
  have hsum (i : ι) : ∑ j, AffineLineGenerator F z j • U j i = U 0 i + z * U 1 i := by
    simp [AffineLineGenerator, Fin.sum_univ_two]
  have hA : A ≤ (polynomialAgreementSet domain (fun i ↦ U 0 i + z * U 1 i) P).card :=
    hT.trans (Finset.card_le_card fun i hi ↦ by
      rw [mem_polynomialAgreementSet, hPc, hcT i hi, hsum])
  obtain ⟨P₀, P₁, hP₀, hP₁, hPeq, hset⟩ := hexact z hz P hP hA
  refine ⟨![fun i ↦ P₀.eval (domain i), fun i ↦ P₁.eval (domain i)], fun j ↦ ?_, ?_, fun i ↦ ?_⟩
  · fin_cases j
    · exact mem_code_iff_eval.mpr ⟨P₀, hP₀, fun _ ↦ rfl⟩
    · exact mem_code_iff_eval.mpr ⟨P₁, hP₁, fun _ ↦ rfl⟩
  · funext i
    simp [← hPc, hPeq, AffineLineGenerator, Fin.sum_univ_two]
  · have hi := congrArg (i ∈ ·) hset
    simp only [mem_polynomialAgreementSet, mem_commonPolynomialAgreementSet, eq_iff_iff] at hi
    rw [hsum, ← hPc, hi, Fin.forall_fin_two]
    simp

variable [Fintype F]

open Classical in
/-- **At most `B` bad line challenges.** Under `LineExactAgreementBound domain k A B`, for every
radius whose integer threshold `⌈|ι| · (1 - radius)⌉₊` is at least `A`, every pair of words has at
most `B` challenges that are MCA-bad for the affine line generator.

The threshold hypothesis is needed: the MCA event at `radius` quantifies over witness sets of
size at least `⌈|ι| · (1 - radius)⌉₊`, and the bound only controls candidates with at least `A`
agreements. -/
theorem affineLine_bad_set_card_le_of_exactAgreement {k A : ℕ} (domain : ι ↪ F) (B : ℝ)
    (hline : LineExactAgreementBound domain k A B) (radius : ℝ)
    (hthreshold : A ≤ ⌈(Fintype.card ι : ℝ) * (1 - radius)⌉₊) (U : Fin 2 → ι → F) :
    ((Finset.univ.filter fun z : F ↦
      IsMCA (AffineLineGenerator F) (code domain k) z U radius).card : ℝ) ≤ B := by
  obtain ⟨exceptional, hcard, hgood⟩ := hline.exists_forall_not_isProjectionBad U
  refine le_trans (Nat.cast_le.mpr (Finset.card_le_card fun z hz ↦ ?_)) hcard
  by_contra hzex
  obtain ⟨T, hT, hmem⟩ := (isMCA_iff_isProjectionBad _ _ _ _ _).mp (Finset.mem_filter.mp hz).2
  exact hgood z hzex ⟨T, hthreshold.trans hT, hmem⟩

variable [SampleableType F]

/-- **Line MCA error.** Under `LineExactAgreementBound domain k A B`, the MCA error of the affine
line generator for the Reed–Solomon code at every radius with threshold at least `A` is at most
`B / |F|`. -/
theorem mcaError_affineLine_le_of_exactAgreement {k A : ℕ} (domain : ι ↪ F) (B : ℝ)
    (hline : LineExactAgreementBound domain k A B) (radius : ℝ)
    (hthreshold : A ≤ ⌈(Fintype.card ι : ℝ) * (1 - radius)⌉₊) :
    mcaError (AffineLineGenerator F) (code domain k) radius ≤
      ENNReal.ofReal (B / (Fintype.card F : ℝ)) :=
  mcaError_le_ofReal_of_forall_card_le _ _ _
    (affineLine_bad_set_card_le_of_exactAgreement domain B hline radius hthreshold)

/-- **Line MCA error, capped at one.** The bound of `mcaError_affineLine_le_of_exactAgreement`
together with the trivial bound `1`. -/
theorem mcaError_affineLine_le_min_one_of_exactAgreement {k A : ℕ} (domain : ι ↪ F) (B : ℝ)
    (hline : LineExactAgreementBound domain k A B) (radius : ℝ)
    (hthreshold : A ≤ ⌈(Fintype.card ι : ℝ) * (1 - radius)⌉₊) :
    mcaError (AffineLineGenerator F) (code domain k) radius ≤
      min 1 (ENNReal.ofReal (B / (Fintype.card F : ℝ))) :=
  le_min (mcaError_le_one _ _ _)
    (mcaError_affineLine_le_of_exactAgreement domain B hline radius hthreshold)

open Classical in
/-- **Affine-space bad density.** Under `LineExactAgreementBound domain k A B`, for every radius
with threshold at least `A`, every dimension `s` and every family `U : Fin (s + 1) → ι → F`, the
density of MCA-bad seeds of the affine space generator is at most `B / (|F| - 1)`. -/
theorem affineSpace_bad_density_le_of_exactAgreement {k A s : ℕ} (domain : ι ↪ F) (B : ℝ)
    (hline : LineExactAgreementBound domain k A B) (radius : ℝ)
    (hthreshold : A ≤ ⌈(Fintype.card ι : ℝ) * (1 - radius)⌉₊) (U : Fin (s + 1) → ι → F) :
    ((Finset.univ.filter fun x : Fin s → F ↦
      IsMCA (AffineSpaceGenerator F s) (code domain k) x U radius).card : ℝ) /
        (Fintype.card F : ℝ) ^ s ≤ B / ((Fintype.card F : ℝ) - 1) :=
  AffineMCAMain.card_filter_isMCA_affineSpaceGenerator_div_le _ _
    (affineLine_bad_set_card_le_of_exactAgreement domain B hline radius hthreshold) U

/-- **Affine-space MCA error.** Under `LineExactAgreementBound domain k A B`, the MCA error of the
affine space generator of every dimension for the Reed–Solomon code, at every radius with
threshold at least `A`, is at most `B / (|F| - 1)`. -/
theorem mcaError_affineSpace_le_of_exactAgreement {k A s : ℕ} (domain : ι ↪ F) (B : ℝ)
    (hline : LineExactAgreementBound domain k A B) (radius : ℝ)
    (hthreshold : A ≤ ⌈(Fintype.card ι : ℝ) * (1 - radius)⌉₊) :
    mcaError (AffineSpaceGenerator F s) (code domain k) radius ≤
      ENNReal.ofReal (B / ((Fintype.card F : ℝ) - 1)) :=
  AffineMCAMain.mcaError_affineSpaceGenerator_le_of_forall_card_le _ _
    (affineLine_bad_set_card_le_of_exactAgreement domain B hline radius hthreshold)

open Classical in
/-- **Exact affine decomposition outside a sparse exceptional set.** Under
`LineExactAgreementBound domain k A B`, for every radius with threshold at least `A` and with
`k ≤ |ι| · (1 - radius)`, and every family `U : Fin (s + 1) → ι → F`, there is a set of at most
`B · |F| ^ s / (|F| - 1)` seeds `x` outside which every polynomial `P` of degree below `k` agreeing
with `∑ j, (1, x) j • U j` on at least `|ι| · (1 - radius)` coordinates is `∑ j, (1, x) j • P₀ j`
for polynomials `P₀ j` of degree below `k`, and agrees with the combined word exactly where every
`P₀ j` agrees with `U j`.

The exceptional set is the set of MCA-bad seeds. The hypothesis `k ≤ |ι| · (1 - radius)` is used
to identify `P` with the combination by uniqueness of interpolation. -/
theorem exists_affine_exceptionalSet_full_agreement_of_exactLine {k A s : ℕ} (domain : ι ↪ F)
    (B : ℝ) (hline : LineExactAgreementBound domain k A B) (radius : ℝ)
    (hthreshold : A ≤ ⌈(Fintype.card ι : ℝ) * (1 - radius)⌉₊)
    (hkThreshold : (k : ℝ) ≤ Fintype.card ι * (1 - radius)) (U : Fin (s + 1) → ι → F) :
    ∃ exceptional : Finset (Fin s → F),
      (exceptional.card : ℝ) ≤ B * (Fintype.card F : ℝ) ^ s / ((Fintype.card F : ℝ) - 1) ∧
      ∀ x ∉ exceptional, ∀ P : F[X], P.degree < k →
        ((Finset.univ.filter fun i ↦
          P.eval (domain i) = ∑ j, AffineSpaceGenerator F s x j * U j i).card : ℝ) ≥
            Fintype.card ι * (1 - radius) →
        ∃ P₀ : Fin (s + 1) → F[X], (∀ j, (P₀ j).degree < k) ∧
          P = ∑ j, AffineSpaceGenerator F s x j • P₀ j ∧
          ∀ i, (P.eval (domain i) = ∑ j, AffineSpaceGenerator F s x j * U j i) ↔
            ∀ j, (P₀ j).eval (domain i) = U j i := by
  refine ⟨Finset.univ.filter fun x ↦ IsMCA (AffineSpaceGenerator F s) (code domain k) x U radius,
    ?_, fun x hx P hP hclose ↦ ?_⟩
  · have hq : (0 : ℝ) < (Fintype.card F : ℝ) ^ s := by positivity
    have hdensity := affineSpace_bad_density_le_of_exactAgreement domain B hline radius
      hthreshold U
    rw [div_le_iff₀ hq] at hdensity
    exact hdensity.trans_eq (by ring)
  · have hgood : ¬ IsMCA (AffineSpaceGenerator F s) (code domain k) x U radius := by
      simpa using hx
    obtain ⟨P₀, hP₀, hPeq, hiff⟩ := exists_polynomials_full_agreement_of_not_isMCA domain k
      (AffineSpaceGenerator F s) x U radius hkThreshold hgood P hP (by
        convert hclose using 3
        ext i
        simp)
    exact ⟨P₀, hP₀, hPeq, fun i ↦ by simpa using hiff i⟩

end

end ReedSolomon
