/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine

/-!
# Johnson mutual correlated agreement error over finite fields

Over a finite field, the Johnson exceptional-set bound at the threshold `⌈a n⌉₊`, with
`a = √(D / n) + η`, bounds the mutual correlated agreement error of the affine line generator at
radius `1 - a` by `min 1 (E₀ / |F|)`, where `E₀ = johnsonExceptionCount n D ⌈a n⌉₊ η`. No
characteristic hypothesis is needed.

## Main statements

* `ReedSolomon.mcaError_affineLine_johnson_le`: the affine-line MCA error bound.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial HiddenDerivative CoreDefinitions LinearCode

/-- **Johnson affine-line MCA error.** For a Reed–Solomon code of dimension `D + 1` over a finite
field and `a = √(D / n) + η ≤ 1`, the affine-line MCA error at radius `1 - a` is at most
`min 1 (johnsonExceptionCount n D ⌈a n⌉₊ η / |F|)`. -/
theorem mcaError_affineLine_johnson_le
    {F : Type} [Field F] [Fintype F] [SampleableType F] {n D : ℕ} {eta : ℝ}
    (domain : Fin n ↪ F) (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (ha : johnsonAgreement n D eta ≤ 1) :
    mcaError (AffineLineGenerator F) (code domain (D + 1)) (1 - johnsonAgreement n D eta) ≤
      min 1 (ENNReal.ofReal
        (johnsonExceptionCount n D ⌈johnsonAgreement n D eta * n⌉₊ eta /
          (Fintype.card F : ℝ))) := by
  classical
  have hline : LineExactAgreementBound domain (D + 1) ⌈johnsonAgreement n D eta * n⌉₊
      (johnsonExceptionCount n D ⌈johnsonAgreement n D eta * n⌉₊ eta) := by
    intro f g
    obtain ⟨ex, hcard, hgood⟩ :=
      exists_johnson_line_exactCorrelatedPair_ceil domain f g hD hDn heta ha
    refine ⟨ex, hcard, fun z hz P hP hagree ↦ ?_⟩
    obtain ⟨pair, hp0, hp1, heq, hset⟩ := hgood z hz P hP (by convert hagree)
    refine ⟨pair.1, pair.2, hp0, hp1, ?_, ?_⟩
    · simpa [correlatedPairSpecialization] using heq
    · rw [← hset]
      ext i
      simp only [polynomialAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
  apply mcaError_affineLine_le_min_one_of_exactAgreement domain _ hline
  rw [Fintype.card_fin, show (n : ℝ) * (1 - (1 - johnsonAgreement n D eta)) =
    johnsonAgreement n D eta * n by ring]

end ReedSolomon
