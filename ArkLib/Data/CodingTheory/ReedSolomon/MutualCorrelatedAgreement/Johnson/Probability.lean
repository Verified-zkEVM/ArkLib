/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Certificate
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine
/-!
# Finite-field Johnson MCA probability

The characteristic-free exact-agreement theorem bounds the canonical affine-line bad event.
Uniform challenge sampling divides its real exceptional-cardinality bound by the field size.
-/

@[expose] public section

namespace ReedSolomon
open Polynomial HiddenDerivative CoreDefinitions LinearCode
open scoped ProbabilityTheory ENNReal

open Classical in
/-- The finite Johnson exception bound controls uniform affine-line MCA failure probability
in every characteristic, including the trivial probability cap of one. -/
theorem johnson_mcaError_le
    {F : Type} [Field F] [Fintype F] {n D : ℕ} {eta : ℝ}
    (domain : Fin n ↪ F) (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (ha : johnsonAgreement n D eta ≤ 1) :
    mcaError (AffineLineGenerator F) (code domain (D + 1))
        (1 - johnsonAgreement n D eta) ≤
      min 1 (ENNReal.ofReal
        (johnsonE0 n D ⌈johnsonAgreement n D eta * n⌉₊ eta / (Fintype.card F : ℝ))) := by
  classical
  let A := ⌈johnsonAgreement n D eta * n⌉₊
  have hAn : A ≤ n := Nat.ceil_le.mpr (by nlinarith [Nat.cast_nonneg n (α := ℝ)])
  have hthreshold : johnsonAgreement n D eta * n ≤ A := Nat.le_ceil _
  have hline : LineExactAgreementBound domain (D + 1) A (johnsonE0 n D A eta) := by
    intro f g
    obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_johnsonMCA
      domain f g hD hDn heta ha hthreshold hAn
    refine ⟨ex, hcard, ?_⟩
    intro z hz P hP hagree
    obtain ⟨pair, hp0, hp1, heq, hset⟩ := hgood z hz P hP hagree
    refine ⟨pair.1, pair.2, hp0, hp1, ?_, ?_⟩
    · simpa [correlatedPairSpecialization] using heq
    · simpa [mappedDomain] using hset
  apply mcaError_affineLine_le_min_one_of_exactAgreement domain _ hline
  have heq : (n : ℝ) * (1 - (1 - johnsonAgreement n D eta)) =
      johnsonAgreement n D eta * n := by ring
  rw [heq]

end ReedSolomon
