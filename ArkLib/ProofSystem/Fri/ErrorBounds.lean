/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import ArkLib.ProofSystem.Fri.FoldingSoundness
public import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.Powers

/-!
# Numerical FRI folding bounds

Instantiate the folding-to-MCA reduction with ArkLib's existing powers-generator bound.
The numerical estimate is separate from the protocol-independent agreement argument, so
stronger MCA estimates can be substituted without changing that argument.

The generator parameter is the maximum exponent, not the number of coefficients: a fold
of factor `2 ^ k` uses the powers generator with parameter `2 ^ k - 1`.

## References

* [Bordage, S., Chiesa, A., Guan, Z., Manzur, I., *All Polynomial Generators Preserve
  Distance with Mutual Correlated Agreement*][BCGM25]
* [Garreta, A., Mohnblatt, N., Wagner, B., *A Simplified Round-by-round Soundness Proof
  of FRI*][GMW25]
-/

@[expose] public section

namespace Fri

open Domain ReedSolomon
open scoped NNReal ProbabilityTheory

/-- The certified powers-MCA estimate applies to a FRI folding round below the generalized
Johnson radius. All field-size, distance, slack, and radius hypotheses of the existing bound
are retained explicitly. Here `δmin` is the relative minimum distance of the next code. -/
theorem foldingAgreementFailure_prob_le_generalizedJohnson
    {F : Type} [Field F] [Fintype F] [SampleableType F] [DecidableEq F] {n k d : ℕ}
    (domain : SmoothCosetFftDomain n F) (f : Fin (2 ^ n) → F) (hd : 0 < d)
    (δmin η θ : ℝ≥0) (hk : 0 < k) (hcard : 2 ^ k ≤ Fintype.card F)
    (hmin : (δmin : ℝ) =
      (Code.minDist (code (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) d :
        Set (Fin (2 ^ (n - k)) → F)) : ℝ) / 2 ^ (n - k))
    (hη : 0 < η) (hηmin : η < δmin)
    (hθ : (θ : ℝ) ≤ 1 - (1 - (δmin : ℝ) + (η : ℝ)) ^
      ((1 : ℝ) / ((2 ^ k - 1 : ℕ) + 2))) :
    let m : ℕ := 2 ^ k - 1
    let r : ℝ := 1 - (δmin : ℝ) + (η : ℝ)
    Pr{let α ←$ᵗ F}[FoldingAgreementFailure domain f k d θ α] ≤
      ENNReal.ofReal
        (((2 ^ (n - k) : ℝ) * (1 - r ^ ((1 : ℝ) / (m + 1)))) / η
          * ((m : ℝ) / Fintype.card F)
          + max
            (2 * (m : ℝ) /
              ((η : ℝ) * (r ^ ((1 : ℝ) / (m + 2)) - r ^ ((1 : ℝ) / (m + 1)))
                * Fintype.card F))
            (((m : ℝ) + 1) * ((m : ℝ) + 2) / ((η : ℝ) * Fintype.card F))) := by
  have hpow : 2 ≤ 2 ^ k := Nat.le_pow (by omega)
  refine (foldingAgreementFailure_prob_le_powers domain f hd θ).trans ?_
  simpa only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using
    CodingTheory.linear_mcaError_powers_le
      (code (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) d)
      (2 ^ k - 1) δmin η θ (by omega) (by omega)
      (by simpa using hmin) hη hηmin hθ

end Fri
