/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.FoldingRound
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.LinearClaims
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Theorem

/-!
# Explicit bounds for the equal-degree and linear-claim combiners

Theorem 5.1 of [CWYZ26] bounds both errors by the affine error plus a Johnson term.
The affine bound of Theorem 1.1 then makes both explicit.
This gives the second inequalities of (5.4) and (5.5).

The first inequality of (5.4) is the `t = 1` case of the `t`-row bound in `FoldingRound`.
`interleavedEqualDegreeMcaError_one` and `interleavedAffineMcaError_one` identify the one-row
errors, so Lean checks that the one-row bound is this case.

Here `n` is the domain size, `q` is the field size, `1 ≤ d < n`, and `ρ = d / n`.
Assume `0 < η < 1 - √ρ` and `n η² ≥ 4 / ρ`.
The threshold is `A = ⌈(√ρ + η) n⌉`, and the loss is one.
The rounded-down Johnson bound is `ℓ₀ = ⌊n(A - 1 - d)/((A - 1)² - nd)⌋`.

## Main statements

* `ReedSolomon.equalDegreeMcaError_le_affineMcaError_add`: the first inequality of (5.4),
  the reduction to the affine error with loss `ℓ₀/q`.
* `ReedSolomon.equalDegreeMcaError_le`: the equal-degree bound
  `(4 / η + ℓ₀) / q + 2¹⁴ n² / (ρ³ η¹⁰ q²)`.
* `ReedSolomon.linearClaimMcaError_le_johnson`: the linear-claim bound
  `(4 / η + ℓ₀) / q + 2¹⁴ n² / (ρ³ η¹⁰ q²)`.
* `ReedSolomon.linearClaimMcaError_le`: the weaker linear-claim bound
  `(4 / η + 2 ℓ₀) / q + 2¹⁴ n² / (ρ³ η¹⁰ q²)`.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι]

/-- If `nd < (A - 1)²`, the equal-degree error at agreement loss one is
at most the affine error plus `ℓ₀/q`, where `n = |ι|`, `q = |F|`, and
`ℓ₀ = ⌊n(A - 1 - d)/((A - 1)² - nd)⌋` is the rounded-down Johnson bound.
This is `interleavedEqualDegreeMcaError_le_interleavedAffineMcaError_add` at `t = 1`, through
`interleavedEqualDegreeMcaError_one` and `interleavedAffineMcaError_one`. -/
theorem equalDegreeMcaError_le_affineMcaError_add [Fintype F] (domain : ι ↪ F) {d A : ℕ}
    (hJ : Fintype.card ι * d < (A - 1) ^ 2) :
    equalDegreeMcaError domain d A 1 ≤ affineMcaError domain d A 1 +
      ENNReal.ofReal
        (((⌊(Fintype.card ι : ℝ) * ((A : ℝ) - 1 - d) /
          (((A : ℝ) - 1) ^ 2 - Fintype.card ι * d)⌋₊ : ℕ) : ℝ) / Fintype.card F) := by
  rw [← interleavedEqualDegreeMcaError_one, ← interleavedAffineMcaError_one]
  exact interleavedEqualDegreeMcaError_le_interleavedAffineMcaError_add domain 1 hJ

/-- With one point of loss, the equal-degree MCA error is at most the explicit bound.

The bound is `(4/η + ℓ₀)/q + 2¹⁴ n² / (ρ³ η¹⁰ q²)`.

Here `n` is the domain size, `q` is the field size, `1 ≤ d < n`, and `ρ = d / n`.
Assume `0 < η < 1 - √ρ` and `n η² ≥ 4 / ρ`.
The threshold is `A = ⌈(√ρ + η) n⌉` and `ℓ₀ = ⌊n(A - 1 - d)/((A - 1)² - nd)⌋`.
This is `interleavedEqualDegreeMcaError_le` at `t = 1`, through
`interleavedEqualDegreeMcaError_one`. -/
theorem equalDegreeMcaError_le [Fintype F] (domain : ι ↪ F) {d : ℕ} {η : ℝ}
    (hd : 1 ≤ d) (hdn : d < Fintype.card ι) (hη : 0 < η)
    (hη1 : η < 1 - √((d : ℝ) / Fintype.card ι))
    (hn : 4 / ((d : ℝ) / Fintype.card ι) ≤ Fintype.card ι * η ^ 2) :
    equalDegreeMcaError domain d ⌈(√((d : ℝ) / Fintype.card ι) + η) * Fintype.card ι⌉₊ 1 ≤
      ENNReal.ofReal ((4 / η +
        ((⌊(Fintype.card ι : ℝ) *
          ((⌈(√((d : ℝ) / Fintype.card ι) + η) * Fintype.card ι⌉₊ : ℝ) - 1 - d) /
          (((⌈(√((d : ℝ) / Fintype.card ι) + η) * Fintype.card ι⌉₊ : ℝ) - 1) ^ 2 -
            Fintype.card ι * d)⌋₊ : ℕ) : ℝ)) / Fintype.card F +
        2 ^ 14 * (Fintype.card ι : ℝ) ^ 2 /
          (((d : ℝ) / Fintype.card ι) ^ 3 * η ^ 10 * (Fintype.card F : ℝ) ^ 2)) := by
  rw [← interleavedEqualDegreeMcaError_one]
  exact interleavedEqualDegreeMcaError_le domain 1 hd hdn hη hη1 hn

/-- With one point of loss, the linear-claim MCA error is at most the explicit bound.

The bound is `(4/η + ℓ₀)/q + 2¹⁴ n² / (ρ³ η¹⁰ q²)`.

Here `n` is the domain size, `q` is the field size, `1 ≤ d < n`, and `ρ = d / n`.
Assume `0 < η < 1 - √ρ` and `n η² ≥ 4 / ρ`.
The threshold is `A = ⌈(√ρ + η) n⌉` and `ℓ₀ = ⌊n(A - 1 - d)/((A - 1)² - nd)⌋`. -/
theorem linearClaimMcaError_le_johnson [Fintype F] (domain : ι ↪ F) {d : ℕ} {η : ℝ}
    (hd : 1 ≤ d) (hdn : d < Fintype.card ι) (hη : 0 < η)
    (hη1 : η < 1 - √((d : ℝ) / Fintype.card ι))
    (hn : 4 / ((d : ℝ) / Fintype.card ι) ≤ Fintype.card ι * η ^ 2) :
    linearClaimMcaError domain d ⌈(√((d : ℝ) / Fintype.card ι) + η) * Fintype.card ι⌉₊ 1 ≤
      ENNReal.ofReal ((4 / η +
        ((⌊(Fintype.card ι : ℝ) *
          ((⌈(√((d : ℝ) / Fintype.card ι) + η) * Fintype.card ι⌉₊ : ℝ) - 1 - d) /
          (((⌈(√((d : ℝ) / Fintype.card ι) + η) * Fintype.card ι⌉₊ : ℝ) - 1) ^ 2 -
            Fintype.card ι * d)⌋₊ : ℕ) : ℝ)) / Fintype.card F +
        2 ^ 14 * (Fintype.card ι : ℝ) ^ 2 /
          (((d : ℝ) / Fintype.card ι) ^ 3 * η ^ 10 * (Fintype.card F : ℝ) ^ 2)) := by
  have hJ := affineThreshold_johnson hd hdn hη hn
  unfold affineThreshold at hJ
  refine (linearClaimMcaError_le_affineMcaError_add_johnson domain hJ).trans ?_
  refine (add_le_add_left (affineMcaError_le domain hd hdn hη hη1 hn) _).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  field_simp
  ring

/-- With one point of loss, the linear-claim MCA error is at most the explicit bound.

The bound is `(4/η + 2ℓ₀)/q + 2¹⁴ n² / (ρ³ η¹⁰ q²)`.

Here `n` is the domain size, `q` is the field size, `1 ≤ d < n`, and `ρ = d / n`.
Assume `0 < η < 1 - √ρ` and `n η² ≥ 4 / ρ`.
The threshold is `A = ⌈(√ρ + η) n⌉` and `ℓ₀ = ⌊n(A - 1 - d)/((A - 1)² - nd)⌋`.
This follows from `linearClaimMcaError_le_johnson`, since `ℓ₀ ≤ 2ℓ₀`. -/
theorem linearClaimMcaError_le [Fintype F] (domain : ι ↪ F) {d : ℕ} {η : ℝ}
    (hd : 1 ≤ d) (hdn : d < Fintype.card ι) (hη : 0 < η)
    (hη1 : η < 1 - √((d : ℝ) / Fintype.card ι))
    (hn : 4 / ((d : ℝ) / Fintype.card ι) ≤ Fintype.card ι * η ^ 2) :
    linearClaimMcaError domain d ⌈(√((d : ℝ) / Fintype.card ι) + η) * Fintype.card ι⌉₊ 1 ≤
      ENNReal.ofReal ((4 / η + 2 *
        ((⌊(Fintype.card ι : ℝ) *
          ((⌈(√((d : ℝ) / Fintype.card ι) + η) * Fintype.card ι⌉₊ : ℝ) - 1 - d) /
          (((⌈(√((d : ℝ) / Fintype.card ι) + η) * Fintype.card ι⌉₊ : ℝ) - 1) ^ 2 -
            Fintype.card ι * d)⌋₊ : ℕ) : ℝ)) / Fintype.card F +
        2 ^ 14 * (Fintype.card ι : ℝ) ^ 2 /
          (((d : ℝ) / Fintype.card ι) ^ 3 * η ^ 10 * (Fintype.card F : ℝ) ^ 2)) := by
  refine (linearClaimMcaError_le_johnson domain hd hdn hη hη1 hn).trans
    (ENNReal.ofReal_le_ofReal ?_)
  gcongr
  exact le_mul_of_one_le_left (by positivity) one_le_two

end ReedSolomon
