/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Justin Thaler
-/
module

public import ArkLib.Data.Finset.WeightedSimplex
public import Mathlib.Algebra.Order.Floor.Div

/-!
# Counts for the certified local rank bound

This file contains the arithmetic behind the certified bound on the rank of the local
constraint map. The local intermediate space has, at each `T`-degree `r < m`, one block of
`(r + 1) (M + 1)` exponents of `U` and `Y₁` for every higher-jet exponent of weight at most
`W + r`. The exhibited kernel removes a rectangle of `(r + 1 - h) (M + 1 - h)` of these, where
`h = ⌈(m - r) / d⌉` is the least power of the hidden error that reaches contact order `m`.

* `weightedHigherJetCount d W` is the number of exponent vectors `(c₂, ..., c_d)` of `Y₂, ..., Y_d`
  with `∑ (j - 1) c_j ≤ W`, counted as a weighted simplex.
* `contactThreshold d m r = ⌈(m - r) / d⌉`.
* `certifiedEnlargedRankBound d m M W` is the sum over `r < m` of the higher-jet count times the
  residual `(r + 1)(M + 1) - (r + 1 - h)(M + 1 - h)`.

## Main statements

* `multiplicity_le_add_mul_contactThreshold`: `m ≤ r + d h` when `d > 0`.
* `add_mul_lt_multiplicity_of_lt_contactThreshold`: every `b < h` has `r + d b < m`.
* `ambient_sub_exhibitedKernel_eq_certifiedEnlargedRankBound`: the ambient count minus the
  exhibited-kernel count is the certified bound.

## References

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Counting.lean`
at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d: `weightedHigherJetCount` (the
source's `weightedHigherJetTuples` filtered the same coordinate box by hand; here it is
`Finset.natWeightedSimplex`), `contactThreshold`, `multiplicity_le_add_mul_contactThreshold`,
`add_mul_lt_multiplicity_of_lt_contactThreshold`, `ambientContactCount`,
`exhibitedKernelContactCount`, `exhibitedKernelResidualCount`,
`exhibitedKernelContactCount_le_ambientContactCount`, `certifiedContactRankBudget`, and
`certifiedEnlargedRankBound`. The source assumed `r < m` in both threshold lemmas and `0 < d` in
the second; neither lemma needs `r < m`, and the second holds for every `d`. The identity
`ambient_sub_exhibitedKernel_eq_certifiedEnlargedRankBound` comes from the source's
`Interpolation/Local/Rank.lean`; it is pure arithmetic and so lives here.

Deferred to the slices that use them: the shell counts and tuple equivalences with
`HigherJetExponent`, the staircase counts and `exactInterpolationDimensionCount`, the
bookkeeping type `CertifiedEnlargedRankBudgetIndex`, and `ExactFiniteCertificate`.

* Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed--Solomon
  Codes up to Capacity in the Low-Rate Regime*, ECCC TR26-164, Section 3.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

open Finset

/-- The number of exponent vectors of the higher jets `Y₂, ..., Y_d` of anisotropic weight
`∑_{j ≥ 2} (j - 1) c_j` at most `W`, as a weighted simplex over `Fin (d - 1)` with weights
`1, 2, ..., d - 1`. For `d ≤ 1` there are no higher jets and the count is `1`. -/
def weightedHigherJetCount (d W : ℕ) : ℕ :=
  (natWeightedSimplex (fun i : Fin (d - 1) => i.val + 1) W).card

/-- For `d = n + 1` the higher jets are indexed by `Fin n`. -/
theorem weightedHigherJetCount_succ (n W : ℕ) :
    weightedHigherJetCount (n + 1) W =
      (natWeightedSimplex (fun i : Fin n => i.val + 1) W).card :=
  rfl

/-- The least power of the hidden error that reaches contact order `m` from `T`-degree `r`:
`⌈(m - r) / d⌉`. It is zero when `r ≥ m`, and also when `d = 0`. -/
def contactThreshold (d m r : ℕ) : ℕ :=
  (m - r) ⌈/⌉ d

/-- At the threshold the contact order `r + d h` reaches `m`. The hypothesis `0 < d` is needed:
for `d = 0` the threshold is `0`, and `m ≤ r` fails whenever `r < m`. -/
theorem multiplicity_le_add_mul_contactThreshold {d : ℕ} (hd : 0 < d) (m r : ℕ) :
    m ≤ r + d * contactThreshold d m r := by
  have hcover : m - r ≤ d * contactThreshold d m r := le_smul_ceilDiv hd
  omega

/-- Below the threshold the contact order stays below `m`. No hypothesis is needed: if
`d = 0` or `r ≥ m`, the threshold is `0` and there is no `b` below it. -/
theorem add_mul_lt_multiplicity_of_lt_contactThreshold {d m r b : ℕ}
    (hb : b < contactThreshold d m r) : r + d * b < m := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [contactThreshold] at hb
  have hnot : ¬m - r ≤ d * b := fun h =>
    absurd ((ceilDiv_le_iff_le_mul hd).mpr h) (Nat.not_le.mpr hb)
  omega

/-- The number of `(U, Y₁)` exponents `(a, b)` with `a ≤ r` and `b ≤ M`. -/
def ambientContactCount (r M : ℕ) : ℕ :=
  (r + 1) * (M + 1)

/-- The number of `(U, Y₁)` exponents `(a, b)` with `a + h ≤ r` and `b + h ≤ M`. Each factor is
written `r + 1 - h` rather than `r - h + 1`, which would be wrong in `ℕ` when `h > r`. -/
def exhibitedKernelContactCount (r M h : ℕ) : ℕ :=
  (r + 1 - h) * (M + 1 - h)

/-- The ambient count minus the exhibited-kernel count. -/
def exhibitedKernelResidualCount (r M h : ℕ) : ℕ :=
  ambientContactCount r M - exhibitedKernelContactCount r M h

/-- The exhibited rectangle is never larger than the ambient one. -/
theorem exhibitedKernelContactCount_le_ambientContactCount (r M h : ℕ) :
    exhibitedKernelContactCount r M h ≤ ambientContactCount r M :=
  Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)

/-- The residual count at `T`-degree `r` with the threshold `contactThreshold d m r`. -/
def certifiedContactRankBudget (d m M r : ℕ) : ℕ :=
  exhibitedKernelResidualCount r M (contactThreshold d m r)

/-- The certified bound on the rank of the enlarged local constraint map:
`∑_{r < m} Λ_d(W + r) ((r + 1)(M + 1) - (r + 1 - h_r)(M + 1 - h_r))`, where `Λ_d` is
`weightedHigherJetCount d` and `h_r = contactThreshold d m r`. It is an upper bound obtained from
an exhibited part of the kernel, not the exact rank. -/
def certifiedEnlargedRankBound (d m M W : ℕ) : ℕ :=
  ∑ r ∈ range m, weightedHigherJetCount d (W + r) * certifiedContactRankBudget d m M r

/-- The ambient count minus the exhibited-kernel count is the certified bound. Truncated
subtraction commutes with the sum because the exhibited count is termwise at most the ambient
count. -/
theorem ambient_sub_exhibitedKernel_eq_certifiedEnlargedRankBound (d m M W : ℕ) :
    (∑ r ∈ range m, weightedHigherJetCount d (W + r) * ambientContactCount r M) -
        ∑ r ∈ range m,
          weightedHigherJetCount d (W + r) *
            exhibitedKernelContactCount r M (contactThreshold d m r) =
      certifiedEnlargedRankBound d m M W := by
  rw [← sum_tsub_distrib]
  · simp only [certifiedEnlargedRankBound, certifiedContactRankBudget,
      exhibitedKernelResidualCount, Nat.mul_sub]
  · exact fun r _ => Nat.mul_le_mul_left _
      (exhibitedKernelContactCount_le_ambientContactCount r M (contactThreshold d m r))

end ReedSolomon.HiddenDerivative
