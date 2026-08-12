/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.InterleavedCode

/-!
# Interleaved Reed-Solomon codes (ABF26 §2.4)

ABF26 Definition 2.13: the `s`-interleaved Reed-Solomon code
`IRS[F, L, k, s] := (RS[F, L, k/s])^≡s`. Each codeword is an `s`-tuple of base RS
codewords, arranged column-wise.

## Main definitions

- `ReedSolomon.Interleaved.irsCode` — ABF26 Definition 2.13.

## Main statements

- `ReedSolomon.Interleaved.dim_irsCode_eq_min` — the assumptionless exact dimension
  `s * min (k / s) |L|`.
- `ReedSolomon.Interleaved.dim_irsCode` — its full-dimension-regime specialization
  `Module.finrank F (irsCode domain k s) = s * (k / s)`.
- `ReedSolomon.Interleaved.dim_irsCode_of_dvd` — the paper-shaped specialisation
  `Module.finrank F (irsCode domain k s) = k` under `s ∣ k`.
- `ReedSolomon.Interleaved.minDist_irsCode_eq_minDist_rsCode` — interleaving does not change
  the minimum block distance, so IRS inherits the RS one verbatim.
- `ReedSolomon.Interleaved.minDist_irsCode` — the resulting closed form
  `|L| - k / s + 1`.
- `ReedSolomon.Interleaved.irs_rate_distance` — IRS satisfies the [ABF26] Lemma 2.6
  MDS rate-distance equation `δ_min = 1 - ρ + 1/n` at the alphabet-normalized rate
  `ρ = LinearCode.alphabetRate`, with **no divisibility hypothesis**. This is the input
  that `JohnsonBound.Family`'s alphabet-generic Corollary 3.3 asks a module-alphabet code
  family to supply; `CodingTheory.irs_lambda_le_johnson_mds` consumes it.

## References

* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and Correlated
    Agreement*][ABF26] (§2.4: Definition 2.13; §2.2: Definition 2.5, Lemma 2.6)
-/

namespace ReedSolomon
namespace Interleaved

/-- **ABF26 Definition 2.13.** The `s`-interleaved Reed-Solomon code

  `IRS[F, L, k, s] := (RS[F, L, k/s])^≡s`

Each codeword is an `s`-tuple of base RS codewords arranged column-wise. Concretely the
carrier is `Code.interleavedCodeSet (ReedSolomon.code domain (k / s))`; closure under addition
and scalar multiplication follows from the same closure of the underlying RS code applied
column-by-column.

**Submodule structure.** Returns `Submodule F (ι → Fin s → F)` (equivalently
`ModuleCode ι F (Fin s → F)`) directly, so downstream theorems consume it as an `F`-linear
code without an existential wrap.

**Truncation is part of the definition.** The inner degree bound is `k / s` in `Nat`, i.e.
`⌊k / s⌋`: this definition *is* `interleavedCodeSet (RS[F, L, ⌊k/s⌋])`, not
`interleavedCodeSet (RS[F, L, k])`. The paper writes `k/s` and implicitly assumes `s ∣ k`, so
the two agree there, but when `s ∤ k` the truncation is silent and consequential:
`dim (irsCode domain k s) = s * (k / s)` (`dim_irsCode`), which is `< k` unless `s ∣ k` — e.g.
`k = 5`, `s = 2` gives dimension `4`. Callers quoting the paper's `dim(IRS) = k` must supply
`s ∣ k` (see `dim_irsCode_of_dvd`); a caller who wants the `s`-interleave of `RS[F, L, k']` for
a *given* inner degree `k'` should write `irsCode domain (s * k') s`. We keep the definition
itself unguarded so degenerate parameter regimes type-check uniformly. -/
noncomputable def irsCode {ι : Type*} {F : Type*} [Semiring F]
    (domain : ι ↪ F) (k s : ℕ) : Submodule F (ι → Fin s → F) :=
  (ReedSolomon.code domain (k / s)) ^⋈ (Fin s)

/-- **Exact dimension of `irsCode`, for every parameter choice.** Interleaving multiplies the
underlying RS dimension by `s` (`Code.finrank_moduleInterleavedCode`), while the base code has
dimension `min (k / s) |L|` (`ReedSolomon.dim_eq_min_deg_card`). Thus the exact answer is
`s * min (k / s) |L|`, including the saturated regime. -/
lemma dim_irsCode_eq_min {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    (domain : ι ↪ F) (k s : ℕ) :
    Module.finrank F (irsCode domain k s) = s * min (k / s) (Fintype.card ι) := by
  rw [irsCode, Code.finrank_moduleInterleavedCode, Fintype.card_fin]
  exact congrArg (s * ·) (ReedSolomon.dim_eq_min_deg_card (n := k / s) (α := domain))

/-- **Full-dimension regime for `irsCode`.** The exact formula `dim_irsCode_eq_min`
simplifies to `s * (k / s)` when the base RS code has enough evaluation points,
`k / s ≤ |L|`.

Note the `Nat` truncation in `k / s`: the value is `k` on the nose only when `s ∣ k`, see
`dim_irsCode_of_dvd`. -/
lemma dim_irsCode {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    (domain : ι ↪ F) (k s : ℕ)
    (h_rs_full : k / s ≤ Fintype.card ι) :
    Module.finrank F (irsCode domain k s) = s * (k / s) := by
  rw [dim_irsCode_eq_min domain k s, min_eq_left h_rs_full]

/-- Paper-shaped dimension formula in the divisible case: when `s ∣ k` (the implicit
convention of ABF26 Definition 2.13, satisfied by every instantiation in the paper),
`dim(IRS[F, L, k, s]) = k` on the nose. -/
lemma dim_irsCode_of_dvd {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    (domain : ι ↪ F) (k s : ℕ) (hdvd : s ∣ k)
    (h_rs_full : k / s ≤ Fintype.card ι) :
    Module.finrank F (irsCode domain k s) = k := by
  rw [dim_irsCode domain k s h_rs_full, Nat.mul_div_cancel' hdvd]

/-- **Interleaving preserves the minimum block distance**, so `IRS[F, L, k, s]` has exactly
the minimum distance of its underlying `RS[F, L, ⌊k/s⌋]`.

A two-line transport: `irsCode` is *definitionally* `Code.interleavedCodeSet` of the base RS
code (`Code.interleavedCode_eq_interleavedCodeSet_of_moduleCode` is `rfl`), so the generic
`Code.minDist_interleavedCodeSet` applies verbatim. Nothing Reed–Solomon-specific enters; the
sibling `CodingTheory.minDist_extensionCode` reaches the same generic theorem by the other
route (a coordinate Hamming isometry).

The metric here is the *block* one on `ι → Fin s → F`: a position counts as a disagreement
when the whole `s`-tuple differs, which is why interleaving leaves it unchanged. -/
theorem minDist_irsCode_eq_minDist_rsCode {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    [DecidableEq F] (domain : ι ↪ F) (k s : ℕ) [NeZero s] :
    Code.minDist ((irsCode domain k s : Submodule F (ι → Fin s → F)) : Set (ι → Fin s → F))
      = Code.minDist ((ReedSolomon.code domain (k / s) : Submodule F (ι → F)) : Set (ι → F)) := by
  haveI : Nonempty (Fin s) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne s))
  rw [irsCode, Code.interleavedCode_eq_interleavedCodeSet_of_moduleCode]
  exact Code.minDist_interleavedCodeSet (κ := Fin s) _

/-- **Closed form for the IRS minimum block distance:** `|L| - ⌊k/s⌋ + 1`, in the regime
`⌊k/s⌋ ≤ |L|` where the base RS code is not saturated.

Composes `minDist_irsCode_eq_minDist_rsCode` with the pre-existing `ReedSolomon.minDist_of_le`.
The `Nat` truncation in `k / s` is the same one `dim_irsCode` carries, and the two truncate
*consistently* — which is exactly why `irs_rate_distance` below needs no `s ∣ k`. -/
theorem minDist_irsCode {ι : Type*} [Fintype ι] {F : Type*} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) [NeZero s] [NeZero (k / s)]
    (h_rs_full : k / s ≤ Fintype.card ι) :
    Code.minDist ((irsCode domain k s : Submodule F (ι → Fin s → F)) : Set (ι → Fin s → F))
      = Fintype.card ι - k / s + 1 := by
  rw [minDist_irsCode_eq_minDist_rsCode, ReedSolomon.minDist_of_le h_rs_full]

/-- **Interleaved Reed–Solomon is MDS in the sense of [ABF26] Lemma 2.6**, unconditionally
in the parameters: at the alphabet-normalized rate `ρ = LinearCode.alphabetRate` of
Definition 2.5 (`finrank / (s · n)`, *not* `finrank / n`),

  `δ_min(IRS[F, L, k, s]) = 1 - ρ + 1/n`.

**No `s ∣ k` hypothesis is needed**, in contrast with the folded code
(`ReedSolomon.Folded.frs_rate_distance_of_dvd`). The reason is that interleaving truncates
*once*: the dimension is `s · ⌊k/s⌋` and the distance is `n - ⌊k/s⌋ + 1`, so the alphabet
normalization cancels the interleaving factor exactly, `ρ = ⌊k/s⌋ / n`, and both sides see
the same `⌊k/s⌋`. The folded code instead fixes the dimension at `k` while its distance
rounds, so there the two disagree by the rounding term unless `s ∣ k`.

This is precisely the input the alphabet-generic
`CodingTheory.mds_johnson_lambda_le_of_rate_distance` asks a module-alphabet family to
provide — see `CodingTheory.irs_lambda_le_johnson_mds`. Note that `LinearCode.IsMDS`
itself cannot be used here: it is stated only for `LinearCode ι F = Submodule F (ι → F)`,
whereas an interleaved code lives in `ι → Fin s → F`. -/
theorem irs_rate_distance {ι : Type*} [Fintype ι] [Nonempty ι] {F : Type*} [Field F]
    [DecidableEq F] (domain : ι ↪ F) (k s : ℕ) [NeZero s] [NeZero (k / s)]
    (h_rs_full : k / s ≤ Fintype.card ι) :
    (Code.minDist ((irsCode domain k s : Submodule F (ι → Fin s → F)) :
        Set (ι → Fin s → F)) : ℝ) / Fintype.card ι
      = 1 - (LinearCode.alphabetRate (irsCode domain k s) : ℝ) + 1 / Fintype.card ι := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hs : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  rw [minDist_irsCode domain k s h_rs_full, LinearCode.alphabetRate_cast_eq,
    dim_irsCode domain k s h_rs_full, Nat.cast_add, Nat.cast_sub h_rs_full, Nat.cast_mul]
  field_simp
  ring

/-- The alphabet-normalized rate of `IRS[F, L, k, s]` is `⌊k/s⌋ / |L|`: the interleaving
factor `s` multiplies the dimension and divides it back out again. Extracted from the
computation inside `irs_rate_distance`, which is where the cancellation matters. -/
lemma alphabetRate_irsCode {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    (domain : ι ↪ F) (k s : ℕ) [NeZero s]
    (h_rs_full : k / s ≤ Fintype.card ι) :
    (LinearCode.alphabetRate (irsCode domain k s) : ℝ)
      = (k / s : ℕ) / Fintype.card ι := by
  have hs : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  rw [LinearCode.alphabetRate_cast_eq, dim_irsCode domain k s h_rs_full, Nat.cast_mul]
  rw [mul_div_mul_left _ _ (ne_of_gt hs)]

end Interleaved
end ReedSolomon
