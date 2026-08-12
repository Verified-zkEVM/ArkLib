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
- `ReedSolomon.Interleaved.minDist_irsCode` — the resulting closed form `|L| - k / s + 1`,
  for every parameter choice (the saturated regime included).
- `ReedSolomon.Interleaved.alphabetRate_irsCode_eq_min` /
  `ReedSolomon.Interleaved.alphabetRate_irsCode` — the [ABF26] Definition 2.5 rate
  `min ⌊k/s⌋ |L| / |L|`, and its non-saturated form `⌊k/s⌋ / |L|`.
- `ReedSolomon.Interleaved.irs_rate_distance` — IRS satisfies the [ABF26] Lemma 2.6
  MDS rate-distance equation `δ_min = 1 - ρ + 1/n` at the alphabet-normalized rate
  `ρ = LinearCode.alphabetRate`, with **no divisibility and no non-saturation hypothesis**.
  This is the input that `JohnsonBound.Family`'s alphabet-generic Corollary 3.3 asks a
  module-alphabet code family to supply; `CodingTheory.irs_lambda_le_johnson_mds` consumes it.
- `ReedSolomon.Interleaved.interleavedCodeSet_rsCode_eq_irsCode` — the identification that
  lets `CodingTheory.lambda_extensionCode_eq_lambda_interleaved` land on an `irsCode`, so an
  extension code over a Reed-Solomon base inherits this file's list-size bound.

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

/-- **The alphabet-normalized rate of `IRS[F, L, k, s]`, for every parameter choice:**
`min ⌊k/s⌋ |L| / |L|`. The interleaving factor `s` multiplies the dimension
(`dim_irsCode_eq_min`) and the [ABF26] Definition 2.5 normalization divides it back out, so
the rate does not see `s` at all. Paired with `alphabetRate_irsCode` exactly as
`dim_irsCode_eq_min` is paired with `dim_irsCode`. -/
lemma alphabetRate_irsCode_eq_min {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    (domain : ι ↪ F) (k s : ℕ) [NeZero s] :
    (LinearCode.alphabetRate (irsCode domain k s) : ℝ)
      = (min (k / s) (Fintype.card ι) : ℕ) / Fintype.card ι := by
  have hs : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  rw [LinearCode.alphabetRate_cast_eq, dim_irsCode_eq_min domain k s, Nat.cast_mul,
    mul_div_mul_left _ _ (ne_of_gt hs)]

/-- The non-saturated specialization of `alphabetRate_irsCode_eq_min`: `ρ = ⌊k/s⌋ / |L|`
when `⌊k/s⌋ ≤ |L|`. -/
lemma alphabetRate_irsCode {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    (domain : ι ↪ F) (k s : ℕ) [NeZero s]
    (h_rs_full : k / s ≤ Fintype.card ι) :
    (LinearCode.alphabetRate (irsCode domain k s) : ℝ)
      = (k / s : ℕ) / Fintype.card ι := by
  rw [alphabetRate_irsCode_eq_min domain k s, min_eq_left h_rs_full]

/-- **Closed form for the IRS minimum block distance:** `|L| - ⌊k/s⌋ + 1`, for **every**
parameter choice.

No non-saturation hypothesis is needed. Composing `minDist_irsCode_eq_minDist_rsCode` with
the pre-existing `ReedSolomon.minDist_eq_card_sub_min_add_1` covers the saturated regime too:
once `⌊k/s⌋ ≥ |L|` the base code is all of `F^L`, the `Nat` subtraction truncates to `0`, and
both sides are `1`. -/
theorem minDist_irsCode {ι : Type*} [Fintype ι] [Nonempty ι] {F : Type*} [Field F]
    [DecidableEq F] (domain : ι ↪ F) (k s : ℕ) [NeZero s] [NeZero (k / s)] :
    Code.minDist ((irsCode domain k s : Submodule F (ι → Fin s → F)) : Set (ι → Fin s → F))
      = Fintype.card ι - k / s + 1 := by
  letI : Inhabited ι := Classical.inhabited_of_nonempty ‹Nonempty ι›
  rw [minDist_irsCode_eq_minDist_rsCode, ReedSolomon.minDist_eq_card_sub_min_add_1]
  omega

/-- **Interleaved Reed–Solomon is MDS in the sense of [ABF26] Lemma 2.6**, unconditionally
in the parameters: at the alphabet-normalized rate `ρ = LinearCode.alphabetRate` of
Definition 2.5 (`finrank / (s · n)`, *not* `finrank / n`),

  `δ_min(IRS[F, L, k, s]) = 1 - ρ + 1/n`.

[ABF26] asserts exactly this in passing — "MDS codes, which include the important class of
interleaved Reed–Solomon codes" — when deriving Corollary 3.3.

**Neither `s ∣ k` nor a non-saturation hypothesis is needed**, in contrast with the folded
code (`ReedSolomon.Folded.frs_rate_distance_of_dvd`, which does need `s ∣ k`). The reason is
that interleaving truncates *once*: dimension `s · min ⌊k/s⌋ n` and distance
`n - ⌊k/s⌋ + 1` degrade through the same `min`/`Nat`-subtraction, and the alphabet
normalization cancels the interleaving factor exactly, so `ρ = min ⌊k/s⌋ n / n`. In the
saturated regime both sides are `1/n`. The folded code instead fixes its dimension at `k`
while its distance rounds, so there the two disagree by the rounding term unless `s ∣ k`.

This is precisely the input the alphabet-generic
`CodingTheory.mds_johnson_lambda_le_of_rate_distance` asks a module-alphabet family to
provide — see `CodingTheory.irs_lambda_le_johnson_mds`. Note that `LinearCode.IsMDS`
itself cannot be used here: it is stated only for `LinearCode ι F = Submodule F (ι → F)`,
whereas an interleaved code lives in `ι → Fin s → F`. -/
theorem irs_rate_distance {ι : Type*} [Fintype ι] [Nonempty ι] {F : Type*} [Field F]
    [DecidableEq F] (domain : ι ↪ F) (k s : ℕ) [NeZero s] [NeZero (k / s)] :
    (Code.minDist ((irsCode domain k s : Submodule F (ι → Fin s → F)) :
        Set (ι → Fin s → F)) : ℝ) / Fintype.card ι
      = 1 - (LinearCode.alphabetRate (irsCode domain k s) : ℝ) + 1 / Fintype.card ι := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hmin : min (k / s) (Fintype.card ι) ≤ Fintype.card ι := min_le_right _ _
  rw [minDist_irsCode domain k s, alphabetRate_irsCode_eq_min domain k s]
  rw [show Fintype.card ι - k / s + 1 = Fintype.card ι - min (k / s) (Fintype.card ι) + 1 by
        omega,
    Nat.cast_add, Nat.cast_sub hmin, Nat.cast_one]
  field_simp

/-- **The interleave of a Reed–Solomon code is an `irsCode`.** Ships the identification that
`CodingTheory.lambda_extensionCode_eq_lambda_interleaved` needs in order to land on a code
this file bounds: an extension code over an RS base has the list size of `IRS[F, L, s·k', s]`.
Definitional once the degree arithmetic is done. -/
lemma interleavedCodeSet_rsCode_eq_irsCode {ι : Type*} {F : Type*} [Field F]
    (domain : ι ↪ F) (k' s : ℕ) (hs : 0 < s) :
    Code.interleavedCodeSet (κ := Fin s)
        ((ReedSolomon.code domain k' : Submodule F (ι → F)) : Set (ι → F))
      = ((irsCode domain (s * k') s : Submodule F (ι → Fin s → F)) : Set (ι → Fin s → F)) := by
  rw [irsCode, Nat.mul_div_cancel_left k' hs]
  rfl

end Interleaved
end ReedSolomon
