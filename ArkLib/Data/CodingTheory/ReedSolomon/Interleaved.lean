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

- `ReedSolomon.Interleaved.dim_irsCode` — `Module.finrank F (irsCode domain k s) = s * (k / s)`,
  a two-line corollary of the general `Code.finrank_moduleInterleavedCode` together with
  `ReedSolomon.dim_eq_deg_of_le`.
- `ReedSolomon.Interleaved.dim_irsCode_of_dvd` — the paper-shaped specialisation
  `Module.finrank F (irsCode domain k s) = k` under `s ∣ k`.

## References

- [ABF26] Arnon-Boneh-Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026. §2.4 Definition 2.13.
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

/-- **Dimension of `irsCode`.** Equal to `s * (k / s)` — interleaving multiplies the underlying
RS code's dimension by the interleaving factor (`Code.finrank_moduleInterleavedCode`), and the
underlying `RS[F, L, k/s]` attains its full dimension `k / s` in the Singleton-tight regime
`k / s ≤ Fintype.card ι` (`ReedSolomon.dim_eq_deg_of_le`).

Note the `Nat` truncation in `k / s`: the value is `k` on the nose only when `s ∣ k`, see
`dim_irsCode_of_dvd`. -/
lemma dim_irsCode {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    (domain : ι ↪ F) (k s : ℕ)
    (h_rs_full : k / s ≤ Fintype.card ι) :
    Module.finrank F (irsCode domain k s) = s * (k / s) := by
  rw [irsCode, Code.finrank_moduleInterleavedCode, Fintype.card_fin]
  exact congrArg (s * ·) (ReedSolomon.dim_eq_deg_of_le (n := k / s) (α := domain) h_rs_full)

/-- Paper-shaped dimension formula in the divisible case: when `s ∣ k` (the implicit
convention of ABF26 Definition 2.13, satisfied by every instantiation in the paper),
`dim(IRS[F, L, k, s]) = k` on the nose. -/
lemma dim_irsCode_of_dvd {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    (domain : ι ↪ F) (k s : ℕ) (hdvd : s ∣ k)
    (h_rs_full : k / s ≤ Fintype.card ι) :
    Module.finrank F (irsCode domain k s) = k := by
  rw [dim_irsCode domain k s h_rs_full, Nat.mul_div_cancel' hdvd]

end Interleaved
end ReedSolomon
