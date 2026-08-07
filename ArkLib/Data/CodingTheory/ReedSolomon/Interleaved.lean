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

## Main lemmas

- `ReedSolomon.Interleaved.dim_irsCode` — `Module.finrank F (irsCode domain k s) = s · (k/s)`
  (proved via an injective F-linear `(Fin s → ↥RS) → (ι → Fin s → F)` with range
  exactly `irsCode`, plus `Module.finrank_pi_fintype` and `dim_eq_deg_of_le`).

## References

- [ABF26] Arnon-Boneh-Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026. §2.4 Definition 2.13.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ReedSolomon
namespace Interleaved

/-- **ABF26 Definition 2.13.** The `s`-interleaved Reed-Solomon code:

  `IRS[F, L, k, s] := (RS[F, L, k/s])^≡s`

Each codeword is an `s`-tuple of base RS codewords arranged column-wise. The carrier is
`Code.interleavedCodeSet (RS[F, L, k/s])`; closure under addition and scalar
multiplication follows from the same closure of the underlying RS code applied
column-by-column.

**Submodule structure.** Returns `Submodule F (ι → Fin s → F)` (equivalently
`ModuleCode ι F (Fin s → F)`) directly, so downstream theorems (e.g. T4.14) consume
it as an F-linear code without an existential wrap.

**Rounding convention.** The paper writes `k/s` and implicitly assumes `s ∣ k` so that
the message length divides cleanly into `s` blocks of size `k/s`. In Lean `k / s` is
Nat truncated division, which silently rounds when `s ∤ k`. Downstream theorems quoting
the paper directly (e.g. `dim(IRS) = k`) should add an explicit `s ∣ k` hypothesis at
the use site; we keep the definition itself unguarded so degenerate parameter regimes
type-check uniformly. -/
noncomputable def irsCode {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) : Submodule F (ι → Fin s → F) :=
  (ReedSolomon.code domain (k / s)) ^⋈ (Fin s)

/-- **Dimension of `irsCode`.** Equal to `s · (k / s)` — the interleave multiplies the
underlying RS code's dimension by the interleaving factor.

Requires `k / s ≤ Fintype.card ι` for the underlying RS code to attain its full
dimension `k / s` (the Singleton-tight regime); the bound holds with equality in this
regime. -/
lemma dim_irsCode {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ)
    (h_rs_full : k / s ≤ Fintype.card ι) :
    Module.finrank F (irsCode domain k s) = s * (k / s) := by
  -- Construct an injective F-linear map `(Fin s → ↥RS) → (ι → Fin s → F)` whose
  -- range is exactly `irsCode`, then chain finrank-equalities.
  let RS : Submodule F (ι → F) := ReedSolomon.code domain (k / s)
  let encoder : (Fin s → ↥RS) →ₗ[F] (ι → Fin s → F) :=
    { toFun := fun g i j ↦ ((g j : ι → F) i)
      map_add' := by intros; ext i j; simp
      map_smul' := by intros; ext i j; simp }
  -- Encoder values: `encoder g i j = (g j).val i`.
  have h_encoder_apply : ∀ (g : Fin s → ↥RS) (i : ι) (j : Fin s),
      encoder g i j = (g j : ι → F) i := fun _ _ _ ↦ rfl
  have h_inj : Function.Injective encoder := by
    intro g g' hgg'
    funext j
    apply Subtype.ext
    funext i
    have := congrFun (congrFun hgg' i) j
    simpa [h_encoder_apply] using this
  -- `encoder.range = irsCode`.
  have h_range : LinearMap.range encoder = irsCode domain k s := by
    unfold irsCode
    ext V
    simp only [LinearMap.mem_range]
    constructor
    · rintro ⟨g, rfl⟩
      -- Show `(RS) ^⋈ (Fin s)` membership: every column is in RS.
      intro j
      change (Matrix.transpose (encoder g) j) ∈ RS
      convert (g j).2 using 1
      rfl
    · intro hV
      -- `V ∈ irsCode` means `∀ j, V.transpose j ∈ RS`. Construct `g j := ⟨V.transpose j, hV j⟩`.
      refine ⟨fun j ↦ ⟨Matrix.transpose V j, hV j⟩, ?_⟩
      ext i j
      rfl
  -- Now: `finrank irsCode = finrank (Fin s → ↥RS) = s · finrank ↥RS = s · (k/s)`.
  rw [← h_range, LinearMap.finrank_range_of_inj h_inj]
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  congr 1
  -- `finrank F ↥RS = k / s` via `dim_eq_deg_of_le`.
  exact ReedSolomon.dim_eq_deg_of_le (n := k / s) (α := domain) h_rs_full

end Interleaved
end ReedSolomon
