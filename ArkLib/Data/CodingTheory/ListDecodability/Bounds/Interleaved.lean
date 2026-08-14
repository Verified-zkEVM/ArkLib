/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ListDecodability
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# List-size bounds for interleaved codes

Paper-cited list-size bounds live in the `ListDecodability/Bounds` layer; the structural
interleaving API remains independent of list decoding.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and Correlated
  Agreement*][ABF26]
* [Gopalan, P., Guruswami, V., Raghavendra, P., *List Decoding Tensor Products and
  Interleaved Codes*][GGR11]
-/

set_option linter.unusedFintypeInType false

namespace InterleavedCode

open Code

/-- **ABF26 Lemma 2.10 / GGR11 Theorem 2.5.** Let `C` have relative minimum distance
`δ_C := minDist C / |ι|`, and let `δ ∈ [0, δ_C)`. With

* `η := δ_C - δ`,
* `b := ⌈δ / η⌉`, and
* `r := ⌈log₂(δ_C / η)⌉`,

the list size of every nonempty row-wise interleaving is bounded by
`choose (b + r) r * Lambda(C, δ)^r`, independently of the interleaving width. -/
theorem lambda_interleaved_le_choose_mul_pow {ι A : Type} [Fintype ι] [Fintype A]
    [DecidableEq A]
    (C : Set (ι → A)) (δ : ℝ) (m : ℕ) (_hm : 1 ≤ m)
    (_hδ_lb : 0 ≤ δ)
    (_hδ_ub : δ < (Code.minDist C : ℝ) / Fintype.card ι) :
    let δC : ℝ := (Code.minDist C : ℝ) / Fintype.card ι
    let η : ℝ := δC - δ
    let b : ℕ := ⌈δ / η⌉₊
    let r : ℕ := ⌈Real.log (δC / η) / Real.log 2⌉₊
    Lambda (interleavedCodeSet (κ := Fin m) C) δ ≤
      ((b + r).choose r : ℕ∞) * (Lambda C δ) ^ r := by
  sorry -- external admit [GGR11 Theorem 2.5].

end InterleavedCode
