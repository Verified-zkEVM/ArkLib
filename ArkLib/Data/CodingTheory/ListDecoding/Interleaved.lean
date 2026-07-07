/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ListDecodability
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# List-decoding bounds for interleaved codes

This file hosts list-decoding theorems about interleaved codes. The base
`InterleavedCode` module contains the structural interleaving API; paper-cited
list-size bounds live here so foundational interleaving code does not import the
list-decoding layer or logarithm machinery.
-/

namespace InterleavedCode

open ListDecodable Code

/-- **Lemma 2.10 of [ABF26]** (= **[GGR11]**) — interleaved-code
list-size bound.

Let `C` be a code with relative minimum distance `δ_C := δ_min(C) / |ι|`,
and let `δ ∈ [0, δ_C)`. Define
  `η := δ_C - δ`,
  `b := ⌈δ / η⌉`,
  `r := ⌈log₂(δ_C / η)⌉`.
Then for every `m ≥ 1`,

  `|Λ(C^{≡m}, δ)| ≤ (b+r choose r) · |Λ(C, δ)|^r`.

The key feature is that the bound's dependence on the interleaving
factor `m` is hidden inside the constant `(b+r choose r)` — once `δ`
is fixed, the list size of `C^{≡m}` grows as a *polynomial in*
`|Λ(C, δ)|` of degree `r`, **independent of `m`**. Used in ABF26 §3
list-decoding analyses and §6.3.

External admit — paper-cited [GGR11]. -/
theorem lambda_le_ggr11 {ι F : Type} [Fintype ι] [Field F] [DecidableEq F]
    (C : Set (ι → F)) (δ : ℝ) (m : ℕ) (_hm : 1 ≤ m)
    (_hδ_lb : 0 ≤ δ)
    (_hδ_ub : δ < (Code.minDist C : ℝ) / Fintype.card ι) :
    let η : ℝ := (Code.minDist C : ℝ) / Fintype.card ι - δ
    let b : ℕ := ⌈δ / η⌉₊
    let r : ℕ := ⌈Real.log ((Code.minDist C : ℝ) / Fintype.card ι / η) /
                  Real.log 2⌉₊
    Lambda (interleavedCodeSet (κ := Fin m) C) δ ≤
      ((b + r).choose r : ℕ∞) * (Lambda C δ) ^ r := by
  sorry -- ABF26-L2.10; external admit [GGR11].

end InterleavedCode
