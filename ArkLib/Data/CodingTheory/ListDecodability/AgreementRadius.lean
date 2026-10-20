/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability

/-!
# Agreement lists and the relative radius `1 - a / n`

For words over an arbitrary alphabet with `n` coordinates, agreeing with `y` in at least `a`
coordinates means disagreeing in at most `n - a`, so the relative Hamming distance to `y` is at
most `1 - a / n`. The codewords of a code `C` with at least `a` agreements with `y` therefore lie
in the point list `closeCodewordsRel C y (1 - a / n)`, and their number is bounded by
`Code.Lambda C (1 - a / n)`. This is the radius convention of `Code.Lambda_le_pairwiseJohnson`.
The Reed–Solomon consumers are in
`ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AnchoredAgreement`.

## Main statements

* `Code.relHammingDist_le_one_sub_div_of_le_agree`: `a ≤ agree c y` gives
  `δᵣ(y, c) ≤ 1 - a / n`.
* `Code.relHammingDist_le_one_sub_div_iff`: for `0 < n` and real `x`,
  `δᵣ(y, c) ≤ 1 - x / n ↔ x ≤ agree c y`.
* `Code.mem_closeCodewordsRel_of_le_agree`: the same statement for point lists.
* `Code.encard_setOf_le_agree_le_Lambda`: the agreement list is bounded by `Lambda`.
* `Code.encard_setOf_le_agree_encode_le_Lambda`: the same bound for messages whose encodings
  lie in `C`, under an encoding that is injective on the messages considered.
-/

@[expose] public section

namespace Code

variable {ι : Type*} [Fintype ι] {A : Type*} [DecidableEq A]

/-- **Agreement bounds the relative distance.** If `c` agrees with `y` in at least `a` of the `n`
coordinates, then `δᵣ(y, c) ≤ 1 - a / n`.

No hypothesis on `n` is needed: for `n = 0` the relative distance is `0` and the right-hand side is
`1`. -/
theorem relHammingDist_le_one_sub_div_of_le_agree {c y : ι → A} {a : ℕ} (h : a ≤ agree c y) :
    (δᵣ(y, c) : ℝ) ≤ 1 - (a : ℝ) / Fintype.card ι := by
  rw [relHammingDist_coe, hammingDist_comm]
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hn | hn
  · simp [hn]
  have hsum : ((agree c y : ℕ) : ℝ) + (Δ₀(c, y) : ℕ) = Fintype.card ι := by
    exact_mod_cast agree_add_hammingDist
  have hnR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have haR : (a : ℝ) ≤ agree c y := by exact_mod_cast h
  rw [div_le_iff₀ hnR, sub_mul, div_mul_cancel₀ _ hnR.ne']
  linarith

/-- **Relative distance at the radius `1 - x / n`.** For a nonempty coordinate type with `n`
coordinates and a real `x`, `δᵣ(y, c) ≤ 1 - x / n` holds exactly when `c` agrees with `y` in at
least `x` coordinates.

The hypothesis `0 < n` is needed: for `n = 0` the left side is `0 ≤ 1` and the right side is
`x ≤ 0`. -/
theorem relHammingDist_le_one_sub_div_iff (hn : 0 < Fintype.card ι) {c y : ι → A} {x : ℝ} :
    (δᵣ(y, c) : ℝ) ≤ 1 - x / Fintype.card ι ↔ x ≤ agree c y := by
  rw [relHammingDist_coe, hammingDist_comm]
  have hsum : ((agree c y : ℕ) : ℝ) + (Δ₀(c, y) : ℕ) = Fintype.card ι := by
    exact_mod_cast agree_add_hammingDist
  have hnR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  rw [div_le_iff₀ hnR, sub_mul, div_mul_cancel₀ _ hnR.ne', one_mul]
  constructor <;> intro h <;> linarith

/-- **Agreement lists lie in point lists.** A codeword with at least `a` agreements with `y` is in
the point list of `C` around `y` at relative radius `1 - a / n`. -/
theorem mem_closeCodewordsRel_of_le_agree {C : Set (ι → A)} {c y : ι → A} {a : ℕ} (hc : c ∈ C)
    (h : a ≤ agree c y) : c ∈ closeCodewordsRel C y (1 - (a : ℝ) / Fintype.card ι) :=
  mem_closeCodewordsRel_iff.mpr ⟨hc, relHammingDist_le_one_sub_div_of_le_agree h⟩

/-- **Agreement lists are bounded by `Lambda`.** The codewords of `C` with at least `a`
agreements with `y` number at most `Lambda C (1 - a / n)`. In particular a finite bound
`Lambda C (1 - a / n) ≤ L` makes every such list finite with at most `L` elements. -/
theorem encard_setOf_le_agree_le_Lambda (C : Set (ι → A)) (y : ι → A) (a : ℕ) :
    {c | c ∈ C ∧ a ≤ agree c y}.encard ≤ Lambda C (1 - (a : ℝ) / Fintype.card ι) :=
  encard_le_Lambda_of_subset_closeCodewordsRel (f := y) fun _ hc ↦
    mem_closeCodewordsRel_of_le_agree hc.1 hc.2

/-- **Agreement lists of messages are bounded by `Lambda`.** Let `encode : M → ι → A` map every
message of `S` into `C` and be injective on `S`. Then the messages of `S` whose encodings have at
least `a` agreements with `y` number at most `Lambda C (1 - a / n)`.

Injectivity on `S` is needed: for a constant encoding into `C`, every message of `S` has the same
encoding, and `S` can be larger than any list bound. For Reed–Solomon codes the encoding is
evaluation on the domain and `S` is the set of polynomials of degree below the dimension. -/
theorem encard_setOf_le_agree_encode_le_Lambda {M : Type*} (C : Set (ι → A)) (y : ι → A)
    (a : ℕ) {encode : M → ι → A} {S : Set M} (hinj : Set.InjOn encode S)
    (hmem : ∀ m ∈ S, encode m ∈ C) :
    {m | m ∈ S ∧ a ≤ agree (encode m) y}.encard ≤ Lambda C (1 - (a : ℝ) / Fintype.card ι) := by
  rw [← (hinj.mono fun _ hm ↦ hm.1).encard_image]
  refine (Set.encard_le_encard ?_).trans (encard_setOf_le_agree_le_Lambda C y a)
  rintro _ ⟨m, hm, rfl⟩
  exact ⟨hmem m hm.1, hm.2⟩

end Code
