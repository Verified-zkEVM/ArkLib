/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Ilia Vlasov, Aristotle (Harmonic)
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ListDecodability.AgreementBound

/-!
# Interleaved Reed-Solomon codes

The `s`-interleaved Reed-Solomon code is the `s`-fold interleave of the Reed-Solomon code of
degree bound `⌊k/s⌋`: each codeword is an `s`-tuple of base codewords, arranged
column-wise, so that the code lives over the alphabet `Fin s → F`.

## Main definitions

* `ReedSolomon.Interleaved.irsCode`

## Main statements

* `ReedSolomon.Interleaved.dim_irsCode_eq_min`, `..._dim_irsCode`, `..._dim_irsCode_of_dvd` —
  the dimension is `s * min ⌊k/s⌋ |L|`, hence `s * ⌊k/s⌋` below saturation and `k` when
  `s ∣ k`.
* `ReedSolomon.Interleaved.minDist_irsCode_eq_minDist_rsCode`,
  `ReedSolomon.Interleaved.minDist_irsCode` — interleaving preserves the minimum block
  distance, which is therefore `|L| - ⌊k/s⌋ + 1`.
* `ReedSolomon.Interleaved.alphabetRate_irsCode_eq_min`,
  `ReedSolomon.Interleaved.alphabetRate_irsCode` — the alphabet-normalized rate is
  `min ⌊k/s⌋ |L| / |L|`, hence `⌊k/s⌋ / |L|` below saturation.
* `ReedSolomon.Interleaved.irs_rate_distance` — the code satisfies the MDS rate-distance
  equation `δ_min = 1 - ρ + 1/n` at that rate, with no divisibility hypothesis.

## References

* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and Correlated
    Agreement*][ABF26]
* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
      with Super-Fast Verification*][ACFY24]
-/

namespace ReedSolomon
namespace Interleaved

/-- The `s`-interleaved Reed-Solomon code, the `s`-fold interleave of
`ReedSolomon.code domain (k / s)`, as a `Submodule F (ι → Fin s → F)`.

Note that the inner degree bound is the `Nat` division `⌊k/s⌋`, so the total dimension is
`s * ⌊k/s⌋`, which is `k` only when `s ∣ k`: at `k = 5`, `s = 2` it is `4`. A caller wanting
the `s`-interleave of `ReedSolomon.code domain k'` for a given inner degree bound `k'` should
write `irsCode domain (s * k') s`. -/
noncomputable def irsCode {ι : Type*} {F : Type*} [Semiring F]
    (domain : ι ↪ F) (k s : ℕ) : Submodule F (ι → Fin s → F) :=
  (ReedSolomon.code domain (k / s)) ^⋈ (Fin s)

/-- The dimension of an interleaved Reed-Solomon code is `s * min ⌊k/s⌋ |L|`: interleaving
multiplies the base dimension by `s`, and the base code has dimension `min ⌊k/s⌋ |L|`. -/
lemma dim_irsCode_eq_min {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    (domain : ι ↪ F) (k s : ℕ) :
    Module.finrank F (irsCode domain k s) = s * min (k / s) (Fintype.card ι) := by
  rw [irsCode, Code.finrank_moduleInterleavedCode, Fintype.card_fin]
  exact congrArg (s * ·) (ReedSolomon.dim_eq_min_deg_card (n := k / s) (α := domain))

/-- Below saturation, `⌊k/s⌋ ≤ |L|`, the dimension is `s * ⌊k/s⌋`. This is `k` only when
`s ∣ k`; see `dim_irsCode_of_dvd`. -/
lemma dim_irsCode {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    (domain : ι ↪ F) (k s : ℕ)
    (h_rs_full : k / s ≤ Fintype.card ι) :
    Module.finrank F (irsCode domain k s) = s * (k / s) := by
  rw [dim_irsCode_eq_min domain k s, min_eq_left h_rs_full]

/-- When `s ∣ k` and the base code is below saturation, the dimension is exactly `k`. -/
lemma dim_irsCode_of_dvd {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    (domain : ι ↪ F) (k s : ℕ) (hdvd : s ∣ k)
    (h_rs_full : k / s ≤ Fintype.card ι) :
    Module.finrank F (irsCode domain k s) = k := by
  rw [dim_irsCode domain k s h_rs_full, Nat.mul_div_cancel' hdvd]

/-- Interleaving preserves the minimum block distance, so an interleaved Reed-Solomon code
has the minimum distance of its base code.

The metric is the block one on `ι → Fin s → F`: a position counts as a disagreement when the
whole `s`-tuple differs, which is why interleaving leaves it unchanged. Nothing
Reed-Solomon-specific enters; this is `Code.minDist_interleavedCodeSet`. -/
theorem minDist_irsCode_eq_minDist_rsCode {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    [DecidableEq F] (domain : ι ↪ F) (k s : ℕ) [NeZero s] :
    Code.minDist ((irsCode domain k s : Submodule F (ι → Fin s → F)) : Set (ι → Fin s → F))
      = Code.minDist ((ReedSolomon.code domain (k / s) : Submodule F (ι → F)) : Set (ι → F)) := by
  have : Nonempty (Fin s) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne s))
  rw [irsCode, Code.interleavedCode_eq_interleavedCodeSet_of_moduleCode]
  exact Code.minDist_interleavedCodeSet (κ := Fin s) _

/-- The alphabet-normalized rate of an interleaved Reed-Solomon code is
`min ⌊k/s⌋ |L| / |L|`. The interleaving factor `s` multiplies the dimension and the
alphabet normalization divides it back out, so the rate does not see `s`. -/
lemma alphabetRate_irsCode_eq_min {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    (domain : ι ↪ F) (k s : ℕ) [NeZero s] :
    (LinearCode.alphabetRate (irsCode domain k s) : ℝ)
      = (min (k / s) (Fintype.card ι) : ℕ) / Fintype.card ι := by
  have hs : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  rw [LinearCode.alphabetRate_cast_eq, dim_irsCode_eq_min domain k s, Nat.cast_mul,
    mul_div_mul_left _ _ (ne_of_gt hs)]

/-- Below saturation, `⌊k/s⌋ ≤ |L|`, the alphabet-normalized rate is `⌊k/s⌋ / |L|`. -/
lemma alphabetRate_irsCode {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    (domain : ι ↪ F) (k s : ℕ) [NeZero s]
    (h_rs_full : k / s ≤ Fintype.card ι) :
    (LinearCode.alphabetRate (irsCode domain k s) : ℝ)
      = (k / s : ℕ) / Fintype.card ι := by
  rw [alphabetRate_irsCode_eq_min domain k s, min_eq_left h_rs_full]

/-- The minimum block distance of an interleaved Reed-Solomon code is `|L| - ⌊k/s⌋ + 1`.

Neither divisibility nor non-saturation is needed: once `⌊k/s⌋ ≥ |L|` the base code is all of
`F^L`, the `Nat` subtraction truncates to `0`, and both sides are `1`.

The hypothesis `0 < ⌊k/s⌋` is necessary: at `k < s` the inner degree bound is `0`, so the
code is `⊥` and its minimum distance is `0`, against a right-hand side of `|L| + 1`. It is
taken explicitly rather than as `[NeZero (k / s)]`, which instance resolution could never
discharge for symbolic `k` and `s`. -/
theorem minDist_irsCode {ι : Type*} [Fintype ι] [Nonempty ι] {F : Type*} [Field F]
    [DecidableEq F] (domain : ι ↪ F) (k s : ℕ) [NeZero s] (hks : 0 < k / s) :
    Code.minDist ((irsCode domain k s : Submodule F (ι → Fin s → F)) : Set (ι → Fin s → F))
      = Fintype.card ι - k / s + 1 := by
  let : Inhabited ι := Classical.inhabited_of_nonempty ‹Nonempty ι›
  have : NeZero (k / s) := ⟨by omega⟩
  rw [minDist_irsCode_eq_minDist_rsCode, ReedSolomon.minDist_eq_card_sub_min_add_1]
  omega

/-- An interleaved Reed-Solomon code satisfies the MDS rate-distance equation at its
alphabet-normalized rate `ρ`:

  `δ_min (irsCode domain k s) = 1 - ρ + 1/n` .

No divisibility or non-saturation hypothesis is needed, in contrast with
`ReedSolomon.Folded.frs_rate_distance_of_dvd`, because interleaving truncates only once:
the dimension `s * min ⌊k/s⌋ n` and the distance `n - ⌊k/s⌋ + 1` degrade through the same
`min`, and the alphabet normalization cancels the interleaving factor, leaving
`ρ = min ⌊k/s⌋ n / n`. In the saturated regime both sides are `1/n`. -/
theorem irs_rate_distance {ι : Type*} [Fintype ι] [Nonempty ι] {F : Type*} [Field F]
    [DecidableEq F] (domain : ι ↪ F) (k s : ℕ) [NeZero s] (hks : 0 < k / s) :
    (Code.minDist ((irsCode domain k s : Submodule F (ι → Fin s → F)) :
        Set (ι → Fin s → F)) : ℝ) / Fintype.card ι
      = 1 - (LinearCode.alphabetRate (irsCode domain k s) : ℝ) + 1 / Fintype.card ι := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hmin : min (k / s) (Fintype.card ι) ≤ Fintype.card ι := min_le_right _ _
  rw [minDist_irsCode domain k s hks, alphabetRate_irsCode_eq_min domain k s]
  rw [show Fintype.card ι - k / s + 1 = Fintype.card ι - min (k / s) (Fintype.card ι) + 1 by
        omega,
    Nat.cast_add, Nat.cast_sub hmin, Nat.cast_one]
  field_simp

/-- The `s`-fold interleave of `ReedSolomon.code domain k'` is `irsCode domain (s * k') s`.
Definitional once the degree arithmetic is done. -/
lemma interleavedCodeSet_rsCode_eq_irsCode {ι : Type*} {F : Type*} [Field F]
    (domain : ι ↪ F) (k' s : ℕ) (hs : 0 < s) :
    Code.interleavedCodeSet (κ := Fin s)
        ((ReedSolomon.code domain k' : Submodule F (ι → F)) : Set (ι → F))
      = ((irsCode domain (s * k') s : Submodule F (ι → Fin s → F)) : Set (ι → Fin s → F)) := by
  rw [irsCode, Nat.mul_div_cancel_left k' hs]
  rfl

/-- Two distinct interleaved Reed-Solomon codewords agree in fewer than `m` positions.
They differ in some entry, hence in some row `j`, and a position where the two `Fin k`-tuples
agree is in particular a position where the `j`-th rows agree; those rows are distinct
codewords of `ReedSolomon.code domain m`, so they agree in fewer than `m` positions. -/
lemma agree_lt_of_mem_interleavedCodeSet {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    [DecidableEq F] {domain : ι ↪ F} {m k : ℕ} {c c' : ι → Fin k → F}
    (hc : c ∈ Code.interleavedCodeSet (κ := Fin k) (ReedSolomon.code domain m : Set (ι → F)))
    (hc' : c' ∈ Code.interleavedCodeSet (κ := Fin k) (ReedSolomon.code domain m : Set (ι → F)))
    (hne : c ≠ c') : Code.agree c c' < m := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hi
  have hrow : (fun i ↦ c i j) ≠ (fun i ↦ c' i j) := fun h ↦ hj (congrFun h i)
  have hle : Code.agree c c' ≤ Code.agree (fun i ↦ c i j) (fun i ↦ c' i j) := by
    refine Finset.card_le_card ?_
    intro i' hi'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' ⊢
    exact congrFun hi' j
  exact lt_of_le_of_lt hle (ReedSolomon.agree_lt_of_mem_code (hc j) (hc' j) hrow)

open NNReal in
/-- The `k`-fold interleave of the Reed-Solomon code `RS[F, domain, m]` of rate `ρ` is
  `(1 - √ρ - η, 1/(2η√ρ))`-list decodable, for every `η > 0`: the same Johnson-type bound as for
  the base code, at the same list size.

  This appears as lemma 4.4 in [ACFY24].
-/
theorem interleaved_listDecodable {F : Type*} [Field F]
  {ι : Type*} [Fintype ι] [Nonempty ι]
  (domain : ι ↪ F) (m k : ℕ) (hm : 0 < m)
  (η : ℝ≥0) (hη : 0 < η) :
  Code.IsListDecodable
    (Code.interleavedCodeSet (κ := Fin k) (ReedSolomon.code domain m : Set (ι → F)))
    (1 - (ReedSolomon.sqrtRate m domain) - η)
    (1 / (2 * η * (ReedSolomon.sqrtRate m domain))) := by
  classical
  have hnpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hs : 0 < (ReedSolomon.sqrtRate m domain : ℝ) := ReedSolomon.sqrtRate_pos hm
  have hηR : (0 : ℝ) < (η : ℝ) := by exact_mod_cast hη
  refine Code.isListDecodable_of_forall_finset_card_le fun y T hT => ?_
  have hpair : ∀ c ∈ Code.interleavedCodeSet (κ := Fin k)
      (ReedSolomon.code domain m : Set (ι → F)), ∀ c' ∈ Code.interleavedCodeSet (κ := Fin k)
      (ReedSolomon.code domain m : Set (ι → F)), c ≠ c' →
      (Code.agree c c' : ℝ)
        ≤ (ReedSolomon.sqrtRate m domain : ℝ) ^ 2 * (Fintype.card ι : ℝ) := by
    intro c hc c' hc' hne
    have h1 : Code.agree c c' ≤ min m (Fintype.card ι) :=
      le_min (le_of_lt (agree_lt_of_mem_interleavedCodeSet hc hc' hne)) Code.agree_le_card
    have h2 : (Code.agree c c' : ℝ) ≤ (min m (Fintype.card ι) : ℝ) := by exact_mod_cast h1
    rw [ReedSolomon.sqrtRate_sq, div_mul_cancel₀ _ (ne_of_gt hnpos)]
    exact h2
  have hbound := Code.card_le_of_pairwise_agree_le hs hηR hpair y T hT
  refine hbound.trans (le_of_eq ?_)
  push_cast
  ring

end Interleaved
end ReedSolomon
