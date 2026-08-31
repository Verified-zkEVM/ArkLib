/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.HammingBallVolume
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Counting identities shared by the list-size bounds

The elementary identities that every bound in `ListDecodability.Bounds` rests on: the Hamming-ball
fiber count, the description of a relative-radius close-codeword set as an explicit
absolute-distance set, the Fubini averaging identity turning a sum of point-list sizes into
`|C| · Vol_q(δ, n)`, and the count `|C| = q ^ dim C` of a subspace, in both its natural and
real-exponent forms. None of them carries a list-decoding hypothesis and none belongs to a single
bound family, which is why they live here rather than in any one of the sibling files.

See `ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean` for the family overview, the
quantification conventions, and the references.
-/

-- All three are load-bearing, verified by removing them and rebuilding: the statements below carry
-- `[Fintype ι]` / `[DecidableEq F]` and section variables that their *proofs* do not use, which the
-- corresponding linters each report.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal
open Code

section LowerBounds_General

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Hamming-ball fiber count.** For a fixed centre `c`, the number of words `f` within
absolute distance `⌊δ · n⌋` of `c` equals `Vol_q(δ, n)` (independent of `c`), via the
existing `hammingBallVolume_eq_ncard_hammingBall` bridge.

Stated for an arbitrary finite alphabet rather than a linear code over a field: the count is pure
`hammingDist` combinatorics, and the alphabet-generic volume bounds need it at that generality. -/
theorem card_filter_hammingDist_le_eq_hammingBallVolume {A : Type} [Fintype A] [DecidableEq A]
    (c : ι → A) (δ : ℝ) :
    (Finset.univ.filter (fun f : ι → A => hammingDist c f ≤ ⌊δ * Fintype.card ι⌋₊)).card
      = hammingBallVolume (Fintype.card A) δ (Fintype.card ι) := by
  rw [hammingBallVolume_eq_ncard_hammingBall δ c, ← Set.ncard_coe_finset]
  congr 1
  ext f
  -- Both sides are `hammingDist c f ≤ ⌊δ·n⌋`; the two `DecidableEq F` instances differ
  -- (`Code.hammingBall` carries a classical one), which `congr!` discharges.
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
    Code.mem_hammingBall_iff]
  congr!

/-- **Relative-distance close-codeword set as an explicit absolute-distance set.**

Stated for an arbitrary alphabet rather than a linear code over a field: the identity is pure
arithmetic on `hammingDist`, and the large-alphabet barrier needs it at that generality. -/
theorem closeCodewordsRel_eq_setOf {A : Type} [DecidableEq A]
    (C : Set (ι → A)) (δ : ℝ) (hδ : 0 ≤ δ) (f : ι → A) :
    closeCodewordsRel C f δ =
      {c : ι → A | c ∈ C ∧ hammingDist c f ≤ ⌊δ * Fintype.card ι⌋₊} := by
  have h_n_pos : 0 < Fintype.card ι := Fintype.card_pos
  ext c
  simp only [closeCodewordsRel, Code.relHammingBall, Set.mem_ofPred_eq,
    Code.relHammingDist, NNRat.cast_div, NNRat.cast_natCast]
  refine and_congr_right (fun _ => ?_)
  rw [div_le_iff₀ (by exact_mod_cast h_n_pos), ← Nat.le_floor_iff (by positivity)]
  rw [hammingDist_comm c f]
  constructor <;> intro h <;> · convert h using 2

/-- **A subspace has `q ^ dim` elements.** Stated for a submodule of an arbitrary finite
`F`-module, since the list-size bounds apply it both to a code in `F^n` and to the kernel of a
projection out of one. -/
theorem submodule_ncard_eq_pow_finrank {V : Type*} [AddCommGroup V] [Module F V] [Finite V]
    (W : Submodule F V) :
    (W : Set V).ncard = Fintype.card F ^ Module.finrank F W := by
  have h1 : (W : Set V).ncard = Nat.card W := by
    rw [← Nat.card_coe_set_eq]
    rfl
  rw [h1, ← Nat.card_eq_fintype_card (α := F)]
  exact Module.natCard_eq_pow_finrank (K := F) (V := W)

/-- **A linear code has `q ^ dim` codewords**, in the real-exponent form the barrier arguments
consume. -/
theorem submodule_ncard_eq_rpow_finrank (C : Submodule F (ι → F)) :
    ((C : Set (ι → F)).ncard : ℝ)
      = (Fintype.card F : ℝ) ^ (Module.finrank F C : ℝ) := by
  rw [submodule_ncard_eq_pow_finrank, Nat.cast_pow, Real.rpow_natCast]

open Classical in
/-- **Averaging identity (Fubini), for an arbitrary code over a finite alphabet.** Summing the
point-list size `|Λ(C, δ, f)|` over all centres `f` gives `|C| · Vol_q(δ, n)`: swap the order of
summation and use that each codeword `c ∈ C` is counted once per centre in its `⌊δ·n⌋`-ball, of
which there are exactly `Vol_q(δ, n)`.

Nothing here is linear: the argument only ever asks whether `c ∈ C`. Stating it over a plain
`Set (ι → A)` is what lets the volume lower bounds hold at the generality their sources claim,
with the field-linear `sum_ncard_closeCodewordsRel_eq` below as the specialization. -/
theorem sum_ncard_closeCodewordsRel_eq_of_set {A : Type} [Fintype A] [DecidableEq A]
    (C : Set (ι → A)) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∑ f : ι → A, (closeCodewordsRel C f δ).ncard
      = C.ncard * hammingBallVolume (Fintype.card A) δ (Fintype.card ι) := by
  have hsummand : ∀ f : ι → A, (closeCodewordsRel C f δ).ncard
      = (Finset.univ.filter
          (fun c : ι → A => c ∈ C ∧ hammingDist c f ≤ ⌊δ * Fintype.card ι⌋₊)).card := by
    intro f
    rw [closeCodewordsRel_eq_setOf C δ hδ f, ← Set.ncard_coe_finset]
    congr 1
    ext c
    simp
  simp_rw [hsummand, Finset.card_filter]
  rw [Finset.sum_comm]
  have hstep : ∀ c : ι → A,
      (∑ f : ι → A, if c ∈ C ∧ hammingDist c f ≤ ⌊δ * Fintype.card ι⌋₊ then 1 else 0)
        = if c ∈ C then hammingBallVolume (Fintype.card A) δ (Fintype.card ι) else 0 := by
    intro c
    by_cases hc : c ∈ C
    · simp only [hc, true_and, if_true]
      rw [← Finset.card_filter]
      exact card_filter_hammingDist_le_eq_hammingBallVolume c δ
    · simp [hc]
  simp_rw [hstep]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul]
  congr 1
  rw [← Set.ncard_coe_finset]
  congr 1
  ext c; simp

/-- **Averaging identity (Fubini)** for a field-linear code, the specialization of
`sum_ncard_closeCodewordsRel_eq_of_set` at `C : Submodule F (ι → F)`. -/
theorem sum_ncard_closeCodewordsRel_eq
    (C : Submodule F (ι → F)) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∑ f : ι → F, (closeCodewordsRel ((C : Set (ι → F))) f δ).ncard
      = (C : Set (ι → F)).ncard * hammingBallVolume (Fintype.card F) δ (Fintype.card ι) :=
  sum_ncard_closeCodewordsRel_eq_of_set (C : Set (ι → F)) δ hδ

end LowerBounds_General

end CodingTheory
