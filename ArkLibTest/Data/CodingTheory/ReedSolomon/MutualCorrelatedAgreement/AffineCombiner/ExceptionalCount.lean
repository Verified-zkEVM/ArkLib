/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.ExceptionalCount

/-!
# Acceptance cases for the exceptional count through the factors of the interpolant

The generic count at `|κ| = 2` and `e = 1` gives the Reed–Solomon term.

That term is `4 d² M² D³ (n / (A - B))²`.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

open ReedSolomon

-- At `|κ| = 2` and `e = 1`, the generic term is the Reed–Solomon term of Lemma 4.7.
example (d M D n A B : ℕ) (hBA : B < A) :
    (2 * d * M * ((n : ℝ) / (A - B - 1 + 1 : ℕ))) ^ 2 * D ^ (2 + 1) =
      4 * d ^ 2 * M ^ 2 * D ^ 3 * ((n : ℝ) / (A - B : ℕ)) ^ 2 := by
  rw [show A - B - 1 + 1 = A - B by omega]
  ring

/-- info: 'ReedSolomon.exists_factorRoots_finset_card_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.exists_factorRoots_finset_card_le

/-- info: 'ReedSolomon.exists_interpolantRoots_finset_card_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.exists_interpolantRoots_finset_card_le

/-- info: 'ReedSolomon.exists_affineExceptional_finset_card_le_of_interpolant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.exists_affineExceptional_finset_card_le_of_interpolant
