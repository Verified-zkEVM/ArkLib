/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Fri.Spec.Extraction.RoundCost
public import ArkLib.ProofSystem.Fri.Spec.Extraction.GeneratorCost

/-!
# A closed field-operation budget for query generation

The numerical envelope bounds the binary initial-point generator and every round's projection,
block-node generation, and final squaring. It uses only the folding schedule and domain size.
-/

@[expose] public section

namespace Fri.Spec.Extractor

/-- A closed envelope for all field operations used to generate one position's query points. -/
def generationBudget (n : ℕ) {r : ℕ} (s : Fin (r + 1) → ℕ+) : ℕ :=
  2 * (n + 2) + ∑ i, ((4 * 2 ^ (s i).val + 8) * (n + 1))

/-- The explicit squaring and binary-power loop bounds fit the closed generation budget. -/
theorem generation_mul_le {n k : ℕ} (s : Fin (k + 1) → ℕ+)
    (hs : (∑ i, (s i).val) ≤ n) :
    2 * n + 1 + (∑ i, (foldingPrefix s i.castSucc +
      2 ^ (s i).val * (2 * (s i).val + 1) + (s i).val)) ≤ generationBudget n s := by
  have hround (i : Fin (k + 1)) :
      foldingPrefix s i.castSucc + 2 ^ (s i).val * (2 * (s i).val + 1) + (s i).val ≤
        (4 * 2 ^ (s i).val + 8) * (n + 1) := by
    have hp := (foldingPrefix_le s i.castSucc).trans hs
    have hi : (s i).val ≤ n :=
      (Finset.single_le_sum (f := fun j ↦ (s j).val) (by simp) (by simp)).trans hs
    have hm := Nat.mul_le_mul_left (2 ^ (s i).val) hi
    generalize hb : 2 ^ (s i).val = b at *
    nlinarith only [hp, hi, hm, Nat.zero_le (b * n), Nat.zero_le b, Nat.zero_le n]
  exact Nat.add_le_add (by omega) (Finset.sum_le_sum (fun i _ ↦ hround i))

end Fri.Spec.Extractor
