/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Incremental

/-!
# The per-challenge bad-event bound at one fold

`prob_incrementalFoldingBadEvent_fresh_le` bounds, for one fresh challenge, the probability that
the incremental folding bad event appears. This test pins it to [DP24] Proposition 4.21 at
folding factor `ϑ = 1`: for a block of a single fold, the fresh event at `k = 0` is exactly the
folding bad event of [DP24] Definition 4.20 (`foldingBadEvent`), so the headline gives
`µ(Eᵢ) ≤ |S⁽ⁱ⁺¹⁾| / |L|`, which is the paper's bound `ϑ · |S⁽ⁱ⁺ᶿ⁾| / |L|` at `ϑ = 1`. The proof
uses only the headline and the two endpoint lemmas of `incrementalFoldingBadEvent` (`False` at
`k = 0`, the folding bad event at `k = ϑ`).

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
-/

open OracleSpec OracleComp ProtocolSpec AdditiveNTT Binius.BinaryBasefold
open scoped NNReal ENNReal

namespace ArkLibTest.Binius.BinaryBasefold

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q]
  [Fact (Nat.Prime (ringChar 𝔽q))] [Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [Fact (LinearIndependent 𝔽q β)] [Fact (β 0 = 1)]
variable {ℓ 𝓡 : ℕ} [NeZero 𝓡] {h_ℓ_add_R_rate : ℓ + 𝓡 < r} [SampleableType L]

/-- [DP24] Proposition 4.21 at `ϑ = 1`, from the per-challenge bound. -/
theorem prob_foldingBadEvent_le_of_one_fold (i : Fin r) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + 1) (h_destIdx_le : destIdx.val ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    Pr{ let r' ← $ᵗ L }[ foldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i 1
        h_destIdx h_destIdx_le f (fun _ => r') ] ≤
      (Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) : ℝ≥0∞) / (Fintype.card L) := by
  have h := prob_incrementalFoldingBadEvent_fresh_le 𝔽q β (ϑ := 1)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (midIdx_i := i) (midIdx_i_succ := destIdx)
    (destIdx := destIdx) 0 Nat.one_pos (by simp) (by omega) h_destIdx h_destIdx_le f Fin.elim0
  refine le_trans (prEvent_mono ($ᵗ L) _ _ ?_) h
  intro r' hbad
  refine ⟨incrementalFoldingBadEvent_of_k_eq_0_is_false 𝔽q β i 0 rfl rfl h_destIdx
    h_destIdx_le f Fin.elim0, ?_⟩
  have hsnoc : (Fin.snoc (Fin.elim0 : Fin 0 → L) r' : Fin (0 + 1) → L) = fun _ => r' := by
    funext x
    rw [show x = Fin.last 0 from Fin.ext (by omega), Fin.snoc_last]
  rw [hsnoc]
  exact (incrementalFoldingBadEvent_eq_foldingBadEvent_of_k_eq_ϑ 𝔽q β (ϑ := 1) i
    (midIdx := destIdx) rfl h_destIdx h_destIdx_le f (fun _ => r')).2 hbad

/--
info: 'ArkLibTest.Binius.BinaryBasefold.prob_foldingBadEvent_le_of_one_fold' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms prob_foldingBadEvent_le_of_one_fold

/--
info: 'Binius.BinaryBasefold.prob_incrementalFoldingBadEvent_fresh_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms prob_incrementalFoldingBadEvent_fresh_le

end ArkLibTest.Binius.BinaryBasefold
