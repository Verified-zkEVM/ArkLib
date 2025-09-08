/-
Helpers about minimum distance for linear codes and Reed–Solomon.
-/

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Tactic

noncomputable section

open Code

namespace ProximityToRS

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι]

/-- General helper: in any linear code, a nonzero codeword has weight at least the minimum distance.
Contraposition form: if a codeword has weight strictly less than `minDist`, it must be zero. -/
lemma zero_of_wt_lt_minDist
  (L : LinearCode ι F) {c : ι → F}
  (hc : c ∈ (L : Set (ι → F)))
  (hwt : Code.wt c < Code.minDist (L : Set (ι → F))) :
  c = 0 := by
  classical
  by_contra hcz
  -- From the definition of `minDist`, nonzero `c ∈ L` witnesses `minDist ≤ wt c`.
  have hmin : Code.minDist (L : Set (ι → F)) ≤ Code.wt c := by
    unfold Code.minDist
    refine Nat.sInf_le ?_
    exact ⟨c, hc, 0, by simp, hcz, by simp [LinearCode.hammingDist_eq_wt_sub]⟩
  -- Contradiction with `wt c < minDist`
  exact (not_lt_of_ge hmin hwt).elim

/-- RS helper: same as `zero_of_wt_lt_minDist` specialized to Reed–Solomon codes. -/
lemma rs_zero_of_wt_lt_minDist
  {α : ι ↪ F} {deg : ℕ} {c : ι → F}
  (hc : c ∈ (ReedSolomon.code α deg : Set (ι → F)))
  (hwt : Code.wt c < Code.minDist (ReedSolomon.code α deg : Set (ι → F))) :
  c = 0 :=
  zero_of_wt_lt_minDist (L := ReedSolomon.code α deg) hc hwt

end ProximityToRS
