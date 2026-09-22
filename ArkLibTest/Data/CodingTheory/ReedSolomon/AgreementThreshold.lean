/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.AgreementThreshold
import Mathlib.Tactic.NormNum

/-!
# Agreement-threshold clients

These clients compute a threshold and a radius, state the distance-agreement equivalence over
`Fin n`, and check that both hypotheses `0 ≤ δ` and `0 < n` are needed.
-/

open ReedSolomon

namespace AgreementThresholdTest

-- Block length `10`, message length `3`, gap `1 / 4`: the threshold is `3 + ⌈5 / 2⌉ = 6`.
example : agreementThreshold (1 / 4) 10 3 = 6 := by
  have : ⌈(1 / 4 : ℝ) * (10 : ℕ)⌉₊ = 3 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  simp only [agreementThreshold, this]

-- The same parameters give the radius `1 - 3 / 10 - 1 / 4 = 9 / 20`.
example : capacityRadius (1 / 4) 10 3 = 9 / 20 := by
  norm_num [capacityRadius]

-- The equivalence with block length `Fin n`.
example {F : Type} [DecidableEq F] {delta : ℝ} (hdelta : 0 ≤ delta) {n k : ℕ} (hn : 0 < n)
    (codeword received : Fin n → F) :
    (Code.relHammingDist received codeword : ℝ) ≤ capacityRadius delta n k ↔
      agreementThreshold delta n k ≤ Code.agree codeword received := by
  simpa using relHammingDist_le_capacityRadius_iff_agreementThreshold_le hdelta
    (messageDim := k) (by simpa using hn) codeword received

-- `0 ≤ δ` is needed in the real form: for `δ = -1`, `n = 1`, `k = 1` the threshold is `1`, but
-- `k + δ n = 0 ≤ 0`.
example : ¬ (agreementThreshold (-1) 1 1 ≤ 0 ↔ ((1 : ℕ) : ℝ) + (-1) * ((1 : ℕ) : ℝ) ≤ 0) := by
  simp [agreementThreshold]

-- `0 ≤ δ` is needed in the distance form: a codeword that disagrees with the word in its one
-- coordinate is within radius `1`, yet has no agreement.
example : ¬ ((Code.relHammingDist ![true] ![false] : ℝ) ≤
      capacityRadius (-1) (Fintype.card (Fin 1)) 1 ↔
    agreementThreshold (-1) (Fintype.card (Fin 1)) 1 ≤ Code.agree ![false] ![true]) := by
  have hagree : Code.agree ![false] ![true] = 0 := by decide
  have hdist : (Code.relHammingDist ![true] ![false] : ℝ) ≤ 1 := by
    exact_mod_cast Code.relHammingDist_le_one
  simp [capacityRadius, agreementThreshold, hagree, hdist]

-- `0 < n` is needed: for `n = 0`, `k = 0` and `δ = 2` the radius is `-1`, which the distance `0`
-- exceeds, while the threshold is `0`.
example : ¬ ∀ c r : Fin 0 → Bool, ((Code.relHammingDist r c : ℝ) ≤
      capacityRadius 2 (Fintype.card (Fin 0)) 0 ↔
    agreementThreshold 2 (Fintype.card (Fin 0)) 0 ≤ Code.agree c r) := by
  intro h
  have := (h Fin.elim0 Fin.elim0).mpr (by simp [agreementThreshold])
  norm_num [capacityRadius] at this
  have h0 : (0 : ℝ) ≤ (Code.relHammingDist (Fin.elim0 : Fin 0 → Bool) Fin.elim0 : ℝ) := by
    positivity
  linarith

end AgreementThresholdTest
