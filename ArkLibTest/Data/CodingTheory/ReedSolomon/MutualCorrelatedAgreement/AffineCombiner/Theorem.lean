/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Theorem

/-! # Acceptance cases for the affine MCA bound -/

open ReedSolomon

/-- The bound applies at `d = 16`, `n = 100`, `η = 1/2`, where `√ρ = 2/5` and `A = 90`. -/
example {F : Type*} [Field F] [DecidableEq F] [Fintype F] (domain : Fin 100 ↪ F) :
    affineMCAError domain 16 90 1 ≤
      8 / Fintype.card F + 2 ^ 22 * 5 ^ 10 / (Fintype.card F : ℝ) ^ 2 := by
  have hsqrt : √((16 : ℕ) / ((Fintype.card (Fin 100) : ℕ) : ℝ)) = 2 / 5 := by
    rw [Fintype.card_fin, Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
    norm_num
  have h := affineMCAError_le domain (d := 16) (η := 1 / 2) (by norm_num) (by simp)
    (by norm_num) (by rw [hsqrt]; norm_num) (by simp; norm_num)
  rw [hsqrt, Fintype.card_fin] at h
  convert h using 2
  · norm_num
  · field_simp
    norm_num
  · ring_nf
