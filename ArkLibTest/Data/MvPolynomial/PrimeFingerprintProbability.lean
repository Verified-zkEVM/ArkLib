/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/

import ArkLib.Data.MvPolynomial.PrimeFingerprintProbability

/-!
# The fingerprinting probability: instances and axiom boundaries

The two-stage sampler (a prime `q` uniform in `P`, then a point uniform in `𝔽_qᵐ`) is not a uniform
draw from all pairs `(q, α)` when the fibres `𝔽_qᵐ` have different sizes. For `P = {2, 3}`, one
variable and the constant polynomial `h = 2`, the fibres have `2` and `3` points and `h mod q`
vanishes everywhere for `q = 2` and nowhere for `q = 3`. The two-stage probability is therefore
`(1 + 0) / 2 = 1/2`, whereas a uniform draw from the `5` pairs would give `2/5`.
-/

open Finset MvPolynomial
open scoped BigOperators ProbabilityTheory

private theorem primes_two_three : ∀ q ∈ ({2, 3} : Finset ℕ), q.Prime := by
  intro q hq
  simp only [mem_insert, mem_singleton] at hq
  rcases hq with rfl | rfl <;> decide

private instance : Nonempty ↥({2, 3} : Finset ℕ) := ⟨⟨2, by simp⟩⟩

/-- The two-stage probability is `1/2` for `P = {2, 3}` and `h = 2`. -/
example : Pr{let q ← $ᵗ ↥({2, 3} : Finset ℕ); let α ← modPointSample primes_two_three q}[
    eval α (MvPolynomial.map (Int.castRingHom (ZMod q.val)) (C 2 : MvPolynomial (Fin 1) ℤ)) = 0] =
      ENNReal.ofReal (1 / 2 : ℝ) := by
  classical
  rw [prEvent_fingerprint_eq_average]
  congr 1
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h3 : (2 : ZMod 3) ≠ 0 := by decide
  norm_num [Finset.expect_eq_sum_div_card, zeroCountMod, Nat.card_eq_fintype_card,
    Fintype.card_subtype, h2, h3]
  simp only [h2, ↓reduceIte]
  norm_num

/-- The bound applied to a nonzero constant `h = 2` of degree `0` and norm `2`, for `P = {2, 3}`. -/
example : Pr{let q ← $ᵗ ↥({2, 3} : Finset ℕ); let α ← modPointSample primes_two_three q}[
    eval α (MvPolynomial.map (Int.castRingHom (ZMod q.val)) (C 2 : MvPolynomial (Fin 1) ℤ)) = 0] ≤
      ENNReal.ofReal ((Nat.log 2 2 : ℝ) / ({2, 3} : Finset ℕ).card + ((0 : ℕ) : ℝ) / 2) :=
  prEvent_fingerprint_le (d := 0) (M := 2) (qmin := 2) (by rw [Ne, C_eq_zero]; norm_num)
    (totalDegree_C _).le
    (fun s => by rw [coeff_C]; split_ifs <;> simp) primes_two_three (by norm_num)
    (fun q hq => by simp only [mem_insert, mem_singleton] at hq; omega)

/--
info: 'MvPolynomial.prEvent_fingerprint_eq_average' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.prEvent_fingerprint_eq_average

/--
info: 'MvPolynomial.prEvent_fingerprint_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.prEvent_fingerprint_le
