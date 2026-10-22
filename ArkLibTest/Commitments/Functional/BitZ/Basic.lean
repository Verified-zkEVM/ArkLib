/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/

import ArkLib.Commitments.Functional.BitZ.ExponentLift
import ArkLib.Data.Matrix.DotProduct
import ArkLib.Data.MvPolynomial.PrimeFingerprint
import ArkLib.Data.Nat.BitSum

/-!
# BitZ leaf lemmas: instances and axiom boundaries

Concrete instances showing the hypotheses of the BitZ lemmas are satisfiable and that the
conclusions are not vacuous: a generator of `(ZMod 7)ˣ`, a counterexample to the overflow
hypothesis, a ring that is not a field, and a prime-divisor count where the bound is attained.
-/

open BitZ MvPolynomial Matrix Finset

/-! ### Exponent lift in `ZMod 7`, where `3` generates `(ZMod 7)ˣ` (order `6`) -/

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The unit `3 ∈ (ZMod 7)ˣ`. -/
private def g7 : (ZMod 7)ˣ := ⟨3, 5, by decide, by decide⟩

/-- `3` generates `(ZMod 7)ˣ`. -/
private theorem g7_generates : ∀ x : (ZMod 7)ˣ, x ∈ Subgroup.zpowers g7 := by
  intro x
  obtain ⟨n, hn⟩ := (by decide +kernel : ∀ x : (ZMod 7)ˣ, ∃ n : Fin 6, g7 ^ (n : ℕ) = x) x
  exact ⟨n, by simpa using hn⟩

private def γ₁ (i : Fin 2) : ℕ := i.val + 1
private def b₁ (_ : Fin 2) : ℕ := 1

/-- The lift is an iff on the nose, for `γ = (1, 2)` and `b = (1, 1)`:
`3 · 9 = 3 ^ 3` in `ZMod 7` exactly when `⟨γ, b⟩ = 3`. -/
example : ∏ i : Fin 2, (((Units.val g7 : ZMod 7) ^ γ₁ i - 1) * (b₁ i : ZMod 7) + 1) =
      (Units.val g7 : ZMod 7) ^ 3 ↔ ∑ i : Fin 2, γ₁ i * b₁ i = 3 := by
  have h1 : ∀ i : Fin 2, γ₁ i ≤ 2 := fun i => by unfold γ₁; omega
  have h2 : ∀ i : Fin 2, b₁ i ≤ 1 := fun _ => le_rfl
  have h3 : 3 ≤ Fintype.card (Fin 2) * 2 := by simp
  have h4 : Fintype.card (Fin 2) * 2 < Fintype.card (ZMod 7) - 1 := by simp [ZMod.card]
  exact prod_bitFactor_eq_pow_iff (qMax := 2) (μ := 3) g7_generates γ₁ b₁ h1 h2 h3 h4

/-- The overflow hypothesis cannot be dropped: with `γ = (3, 3)`, `b = (1, 1)` and `μ = 0`
(so `|ι| · qMax = 6 = orderOf 3`), the grand product is `3 ^ 6 = 1 = 3 ^ 0` but `⟨γ, b⟩ = 6`. -/
example : ∏ i : Fin 2, (((3 : ZMod 7) ^ (fun _ => 3 : Fin 2 → ℕ) i - 1) *
      ((fun _ => 1 : Fin 2 → ℕ) i : ZMod 7) + 1) = (3 : ZMod 7) ^ 0 ∧
    ∑ i : Fin 2, (fun _ => 3 : Fin 2 → ℕ) i * (fun _ => 1 : Fin 2 → ℕ) i ≠ 0 := by
  decide

/-- The general iff needs no field: `2 ∈ ZMod 15` has order `4`, and with `γ = (1, 1)`, `b = (1, 1)`
the product `2 · 2` is `2 ^ 2` exactly when `⟨γ, b⟩ = 2`. -/
example : ∏ i : Fin 2, (((2 : ZMod 15) ^ (fun _ => 1 : Fin 2 → ℕ) i - 1) *
      ((fun _ => 1 : Fin 2 → ℕ) i : ZMod 15) + 1) = (2 : ZMod 15) ^ 2 ↔
    ∑ i : Fin 2, (fun _ => 1 : Fin 2 → ℕ) i * (fun _ => 1 : Fin 2 → ℕ) i = 2 := by
  have hord : orderOf (2 : ZMod 15) = 4 :=
    (orderOf_eq_iff (by norm_num)).2 ⟨by decide, by decide⟩
  exact prod_bitFactor_eq_pow_iff_of_lt_orderOf (x := (2 : ZMod 15)) (qMax := 1) (μ := 2)
    (fun _ : Fin 2 => 1) (fun _ => 1) (fun _ => le_rfl) (fun _ => le_rfl) (by simp)
    (by simp [hord])

/-! ### Generic lemmas -/

/-- Three bits encode a number below `2 ^ 3`. -/
example : ∑ k : Fin 3, 2 ^ (k : ℕ) * (![1, 0, 1] : Fin 3 → ℕ) k < 2 ^ 3 :=
  Nat.sum_pow_two_mul_lt _ (by decide)

/-- The product vector `(1, 2) ⊗ (3, 4)` paired with the entries `1, 2, 3, 4`. -/
example : ∑ p : Fin 2 × Fin 2, (![1, 2] : Fin 2 → ℤ) p.1 * (![3, 4] : Fin 2 → ℤ) p.2 *
      (![![1, 2], ![3, 4]] : Fin 2 → Fin 2 → ℤ) p.1 p.2 =
    ∑ j, ((![1, 2] : Fin 2 → ℤ) ⬝ᵥ fun i => (![![1, 2], ![3, 4]] : Fin 2 → Fin 2 → ℤ) i j) *
      (![3, 4] : Fin 2 → ℤ) j :=
  Matrix.sum_prod_mul_mul_eq_sum_dotProduct _ _
    fun p => (![![1, 2], ![3, 4]] : Fin 2 → Fin 2 → ℤ) p.1 p.2

/-! ### Fingerprinting -/

/-- The bound `⌊log₂ 6⌋ = 2` is attained: of the primes `2, 3, 5`, exactly `2` and `3` divide the
constant polynomial `6`. -/
example : #{q ∈ ({2, 3, 5} : Finset ℕ) |
    map (Int.castRingHom (ZMod q)) (C 6 : MvPolynomial (Fin 1) ℤ) = 0} = 2 ∧
      Nat.log 2 6 = 2 := by
  refine ⟨?_, by decide⟩
  rw [Finset.card_eq_two]
  refine ⟨2, 3, by decide, ?_⟩
  ext q
  simp only [mem_filter, mem_insert, mem_singleton, map_C, C_eq_zero]
  constructor
  · rintro ⟨rfl | rfl | rfl, hq⟩
    · simp
    · simp
    · exact absurd hq (by decide)
  · rintro (rfl | rfl) <;> exact ⟨by simp, by decide⟩

/-- The averaged bound applied to `6 ∈ ℤ` (`d = 0`, `M = 6`) and the primes `{2, 3, 5}`. -/
example : (∑ q ∈ ({2, 3, 5} : Finset ℕ),
      (zeroCountMod (C 6 : MvPolynomial (Fin 1) ℤ) q : ℝ) / (q : ℝ) ^ 1) /
        #({2, 3, 5} : Finset ℕ) ≤
    (Nat.log 2 6 : ℝ) / #({2, 3, 5} : Finset ℕ) + ((0 : ℕ) : ℝ) / (2 : ℕ) :=
  avg_zeroCountMod_div_le (C_ne_zero.2 (by norm_num)) (totalDegree_C _).le
    (fun s => by by_cases hs : s = 0 <;> simp [hs])
    (by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl <;> decide)
    le_rfl
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega)

/--
info: 'BitZ.prod_bitFactor_eq_pow_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.prod_bitFactor_eq_pow_iff

/--
info: 'BitZ.prod_bitFactor_eq_pow_iff_of_lt_orderOf' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.prod_bitFactor_eq_pow_iff_of_lt_orderOf

/--
info: 'Nat.sum_pow_two_mul_lt' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Nat.sum_pow_two_mul_lt

/--
info: 'Matrix.sum_prod_mul_mul_eq_sum_dotProduct' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.sum_prod_mul_mul_eq_sum_dotProduct

/--
info: 'MvPolynomial.avg_zeroCountMod_div_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.avg_zeroCountMod_div_le

/--
info: 'MvPolynomial.avg_zeroCountMod_div_le_logb' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.avg_zeroCountMod_div_le_logb
