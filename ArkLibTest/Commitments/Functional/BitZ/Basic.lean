/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/

import ArkLib.Commitments.Functional.BitZ.Bitification
import ArkLib.Commitments.Functional.BitZ.ExponentLift
import ArkLib.Data.MvPolynomial.PrimeFingerprint

/-!
# BitZ leaf lemmas: instances and axiom boundaries

Concrete instances showing the hypotheses of the BitZ lemmas are satisfiable and that the
conclusions are not vacuous: a generator of `(ZMod 7)ˣ`, the integer range check, and a
prime-divisor count.
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

/-- The overflow hypothesis cannot be dropped: exponents `0` and `6 = orderOf 3` collide. -/
example : (3 : ZMod 7) ^ 0 = (3 : ZMod 7) ^ 6 ∧ (0 : ℕ) ≠ 6 := by decide

/-! ### Bitification over `ℤ → ZMod 5` -/

/-- The range check is real: `5 ∈ S^{<D}_{≤3}` but `8 ∉ S^{<D}_{≤3}` with a single monomial `1`. -/
example : (5 : ℤ) ∈ boundedSpan (fun _ : Unit => (1 : ℤ)) 3 :=
  ⟨fun _ => 5, by decide, by simp⟩

example : (8 : ℤ) ∉ boundedSpan (fun _ : Unit => (1 : ℤ)) 3 := by
  rintro ⟨h, hlt, hs⟩
  have := hlt PUnit.unit
  norm_num at this
  simp at hs
  omega

/-- The equivalence of witnesses is instantiated: integer witnesses of three bits against
`ψ : ℤ → ZMod 5`. -/
example (v : Fin 2 → ZMod 5) (μ : ZMod 5) :
    (∃ f : Fin 2 → ℤ, (∀ i, f i ∈ boundedSpan (fun _ : Unit => (1 : ℤ)) 3) ∧
        v ⬝ᵥ (fun i => Int.castRingHom (ZMod 5) (f i)) = μ) ↔
      ∃ g : Fin 2 × Fin 3 × Unit → ℕ, (∀ x, g x ≤ 1) ∧
        (fun p => (g p : ZMod 5)) ⬝ᵥ
          (((bitMatrix (fun _ : Unit => (1 : ℤ)) 3).map (Int.castRingHom (ZMod 5)))ᵀ.mulVec v) =
          μ :=
  exists_witness_iff_exists_bits _ _ _ _ _

/-! ### Fingerprinting -/

/-- Primes `2, 3, 5` all `≥ 2`; the constant polynomial `6` is killed by exactly `2` and `3`, and
the bound `⌊log₂ 6⌋ = 2` is attained. -/
example : #{q ∈ ({2, 3, 5} : Finset ℕ) |
    map (Int.castRingHom (ZMod q)) (C 6 : MvPolynomial (Fin 1) ℤ) = 0} ≤ Nat.log 2 6 :=
  card_filter_map_eq_zero_le_log (C_ne_zero.2 (by norm_num)) (M := 6) (qmin := 2)
    (fun s => by
      by_cases hs : s = 0 <;> simp [hs])
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
info: 'BitZ.exists_witness_iff_exists_bits' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.exists_witness_iff_exists_bits

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
