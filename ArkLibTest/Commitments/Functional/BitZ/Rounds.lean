/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/

import ArkLib.Commitments.Functional.BitZ.Round1
import ArkLib.Commitments.Functional.BitZ.Round2
import ArkLibTest.Commitments.Functional.BitZ.Basic

/-!
# BitZ Rounds 1 and 2: instances and axiom boundaries

Concrete instances showing that the hypotheses of the Round 1 and Round 2 soundness lemmas are
satisfiable and that the conclusions are not vacuous. The generator `g7` of `(ZMod 7)ˣ` comes from
`ArkLibTest.Commitments.Functional.BitZ.Basic`.
-/

open BitZ MvPolynomial Finset
open scoped BigOperators ProbabilityTheory

/-! ### Round 2 in `ZMod 7`, where `3` generates `(ZMod 7)ˣ` (order `6`) -/

/-- `q = 3`, `ℓ₁ = 2`, `ℓ₂ = 1`, `γ = (1, 2)`, all bits `1`, `µ₁ = 3`. The overflow hypothesis
`ℓ₁ · (q - 1) = 4 < 6 = |𝔽₇| - 1` holds, and the verifier's tensor claim over `𝔽₃` is derived:
`(1, 2) ⊗ (2) · (1, 1) = 1·2 + 2·2 = 0` in `ZMod 3`. -/
example : ∑ p : Fin 2 × Fin 1, ((fun i : Fin 2 => ((i.val + 1 : ℕ) : ZMod 3)) p.1) *
      ((fun _ : Fin 1 => (2 : ZMod 3)) p.2) * (((fun _ => 1 : Fin 2 × Fin 1 → ℕ) p : ℕ) : ZMod 3)
        = 0 :=
  sum_prod_mul_mul_eq_of_prod_bitFactor_eq_pow (K := ZMod 3) (g := g7) (q := 3) g7_generates
    (fun i : Fin 2 => i.val + 1) (fun i => by omega) (fun _ => 1) (fun _ => le_rfl)
    (fun _ : Fin 1 => 3) (fun _ => by simp) (by simp [ZMod.card])
    (fun _ => by decide +kernel) _ (fun _ : Fin 1 => (2 : ZMod 3)) (fun _ => rfl) 0 (by decide)

/-- The overflow hypothesis cannot be weakened to `≤`: at `ℓ₁ = 3`, `q = 3`, `γ = (2, 2, 2)`,
bits `(1, 1, 1)` and `µ = 0`, every other hypothesis holds and `ℓ₁ · (q - 1) = 6 = |𝔽₇| - 1`,
but `∑ᵢ γᵢ · fᵢ = 6 ≠ 0`, so the conclusion over `K = ℤ` fails. -/
example : ¬ ∀ (γ : Fin 3 → ℕ) (f : Fin 3 × Fin 1 → ℕ) (μ : Fin 1 → ℕ),
    (∀ i, γ i < 3) → (∀ p, f p ≤ 1) → (∀ j, μ j ≤ Fintype.card (Fin 3) * (3 - 1)) →
    Fintype.card (Fin 3) * (3 - 1) ≤ Fintype.card (ZMod 7) - 1 →
    (∀ j, ∏ i, (((g7 : ZMod 7) ^ γ i - 1) * (f (i, j) : ZMod 7) + 1) = (g7 : ZMod 7) ^ μ j) →
    ∑ p : Fin 3 × Fin 1, (γ p.1 : ℤ) * 1 * (f p : ℤ) = ∑ j, (μ j : ℤ) * 1 := by
  intro h
  have := h (fun _ => 2) (fun _ => 1) (fun _ => 0) (fun _ => by decide) (fun _ => le_rfl)
    (fun _ => by simp) (by simp [ZMod.card]) (fun _ => by decide)
  simp at this

/-! ### Monomial count and the product bound -/

example : #(Finsupp.degreeLEFinset (Fin 2) 3) = 10 := by
  rw [Finsupp.card_degreeLEFinset, Fintype.card_fin]
  decide

/-- The coefficient of `X²` in `X · X` is bounded by `T · A · B = C(1 + 1, 1) · 1 · 1 = 2`. -/
example : ((X 0 * X 0 : MvPolynomial (Fin 1) ℤ).coeff (Finsupp.single 0 2)).natAbs ≤
    (1 + 1).choose 1 * (1 * 1) := by
  have hX : ∀ s, ((X 0 : MvPolynomial (Fin 1) ℤ).coeff s).natAbs ≤ 1 := by
    intro s
    rw [coeff_X]
    split_ifs <;> simp
  simpa only [Fintype.card_fin] using
    natAbs_coeff_mul_le (D := 1) (A := 1) (B := 1) (totalDegree_X _).le hX hX
      (Finsupp.single 0 2)

/-! ### Round 1 over `ℤ` with no generators (`k = 0`, `π_canon = eval`) -/

/-- A cheating prover in Round 1: `v₁ = v₂ = (1)`, `f = (1)`, so `⟨v₁ ⊗ v₂, f⟩ = 1`, but the claim
is `µ = 0` and the prover sends `µ' = 0`, which passes `π_canon(µ') = µ`. Then `h = 1 ≠ 0`, and the
reduced claim holds with probability `≤ ⌊log₃ 2⌋ / 1 + 0 / 3 = 0`. -/
example : 𝔼 q ∈ ({3} : Finset ℕ), (Nat.card {α : Fin 0 → ZMod q //
        ∑ p : Fin 1 × Fin 1, reduceAt q α (C (1 : ℤ)) * reduceAt q α (C (1 : ℤ)) *
          (((fun _ => 1 : Fin 1 × Fin 1 → ℕ) p : ℕ) : ZMod q) = reduceAt q α 0} : ℝ) /
          (q : ℝ) ^ 0 ≤
      (Nat.log 3 (2 * (0 + 0).choose 0 * Fintype.card (Fin 1 × Fin 1) * 1 ^ 2) : ℝ) /
        ({3} : Finset ℕ).card + ((2 * 0 : ℕ) : ℝ) / 3 := by
  have hC : ∀ s : Fin 0 →₀ ℕ, ((C 1 : MvPolynomial (Fin 0) ℤ).coeff s).natAbs ≤ 1 := by
    intro s
    rw [coeff_C]
    split_ifs <;> simp
  refine avg_card_claim_le (R := ℤ) (eval Fin.elim0) (a := fun _ : Fin 1 => C 1)
    (b := fun _ : Fin 1 => C 1) (v₁ := fun _ => 1) (v₂ := fun _ => 1) (fun _ => by simp)
    (fun _ => by simp) (f := fun _ => 1) (fun _ => le_rfl) (μ := 0) (μ' := 0) (by simp)
    (by simp) (D := 0) (N := 1) (fun _ => by simp) (fun _ => by simp) (fun _ s => hC s)
    (fun _ s => hC s) (by simp) (fun s => by simp)
    (P := {3}) (fun q hq => by rw [mem_singleton.1 hq]; decide) (qmin := 3) (by norm_num)
    (by simp)

/-! ### The honest message and the challenge sampler of Round 1 -/

/-- The honest message `µ' = ⟨a ⊗ b, f⟩` with `a = X₀`, `b = 1` and `f = (1)` has coefficients
bounded by `T · ℓ · N² = C(1 + 1, 1) · 1 · 1 = 2`. -/
example (s : Fin 1 →₀ ℕ) :
    ((∑ p : Fin 1 × Fin 1, (fun _ : Fin 1 => X 0 : Fin 1 → MvPolynomial (Fin 1) ℤ) p.1 *
      (fun _ : Fin 1 => C 1 : Fin 1 → MvPolynomial (Fin 1) ℤ) p.2 *
        (((fun _ => 1 : Fin 1 × Fin 1 → ℕ) p : ℕ) : MvPolynomial (Fin 1) ℤ)).coeff s).natAbs ≤
      (1 + 1).choose 1 * Fintype.card (Fin 1 × Fin 1) * 1 ^ 2 := by
  have hX : ∀ s, ((X 0 : MvPolynomial (Fin 1) ℤ).coeff s).natAbs ≤ 1 := by
    intro s
    rw [coeff_X]
    split_ifs <;> simp
  have hC : ∀ s, ((C 1 : MvPolynomial (Fin 1) ℤ).coeff s).natAbs ≤ 1 := by
    intro s
    rw [coeff_C]
    split_ifs <;> simp
  exact natAbs_coeff_honestMessage_le (D := 1) (N := 1) (fun _ => le_rfl)
    (fun _ => (totalDegree_X _).le) (fun _ s => hX s) (fun _ s => hC s) s

private theorem primes_two_three : ∀ q ∈ ({2, 3} : Finset ℕ), q.Prime := by
  intro q hq
  simp only [mem_insert, mem_singleton] at hq
  rcases hq with rfl | rfl <;> decide

private instance : Nonempty ↥({2, 3} : Finset ℕ) := ⟨⟨2, by simp⟩⟩

/-- The challenge sampler of Round 1 with one variable and two primes: `π_canon` sends `X₀` to `1`,
so the claim `⟨1 ⊗ 1, 1⟩ = 1 = µ + 1` is false for `µ = 0`, and the cheating message `µ' = 0`
passes the check `π_canon(µ') = µ`. -/
example : Pr{let q ← $ᵗ ↥({2, 3} : Finset ℕ); let α ← modPointSample primes_two_three q}[
    ∑ p : Fin 1 × Fin 1, reduceAt q.val α (X 0 : MvPolynomial (Fin 1) ℤ) *
      reduceAt q.val α (C 1) * (((fun _ => 1 : Fin 1 × Fin 1 → ℕ) p : ℕ) : ZMod q.val) =
        reduceAt q.val α 0] ≤
      ENNReal.ofReal ((Nat.log 2 (2 * (1 + 1).choose 1 * Fintype.card (Fin 1 × Fin 1) * 1 ^ 2) :
        ℝ) / ({2, 3} : Finset ℕ).card + ((2 * 1 : ℕ) : ℝ) / 2) := by
  have hX : ∀ s, ((X 0 : MvPolynomial (Fin 1) ℤ).coeff s).natAbs ≤ 1 := by
    intro s
    rw [coeff_X]
    split_ifs <;> simp
  have hC : ∀ s, ((C 1 : MvPolynomial (Fin 1) ℤ).coeff s).natAbs ≤ 1 := by
    intro s
    rw [coeff_C]
    split_ifs <;> simp
  exact prEvent_claim_le (R := ℤ) (eval fun _ => 1) (a := fun _ : Fin 1 => X 0)
    (b := fun _ : Fin 1 => C 1) (v₁ := fun _ => 1) (v₂ := fun _ => 1) (fun _ => by simp)
    (fun _ => by simp) (f := fun _ => 1) (fun _ => le_rfl) (μ := 0) (μ' := 0) (by simp)
    (by simp) (D := 1) (N := 1) (fun _ => (totalDegree_X _).le)
    (fun _ => (totalDegree_C _).le.trans (Nat.zero_le _)) (fun _ s => hX s) (fun _ s => hC s)
    (by simp) (fun s => by simp) primes_two_three (qmin := 2) le_rfl
    (fun q hq => by simp only [mem_insert, mem_singleton] at hq; omega)

/-! ### Axiom boundaries -/

/--
info: 'BitZ.sum_prod_mul_mul_eq_of_prod_bitFactor_eq_pow' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.sum_prod_mul_mul_eq_of_prod_bitFactor_eq_pow

/--
info: 'BitZ.avg_card_claim_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.avg_card_claim_le

/--
info: 'BitZ.avg_card_claim_le_logb' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.avg_card_claim_le_logb

/--
info: 'MvPolynomial.natAbs_coeff_mul_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.natAbs_coeff_mul_le

/--
info: 'BitZ.natAbs_coeff_honestMessage_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.natAbs_coeff_honestMessage_le

/--
info: 'BitZ.prEvent_claim_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.prEvent_claim_le
