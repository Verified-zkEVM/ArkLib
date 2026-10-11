/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/

import ArkLib.Commitments.Functional.BitZ.Round1
import ArkLib.Commitments.Functional.BitZ.Round2

/-!
# BitZ Rounds 1 and 2: instances and axiom boundaries

Concrete instances showing that the hypotheses of the Round 1 and Round 2 soundness lemmas are
satisfiable and that the conclusions are not vacuous.
-/

open BitZ MvPolynomial Finset

/-! ### Round 2 in `ZMod 7`, where `3` generates `(ZMod 7)ˣ` (order `6`) -/

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The unit `3 ∈ (ZMod 7)ˣ`. -/
private def g7 : (ZMod 7)ˣ := ⟨3, 5, by decide, by decide⟩

/-- `3` generates `(ZMod 7)ˣ`. -/
private theorem g7_generates : ∀ x : (ZMod 7)ˣ, x ∈ Subgroup.zpowers g7 := by
  intro x
  obtain ⟨n, hn⟩ := (by decide +kernel : ∀ x : (ZMod 7)ˣ, ∃ n : Fin 6, g7 ^ (n : ℕ) = x) x
  exact ⟨n, by simpa using hn⟩

/-- `q = 3`, `ℓ₁ = 2`, `ℓ₂ = 1`, `γ = (1, 2)`, all bits `1`, `µ₁ = 3`. The overflow hypothesis
`ℓ₁ · (q - 1) = 4 < 6 = |𝔽₇| - 1` holds, and the verifier's tensor claim over `𝔽₃` is derived:
`(1, 2) ⊗ (2) · (1, 1) = 1·2 + 2·2 = 0` in `ZMod 3`. -/
example : ∑ p : Fin 2 × Fin 1, ((fun i : Fin 2 => ((i.val + 1 : ℕ) : ZMod 3)) p.1) *
      ((fun _ : Fin 1 => (2 : ZMod 3)) p.2) * (((fun _ => 1 : Fin 2 × Fin 1 → ℕ) p : ℕ) : ZMod 3)
        = 0 :=
  inner_tensor_eq_of_prod_bitFactor_eq_pow (K := ZMod 3) (g := g7) (q := 3) g7_generates
    (fun i : Fin 2 => i.val + 1) (fun i => by omega) (fun _ => 1) (fun _ => le_rfl)
    (fun _ : Fin 1 => 3) (fun _ => by simp) (by simp [ZMod.card])
    (fun _ => by decide +kernel) _ (fun _ : Fin 1 => (2 : ZMod 3)) (fun _ => rfl) 0 (by decide)

/-- The overflow hypothesis cannot be dropped: `3 ^ 6 = 3 ^ 0` in `ZMod 7`, so the exponents `0`
and `6 = |𝔽₇| - 1` are indistinguishable. -/
example : (3 : ZMod 7) ^ 0 = (3 : ZMod 7) ^ 6 ∧ (0 : ℕ) ≠ 6 := by decide

/-! ### Monomial count and the product bound -/

example : #(monomialsLE 2 3) = 10 := by
  rw [card_monomialsLE]
  decide

/-- The coefficient of `X²` in `X · X` is bounded by `T · A · B = C(1 + 1, 1) · 1 · 1 = 2`. -/
example : ((X 0 * X 0 : MvPolynomial (Fin 1) ℤ).coeff (Finsupp.single 0 2)).natAbs ≤
    (1 + 1).choose 1 * (1 * 1) := by
  have hX : ∀ s, ((X 0 : MvPolynomial (Fin 1) ℤ).coeff s).natAbs ≤ 1 := by
    intro s
    rw [coeff_X]
    split_ifs <;> simp
  exact natAbs_coeff_mul_le (D := 1) (A := 1) (B := 1) (totalDegree_X _).le hX hX _

/-! ### Round 1 over `ℤ` with no generators (`k = 0`, `π_canon = eval`) -/

/-- A cheating prover in Round 1: `v₁ = v₂ = (1)`, `f = (1)`, so `⟨v₁ ⊗ v₂, f⟩ = 1`, but the claim
is `µ = 0` and the prover sends `µ' = 0`, which passes `π_canon(µ') = µ`. Then `h = 1 ≠ 0`, and the
reduced claim holds with probability `≤ log₃ 2 / 1 + 0 / 3 = 0`. -/
example : (∑ q ∈ ({3} : Finset ℕ), (Nat.card {α : Fin 0 → ZMod q //
        ∑ p : Fin 1 × Fin 1, reduceAt q α (C (1 : ℤ)) * reduceAt q α (C (1 : ℤ)) *
          (((fun _ => 1 : Fin 1 × Fin 1 → ℕ) p : ℕ) : ZMod q) = reduceAt q α 0} : ℝ) /
          (q : ℝ) ^ 0) / ({3} : Finset ℕ).card ≤
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
    (P := {3}) (fun q hq => by rw [mem_singleton.1 hq]; decide) (by simp) (qmin := 3)
    (by norm_num) (by simp)

/-! ### Axiom boundaries -/

/--
info: 'BitZ.inner_tensor_eq_of_prod_bitFactor_eq_pow' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.inner_tensor_eq_of_prod_bitFactor_eq_pow

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
info: 'MvPolynomial.card_monomialsLE' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.card_monomialsLE
