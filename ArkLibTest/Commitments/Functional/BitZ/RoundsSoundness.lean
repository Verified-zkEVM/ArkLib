/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/

import ArkLib.Commitments.Functional.BitZ.RoundsSoundness
import ArkLibTest.Commitments.Functional.BitZ.Basic
import ArkLibTest.Commitments.Functional.BitZ.Rounds

/-!
# BitZ Rounds 1 and 2 together: instances and axiom boundaries

The verifier's check of Round 2 is decidable and runs on explicit constant polynomials. The
overflow hypothesis `ℓ₁ · (q - 1) < |F| - 1` is necessary: with the same weights and message, the
check passes in `ZMod 7` (where the hypothesis fails) with a false reduced claim, and the reduced
claim follows in `ZMod 17` (where it holds). The probability bound is instantiated with the
nontrivial error `2 / 11`. The generator `g7` of `(ZMod 7)ˣ` is shared from `Basic` and the primes
`{11, 13}` from `Rounds`.
-/

open BitZ MvPolynomial Finset
open scoped BigOperators ProbabilityTheory

/-! ### A generator of `(ZMod 17)ˣ`, whose order `16` allows `ℓ₁ · (q - 1) = 12` -/

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The unit `3 ∈ (ZMod 17)ˣ`. -/
def g17 : (ZMod 17)ˣ := ⟨3, 6, by decide, by decide⟩

/-- `3` generates `(ZMod 17)ˣ`. -/
theorem g17_generates : ∀ x : (ZMod 17)ˣ, x ∈ Subgroup.zpowers g17 := by
  intro x
  obtain ⟨n, hn⟩ := (by decide +kernel : ∀ x : (ZMod 17)ˣ, ∃ n : Fin 16, g17 ^ (n : ℕ) = x) x
  exact ⟨n, by simpa using hn⟩

/-! ### The overflow hypothesis is necessary and sufficient here

Three weights `4`, one column of bits `1`, `q = 5` and no variables. The honest sum is
`⟨γ, f⟩ = 12 ≡ 2 (mod 5)`. -/

/-- In `ZMod 7`, where `ℓ₁ · (q - 1) = 12 ≥ 6 = |F| - 1`, the message `μ = 0` passes the checks of
Round 2 against `μ' = 0`, because `g ^ 12 = 1 = g ^ 0`, but the reduced claim `12 = 0` fails
in `𝔽₅`. -/
example : Round2Check g7 (fun _ : Fin 3 => (C 4 : MvPolynomial (Fin 0) ℤ))
      (fun _ : Fin 1 => (C 1 : MvPolynomial (Fin 0) ℤ)) (fun _ => 1) 0 5 (fun i => i.elim0)
      (fun _ => 0) ∧
    ¬ (∑ p : Fin 3 × Fin 1, reduceAt 5 (fun i : Fin 0 => i.elim0) (C 4 : MvPolynomial (Fin 0) ℤ) *
      reduceAt 5 (fun i : Fin 0 => i.elim0) (C 1 : MvPolynomial (Fin 0) ℤ) *
        (((fun _ => 1 : Fin 3 × Fin 1 → ℕ) p : ℕ) : ZMod 5) =
          reduceAt 5 (fun i : Fin 0 => i.elim0) (0 : MvPolynomial (Fin 0) ℤ)) ∧
    ¬ (Fintype.card (Fin 3) * (5 - 1) < Fintype.card (ZMod 7) - 1) := by
  simp only [Round2Check, Fintype.card_fin, Nat.add_one_sub_one, Nat.reduceMul, zero_le,
    implies_true, univ_unique, Fin.default_eq_zero, Fin.isValue, Nat.cast_zero, eq_intCast,
    reduceAt_apply, map_one, mul_one, sum_const_zero, map_zero, Int.cast_ofNat,
    MvPolynomial.map_ofNat, eval_ofNat, Nat.cast_one, sub_add_cancel, prod_const, card_univ,
    pow_zero, forall_const, true_and, sum_const, Fintype.card_prod, Fintype.card_unique,
    nsmul_eq_mul, Nat.cast_ofNat, ZMod.card, Nat.reduceLT, not_false_eq_true, and_true]
  decide +kernel

/-- In `ZMod 17`, where `ℓ₁ · (q - 1) = 12 < 16 = |F| - 1`, a message passing the checks of Round 2
for the honest `μ = 12` and `μ' = 12` gives the reduced claim `12 = 12` in `𝔽₅`. -/
example : ∑ p : Fin 3 × Fin 1, reduceAt 5 (fun i : Fin 0 => i.elim0)
      (C 4 : MvPolynomial (Fin 0) ℤ) * reduceAt 5 (fun i : Fin 0 => i.elim0)
        (C 1 : MvPolynomial (Fin 0) ℤ) * (((fun _ => 1 : Fin 3 × Fin 1 → ℕ) p : ℕ) : ZMod 5) =
      reduceAt 5 (fun i : Fin 0 => i.elim0) (C 12 : MvPolynomial (Fin 0) ℤ) := by
  have : NeZero 5 := ⟨by norm_num⟩
  refine sum_prod_mul_mul_eq_of_round2Accepts (F := ZMod 17) (g := g17) g17_generates
    (a := fun _ : Fin 3 => (C 4 : MvPolynomial (Fin 0) ℤ))
    (b := fun _ : Fin 1 => (C 1 : MvPolynomial (Fin 0) ℤ)) (f := fun _ => 1)
    (fun _ => le_rfl) (by simp [ZMod.card]) ⟨fun _ => 12, ?_⟩
  simp only [Round2Check, Fintype.card_fin, Nat.add_one_sub_one, Nat.reduceMul, Std.le_refl,
    implies_true, univ_unique, Fin.default_eq_zero, Fin.isValue, Nat.cast_ofNat, eq_intCast,
    reduceAt_apply, map_one, mul_one, sum_const, card_singleton, one_smul,
    Int.cast_ofNat, MvPolynomial.map_ofNat, eval_ofNat, Nat.cast_one, sub_add_cancel, prod_const,
    card_univ, forall_const, true_and]
  decide +kernel

/-! ### Running the verifier's check

A constant polynomial with an explicit coefficient representation avoids Mathlib's classical
polynomial constructors, so that `Round2Check` evaluates. -/

private def zeroPoly : MvPolynomial (Fin 0) ℤ := AddMonoidAlgebra.ofCoeff 0

private def constPoly (n : ℤ) (hn : n ≠ 0) : MvPolynomial (Fin 0) ℤ :=
  AddMonoidAlgebra.ofCoeff
    { support := {0}
      toFun := fun s => if s = 0 then n else 0
      mem_support_toFun := by intro s; by_cases h : s = 0 <;> simp [h, hn] }

/-- The data of the first example above. -/
private def check (μ' : MvPolynomial (Fin 0) ℤ) (μ : ℕ) : Bool :=
  decide (Round2Check g7 (fun _ : Fin 3 => constPoly 4 (by norm_num))
    (fun _ : Fin 1 => constPoly 1 (by norm_num)) (fun _ => 1) μ' 5 (fun i => i.elim0)
    (fun _ => μ))

-- `μ = 0` against `μ' = 0` passes; `μ = 1` fails the grand product `g ^ 12 = 1 ≠ g`; `μ = 13`
-- exceeds the range `ℓ₁ · (q - 1) = 12`; `μ = 0` against `μ' = 1` fails the weighted sum.
/-- info: [true, false, false, false] -/
#guard_msgs in
#eval [check zeroPoly 0, check zeroPoly 1, check zeroPoly 13, check (constPoly 1 (by norm_num)) 0]

/-! ### The probability bound with a nontrivial error -/

/-- The cheating prover of Round 1 also passes Round 2 with probability at most `2 / 11`: with
`a = X₀`, `b = 1`, `f = (1)`, `μ = 0` and `μ' = 0`, the claim `⟨1 ⊗ 1, 1⟩ = 1 ≠ 0` is false, and
`ℓ₁ · (q - 1) ≤ 12 < 16 = |𝔽₁₇| - 1` for the primes `{11, 13}`. -/
example : Pr{let q ← $ᵗ ↥({11, 13} : Finset ℕ); let α ← modPointSample primes_eleven_thirteen q}[
    Round2Accepts g17 (fun _ : Fin 1 => (X 0 : MvPolynomial (Fin 1) ℤ))
      (fun _ : Fin 1 => (C 1 : MvPolynomial (Fin 1) ℤ)) (fun _ : Fin 1 × Fin 1 => 1) 0 q.val α] ≤
      ENNReal.ofReal (2 / 11 : ℝ) := by
  have hX : ∀ s, ((X 0 : MvPolynomial (Fin 1) ℤ).coeff s).natAbs ≤ 1 := by
    intro s
    rw [coeff_X]
    split_ifs <;> simp
  have hC : ∀ s, ((C 1 : MvPolynomial (Fin 1) ℤ).coeff s).natAbs ≤ 1 := by
    intro s
    rw [coeff_C]
    split_ifs <;> simp
  have h := prEvent_round2Accepts_le (F := ZMod 17) (R := ℤ) (g := g17) g17_generates
    (eval fun _ => 1) (a := fun _ : Fin 1 => X 0) (b := fun _ : Fin 1 => C 1) (v₁ := fun _ => 1)
    (v₂ := fun _ => 1) (fun _ => by simp) (fun _ => by simp) (f := fun _ => 1) (fun _ => le_rfl)
    (μ := 0) (μ' := 0) (by simp) (by simp) (D := 1) (N := 1) (fun _ => (totalDegree_X _).le)
    (fun _ => (totalDegree_C _).le.trans (Nat.zero_le _)) (fun _ s => hX s) (fun _ s => hC s)
    (by simp) (fun s => by simp) primes_eleven_thirteen (qmin := 11) (by norm_num)
    (fun q hq => by simp only [mem_insert, mem_singleton] at hq; omega)
    (fun q hq => by
      simp only [mem_insert, mem_singleton] at hq
      rcases hq with rfl | rfl <;> simp [ZMod.card])
  have hlog : Nat.log 11 4 = 0 := by decide
  convert h using 1
  norm_num [hlog]

/-! ### Axiom boundaries -/

/--
info: 'BitZ.sum_prod_mul_mul_eq_of_round2Accepts' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.sum_prod_mul_mul_eq_of_round2Accepts

/--
info: 'BitZ.prEvent_round2Accepts_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.prEvent_round2Accepts_le

/--
info: 'MvPolynomial.prEvent_modPointSample_mono' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.prEvent_modPointSample_mono
