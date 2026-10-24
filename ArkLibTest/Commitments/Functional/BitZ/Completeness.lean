/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/

import ArkLib.Commitments.Functional.BitZ.Completeness
import ArkLibTest.Commitments.Functional.BitZ.RoundsSoundness

/-!
# BitZ honest messages: instances and axiom boundaries

The honest second message is executable and is run through the decidable verifier check on
explicit constant polynomials, with a tampered message and a non-bit matrix as controls. The
theorems are applied to the same data, and the identification of the honest first message with the
original claim is instantiated over `ℤ` and over the semiring `S = ℕ`. The explicit constant
polynomial `constPoly` comes from `RoundsSoundness`, and the generator `g7` of `(ZMod 7)ˣ` from
`Basic`.
-/

open BitZ MvPolynomial Matrix Finset
open scoped BigOperators

/-! ### Running the honest second message

Lifts `a = (1, 2)` and `b = (2)`, bits `f = (1, 1)`, `q = 3` and no variables: the honest message is
`μ₁ = 1 + 2 = 3`, within the range `ℓ₁ · (q - 1) = 4`, and the honest first message is
`1 · 2 + 2 · 2 = 6 ≡ 0 (mod 3)`. -/

private def lifts : Fin 2 → MvPolynomial (Fin 0) ℤ :=
  ![constPoly 1 (by norm_num), constPoly 2 (by norm_num)]

-- The honest message `μ₁ = ∑ᵢ γᵢ · fᵢ₁ = 1 + 2`.
/-- info: [3] -/
#guard_msgs in
#eval List.ofFn (honestRound2Message (f := fun _ : Fin 2 × Fin 1 => 1) 3 (fun i : Fin 0 => i.elim0)
  lifts)

private def pass (f : Fin 2 × Fin 1 → ℕ) (μ' : MvPolynomial (Fin 0) ℤ) (μ : Fin 1 → ℕ) : Bool :=
  decide (Round2Check g7 lifts (fun _ : Fin 1 => constPoly 2 (by norm_num)) f μ' 3
    (fun i => i.elim0) μ)

-- The honest messages pass; a tampered second message `2` fails the grand product; for the
-- non-bit matrix `f = 2` the honest messages `μ₁ = 6` and `μ' = 12` fail the range check.
/-- info: [true, false, false] -/
#guard_msgs in
#eval
  [pass (fun _ => 1) (constPoly 6 (by norm_num))
      (honestRound2Message (f := fun _ : Fin 2 × Fin 1 => 1) 3 (fun i : Fin 0 => i.elim0) lifts),
    pass (fun _ => 1) (constPoly 6 (by norm_num)) (fun _ => 2),
    pass (fun _ => 2) (constPoly 12 (by norm_num))
      (honestRound2Message (f := fun _ : Fin 2 × Fin 1 => 2) 3 (fun i : Fin 0 => i.elim0) lifts)]

/-! ### The theorems on the same shape of data -/

/-- The honest messages pass for any unit, here `g7`, without an overflow hypothesis (compare the
necessity example in `RoundsSoundness`, where the same shape of data needs the overflow bound to
conclude the reduced claim). -/
example : Round2Check g7 (fun _ : Fin 2 => (C 1 : MvPolynomial (Fin 0) ℤ))
    (fun _ : Fin 1 => (C 2 : MvPolynomial (Fin 0) ℤ)) (fun _ => 1)
    (honestMessage (fun _ : Fin 2 => (C 1 : MvPolynomial (Fin 0) ℤ))
      (fun _ : Fin 1 => (C 2 : MvPolynomial (Fin 0) ℤ)) (fun _ => 1)) 3 (fun i => i.elim0)
    (honestRound2Message 3 (fun i : Fin 0 => i.elim0) (fun _ : Fin 2 => (C 1 : MvPolynomial _ ℤ))
      (fun _ : Fin 2 × Fin 1 => 1)) :=
  round2Check_honestRound2Message g7 _ _ (fun _ => le_rfl) 3 _

/-- The honest message `⟨X₀ ⊗ 1, (1)⟩` has degree at most `2` and coefficients bounded by
`C(1 + 1, 1) · 1 · 1 = 2`; the norm bound is the one of `Round1`, now about the named message. -/
example :
    (honestMessage (fun _ : Fin 1 => (X 0 : MvPolynomial (Fin 1) ℤ))
      (fun _ : Fin 1 => (C 1 : MvPolynomial (Fin 1) ℤ)) (fun _ => 1)).totalDegree ≤ 2 * 1 :=
  totalDegree_honestMessage_le (fun _ => (totalDegree_X _).le)
    (fun _ => (totalDegree_C _).le.trans (Nat.zero_le _))

example (s : Fin 1 →₀ ℕ) :
    ((honestMessage (fun _ : Fin 1 => (X 0 : MvPolynomial (Fin 1) ℤ))
      (fun _ : Fin 1 => (C 1 : MvPolynomial (Fin 1) ℤ)) (fun _ => 1)).coeff s).natAbs ≤
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

/-! ### The honest first message of a bitified claim -/

/-- With `S = R = ℤ`, `γ = (1)`, `B = 1`, `v₁ = v₂ = (1)` and the bit `1`, the canonical image of
the honest message is the original claim `⟨1, L · 1⟩ = 1`. -/
example : eval (Fin.elim0 : Fin 0 → ℤ)
      (honestMessage (fun _ : Fin 1 => (C 1 : MvPolynomial (Fin 0) ℤ))
        (fun _ : Fin 1 × Fin 1 × Unit => (C 1 : MvPolynomial (Fin 0) ℤ))
        (fun _ : Fin 1 × Fin 1 × Fin 1 × Unit => 1)) = 1 := by
  have h := map_honestMessage_bitified (eval (Fin.elim0 : Fin 0 → ℤ)) (RingHom.id ℤ)
    (fun _ : Unit => (1 : ℤ)) 1 (a := fun _ : Fin 1 => (C 1 : MvPolynomial (Fin 0) ℤ))
    (b := fun _ : Fin 1 × Fin 1 × Unit => (C 1 : MvPolynomial (Fin 0) ℤ)) (v₁ := fun _ => 1)
    (v₂ := fun _ => 1) (fun _ => by simp) (fun j => by simp [bitWeights])
    (fun _ : (Fin 1 × Fin 1) × Fin 1 × Unit => 1)
  exact h.trans (by decide +kernel)

/-- The ring `S` need not have subtraction: with `S = ℕ`, `R = ℤ`, `ψ` the cast, `γ = (1)`,
`B = 2`, `v₁ = (1)`, `v₂ = (3)` and the bits `(1, 1)`, the original claim is `3 · (1 + 2) = 9`, and
the honest message for the lifts `a = (1)`, `b = (3, 6)` of `v₁` and of the bitified weights
evaluates to it. -/
example : eval (Fin.elim0 : Fin 0 → ℤ)
      (honestMessage (fun _ : Fin 1 => (C 1 : MvPolynomial (Fin 0) ℤ))
        (fun x : Fin 1 × Fin 2 × Unit =>
          (C (3 * 2 ^ (x.2.1 : ℕ)) : MvPolynomial (Fin 0) ℤ))
        (fun _ : Fin 1 × Fin 1 × Fin 2 × Unit => 1)) = 9 := by
  have h := map_honestMessage_bitified (eval (Fin.elim0 : Fin 0 → ℤ)) (Nat.castRingHom ℤ)
    (fun _ : Unit => (1 : ℕ)) 2 (a := fun _ : Fin 1 => (C 1 : MvPolynomial (Fin 0) ℤ))
    (b := fun x : Fin 1 × Fin 2 × Unit =>
      (C (3 * 2 ^ (x.2.1 : ℕ)) : MvPolynomial (Fin 0) ℤ))
    (v₁ := fun _ => 1) (v₂ := fun _ => 3) (fun _ => by simp) (fun j => by simp [bitWeights])
    (fun _ : (Fin 1 × Fin 1) × Fin 2 × Unit => 1)
  exact h.trans (by decide +kernel)

/-! ### Axiom boundaries -/

/--
info: 'BitZ.round2Check_honestRound2Message' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.round2Check_honestRound2Message

/--
info: 'BitZ.map_honestMessage_bitified' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.map_honestMessage_bitified

/--
info: 'BitZ.totalDegree_honestMessage_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.totalDegree_honestMessage_le
