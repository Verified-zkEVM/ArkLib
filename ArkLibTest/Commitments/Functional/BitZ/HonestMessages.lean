/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/

import ArkLib.Commitments.Functional.BitZ.HonestMessages
import ArkLibTest.Commitments.Functional.BitZ.FixedWitnessError

/-!
# BitZ honest messages: instances and axiom boundaries

The honest second message is executable and is run through the decidable `Round2Check` and
`GrandProductClaim` on explicit constant polynomials, with a tampered message and a non-bit matrix
as controls. The theorems are applied to the same data, to the data where the overflow hypothesis
fails, and at the generality of the theorems, where the honest first message meets the hypotheses of
the bound on Rounds 1 and 2. The identification of the honest first message with the original claim
is instantiated over `ℤ` and over the semiring `S = ℕ`, and for the bits of a witness with bounded
digits. The explicit constant polynomial `constPoly` comes from `FixedWitnessError`, and the
generator `g7` of `(ZMod 7)ˣ` from `Basic`.
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
  decide (Round2Check 2 (fun _ : Fin 1 => constPoly 2 (by norm_num)) μ' 3 (fun i => i.elim0) μ ∧
    GrandProductClaim g7 lifts f 3 (fun i => i.elim0) μ)

-- The honest messages pass; a tampered second message `0` fails only the grand product; for the
-- non-bit matrix `f = 2` the honest messages `μ₁ = 6` and `μ' = 12` fail only the range check.
/-- info: [true, false, false] -/
#guard_msgs in
#eval
  [pass (fun _ => 1) (constPoly 6 (by norm_num))
      (honestRound2Message (f := fun _ : Fin 2 × Fin 1 => 1) 3 (fun i : Fin 0 => i.elim0) lifts),
    pass (fun _ => 1) (constPoly 6 (by norm_num)) (fun _ => 0),
    pass (fun _ => 2) (constPoly 12 (by norm_num))
      (honestRound2Message (f := fun _ : Fin 2 × Fin 1 => 2) 3 (fun i : Fin 0 => i.elim0) lifts)]

/-! ### The theorems on the same shape of data -/

/-- The honest messages pass without an overflow hypothesis. On the data of the necessity example
in `FixedWitnessError` (three lifts `4`, one lift `1`, `q = 5`), where `ℓ₁ · (q - 1) = 12` is not
below `|F| - 1 = 6` in `ZMod 7` and a dishonest message satisfies the check and the claim with a
false reduced claim, the honest messages still pass. -/
example : Round2Check 3 (fun _ : Fin 1 => (C 1 : MvPolynomial (Fin 0) ℤ))
      (honestMessage (fun _ : Fin 3 => (C 4 : MvPolynomial (Fin 0) ℤ))
        (fun _ : Fin 1 => (C 1 : MvPolynomial (Fin 0) ℤ)) (fun _ => 1)) 5 (fun i => i.elim0)
      (honestRound2Message 5 (fun i : Fin 0 => i.elim0)
        (fun _ : Fin 3 => (C 4 : MvPolynomial _ ℤ)) (fun _ : Fin 3 × Fin 1 => 1)) ∧
    GrandProductClaim g7 (fun _ : Fin 3 => (C 4 : MvPolynomial (Fin 0) ℤ)) (fun _ => 1) 5
      (fun i => i.elim0)
      (honestRound2Message 5 (fun i : Fin 0 => i.elim0)
        (fun _ : Fin 3 => (C 4 : MvPolynomial _ ℤ)) (fun _ : Fin 3 × Fin 1 => 1)) :=
  ⟨round2Check_honestRound2Message _ _ (fun _ => le_rfl) 5 _,
    grandProductClaim_honestRound2Message g7 _ (fun _ => le_rfl) 5 _⟩

/-- For a true claim, the honest first message satisfies the hypotheses `hμD`, `hμN` and `hμ` that
`prEvent_round2Satisfiable_le` places on the first message, and the honest second message passes
`Round2Check` and satisfies `GrandProductClaim` at every modulus `q > 0` and every point. -/
example {k : ℕ} {ι₁ ι₂ R F : Type*} [Fintype ι₁] [Fintype ι₂] [CommSemiring R] [Field F]
    (πc : MvPolynomial (Fin k) ℤ →+* R) {a : ι₁ → MvPolynomial (Fin k) ℤ}
    {b : ι₂ → MvPolynomial (Fin k) ℤ} {v₁ : ι₁ → R} {v₂ : ι₂ → R} (ha : ∀ i, πc (a i) = v₁ i)
    (hb : ∀ j, πc (b j) = v₂ j) {f : ι₁ × ι₂ → ℕ} (hf : ∀ p, f p ≤ 1) {μ : R}
    (hclaim : ∑ p : ι₁ × ι₂, v₁ p.1 * v₂ p.2 * (f p : R) = μ) {D N : ℕ}
    (haD : ∀ i, (a i).totalDegree ≤ D) (hbD : ∀ j, (b j).totalDegree ≤ D)
    (haN : ∀ i s, ((a i).coeff s).natAbs ≤ N) (hbN : ∀ j s, ((b j).coeff s).natAbs ≤ N) :
    πc (honestMessage a b f) = μ ∧ (honestMessage a b f).totalDegree ≤ 2 * D ∧
      (∀ s, ((honestMessage a b f).coeff s).natAbs ≤
        (D + k).choose k * Fintype.card (ι₁ × ι₂) * N ^ 2) ∧
      ∀ (g : Fˣ) (q : ℕ) [NeZero q] (α : Fin k → ZMod q),
        Round2Check (Fintype.card ι₁) b (honestMessage a b f) q α
            (honestRound2Message q α a f) ∧
          GrandProductClaim g a f q α (honestRound2Message q α a f) :=
  ⟨by simp only [map_honestMessage, ha, hb, hclaim], totalDegree_honestMessage_le haD hbD,
    natAbs_coeff_honestMessage_le hf haD haN hbN, fun g q _ α =>
      ⟨round2Check_honestRound2Message a b hf q α,
        grandProductClaim_honestRound2Message g a hf q α⟩⟩

/-- The honest message `⟨X₀ ⊗ 1, (1)⟩` has total degree at most `2 · 1`. -/
example :
    (honestMessage (fun _ : Fin 1 => (X 0 : MvPolynomial (Fin 1) ℤ))
      (fun _ : Fin 1 => (C 1 : MvPolynomial (Fin 1) ℤ)) (fun _ => 1)).totalDegree ≤ 2 * 1 :=
  totalDegree_honestMessage_le (fun _ => (totalDegree_X _).le)
    (fun _ => (totalDegree_C _).le.trans (Nat.zero_le _))

/-- The coefficients of the honest message `⟨X₀ ⊗ 1, (1)⟩` are bounded by
`C(1 + 1, 1) · 1 · 1 = 2`. -/
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

/-! ### The honest witness of a bounded claim

The witness `f = 5 = 1 · 4 + 0 · 2 + 1 · 1` over `γ = (1)` with `B = 3` has the bits `(1, 0, 1)` of
`coeffBits`. These satisfy the bit hypothesis, so both rounds apply to the honest witness. -/

-- Proof-only data: the polynomial constants `C n` are noncomputable, so nothing here is evaluated.
private noncomputable def liftA : Fin 1 → MvPolynomial (Fin 0) ℤ := fun _ => C 1

private noncomputable def liftB : Fin 1 × Fin 3 × Unit → MvPolynomial (Fin 0) ℤ :=
  fun x => C (2 ^ (x.2.1 : ℕ))

/-- The bits of the digits `h = 5` of the witness `f = 5` below `2 ^ 3`. -/
private def witnessBits : Fin 1 × (Fin 1 × Fin 3 × Unit) → ℕ :=
  fun p => coeffBits 3 (fun _ _ => 5 : Fin 1 × Fin 1 → Unit → ℕ) ((p.1, p.2.1), p.2.2)

/-- With `v₁ = v₂ = (1)`, the canonical image of the honest first message for the bits
`coeffBits 3 h` is the original claim `⟨1, f⟩ = 5`. -/
example : eval (Fin.elim0 : Fin 0 → ℤ) (honestMessage liftA liftB witnessBits) = 5 := by
  have h := map_honestMessage_coeffBits (eval (Fin.elim0 : Fin 0 → ℤ)) (RingHom.id ℤ)
    (fun _ : Unit => (1 : ℤ)) (B := 3) (a := liftA) (b := liftB)
    (v₁ := fun _ => 1) (v₂ := fun _ => 1) (fun _ => by simp [liftA])
    (fun j => by simp [liftB, bitWeights]) (fun _ _ => 5) (fun _ _ => by decide)
  exact h.trans (by decide +kernel)

/-- The honest second message for these bits passes `Round2Check` and satisfies
`GrandProductClaim` at every modulus `q > 0` and every point, with `coeffBits_le_one` as the bit
hypothesis. -/
example (q : ℕ) [NeZero q] (α : Fin 0 → ZMod q) :
    Round2Check (Fintype.card (Fin 1)) liftB (honestMessage liftA liftB witnessBits) q α
        (honestRound2Message q α liftA witnessBits) ∧
      GrandProductClaim g7 liftA witnessBits q α (honestRound2Message q α liftA witnessBits) :=
  ⟨round2Check_honestRound2Message liftA liftB (fun _ => coeffBits_le_one _ _ _) q α,
    grandProductClaim_honestRound2Message g7 liftA (fun _ => coeffBits_le_one _ _ _) q α⟩

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

/--
info: 'BitZ.map_honestMessage_coeffBits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.map_honestMessage_coeffBits

/--
info: 'BitZ.grandProductClaim_honestRound2Message' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.grandProductClaim_honestRound2Message
