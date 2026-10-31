/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/

import ArkLib.Commitments.Functional.BitZ.Bitification
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

/-!
# BitZ bitification: instances and axiom boundaries

Instances over `S = ℤ` and `ψ : ℤ → ZMod 5`. The range of `boundedCombos` is tight at `2 ^ B`, and
the closure property rules out the entries outside it. The executable definitions `bitMatrix`,
`coeffBits` and `bitWeights` are run on concrete data with independently computed results, including
the boundary `h = 2 ^ B` where the digits no longer determine the coefficient.
-/

open BitZ Matrix

/-- One monomial `1`, so that `boundedCombos` is the interval `[0, 2 ^ B)`. -/
private def oneFam : Unit → ℤ := fun _ => 1

/-- The range is tight: `7 = 2 ^ 3 - 1` is in `S^{<D}_{≤3}` but `8` is not. -/
example : (7 : ℤ) ∈ boundedCombos oneFam 3 :=
  ⟨fun _ => 7, by decide, by simp [oneFam]⟩

example : (8 : ℤ) ∉ boundedCombos oneFam 3 := by
  rintro ⟨h, hlt, hs⟩
  have := hlt default
  simp only [oneFam, Finset.univ_unique, Finset.sum_singleton, mul_one] at hs
  omega

/-- A family that lists the same monomial twice is allowed, and gives the same set. -/
example : (6 : ℤ) ∈ boundedCombos (fun _ : Fin 2 => (1 : ℤ)) 2 :=
  ⟨![3, 3], by decide, by simp [Fin.sum_univ_two]⟩

/-- Closure on a bit vector: the bits `(1, 1, 0)` are the value `3 < 2 ^ 3`. -/
example : (bitMatrix oneFam 3 *ᵥ fun x : Unit × Fin 3 × Unit => ((![1, 1, 0] x.2.1 : ℕ) : ℤ)) () ∈
    boundedCombos oneFam 3 :=
  bitMatrix_mulVec_mem _ 3 _ (fun x => by
    obtain ⟨_, k, _⟩ := x
    fin_cases k <;> simp) ()

/-- Nothing outside the range has a bitification: no vector of bits is mapped to `8` by `L`. -/
example : ¬ ∃ g : Unit × Fin 3 × Unit → ℕ, (∀ x, g x ≤ 1) ∧
    (fun _ : Unit => (8 : ℤ)) = bitMatrix oneFam 3 *ᵥ fun x => (g x : ℤ) := by
  rintro ⟨g, hg, hf⟩
  have := bitMatrix_mulVec_mem oneFam 3 g hg ()
  rw [← congrFun hf ()] at this
  exact absurd this (by
    rintro ⟨h, hlt, hs⟩
    have := hlt default
    simp only [oneFam, Finset.univ_unique, Finset.sum_singleton, mul_one] at hs
    omega)

/-! ### Running the executable definitions -/

private def γ₂ : Fin 2 → ℤ := ![1, 10]

/-- The coefficients `h = ((5, 3), (7, 0))` below `2 ^ 3`. -/
private def h₂ : Fin 2 → Fin 2 → ℕ := ![![5, 3], ![7, 0]]

-- The digits of `5 = 101₂` and `3 = 011₂`, least significant first.
/-- info: [[1, 0, 1], [1, 1, 0]] -/
#guard_msgs in
#eval [(List.finRange 3).map fun k => coeffBits 3 h₂ ((0 : Fin 2), k, (0 : Fin 2)),
  (List.finRange 3).map fun k => coeffBits 3 h₂ ((0 : Fin 2), k, (1 : Fin 2))]

-- `L` applied to the digits is `(5 · 1 + 3 · 10, 7 · 1 + 0 · 10) = (35, 7)`.
/-- info: [35, 7] -/
#guard_msgs in
#eval List.ofFn (bitMatrix γ₂ 3 *ᵥ fun x => (coeffBits 3 h₂ x : ℤ))

-- Below the boundary `h = 7 < 2 ^ 3` the digits recover `7 · (1 + 10) = 77` in each row; at the
-- boundary `h = 8 = 2 ^ 3` all digits vanish, which is why the agreement theorem needs `h < 2 ^ B`.
/-- info: [[77, 77], [0, 0]] -/
#guard_msgs in
#eval [List.ofFn (bitMatrix γ₂ 3 *ᵥ fun x =>
    (coeffBits 3 (fun _ _ => 7 : Fin 2 → Fin 2 → ℕ) x : ℤ)),
  List.ofFn (bitMatrix γ₂ 3 *ᵥ fun x =>
    (coeffBits 3 (fun _ _ => 8 : Fin 2 → Fin 2 → ℕ) x : ℤ))]

/-- The ring homomorphism `ℤ → ZMod 5`. -/
private def ψ₅ : ℤ →+* ZMod 5 := Int.castRingHom (ZMod 5)

-- The weight vector over `ZMod 5`: for `v = (2, 3)`, `γ = (1, 10)` and `ψ(10) = 0`, the entry at
-- `(1, 2, 0)` is `3 · 2 ^ 2 · 1 = 12 ≡ 2`, and every entry with `j = 1` vanishes.
/-- info: [2, 0] -/
#guard_msgs in
#eval [(bitWeights ψ₅ γ₂ 3 ![(2 : ZMod 5), 3] ((1 : Fin 2), (2 : Fin 3), (0 : Fin 2))).val,
  (bitWeights ψ₅ γ₂ 3 ![(2 : ZMod 5), 3] ((1 : Fin 2), (2 : Fin 3), (1 : Fin 2))).val]

/-- The weight vector is `ψ(L)ᵀ v`, here at one entry. -/
example :
    (((bitMatrix γ₂ 3).map ψ₅)ᵀ *ᵥ ![(2 : ZMod 5), 3]) ((1 : Fin 2), (2 : Fin 3), (0 : Fin 2)) =
      2 := by
  rw [bitMatrix_map_transpose_mulVec]
  decide

/-! ### The satisfiability equivalence is instantiated -/

/-- The claim `⟨(1, 1), ψ(f)⟩ = 2` over `ZMod 5` has the witness `f = (5, 2)`, so the bitified claim
has a witness of bits. -/
example : ∃ g : Fin 2 × Fin 3 × Unit → ℕ, (∀ x, g x ≤ 1) ∧
    (fun p => (g p : ZMod 5)) ⬝ᵥ bitWeights ψ₅ oneFam 3 ![(1 : ZMod 5), 1] = 2 :=
  (exists_witness_iff_exists_bits ψ₅ oneFam 3 ![(1 : ZMod 5), 1] 2).1
    ⟨![5, 2], fun i => by
      fin_cases i
      · exact ⟨fun _ => 5, by decide, by simp [oneFam]⟩
      · exact ⟨fun _ => 2, by decide, by simp [oneFam]⟩,
      by decide +kernel⟩

/-- The converse direction produces a witness in the range from any vector of bits. -/
example : ∃ f : Fin 2 → ℤ, (∀ i, f i ∈ boundedCombos oneFam 3) ∧
    ![(1 : ZMod 5), 1] ⬝ᵥ (fun i => ψ₅ (f i)) = ψ₅ 0 := by
  refine (exists_witness_iff_exists_bits ψ₅ oneFam 3 ![(1 : ZMod 5), 1] (ψ₅ 0)).2 ⟨fun _ => 0, ?_⟩
  simp

/-! ### No subtraction is needed

The statements hold over a commutative semiring that is not a ring: here `S = R = ℕ`. -/

/-- Closure over `ℕ`: the bits `(1, 0, 1)` give the value `5 < 2 ^ 3`. -/
example : (bitMatrix (fun _ : Unit => (1 : ℕ)) 3 *ᵥ
    fun x : Unit × Fin 3 × Unit => if x.2.1 = 1 then 0 else 1) () ∈
      boundedCombos (fun _ : Unit => (1 : ℕ)) 3 :=
  bitMatrix_mulVec_mem _ 3 (fun x : Unit × Fin 3 × Unit => if x.2.1 = 1 then 0 else 1)
    (fun x => by split_ifs <;> decide) ()

/-- The equivalence of claims over `ℕ`, instantiated with `v = (1, 1)` and `μ = 7`: the witness
`f = (5, 2)` has `⟨v, f⟩ = 7`, so the bitified claim has a witness of bits. -/
example : ∃ g : Fin 2 × Fin 3 × Unit → ℕ, (∀ x, g x ≤ 1) ∧
    (fun p => (g p : ℕ)) ⬝ᵥ bitWeights (RingHom.id ℕ) (fun _ : Unit => (1 : ℕ)) 3 ![1, 1] = 7 :=
  (exists_witness_iff_exists_bits (RingHom.id ℕ) (fun _ : Unit => (1 : ℕ)) 3 ![1, 1] 7).1
    ⟨![5, 2], fun i => by
      fin_cases i
      · exact ⟨fun _ => 5, by decide, by simp⟩
      · exact ⟨fun _ => 2, by decide, by simp⟩,
      by decide +kernel⟩

/-! ### Axiom boundaries -/

/--
info: 'BitZ.exists_bitification' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.exists_bitification

/--
info: 'BitZ.bitMatrix_mulVec_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.bitMatrix_mulVec_mem

/--
info: 'BitZ.bitMatrix_mulVec_coeffBits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.bitMatrix_mulVec_coeffBits

/--
info: 'BitZ.exists_witness_iff_exists_bits' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.exists_witness_iff_exists_bits

/--
info: 'Matrix.dotProduct_map_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.dotProduct_map_mulVec
