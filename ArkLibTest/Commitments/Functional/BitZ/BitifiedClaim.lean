/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/

import ArkLib.Commitments.Functional.BitZ.BitifiedClaim
import ArkLibTest.Commitments.Functional.BitZ.RoundsSoundness

/-!
# BitZ bitified claim: instances and axiom boundaries

Over `S = ℤ` and `R = ZMod 5`, the original claim `⟨v₁ ⊗ v₂, ψ(L g)⟩` is computed on both sides of
the correspondence for a vector of bits. The soundness bound is instantiated with `S = R = ℤ`, the
primes `{11, 13}` and the generator `g17` of `(ZMod 17)ˣ`, with the nontrivial error `2 / 11`.
-/

open BitZ MvPolynomial Matrix Finset
open scoped BigOperators ProbabilityTheory

private def ψ₅ : ℤ →+* ZMod 5 := Int.castRingHom (ZMod 5)

/-- `γ = (1)`, `B = 2`, `v₁ = (1, 2)`, `v₂ = (3)` and the bits `g(i, k) = [[1, 1], [0, 1]]` give the
entries `f = L g = (3, 2)` and `v = (3, 6) ≡ (3, 1)`, so `⟨v, ψ(f)⟩ = 3 · 3 + 1 · 2 = 11 ≡ 1`.
The tensor form `∑ v₁ᵢ · u₂ⱼ · gᵢⱼ` with `u₂ = (3, 6) ≡ (3, 1)` is
`1 · (3 + 1) + 2 · (0 + 1) = 6 ≡ 1`. -/
example :
    (fun p : Fin 2 × Fin 1 => (![1, 2] p.1 : ZMod 5) * (![3] p.2 : ZMod 5)) ⬝ᵥ
      (fun p => ψ₅ ((bitMatrix (fun _ : Unit => (1 : ℤ)) 2 *ᵥ fun x =>
        ((![![1, 1], ![0, 1]] x.1.1 x.2.1 : ℕ) : ℤ)) p)) = 1 ∧
    ∑ p : Fin 2 × Fin 1 × Fin 2 × Unit, (![1, 2] p.1 : ZMod 5) *
      bitWeights ψ₅ (fun _ : Unit => (1 : ℤ)) 2 (![3] : Fin 1 → ZMod 5) p.2 *
        (((fun x : (Fin 2 × Fin 1) × Fin 2 × Unit => ![![1, 1], ![0, 1]] x.1.1 x.2.1)
          ((p.1, p.2.1), p.2.2) : ℕ) : ZMod 5) = 1 := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- The correspondence holds for these data, as an instance of the theorem. -/
example :
    (fun p : Fin 2 × Fin 1 => (![1, 2] p.1 : ZMod 5) * (![3] p.2 : ZMod 5)) ⬝ᵥ
      (fun p => ψ₅ ((bitMatrix (fun _ : Unit => (1 : ℤ)) 2 *ᵥ fun x =>
        ((![![1, 1], ![0, 1]] x.1.1 x.2.1 : ℕ) : ℤ)) p)) =
    ∑ p : Fin 2 × Fin 1 × Fin 2 × Unit, (![1, 2] p.1 : ZMod 5) *
      bitWeights ψ₅ (fun _ : Unit => (1 : ℤ)) 2 (![3] : Fin 1 → ZMod 5) p.2 *
        (((![![1, 1], ![0, 1]] p.1 p.2.2.1 : ℕ)) : ZMod 5) :=
  dotProduct_tensor_map_bitMatrix_mulVec ψ₅ (fun _ : Unit => (1 : ℤ)) 2 ![1, 2] ![3]
    (fun x => ![![1, 1], ![0, 1]] x.1.1 x.2.1)

/-- The tensor decomposition of the weights: the entry at `((1, 0), 1, ())` is
`v₁ 1 · u₂ (0, 1, ())` with `v₁ = (1, 2)` and `v₂ = (3)`. -/
example :
    bitWeights ψ₅ (fun _ : Unit => (1 : ℤ)) 2
        (fun p : Fin 2 × Fin 1 => (![1, 2] p.1 : ZMod 5) * (![3] p.2 : ZMod 5))
        (((1 : Fin 2), (0 : Fin 1)), (1 : Fin 2), ()) =
      (![1, 2] (1 : Fin 2) : ZMod 5) *
        bitWeights ψ₅ (fun _ : Unit => (1 : ℤ)) 2 (![3] : Fin 1 → ZMod 5)
          ((0 : Fin 1), (1 : Fin 2), ()) :=
  bitWeights_tensor ψ₅ (fun _ : Unit => (1 : ℤ)) 2 ![1, 2] ![3] _

/-- The identification holds over a commutative semiring that is not a ring: over `S = R = ℕ` with
`ψ = id`, `γ = (1)`, `B = 2`, `v₁ = (1, 2)`, `v₂ = (3)` and the bits `[[1, 1], [0, 1]]`, both
sides are `3 · 3 + 6 · 2 = 21`. -/
example :
    (fun p : Fin 2 × Fin 1 => (![1, 2] p.1 : ℕ) * (![3] p.2 : ℕ)) ⬝ᵥ
      (fun p => RingHom.id ℕ ((bitMatrix (fun _ : Unit => (1 : ℕ)) 2 *ᵥ fun x =>
        ((![![1, 1], ![0, 1]] x.1.1 x.2.1 : ℕ) : ℕ)) p)) = 21 ∧
    (fun p : Fin 2 × Fin 1 => (![1, 2] p.1 : ℕ) * (![3] p.2 : ℕ)) ⬝ᵥ
      (fun p => RingHom.id ℕ ((bitMatrix (fun _ : Unit => (1 : ℕ)) 2 *ᵥ fun x =>
        ((![![1, 1], ![0, 1]] x.1.1 x.2.1 : ℕ) : ℕ)) p)) =
    ∑ p : Fin 2 × Fin 1 × Fin 2 × Unit, (![1, 2] p.1 : ℕ) *
      bitWeights (RingHom.id ℕ) (fun _ : Unit => (1 : ℕ)) 2 (![3] : Fin 1 → ℕ) p.2 *
        (((![![1, 1], ![0, 1]] p.1 p.2.2.1 : ℕ)) : ℕ) :=
  ⟨by decide +kernel, dotProduct_tensor_map_bitMatrix_mulVec (RingHom.id ℕ)
    (fun _ : Unit => (1 : ℕ)) 2 ![1, 2] ![3] (fun x => ![![1, 1], ![0, 1]] x.1.1 x.2.1)⟩

/-- The soundness bound for a bitified claim, with the nontrivial error `2 / 11`. Take `S = R = ℤ`,
`ψ = id`, `γ = (1)`, `B = 1`, `v₁ = v₂ = (1)`, the bit `0`, so `⟨v, ψ(L · 0)⟩ = 0 ≠ 1 = μ`, the
lifts `a = X₀`, `b = 1` and `μ' = 1`, which `π_canon = eval (1, …)` sends to `1`. -/
example : Pr{let q ← $ᵗ ↥({11, 13} : Finset ℕ); let α ← modPointSample primes_eleven_thirteen q}[
    Round2Accepts g17 (fun _ : Fin 1 => (X 0 : MvPolynomial (Fin 1) ℤ))
      (fun _ : Fin 1 × Fin 1 × Unit => (C 1 : MvPolynomial (Fin 1) ℤ))
      (fun p : Fin 1 × Fin 1 × Fin 1 × Unit => ((fun _ => 0 : (Fin 1 × Fin 1) × Fin 1 × Unit → ℕ)
        ((p.1, p.2.1), p.2.2))) (1 : MvPolynomial (Fin 1) ℤ) q.val α] ≤
      ENNReal.ofReal (2 / 11 : ℝ) := by
  have hX : ∀ s, ((X 0 : MvPolynomial (Fin 1) ℤ).coeff s).natAbs ≤ 1 := by
    intro s
    rw [coeff_X]
    split_ifs <;> simp
  have hC : ∀ s, ((C 1 : MvPolynomial (Fin 1) ℤ).coeff s).natAbs ≤ 1 := by
    intro s
    rw [coeff_C]
    split_ifs <;> simp
  have h := prEvent_round2Accepts_le_bitified (F := ZMod 17) (g := g17) g17_generates
    (eval fun _ => 1) (RingHom.id ℤ) (fun _ : Unit => (1 : ℤ)) 1
    (a := fun _ : Fin 1 => X 0) (b := fun _ : Fin 1 × Fin 1 × Unit => C 1)
    (v₁ := fun _ => 1) (v₂ := fun _ => 1) (fun _ => by simp)
    (fun j => by simp [bitWeights]) (bits := fun _ => 0) (fun _ => Nat.zero_le _)
    (μ := 1) (μ' := 1) (by simp) (by simp [dotProduct, bitMatrix, mulVec]) (D := 1) (N := 1)
    (fun _ => (totalDegree_X _).le) (fun _ => (totalDegree_C _).le.trans (Nat.zero_le _))
    (fun _ s => hX s) (fun _ s => hC s) (by simp) (fun s => by
      rw [coeff_one]
      split_ifs <;> simp)
    primes_eleven_thirteen (qmin := 11) (by norm_num)
    (fun q hq => by simp only [mem_insert, mem_singleton] at hq; omega)
    (fun q hq => by
      simp only [mem_insert, mem_singleton] at hq
      rcases hq with rfl | rfl <;> simp [ZMod.card])
  have hlog : Nat.log 11 4 = 0 := by decide
  convert h using 1
  norm_num [hlog]

/-! ### Axiom boundaries -/

/--
info: 'BitZ.dotProduct_tensor_map_bitMatrix_mulVec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.dotProduct_tensor_map_bitMatrix_mulVec

/--
info: 'BitZ.prEvent_round2Accepts_le_bitified' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.prEvent_round2Accepts_le_bitified
