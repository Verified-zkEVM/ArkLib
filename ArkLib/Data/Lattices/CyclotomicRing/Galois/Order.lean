/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import Mathlib.NumberTheory.Multiplicity
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# The order of `4k+1` modulo `2^{α+1}` (2-adic lifting-the-exponent)

This file isolates the number-theoretic core behind the cardinality and permutation facts for the
subgroup `H = ⟨σ_{-1}, σ_{4k+1}⟩` used in Hachi [NOZ26, §3] (`CyclotomicRing/Galois/Group.lean`).

For `k = 2^κ`, write `g := 4k+1 = 1 + 2^{κ+2}`. The Lyubashevsky–Seiler order fact
([LS18, Lem 2.4]) is that `g` has order `2^{α-κ-1} = d/(2k)` modulo `2^{α+1} = 2d`. We obtain it
from Mathlib's 2-adic lifting-the-exponent `Int.two_pow_sub_pow'`:
`v₂(gⁿ − 1) = v₂(g − 1) + v₂(n) = (κ+2) + v₂(n)`.

## Main results

* `emultiplicity_four_pow_sub_one` — the LTE valuation `v₂(gⁿ − 1) = (κ+2) + v₂(n)`.
* `two_pow_dvd_four_pow_sub_one_iff` — `2^{α+1} ∣ gⁿ − 1 ↔ 2^{α-κ-1} ∣ n`.

## References

* [Lyubashevsky, V., and Seiler, G., *Short, Invertible Elements …*][LS18]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi …*][NOZ26]
-/

namespace ArkLib.Lattices.CyclotomicModulus

/-- **2-adic LTE for `g = 4·2^κ + 1`**: `v₂(gⁿ − 1) = (κ+2) + v₂(n)`. -/
theorem emultiplicity_four_pow_sub_one (κ n : ℕ) :
    emultiplicity 2 ((4 * 2 ^ κ + 1 : ℤ) ^ n - 1)
      = (κ + 2 : ℕ) + emultiplicity 2 (n : ℤ) := by
  have hodd : Odd (4 * 2 ^ κ + 1 : ℤ) := ⟨2 * 2 ^ κ, by ring⟩
  have hx : ¬ (2 : ℤ) ∣ (4 * 2 ^ κ + 1) := by rcases hodd with ⟨m, hm⟩; omega
  have hxy : (4 : ℤ) ∣ (4 * 2 ^ κ + 1) - 1 := ⟨2 ^ κ, by ring⟩
  have hsub : (4 * 2 ^ κ + 1 : ℤ) - 1 = 2 ^ (κ + 2) := by rw [pow_add]; ring
  have h := Int.two_pow_sub_pow' (x := 4 * 2 ^ κ + 1) (y := 1) n hxy hx
  rw [one_pow, hsub, emultiplicity_pow_self_of_prime Int.prime_two] at h
  exact h

/-- **Divisibility characterization**: `2^{α+1} ∣ gⁿ − 1 ↔ 2^{α-κ-1} ∣ n` for `g = 4·2^κ+1`,
when `κ + 1 ≤ α` (so `α - κ - 1` is the genuine order `d/(2k)`). -/
theorem two_pow_dvd_four_pow_sub_one_iff (κ α n : ℕ) (hκ : κ + 1 ≤ α) :
    (2 : ℤ) ^ (α + 1) ∣ (4 * 2 ^ κ + 1 : ℤ) ^ n - 1 ↔ 2 ^ (α - κ - 1) ∣ n := by
  rw [pow_dvd_iff_le_emultiplicity, emultiplicity_four_pow_sub_one,
    ← Int.natCast_dvd_natCast (m := 2 ^ (α - κ - 1)) (n := n), Int.natCast_pow,
    Nat.cast_ofNat, pow_dvd_iff_le_emultiplicity,
    show ((α + 1 : ℕ) : ℕ∞) = ((κ + 2 : ℕ) : ℕ∞) + ((α - κ - 1 : ℕ) : ℕ∞) by
      rw [← Nat.cast_add]; congr 1; omega]
  exact WithTop.add_le_add_iff_left (ENat.coe_ne_top (κ + 2))

/-- The `ℕ`-level divisibility characterization: `2^{α+1} ∣ gⁿ − 1 ↔ 2^{α-κ-1} ∣ n`. -/
theorem four_pow_dvd_iff_nat (κ α n : ℕ) (hκ : κ + 1 ≤ α) :
    2 ^ (α + 1) ∣ (4 * 2 ^ κ + 1) ^ n - 1 ↔ 2 ^ (α - κ - 1) ∣ n := by
  have hge : (1 : ℕ) ≤ (4 * 2 ^ κ + 1) ^ n := Nat.one_le_pow _ _ (by positivity)
  rw [← two_pow_dvd_four_pow_sub_one_iff κ α n hκ, ← Int.natCast_dvd_natCast, Nat.cast_sub hge]
  push_cast
  rfl

private theorem four_pow_aux (κ α a b : ℕ) (hκ : κ + 1 ≤ α) (hb : b < 2 ^ (α - κ - 1))
    (hlt : a < b)
    (hab : (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1) = (4 * 2 ^ κ + 1) ^ b % 2 ^ (α + 1)) : False := by
  have hmod : (4 * 2 ^ κ + 1) ^ a ≡ (4 * 2 ^ κ + 1) ^ b [MOD 2 ^ (α + 1)] := hab
  have hdvdZ : (2 : ℤ) ^ (α + 1) ∣ (4 * 2 ^ κ + 1 : ℤ) ^ b - (4 * 2 ^ κ + 1 : ℤ) ^ a := by
    have h := Nat.modEq_iff_dvd.mp hmod
    push_cast at h
    exact h
  have hfact : (4 * 2 ^ κ + 1 : ℤ) ^ b - (4 * 2 ^ κ + 1 : ℤ) ^ a
      = (4 * 2 ^ κ + 1 : ℤ) ^ a * ((4 * 2 ^ κ + 1 : ℤ) ^ (b - a) - 1) := by
    rw [mul_sub, mul_one, ← pow_add]; congr 2; omega
  rw [hfact] at hdvdZ
  have hc2 : IsCoprime (2 : ℤ) (4 * 2 ^ κ + 1) := ⟨-(2 * 2 ^ κ), 1, by ring⟩
  have hcop : IsCoprime ((2 : ℤ) ^ (α + 1)) ((4 * 2 ^ κ + 1 : ℤ) ^ a) := hc2.pow
  have ho : 2 ^ (α - κ - 1) ∣ (b - a) :=
    (two_pow_dvd_four_pow_sub_one_iff κ α (b - a) hκ).mp (hcop.dvd_of_dvd_mul_left hdvdZ)
  have := Nat.le_of_dvd (by omega) ho
  omega

/-- `a ↦ gᵃ mod 2^{α+1}` is injective on `range (2^{α-κ-1})` (the order of `g`). -/
theorem four_pow_injOn (κ α : ℕ) (hκ : κ + 1 ≤ α) :
    Set.InjOn (fun a => (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1))
      (Finset.range (2 ^ (α - κ - 1))) := by
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  rcases lt_trichotomy a b with h | h | h
  · exact (four_pow_aux κ α a b hκ hb h hab).elim
  · exact h
  · exact (four_pow_aux κ α b a hκ ha h hab.symm).elim

/-- `g` raised to its order `2^{α-κ-1}` is `≡ 1` mod `2^{α+1}`. -/
theorem four_pow_order_modEq_one (κ α : ℕ) (hκ : κ + 1 ≤ α) :
    (1 : ℕ) ≡ (4 * 2 ^ κ + 1) ^ (2 ^ (α - κ - 1)) [MOD 2 ^ (α + 1)] := by
  rw [Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by positivity))]
  exact (four_pow_dvd_iff_nat κ α _ hκ).mpr (dvd_refl _)

/-- The power `gⁿ mod 2^{α+1}` depends only on `n mod 2^{α-κ-1}` (period = order of `g`). -/
theorem four_pow_mod_period (κ α n : ℕ) (hκ : κ + 1 ≤ α) :
    (4 * 2 ^ κ + 1) ^ n ≡ (4 * 2 ^ κ + 1) ^ (n % 2 ^ (α - κ - 1)) [MOD 2 ^ (α + 1)] := by
  conv_lhs => rw [← Nat.div_add_mod n (2 ^ (α - κ - 1)), pow_add, pow_mul]
  calc ((4 * 2 ^ κ + 1) ^ 2 ^ (α - κ - 1)) ^ (n / 2 ^ (α - κ - 1))
        * (4 * 2 ^ κ + 1) ^ (n % 2 ^ (α - κ - 1))
      ≡ 1 ^ (n / 2 ^ (α - κ - 1)) * (4 * 2 ^ κ + 1) ^ (n % 2 ^ (α - κ - 1))
        [MOD 2 ^ (α + 1)] :=
        Nat.ModEq.mul_right _ (Nat.ModEq.pow _ (four_pow_order_modEq_one κ α hκ).symm)
    _ = (4 * 2 ^ κ + 1) ^ (n % 2 ^ (α - κ - 1)) := by rw [one_pow, one_mul]

/-- If the conductor `2k = 2^{κ+1}` divides `d = 2^α` (i.e. `2·2^κ ∣ 2^α`), then `κ + 1 ≤ α`.
The recurring side condition `κ + 1 ≤ α` of the Hachi `R_q^H` lemmas, extracted once. -/
theorem succ_le_of_two_mul_two_pow_dvd {α κ : ℕ} (hk : 2 * 2 ^ κ ∣ 2 ^ α) : κ + 1 ≤ α := by
  have hd : 2 ^ (κ + 1) ∣ 2 ^ α := by rw [pow_succ, mul_comm]; exact hk
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : (1 : ℕ) < 2)).mp hd

end ArkLib.Lattices.CyclotomicModulus
