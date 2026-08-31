/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.PowTwo
import ArkLib.Data.Lattices.CyclotomicRing.Galois.Order
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Two-Factor Decomposition of `R_q` for `q ≡ 5 (mod 8)` (Hachi §3, Lemma 5)

For a prime `q ≡ 5 (mod 8)`, the cyclotomic ring `R_q = Z_q[X]/(X^{2^α}+1)` has, behind the
field property of `R_q^H` (Hachi [NOZ26, §3, Lemma 5]), the structural fact that `X^{2^α}+1`
factors over `Z_q` into exactly **two** coprime irreducibles, with the conjugation `σ_{-1}`
swapping them. This file supplies the number-theoretic inputs; the field statement is assembled in
`Subfield/Field.lean` via a direct divisibility argument.

This file collects Phases 1–2 of the blueprint
(`blueprint/src/lattices/hachi_subfield.tex`):

* **Phase 1** — number theory: `orderOf q = 2^{α-1}` in `(Z/2^{α+1})ˣ` and `−1 ∉ ⟨q⟩`.
* **Phase 2** — `X^{2^α}+1 = Φ_{2^{α+1}}` has exactly two irreducible factors of degree `d/2`.

The cyclotomic identity is immediate from `IsCyclotomic`; the factor count comes from Mathlib's
`normalizedFactors_cyclotomic_card`; the order computation reuses the 2-adic
lifting-the-exponent toolkit of `Galois/Order.lean` together with
`ZMod.orderOf_one_add_four_mul`.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi …*][NOZ26]
-/

open Polynomial

namespace ArkLib.Lattices.CyclotomicModulus

variable (q : ℕ) [Fact (Nat.Prime q)] [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)]

/-! ## Phase 2: the cyclotomic identity (free from `IsCyclotomic`) -/

omit [NeZero q] in
/-- **`X^{2^α}+1 = Φ_{2^{α+1}}` over `Z_q`** (Hachi modulus is the `2^{α+1}`-th cyclotomic).
Immediate from the `IsCyclotomic` instance of `powTwoCyclotomic` and `powTwoCyclotomic_toPoly`;
`conductor = 2^{α+1}` definitionally. -/
theorem Xpow_add_one_eq_cyclotomic (α : ℕ) :
    (Polynomial.X ^ (2 ^ α) + 1 : (ZMod q)[X]) = cyclotomic (2 ^ (α + 1)) (ZMod q) := by
  have h := (powTwoCyclotomic_isCyclotomic (R := ZMod q) α).isCyclotomic
  rwa [powTwoCyclotomic_toPoly] at h

/-! ## Phase 1: the order of `q` and `−1 ∉ ⟨q⟩` -/

omit [Fact (Nat.Prime q)] [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
/-- **(Phase 1)** The multiplicative order of `q` modulo the conductor `2^{α+1}` is `2^{α-1}`,
for `q ≡ 5 (mod 8)`. Writing `q = 1 + 4·(2t+1)` (from `q = 8t+5`) with `2t+1` odd, this is
`ZMod.orderOf_one_add_four_mul` over `ZMod (2^{(α-1)+2})`. -/
theorem orderOf_q_eq (hq5 : q % 8 = 5) {α : ℕ} (hα : 1 ≤ α) :
    orderOf (q : ZMod (2 ^ (α + 1))) = 2 ^ (α - 1) := by
  obtain ⟨t, ht⟩ : ∃ t, q = 8 * t + 5 := ⟨q / 8, by omega⟩
  have hae : α - 1 + 2 = α + 1 := by omega
  have key := ZMod.orderOf_one_add_four_mul (2 * (t : ℤ) + 1) ⟨t, by ring⟩ (α - 1)
  rw [hae] at key
  rw [← key]
  congr 1
  rw [ht]; push_cast; ring

omit [Fact (Nat.Prime q)] [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
/-- **(Phase 1)** `−1 ∉ ⟨q⟩` in `(Z/2^{α+1})ˣ`, stated as: no power of `q` equals `−1`. For
`q ≡ 5 (mod 8)`, every power of `q` is `≡ 1 (mod 4)` (since `q ≡ 1 (mod 4)`), while `−1 ≡ 3 (mod 4)`
(as `α ≥ 1`, so `4 ∣ 2^{α+1}`); projecting to `ZMod 4` separates them. This is the precise sense in
which `q ≡ 5 (mod 8)` forces `σ_{-1}` to swap the two CRT factors. -/
theorem neg_one_notMem_powers_q (hq5 : q % 8 = 5) {α : ℕ} (hα : 1 ≤ α) :
    ∀ n : ℕ, (q : ZMod (2 ^ (α + 1))) ^ n ≠ -1 := by
  intro n hn
  have hdvd : (4 : ℕ) ∣ 2 ^ (α + 1) := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl]; exact pow_dvd_pow 2 (by omega)
  have hq4 : (q : ZMod 4) = 1 := by
    have h := (ZMod.natCast_eq_natCast_iff q 1 4).mpr (by rw [Nat.ModEq]; omega)
    simpa using h
  have hcast := congrArg (ZMod.castHom hdvd (ZMod 4)) hn
  rw [map_pow, map_neg, map_one, map_natCast, hq4, one_pow] at hcast
  exact absurd hcast (by decide)

/-! ## Phase 2: factor count -/

omit [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
/-- **(Phase 2)** `Φ_{2^{α+1}}` over `Z_q` has exactly two distinct monic irreducible factors,
each of degree `2^{α-1} = d/2`, for `q ≡ 5 (mod 8)`. From Mathlib's
`normalizedFactors_cyclotomic_card` (count `= φ(2^{α+1}) / ord = 2^α / 2^{α-1} = 2`) and
`natDegree_of_mem_normalizedFactors_cyclotomic` (degree `= ord = 2^{α-1}`), using
`orderOf_q_eq`. -/
theorem cyclotomic_card_normalizedFactors (hq5 : q % 8 = 5) {α : ℕ} (hα : 1 ≤ α) :
    (UniqueFactorizationMonoid.normalizedFactors
        (cyclotomic (2 ^ (α + 1)) (ZMod q))).toFinset.card = 2 := by
  have hcard : Fintype.card (ZMod q) = q ^ 1 := by rw [pow_one]; exact ZMod.card q
  have hcop : Nat.Coprime q (2 ^ (α + 1)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes (Fact.out : q.Prime) Nat.prime_two).mpr (by omega))
  rw [Polynomial.normalizedFactors_cyclotomic_card hcard hcop,
    Nat.totient_prime_pow_succ Nat.prime_two α]
  have hord : orderOf (ZMod.unitOfCoprime (q ^ 1) (hcop.pow_left 1)) = 2 ^ (α - 1) := by
    rw [← orderOf_units, ZMod.coe_unitOfCoprime, pow_one]
    exact orderOf_q_eq q hq5 hα
  rw [hord, show (2 : ℕ) - 1 = 1 from rfl, mul_one,
    Nat.pow_div (Nat.sub_le α 1) (by norm_num), show α - (α - 1) = 1 from by omega, pow_one]

end ArkLib.Lattices.CyclotomicModulus
