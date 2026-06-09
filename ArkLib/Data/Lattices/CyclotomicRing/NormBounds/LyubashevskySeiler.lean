/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.NormBounds.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# Lyubashevsky–Seiler: Short Elements Are Invertible

The Lyubashevsky–Seiler invertibility result [LS18, Corollary 1.2]; recalled as Lemma 3 of
the Hachi paper [NOZ26]: over the power-of-two cyclotomic modulus `φ = X^{2^α} + 1`
(`powTwoCyclotomic α`) with a prime `q ≡ 5 (mod 8)`, a nonzero element of
`Rq (powTwoCyclotomic α) = ZMod q[X]/(X^{2^α}+1)` whose centered Euclidean norm is below
`√q` is a unit.

The statement is deliberately pinned to `powTwoCyclotomic α` (`X^{2^α}+1`): LS18 Cor. 1.2
is the `k = 2` splitting case (`q ≡ 2·2+1 ≡ 5 (mod 8)`, Euclidean bound `q^{1/2} = √q`),
and that splitting / minimum-distance analysis is specific to the negacyclic ring. For a
general cyclotomic `Φ_m` of power-of-two *degree* (e.g. `Φ₁₅`, `Φ₁₂`) the `q ≡ 5 (mod 8)`
condition and the `√q` bound are simply wrong, so phrasing the lemma for an arbitrary
`Φ` with `deg φ = 2^α` would be unsound.

This is one of the two unproven lemmas for the Greyhound [NS24] / Hachi [NOZ26]
weak-binding argument; the other is `scalarVecMul_mul_l2NormSq_le` in
`NormBounds.MicciancioYoung`.

## Proof plan (issue #549)

The argument specializes to the `k = 2` splitting case and, crucially, needs **no** ideal
lattices, canonical embedding, or Minkowski bound (contrary to the original sketch): it
reduces to an elementary `mod q` divisibility count. Write `n := 2^α`. All Mathlib pieces
exist, so the remaining work is formalization, not new theory.

* **A. Order of `q` and factor degree.** For `q ≡ 5 (mod 8)`, lifting-the-exponent
  (`Int.two_pow_sub_pow'`) gives `v₂(q^{2^k} - 1) = k + 2`, so the multiplicative order of
  `q` modulo `2^{α+1}` is `2^{α-1}`. Hence every irreducible factor of
  `cyclotomic (2^{α+1}) (ZMod q) = X^n + 1` has degree `2^{α-1} = n/2`
  (`Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible`); a root `ζ` (`ζ^n = -1`) then has
  `[ZMod q (ζ) : ZMod q] = n/2`. Edge case `α = 0`: `Rq = ZMod q` is a field, nonzero ⇒ unit.
* **B. Square root of `-1`.** `q ≡ 5 (mod 8) ⇒ q % 4 ≠ 3`, so `∃ r : ZMod q, r^2 = -1`
  (`ZMod.exists_sq_eq_neg_one_iff`). For a root `ζ`, `s := ζ^{n/2}` has `s^2 = ζ^n = -1`, so
  `s = ±r ∈ ZMod q`.
* **C. Coefficient relations (replaces the lattice argument).** If `c` is a non-unit, an
  irreducible factor divides its lift, giving a root `ζ` with `c̃(ζ) = 0`. Splitting the `n`
  coefficients into low/high halves, `c̃(ζ) = Σ_{j<n/2} (c_j + s·c_{n/2+j}) ζ^j`; by the
  degree-`n/2` independence of `1,…,ζ^{n/2-1}` from A, every `c_j + s·c_{n/2+j} = 0` in
  `ZMod q`. Squaring with `s^2 = -1` gives, over `ℤ`, `q ∣ (c̃_j² + c̃_{n/2+j}²)` for each `j`.
* **D. Finish (norm bridge proven below).** `‖c‖₂² = Σ_{j<n/2} (c̃_j² + c̃_{n/2+j}²)` is a sum
  of nonnegative multiples of `q`, while `‖c‖₂² ≤ ‖c‖₁² ≤ κ² < q` (`l2NormSq_le_l1Norm_sq`),
  so every term is `0`, forcing `c = 0` and contradicting `‖c‖₁ > 0`. Hence `c` is a unit.

Phase D's `‖c‖₂² ≤ ‖c‖₁²` is proven as `l2NormSq_le_l1Norm_sq`; phases A–C remain to be
formalized. Main theorem currently `sorry`.

## References

* [Lyubashevsky, V., and Seiler, G., *Short, Invertible Elements in Partially Splitting
    Cyclotomic Rings*][LS18]
* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open scoped BigOperators

namespace ArkLib.Lattices.CyclotomicModulus

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] (α : ℕ)

/-- The power-of-two ("Hachi") cyclotomic modulus `X^{2^α}+1` over `ZMod q`. -/
local notation "Φ" => (powTwoCyclotomic (R := ZMod q) α)

omit [NeZero q] in
/-- **Phase D norm bridge.** The centered squared `ℓ₂` norm is at most the square of the
centered `ℓ₁` norm: `‖c‖₂² ≤ ‖c‖₁²`. This is `Σ aₖ² ≤ (Σ aₖ)²` for nonnegative `aₖ`. -/
theorem Rq.l2NormSq_le_l1Norm_sq (c : Rq Φ) :
    Rq.l2NormSq Φ c ≤ (Rq.l1Norm Φ c) ^ 2 := by
  unfold Rq.l2NormSq Rq.l1Norm
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => Nat.zero_le _)

/-- **Lyubashevsky–Seiler: short elements are invertible** (LS18, Cor. 1.2; Hachi, Lemma 3).
Over the power-of-two cyclotomic modulus `powTwoCyclotomic α` (`φ = X^{2^α}+1`) with a prime
`q ≡ 5 (mod 8)`, a nonzero element of `Rq (powTwoCyclotomic α)` with centered `ℓ₁` norm
`≤ κ` and `κ² < q` is a unit (then `‖c‖₂² ≤ ‖c‖₁² ≤ κ² < q`, the LS `k = 2` bound
`‖c‖ < √q`). A genuine piece of algebraic number theory (ideal-lattice minimum distance via
the cyclotomic embedding); recorded here with `sorry`. -/
theorem isUnit_of_l1Norm_le (hq5 : q % 8 = 5) {c : Rq Φ} {κ : ℕ}
    (hpos : 0 < Rq.l1Norm Φ c) (hle : Rq.l1Norm Φ c ≤ κ) (hκ : κ ^ 2 < q) :
    IsUnit c := by
  sorry

end ArkLib.Lattices.CyclotomicModulus
