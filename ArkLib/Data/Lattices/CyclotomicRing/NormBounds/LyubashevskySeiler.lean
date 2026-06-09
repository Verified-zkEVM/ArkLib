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

The argument is a genuine piece of algebraic number theory, specialized to the `k = 2`
splitting case, and is *not* available in Mathlib in directly usable form. Write `n := 2^α`.
The plan decomposes it into provable sub-lemmas:

* **A. Splitting of the modulus mod `q`.** `q ≡ 5 (mod 8)` forces the multiplicative order
  of `q` in `(ZMod (2^{α+1}))ˣ` to be `2^{α-1}` (the structure of the 2-power unit group).
  Hence `cyclotomic (2^{α+1}) (ZMod q) = X^n + 1` factors into *exactly two* monic
  irreducibles `φ₁ · φ₂`, each of degree `n / 2`, via
  `natDegree_of_dvd_cyclotomic_of_irreducible` (factor degree `= orderOf`) plus counting.
  Edge case `α = 0`: `Rq = ZMod q` is a field, so nonzero implies unit; handle separately.
* **B. CRT and the unit criterion.** `φ₁, φ₂` are coprime, so
  `Rq Φ ≅ (ZMod q)[X]/(φ₁) × (ZMod q)[X]/(φ₂)` (`Ideal.quotientInfRingEquivPiQuotient`), with
  each factor a field. Thus `c` is a unit iff `φᵢ ∤ c` for both `i`.
* **C. Minimum-distance bound (the hard core).** If `φᵢ | c` with `c ≠ 0` and `deg c < n`,
  then `c` is a nonzero element of the ideal lattice `(φᵢ)` of determinant `q^{n/2}`, so its
  centered Euclidean norm obeys `‖c‖₂ ≥ √q`. The most tractable Lean route is the LS `k = 2`
  field-norm trick (multiply by the Galois conjugate; `q` divides a quantity `≤ ‖c‖₂²`),
  rather than the general `min ≥ det^{1/n}` Minkowski bound. No Mathlib lemma covers this.
* **D. Norm bridge and assembly.** `‖c‖₂² ≤ ‖c‖₁² ≤ κ² < q` (elementary `l2NormSq ≤ l1Norm²`,
  provable from the definitions in `NormBounds.Basic`), i.e. `‖c‖₂ < √q`. With C, a nonzero
  non-unit `c` would force `‖c‖₂² ≥ q`, a contradiction; hence `c` is a unit.

Phase D is routine ArkLib-norm bookkeeping; phases A and C are the heavy number-theoretic
lifts and may need new Mathlib-level lemmas. Proof currently deferred (`sorry`).

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
