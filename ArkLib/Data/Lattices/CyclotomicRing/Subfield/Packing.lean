/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.Basis

/-!
# The Packing Map `ψ : (R_q^H)^{d/k} → R_q` (Hachi §3, Theorem 2, Eq. 8)

Hachi [NOZ26, §3, Theorem 2] packs a vector of `d/k` subfield elements into a single ring
element via

  `ψ(a) = Σ_{i<d/2k} a_i · X^i + X^{d/2} · Σ_{i<d/2k} a_{d/2k+i} · X^i`.   (Eq. 8)

Writing `d = 2^α`, `d/2 = 2^{α-1}`, `d/2k = 2^α/(2k)`, `d/k = 2^α/k`, this is a single sum over
the index set `Fin (d/k)` with a piecewise exponent map `packExp`:

  `ψ(a) = Σ_{j : Fin (d/k)} a_j · X^{packExp j}`,
  `packExp j = j`                     for `j < d/2k`,
  `packExp j = d/2 + (j − d/2k)`       for `j ≥ d/2k`.

## Main definitions

* `packExp α k` — the exponent map `j ↦ packExp j`.
* `psi α k` — the packing map `ψ`, additive in its argument (`psi_add`).

## Bijectivity (Theorem 2)

`ψ` is a bijection. The proof routes through:

* **injectivity** (`psi_injective`, in `Subfield/TraceInnerProduct.lean`), from the non-degenerate
  trace pairing of Theorem 2 (`traceH_psi_mul_conj`): testing `ψ(a) = ψ(b)` against `e_j` recovers
  `a_j = b_j`; and
* **cardinality** (`card_fixedSubring_eq`, `|R_q^H| = q^k`, in `Subfield/Cardinality.lean`), from
  the symmetric basis of `Subfield/Basis.lean`, giving `|(R_q^H)^{d/k}| = (q^k)^{d/k} = q^d`.

These combine in `Subfield/Bijectivity.lean` (`psi_bijective`, over `R = ZMod q`).

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi …*][NOZ26]
-/

open Polynomial CompPoly CompPoly.CPolynomial Finset

namespace ArkLib.Lattices.CyclotomicModulus

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R] [DecidableEq R]

/-! ## The packing map -/

/-- The **packing exponent map**: index `j` of the packed vector contributes the monomial
`X^{packExp j}`. The first half `[0, d/2k)` maps to `[0, d/2k)`; the second half `[d/2k, d/k)`
maps to `[d/2, d/2 + d/2k)` via the `X^{d/2}` shift. -/
def packExp (α k j : ℕ) : ℕ :=
  if j < 2 ^ α / (2 * k) then j else 2 ^ (α - 1) + (j - 2 ^ α / (2 * k))

/-- The **packing map** `ψ : (R_q^H)^{d/k} → R_q` of Hachi [NOZ26, §3, Eq. 8], as the single sum
`Σ_{j} a_j · X^{packExp j}` over the index set `Fin (d/k)`. -/
def psi (α k : ℕ) (a : Fin (2 ^ α / k) → fixedSubring (R := R) α k) :
    Rq (powTwoCyclotomic (R := R) α) :=
  ∑ j : Fin (2 ^ α / k),
    (a j : Rq (powTwoCyclotomic α)) * Xpow (powTwoCyclotomic α) (packExp α k j.val)

@[simp] theorem psi_zero (α k : ℕ) :
    psi α k (0 : Fin (2 ^ α / k) → fixedSubring (R := R) α k) = 0 := by
  unfold psi
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [Pi.zero_apply, ZeroMemClass.coe_zero, MulZeroClass.zero_mul]

/-- `ψ` is additive (it is a `Z_q`-linear / additive map; additivity is what the injectivity
argument needs). -/
theorem psi_add (α k : ℕ) (a b : Fin (2 ^ α / k) → fixedSubring (R := R) α k) :
    psi α k (a + b) = psi α k a + psi α k b := by
  unfold psi
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Pi.add_apply, AddMemClass.coe_add, _root_.add_mul]

/-! ## Bijectivity

`ψ` is injective (from the non-degenerate trace pairing of Theorem 2) and bijective (injectivity
plus the cardinality match `|(R_q^H)^{d/k}| = q^d = |R_q|`). These are proven in
`Subfield/TraceInnerProduct.lean`, after the trace formula `traceH_psi_mul_conj`. -/

end ArkLib.Lattices.CyclotomicModulus
