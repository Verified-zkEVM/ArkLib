/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.Cardinality
import ArkLib.Data.Lattices.CyclotomicRing.Norms

/-!
# The Norm Bound `‖ψ(a)‖∞ ≤ 2β` (Hachi §3, Lemma 6)

Hachi [NOZ26, §3, Lemma 6]: if `a` is a vector over `R_q^H` with `‖a‖∞ ≤ β` and `ψ` is
the packing map of Theorem 2 (Eq. 8), then `‖ψ(a)‖∞ ≤ 2β`.

The paper derives this "directly from the explicit formula in Equation (9), where some
coefficients of `ψ(a)` are equal to the sum of two coefficients of `a`". Concretely: every
entry `a_j ∈ R_q^H` is supported on the coefficient positions `(d/2k)·s` (Eq. 7), the
packing exponents `packExp j` of distinct summands of `ψ(a)` are distinct modulo `d/2k`
*within* each half of the index range, and the `X^{d/2}`-shift of the second half realigns
it with the first (`d/2 = k·(d/2k)`). Hence each coefficient of `ψ(a)` receives
contributions (with signs, from the `X^d = -1` folding) from **at most two** coefficients
of the entries of `a` — one from the first half and one from the second — which gives the
factor `2`.

Norms are the centered coefficient norms of `Norms.lean` with the balanced representative
`zmodCenteredView` (`ZMod.valMinAbs`, the paper's `mod± q` convention); `‖a‖∞` is the
entrywise maximum `vecCInfNorm`, matching the vector norm of [NOZ26, §2.1].

## Main statement

* `cInfNorm_psi_le` — **Lemma 6**, currently `sorry` (see its docstring for a proof plan).

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open CompPoly Finset

namespace ArkLib.Lattices.CyclotomicModulus

variable (q : ℕ) [Fact (Nat.Prime q)] [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)]

/-- **Hachi [NOZ26, §3, Lemma 6]: `‖ψ(a)‖∞ ≤ 2β`.** If every entry of the vector
`a : (R_q^H)^{d/k}` has centered coefficient `ℓ∞`-norm at most `β` (i.e. `‖a‖∞ ≤ β` in the
`mod± q` convention of [NOZ26, §2.1]), then the packed ring element `ψ(a) ∈ R_q` satisfies
`‖ψ(a)‖∞ ≤ 2β`.

The hypotheses are the standing assumptions of [NOZ26, §3]: `k = 2^κ` divides `d/2`
(`2·2^κ ∣ 2^α`) and `q` is odd (`(2 : ZMod q) ≠ 0`; the paper assumes `q ≡ 5 (mod 8)`, of
which only oddness is needed here).

**Status: `sorry` — open for contribution.** The paper proves this "directly from the
explicit formula in Equation (9)"; the formal proof is index/sign bookkeeping over the
existing monomial toolkit, with no new mathematical content.

## Suggested proof outline

1. *Explicit form of subfield elements (Eq. 7).* `fixedBasisMap` is injective
   (`fixedBasisMap_injective`) between fintypes of equal cardinality
   (`card_fixedSubring_eq`), hence surjective (`Fintype.bijective_iff_injective_and_card`):
   every `x ∈ R_q^H` is `Σ_s n_s • vElt s`. Extend `vElt_coeff` (currently only the
   positions `(d/2k)·s`, `s < k`) to a *full* coefficient formula: `vElt j` folds to
   `X^{(d/2k)j} − X^{d−(d/2k)j}` (`conjAut_Xpow`, `Xpow_fold`), so its coefficients vanish
   off the two positions `(d/2k)j` and `d−(d/2k)j` (`Xpow_coeff_eq_zero_of_ne`). In
   particular `x ∈ R_q^H` is supported on `{(d/2k)·s : s < 2k}`, and every coefficient of
   `x` at a support position is (up to sign and the `j = 0` doubling) one of the `n_s`, so
   each is bounded by `‖x‖∞` at a *witnessed* coefficient position of `x` itself.

2. *Coefficient of a shifted entry.* For `e < d`, expand
   `x · X^e = Σ_s n_s • (vElt s · X^e)` and
   `vElt s · X^e = X^{(d/2k)s+e} − X^{d−(d/2k)s+e}` via `vElt_coe`, `Xpow_add`,
   `mk_monomial_fold` — sums of scaled monomials only, so no general product-coefficient
   lemma is needed. Each coefficient of `x · X^e` is `±` a single coefficient of `x`
   (positions shift by `e` mod `d`, signs from `X^d = -1`).

3. *At most two contributions per position.* `packExp j ≡ j (mod d/2k)` on the first half
   and `packExp (d/2k + j) = d/2 + j ≡ j (mod d/2k)` on the second (`d/2 = k·(d/2k)`).
   Since the entries are supported on multiples of `d/2k` (step 1), the coefficient of
   `ψ(a)` at a position `p` with `p ≡ j (mod d/2k)` is `±c₁ ± c₂` where `c₁` (resp. `c₂`)
   is a coefficient of `a_j` (resp. `a_{d/2k+j}`); all other summands of `psi` vanish at
   `p`.

4. *Conclude with the balanced-representative triangle inequality.*
   `ZMod.natAbs_valMinAbs_add_le` and `ZMod.natAbs_valMinAbs_neg` (both in Mathlib) give
   `|±c₁ ± c₂|± ≤ |c₁|± + |c₂|± ≤ β + β`, using `ha` at the witnessed positions of step 1.

## Available ingredients (all proven)

- `fixedBasisMap_injective`, `card_fixedSubring_eq` (`Subfield/Cardinality.lean`) —
  surjectivity of the `vElt` expansion comes for free from the cardinality match.
- `vElt_coe`, `vElt_coeff`, `conjAut_Xpow`, `Xpow_fold`, `mk_monomial_fold`,
  `Xpow_coeff_eq_zero_of_ne`, `mk_monomial_coeff_lt` (`Subfield/Basis.lean`) — the monomial
  folding toolkit; step 1's full formula is an extension of `vElt_coeff` by the same cases.
- `ZMod.natAbs_valMinAbs_add_le`, `ZMod.natAbs_valMinAbs_neg` (Mathlib) — the `mod± q`
  triangle inequality and sign invariance. -/
theorem cInfNorm_psi_le (α κ : ℕ) (h2 : (2 : ZMod q) ≠ 0) (hk : 2 * 2 ^ κ ∣ 2 ^ α) {β : ℕ}
    (a : Fin (2 ^ α / 2 ^ κ) → fixedSubring (R := ZMod q) α (2 ^ κ))
    (ha : (zmodCenteredView q).vecCInfNorm
      (fun i => ((a i : Rq (powTwoCyclotomic (R := ZMod q) α))).1) ≤ β) :
    (zmodCenteredView q).cInfNorm (psi α (2 ^ κ) a).1 ≤ 2 * β := by
  sorry

end ArkLib.Lattices.CyclotomicModulus
