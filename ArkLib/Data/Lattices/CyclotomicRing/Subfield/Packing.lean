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

/-- **Packing exponents stay in range**: for `2·2^κ ∣ 2^α`, every packed exponent
`packExp α (2^κ) j` lands below the ring dimension `d = 2^α`, for `j` ranging over the packed
index set `Fin (d/2^κ)`. -/
theorem packExp_lt (α κ : ℕ) (hk : 2 * 2 ^ κ ∣ 2 ^ α) (j : Fin (2 ^ α / 2 ^ κ)) :
    packExp α (2 ^ κ) (j : ℕ) < 2 ^ α := by
  have hκ : κ + 1 ≤ α := succ_le_of_two_mul_two_pow_dvd hk
  have hMle : 2 ^ (α - κ - 1) ≤ 2 ^ (α - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hd2 : (2 : ℕ) ^ α = 2 * 2 ^ (α - 1) := by rw [← pow_succ']; congr 1; omega
  have hN : 2 ^ α / 2 ^ κ = 2 * 2 ^ (α - κ - 1) := by
    have hfac : (2 : ℕ) ^ κ * (2 * 2 ^ (α - κ - 1)) = 2 ^ α := by
      rw [← Nat.mul_assoc, show (2 : ℕ) ^ κ * 2 = 2 ^ (κ + 1) from by rw [pow_succ], ← pow_add]
      congr 1; omega
    rw [← hfac, Nat.mul_div_cancel_left _ (by positivity : 0 < 2 ^ κ)]
  have hMM : 2 ^ α / (2 * 2 ^ κ) = 2 ^ (α - κ - 1) := by
    rw [show 2 * 2 ^ κ = 2 ^ (κ + 1) from by rw [pow_succ]; ring,
      Nat.pow_div (by omega) (by norm_num), show α - (κ + 1) = α - κ - 1 from by omega]
  have hj : (j : ℕ) < 2 * 2 ^ (α - κ - 1) := hN ▸ j.isLt
  unfold packExp; rw [hMM]; split_ifs with h <;> omega

/-- **Alignment of the second half after the `X^{d/2}` shift**: `packExp α (2^κ) j` is congruent
to `j` modulo `d/2k = 2^{α-κ-1}`, on both halves of the index range. On the first half this is
`rfl` (no shift); on the second half the shift `2^{α-1} = 2^κ·2^{α-κ-1}` is a multiple of
`2^{α-κ-1}`, so it vanishes mod `2^{α-κ-1}`. This is what lets a single output coefficient
position see contributions from a first-half and a second-half packed index alike. -/
theorem packExp_mod_eq (α κ : ℕ) (hk : 2 * 2 ^ κ ∣ 2 ^ α) (j : Fin (2 ^ α / 2 ^ κ)) :
    packExp α (2 ^ κ) (j : ℕ) % 2 ^ (α - κ - 1) = (j : ℕ) % 2 ^ (α - κ - 1) := by
  have hκ : κ + 1 ≤ α := succ_le_of_two_mul_two_pow_dvd hk
  have hH : (2 : ℕ) ^ (α - 1) = 2 ^ κ * 2 ^ (α - κ - 1) := by rw [← pow_add]; congr 1; omega
  have hN : 2 ^ α / 2 ^ κ = 2 * 2 ^ (α - κ - 1) := by
    have hfac : (2 : ℕ) ^ κ * (2 * 2 ^ (α - κ - 1)) = 2 ^ α := by
      rw [← Nat.mul_assoc, show (2 : ℕ) ^ κ * 2 = 2 ^ (κ + 1) from by rw [pow_succ], ← pow_add]
      congr 1; omega
    rw [← hfac, Nat.mul_div_cancel_left _ (by positivity : 0 < 2 ^ κ)]
  have hMM : 2 ^ α / (2 * 2 ^ κ) = 2 ^ (α - κ - 1) := by
    rw [show 2 * 2 ^ κ = 2 ^ (κ + 1) from by rw [pow_succ]; ring,
      Nat.pow_div (by omega) (by norm_num), show α - (κ + 1) = α - κ - 1 from by omega]
  have hj : (j : ℕ) < 2 * 2 ^ (α - κ - 1) := hN ▸ j.isLt
  unfold packExp; rw [hMM]
  split_ifs with h
  · rfl
  · rw [hH, Nat.add_comm (2 ^ κ * 2 ^ (α - κ - 1)) _, Nat.add_mul_mod_self_right,
      ← Nat.mod_eq_sub_mod (by omega : 2 ^ (α - κ - 1) ≤ (j : ℕ))]

/-- **At most two packed indices share a residue class mod `d/2k`.** Given a residue
`r` with `j ≡ r (mod d/2k = 2^{α-κ-1})`, the index `j : Fin (d/2^κ)` is either the first-half
witness (value `r`) or the second-half witness (value `d/2k + r`). Combined with
`packExp_mod_eq`, this pins down exactly which (at most two) packed summands can contribute to a
given output coefficient position. -/
theorem eq_or_eq_of_mod_eq (α κ : ℕ) (hk : 2 * 2 ^ κ ∣ 2 ^ α) {r : ℕ}
    (j : Fin (2 ^ α / 2 ^ κ)) (heq : (j : ℕ) % 2 ^ (α - κ - 1) = r) :
    (j : ℕ) = r ∨ (j : ℕ) = 2 ^ (α - κ - 1) + r := by
  have hκ : κ + 1 ≤ α := succ_le_of_two_mul_two_pow_dvd hk
  have hN : 2 ^ α / 2 ^ κ = 2 * 2 ^ (α - κ - 1) := by
    have hfac : (2 : ℕ) ^ κ * (2 * 2 ^ (α - κ - 1)) = 2 ^ α := by
      rw [← Nat.mul_assoc, show (2 : ℕ) ^ κ * 2 = 2 ^ (κ + 1) from by rw [pow_succ], ← pow_add]
      congr 1; omega
    rw [← hfac, Nat.mul_div_cancel_left _ (by positivity : 0 < 2 ^ κ)]
  have hjlt : (j : ℕ) < 2 * 2 ^ (α - κ - 1) := hN ▸ j.isLt
  rcases lt_or_ge (j : ℕ) (2 ^ (α - κ - 1)) with hjl | hjg
  · left; rw [Nat.mod_eq_of_lt hjl] at heq; omega
  · right
    have hjm : (j : ℕ) % 2 ^ (α - κ - 1) = (j : ℕ) - 2 ^ (α - κ - 1) := by
      rw [Nat.mod_eq_sub_mod hjg, Nat.mod_eq_of_lt (by omega)]
    rw [hjm] at heq; omega

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
