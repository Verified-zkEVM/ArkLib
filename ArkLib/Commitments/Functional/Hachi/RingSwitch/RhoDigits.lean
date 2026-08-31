/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.Gadget.Norms
import ArkLib.ToCompPoly.Univariate.Basic
import ArkLib.ProofSystem.RingSwitching.Transport.Eval

/-!
# The hidden gadget decomposition of the lift quotient

[NOZ26] §4.3 (p. 19) commits to `(z, r₁, …, r_δ)` rather than to `(z, r)`: the ring-switching
quotient is split into `δ = clog_b q` **balanced** base-`b` digits with `‖r_u‖∞ ≤ ⌊b/2⌋`, after
which the digit subscript is dropped from all later notation ("there is a hidden gadget
decomposition of `r`"). This file supplies that encoding at the Hachi boundary, where Figure 4's
generic `Lift` layer hands over the raw pair `(z, ρ)`.

**Why it is load-bearing.** The only unconditional bound on a raw Hachi quotient is `q/2`
(`rhoShort_half`, `QuotientNorms.lean`) — sharp, because the `R^lin` matrix carries the Ajtai key
blocks. Range-checking a raw quotient at a single base therefore forces the zero-check base up to
`q/2 + 1`, which pins `γ = q/2 = bZero − 1` and makes both the Eq. (20) ball check and the
Module-SIS escape target vacuous. Committing the *digits* instead makes the quotient block of the
committed vector short **by construction**, at radius `⌊b/2⌋ = O(b)`, which is what leaves
`LiftCom.Collision` a genuine Module-SIS instance.

The decomposition reuses the coefficient-level machinery already built for the `z` side
(`balancedZmodDigitDecomposition`, `Gadget/Core.lean`; the bounds in `Gadget/Norms.lean`); the only
new data is its proof-free repackaging `balancedDigit` and the polynomial-level lift `rhoDigits`.

## Main definitions

* `balancedDigit`: the balanced base-`b` digit map on `ZMod q`, as a plain function — the `digit`
  field of `balancedZmodDigitDecomposition` with its two proof arguments erased
  (`balancedDigit_eq_digit`, by `rfl`). Definitions downstream of it stay hypothesis-free.
* `rhoDigits`: digit `u` of a quotient row, coefficient-wise, truncated at the ring dimension.

## Main results

* `rhoDigits_reconstruct`: `ρ = ∑_u b^u · rhoDigits ρ u` — the reconstruction identity the
  recombined `H_α` table is proved against.
* `rhoDigits_evalAt`: its `evalAt` corollary, the form the Eq. (22) row defect consumes.
* `rhoDigits_valMinAbs_natAbs_le`: every digit coefficient is `⌊b/2⌋`-bounded, for an **arbitrary**
  quotient — the honest-prover norm obligation, discharged unconditionally.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus
open RingSwitching

namespace ArkLib.Lattices.Ajtai.InnerOuter

section BalancedDigit

variable {q : ℕ} [NeZero q]

/-! ## The digit count -/

/-- The number of base-`b` digits the quotient is split into: `δ = ⌈log_b q⌉`, the same convention
`zDigits` uses for the message side (`Nat.clog`). `Nat.le_pow_clog` is exactly the
`q ≤ b ^ δ` hypothesis the balanced decomposition needs. -/
abbrev rhoDigitCount (q b : ℕ) : ℕ := Nat.clog b q

/-! ## The balanced digit map, proof-free -/

/-- The balanced base-`b` digit map on `ZMod q`, as a plain function of `b`, the digit count, the
coefficient and the digit index.

This is definitionally the `digit` field of `balancedZmodDigitDecomposition`
(`balancedDigit_eq_digit`, `rfl`): that field never mentions the structure's `hb`/`hq` arguments,
which are consumed only by `reconstruct`. Erasing them here is what lets `rhoDigits` — and hence
`liftMessage`, `liftShort` and the `w̃` table — be stated without dragging `1 < b` and `q ≤ b ^ δ`
through every downstream signature; the two hypotheses reappear exactly where they are needed, on
the reconstruction lemma. -/
def balancedDigit (b digits : ℕ) (c : ZMod q) (e : ℕ) : ZMod q :=
  (((Nat.digits b (c + balancedShift b digits).val).getD e 0 : ℕ) : ZMod q)
    - ((b / 2 : ℕ) : ZMod q)

/-- `balancedDigit` is the bundled decomposition's digit map. Holds by `rfl`, which is the point:
every bound proved about `balancedZmodDigitDecomposition` in `Gadget/Norms.lean` transfers to
`balancedDigit` for free. -/
theorem balancedDigit_eq_digit {b digits : ℕ} (hb : 1 < b) (hq : q ≤ b ^ digits) (c : ZMod q)
    (e : Fin digits) :
    balancedDigit b digits c (e : ℕ)
      = (balancedZmodDigitDecomposition b digits hb hq).digit c e := rfl

/-- **Coefficient-level reconstruction**: the `δ` balanced digits of a residue recombine to it
under the public weights `b^u`. Inherited from `DigitDecomposition.reconstruct`. -/
theorem balancedDigit_reconstruct {b digits : ℕ} (hb : 1 < b) (hq : q ≤ b ^ digits) (c : ZMod q) :
    ∑ e : Fin digits, (b : ZMod q) ^ (e : ℕ) * balancedDigit b digits c (e : ℕ) = c :=
  (balancedZmodDigitDecomposition b digits hb hq).reconstruct c

/-- **Core per-digit bound**, ball form: every balanced digit is `⌊b/2⌋`-bounded as a centered
residue — for *every* input, with no shortness hypothesis on `c`. This is what makes the digit
encoding unconditional where `rhoShort_half` was forced up to `q/2`. -/
theorem balancedDigit_valMinAbs_natAbs_le {b digits : ℕ} (hb : 1 < b) (hq : q ≤ b ^ digits)
    (hbq : b ≤ q / 2) (c : ZMod q) {e : ℕ} (he : e < digits) :
    (balancedDigit b digits c e).valMinAbs.natAbs ≤ b / 2 := by
  rw [show e = ((⟨e, he⟩ : Fin digits) : ℕ) from rfl, balancedDigit_eq_digit hb hq]
  exact balancedZmodDigit_natAbs_le hb hq hbq c _

/-- **Core per-digit bound**, two-sided box form: every balanced digit lies in the paper's box
`S_b = [−⌊b/2⌋, ⌈b/2⌉−1]` ([NOZ26] §2.1), which is the interval Eq. (20)'s range check tests. -/
theorem balancedDigit_valMinAbs_mem {b digits : ℕ} (hb : 1 < b) (hq : q ≤ b ^ digits)
    (hbq : b ≤ q / 2) (c : ZMod q) {e : ℕ} (he : e < digits) :
    -((b / 2 : ℕ) : ℤ) ≤ (balancedDigit b digits c e).valMinAbs ∧
      (balancedDigit b digits c e).valMinAbs ≤ (((b + 1) / 2 : ℕ) : ℤ) - 1 := by
  rw [show e = ((⟨e, he⟩ : Fin digits) : ℕ) from rfl, balancedDigit_eq_digit hb hq]
  exact balancedZmodDigit_valMinAbs_mem hb hq hbq c _

end BalancedDigit

/-! ## The quotient digits -/

section RhoDigits

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q))


/-- **Digit `u` of a quotient row**: apply `balancedDigit` to every coefficient below the ring
dimension `d = deg φ`, and truncate there.

Truncation is lossless: `LiftedWitness.hρ` bounds every quotient row by `natDegree ≤ d − 1`, so
the discarded coefficients are already zero (`rhoDigits_reconstruct` takes exactly that
hypothesis). Truncating rather than tracking the row's own degree keeps every digit a `d`-wide
block, which is what makes the widened `w̃` table a uniform `(μ + n·δ)·d` grid and the Ajtai key
width `μ + n·δ` a constant of the wire format.

Computable: `CPolynomial.ofFinCoeff` is a finite sum of monomials over coefficient arrays. -/
def rhoDigits (b : ℕ) (ρ : CPolynomial (ZMod q)) (u : ℕ) : CPolynomial (ZMod q) :=
  CPolynomial.ofFinCoeff Φ.φ.natDegree fun k => balancedDigit b (rhoDigitCount q b) (ρ.coeff k) u

omit [NeZero q] in
/-- Coefficients of a quotient digit: the corresponding digit of the corresponding coefficient,
below the ring dimension, and zero above it. -/
@[simp] theorem rhoDigits_coeff (b : ℕ) (ρ : CPolynomial (ZMod q)) (u k : ℕ) :
    (rhoDigits Φ b ρ u).coeff k
      = if k < Φ.φ.natDegree then balancedDigit b (rhoDigitCount q b) (ρ.coeff k) u else 0 := by
  rw [rhoDigits, CPolynomial.coeff_ofFinCoeff]

omit [NeZero q] in
/-- Quotient digits are `d`-wide blocks: `natDegree ≤ d − 1`, the same degree bound
`LiftedWitness.hρ` imposes on the rows they decompose. So a digit is a legitimate quotient-shaped
object, and `Rq.ofFinCoeff` reads it back into `Rq Φ` losslessly. -/
theorem rhoDigits_natDegree_le (b : ℕ) (ρ : CPolynomial (ZMod q)) (u : ℕ) :
    (rhoDigits Φ b ρ u).toPoly.natDegree ≤ Φ.φ.natDegree - 1 := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun k hk => ?_
  rw [← CPolynomial.coeff_toPoly, rhoDigits_coeff, if_neg (by omega)]

omit [NeZero q] in
/-- Every digit coefficient of every quotient row is `⌊b/2⌋`-bounded, unconditionally.

This is the honest prover's per-digit norm obligation, and it holds for an **arbitrary** `ρ` — no
shortness hypothesis on the quotient, no assumption that the commitment key is short. It is the
whole point of the encoding: the quotient block of the committed vector is short by construction,
where the raw block was only `q/2`-bounded (`rhoShort_half`). -/
theorem rhoDigits_valMinAbs_natAbs_le {b : ℕ} (hb : 1 < b) (hbq : b ≤ q / 2)
    (ρ : CPolynomial (ZMod q)) {u : ℕ} (hu : u < rhoDigitCount q b) (k : ℕ) :
    ((rhoDigits Φ b ρ u).coeff k).valMinAbs.natAbs ≤ b / 2 := by
  rw [rhoDigits_coeff]
  split
  · exact balancedDigit_valMinAbs_natAbs_le hb (Nat.le_pow_clog hb q) hbq _ hu
  · simp

omit [NeZero q] in
/-- **The reconstruction identity** ([NOZ26] §4.3): a quotient row is recovered from its digits
under the public weights `b^u`. The degree hypothesis is `LiftedWitness.hρ`, so it is available
wherever the lifted witness is.

Stated on `toPoly` because that is the representation the Eq. (22) row defect evaluates
(`rhoDigits_evalAt`); the `CPolynomial` values themselves are equal too, but nothing downstream
needs that. -/
theorem rhoDigits_reconstruct {b : ℕ} (hb : 1 < b) (hd : 0 < Φ.φ.natDegree)
    (ρ : CPolynomial (ZMod q)) (hρ : ρ.toPoly.natDegree ≤ Φ.φ.natDegree - 1) :
    ρ.toPoly = ∑ u : Fin (rhoDigitCount q b),
      Polynomial.C ((b : ZMod q) ^ (u : ℕ)) * (rhoDigits Φ b ρ (u : ℕ)).toPoly := by
  ext k
  have hcoe : ∀ u : ℕ, (rhoDigits Φ b ρ u).toPoly.coeff k
      = if k < Φ.φ.natDegree then balancedDigit b (rhoDigitCount q b) (ρ.coeff k) u else 0 :=
    fun u => by rw [← CPolynomial.coeff_toPoly, rhoDigits_coeff]
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, hcoe]
  by_cases hk : k < Φ.φ.natDegree
  · simp only [if_pos hk]
    rw [balancedDigit_reconstruct hb (Nat.le_pow_clog hb q) (ρ.coeff k),
      ← CPolynomial.coeff_toPoly]
  · simp only [if_neg hk, mul_zero, Finset.sum_const_zero]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

omit [NeZero q] in
/-- **The reconstruction identity through `evalAt`**: the form Eq. (22)'s row defect consumes.
The quotient term `evalAt α ρ` becomes the public-weighted digit sum
`∑_u φF(b^u) · evalAt α (rhoDigits ρ u)`, which is the paper's `M̃_α(i, u) = −(α^d + 1)·b^u` on
digit columns. -/
theorem rhoDigits_evalAt {F : Type} [Field F] (φF : ZMod q →+* F) (α : F) {b : ℕ} (hb : 1 < b)
    (hd : 0 < Φ.φ.natDegree) (ρ : CPolynomial (ZMod q))
    (hρ : ρ.toPoly.natDegree ≤ Φ.φ.natDegree - 1) :
    evalAt φF α ρ.toPoly = ∑ u : Fin (rhoDigitCount q b),
      φF ((b : ZMod q) ^ (u : ℕ)) * evalAt φF α (rhoDigits Φ b ρ (u : ℕ)).toPoly := by
  have hC : ∀ c : ZMod q, evalAt φF α (Polynomial.C c) = φF c := fun c =>
    Polynomial.eval₂_C _ _
  rw [rhoDigits_reconstruct Φ hb hd ρ hρ, map_sum]
  exact Finset.sum_congr rfl fun u _ => by rw [map_mul, hC]

end RhoDigits

end ArkLib.Lattices.Ajtai.InnerOuter
