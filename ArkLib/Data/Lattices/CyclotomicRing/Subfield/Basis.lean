/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Galois.FixedSubring

/-!
# Monomials and the `Z_q`-Basis of the Fixed Subring `R_q^H` (Hachi §3, Eq. 7)

This file collects the monomial-level facts about `R_q = Z_q[X] / (X^{2^α} + 1)` that the
`Subfield/` layer is built on.

* `Xpow Φ i` — the reduced element `X^i ∈ Rq Φ` (the monomial with coefficient `1`).
* `galoisAut_Xpow` — the Galois automorphism on a monomial: `σ_m (X^i) = X^{i·m}` (reduced).
  This is the workhorse for the trace-of-monomial computation in `TraceInnerProduct.lean`.

## Coefficient structure and cardinality (Eq. 7)

The symmetric basis `vElt j = X^{(d/2k)·j} + σ_{-1}(X^{(d/2k)·j})` (`j < k`) realizes the **Eq. 7**
characterization of `R_q^H`: `vElt_coeff` gives the triangular coefficient formula
`(v_j).coeff((d/2k)·s) = [s=j]·(2 if j=0 else 1)`, from which (over `R = ZMod q`) the `ℤ_q`-linear
injection `(ZMod q)^k ↪ R_q^H` and the cardinality `|R_q^H| = q^k` follow (see
`Subfield/TraceInnerProduct.lean`, `fixedBasisMap_injective`/`card_fixedSubring_eq`). The
`Fintype` instance on `Rq Φ` (`Rq.fintypePowTwo`, reduced representatives biject with
`Fin (2^α) → R`) and `|R_q| = q^{2^α}` (`Rq.card_powTwo`) are established below.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi …*][NOZ26]
-/

open Polynomial CompPoly CompPoly.CPolynomial Finset

namespace ArkLib.Lattices.CyclotomicModulus

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R] [DecidableEq R]

/-! ## The monomial `X^i` as a reduced element -/

/-- The reduced element `X^i ∈ Rq Φ`: the monomial `X^i` with coefficient `1`, reduced modulo the
cyclotomic modulus. For `i < d` this is just `monomial i 1`; for `i ≥ d` the reduction folds it
back (with a sign) into degree `< d`. -/
def Xpow (Φ : CyclotomicModulus R) [IsCyclotomic Φ] (i : ℕ) : Rq Φ :=
  Rq.mk Φ (CompPoly.CPolynomial.monomial i 1)

/-- For `i < 2^α` (below the modulus degree), `X^i` is already reduced, so its `j`-th coefficient
is the Kronecker delta `[j = i]`. -/
theorem Xpow_coeff_of_lt (α : ℕ) {i : ℕ} (hi : i < 2 ^ α) (j : ℕ) :
    (Xpow (powTwoCyclotomic (R := R) α) i).1.coeff j = if j = i then (1 : R) else 0 := by
  have h2 : (0 : ℕ) < 2 ^ α := pow_pos (by norm_num) α
  have hself : (powTwoCyclotomic (R := R) α).reduce (CompPoly.CPolynomial.monomial i 1)
      = CompPoly.CPolynomial.monomial i 1 := by
    refine CyclotomicModulus.reduce_eq_self_of_degree_lt _ ?_
    rw [toPoly_monomial, Polynomial.degree_monomial i (one_ne_zero), powTwoCyclotomic_toPoly,
      ← Polynomial.C_1, Polynomial.degree_X_pow_add_C h2 (1 : R)]
    exact_mod_cast hi
  change ((powTwoCyclotomic (R := R) α).reduce (CompPoly.CPolynomial.monomial i 1)).coeff j = _
  rw [hself, CPolynomial.coeff_monomial]

/-! ## The Galois automorphism on a monomial -/

/-- **`σ_m (X^i) = X^{i·m}`** (reduced). For `i < 2^α` the monomial-remap defining `galoisAut`
collapses to the single surviving term. This is the key input to the trace-of-monomial
computation in `TraceInnerProduct.lean`. -/
theorem galoisAut_Xpow (α m : ℕ) {i : ℕ} (hi : i < 2 ^ α) :
    galoisAut (powTwoCyclotomic (R := R) α) m (Xpow (powTwoCyclotomic (R := R) α) i)
      = Xpow (powTwoCyclotomic (R := R) α) (i * m) := by
  have hi' : i < (powTwoCyclotomic (R := R) α).φ.natDegree := by
    rwa [powTwoCyclotomic_natDegree]
  have key : (∑ kk ∈ range (powTwoCyclotomic (R := R) α).φ.natDegree,
      CompPoly.CPolynomial.monomial (kk * m) ((Xpow (powTwoCyclotomic α) i).1.coeff kk))
      = CompPoly.CPolynomial.monomial (i * m) (1 : R) := by
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr hi')
        (fun kk _ hkk => by
          rw [Xpow_coeff_of_lt α hi, if_neg hkk, CPolynomial.monomial_eq_zero (R := R)]),
      Xpow_coeff_of_lt α hi, if_pos rfl]
  rw [galoisAut, key, Xpow]

/-! ## Algebraic toolkit for `X^n`: folding via `X^d = -1`

`Xpow Φ n` is a genuine ring power (`Xpow Φ n = (Xpow Φ 1)^n` semantically), so the
reduction-mod-`X^d+1` of high-degree monomials is governed by the single algebraic relation
`X^{2^α} = -1`, proven through the injective quotient. No `modByMonic` coefficient formula is
needed. The folding lemma `Xpow_fold` (`X^n = (-1)^{n/d}·X^{n mod d}`) underlies both the
coefficient-permutation action of `σ_m` and the sign-pairing for the trace-of-monomial vanishing
(Hachi [NOZ26, §3, Claim 2]). -/

/-- `X^n` lifts to the class of `X^n` in the semantic quotient. -/
theorem Xpow_toQuotient (Φ : CyclotomicModulus R) [IsCyclotomic Φ] (n : ℕ) :
    (Xpow Φ n).toQuotient = Ideal.Quotient.mk Φ.modIdeal (Polynomial.X ^ n) := by
  rw [Xpow, Rq.toQuotient_mk, quotientHom_apply, toPoly_monomial,
    ← Polynomial.X_pow_eq_monomial]

/-- `X^{a+b} = X^a · X^b`. -/
theorem Xpow_add (Φ : CyclotomicModulus R) [IsCyclotomic Φ] (a b : ℕ) :
    Xpow Φ (a + b) = Xpow Φ a * Xpow Φ b := by
  apply Rq.toQuotient_injective Φ
  have hmul : (Xpow Φ a * Xpow Φ b).toQuotient
      = (Xpow Φ a).toQuotient * (Xpow Φ b).toQuotient :=
    map_mul (Rq.toQuotientHom Φ) _ _
  rw [hmul]
  simp only [Xpow_toQuotient]
  rw [← map_mul, ← pow_add]

/-- `X^{a·t} = (X^a)^t`. -/
theorem Xpow_mul (Φ : CyclotomicModulus R) [IsCyclotomic Φ] (a t : ℕ) :
    Xpow Φ (a * t) = (Xpow Φ a) ^ t := by
  apply Rq.toQuotient_injective Φ
  have hpow : ((Xpow Φ a) ^ t).toQuotient = ((Xpow Φ a).toQuotient) ^ t :=
    map_pow (Rq.toQuotientHom Φ) _ _
  rw [hpow]
  simp only [Xpow_toQuotient]
  rw [← map_pow, ← pow_mul]

/-- **The key relation `X^{2^α} = -1`** (`X^d = -1`), proven via the quotient: `X^d + 1` is the
modulus, so it vanishes in the quotient. -/
theorem Xpow_natDegree (α : ℕ) : Xpow (powTwoCyclotomic (R := R) α) (2 ^ α) = -1 := by
  apply Rq.toQuotient_injective (powTwoCyclotomic α)
  have hmem : (Polynomial.X ^ 2 ^ α + 1 : Polynomial R)
      ∈ (powTwoCyclotomic (R := R) α).modIdeal := by
    rw [modIdeal, powTwoCyclotomic_toPoly]; exact Ideal.mem_span_singleton_self _
  have hzero : Ideal.Quotient.mk (powTwoCyclotomic (R := R) α).modIdeal
      (Polynomial.X ^ 2 ^ α + 1) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [map_add, map_one] at hzero
  have hneg : Rq.toQuotient (powTwoCyclotomic (R := R) α) (-1) = -1 := by
    have h := map_neg (Rq.toQuotientHom (powTwoCyclotomic (R := R) α)) 1
    rw [map_one] at h
    exact h
  rw [Xpow_toQuotient, hneg]
  exact eq_neg_of_add_eq_zero_left hzero

/-- **Folding**: `X^n = (-1)^{n/2^α} · X^{n mod 2^α}` (the reduction mod `X^d+1` of a high-degree
monomial, expressed as a sign times a genuine monomial of degree `< d`). -/
theorem Xpow_fold (α n : ℕ) :
    Xpow (powTwoCyclotomic (R := R) α) n
      = (-1) ^ (n / 2 ^ α) * Xpow (powTwoCyclotomic (R := R) α) (n % 2 ^ α) := by
  conv_lhs => rw [← Nat.div_add_mod n (2 ^ α)]
  rw [Xpow_add, Xpow_mul, Xpow_natDegree]

/-! ## The coefficient action of `σ_m` -/

/-- The scaled monomial `c·X^j ∈ Rq Φ` factors as `(constant c)·X^j`. -/
theorem mk_monomial_eq (Φ : CyclotomicModulus R) [IsCyclotomic Φ] (j : ℕ) (c : R) :
    Rq.mk Φ (CompPoly.CPolynomial.monomial j c)
      = Rq.mk Φ (CompPoly.CPolynomial.C c) * Xpow Φ j := by
  apply Rq.toQuotient_injective Φ
  have hmul : (Rq.mk Φ (CompPoly.CPolynomial.C c) * Xpow Φ j).toQuotient
      = (Rq.mk Φ (CompPoly.CPolynomial.C c)).toQuotient * (Xpow Φ j).toQuotient :=
    map_mul (Rq.toQuotientHom Φ) _ _
  rw [hmul, Rq.toQuotient_mk, quotientHom_apply, Xpow_toQuotient, Rq.toQuotient_mk,
    quotientHom_apply, toPoly_monomial, toPoly_C, ← map_mul, Polynomial.C_mul_X_pow_eq_monomial]

/-- **Monomial folding in `Rq`**: `c·X^j = (-1)^{j/d}·(c·X^{j mod d})`. The reduction of a
high-degree scaled monomial is a sign times a genuine (degree `< d`) scaled monomial. -/
theorem mk_monomial_fold (α j : ℕ) (c : R) :
    Rq.mk (powTwoCyclotomic (R := R) α) (CompPoly.CPolynomial.monomial j c)
      = (-1) ^ (j / 2 ^ α)
        * Rq.mk (powTwoCyclotomic (R := R) α) (CompPoly.CPolynomial.monomial (j % 2 ^ α) c) := by
  rw [mk_monomial_eq, mk_monomial_eq, Xpow_fold]
  ring

/-- **`σ_m` as a monomial sum (the coefficient action)**: the Galois automorphism sends the
monomial decomposition `x = Σ_{k<d} x_k X^k` to `Σ_{k<d} x_k X^{k·m}`. Combined with
`mk_monomial_fold` (each `X^{k·m}` folds to `±X^{(k·m) mod d}`), this expresses `σ_m` as the
signed coefficient permutation underlying the Eq. 7 fixed-subring analysis. -/
theorem galoisAut_eq_sum (Φ : CyclotomicModulus R) [IsCyclotomic Φ] (m : ℕ) (x : Rq Φ) :
    galoisAut Φ m x
      = ∑ k ∈ range Φ.φ.natDegree,
          Rq.mk Φ (CompPoly.CPolynomial.monomial (k * m) (x.1.coeff k)) := by
  unfold galoisAut
  rw [Rq.mk_sum]

/-- **`σ_m (X^j) = X^{j·m}` for any exponent `j`** (`m` odd, so `σ_m` is a genuine automorphism).
Unlike `galoisAut_Xpow`, no `j < d` bound: routes through the semantic side, where `σ_m` is
`aeval (X^m)` and `X^j ↦ (X^m)^j = X^{jm}`. -/
theorem galoisAut_Xpow' (α m j : ℕ) (hm : Odd m) :
    galoisAut (powTwoCyclotomic (R := R) α) m (Xpow (powTwoCyclotomic (R := R) α) j)
      = Xpow (powTwoCyclotomic (R := R) α) (j * m) := by
  apply Rq.toQuotient_injective (powTwoCyclotomic α)
  rw [galoisAut_toQuotient α m hm, Xpow_toQuotient, galoisAutₛ_mk, Xpow_toQuotient,
    map_pow, Polynomial.aeval_X, ← pow_mul, Nat.mul_comm]

/-- `X^{2^{α+1}} = 1` (the conductor `2d = 2^{α+1}` is the order of `X`): `X^{2d} = (X^d)^2 = 1`. -/
theorem Xpow_conductor (α : ℕ) : Xpow (powTwoCyclotomic (R := R) α) (2 ^ (α + 1)) = 1 := by
  rw [pow_succ, Xpow_mul, Xpow_natDegree, neg_one_sq]

/-- **Conductor periodicity**: `X^n = X^{n mod 2^{α+1}}` (no sign — `X` has order `2d`). -/
theorem Xpow_periodic (α n : ℕ) :
    Xpow (powTwoCyclotomic (R := R) α) n
      = Xpow (powTwoCyclotomic (R := R) α) (n % 2 ^ (α + 1)) := by
  conv_lhs => rw [← Nat.div_add_mod n (2 ^ (α + 1))]
  rw [Xpow_add, Xpow_mul, Xpow_conductor, one_pow, _root_.one_mul]

/-- `X^a = X^b` whenever `a ≡ b (mod 2^{α+1})`. -/
theorem Xpow_congr_mod (α : ℕ) {a b : ℕ} (h : a % 2 ^ (α + 1) = b % 2 ^ (α + 1)) :
    Xpow (powTwoCyclotomic (R := R) α) a = Xpow (powTwoCyclotomic (R := R) α) b := by
  rw [Xpow_periodic α a, Xpow_periodic α b, h]

/-- **Conjugation negates a square-root-of-`-1` monomial**: if `X^{2j} = -1` then
`σ_{-1}(X^j) = X^{j·conjExp} = -X^j`. The exponent `j·conjExp ≡ -j`, so `X^{j·conjExp}` is the
inverse of `X^j`; and `X^j·(-X^j) = -(X^j)² = -X^{2j} = 1`, so the inverse is `-X^j`. -/
theorem Xpow_mul_conjExp (α j : ℕ)
    (hsq : Xpow (powTwoCyclotomic (R := R) α) (2 * j) = -1) :
    Xpow (powTwoCyclotomic (R := R) α) (j * conjExp α)
      = -Xpow (powTwoCyclotomic (R := R) α) j := by
  have hsum : j * conjExp α + j = 2 ^ (α + 1) * j := by
    have hc : conjExp α + 1 = 2 ^ (α + 1) := by
      have h1 : 1 ≤ 2 ^ (α + 1) := Nat.one_le_two_pow
      rw [conjExp]; omega
    calc j * conjExp α + j = j * (conjExp α + 1) := by ring
      _ = j * 2 ^ (α + 1) := by rw [hc]
      _ = 2 ^ (α + 1) * j := by ring
  have hinv : Xpow (powTwoCyclotomic (R := R) α) (j * conjExp α)
      * Xpow (powTwoCyclotomic (R := R) α) j = 1 := by
    rw [← Xpow_add, hsum, Xpow_mul, Xpow_conductor, one_pow]
  have hjj : Xpow (powTwoCyclotomic (R := R) α) j * Xpow (powTwoCyclotomic (R := R) α) j = -1 := by
    rw [← pow_two, ← Xpow_mul, mul_comm j 2, hsq]
  linear_combination (-Xpow (powTwoCyclotomic (R := R) α) j) * hinv
    + Xpow (powTwoCyclotomic (R := R) α) (j * conjExp α) * hjj

/-! ## `X^c - 1` is a unit when `X^c ≠ 1` -/

omit [DecidableEq R] in
/-- `2` is a unit in `Rq Φ` when it is a unit in `R` (e.g. `R = ZMod q`, `q` odd). Transferred
from `R` through the algebra map into the semantic quotient and back across `equivQuotient`. -/
theorem isUnit_two (Φ : CyclotomicModulus R) [IsCyclotomic Φ] (h2 : (2 : R) ≠ 0) :
    IsUnit (2 : Rq Φ) := by
  have hR : IsUnit (2 : R) := isUnit_iff_ne_zero.mpr h2
  have hq : IsUnit (2 : Φ.CyclotomicRing) := by
    have h := hR.map (algebraMap R Φ.CyclotomicRing)
    rwa [map_ofNat] at h
  have h := hq.map (Rq.equivQuotient Φ).symm
  rwa [map_ofNat] at h

/-- **`X^c - 1` is a unit** whenever some `X^{c·2^t} = -1`. Then `(∑_{j<2^t} (X^c)^j)·(X^c - 1)
= (X^c)^{2^t} - 1 = -2`, a unit (`isUnit_two`), so `X^c - 1` is a unit. This is the crux of the
trace-of-monomial vanishing (Hachi [NOZ26, §3, Claim 2]): it makes the geometric sum collapse
without a domain. -/
theorem Xpow_sub_one_isUnit (α : ℕ) (h2 : (2 : R) ≠ 0) {c t : ℕ}
    (ht : Xpow (powTwoCyclotomic (R := R) α) (c * 2 ^ t) = -1) :
    IsUnit (Xpow (powTwoCyclotomic (R := R) α) c - 1) := by
  have hz : (Xpow (powTwoCyclotomic (R := R) α) c) ^ (2 ^ t) = -1 := by rw [← Xpow_mul]; exact ht
  have hmul : (∑ j ∈ range (2 ^ t), (Xpow (powTwoCyclotomic (R := R) α) c) ^ j)
      * (Xpow (powTwoCyclotomic (R := R) α) c - 1) = -2 := by
    rw [geom_sum_mul, hz]; ring
  have hu2 : IsUnit ((∑ j ∈ range (2 ^ t), (Xpow (powTwoCyclotomic (R := R) α) c) ^ j)
      * (Xpow (powTwoCyclotomic (R := R) α) c - 1)) := by
    rw [hmul]; exact (isUnit_two (powTwoCyclotomic α) h2).neg
  exact isUnit_of_mul_isUnit_right hu2

/-! ## `Rq` is finite over a finite base field -/

omit [DecidableEq R] in
/-- The modulus `X^{2^α}+1` has degree `2^α` (as a `Polynomial`). -/
theorem powTwoCyclotomic_toPoly_degree (α : ℕ) :
    (powTwoCyclotomic (R := R) α).φ.toPoly.degree = ((2 ^ α : ℕ) : WithBot ℕ) := by
  rw [powTwoCyclotomic_toPoly, ← Polynomial.C_1,
    Polynomial.degree_X_pow_add_C (by positivity) (1 : R)]

omit [DecidableEq R] in
/-- A reduced representative of `Rq (powTwoCyclotomic α)` has vanishing coefficients at and above
the modulus degree `2^α`. The power-of-two special case of `Rq.coeff_eq_zero_of_natDegree_le`. -/
theorem coeff_eq_zero_of_le (α : ℕ) (a : Rq (powTwoCyclotomic (R := R) α)) {k : ℕ}
    (hk : 2 ^ α ≤ k) : a.1.coeff k = 0 :=
  Rq.coeff_eq_zero_of_natDegree_le _ a (by rw [powTwoCyclotomic_natDegree]; exact hk)

/-- **`Rq` is in bijection with its coefficient vectors** `Fin (2^α) → R`: a reduced
representative is determined by its `2^α` low coefficients. -/
def Rq.powTwoCoeffEquiv (α : ℕ) :
    Rq (powTwoCyclotomic (R := R) α) ≃ (Fin (2 ^ α) → R) where
  toFun a i := a.1.coeff i.val
  invFun c := Rq.ofFinCoeff (powTwoCyclotomic α) (2 ^ α)
    (fun j => if h : j < 2 ^ α then c ⟨j, h⟩ else 0)
  left_inv a := by
    apply Subtype.ext
    apply CompPoly.CPolynomial.eq_iff_coeff.mpr
    intro k
    rw [Rq.ofFinCoeff_coeff _ _ (le_of_eq (powTwoCyclotomic_toPoly_degree α).symm)]
    by_cases hk : k < 2 ^ α
    · rw [if_pos hk, dif_pos hk]
    · rw [if_neg hk]; exact (coeff_eq_zero_of_le α a (Nat.not_lt.mp hk)).symm
  right_inv c := by
    funext i
    change (Rq.ofFinCoeff (powTwoCyclotomic α) (2 ^ α)
      (fun j => if h : j < 2 ^ α then c ⟨j, h⟩ else 0)).1.coeff i.val = c i
    rw [Rq.ofFinCoeff_coeff _ _ (le_of_eq (powTwoCyclotomic_toPoly_degree α).symm), if_pos i.isLt,
      dif_pos i.isLt]

noncomputable instance Rq.fintypePowTwo (α : ℕ) [Fintype R] :
    Fintype (Rq (powTwoCyclotomic (R := R) α)) :=
  Fintype.ofEquiv _ (Rq.powTwoCoeffEquiv α).symm

/-- **`|R_q| = q^{2^α}`** (here `q = |R|`). -/
theorem Rq.card_powTwo (α : ℕ) [Fintype R] :
    Fintype.card (Rq (powTwoCyclotomic (R := R) α)) = Fintype.card R ^ 2 ^ α := by
  rw [Fintype.card_congr (Rq.powTwoCoeffEquiv α), Fintype.card_fun, Fintype.card_fin]

/-- `R_q^H` is finite (a subtype of the finite `R_q`). -/
noncomputable instance fixedSubring.fintype (α k : ℕ) [Fintype R] :
    Fintype (fixedSubring (R := R) α k) :=
  Fintype.ofFinite _

/-! ## Explicit `H`-fixed elements `X^e + σ_{-1}(X^e)` -/

/-- `σ_{-1}(X^e) = X^{e·conjExp}`. -/
theorem conjAut_Xpow (α e : ℕ) :
    conjAut α (Xpow (powTwoCyclotomic (R := R) α) e)
      = Xpow (powTwoCyclotomic (R := R) α) (e * conjExp α) := by
  rw [conjAut, galoisRingHom_apply, galoisAut_Xpow' α (conjExp α) e (conjExp_odd α)]

/-- **`X^e + σ_{-1}(X^e) ∈ R_q^H`** when `d/2k ∣ e`: `X^e` is then `σ_{4k+1}`-fixed (its exponent
is a multiple of `d/2k`), and the sum is symmetric under `σ_{-1}` (which has order `2`). -/
theorem mem_fixed_symm (α κ : ℕ) (hκ : κ + 1 ≤ α) {e : ℕ} (hdvd : 2 ^ (α - κ - 1) ∣ e) :
    Xpow (powTwoCyclotomic (R := R) α) e + conjAut α (Xpow (powTwoCyclotomic α) e)
      ∈ fixedSubring α (2 ^ κ) := by
  have hgenX : ∀ f, genAut α (2 ^ κ) (Xpow (powTwoCyclotomic (R := R) α) f)
      = Xpow (powTwoCyclotomic α) (f * genExp (2 ^ κ)) := fun f => by
    rw [genAut, galoisRingHom_apply, galoisAut_Xpow' α (genExp (2 ^ κ)) f (genExp_odd (2 ^ κ))]
  have hpow : 4 * 2 ^ κ * 2 ^ (α - κ - 1) = 2 ^ (α + 1) := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, _root_.mul_assoc, ← pow_add, ← pow_add]; congr 1; omega
  have h4ke : (2 : ℕ) ^ (α + 1) ∣ 4 * 2 ^ κ * e := by
    obtain ⟨t, rfl⟩ := hdvd
    exact ⟨t, by rw [← _root_.mul_assoc, hpow]⟩
  have hconjsq : e * conjExp α * conjExp α ≡ e [MOD 2 ^ (α + 1)] := by
    have hcsq : conjExp α * conjExp α ≡ 1 [MOD 2 ^ (α + 1)] := by
      have hid : conjExp α * conjExp α = 2 ^ (α + 1) * (2 ^ (α + 1) - 2) + 1 := by
        have hM2 : 2 ≤ 2 ^ (α + 1) := by
          calc 2 = 2 ^ 1 := rfl
            _ ≤ 2 ^ (α + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hM2
        rw [conjExp, ht]
        simp only [show 2 + t - 1 = t + 1 from by omega, show 2 + t - 2 = t from by omega]; ring
      rw [Nat.ModEq, hid, Nat.mul_add_mod]
    calc e * conjExp α * conjExp α = e * (conjExp α * conjExp α) := by ring
      _ ≡ e * 1 [MOD 2 ^ (α + 1)] := Nat.ModEq.mul_left e hcsq
      _ = e := _root_.mul_one e
  have hgen : e * genExp (2 ^ κ) ≡ e [MOD 2 ^ (α + 1)] := by
    have he : e * genExp (2 ^ κ) = e + 4 * 2 ^ κ * e := by rw [genExp]; ring
    rw [he]
    calc e + 4 * 2 ^ κ * e ≡ e + 0 [MOD 2 ^ (α + 1)] :=
          Nat.ModEq.add_left e ((Nat.modEq_zero_iff_dvd).mpr h4ke)
      _ = e := Nat.add_zero e
  have hcgen : e * conjExp α * genExp (2 ^ κ) ≡ e * conjExp α [MOD 2 ^ (α + 1)] := by
    have he : e * conjExp α * genExp (2 ^ κ) = e * conjExp α + 4 * 2 ^ κ * e * conjExp α := by
      rw [genExp]; ring
    rw [he]
    calc e * conjExp α + 4 * 2 ^ κ * e * conjExp α ≡ e * conjExp α + 0 [MOD 2 ^ (α + 1)] :=
          Nat.ModEq.add_left _ ((Nat.modEq_zero_iff_dvd).mpr (h4ke.mul_right _))
      _ = e * conjExp α := Nat.add_zero _
  rw [conjAut_Xpow, mem_fixedSubring_iff]
  refine ⟨?_, ?_⟩
  · rw [map_add, conjAut_Xpow, conjAut_Xpow, Xpow_congr_mod α hconjsq, _root_.add_comm]
  · rw [map_add, hgenX, hgenX, Xpow_congr_mod α hgen, Xpow_congr_mod α hcgen]

/-! ## Coefficients of monomials and conjugates -/

/-- The `j`-th coefficient of the reduced `c·X^i` (for `i < d`) is `c·[j = i]`. -/
theorem mk_monomial_coeff_lt (α : ℕ) {i : ℕ} (hi : i < 2 ^ α) (c : R) (j : ℕ) :
    (Rq.mk (powTwoCyclotomic α) (CompPoly.CPolynomial.monomial i c)).1.coeff j
      = if j = i then c else 0 := by
  have hself : (powTwoCyclotomic (R := R) α).reduce (CompPoly.CPolynomial.monomial i c)
      = CompPoly.CPolynomial.monomial i c := by
    refine CyclotomicModulus.reduce_eq_self_of_degree_lt _ ?_
    rw [toPoly_monomial]
    calc (Polynomial.monomial i c).degree ≤ (i : WithBot ℕ) := Polynomial.degree_monomial_le i c
      _ < (powTwoCyclotomic α).φ.toPoly.degree := by
          rw [powTwoCyclotomic_toPoly_degree]; exact_mod_cast hi
  change ((powTwoCyclotomic (R := R) α).reduce (CompPoly.CPolynomial.monomial i c)).coeff j = _
  rw [hself, CPolynomial.coeff_monomial]

/-- **`X^f` has no coefficient off its folded position**: `(X^f).coeff p = 0` for `p < d` with
`p ≠ f mod d`. Proved by folding `X^f = (-1)^{f/d}·X^{f mod d}` and casing on the parity of `f/d`
(so the sign is literally `±1`), avoiding any product-coefficient evaluation. -/
theorem Xpow_coeff_eq_zero_of_ne (α f p : ℕ) (hne : p ≠ f % 2 ^ α) :
    (Xpow (powTwoCyclotomic (R := R) α) f).1.coeff p = 0 := by
  have hmod : f % 2 ^ α < 2 ^ α := Nat.mod_lt _ (by positivity)
  rw [Xpow, mk_monomial_fold]
  rcases Nat.even_or_odd (f / 2 ^ α) with he | ho
  · rw [he.neg_one_pow, _root_.one_mul, mk_monomial_coeff_lt α hmod, if_neg hne]
  · rw [ho.neg_one_pow, neg_one_mul, Rq.neg_val, CPolynomial.coeff_neg,
      mk_monomial_coeff_lt α hmod, if_neg hne, neg_zero]

/-- The conjugate `σ_{-1}(X^e)` lands at position `d - e` (mod `d`), for `0 < e < d`. -/
theorem mul_conjExp_mod (α : ℕ) {e : ℕ} (he0 : 0 < e) (he : e < 2 ^ α) :
    (e * conjExp α) % 2 ^ α = 2 ^ α - e := by
  have hc : conjExp α + 1 = 2 ^ (α + 1) := by
    have : 1 ≤ 2 ^ (α + 1) := Nat.one_le_two_pow; rw [conjExp]; omega
  have hmod : e * conjExp α ≡ 2 ^ α - e [MOD 2 ^ α] := by
    apply Nat.ModEq.add_right_cancel' e
    rw [Nat.sub_add_cancel (le_of_lt he),
      show e * conjExp α + e = e * 2 ^ (α + 1) from by
        calc e * conjExp α + e = e * (conjExp α + 1) := by ring
          _ = e * 2 ^ (α + 1) := by rw [hc]]
    exact (Nat.modEq_zero_iff_dvd.mpr ⟨2 * e, by rw [pow_succ]; ring⟩).trans
      (Nat.modEq_zero_iff_dvd.mpr (dvd_refl _)).symm
  rw [Nat.ModEq] at hmod
  rw [hmod, Nat.mod_eq_of_lt (by omega)]

/-- **`σ_{-1}(X^e)` has no low-degree coefficient**: for `0 < e < d/2` and `p < d/2`,
`(σ_{-1}(X^e)).coeff p = 0` (its only coefficient sits at `d - e > d/2`). -/
theorem conjAut_Xpow_coeff_low (α : ℕ) (hα : 1 ≤ α) {e p : ℕ} (he0 : 0 < e)
    (he : e < 2 ^ (α - 1)) (hp : p < 2 ^ (α - 1)) :
    (conjAut α (Xpow (powTwoCyclotomic (R := R) α) e)).1.coeff p = 0 := by
  have hhalf : (2 : ℕ) ^ α = 2 * 2 ^ (α - 1) := by rw [← pow_succ']; congr 1; omega
  rw [conjAut_Xpow]
  refine Xpow_coeff_eq_zero_of_ne α (e * conjExp α) p ?_
  rw [mul_conjExp_mod α he0 (by omega)]
  omega

/-! ## The basis `{X^{(d/2k)·j} + σ_{-1}(X^{(d/2k)·j})}` of `R_q^H` -/

/-- The `j`-th symmetric basis element of `R_q^H`: `X^{(d/2k)·j} + σ_{-1}(X^{(d/2k)·j})`. -/
noncomputable def vElt (α κ : ℕ) (hκ : κ + 1 ≤ α) (j : Fin (2 ^ κ)) :
    fixedSubring (R := R) α (2 ^ κ) :=
  ⟨Xpow (powTwoCyclotomic α) (2 ^ (α - κ - 1) * (j : ℕ))
      + conjAut α (Xpow (powTwoCyclotomic α) (2 ^ (α - κ - 1) * (j : ℕ))),
    mem_fixed_symm α κ hκ ⟨(j : ℕ), rfl⟩⟩

theorem vElt_coe (α κ : ℕ) (hκ : κ + 1 ≤ α) (j : Fin (2 ^ κ)) :
    (vElt α κ hκ j).val
      = Xpow (powTwoCyclotomic (R := R) α) (2 ^ (α - κ - 1) * (j : ℕ))
        + conjAut α (Xpow (powTwoCyclotomic (R := R) α) (2 ^ (α - κ - 1) * (j : ℕ))) := rfl

/-- **Coefficient of the basis element**: `v_j` has coefficient `[s = j]·(2 if j=0 else 1)` at the
position `(d/2k)·s`. The two basis exponents of `v_j` are `(d/2k)·j` (degree `< d/2`) and its
conjugate (degree `> d/2`); only the former can equal `(d/2k)·s < d/2`, except at `j=0` where the
conjugate coincides (giving the doubling). -/
theorem vElt_coeff (α κ : ℕ) (hκ : κ + 1 ≤ α) (j s : Fin (2 ^ κ)) :
    (vElt α κ hκ j).val.1.coeff (2 ^ (α - κ - 1) * (s : ℕ))
      = if s = j then (if (j : ℕ) = 0 then (2 : R) else 1) else 0 := by
  have hα : 1 ≤ α := by omega
  have hhalf : (2 : ℕ) ^ (α - 1) = 2 ^ (α - κ - 1) * 2 ^ κ := by rw [← pow_add]; congr 1; omega
  have hej : 2 ^ (α - κ - 1) * (j : ℕ) < 2 ^ (α - 1) := by
    rw [hhalf]; exact mul_lt_mul_of_pos_left j.isLt (by positivity)
  have hes : 2 ^ (α - κ - 1) * (s : ℕ) < 2 ^ (α - 1) := by
    rw [hhalf]; exact mul_lt_mul_of_pos_left s.isLt (by positivity)
  have hejα : 2 ^ (α - κ - 1) * (j : ℕ) < 2 ^ α := by
    have h2 : (2 : ℕ) ^ α = 2 * 2 ^ (α - 1) := by rw [← pow_succ']; congr 1; omega
    omega
  have hpos : (0 : ℕ) < 2 ^ (α - κ - 1) := by positivity
  have heq_iff : (2 ^ (α - κ - 1) * (s : ℕ) = 2 ^ (α - κ - 1) * (j : ℕ)) ↔ s = j := by
    rw [mul_right_inj' hpos.ne', Fin.val_inj]
  rw [vElt_coe, Rq.add_val, CPolynomial.coeff_add, Xpow_coeff_of_lt α hejα]
  by_cases hsj : s = j
  · rw [if_pos (heq_iff.mpr hsj), if_pos hsj]
    by_cases hj0 : (j : ℕ) = 0
    · rw [hj0, Nat.mul_zero, conjAut_Xpow, Nat.zero_mul,
        Xpow_coeff_of_lt α (show (0 : ℕ) < 2 ^ α from by positivity)]
      have hs0 : 2 ^ (α - κ - 1) * (s : ℕ) = 0 := by
        rw [show (s : ℕ) = (j : ℕ) from by rw [hsj], hj0, Nat.mul_zero]
      rw [if_pos hs0, if_pos rfl]; norm_num
    · rw [conjAut_Xpow_coeff_low α hα
          (Nat.mul_pos hpos (Nat.pos_of_ne_zero hj0)) hej hes, _root_.add_zero, if_neg hj0]
  · rw [if_neg (fun h => hsj (heq_iff.mp h)), if_neg hsj]
    by_cases hj0 : (j : ℕ) = 0
    · rw [hj0, Nat.mul_zero, conjAut_Xpow, Nat.zero_mul,
        Xpow_coeff_of_lt α (show (0 : ℕ) < 2 ^ α from by positivity)]
      have hs0 : ¬ (2 ^ (α - κ - 1) * (s : ℕ) = 0) := by
        rw [Nat.mul_eq_zero, not_or]
        exact ⟨hpos.ne', fun h => hsj (Fin.ext (h.trans hj0.symm))⟩
      rw [if_neg hs0, _root_.add_zero]
    · rw [conjAut_Xpow_coeff_low α hα
          (Nat.mul_pos hpos (Nat.pos_of_ne_zero hj0)) hej hes, _root_.add_zero]

end ArkLib.Lattices.CyclotomicModulus
