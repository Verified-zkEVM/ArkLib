/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.PowTwo
import ArkLib.ToMathlib.Polynomial.AevalXPow

/-!
# Galois Automorphisms `σ_i : X ↦ X^i` of the Cyclotomic Ring

For the power-of-two cyclotomic ring `R_q = Z_q[X] / (X^{2^α} + 1)`, the Galois automorphisms
are the ring automorphisms `σ_i` induced by `X ↦ X^i` for `i` a unit modulo the conductor
`2d = 2^{α+1}` (equivalently, `i` odd). These are the maps used throughout Hachi [NOZ26, §3]
to identify the finite-field extensions inside `R_q`.

Following the project's two-layer discipline (cf. `CyclotomicRing/Basic.lean`):

* **Computable layer** (`galoisAut`): on a reduced representative `a = Σ_{k<d} a_k X^k`, the
  automorphism remaps each monomial `X^k ↦ X^{ki}` and reduces modulo `X^d + 1`. Since
  `X^d = -1`, this is a *signed coefficient permutation*, here realised directly as
  `Rq.mk Φ (Σ_k monomial (k·i) a_k)` (reduction handles the `X^{ki}`-folding). Fully
  computable / `#eval`-able.
* **Semantic layer** (`galoisAutₛ`): the Mathlib `R`-algebra endomorphism `aeval (X^i)` of
  `Polynomial R`, descended to the quotient `Polynomial R ⧸ (X^d+1)` via
  `Ideal.Quotient.lift`. This is a genuine `RingHom` for free; well-definedness needs
  `aeval (X^i)` to fix the ideal, which holds for `i` odd because `X^d + 1 ∣ X^{di} + 1`.
* **Soundness bridge** (`galoisAut_toQuotient`): the computable map agrees with the semantic
  one under `Rq.toQuotient`. This is the load-bearing (and hardest) lemma; it transfers the
  `RingHom`/bijectivity structure from the semantic side back to the computable map.

## Main definitions

* `galoisAut Φ i` — the computable automorphism action `Rq Φ → Rq Φ`.
* `galoisAutₛ α i hi` — the semantic automorphism `RingHom` on the quotient (`i` odd).
* `galoisRingHom α i hi` — the computable action bundled as a `RingHom`.

## References

* [Lyubashevsky, V., Nguyen, N. K., and Plançon, M., *Lattice-Based Zero-Knowledge Proofs*][LNP22]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open Polynomial CompPoly CompPoly.CPolynomial Finset

namespace ArkLib.Lattices.CyclotomicModulus

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R] [DecidableEq R]

variable (Φ : CyclotomicModulus R) [IsCyclotomic Φ]

/-! ## The computable automorphism `galoisAut` -/

/-- The **computable Galois automorphism action** `σ_i : Rq Φ → Rq Φ`, `X^k ↦ X^{ki}`.

On a reduced representative `a = Σ_{k<d} a_k X^k`, it forms `Σ_k a_k X^{ki}` and reduces modulo
the modulus; since `X^d = -1`, this is the signed coefficient permutation. It is a genuine ring
automorphism only when `i` is a unit modulo the conductor (`i` odd, for the power-of-two ring);
the bare action is defined for all `i`. -/
def galoisAut (i : ℕ) (a : Rq Φ) : Rq Φ :=
  Rq.mk Φ (∑ k ∈ range Φ.φ.natDegree, monomial (k * i) (a.1.coeff k))

@[simp] theorem galoisAut_zero (i : ℕ) : galoisAut Φ i 0 = 0 := by
  unfold galoisAut
  have : ∀ k ∈ range Φ.φ.natDegree,
      (monomial (k * i) ((0 : Rq Φ).1.coeff k) : CPolynomial R) = 0 := by
    intro k _
    rw [Rq.zero_val, CompPoly.CPolynomial.coeff_zero, monomial_eq_zero]
  rw [Finset.sum_congr rfl this, Finset.sum_const_zero]
  rfl

/-- `galoisAut` is additive. Follows from additivity of coefficient extraction, of `monomial`
in its coefficient, of finite sums, and of `Rq.mk`. -/
theorem galoisAut_add (i : ℕ) (a b : Rq Φ) :
    galoisAut Φ i (a + b) = galoisAut Φ i a + galoisAut Φ i b := by
  unfold galoisAut
  rw [← Rq.mk_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Rq.add_val, CompPoly.CPolynomial.coeff_add, CompPoly.CPolynomial.monomial_add]

/-- `σ_i` fixes `1`, since only the constant term contributes (so in particular `σ_1` fixes it). -/
theorem galoisAut_map_one (α i : ℕ) : galoisAut (powTwoCyclotomic (R := R) α) i 1 = 1 := by
  have h2 : (0 : ℕ) < 2 ^ α := pow_pos (by norm_num) α
  have hpos : 0 < (powTwoCyclotomic (R := R) α).φ.natDegree := by
    rw [powTwoCyclotomic_natDegree]; exact h2
  have hone : (1 : Rq (powTwoCyclotomic (R := R) α)).1 = (1 : CPolynomial R) := by
    change (powTwoCyclotomic (R := R) α).reduce 1 = 1
    refine CyclotomicModulus.reduce_eq_self_of_degree_lt _ ?_
    rw [CompPoly.CPolynomial.toPoly_one, Polynomial.degree_one, powTwoCyclotomic_toPoly,
      ← Polynomial.C_1, Polynomial.degree_X_pow_add_C h2 (1 : R)]
    exact_mod_cast h2
  have hcoeff : ∀ k,
      (1 : Rq (powTwoCyclotomic (R := R) α)).1.coeff k = if k = 0 then (1 : R) else 0 :=
    fun k => by rw [hone]; exact CompPoly.CPolynomial.coeff_one k
  have hm : (monomial 0 (1 : R) : CPolynomial R) = 1 :=
    CompPoly.CPolynomial.eq_iff_coeff.mpr fun j => by
      rw [CompPoly.CPolynomial.coeff_monomial, CompPoly.CPolynomial.coeff_one]
  unfold galoisAut
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hpos)
        (fun k _ hk => by rw [hcoeff, if_neg hk, monomial_eq_zero]),
      hcoeff, if_pos rfl, Nat.zero_mul, hm]
  rfl

/-! ## The semantic automorphism via Mathlib `aeval` -/

/-- The Mathlib `R`-algebra endomorphism of `Polynomial R` sending `X ↦ X^i` (i.e. `p ↦ p(X^i)`),
as a `RingHom`. -/
noncomputable def galoisAeval (i : ℕ) : Polynomial R →+* Polynomial R :=
  (Polynomial.aeval (Polynomial.X ^ i : Polynomial R)).toRingHom

omit [BEq R] [LawfulBEq R] [DecidableEq R] in
@[simp] theorem galoisAeval_apply (i : ℕ) (p : Polynomial R) :
    galoisAeval i p = Polynomial.aeval (Polynomial.X ^ i : Polynomial R) p := rfl

omit [DecidableEq R] in
/-- Well-definedness on the power-of-two ring: `aeval (X^i)` maps the modulus ideal into itself
for odd `i`, since `X^{2^α} + 1 ∣ (X^{2^α})^i + 1`. -/
theorem powTwo_galoisAeval_mem (α i : ℕ) (hi : Odd i) {p : Polynomial R}
    (hp : p ∈ (powTwoCyclotomic (R := R) α).modIdeal) :
    galoisAeval i p ∈ (powTwoCyclotomic (R := R) α).modIdeal := by
  -- `galoisAeval i X = X ^ i`
  have hX : galoisAeval i (Polynomial.X : Polynomial R) = Polynomial.X ^ i := by
    simp [galoisAeval]
  -- `aeval (X^i)` sends the modulus to `(X^{2^α})^i + 1`, divisible by `X^{2^α} + 1`.
  have hdvd : (powTwoCyclotomic (R := R) α).φ.toPoly ∣
      galoisAeval i (powTwoCyclotomic (R := R) α).φ.toPoly := by
    rw [powTwoCyclotomic_toPoly, map_add, map_pow, map_one, hX,
      show ((Polynomial.X : Polynomial R) ^ i) ^ 2 ^ α = (Polynomial.X ^ 2 ^ α) ^ i by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
    have hd := sub_dvd_pow_sub_pow (Polynomial.X ^ 2 ^ α : Polynomial R) (-1) i
    rwa [Odd.neg_one_pow hi, sub_neg_eq_add, sub_neg_eq_add] at hd
  simp only [modIdeal, Ideal.mem_span_singleton] at hp ⊢
  obtain ⟨c, rfl⟩ := hp
  rw [map_mul]
  exact hdvd.mul_right _

/-- The **semantic Galois automorphism** `σ_i` on the quotient ring, obtained by descending the
Mathlib endomorphism `aeval (X^i)` along `Ideal.Quotient.lift`. A genuine `RingHom`. -/
noncomputable def galoisAutₛ (α i : ℕ) (hi : Odd i) :
    (powTwoCyclotomic (R := R) α).CyclotomicRing →+* (powTwoCyclotomic (R := R) α).CyclotomicRing :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk (powTwoCyclotomic (R := R) α).modIdeal).comp (galoisAeval i))
    (fun p hp => by
      rw [RingHom.comp_apply]
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr (powTwo_galoisAeval_mem α i hi hp))

omit [DecidableEq R] in
/-- The semantic automorphism on a quotient class: `galoisAutₛ (mk p) = mk (aeval (X^i) p)`. -/
theorem galoisAutₛ_mk (α i : ℕ) (hi : Odd i) (p : Polynomial R) :
    galoisAutₛ α i hi (Ideal.Quotient.mk _ p)
      = Ideal.Quotient.mk _ (Polynomial.aeval (Polynomial.X ^ i : Polynomial R) p) := by
  rw [galoisAutₛ, Ideal.Quotient.lift_mk, RingHom.comp_apply, galoisAeval_apply]

omit [DecidableEq R] in
/-- **(S1)** The semantic automorphism on a lifted element: `galoisAutₛ` applied to
`a.toQuotient` is the class of `aeval (X^i)` applied to the underlying polynomial. -/
theorem galoisAutₛ_toQuotient (α i : ℕ) (hi : Odd i) (a : Rq (powTwoCyclotomic (R := R) α)) :
    galoisAutₛ α i hi a.toQuotient
      = Ideal.Quotient.mk _
          (Polynomial.aeval (Polynomial.X ^ i : Polynomial R) a.1.toPoly) := by
  rw [Rq.toQuotient, quotientHom_apply, galoisAutₛ_mk]

/-! ## Soundness bridge -/

/-- **(S5)** The core polynomial identity behind soundness: the monomial-remapped sum (before
reduction) equals `aeval (X^i)` of the underlying polynomial. Both sides are
`∑_{k<d} X^{ki}·a_k`. -/
theorem galoisAut_sum_toPoly_eq_aeval (α i : ℕ) (a : Rq (powTwoCyclotomic (R := R) α)) :
    (∑ k ∈ range (powTwoCyclotomic (R := R) α).φ.natDegree,
        CompPoly.CPolynomial.monomial (k * i) (a.1.coeff k)).toPoly
      = Polynomial.aeval (Polynomial.X ^ i : Polynomial R) a.1.toPoly := by
  rw [toPoly_sum,
    show a.1.toPoly = ∑ k ∈ range (powTwoCyclotomic (R := R) α).φ.natDegree,
        Polynomial.monomial k (a.1.toPoly.coeff k)
      from a.1.toPoly.as_sum_range' _ (Rq.natDegree_val_toPoly_lt α a),
    map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [toPoly_monomial, aeval_X_pow_monomial, coeff_toPoly]

/-- **(S6) Soundness**: the computable automorphism agrees with the semantic one under
`Rq.toQuotient`. This is the key bridge (Hachi [NOZ26, §3]); it lets all algebraic structure
(ring-hom laws, bijectivity) be proven on the Mathlib side and transported back. -/
theorem galoisAut_toQuotient (α i : ℕ) (hi : Odd i) (a : Rq (powTwoCyclotomic (R := R) α)) :
    (galoisAut (powTwoCyclotomic α) i a).toQuotient = galoisAutₛ α i hi a.toQuotient := by
  rw [galoisAut, Rq.toQuotient_mk, galoisAutₛ_toQuotient α i hi, quotientHom_apply]
  exact congrArg (Ideal.Quotient.mk _) (galoisAut_sum_toPoly_eq_aeval α i a)

/-- Multiplicativity of the computable automorphism, transported from `galoisAutₛ` (a `RingHom`)
through the soundness bridge. -/
theorem galoisAut_mul (α i : ℕ) (hi : Odd i) (a b : Rq (powTwoCyclotomic (R := R) α)) :
    galoisAut (powTwoCyclotomic α) i (a * b)
      = galoisAut (powTwoCyclotomic α) i a * galoisAut (powTwoCyclotomic α) i b := by
  apply Rq.toQuotient_injective (powTwoCyclotomic α)
  have hmul : ∀ x y : Rq (powTwoCyclotomic (R := R) α),
      (x * y).toQuotient = x.toQuotient * y.toQuotient :=
    fun x y => map_mul (Rq.toQuotientHom _) x y
  rw [galoisAut_toQuotient α i hi, hmul a b, map_mul,
    hmul (galoisAut (powTwoCyclotomic α) i a) (galoisAut (powTwoCyclotomic α) i b),
    galoisAut_toQuotient α i hi, galoisAut_toQuotient α i hi]

/-! ## Exponent periodicity (`σ_n` depends only on `n mod 2^{α+1}`) -/

-- TODO this is not the right place for this.
omit [DecidableEq R] in
/-- **(C-1)** `X^{2^{α+1}} ≡ 1` in the quotient, since `X^{2d} - 1 = (X^d - 1)(X^d + 1)`. -/
theorem mk_X_pow_conductor_eq_one (α : ℕ) :
    Ideal.Quotient.mk (powTwoCyclotomic (R := R) α).modIdeal (Polynomial.X ^ 2 ^ (α + 1)) = 1 := by
  have hmem : (Polynomial.X ^ 2 ^ (α + 1) - 1 : Polynomial R)
      ∈ (powTwoCyclotomic (R := R) α).modIdeal := by
    rw [modIdeal, Ideal.mem_span_singleton, powTwoCyclotomic_toPoly, pow_succ, pow_mul]
    exact ⟨Polynomial.X ^ 2 ^ α - 1, by ring⟩
  rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk (powTwoCyclotomic (R := R) α).modIdeal),
    ← map_sub]
  exact (Ideal.Quotient.eq_zero_iff_mem).mpr hmem

omit [DecidableEq R] in
/-- **(C-2)** `X^n ≡ X^{n mod 2^{α+1}}` in the quotient. -/
theorem mk_X_pow_periodic (α n : ℕ) :
    Ideal.Quotient.mk (powTwoCyclotomic (R := R) α).modIdeal (Polynomial.X ^ n)
      = Ideal.Quotient.mk _ (Polynomial.X ^ (n % 2 ^ (α + 1))) := by
  nth_rewrite 1 [← Nat.div_add_mod n (2 ^ (α + 1))]
  rw [pow_add, pow_mul, map_mul, map_pow, mk_X_pow_conductor_eq_one, one_pow, _root_.one_mul]

omit [DecidableEq R] in
/-- **(C-3 helper)** `aeval (X^n)` and `aeval (X^{n mod 2^{α+1}})` agree in the quotient. -/
theorem mk_aeval_X_pow_periodic (α n : ℕ) (p : Polynomial R) :
    Ideal.Quotient.mk (powTwoCyclotomic (R := R) α).modIdeal
        (Polynomial.aeval (Polynomial.X ^ n : Polynomial R) p)
      = Ideal.Quotient.mk _
          (Polynomial.aeval (Polynomial.X ^ (n % 2 ^ (α + 1)) : Polynomial R) p) := by
  have e : ∀ j : ℕ,
      Ideal.Quotient.mk (powTwoCyclotomic (R := R) α).modIdeal (aeval (Polynomial.X ^ j) p)
        = aeval (Ideal.Quotient.mk (powTwoCyclotomic (R := R) α).modIdeal
            (Polynomial.X ^ j)) p := by
    intro j
    have h := aeval_algHom_apply (Ideal.Quotient.mkₐ R (powTwoCyclotomic (R := R) α).modIdeal)
      (Polynomial.X ^ j) p
    simp only [Ideal.Quotient.mkₐ_eq_mk] at h
    exact h.symm
  rw [e, e, mk_X_pow_periodic]

/-- The computable automorphism, mapped to the quotient, is `mk (aeval (X^n) ·)` for any `n`
(unlike `galoisAut_toQuotient`, no oddness is needed — this routes through `aeval` directly). -/
theorem galoisAut_aeval_toQuotient (α n : ℕ) (a : Rq (powTwoCyclotomic (R := R) α)) :
    (galoisAut (powTwoCyclotomic α) n a).toQuotient
      = Ideal.Quotient.mk _ (Polynomial.aeval (Polynomial.X ^ n : Polynomial R) a.1.toPoly) := by
  rw [galoisAut, Rq.toQuotient_mk, quotientHom_apply]
  exact congrArg _ (galoisAut_sum_toPoly_eq_aeval α n a)

/-- **Exponent periodicity**: `σ_n = σ_{n mod 2^{α+1}}` (the conductor is `2^{α+1}`). -/
theorem galoisAut_periodic (α n : ℕ) (a : Rq (powTwoCyclotomic (R := R) α)) :
    galoisAut (powTwoCyclotomic α) n a
      = galoisAut (powTwoCyclotomic α) (n % 2 ^ (α + 1)) a := by
  apply Rq.toQuotient_injective (powTwoCyclotomic α)
  rw [galoisAut_aeval_toQuotient, galoisAut_aeval_toQuotient, mk_aeval_X_pow_periodic]

/-! ## The computable automorphism bundled as a `RingHom` -/

/-- The computable Galois automorphism action bundled as a `RingHom` on `Rq`. The additive
structure and unitality are proven directly; multiplicativity (`map_mul'`) is transported from
the semantic `galoisAutₛ` via the soundness bridge `galoisAut_toQuotient` (see `galoisAut_mul`). -/
noncomputable def galoisRingHom (α i : ℕ) (hi : Odd i) :
    Rq (powTwoCyclotomic (R := R) α) →+* Rq (powTwoCyclotomic (R := R) α) where
  toFun := galoisAut (powTwoCyclotomic α) i
  map_one' := galoisAut_map_one α i
  map_mul' := galoisAut_mul α i hi
  map_zero' := galoisAut_zero (powTwoCyclotomic α) i
  map_add' := galoisAut_add (powTwoCyclotomic α) i

@[simp] theorem galoisRingHom_apply (α i : ℕ) (hi : Odd i)
    (a : Rq (powTwoCyclotomic (R := R) α)) :
    galoisRingHom α i hi a = galoisAut (powTwoCyclotomic α) i a := rfl

end ArkLib.Lattices.CyclotomicModulus
