/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Rq
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Building Blocks for Lyubashevsky–Seiler Short-Element Invertibility

Reusable lemmas feeding the proof of `isUnit_of_l1Norm_le` in
`NormBounds.LyubashevskySeiler`:

* **Iso** — the ring isomorphism `Rq Ψ ≃+* Ψ.CyclotomicRing` (surjectivity of the existing
  injective `toQuotientHom`) and unit-transfer along it.
* **Lte** — the 2-adic valuation `v₂(q^{2^k} - 1) = k + 2` (lifting-the-exponent) and the
  resulting multiplicative order `orderOf (q mod 2^{α+1}) = 2^{α-1}` for `q ≡ 5 (mod 8)`.
* **Irred** — irreducibility of the splitting factor `X^{2^{α-1}} - r` over `ZMod q`.
* **Coeff** — the abstract coefficient-extraction kernel: a vanishing combination of powers of a
  root `ζ` (with `ζ^{2^{α-1}}` a scalar square root of `-1`) forces, per coefficient pair,
  `q ∣ (â_j² + â_{2^{α-1}+j}²)` over `ℤ`.

## References

* [Lyubashevsky, V., and Seiler, G., *Short, Invertible Elements in Partially Splitting
    Cyclotomic Rings and Applications to Lattice-Based Zero-Knowledge Proofs*][LS18]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open scoped BigOperators

namespace ArkLib.Lattices.CyclotomicModulus

/-! ## Iso: surjectivity of `toQuotientHom` and unit transfer -/

section Iso

open Polynomial CompPoly CompPoly.CPolynomial

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R]
variable (Ψ : CyclotomicModulus R) [IsCyclotomic Ψ]

-- `Rq.toQuotient_surjective` and `Rq.equivQuotient` live in `CyclotomicRing.Rq`; reuse them here.

@[simp] theorem Rq.coe_equivQuotient :
    ⇑(Rq.equivQuotient Ψ) = Rq.toQuotientHom Ψ := rfl

/-- Non-units transfer along the iso: if `c : Rq Ψ` is not a unit, neither is its image
under `toQuotientHom`. -/
theorem Rq.not_isUnit_toQuotientHom_of_not_isUnit {c : Rq Ψ} (hc : ¬ IsUnit c) :
    ¬ IsUnit (Rq.toQuotientHom Ψ c) := by
  intro h
  apply hc
  have hu : IsUnit (Rq.equivQuotient Ψ c) := h
  have := hu.map (Rq.equivQuotient Ψ).symm
  rwa [RingEquiv.symm_apply_apply] at this

end Iso

/-! ## Lte: 2-adic valuation and multiplicative order of `q` -/

section Lte

variable {q : ℕ} [Fact (Nat.Prime q)]

omit [Fact (Nat.Prime q)] in
/-- For a prime `q` with `q % 8 = 5`, `q - 1 ≡ 4 (mod 8)`, hence `v₂(q-1) = 2`. -/
theorem emultiplicity_two_q_sub_one (hq5 : q % 8 = 5) :
    emultiplicity (2 : ℤ) ((q : ℤ) - 1) = 2 := by
  have h4 : (4 : ℤ) ∣ ((q : ℤ) - 1) := by
    have : ((q : ℤ) - 1) % 4 = 0 := by omega
    omega
  have h8 : ¬ (8 : ℤ) ∣ ((q : ℤ) - 1) := by intro hd; omega
  have : emultiplicity (2 : ℤ) ((q : ℤ) - 1) = ((2 : ℕ) : ℕ∞) := by
    rw [emultiplicity_eq_coe]
    refine ⟨?_, ?_⟩
    · simpa using (show (2 : ℤ) ^ 2 ∣ ((q : ℤ) - 1) by simpa using h4)
    · intro hd
      exact h8 (by simpa using (dvd_trans (by norm_num : (8 : ℤ) ∣ 2 ^ (2 + 1)) hd))
  simpa using this

omit [Fact (Nat.Prime q)] in
/-- `q` is odd, so `¬ 2 ∣ q`. -/
theorem not_two_dvd_q (hq5 : q % 8 = 5) : ¬ (2 : ℤ) ∣ (q : ℤ) := by
  intro hd; obtain ⟨c, hc⟩ := hd; omega

omit [Fact (Nat.Prime q)] in
/-- `4 ∣ q - 1` from `q % 8 = 5`. -/
theorem four_dvd_q_sub_one (hq5 : q % 8 = 5) : (4 : ℤ) ∣ ((q : ℤ) - 1) := by omega

omit [Fact (Nat.Prime q)] in
/-- The 2-adic valuation of `q^(2^k) - 1` is `k + 2`. -/
theorem emultiplicity_two_q_pow_sub_one (hq5 : q % 8 = 5) (k : ℕ) :
    emultiplicity (2 : ℤ) ((q : ℤ) ^ (2 ^ k) - 1) = (k : ℕ∞) + 2 := by
  have hxy : (4 : ℤ) ∣ ((q : ℤ) - 1) := four_dvd_q_sub_one hq5
  have hx : ¬ (2 : ℤ) ∣ (q : ℤ) := not_two_dvd_q hq5
  have key := Int.two_pow_sub_pow' (x := (q : ℤ)) (y := 1) (2 ^ k) (by simpa using hxy)
    (by simpa using hx)
  rw [one_pow] at key
  rw [key, emultiplicity_two_q_sub_one hq5]
  have h2 : emultiplicity (2 : ℤ) ((2 ^ k : ℕ) : ℤ) = (k : ℕ∞) := by
    have hc : ((2 ^ k : ℕ) : ℤ) = (2 : ℤ) ^ k := by push_cast; ring
    rw [hc, emultiplicity_pow_self_of_prime (Int.prime_two) k]
  rw [h2, add_comm]

omit [Fact (Nat.Prime q)] in
/-- `2^(k+2) ∣ q^(2^k) - 1`. -/
theorem two_pow_dvd (hq5 : q % 8 = 5) (k : ℕ) :
    ((2 : ℤ) ^ (k + 2)) ∣ ((q : ℤ) ^ (2 ^ k) - 1) := by
  rw [pow_dvd_iff_le_emultiplicity, emultiplicity_two_q_pow_sub_one hq5 k]; push_cast; rw [add_comm]

omit [Fact (Nat.Prime q)] in
/-- `¬ 2^(k+3) ∣ q^(2^k) - 1`. -/
theorem not_two_pow_dvd (hq5 : q % 8 = 5) (k : ℕ) :
    ¬ (((2 : ℤ) ^ (k + 3)) ∣ ((q : ℤ) ^ (2 ^ k) - 1)) := by
  rw [← emultiplicity_lt_iff_not_dvd, emultiplicity_two_q_pow_sub_one hq5 k]
  have : ((k : ℕ∞) + 2) = ((k + 2 : ℕ) : ℕ∞) := by push_cast; ring
  rw [this]
  exact_mod_cast WithTop.coe_lt_coe.mpr (by omega : (k + 2 : ℕ) < (k + 3 : ℕ))

omit [Fact (Nat.Prime q)] in
/-- `q` is coprime to `2^m` when `q % 8 = 5` (`q` odd). -/
theorem coprime_q_two_pow (hq5 : q % 8 = 5) (m : ℕ) : Nat.Coprime q (2 ^ m) := by
  apply Nat.Coprime.pow_right
  have : q % 2 = 1 := by omega
  rw [Nat.coprime_two_right, Nat.odd_iff]; exact this

omit [Fact (Nat.Prime q)] in
/-- Bridge: `u^m = 1` in the unit group iff `2^(α+1) ∣ q^m - 1`. -/
theorem unit_pow_eq_one_iff (hq5 : q % 8 = 5) (α : ℕ) (m : ℕ) :
    (ZMod.unitOfCoprime q (coprime_q_two_pow hq5 (α + 1))) ^ m = 1
      ↔ ((2 : ℤ) ^ (α + 1)) ∣ ((q : ℤ) ^ m - 1) := by
  rw [← Units.val_eq_one, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime]
  rw [show ((q : ZMod (2 ^ (α + 1))) ^ m) = (((q ^ m : ℕ) : ZMod (2 ^ (α + 1)))) by
    push_cast; ring]
  rw [show (1 : ZMod (2 ^ (α + 1))) = ((1 : ℕ) : ZMod (2 ^ (α + 1))) by push_cast; ring]
  rw [ZMod.natCast_eq_natCast_iff, Nat.modEq_iff_dvd]
  have hc : ((2 ^ (α + 1) : ℕ) : ℤ) = (2 : ℤ) ^ (α + 1) := by push_cast; ring
  rw [hc]
  have hcast : ((1 : ℕ) : ℤ) - ((q ^ m : ℕ) : ℤ) = -((q : ℤ) ^ m - 1) := by push_cast; ring
  rw [hcast, dvd_neg]

omit [Fact (Nat.Prime q)] in
/-- The multiplicative order of `q` modulo `2^(α+1)` is `2^(α-1)`, phrased to match
`ZMod.irreducible_of_dvd_cyclotomic_of_natDegree` (`K = ZMod q`, `n = 2^(α+1)`). -/
theorem orderOf_q_mod_two_pow (hq5 : q % 8 = 5) (α : ℕ) (hα : 1 ≤ α) :
    orderOf (ZMod.unitOfCoprime q (coprime_q_two_pow hq5 (α + 1))) = 2 ^ (α - 1) := by
  rcases Nat.lt_or_ge α 2 with hlt | hge
  · have hα1 : α = 1 := by omega
    subst hα1
    simp only [Nat.sub_self, pow_zero]
    rw [orderOf_eq_one_iff, ← pow_one (ZMod.unitOfCoprime q _), unit_pow_eq_one_iff hq5 1 1]
    simpa using four_dvd_q_sub_one hq5
  · have key := orderOf_eq_prime_pow (x := ZMod.unitOfCoprime q (coprime_q_two_pow hq5 (α + 1)))
      (p := 2) (n := α - 2) ?_ ?_
    · rw [key]; congr 1; omega
    · rw [unit_pow_eq_one_iff hq5 α]
      have h3 := not_two_pow_dvd (q := q) hq5 (α - 2)
      have he : (α - 2) + 3 = α + 1 := by omega
      rwa [he] at h3
    · rw [unit_pow_eq_one_iff hq5 α]
      have h2 := two_pow_dvd (q := q) hq5 (α - 1)
      have he : (α - 1) + 2 = α + 1 := by omega
      have he2 : (α - 2) + 1 = α - 1 := by omega
      rw [he2]; rwa [he] at h2

end Lte

/-! ## Irred: irreducibility of the splitting factor `X^{2^{α-1}} - r` -/

section Irred

open Polynomial

variable {q : ℕ} [Fact (Nat.Prime q)] (α : ℕ)

/-- The `2^(α+1)`-th cyclotomic polynomial over a field equals `X^(2^α)+1`. -/
theorem cyclotomic_two_pow_eq (R : Type*) [Field R] :
    cyclotomic (2 ^ (α + 1)) R = X ^ (2 ^ α) + 1 := by
  rw [cyclotomic_prime_pow_eq_geom_sum (R := R) (p := 2) (n := α) Nat.prime_two]
  rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, add_comm]

/-- `X^(2^(α-1)) - C r` divides `X^(2^α)+1` when `r^2 = -1` and `α ≥ 1`. -/
theorem dvd_cyclotomic_factor (R : Type*) [Field R] (r : R) (hr : r ^ 2 = -1) (hα : 1 ≤ α) :
    (X ^ (2 ^ (α - 1)) - C r : R[X]) ∣ X ^ (2 ^ α) + 1 := by
  refine ⟨X ^ (2 ^ (α - 1)) + C r, ?_⟩
  have hpow : 2 ^ (α - 1) + 2 ^ (α - 1) = 2 ^ α := by
    rw [← two_mul, ← pow_succ']; congr 1; omega
  have : (X ^ (2 ^ (α - 1)) - C r) * (X ^ (2 ^ (α - 1)) + C r)
      = X ^ (2 ^ (α - 1)) * X ^ (2 ^ (α - 1)) - C r * C r := by ring
  rw [this, ← pow_add, hpow, ← C_mul, ← sq, hr, C_neg, C_1, sub_neg_eq_add]

/-- **Irreducibility of the splitting factor.** `X^{2^{α-1}} - r` is irreducible over `ZMod q`,
given the order
fact `horder` (supplied by `orderOf_q_mod_two_pow`). Uses
`ZMod.irreducible_of_dvd_cyclotomic_of_natDegree`: the factor divides
`cyclotomic 2^{α+1} = X^{2^α}+1` and has degree `2^{α-1} = orderOf (q mod 2^{α+1})`. -/
theorem irreducible_X_pow_sub_C_r (hq8 : q % 8 = 5) (hα : 1 ≤ α) (r : ZMod q) (hr : r ^ 2 = -1)
    (horder : orderOf
        (ZMod.unitOfCoprime q (n := 2 ^ (α + 1))
          ((Fact.out (p := Nat.Prime q)).coprime_iff_not_dvd.mpr
            (by
              intro h
              have hq2 : q = 2 :=
                (Nat.prime_dvd_prime_iff_eq (Fact.out (p := Nat.Prime q)) Nat.prime_two).mp
                  ((Fact.out (p := Nat.Prime q)).dvd_of_dvd_pow h)
              omega)))
      = 2 ^ (α - 1)) :
    Irreducible (X ^ (2 ^ (α - 1)) - C r : (ZMod q)[X]) := by
  have hqodd : ¬ q ∣ 2 ^ (α + 1) := by
    intro h
    have hq2 : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq (Fact.out (p := Nat.Prime q)) Nat.prime_two).mp
        ((Fact.out (p := Nat.Prime q)).dvd_of_dvd_pow h)
    omega
  apply ZMod.irreducible_of_dvd_cyclotomic_of_natDegree (p := q) (n := 2 ^ (α + 1)) hqodd
  · rw [cyclotomic_two_pow_eq]; exact dvd_cyclotomic_factor α (ZMod q) r hr hα
  · rw [natDegree_X_pow_sub_C]; exact horder.symm

end Irred

/-! ## Coeff: the abstract coefficient-extraction kernel -/

section Coeff

variable {q : ℕ} [NeZero q] {F : Type*} [Field F] [Algebra (ZMod q) F]

omit [NeZero q] in
/-- Splitting the degree-`2^α` sum into low/high halves and factoring `ζ^{2^{α-1}} = s`
collects the coefficient of `ζ^j` as `a_j + s·a_{2^{α-1}+j}`. -/
theorem sum_eq_halfSum (α : ℕ) (hα : 1 ≤ α) (ζ : F) (s : ZMod q)
    (hζ : ζ ^ (2 ^ (α - 1)) = algebraMap (ZMod q) F s) (a : ℕ → ZMod q)
    (hsum : ∑ k ∈ Finset.range (2 ^ α), algebraMap (ZMod q) F (a k) * ζ ^ k = 0) :
    ∑ j ∈ Finset.range (2 ^ (α - 1)),
      algebraMap (ZMod q) F (a j + s * a (2 ^ (α - 1) + j)) * ζ ^ j = 0 := by
  have hsplit : 2 ^ α = 2 ^ (α - 1) + 2 ^ (α - 1) := by
    conv_lhs => rw [show α = (α - 1) + 1 from (Nat.succ_pred_eq_of_pos hα).symm]
    rw [pow_succ]; ring
  rw [hsplit, Finset.sum_range_add] at hsum
  have hhigh : ∀ j ∈ Finset.range (2 ^ (α - 1)),
      algebraMap (ZMod q) F (a (2 ^ (α - 1) + j)) * ζ ^ (2 ^ (α - 1) + j)
        = algebraMap (ZMod q) F (s * a (2 ^ (α - 1) + j)) * ζ ^ j := by
    intro j _; rw [pow_add, hζ, map_mul]; ring
  rw [Finset.sum_congr rfl hhigh, ← Finset.sum_add_distrib] at hsum
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro j _; rw [map_add, add_mul]

omit [NeZero q] in
/-- Linear independence of `1, ζ, …, ζ^{2^{α-1}-1}` makes each collected coefficient vanish. -/
theorem halfSum_coeff_eq_zero (α : ℕ) (hα : 1 ≤ α) (ζ : F) (s : ZMod q)
    (hζ : ζ ^ (2 ^ (α - 1)) = algebraMap (ZMod q) F s)
    (hindep : LinearIndependent (ZMod q) (fun i : Fin (2 ^ (α - 1)) ↦ ζ ^ (i : ℕ)))
    (a : ℕ → ZMod q)
    (hsum : ∑ k ∈ Finset.range (2 ^ α), algebraMap (ZMod q) F (a k) * ζ ^ k = 0)
    (j : ℕ) (hj : j < 2 ^ (α - 1)) :
    a j + s * a (2 ^ (α - 1) + j) = 0 := by
  set g : Fin (2 ^ (α - 1)) → ZMod q :=
    fun i ↦ a (i : ℕ) + s * a (2 ^ (α - 1) + (i : ℕ)) with hg
  have hcollapse := sum_eq_halfSum α hα ζ s hζ a hsum
  have hsmul : ∀ i : Fin (2 ^ (α - 1)), g i • ζ ^ (i : ℕ)
      = algebraMap (ZMod q) F (a (i : ℕ) + s * a (2 ^ (α - 1) + (i : ℕ))) * ζ ^ (i : ℕ) := by
    intro i; rw [hg, Algebra.smul_def]
  have huniv : ∑ i : Fin (2 ^ (α - 1)), g i • ζ ^ (i : ℕ) = 0 := by
    rw [Finset.sum_congr rfl (fun i _ ↦ hsmul i)]
    rw [Fin.sum_univ_eq_sum_range
      (fun k ↦ algebraMap (ZMod q) F (a k + s * a (2 ^ (α - 1) + k)) * ζ ^ k)]
    exact hcollapse
  have := (Fintype.linearIndependent_iff.mp hindep) g huniv ⟨j, hj⟩
  simpa [hg] using this

omit [NeZero q] [Algebra (ZMod q) F] in
/-- From `x + s·y = 0` with `s² = -1`, the centered representatives satisfy
`q ∣ (x̂² + ŷ²)` over `ℤ`. -/
theorem dvd_valMinAbs_sq_add_sq (s x y : ZMod q) (hs : s ^ 2 = -1) (hxy : x + s * y = 0) :
    (q : ℤ) ∣ (x.valMinAbs ^ 2 + y.valMinAbs ^ 2) := by
  have hx : x = -(s * y) := by linear_combination hxy
  have hzero : x ^ 2 + y ^ 2 = 0 := by rw [hx]; ring_nf; rw [hs]; ring
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast [ZMod.coe_valMinAbs]
  exact_mod_cast hzero

omit [NeZero q] in
/-- **Coefficient-extraction kernel.** A vanishing degree-`2^α` combination of powers of `ζ` (with
`ζ^{2^{α-1}} = s`, `s² = -1`, and `1,…,ζ^{2^{α-1}-1}` independent) yields, for each half-index
`j`, the integer divisibility `q ∣ (â_j² + â_{2^{α-1}+j}²)`. -/
theorem dvd_sq_add_sq (α : ℕ) (hα : 1 ≤ α) (ζ : F) (s : ZMod q)
    (hζ : ζ ^ (2 ^ (α - 1)) = algebraMap (ZMod q) F s) (hs : s ^ 2 = -1)
    (hindep : LinearIndependent (ZMod q) (fun i : Fin (2 ^ (α - 1)) ↦ ζ ^ (i : ℕ)))
    (a : ℕ → ZMod q)
    (hsum : ∑ k ∈ Finset.range (2 ^ α), algebraMap (ZMod q) F (a k) * ζ ^ k = 0)
    (j : ℕ) (hj : j < 2 ^ (α - 1)) :
    (q : ℤ) ∣ ((a j).valMinAbs ^ 2 + (a (2 ^ (α - 1) + j)).valMinAbs ^ 2) :=
  dvd_valMinAbs_sq_add_sq s (a j) (a (2 ^ (α - 1) + j)) hs
    (halfSum_coeff_eq_zero α hα ζ s hζ hindep a hsum j hj)

end Coeff

end ArkLib.Lattices.CyclotomicModulus
