/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.NormBounds.Basic

/-!
# The Micciancio/Young Product Norm-Growth Bound

The Young/Micciancio inequality `‖(c·d)·v‖₂² ≤ ‖d‖₁² · ‖c·v‖₂²` over the power-of-two
negacyclic convolution (`φ = X^{2^α} + 1`, `powTwoCyclotomic α`) with centered
representatives: scaling an already-`c`-scaled vector by a further ring element `d` of
bounded centered `ℓ₁` norm grows the squared `ℓ₂` norm by at most `κ²`.

The statement is pinned to `powTwoCyclotomic α`: the per-entry product bound
`‖d·w‖₂ ≤ ‖d‖₁·‖w‖₂` rests on multiplication-by-`X` being an `ℓ₂`-isometry on the
coefficient vector, which holds for the cyclic/negacyclic rings `X^n ∓ 1` of [Mic07] but
*fails* for a general cyclotomic `Φ_m` (e.g. in `ℤ[X]/(X²+X+1)`, `‖X·X‖₂ = √2 > ‖X‖₁·‖X‖₂`).
Phrasing this for an arbitrary `Φ` would therefore be unsound.

This is one of the two unproven lemmas for the Greyhound [NS24] / Hachi [NOZ26]
weak-binding argument. For the *cyclic* ring `X^n − 1`, Micciancio proves the analogous
convolution-norm bounds `‖f ⊗ g‖∞ ≤ ‖f‖₂·‖g‖₂` and `‖f ⊗ g‖∞ ≤ ‖f‖₁·‖g‖∞`
([Mic07, ineqs. (2.6)–(2.7)]). The `ℓ₂` bound `‖f·g‖₂ ≤ ‖f‖₁·‖g‖₂` proved here is the same
discrete Young / Cauchy–Schwarz convolution inequality, adapted sign-invariantly (via
`natAbs`) to the *negacyclic* ring `X^n + 1`; minimality of the centered representative
supplies the per-coefficient bound.

## References

* [Micciancio, D., *Generalized Compact Knapsacks, Cyclic Lattices, and Efficient One-Way
    Functions*][Mic07]
* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open scoped BigOperators

namespace ArkLib.Lattices.CyclotomicModulus

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] (α : ℕ)

/-- The power-of-two ("Hachi") cyclotomic modulus `X^{2^α}+1` over `ZMod q`. -/
local notation "Φ" => (powTwoCyclotomic (R := ZMod q) α)

section Helpers
open Polynomial Finset

/-- **Negacyclic two-block coefficient identity (Mathlib layer).** Reducing a polynomial `P`
of degree `< 2n` modulo the monic `X^n + 1` only mixes the two coefficient blocks `k` and
`n + k` (with the negacyclic sign): for `k < n`, `(P %ₘ (X^n+1)).coeff k = P.coeff k -
P.coeff (n + k)`. All higher blocks vanish because `deg P < 2n`. -/
private lemma coeff_modByMonic_X_pow_add_one {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
    (hn : 0 < n) (P : R[X]) (hP : P.natDegree < 2 * n) {k : ℕ} (hk : k < n) :
    (P %ₘ (X ^ n + 1)).coeff k = P.coeff k - P.coeff (n + k) := by
  set g : R[X] := X ^ n + 1 with hgdef
  have hg : g.Monic := by rw [hgdef, ← C_1]; exact monic_X_pow_add_C (1 : R) hn.ne'
  have hgdeg : g.degree = (n : ℕ) := by rw [hgdef, ← C_1]; exact degree_X_pow_add_C hn 1
  have hgnd : g.natDegree = n := by rw [hgdef, ← C_1]; exact natDegree_X_pow_add_C
  set Q : R[X] := P /ₘ g with hQdef
  have hsum : P %ₘ g + g * Q = P := modByMonic_add_div P g
  have hQnd : Q.natDegree < n := by
    have hh : Q.natDegree = P.natDegree - n := by rw [hQdef, natDegree_divByMonic P hg, hgnd]
    omega
  have hRrlt : (P %ₘ g).degree < (n : WithBot ℕ) := by
    rw [← hgdeg]; exact degree_modByMonic_lt P hg
  have hcoeff : ∀ m : ℕ, P.coeff m
      = (P %ₘ g).coeff m + ((if n ≤ m then Q.coeff (m - n) else 0) + Q.coeff m) := by
    intro m
    have hgQ : g * Q = Q * X ^ n + Q := by rw [hgdef]; ring
    have hP' : P = (P %ₘ g) + (Q * X ^ n + Q) := by rw [← hgQ, hsum]
    conv_lhs => rw [hP']
    rw [coeff_add, coeff_add, coeff_mul_X_pow']
  have hk' : ¬ n ≤ k := by omega
  have hPk := hcoeff k
  rw [if_neg hk'] at hPk
  have hPnk := hcoeff (n + k)
  rw [if_pos (Nat.le_add_right n k)] at hPnk
  have hRr0 : (P %ₘ g).coeff (n + k) = 0 :=
    coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hRrlt (by exact_mod_cast Nat.le_add_right n k))
  have hQ0 : Q.coeff (n + k) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hQnd (Nat.le_add_right n k))
  have hsub : n + k - n = k := by omega
  rw [hsub, hRr0, hQ0] at hPnk
  rw [hPk, hPnk]; ring

/-- **Weighted discrete Cauchy–Schwarz (integers).** For nonnegative weights `w`,
`(∑ wᵢ xᵢ)² ≤ (∑ wᵢ)·(∑ wᵢ xᵢ²)`. The engine behind the `‖·‖₁ · ‖·‖₂` product bound. -/
private lemma weighted_cauchy_schwarz {ι : Type*} (s : Finset ι) (w x : ι → ℤ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * x i) ^ 2 ≤ (∑ i ∈ s, w i) * (∑ i ∈ s, w i * x i ^ 2) := by
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s hw ?_ ?_
  · exact fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)
  · intro i hi
    nlinarith [hw i hi]

/-- **Negacyclic reindexing (the `ℓ₂`-isometry of multiplication by `X`).** The cyclic shift
`k ↦ (k + n - i) % n` is a bijection of `range n`, so it preserves the squared-`ℓ₂` sum. -/
private lemma negacyc_reindex {n : ℕ} {i : ℕ} (hi : i < n) (b : ℕ → ℤ) :
    ∑ k ∈ Finset.range n, b ((k + n - i) % n) ^ 2 = ∑ k ∈ Finset.range n, b k ^ 2 := by
  refine Finset.sum_nbij' (fun k => (k + n - i) % n) (fun m => (m + i) % n) ?_ ?_ ?_ ?_ ?_
  · intro a _; simp only [Finset.mem_range]; exact Nat.mod_lt _ (by omega)
  · intro a _; simp only [Finset.mem_range]; exact Nat.mod_lt _ (by omega)
  · intro a ha; simp only [Finset.mem_range] at ha
    change ((a + n - i) % n + i) % n = a
    by_cases h : i ≤ a
    · rw [show a + n - i = (a - i) + n by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (show a - i < n by omega), Nat.sub_add_cancel h, Nat.mod_eq_of_lt ha]
    · push Not at h
      rw [Nat.mod_eq_of_lt (show a + n - i < n by omega),
          show a + n - i + i = a + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt ha]
  · intro a ha; simp only [Finset.mem_range] at ha
    change ((a + i) % n + n - i) % n = a
    by_cases h : a + i < n
    · rw [Nat.mod_eq_of_lt h, show a + i + n - i = a + n by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt ha]
    · push Not at h
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (show a + i - n < n by omega),
          show a + i - n + n - i = a by omega, Nat.mod_eq_of_lt ha]
  · intro a _; rfl

omit [NeZero q] in
/-- The underlying polynomial of the modulus `Φ = X^{2^α}+1`. -/
private lemma hachi_toPoly :
    (Φ).φ.toPoly = (Polynomial.X : (ZMod q)[X]) ^ (2 ^ α) + 1 := by
  change (CompPoly.CPolynomial.X ^ (2 ^ α) + 1 : CompPoly.CPolynomial (ZMod q)).toPoly = _
  rw [CompPoly.CPolynomial.toPoly_add, CompPoly.CPolynomial.toPoly_pow,
      CompPoly.CPolynomial.toPoly_X, CompPoly.CPolynomial.toPoly_one]

omit [NeZero q] in
/-- The degree of the modulus is `2^α`. -/
private lemma hachi_natDegree : (Φ).φ.natDegree = 2 ^ α := by
  rw [CompPoly.CPolynomial.natDegree_toPoly, hachi_toPoly, ← Polynomial.C_1,
      Polynomial.natDegree_X_pow_add_C]

omit [NeZero q] in
/-- The Mathlib degree of the modulus equals its `natDegree` (cast). -/
private lemma hachi_degree : (Φ).φ.toPoly.degree = ((Φ).φ.natDegree : WithBot ℕ) := by
  rw [CompPoly.CPolynomial.natDegree_toPoly]
  refine Polynomial.degree_eq_natDegree ?_
  rw [hachi_toPoly, ← Polynomial.C_1]
  exact (monic_X_pow_add_C (1 : ZMod q) (pow_ne_zero α two_ne_zero)).ne_zero

omit [NeZero q] in
/-- **Two-block product-coefficient identity in `Rq`.** Specialization of
`coeff_modByMonic_X_pow_add_one` to the cyclotomic ring product `d * w`. -/
private lemma coeff_mul_rq_two_block (d w : Rq Φ) {k : ℕ} (hk : k < 2 ^ α) :
    (d * w).1.coeff k
      = (d.1.toPoly * w.1.toPoly).coeff k
        - (d.1.toPoly * w.1.toPoly).coeff (2 ^ α + k) := by
  have hmul : (d * w).1 = (Φ).reduce (d.1 * w.1) := rfl
  rw [hmul, CompPoly.CPolynomial.coeff_toPoly, (Φ).reduce_toPoly,
      CompPoly.CPolynomial.toPoly_mul, hachi_toPoly]
  have hdnd : d.1.toPoly.natDegree < 2 ^ α := by
    by_cases h : d.1.toPoly = 0
    · rw [h, Polynomial.natDegree_zero]; positivity
    · rw [Polynomial.natDegree_lt_iff_degree_lt h]
      calc d.1.toPoly.degree < (Φ).φ.toPoly.degree := (Φ).degree_toPoly_lt_of_reduced d.2
        _ = ((2 ^ α : ℕ) : WithBot ℕ) := by rw [hachi_degree, hachi_natDegree]
  have hwnd : w.1.toPoly.natDegree < 2 ^ α := by
    by_cases h : w.1.toPoly = 0
    · rw [h, Polynomial.natDegree_zero]; positivity
    · rw [Polynomial.natDegree_lt_iff_degree_lt h]
      calc w.1.toPoly.degree < (Φ).φ.toPoly.degree := (Φ).degree_toPoly_lt_of_reduced w.2
        _ = ((2 ^ α : ℕ) : WithBot ℕ) := by rw [hachi_degree, hachi_natDegree]
  refine coeff_modByMonic_X_pow_add_one (by positivity) _ ?_ hk
  calc (d.1.toPoly * w.1.toPoly).natDegree
      ≤ d.1.toPoly.natDegree + w.1.toPoly.natDegree := Polynomial.natDegree_mul_le
    _ < 2 * 2 ^ α := by omega

omit [NeZero q] in
/-- The integer convolution of the centered coefficient lifts casts back to the product
coefficient in `ZMod q`. -/
private lemma cast_conv (d w : Rq Φ) (m : ℕ) :
    ((∑ p ∈ Finset.antidiagonal m,
        (d.1.coeff p.1).valMinAbs * (w.1.coeff p.2).valMinAbs : ℤ) : ZMod q)
      = (d.1.toPoly * w.1.toPoly).coeff m := by
  rw [Polynomial.coeff_mul]
  push_cast [ZMod.coe_valMinAbs]
  apply Finset.sum_congr rfl
  intro p _
  rw [CompPoly.CPolynomial.coeff_toPoly, CompPoly.CPolynomial.coeff_toPoly]

/-- **Per-coefficient negacyclic bound.** The centered absolute value of a product coefficient
is bounded by the cyclic convolution of the centered absolute values of the factors. The
negacyclic sign is irrelevant since only `natAbs` upper bounds are taken. -/
private lemma natAbs_conv_le {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k < n)
    (A B : ℕ → ℤ) (hA : ∀ i, n ≤ i → A i = 0) (hB : ∀ j, n ≤ j → B j = 0) :
    ((∑ p ∈ Finset.antidiagonal k, A p.1 * B p.2)
        - ∑ p ∈ Finset.antidiagonal (n + k), A p.1 * B p.2).natAbs
      ≤ ∑ i ∈ Finset.range n, (A i).natAbs * (B ((k + n - i) % n)).natAbs := by
  have hbound : ((∑ p ∈ Finset.antidiagonal k, A p.1 * B p.2)
        - ∑ p ∈ Finset.antidiagonal (n + k), A p.1 * B p.2).natAbs
      ≤ (∑ i ∈ Finset.range (k + 1), (A i).natAbs * (B (k - i)).natAbs)
        + (∑ i ∈ Finset.range (n + k + 1), (A i).natAbs * (B (n + k - i)).natAbs) := by
    refine le_trans (Int.natAbs_sub_le _ _) (add_le_add ?_ ?_)
    · rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk (fun p => A p.1 * B p.2) k]
      refine le_trans (Int.natAbs_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
      rw [Int.natAbs_mul]
    · rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk (fun p => A p.1 * B p.2) (n + k)]
      refine le_trans (Int.natAbs_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
      rw [Int.natAbs_mul]
  refine le_trans hbound (le_of_eq ?_)
  rw [← Finset.sum_range_add_sum_Ico
        (fun i => (A i).natAbs * (B ((k + n - i) % n)).natAbs) (show k + 1 ≤ n by omega)]
  congr 1
  · apply Finset.sum_congr rfl; intro i hi
    rw [Finset.mem_range] at hi
    have hmod : (k + n - i) % n = k - i := by
      rw [show k + n - i = (k - i) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
  · rw [← Finset.sum_subset (s₁ := Finset.Ico (k + 1) n) (s₂ := Finset.range (n + k + 1))
          (by intro x hx; rw [Finset.mem_Ico] at hx; rw [Finset.mem_range]; omega)
          (by intro x hx hxni
              rw [Finset.mem_range] at hx
              rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hxni
              rcases hxni with h | h
              · rw [hB (n + k - x) (by omega), Int.natAbs_zero, mul_zero]
              · rw [hA x h, Int.natAbs_zero, zero_mul])]
    apply Finset.sum_congr rfl; intro i hi
    rw [Finset.mem_Ico] at hi
    have hmod : (k + n - i) % n = n + k - i := by
      rw [Nat.mod_eq_of_lt (show k + n - i < n by omega)]; omega
    rw [hmod]

/-- **Cauchy–Schwarz over the cyclic convolution.** Packages the weighted Cauchy–Schwarz and the
isometric reindexing into the squared `ℓ₂` product bound, given the per-coefficient bound `hc`. -/
private lemma sum_conv_sq_le {n : ℕ} (da wb c : ℕ → ℤ)
    (hda : ∀ i, 0 ≤ da i) (_hwb : ∀ j, 0 ≤ wb j) (hc0 : ∀ k, 0 ≤ c k)
    (hc : ∀ k ∈ Finset.range n, c k ≤ ∑ i ∈ Finset.range n, da i * wb ((k + n - i) % n)) :
    ∑ k ∈ Finset.range n, c k ^ 2
      ≤ (∑ i ∈ Finset.range n, da i) ^ 2 * ∑ j ∈ Finset.range n, wb j ^ 2 := by
  calc ∑ k ∈ Finset.range n, c k ^ 2
      ≤ ∑ k ∈ Finset.range n, (∑ i ∈ Finset.range n, da i * wb ((k + n - i) % n)) ^ 2 :=
        Finset.sum_le_sum fun k hk => pow_le_pow_left₀ (hc0 k) (hc k hk) 2
    _ ≤ ∑ k ∈ Finset.range n,
          (∑ i ∈ Finset.range n, da i) * ∑ i ∈ Finset.range n, da i * wb ((k + n - i) % n) ^ 2 :=
        Finset.sum_le_sum fun k _ =>
          weighted_cauchy_schwarz (Finset.range n) da (fun i => wb ((k + n - i) % n))
            (fun i _ => hda i)
    _ = (∑ i ∈ Finset.range n, da i)
          * ∑ k ∈ Finset.range n, ∑ i ∈ Finset.range n, da i * wb ((k + n - i) % n) ^ 2 := by
        rw [Finset.mul_sum]
    _ = (∑ i ∈ Finset.range n, da i)
          * ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range n, da i * wb ((k + n - i) % n) ^ 2 := by
        rw [Finset.sum_comm]
    _ = (∑ i ∈ Finset.range n, da i)
          * ∑ i ∈ Finset.range n, da i * ∑ k ∈ Finset.range n, wb ((k + n - i) % n) ^ 2 := by
        congr 1; apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
    _ = (∑ i ∈ Finset.range n, da i)
          * ∑ i ∈ Finset.range n, da i * ∑ j ∈ Finset.range n, wb j ^ 2 := by
        congr 1; apply Finset.sum_congr rfl; intro i hi
        rw [negacyc_reindex (Finset.mem_range.mp hi) wb]
    _ = (∑ i ∈ Finset.range n, da i)
          * ((∑ i ∈ Finset.range n, da i) * ∑ j ∈ Finset.range n, wb j ^ 2) := by
        rw [← Finset.sum_mul]
    _ = (∑ i ∈ Finset.range n, da i) ^ 2 * ∑ j ∈ Finset.range n, wb j ^ 2 := by ring

/-- **Per-entry product norm bound (Micciancio/Young, cf. [Mic07, ineqs. (2.6)–(2.7)]).**
Over the negacyclic ring `X^{2^α}+1`, `‖d·w‖₂² ≤ ‖d‖₁²·‖w‖₂²`. -/
theorem Rq.l2NormSq_mul_le (d w : Rq Φ) :
    Rq.l2NormSq Φ (d * w) ≤ (Rq.l1Norm Φ d) ^ 2 * Rq.l2NormSq Φ w := by
  have hAzero : ∀ i, 2 ^ α ≤ i → (d.1.coeff i).valMinAbs = 0 := by
    intro i hi
    have hc : d.1.coeff i = 0 := by
      rw [CompPoly.CPolynomial.coeff_toPoly]
      refine Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le ((Φ).degree_toPoly_lt_of_reduced d.2) ?_)
      rw [hachi_degree, hachi_natDegree]; exact_mod_cast hi
    rw [hc, ZMod.valMinAbs_zero]
  have hBzero : ∀ j, 2 ^ α ≤ j → (w.1.coeff j).valMinAbs = 0 := by
    intro j hj
    have hc : w.1.coeff j = 0 := by
      rw [CompPoly.CPolynomial.coeff_toPoly]
      refine Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le ((Φ).degree_toPoly_lt_of_reduced w.2) ?_)
      rw [hachi_degree, hachi_natDegree]; exact_mod_cast hj
    rw [hc, ZMod.valMinAbs_zero]
  have hc : ∀ k ∈ Finset.range (2 ^ α),
      (((d * w).1.coeff k).valMinAbs.natAbs : ℤ)
        ≤ ∑ i ∈ Finset.range (2 ^ α),
            ((d.1.coeff i).valMinAbs.natAbs : ℤ)
              * ((w.1.coeff ((k + 2 ^ α - i) % (2 ^ α))).valMinAbs.natAbs : ℤ) := by
    intro k hk
    have hkn : k < 2 ^ α := Finset.mem_range.mp hk
    have hnat : ((d * w).1.coeff k).valMinAbs.natAbs
        ≤ ∑ i ∈ Finset.range (2 ^ α),
            ((d.1.coeff i).valMinAbs).natAbs
              * ((w.1.coeff ((k + 2 ^ α - i) % (2 ^ α))).valMinAbs).natAbs := by
      refine le_trans (valMinAbs_natAbs_le
          ((∑ p ∈ Finset.antidiagonal k, (d.1.coeff p.1).valMinAbs * (w.1.coeff p.2).valMinAbs)
            - ∑ p ∈ Finset.antidiagonal (2 ^ α + k),
                (d.1.coeff p.1).valMinAbs * (w.1.coeff p.2).valMinAbs) ?_)
        (natAbs_conv_le (by positivity) k hkn
          (fun i => (d.1.coeff i).valMinAbs) (fun j => (w.1.coeff j).valMinAbs) hAzero hBzero)
      rw [Int.cast_sub, cast_conv (α := α) d w k, cast_conv (α := α) d w (2 ^ α + k),
          ← coeff_mul_rq_two_block (α := α) d w hkn]
    exact_mod_cast hnat
  have key := sum_conv_sq_le (n := 2 ^ α)
      (fun i => ((d.1.coeff i).valMinAbs.natAbs : ℤ))
      (fun j => ((w.1.coeff j).valMinAbs.natAbs : ℤ))
      (fun k => (((d * w).1.coeff k).valMinAbs.natAbs : ℤ))
      (fun i => by positivity) (fun j => by positivity) (fun k => by positivity) hc
  have e1 : (Rq.l2NormSq Φ (d * w) : ℤ)
      = ∑ k ∈ Finset.range (2 ^ α), (((d * w).1.coeff k).valMinAbs.natAbs : ℤ) ^ 2 := by
    simp only [Rq.l2NormSq]; rw [hachi_natDegree]; push_cast; rfl
  have e2 : (Rq.l1Norm Φ d : ℤ)
      = ∑ i ∈ Finset.range (2 ^ α), ((d.1.coeff i).valMinAbs.natAbs : ℤ) := by
    simp only [Rq.l1Norm]; rw [hachi_natDegree]; push_cast; rfl
  have e3 : (Rq.l2NormSq Φ w : ℤ)
      = ∑ j ∈ Finset.range (2 ^ α), ((w.1.coeff j).valMinAbs.natAbs : ℤ) ^ 2 := by
    simp only [Rq.l2NormSq]; rw [hachi_natDegree]; push_cast; rfl
  have hgoal : (Rq.l2NormSq Φ (d * w) : ℤ) ≤ ((Rq.l1Norm Φ d : ℤ)) ^ 2 * (Rq.l2NormSq Φ w : ℤ) := by
    rw [e1, e2, e3]; exact key
  exact_mod_cast hgoal

end Helpers

/-- **Micciancio/Young product bound.** Over the power-of-two cyclotomic modulus
`powTwoCyclotomic α` (`φ = X^{2^α}+1`), scaling an already-`c`-scaled vector by a further
ring element `d` of bounded centered `ℓ₁` norm grows the squared `ℓ₂` norm by at most `κ²`
(the honest Young/Micciancio inequality `‖(c·d)·v‖₂² ≤ ‖d‖₁² · ‖c·v‖₂²` over the negacyclic
convolution with centered representatives), via the per-entry product bound
`Rq.l2NormSq_mul_le`. -/
theorem scalarVecMul_mul_l2NormSq_le {cols : ℕ} (c d : Rq Φ) (v : PolyVec (Rq Φ) cols)
    {κ βSq : ℕ} (hd : Rq.l1Norm Φ d ≤ κ)
    (hv : vecL2NormSq Φ (scalarVecMul c v) ≤ βSq) :
    vecL2NormSq Φ (scalarVecMul (c * d) v) ≤ scalarVecMulMulL2NormSqBound κ βSq := by
  unfold vecL2NormSq scalarVecMulMulL2NormSqBound
  have hcomm : ∀ i, scalarVecMul (c * d) v i = d * scalarVecMul c v i := by
    intro i; simp only [scalarVecMul_apply]; ring
  calc ∑ i, Rq.l2NormSq Φ (scalarVecMul (c * d) v i)
      = ∑ i, Rq.l2NormSq Φ (d * scalarVecMul c v i) := by simp_rw [hcomm]
    _ ≤ ∑ i, (Rq.l1Norm Φ d) ^ 2 * Rq.l2NormSq Φ (scalarVecMul c v i) :=
        Finset.sum_le_sum fun i _ => Rq.l2NormSq_mul_le (α := α) d (scalarVecMul c v i)
    _ = (Rq.l1Norm Φ d) ^ 2 * ∑ i, Rq.l2NormSq Φ (scalarVecMul c v i) := by rw [← Finset.mul_sum]
    _ ≤ κ ^ 2 * βSq := Nat.mul_le_mul (Nat.pow_le_pow_left hd 2) hv

end ArkLib.Lattices.CyclotomicModulus
