/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.MvPolynomial.CappedDegree

/-!
# Acceptance tests for polynomials of bounded degree with a capped variable

The examples state the point statements for the capped monomial map as instances of those for
monomial maps, count capped exponents on `Fin 2` and compute a dimension, state the dimension in
the form `(c + 1) * (b + 1) - c * (c + 1) / 2`, check that the cap is no condition when it exceeds
the bound on the degree, derive the total-degree and `X 1`-degree bounds of the monomial map and
the linear lift, and show that surjectivity of the monomial map needs a positive cap and that the
count on `Fin 2` needs `c ≤ b`. The mixed volume examples compute small values, check the
decomposition of the doubled area of a sum of truncated triangles, derive the triangle bounds in
the form `2 * b * c - c ^ 2`, and show that the hypotheses of the lemmas are needed.
-/

open MvPolynomial

namespace CappedDegreeTest

section CappedDegreePoints

variable {σ k E : Type*} [Field k] [Field E] [Algebra k E] {i : σ} {b c : ℕ}

/-- The coordinate of the point of monomial values at a capped exponent `m` is the value of the
monomial of exponent `m`. -/
example (x : σ → E) (m : cappedDegreeExponents σ i b c) :
    monomialPoint _ x m = aeval x (monomial m.1 (1 : k)) := by
  rw [monomialPoint_apply, aeval_monomial, map_one, one_mul]

/-- Evaluation at the point of monomial values is evaluation after the capped monomial map. -/
example (x : σ → E) (P : MvPolynomial (cappedDegreeExponents σ i b c) k) :
    aeval (monomialPoint _ x) P = aeval x (monomialMap k _ P) :=
  aeval_monomialPoint x P

/-- The linear lift of a capped polynomial has total degree at most `1` and vanishes at the point
of monomial values of `x` exactly when the polynomial vanishes at `x`. -/
example (x : σ → E) (q : MvPolynomial σ k) (hq : q ∈ restrictCappedDegree σ k i b c) :
    (monomialLift (S := cappedDegreeExponents σ i b c) q hq).totalDegree ≤ 1 ∧
      (aeval (monomialPoint _ x) (monomialLift (S := cappedDegreeExponents σ i b c) q hq) = 0 ↔
        aeval x q = 0) := by
  have hlift := monomialMap_monomialLift (R := k) (S := cappedDegreeExponents σ i b c) q hq
  refine ⟨totalDegree_monomialLift_le_one q hq, ?_⟩
  rw [aeval_monomialPoint, hlift]

/-- For positive bounds, the point of monomial values of `x` lies on the pullback of the
hypersurface `g = 0` along the capped monomial map exactly when `g` vanishes at `x`. -/
example (hb : 0 < b) (hc : 0 < c) (g : MvPolynomial σ k) (x : σ → E) :
    monomialPoint _ x ∈ zeroLocus E
        ((Ideal.span {g}).comap (monomialMap k (cappedDegreeExponents σ i b c))) ↔
      aeval x g = 0 := by
  rw [monomialPoint_mem_zeroLocus_comap_iff (single_mem_cappedDegreeExponents hb hc),
    zeroLocus_span]
  simp

/-- For positive bounds, the same statement with the zero locus of `span {g}` on the right. -/
example (hb : 0 < b) (hc : 0 < c) (g : MvPolynomial σ k) (x : σ → E) :
    monomialPoint _ x ∈ zeroLocus E
        ((Ideal.span {g}).comap (monomialMap k (cappedDegreeExponents σ i b c))) ↔
      x ∈ zeroLocus E (Ideal.span {g}) :=
  monomialPoint_mem_zeroLocus_comap_iff (single_mem_cappedDegreeExponents hb hc) _ x

/-- For positive bounds, every point of the zero locus of the kernel of the capped monomial map is
a point of monomial values. -/
example (hb : 0 < b) (hc : 0 < c) (z : cappedDegreeExponents σ i b c → E)
    (hz : z ∈ zeroLocus E (RingHom.ker (monomialMap k (cappedDegreeExponents σ i b c)))) :
    ∃ x : σ → E, monomialPoint _ x = z :=
  exists_monomialPoint_eq_of_mem_zeroLocus_ker (single_mem_cappedDegreeExponents hb hc) hz

/-- For positive bounds, a point is determined by its point of capped monomial values. -/
example (hb : 0 < b) (hc : 0 < c) :
    Function.Injective (monomialPoint (E := E) (cappedDegreeExponents σ i b c)) :=
  monomialPoint_injective (single_mem_cappedDegreeExponents hb hc)

end CappedDegreePoints

/-- In two variables with cap `1` on the second, there are `5` exponents of degree at most `2`:
`1`, `x₀`, `x₀ ^ 2`, `x₁` and `x₀ * x₁`. -/
example : (cappedDegreeExponents (Fin 2) 1 2 1).ncard = 5 := by
  have h := two_mul_ncard_cappedDegreeExponents_fin_two 2 1 (by norm_num)
  omega

/-- The corresponding polynomials form a space of dimension `5`. -/
example : Module.finrank ℚ (restrictCappedDegree (Fin 2) ℚ 1 2 1) = 5 := by
  have h := two_mul_ncard_cappedDegreeExponents_fin_two 2 1 (by norm_num)
  rw [finrank_restrictCappedDegree]
  omega

/-- For `c ≤ b`, the capped polynomials on `Fin 2` have dimension
`(c + 1) * (b + 1) - c * (c + 1) / 2`. -/
example {k : Type*} [Field k] (b c : ℕ) (hcb : c ≤ b) :
    Module.finrank k (restrictCappedDegree (Fin 2) k 1 b c) =
      (c + 1) * (b + 1) - c * (c + 1) / 2 := by
  have h := two_mul_ncard_cappedDegreeExponents_fin_two b c hcb
  rw [finrank_restrictCappedDegree]
  have hdiv : c * (c + 1) / 2 * 2 = c * (c + 1) :=
    Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.even_mul_succ_self c))
  zify [show c * (c + 1) / 2 ≤ (c + 1) * (b + 1) by nlinarith,
    show c ≤ 2 * b + 2 by omega] at h hdiv ⊢
  nlinarith

/-- A cap at least the bound on the degree is no condition. -/
example {σ : Type*} (i : σ) (b : ℕ) :
    cappedDegreeExponents σ i b (b + 1) = {e | e.degree ≤ b} :=
  cappedDegreeExponents_eq_setOf_degree_le (Nat.le_succ b)

/-- The bounds of a product of capped polynomials add. -/
example {P Q : MvPolynomial (Fin 2) ℚ} (hP : P ∈ restrictCappedDegree (Fin 2) ℚ 1 2 1)
    (hQ : Q ∈ restrictCappedDegree (Fin 2) ℚ 1 1 1) :
    P * Q ∈ restrictCappedDegree (Fin 2) ℚ 1 3 2 :=
  mul_mem_restrictCappedDegree hP hQ

/-- The monomial map of the capped exponents multiplies total degree by at most `b`. -/
example {k : Type*} [Field k] (b c : ℕ)
    (P : MvPolynomial (cappedDegreeExponents (Fin 2) 1 b c) k) :
    (monomialMap k _ P).totalDegree ≤ b * P.totalDegree :=
  Finset.sup_le fun _ he ↦ (monomialMap_mem_restrictCappedDegree le_rfl he).1

/-- The monomial map of the capped exponents multiplies total degree into `X 1`-degree at most
`c`. -/
example {k : Type*} [Field k] (b c : ℕ)
    (P : MvPolynomial (cappedDegreeExponents (Fin 2) 1 b c) k) :
    (monomialMap k _ P).degreeOf 1 ≤ c * P.totalDegree :=
  degreeOf_le_iff.mpr fun _ he ↦ (monomialMap_mem_restrictCappedDegree le_rfl he).2

/-- A capped polynomial has a linear preimage under the monomial map. -/
example {k : Type*} [Field k] (b c : ℕ) (P : MvPolynomial (Fin 2) k)
    (hP : P ∈ restrictCappedDegree (Fin 2) k 1 b c) :
    monomialMap k _ (monomialLift P hP) = P ∧ (monomialLift P hP).totalDegree ≤ 1 :=
  ⟨monomialMap_monomialLift P hP, totalDegree_monomialLift_le_one P hP⟩

/-- `monomialMap_cappedDegreeExponents_surjective` needs `0 < c`: with cap `0` no exponent
involves `1`, so the points `0` and `Pi.single 1 1` have the same point of monomial values, and
`X 1` is not in the image. -/
example : ¬Function.Surjective (monomialMap ℚ (cappedDegreeExponents (Fin 2) 1 1 0)) := by
  intro h
  obtain ⟨P, hP⟩ := h (X 1)
  have hpt : monomialPoint (cappedDegreeExponents (Fin 2) 1 1 0) (0 : Fin 2 → ℚ) =
      monomialPoint _ (Pi.single 1 1) := funext fun m ↦ by
    rw [monomialPoint_apply, monomialPoint_apply]
    refine Finsupp.prod_congr fun v hv ↦ ?_
    have hv1 : v ≠ 1 := by
      rintro rfl
      exact Finsupp.mem_support_iff.mp hv (Nat.le_zero.mp m.2.2)
    rw [Pi.single_eq_of_ne hv1, Pi.zero_apply]
  have h0 := aeval_monomialPoint (R := ℚ) (0 : Fin 2 → ℚ) P
  have h1 := aeval_monomialPoint (R := ℚ) (Pi.single 1 (1 : ℚ)) P
  rw [hP, aeval_X] at h0 h1
  rw [hpt, h1] at h0
  simp at h0

/-- `two_mul_ncard_cappedDegreeExponents_fin_two` needs `c ≤ b`: for `b = 1` and `c = 3` the cap is
no condition, so there are `3` capped exponents, while `(c + 1) * (2 * b + 2 - c) = 4` is not
`2 * 3`. -/
example : 2 * (cappedDegreeExponents (Fin 2) 1 1 3).ncard ≠ (3 + 1) * (2 * 1 + 2 - 3) := by
  rw [cappedDegreeExponents_eq_setOf_degree_le (by norm_num), Finsupp.ncard_setOf_degree_le,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

section MixedVolume

/-- In `ℕ`, `c * (2 * b - c) = 2 * b * c - c ^ 2`. -/
theorem mul_two_mul_sub_eq (b c : ℕ) : c * (2 * b - c) = 2 * b * c - c ^ 2 := by
  rw [Nat.mul_sub, sq, mul_comm c (2 * b)]

/-- The truncated triangles for `(3, 1)` and `(2, 1)` have mixed volume `3 * 1 + 1 * 1 = 4`. -/
example : cappedDegreeMixedVolume 3 1 2 1 = 4 := rfl

/-- The truncated triangle with vertices `(0, 0)`, `(2, 0)`, `(1, 1)` and `(0, 1)` has area `3 / 2`,
and its mixed volume with itself is `3`. -/
example : cappedDegreeMixedVolume 2 1 2 1 = 3 := rfl

/-- The Minkowski sum of the truncated triangles for `(j, r)` and `(b, c)` is the truncated
triangle for `(j + b, r + c)`, and twice its area decomposes into mixed volumes. -/
example {j r b c : ℕ} (hrj : r ≤ j) (hcb : c ≤ b) :
    cappedDegreeMixedVolume (j + b) (r + c) (j + b) (r + c) =
      cappedDegreeMixedVolume j r j r + 2 * cappedDegreeMixedVolume j r b c +
        cappedDegreeMixedVolume b c b c := by
  rw [cappedDegreeMixedVolume_self (by omega), cappedDegreeMixedVolume_self hrj,
    cappedDegreeMixedVolume_self hcb, cappedDegreeMixedVolume]
  zify [hcb, show r ≤ 2 * j by omega, show c ≤ 2 * b by omega,
    show r + c ≤ 2 * (j + b) by omega]
  ring

/-- For `c ≤ b`, the mixed volume of the truncated triangle with itself is `2 * b * c - c ^ 2`. -/
example {b c : ℕ} (hcb : c ≤ b) : cappedDegreeMixedVolume b c b c = 2 * b * c - c ^ 2 := by
  rw [cappedDegreeMixedVolume_self hcb, mul_two_mul_sub_eq]

/-- For `0 < c ≤ b`, `b ≤ 2 * b * c - c ^ 2`. -/
example {b c : ℕ} (hc : 0 < c) (hcb : c ≤ b) : b ≤ 2 * b * c - c ^ 2 := by
  have h := le_cappedDegreeMixedVolume (j := b) (r := c) (b := b) hc
  rwa [cappedDegreeMixedVolume_self hcb, mul_two_mul_sub_eq] at h

/-- `2 * b * c - c ^ 2` is monotone among truncated triangles with `c ≤ b`. -/
example {b c b' c' : ℕ} (hcb : c ≤ b) (hc'b' : c' ≤ b') (hb : b ≤ b') (hc : c ≤ c') :
    2 * b * c - c ^ 2 ≤ 2 * b' * c' - c' ^ 2 := by
  have h := (cappedDegreeMixedVolume_mono_right hcb hcb hc'b' hb hc).trans
    (cappedDegreeMixedVolume_mono_left (r := c) (b := b') (c := c') hb hc)
  rwa [cappedDegreeMixedVolume_self hcb, cappedDegreeMixedVolume_self hc'b', mul_two_mul_sub_eq,
    mul_two_mul_sub_eq] at h

/-- `cappedDegreeMixedVolume_eq` needs `r ≤ j`: the mixed volume for `(0, 1)` and `(2, 1)` is `1`,
while `(j - r) * c + r * b = 2`. -/
example : cappedDegreeMixedVolume 0 1 2 1 ≠ (0 - 1) * 1 + 1 * 2 := by decide

/-- `cappedDegreeMixedVolume_eq` needs `c ≤ b`: the mixed volume for `(1, 1)` and `(0, 1)` is `1`,
while `(j - r) * c + r * b = 0`. -/
example : cappedDegreeMixedVolume 1 1 0 1 ≠ (1 - 1) * 1 + 1 * 0 := by decide

/-- `cappedDegreeMixedVolume_comm` needs `r ≤ j`: the mixed volume for `(0, 1)` and `(1, 1)` is
`1 * 0 = 0`, while swapping gives `0 * 1 + 1 * 1 = 1`. -/
example : cappedDegreeMixedVolume 0 1 1 1 ≠ cappedDegreeMixedVolume 1 1 0 1 := by decide

/-- `cappedDegreeMixedVolume_mono_right` needs `r ≤ j`: for `(j, r) = (0, 1)`, raising `(1, 0)` to
`(1, 1)` lowers the value from `1` to `0`. -/
example : ¬cappedDegreeMixedVolume 0 1 1 0 ≤ cappedDegreeMixedVolume 0 1 1 1 := by decide

/-- `le_cappedDegreeMixedVolume` needs `0 < c`: for `c = 0` and `r = 0` the value is `0 < j`. -/
example : ¬1 ≤ cappedDegreeMixedVolume 1 0 1 0 := by decide

end MixedVolume

end CappedDegreeTest
