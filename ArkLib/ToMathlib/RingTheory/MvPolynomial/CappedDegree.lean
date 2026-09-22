/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.WeightAtMost
public import ArkLib.ToMathlib.RingTheory.MvPolynomial.MonomialMap

/-!
# Polynomials of bounded degree with a capped variable

Fix `i : σ`. The exponents `cappedDegreeExponents σ i b c` are the exponent vectors on `σ` of
degree at most `b` whose `i`-coordinate is at most `c`, and the polynomials supported on them form
the submodule `restrictCappedDegree σ R i b c`. For `b ≤ c` the cap is no condition, and these are
the exponents of degree at most `b`. For `σ = Fin 2`, `i = 1` and `c ≤ b` they form the truncated
triangle of the vectors `single 0 x + single 1 v` with `v ≤ c` and `x ≤ b - v`.

The two bounds add under addition of exponents, so the capped polynomials are closed under
multiplication, and the monomial map `monomialMap R (cappedDegreeExponents σ i b c)` sends
polynomials of total degree at most `N` to polynomials with bounds `(b * N, c * N)`. For positive
`b` and `c` the exponents `Finsupp.single v 1` are capped exponents, so the monomial map is
surjective and the statements on points in `ArkLib.ToMathlib.RingTheory.MvPolynomial.MonomialMap`
apply to it.

For `σ = Fin 2`, `i = 1` and `c ≤ b` there are `(c + 1) * (2 * b + 2 - c) / 2` capped exponents.
The convex hull of these exponents is the truncated triangle
`{(x, y) | 0 ≤ x, 0 ≤ y ≤ c, x + y ≤ b}`, and
`cappedDegreeMixedVolume j r b c = j * c + r * (b - c)` is the mixed volume of the truncated
triangles for `(j, r)` and `(b, c)` when `r ≤ j` and `c ≤ b`, normalized so that the mixed volume
of a triangle with itself is twice its area. It bounds the affine degree of the pullback of a curve
with bounds `(j, r)` along the monomial map
(`ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertCappedDegree`).

## Main statements

* `MvPolynomial.cappedDegreeExponents`, `MvPolynomial.restrictCappedDegree`: the capped exponents
  and polynomials.
* `MvPolynomial.mul_mem_restrictCappedDegree`: the bounds add under multiplication.
* `MvPolynomial.monomialMap_mem_restrictCappedDegree`: total degree `N` maps to bounds
  `(b * N, c * N)`.
* `MvPolynomial.single_mem_cappedDegreeExponents`,
  `MvPolynomial.monomialMap_cappedDegreeExponents_surjective`: the monomial map is surjective for
  positive bounds.
* `MvPolynomial.finrank_restrictCappedDegree`: the capped polynomials have rank the number of
  capped exponents.
* `MvPolynomial.cappedDegreeExponentsFinTwoEquiv`,
  `MvPolynomial.two_mul_ncard_cappedDegreeExponents_fin_two`: the truncated triangle for
  `σ = Fin 2` and its count.
* `MvPolynomial.cappedDegreeMixedVolume`: the mixed volume of two truncated triangles, with its
  monotonicity, symmetry and value on the diagonal.
-/

@[expose] public section

noncomputable section

open scoped Pointwise

namespace MvPolynomial

variable {σ R : Type*}

section Exponents

variable (σ) in
/-- The exponent vectors on `σ` of degree at most `b` whose `i`-coordinate is at most `c`. -/
def cappedDegreeExponents (i : σ) (b c : ℕ) : Set (σ →₀ ℕ) :=
  {e | e.degree ≤ b ∧ e i ≤ c}

variable {i : σ} {b c : ℕ}

/-- Membership in `cappedDegreeExponents σ i b c`. -/
theorem mem_cappedDegreeExponents {e : σ →₀ ℕ} :
    e ∈ cappedDegreeExponents σ i b c ↔ e.degree ≤ b ∧ e i ≤ c :=
  Iff.rfl

/-- Capped exponents have degree at most `b`. -/
theorem cappedDegreeExponents_subset_setOf_degree_le :
    cappedDegreeExponents σ i b c ⊆ {e | e.degree ≤ b} :=
  fun _ he ↦ he.1

/-- For `b ≤ c`, the cap is no condition: the capped exponents are the exponents of degree at most
`b`. -/
theorem cappedDegreeExponents_eq_setOf_degree_le (hbc : b ≤ c) :
    cappedDegreeExponents σ i b c = {e | e.degree ≤ b} :=
  Set.Subset.antisymm cappedDegreeExponents_subset_setOf_degree_le fun e he ↦
    ⟨he, ((Finsupp.le_degree i e).trans he).trans hbc⟩

/-- The zero exponent is a capped exponent. -/
theorem zero_mem_cappedDegreeExponents : 0 ∈ cappedDegreeExponents σ i b c := by
  simp [mem_cappedDegreeExponents]

/-- For positive `b` and `c`, the exponent `Finsupp.single v 1` is a capped exponent. -/
theorem single_mem_cappedDegreeExponents (hb : 0 < b) (hc : 0 < c) (v : σ) :
    Finsupp.single v 1 ∈ cappedDegreeExponents σ i b c := by
  classical
  refine ⟨by rwa [Finsupp.degree_single], ?_⟩
  rw [Finsupp.single_apply]
  split_ifs <;> omega

/-- The bounds of capped exponents add under addition. -/
theorem cappedDegreeExponents_add_subset (b' c' : ℕ) :
    cappedDegreeExponents σ i b c + cappedDegreeExponents σ i b' c' ⊆
      cappedDegreeExponents σ i (b + b') (c + c') := by
  rintro _ ⟨e, he, e', he', rfl⟩
  exact ⟨by simpa using Nat.add_le_add he.1 he'.1, by simpa using Nat.add_le_add he.2 he'.2⟩

/-- A sum of `N` capped exponents with bounds `(b, c)` has bounds `(b * N, c * N)`. -/
theorem nsmul_cappedDegreeExponents_subset (N : ℕ) :
    N • cappedDegreeExponents σ i b c ⊆ cappedDegreeExponents σ i (b * N) (c * N) := by
  induction N with
  | zero =>
    rw [zero_smul, Set.zero_subset]
    exact zero_mem_cappedDegreeExponents
  | succ N ih =>
    rw [succ_nsmul]
    exact (Set.add_subset_add ih subset_rfl).trans (cappedDegreeExponents_add_subset b c)

/-- The capped exponents form a finite set when `σ` is finite. -/
instance cappedDegreeExponents.finite [Finite σ] : Finite (cappedDegreeExponents σ i b c) :=
  ((Finsupp.finite_of_degree_le b).subset cappedDegreeExponents_subset_setOf_degree_le).to_subtype

end Exponents

section Submodule

variable [CommSemiring R] {i : σ} {b c : ℕ}

variable (σ R i b c) in
/-- The polynomials of total degree at most `b` whose degree in `X i` is at most `c`. -/
def restrictCappedDegree : Submodule R (MvPolynomial σ R) :=
  restrictSupport R (cappedDegreeExponents σ i b c)

/-- Membership in `restrictCappedDegree σ R i b c`, monomial by monomial. -/
theorem mem_restrictCappedDegree {P : MvPolynomial σ R} :
    P ∈ restrictCappedDegree σ R i b c ↔ ∀ e ∈ P.support, e.degree ≤ b ∧ e i ≤ c :=
  Iff.rfl

/-- The bounds of capped polynomials add under multiplication. -/
theorem mul_mem_restrictCappedDegree {b' c' : ℕ} {P Q : MvPolynomial σ R}
    (hP : P ∈ restrictCappedDegree σ R i b c) (hQ : Q ∈ restrictCappedDegree σ R i b' c') :
    P * Q ∈ restrictCappedDegree σ R i (b + b') (c + c') := by
  refine restrictSupport_mono R (cappedDegreeExponents_add_subset b' c') ?_
  rw [restrictSupport_add]
  exact Submodule.mul_mem_mul hP hQ

/-- `monomialMap R (cappedDegreeExponents σ i b c)` sends a polynomial of total degree at most `N`
to a polynomial with bounds `(b * N, c * N)`. -/
theorem monomialMap_mem_restrictCappedDegree {N : ℕ}
    {P : MvPolynomial (cappedDegreeExponents σ i b c) R} (hP : P.totalDegree ≤ N) :
    monomialMap R _ P ∈ restrictCappedDegree σ R i (b * N) (c * N) :=
  restrictSupport_mono R (nsmul_cappedDegreeExponents_subset N)
    (monomialMap_mem_restrictSupport_nsmul zero_mem_cappedDegreeExponents hP)

/-- For positive `b` and `c`, the monomial map of the capped exponents is surjective. -/
theorem monomialMap_cappedDegreeExponents_surjective (hb : 0 < b) (hc : 0 < c) :
    Function.Surjective (monomialMap R (cappedDegreeExponents σ i b c)) :=
  monomialMap_surjective (single_mem_cappedDegreeExponents hb hc)

/-- With finitely many variables, the capped polynomials form a finite module. -/
instance restrictCappedDegree.moduleFinite [Finite σ] :
    Module.Finite R (restrictCappedDegree σ R i b c) :=
  restrictSupport_finite (Set.toFinite _)

/-- The capped polynomials form a free module whose rank is the number of capped exponents. -/
theorem finrank_restrictCappedDegree {R : Type*} [CommRing R] [StrongRankCondition R]
    [Finite σ] :
    Module.finrank R (restrictCappedDegree σ R i b c) = (cappedDegreeExponents σ i b c).ncard := by
  rw [restrictCappedDegree, Module.finrank_eq_nat_card_basis (basisRestrictSupport R _),
    Nat.card_coe_set_eq]

end Submodule

section FinTwo

private theorem degree_fin_two (e : Fin 2 →₀ ℕ) : e.degree = e 0 + e 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

/-- For `c ≤ b`, splitting off the second coordinate identifies the capped exponents on `Fin 2`
with bounds `(b, c)` with the pairs `(v, x)` with `v ≤ c` and `x ≤ b - v`, via
`single 0 x + single 1 v`. -/
def cappedDegreeExponentsFinTwoEquiv (b c : ℕ) (hcb : c ≤ b) :
    cappedDegreeExponents (Fin 2) 1 b c ≃ Σ v : Fin (c + 1), Fin (b - v + 1) where
  toFun e :=
    ⟨⟨e.1 1, Nat.lt_succ_of_le e.2.2⟩, ⟨e.1 0, by
      have h := e.2.1
      rw [degree_fin_two] at h
      simp only
      omega⟩⟩
  invFun p :=
    ⟨Finsupp.single 0 p.2.val + Finsupp.single 1 p.1.val, by
      have h1 := p.1.isLt
      have h2 := p.2.isLt
      simp only [mem_cappedDegreeExponents, degree_fin_two, Finsupp.coe_add, Pi.add_apply,
        Finsupp.single_eq_same, ne_eq, zero_ne_one, not_false_eq_true, Finsupp.single_eq_of_ne,
        add_zero, one_ne_zero, zero_add]
      omega⟩
  left_inv e := by
    apply Subtype.ext
    ext j
    fin_cases j <;> simp
  right_inv p := by
    rcases p with ⟨⟨v, hv⟩, ⟨x, hx⟩⟩
    apply Sigma.ext
    · apply Fin.ext
      simp
    · apply (Fin.heq_ext_iff (by simp)).2
      simp

private theorem two_mul_sum_range_sub_add_one (b c : ℕ) (hcb : c ≤ b) :
    2 * ∑ v ∈ Finset.range (c + 1), (b - v + 1) = (c + 1) * (2 * b + 2 - c) := by
  induction c with
  | zero => simp; ring
  | succ c ih =>
    rw [Finset.sum_range_succ, mul_add, ih (by omega)]
    have h1 : c ≤ 2 * b + 2 := by omega
    have h2 : c + 1 ≤ b := hcb
    have h3 : c + 1 ≤ 2 * b + 2 := by omega
    zify [h1, h2, h3]
    ring

/-- For `c ≤ b`, there are `(c + 1) * (2 * b + 2 - c) / 2` capped exponents on `Fin 2` with
bounds `(b, c)`. -/
theorem two_mul_ncard_cappedDegreeExponents_fin_two (b c : ℕ) (hcb : c ≤ b) :
    2 * (cappedDegreeExponents (Fin 2) 1 b c).ncard = (c + 1) * (2 * b + 2 - c) := by
  rw [← Nat.card_coe_set_eq, Nat.card_congr (cappedDegreeExponentsFinTwoEquiv b c hcb),
    Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun v ↦ b - v + 1) (c + 1)]
  exact two_mul_sum_range_sub_add_one b c hcb

end FinTwo

section MixedVolume

/-- The mixed volume `j * c + r * (b - c)` of the truncated triangles
`{(x, y) | 0 ≤ x, 0 ≤ y ≤ r, x + y ≤ j}` and `{(x, y) | 0 ≤ x, 0 ≤ y ≤ c, x + y ≤ b}` for `r ≤ j`
and `c ≤ b`, normalized so that the mixed volume of a triangle with itself is twice its area. It is
the sum of the support values `j` and `r` of the first triangle in the directions `(1, 1)` and
`(0, 1)`, weighted by the lattice lengths `c` and `b - c` of the edges of the second triangle with
these outer normals. -/
def cappedDegreeMixedVolume (j r b c : ℕ) : ℕ :=
  j * c + r * (b - c)

variable {j r j' r' b c b' c' : ℕ}

/-- For `r ≤ j` and `c ≤ b`, the mixed volume is `(j - r) * c + r * b`. -/
theorem cappedDegreeMixedVolume_eq (hrj : r ≤ j) (hcb : c ≤ b) :
    cappedDegreeMixedVolume j r b c = (j - r) * c + r * b := by
  unfold cappedDegreeMixedVolume
  zify [hrj, hcb]
  ring

/-- For `r ≤ j` and `c ≤ b`, the mixed volume is symmetric in the two triangles. -/
theorem cappedDegreeMixedVolume_comm (hrj : r ≤ j) (hcb : c ≤ b) :
    cappedDegreeMixedVolume j r b c = cappedDegreeMixedVolume b c j r := by
  unfold cappedDegreeMixedVolume
  zify [hrj, hcb]
  ring

/-- For `c ≤ b`, the mixed volume of the truncated triangle with itself is `c * (2 * b - c)`,
twice its area. -/
theorem cappedDegreeMixedVolume_self (hcb : c ≤ b) :
    cappedDegreeMixedVolume b c b c = c * (2 * b - c) := by
  unfold cappedDegreeMixedVolume
  zify [hcb, show c ≤ 2 * b by omega]
  ring

/-- The mixed volume is monotone in the first triangle. -/
theorem cappedDegreeMixedVolume_mono_left (hj : j ≤ j') (hr : r ≤ r') :
    cappedDegreeMixedVolume j r b c ≤ cappedDegreeMixedVolume j' r' b c :=
  Nat.add_le_add (Nat.mul_le_mul_right c hj) (Nat.mul_le_mul_right (b - c) hr)

/-- For `r ≤ j`, the mixed volume is monotone in the second triangle among truncated triangles
with `c ≤ b`. -/
theorem cappedDegreeMixedVolume_mono_right (hrj : r ≤ j) (hcb : c ≤ b) (hc'b' : c' ≤ b')
    (hb : b ≤ b') (hc : c ≤ c') :
    cappedDegreeMixedVolume j r b c ≤ cappedDegreeMixedVolume j r b' c' := by
  rw [cappedDegreeMixedVolume_eq hrj hcb, cappedDegreeMixedVolume_eq hrj hc'b']
  exact Nat.add_le_add (Nat.mul_le_mul_left (j - r) hc) (Nat.mul_le_mul_left r hb)

/-- For `0 < c`, the mixed volume is at least `j`. -/
theorem le_cappedDegreeMixedVolume (hc : 0 < c) : j ≤ cappedDegreeMixedVolume j r b c := by
  unfold cappedDegreeMixedVolume
  have : j ≤ j * c := Nat.le_mul_of_pos_right j hc
  omega

end MixedVolume

end MvPolynomial
