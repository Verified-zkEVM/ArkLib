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

end MvPolynomial
