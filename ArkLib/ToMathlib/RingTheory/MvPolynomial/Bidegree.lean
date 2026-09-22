/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.WeightAtMost
public import ArkLib.ToMathlib.Combinatorics.Enumerative.MonomialCount
public import ArkLib.ToMathlib.MvPolynomial.OptionWeightedDegree

/-!
# Polynomials of bounded bidegree in `Option σ` variables

Split the variables of `MvPolynomial (Option σ) R` into the distinguished variable `none` and the
variables `some i`. A polynomial has bidegree at most `(a, b)` when each of its monomials has
exponent at most `a` in `none` and total degree at most `b` in the variables `some i`. These
polynomials form the submodule `restrictBidegree σ R a b`, spanned by the monomials whose exponents
lie in `bidegreeExponents σ a b`. Splitting off the `none`-coordinate identifies these exponents
with pairs of an integer in `[0, a]` and an exponent vector on `σ` of degree at most `b`, so with
`n = Nat.card σ` the submodule has rank `(a + 1) * (b + n).choose n`.

The monomials of bidegree at most `(a, b)` are the coordinates of the algebra map
`bidegreeMap σ R a b` from the polynomial ring in one variable per exponent of
`bidegreeExponents σ a b`, sending the variable of `m` to the monomial of exponent `m`. It sends
polynomials of total degree at most `N` to polynomials of bidegree at most `(a * N, b * N)`, and
it is surjective when `a` and `b` are positive, since the variables `none` and `some i` are then
among its coordinates. A polynomial of bidegree at most `(a, b)` has the preimage
`bidegreeLift`, of total degree at most `1`.

## Main statements

* `MvPolynomial.bidegreeExponents`, `MvPolynomial.restrictBidegree`: the exponents and the
  polynomials of bidegree at most `(a, b)`.
* `MvPolynomial.mem_restrictBidegree_iff_weightedTotalDegree_le`: membership through the two
  weighted degrees.
* `MvPolynomial.mul_mem_restrictBidegree`: bidegree bounds add under multiplication.
* `MvPolynomial.ncard_bidegreeExponents`, `MvPolynomial.finrank_restrictBidegree`: the count
  `(a + 1) * (b + n).choose n`.
* `MvPolynomial.bidegreeMap`, `MvPolynomial.bidegreeMap_surjective`: the monomial map and its
  surjectivity for positive `a` and `b`.
* `MvPolynomial.bidegreeMap_mem_restrictBidegree`: total degree `N` maps to bidegree
  `(a * N, b * N)`.
* `MvPolynomial.bidegreeLift`, `MvPolynomial.bidegreeMap_bidegreeLift`,
  `MvPolynomial.totalDegree_bidegreeLift_le_one`: the linear preimage.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

variable {σ R : Type*}

section Exponents

variable (σ) in
/-- The exponent vectors on `Option σ` whose `none`-coordinate is at most `a` and whose
`some`-coordinates have total degree at most `b`. -/
def bidegreeExponents (a b : ℕ) : Set (Option σ →₀ ℕ) :=
  {m | m none ≤ a ∧ m.some.degree ≤ b}

/-- Membership in `bidegreeExponents σ a b`. -/
theorem mem_bidegreeExponents {a b : ℕ} {m : Option σ →₀ ℕ} :
    m ∈ bidegreeExponents σ a b ↔ m none ≤ a ∧ m.some.degree ≤ b :=
  Iff.rfl

variable (σ) in
/-- Splitting off the `none`-coordinate identifies the exponents of bidegree at most `(a, b)`
with pairs of an integer at most `a` and an exponent vector on `σ` of degree at most `b`. -/
def bidegreeExponentsEquiv (a b : ℕ) :
    bidegreeExponents σ a b ≃ Set.Iic a × {e : σ →₀ ℕ | e.degree ≤ b} where
  toFun m := (⟨m.1 none, m.2.1⟩, ⟨m.1.some, m.2.2⟩)
  invFun p := ⟨p.2.1.optionElim p.1.1, by
    rw [mem_bidegreeExponents, Finsupp.optionElim_apply_none, Finsupp.some_optionElim]
    exact ⟨p.1.2, p.2.2⟩⟩
  left_inv m := Subtype.ext (Finsupp.optionElim_some m.1)
  right_inv p := Prod.ext (Subtype.ext (Finsupp.optionElim_apply_none _ _))
    (Subtype.ext (Finsupp.some_optionElim _ _))

/-- The exponents of bidegree at most `(a, b)` form a finite set when `σ` is finite. -/
instance bidegreeExponents.finite [Finite σ] (a b : ℕ) : Finite (bidegreeExponents σ a b) :=
  have : Finite {e : σ →₀ ℕ | e.degree ≤ b} := (Finsupp.finite_of_degree_le b).to_subtype
  Finite.of_equiv _ (bidegreeExponentsEquiv σ a b).symm

/-- With `n = Nat.card σ`, there are `(a + 1) * (b + n).choose n` exponents of bidegree at most
`(a, b)`. -/
theorem ncard_bidegreeExponents [Finite σ] (a b : ℕ) :
    (bidegreeExponents σ a b).ncard = (a + 1) * (b + Nat.card σ).choose (Nat.card σ) := by
  rw [← Nat.card_coe_set_eq, Nat.card_congr (bidegreeExponentsEquiv σ a b), Nat.card_prod,
    Nat.card_coe_set_eq, Nat.card_coe_set_eq, Finsupp.ncard_setOf_degree_le,
    Set.ncard_eq_toFinset_card', Set.toFinset_Iic, Nat.card_Iic]

end Exponents

section Submodule

variable [CommSemiring R]

variable (σ R) in
/-- The polynomials of bidegree at most `(a, b)`: each monomial has exponent at most `a` in
`none` and total degree at most `b` in the variables `some i`. -/
def restrictBidegree (a b : ℕ) : Submodule R (MvPolynomial (Option σ) R) :=
  restrictSupport R (bidegreeExponents σ a b)

/-- Membership in `restrictBidegree σ R a b`, monomial by monomial. -/
theorem mem_restrictBidegree {a b : ℕ} {P : MvPolynomial (Option σ) R} :
    P ∈ restrictBidegree σ R a b ↔ ∀ m ∈ P.support, m none ≤ a ∧ m.some.degree ≤ b :=
  Iff.rfl

/-- A polynomial has bidegree at most `(a, b)` exactly when its weighted degree for the weight
counting `none` is at most `a` and its weighted degree for the weight counting the variables
`some i` is at most `b`. -/
theorem mem_restrictBidegree_iff_weightedTotalDegree_le {a b : ℕ}
    {P : MvPolynomial (Option σ) R} :
    P ∈ restrictBidegree σ R a b ↔
      P.weightedTotalDegree (fun v ↦ v.elim 1 fun _ ↦ 0) ≤ a ∧
        P.weightedTotalDegree (fun v ↦ v.elim 0 fun _ ↦ 1) ≤ b := by
  simp only [mem_restrictBidegree, weightedTotalDegree, Finset.sup_le_iff,
    Finsupp.weight_elim_one_zero, Finsupp.weight_elim_zero_one]
  exact ⟨fun h ↦ ⟨fun m hm ↦ (h m hm).1, fun m hm ↦ (h m hm).2⟩,
    fun h m hm ↦ ⟨h.1 m hm, h.2 m hm⟩⟩

/-- Bidegree bounds add under multiplication. -/
theorem mul_mem_restrictBidegree {a b c d : ℕ} {P Q : MvPolynomial (Option σ) R}
    (hP : P ∈ restrictBidegree σ R a b) (hQ : Q ∈ restrictBidegree σ R c d) :
    P * Q ∈ restrictBidegree σ R (a + c) (b + d) := by
  rw [mem_restrictBidegree_iff_weightedTotalDegree_le] at hP hQ ⊢
  exact ⟨(weightedTotalDegree_mul_le _ P Q).trans (Nat.add_le_add hP.1 hQ.1),
    (weightedTotalDegree_mul_le _ P Q).trans (Nat.add_le_add hP.2 hQ.2)⟩

/-- With finitely many variables, the polynomials of bounded bidegree form a finite module. -/
instance restrictBidegree.moduleFinite [Finite σ] (a b : ℕ) :
    Module.Finite R (restrictBidegree σ R a b) :=
  restrictSupport_finite (Set.toFinite _)

/-- With `n = Nat.card σ`, the polynomials of bidegree at most `(a, b)` form a free module of rank
`(a + 1) * (b + n).choose n`. -/
theorem finrank_restrictBidegree {R : Type*} [CommRing R] [StrongRankCondition R] [Finite σ]
    (a b : ℕ) :
    Module.finrank R (restrictBidegree σ R a b) =
      (a + 1) * (b + Nat.card σ).choose (Nat.card σ) := by
  rw [restrictBidegree, Module.finrank_eq_nat_card_basis (basisRestrictSupport R _),
    Nat.card_coe_set_eq, ncard_bidegreeExponents]

end Submodule

section Map

variable [CommSemiring R]

variable (σ R) in
/-- The algebra map from the polynomial ring with one variable for each exponent of bidegree at
most `(a, b)` that sends the variable of `m` to the monomial of exponent `m`. -/
def bidegreeMap (a b : ℕ) :
    MvPolynomial (bidegreeExponents σ a b) R →ₐ[R] MvPolynomial (Option σ) R :=
  aeval fun m ↦ monomial m.1 1

/-- `bidegreeMap` sends the variable of `m` to the monomial of exponent `m`. -/
@[simp]
theorem bidegreeMap_X {a b : ℕ} (m : bidegreeExponents σ a b) :
    bidegreeMap σ R a b (X m) = monomial m.1 1 :=
  aeval_X _ _

/-- For positive `a` and `b`, the variables `none` and `some i` are coordinates of `bidegreeMap`,
so it is surjective. -/
theorem bidegreeMap_surjective {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Function.Surjective (bidegreeMap σ R a b) := by
  intro P
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨C c, by simp [bidegreeMap]⟩
  | add P Q hP hQ =>
    obtain ⟨P', rfl⟩ := hP
    obtain ⟨Q', rfl⟩ := hQ
    exact ⟨P' + Q', map_add _ _ _⟩
  | mul_X P i hP =>
    obtain ⟨P', rfl⟩ := hP
    have hi : Finsupp.single i 1 ∈ bidegreeExponents σ a b := by
      rw [mem_bidegreeExponents]
      cases i with
      | none => simp [Finsupp.some_single_none]; omega
      | some i => simp [Finsupp.some_single_some]; omega
    exact ⟨P' * X ⟨_, hi⟩, by rw [map_mul, bidegreeMap_X, X]⟩

/-- `bidegreeMap` sends a polynomial of total degree at most `N` to a polynomial of bidegree at
most `(a * N, b * N)`. -/
theorem bidegreeMap_mem_restrictBidegree {a b N : ℕ}
    {P : MvPolynomial (bidegreeExponents σ a b) R} (hP : P.totalDegree ≤ N) :
    bidegreeMap σ R a b P ∈ restrictBidegree σ R (a * N) (b * N) := by
  have key (w : Option σ → ℕ) (c : ℕ) (hw : ∀ m : bidegreeExponents σ a b, m.1.weight w ≤ c) :
      (bidegreeMap σ R a b P).weightedTotalDegree w ≤ c * N := by
    refine (weightedTotalDegree_aeval_le_of_le (fun _ ↦ c) w _ P fun m ↦ ?_).trans ?_
    · exact (Finset.sup_le fun d hd ↦ by
        rw [Finset.mem_singleton.mp (support_monomial_subset hd)]; exact hw m)
    · refine Finset.sup_le fun d hd ↦ ?_
      have hd' : d.weight (fun _ ↦ c) = c * d.degree := by
        rw [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum, Finset.mul_sum]
        simp [mul_comm]
      rw [hd']
      exact Nat.mul_le_mul_left c ((le_totalDegree hd).trans hP)
  rw [mem_restrictBidegree_iff_weightedTotalDegree_le]
  exact ⟨key _ a fun m ↦ by simpa using m.2.1, key _ b fun m ↦ by simpa using m.2.2⟩

/-- The preimage under `bidegreeMap` of a polynomial of bidegree at most `(a, b)` that replaces
each monomial by the variable of its exponent. -/
def bidegreeLift {a b : ℕ} (P : MvPolynomial (Option σ) R) (hP : P ∈ restrictBidegree σ R a b) :
    MvPolynomial (bidegreeExponents σ a b) R :=
  ∑ m : P.support, C (P.coeff m) * X ⟨m, hP m.2⟩

/-- `bidegreeLift` is a preimage under `bidegreeMap`. -/
theorem bidegreeMap_bidegreeLift {a b : ℕ} (P : MvPolynomial (Option σ) R)
    (hP : P ∈ restrictBidegree σ R a b) :
    bidegreeMap σ R a b (bidegreeLift P hP) = P := by
  classical
  simp only [bidegreeLift, map_sum, map_mul, bidegreeMap, aeval_C, aeval_X, algebraMap_eq,
    C_mul_monomial, mul_one]
  rw [Finset.sum_coe_sort P.support fun m ↦ monomial m (P.coeff m)]
  exact P.support_sum_monomial_coeff

/-- `bidegreeLift` is a linear polynomial. -/
theorem totalDegree_bidegreeLift_le_one {a b : ℕ} (P : MvPolynomial (Option σ) R)
    (hP : P ∈ restrictBidegree σ R a b) :
    (bidegreeLift P hP).totalDegree ≤ 1 := by
  classical
  refine totalDegree_finsetSum_le fun m _ ↦ (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact (totalDegree_monomial_le _ _).trans_eq (Finsupp.degree_single _ _)

end Map

end MvPolynomial
