/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.RingTheory.MvPolynomial.Bidegree
public import ArkLib.ToMathlib.RingTheory.MvPolynomial.CappedDegree

/-!
# Polynomials of bounded bidegree with a capped variable

As in `ArkLib.ToMathlib.RingTheory.MvPolynomial.Bidegree`, split the variables of
`MvPolynomial (Option σ) R` into `none` and the variables `some j`. Fix `i : σ`. The exponents
`cappedBidegreeExponents σ i a b c` are those of bidegree at most `(a, b)` whose exponent in
`some i` is at most `c`, and the polynomials supported on them form the submodule
`restrictCappedBidegree σ R i a b c`. For `b ≤ c` the cap is no condition, and these are the
exponents of bidegree at most `(a, b)`.

The three bounds add under addition of exponents, so the capped polynomials are closed under
multiplication, and the monomial map `monomialMap R (cappedBidegreeExponents σ i a b c)` sends
polynomials of total degree at most `N` to polynomials with bounds `(a * N, b * N, c * N)`. For
positive `a`, `b` and `c` the exponents `Finsupp.single v 1` are capped exponents, so the monomial
map is surjective.

Splitting off the `none`-coordinate identifies the capped exponents with pairs of an integer in
`[0, a]` and a capped exponent in `cappedDegreeExponents σ i b c`. For `σ = Fin 2`, `i = 1` and
`c ≤ b` their convex hull is the prism `[0, a] × T` over the truncated triangle `T` of
`cappedDegreeExponents (Fin 2) 1 b c`, and `cappedBidegreeMixedVolume h j r a b c` is the mixed
volume of one prism for `(h, j, r)` and two prisms for `(a, b, c)`, normalized so that the mixed
volume of a prism with itself is `3!` times its volume. It bounds the affine degree of the pullback
of a hypersurface with bounds `(h, j, r)` along the monomial map
(`ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertCappedBidegree`).

The bidegree map `bidegreeMap σ R a b` is the monomial map of `bidegreeExponents σ a b`, and the
exponents `Finsupp.single v 1` are exponents of bidegree at most `(a, b)` for positive `a` and `b`,
so the statements on points in `ArkLib.ToMathlib.RingTheory.MvPolynomial.MonomialMap` apply to it.

## Main statements

* `MvPolynomial.bidegreeMap_eq_monomialMap`, `MvPolynomial.single_mem_bidegreeExponents`: the
  bidegree map as a surjective monomial map.
* `MvPolynomial.cappedBidegreeExponents`, `MvPolynomial.restrictCappedBidegree`: the capped
  exponents and polynomials.
* `MvPolynomial.mul_mem_restrictCappedBidegree`: the bounds add under multiplication.
* `MvPolynomial.monomialMap_mem_restrictCappedBidegree`: total degree `N` maps to bounds
  `(a * N, b * N, c * N)`.
* `MvPolynomial.monomialMap_cappedBidegreeExponents_surjective`: the monomial map is surjective
  for positive bounds.
* `MvPolynomial.ncard_cappedBidegreeExponents`, `MvPolynomial.finrank_restrictCappedBidegree`: the
  count `(a + 1) * (cappedDegreeExponents σ i b c).ncard`.
* `MvPolynomial.cappedBidegreeMixedVolume`: the mixed volume of the prisms, with its
  monotonicity.
-/

@[expose] public section

noncomputable section

open scoped Pointwise

namespace MvPolynomial

variable {σ R : Type*}

section BidegreeMap

/-- `bidegreeMap σ R a b` is the monomial map of the exponents of bidegree at most `(a, b)`. -/
theorem bidegreeMap_eq_monomialMap [CommSemiring R] (a b : ℕ) :
    bidegreeMap σ R a b = monomialMap R (bidegreeExponents σ a b) :=
  rfl

/-- The zero exponent has bidegree at most `(a, b)`. -/
theorem zero_mem_bidegreeExponents (a b : ℕ) : (0 : Option σ →₀ ℕ) ∈ bidegreeExponents σ a b := by
  simp [mem_bidegreeExponents, Finsupp.some_zero]

/-- For positive `a` and `b`, the exponent `Finsupp.single v 1` has bidegree at most `(a, b)`. -/
theorem single_mem_bidegreeExponents {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (v : Option σ) :
    Finsupp.single v 1 ∈ bidegreeExponents σ a b := by
  rw [mem_bidegreeExponents]
  cases v with
  | none => simp [Finsupp.some_single_none]; omega
  | some j => simp [Finsupp.some_single_some]; omega

end BidegreeMap

section Exponents

variable (σ) in
/-- The exponent vectors on `Option σ` whose `none`-coordinate is at most `a`, whose
`some`-coordinates have total degree at most `b`, and whose `some i`-coordinate is at most `c`. -/
def cappedBidegreeExponents (i : σ) (a b c : ℕ) : Set (Option σ →₀ ℕ) :=
  {m | m none ≤ a ∧ m.some.degree ≤ b ∧ m (some i) ≤ c}

variable {i : σ} {a b c : ℕ}

/-- Membership in `cappedBidegreeExponents σ i a b c`. -/
theorem mem_cappedBidegreeExponents {m : Option σ →₀ ℕ} :
    m ∈ cappedBidegreeExponents σ i a b c ↔
      m none ≤ a ∧ m.some.degree ≤ b ∧ m (some i) ≤ c :=
  Iff.rfl

/-- Capped exponents have bidegree at most `(a, b)`. -/
theorem cappedBidegreeExponents_subset_bidegreeExponents :
    cappedBidegreeExponents σ i a b c ⊆ bidegreeExponents σ a b :=
  fun _ hm ↦ ⟨hm.1, hm.2.1⟩

/-- For `b ≤ c`, the cap is no condition: the capped exponents are the exponents of bidegree at
most `(a, b)`. -/
theorem cappedBidegreeExponents_eq_bidegreeExponents (hbc : b ≤ c) :
    cappedBidegreeExponents σ i a b c = bidegreeExponents σ a b :=
  Set.Subset.antisymm cappedBidegreeExponents_subset_bidegreeExponents fun _ hm ↦
    ⟨hm.1, hm.2, ((Finsupp.le_degree i _).trans hm.2).trans hbc⟩

/-- The zero exponent is a capped exponent. -/
theorem zero_mem_cappedBidegreeExponents : 0 ∈ cappedBidegreeExponents σ i a b c := by
  simp [mem_cappedBidegreeExponents, Finsupp.some_zero]

/-- For positive `a`, `b` and `c`, the exponent `Finsupp.single v 1` is a capped exponent. -/
theorem single_mem_cappedBidegreeExponents (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (v : Option σ) : Finsupp.single v 1 ∈ cappedBidegreeExponents σ i a b c := by
  refine ⟨(single_mem_bidegreeExponents ha hb v).1, (single_mem_bidegreeExponents ha hb v).2, ?_⟩
  classical
  rw [Finsupp.single_apply]
  split_ifs <;> omega

/-- The bounds of capped exponents add under addition. -/
theorem cappedBidegreeExponents_add_subset (a' b' c' : ℕ) :
    cappedBidegreeExponents σ i a b c + cappedBidegreeExponents σ i a' b' c' ⊆
      cappedBidegreeExponents σ i (a + a') (b + b') (c + c') := by
  rintro _ ⟨m, hm, m', hm', rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa using Nat.add_le_add hm.1 hm'.1
  · simpa [Finsupp.some_add] using Nat.add_le_add hm.2.1 hm'.2.1
  · simpa using Nat.add_le_add hm.2.2 hm'.2.2

/-- A sum of `N` capped exponents with bounds `(a, b, c)` has bounds `(a * N, b * N, c * N)`. -/
theorem nsmul_cappedBidegreeExponents_subset (N : ℕ) :
    N • cappedBidegreeExponents σ i a b c ⊆
      cappedBidegreeExponents σ i (a * N) (b * N) (c * N) := by
  induction N with
  | zero =>
    rw [zero_smul, Set.zero_subset]
    exact zero_mem_cappedBidegreeExponents
  | succ N ih =>
    rw [succ_nsmul]
    exact (Set.add_subset_add ih subset_rfl).trans (cappedBidegreeExponents_add_subset a b c)

variable (σ i a b c) in
/-- Splitting off the `none`-coordinate identifies the capped exponents with pairs of an integer
at most `a` and a capped exponent in `cappedDegreeExponents σ i b c`. -/
def cappedBidegreeExponentsEquiv :
    cappedBidegreeExponents σ i a b c ≃ Set.Iic a × cappedDegreeExponents σ i b c where
  toFun m := (⟨m.1 none, m.2.1⟩, ⟨m.1.some, m.2.2⟩)
  invFun p := ⟨p.2.1.optionElim p.1.1, by
    rw [mem_cappedBidegreeExponents, Finsupp.optionElim_apply_none, Finsupp.some_optionElim]
    exact ⟨p.1.2, p.2.2.1, by simpa using p.2.2.2⟩⟩
  left_inv m := Subtype.ext (Finsupp.optionElim_some m.1)
  right_inv p := Prod.ext (Subtype.ext (Finsupp.optionElim_apply_none _ _))
    (Subtype.ext (Finsupp.some_optionElim _ _))

/-- The capped exponents form a finite set when `σ` is finite. -/
instance cappedBidegreeExponents.finite [Finite σ] :
    Finite (cappedBidegreeExponents σ i a b c) :=
  Finite.Set.subset _ cappedBidegreeExponents_subset_bidegreeExponents

/-- There are `(a + 1)` times as many capped exponents as capped exponents in
`cappedDegreeExponents σ i b c`. -/
theorem ncard_cappedBidegreeExponents :
    (cappedBidegreeExponents σ i a b c).ncard =
      (a + 1) * (cappedDegreeExponents σ i b c).ncard := by
  rw [← Nat.card_coe_set_eq, Nat.card_congr (cappedBidegreeExponentsEquiv σ i a b c),
    Nat.card_prod, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card',
    Set.toFinset_Iic, Nat.card_Iic]

end Exponents

section Submodule

variable [CommSemiring R] {i : σ} {a b c : ℕ}

variable (σ R i a b c) in
/-- The polynomials of bidegree at most `(a, b)` whose exponent in `some i` is at most `c`. -/
def restrictCappedBidegree : Submodule R (MvPolynomial (Option σ) R) :=
  restrictSupport R (cappedBidegreeExponents σ i a b c)

/-- Membership in `restrictCappedBidegree σ R i a b c`, monomial by monomial. -/
theorem mem_restrictCappedBidegree {P : MvPolynomial (Option σ) R} :
    P ∈ restrictCappedBidegree σ R i a b c ↔
      ∀ m ∈ P.support, m none ≤ a ∧ m.some.degree ≤ b ∧ m (some i) ≤ c :=
  Iff.rfl

/-- Capped polynomials have bidegree at most `(a, b)`. -/
theorem restrictCappedBidegree_le_restrictBidegree :
    restrictCappedBidegree σ R i a b c ≤ restrictBidegree σ R a b :=
  restrictSupport_mono R cappedBidegreeExponents_subset_bidegreeExponents

/-- The bounds of capped polynomials add under multiplication. -/
theorem mul_mem_restrictCappedBidegree {a' b' c' : ℕ} {P Q : MvPolynomial (Option σ) R}
    (hP : P ∈ restrictCappedBidegree σ R i a b c)
    (hQ : Q ∈ restrictCappedBidegree σ R i a' b' c') :
    P * Q ∈ restrictCappedBidegree σ R i (a + a') (b + b') (c + c') := by
  refine restrictSupport_mono R (cappedBidegreeExponents_add_subset a' b' c') ?_
  rw [restrictSupport_add]
  exact Submodule.mul_mem_mul hP hQ

/-- `monomialMap R (cappedBidegreeExponents σ i a b c)` sends a polynomial of total degree at most
`N` to a polynomial with bounds `(a * N, b * N, c * N)`. -/
theorem monomialMap_mem_restrictCappedBidegree {N : ℕ}
    {P : MvPolynomial (cappedBidegreeExponents σ i a b c) R} (hP : P.totalDegree ≤ N) :
    monomialMap R _ P ∈ restrictCappedBidegree σ R i (a * N) (b * N) (c * N) :=
  restrictSupport_mono R (nsmul_cappedBidegreeExponents_subset N)
    (monomialMap_mem_restrictSupport_nsmul zero_mem_cappedBidegreeExponents hP)

/-- For positive `a`, `b` and `c`, the monomial map of the capped exponents is surjective. -/
theorem monomialMap_cappedBidegreeExponents_surjective (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Function.Surjective (monomialMap R (cappedBidegreeExponents σ i a b c)) :=
  monomialMap_surjective (single_mem_cappedBidegreeExponents ha hb hc)

/-- With finitely many variables, the capped polynomials form a finite module. -/
instance restrictCappedBidegree.moduleFinite [Finite σ] :
    Module.Finite R (restrictCappedBidegree σ R i a b c) :=
  restrictSupport_finite (Set.toFinite _)

/-- The capped polynomials form a free module of rank `(a + 1)` times the number of capped
exponents in `cappedDegreeExponents σ i b c`. -/
theorem finrank_restrictCappedBidegree {R : Type*} [CommRing R] [StrongRankCondition R]
    [Finite σ] :
    Module.finrank R (restrictCappedBidegree σ R i a b c) =
      (a + 1) * (cappedDegreeExponents σ i b c).ncard := by
  rw [restrictCappedBidegree, Module.finrank_eq_nat_card_basis (basisRestrictSupport R _),
    Nat.card_coe_set_eq, ncard_cappedBidegreeExponents]

end Submodule

section MixedVolume

/-- For `r ≤ j` and `c ≤ b`, the mixed volume of the prism `[0, h] × T` over the truncated
triangle `T` for `(j, r)` and two copies of the prism `[0, a] × T'` over the truncated triangle
`T'` for `(b, c)`, normalized so that the mixed volume of a prism with itself is `3!` times its
volume. It is `h` times the mixed volume of `T'` with itself plus `2 * a` times the mixed volume
of `T` and `T'`; for `c ≤ b` the first mixed volume is `c * (2 * b - c)`
(`cappedDegreeMixedVolume_self`). -/
def cappedBidegreeMixedVolume (h j r a b c : ℕ) : ℕ :=
  h * cappedDegreeMixedVolume b c b c + 2 * a * cappedDegreeMixedVolume j r b c

variable {h j r h' j' r' a b c a' b' c' : ℕ}

/-- For `c ≤ b`, the mixed volume is `h * c * (2 * b - c) + 2 * a * (j * c + r * (b - c))`. -/
theorem cappedBidegreeMixedVolume_eq (hcb : c ≤ b) :
    cappedBidegreeMixedVolume h j r a b c =
      h * c * (2 * b - c) + 2 * a * (j * c + r * (b - c)) := by
  rw [cappedBidegreeMixedVolume, cappedDegreeMixedVolume_self hcb, ← mul_assoc,
    cappedDegreeMixedVolume]

/-- The mixed volume is monotone in the first prism. -/
theorem cappedBidegreeMixedVolume_mono_left (hh : h ≤ h') (hj : j ≤ j') (hr : r ≤ r') :
    cappedBidegreeMixedVolume h j r a b c ≤ cappedBidegreeMixedVolume h' j' r' a b c :=
  Nat.add_le_add (Nat.mul_le_mul_right _ hh)
    (Nat.mul_le_mul_left _ (cappedDegreeMixedVolume_mono_left hj hr))

/-- For `r ≤ j`, the mixed volume is monotone in the second prism among prisms over truncated
triangles with `c ≤ b`. -/
theorem cappedBidegreeMixedVolume_mono_right (hrj : r ≤ j) (hcb : c ≤ b) (hc'b' : c' ≤ b')
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    cappedBidegreeMixedVolume h j r a b c ≤ cappedBidegreeMixedVolume h j r a' b' c' := by
  refine Nat.add_le_add (Nat.mul_le_mul_left h ?_) (Nat.mul_le_mul (by omega)
    (cappedDegreeMixedVolume_mono_right hrj hcb hc'b' hb hc))
  exact (cappedDegreeMixedVolume_mono_right hcb hcb hc'b' hb hc).trans
    (cappedDegreeMixedVolume_mono_left hb hc)

end MixedVolume

end MvPolynomial
