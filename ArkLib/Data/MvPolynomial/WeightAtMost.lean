/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Justin Thaler
-/
module

public import ArkLib.Data.MvPolynomial.WeightedDegree
public import Mathlib.Algebra.Order.Group.Int
public import ArkLib.ToMathlib.Finsupp.Weight
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Weight upper bounds with values in an ordered monoid

`ArkLib.Data.MvPolynomial.WeightedDegree` bounds the natural-number weights of the monomials of a
polynomial. This file allows the weight to take values in any ordered additive commutative
monoid `M`, so that a variable may have negative weight when `M = ℤ`. A bound such as
`e U - e T ≤ 0` is then a weight bound for the weight `T ↦ -1, U ↦ 1`, and it is preserved by
products and substitutions exactly as a degree bound is.

* `restrictWeightAtMost w a` is the submodule of polynomials each of whose monomials has
  `w`-weight at most `a`. For `M = ℕ` it is `restrictWeightedDegree w a`.

The file also records three facts about `restrictSupport`: its canonical basis vectors are
monomials, and for a finite exponent set it is a finite module whose dimension over a field is
the number of exponents.

## Main statements

* `mul_mem_restrictWeightAtMost`, `pow_mem_restrictWeightAtMost`: weight bounds add under
  products.
* `bind₁_mem_restrictWeightAtMost`: substitution preserves weight bounds when each generator image
  is bounded by the weight of its variable.
* `degreeOf_le_div_of_mem_restrictWeightAtMost`: a natural-number weight bound `a` bounds the
  degree in a variable of positive weight `w i` by `a / w i`.
* `coe_basisRestrictSupport_apply`: the basis vector at `e` is `monomial e 1`.
* `finrank_restrictSupport_finset`: the coefficient space of a finite exponent set has
  dimension its cardinality.
-/

@[expose] public section

noncomputable section

open Finsupp
open scoped Pointwise

namespace MvPolynomial

variable {σ τ R M : Type*} [CommSemiring R]
variable [AddCommMonoid M] [PartialOrder M]

/-- The polynomials all of whose monomials have `w`-weight at most `a`, for a weight with values
in an ordered additive monoid. -/
def restrictWeightAtMost (w : σ → M) (a : M) : Submodule R (MvPolynomial σ R) :=
  restrictSupport R {e | e.weight w ≤ a}

/-- Membership is the pointwise weight bound on the support. -/
theorem mem_restrictWeightAtMost {w : σ → M} {a : M} {p : MvPolynomial σ R} :
    p ∈ restrictWeightAtMost (R := R) w a ↔ ∀ e ∈ p.support, e.weight w ≤ a :=
  Iff.rfl

/-- For natural-number weights this is the weighted-degree submodule. -/
theorem restrictWeightAtMost_eq_restrictWeightedDegree (w : σ → ℕ) (a : ℕ) :
    restrictWeightAtMost (R := R) w a = restrictWeightedDegree w a :=
  rfl

/-- Relaxing the bound enlarges the submodule. -/
theorem restrictWeightAtMost_mono (w : σ → M) {a b : M} (hab : a ≤ b) :
    restrictWeightAtMost (R := R) w a ≤ restrictWeightAtMost (R := R) w b :=
  restrictSupport_mono R fun _ he => le_trans he hab

/-- A monomial satisfies the bound exactly when its exponent does, unless its coefficient is
zero. -/
@[simp]
theorem monomial_mem_restrictWeightAtMost (w : σ → M) (a : M) (e : σ →₀ ℕ) (r : R) :
    monomial e r ∈ restrictWeightAtMost (R := R) w a ↔ e.weight w ≤ a ∨ r = 0 :=
  monomial_mem_restrictSupport (R := R) (s := {e | e.weight w ≤ a})

/-- A constant has weight zero, so it satisfies every nonnegative bound. The bound must be
nonnegative: with `M = ℤ` and `a = -1`, the constant `1` is not in the submodule. -/
theorem C_mem_restrictWeightAtMost (w : σ → M) {a : M} (ha : 0 ≤ a) (r : R) :
    C r ∈ restrictWeightAtMost (R := R) w a := by
  rw [← monomial_zero', monomial_mem_restrictWeightAtMost]
  simp [ha]

/-- The variable `X i` satisfies every bound at least its weight. -/
theorem X_mem_restrictWeightAtMost (w : σ → M) {a : M} (i : σ) (hi : w i ≤ a) :
    X i ∈ restrictWeightAtMost (R := R) w a := by
  rw [X, monomial_mem_restrictWeightAtMost]
  simp [weight_single, hi]

/-- Weight bounds add under multiplication. -/
theorem mul_mem_restrictWeightAtMost [IsOrderedAddMonoid M] {w : σ → M} {a b : M}
    {p q : MvPolynomial σ R}
    (hp : p ∈ restrictWeightAtMost (R := R) w a)
    (hq : q ∈ restrictWeightAtMost (R := R) w b) :
    p * q ∈ restrictWeightAtMost (R := R) w (a + b) := by
  have hpq : p * q ∈ restrictSupport R
      ({e : σ →₀ ℕ | e.weight w ≤ a} + {e : σ →₀ ℕ | e.weight w ≤ b}) := by
    rw [restrictSupport_add]
    exact Submodule.mul_mem_mul hp hq
  refine restrictSupport_mono R ?_ hpq
  rintro _ ⟨e, he, e', he', rfl⟩
  simp only [Set.mem_ofPred_eq, map_add] at he he' ⊢
  exact add_le_add he he'

/-- The `n`th power of a polynomial of weight at most `a` has weight at most `n • a`. -/
theorem pow_mem_restrictWeightAtMost [IsOrderedAddMonoid M] {w : σ → M} {a : M}
    {p : MvPolynomial σ R}
    (hp : p ∈ restrictWeightAtMost (R := R) w a) (n : ℕ) :
    p ^ n ∈ restrictWeightAtMost (R := R) w (n • a) := by
  induction n with
  | zero =>
      rw [pow_zero, zero_smul, ← C_1]
      exact C_mem_restrictWeightAtMost w le_rfl 1
  | succ n ih =>
      rw [pow_succ, succ_nsmul]
      exact mul_mem_restrictWeightAtMost ih hp

/-- A finite product satisfies the sum of the factors' bounds. -/
theorem prod_mem_restrictWeightAtMost [IsOrderedAddMonoid M] {ι : Type*} {w : σ → M}
    (s : Finset ι)
    {a : ι → M} {p : ι → MvPolynomial σ R}
    (hp : ∀ i ∈ s, p i ∈ restrictWeightAtMost (R := R) w (a i)) :
    ∏ i ∈ s, p i ∈ restrictWeightAtMost (R := R) w (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, Finset.sum_empty, ← C_1]
      exact C_mem_restrictWeightAtMost w le_rfl 1
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      exact mul_mem_restrictWeightAtMost (hp i (Finset.mem_insert_self i s))
        (ih fun j hj => hp j (Finset.mem_insert_of_mem hj))

/-- Substitution preserves weight bounds: if the image of each source variable `i` has
`v`-weight at most `w i`, then a polynomial of `w`-weight at most `a` is sent to a polynomial of
`v`-weight at most `a`. -/
theorem bind₁_mem_restrictWeightAtMost [IsOrderedAddMonoid M] {w : σ → M} {v : τ → M} {a : M}
    {f : σ → MvPolynomial τ R} {p : MvPolynomial σ R}
    (hf : ∀ i, f i ∈ restrictWeightAtMost (R := R) v (w i))
    (hp : p ∈ restrictWeightAtMost (R := R) w a) :
    bind₁ f p ∈ restrictWeightAtMost (R := R) v a := by
  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun e he => ?_
  rw [bind₁_monomial, ← smul_eq_C_mul]
  refine Submodule.smul_mem _ _
    (restrictWeightAtMost_mono v (mem_restrictWeightAtMost.mp hp e he) ?_)
  have hprod := prod_mem_restrictWeightAtMost (R := R) (w := v) e.support
    (a := fun i => e i • w i) (p := fun i => f i ^ e i)
    fun i _ => pow_mem_restrictWeightAtMost (hf i) (e i)
  simpa only [weight_apply, Finsupp.sum] using hprod

/-- Integer-valued copies of a natural-number weight give the same bounds. -/
theorem mem_restrictWeightAtMost_natCast_iff {w : σ → ℕ} {a : ℕ} {p : MvPolynomial σ R} :
    p ∈ restrictWeightAtMost (R := R) (fun i => (w i : ℤ)) (a : ℤ) ↔
      p ∈ restrictWeightAtMost (R := R) w a := by
  have hweight : ∀ e : σ →₀ ℕ, e.weight (fun i => (w i : ℤ)) = ((e.weight w : ℕ) : ℤ) := by
    intro e
    simp [weight_apply, Finsupp.sum]
  simp only [mem_restrictWeightAtMost, hweight, Nat.cast_le]

/-- If every monomial of `p` has natural-number `w`-weight at most `a` and `0 < w i`, the degree
of `p` in the variable `i` is at most `a / w i`: a monomial containing `X i ^ k` has weight at
least `k * w i`. The hypothesis `0 < w i` is needed, since for `w i = 0` every power of `X i` has
weight `0`. -/
theorem degreeOf_le_div_of_mem_restrictWeightAtMost {w : σ → ℕ} {a : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ restrictWeightAtMost (R := R) w a) {i : σ} (hw : 0 < w i) :
    degreeOf i p ≤ a / w i := by
  refine degreeOf_le_iff.mpr fun e he => (Nat.le_div_iff_mul_le hw).mpr ?_
  simpa [smul_eq_mul] using (Finsupp.apply_smul_le_weight w e i).trans (hp he)

/-! ### Finite exponent sets -/

/-- The coefficient space of a finite exponent set is a finite module. -/
theorem restrictSupport_finite {s : Set (σ →₀ ℕ)} (hs : s.Finite) :
    Module.Finite R (restrictSupport R s) :=
  haveI : Finite s := hs.to_subtype
  Module.Finite.of_basis (basisRestrictSupport R s)

/-- The basis vector of `basisRestrictSupport R s` at an exponent `e ∈ s` is the monomial
`monomial e 1`. -/
@[simp]
theorem coe_basisRestrictSupport_apply (s : Set (σ →₀ ℕ)) (e : s) :
    (basisRestrictSupport R s e : MvPolynomial σ R) = monomial e.1 1 := by
  change AddMonoidAlgebra.ofCoeff (R := R) (M := σ →₀ ℕ)
      (↑((Finsupp.supportedEquivFinsupp (M := R) (R := R) s).symm (Finsupp.single e 1))) =
    monomial e.1 1
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

/-- Over a field, the coefficient space of a finite exponent set has dimension its cardinality. -/
theorem finrank_restrictSupport_finset {K : Type*} [Field K] (s : Finset (σ →₀ ℕ)) :
    Module.finrank K (restrictSupport K (↑s : Set (σ →₀ ℕ))) = s.card := by
  rw [Module.finrank_eq_card_basis (basisRestrictSupport K (↑s : Set (σ →₀ ℕ)))]
  simp

end MvPolynomial
