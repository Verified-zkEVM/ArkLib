/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Zhe Zheng, Quang Dao
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Weighted-order bounds and weighted truncation of multivariate polynomials

For a weight `w : σ → ℕ`, this file studies lower bounds on the weights of monomials, the
counterpart of the upper bounds in `ArkLib.Data.MvPolynomial.WeightedDegree`.

* `restrictWeightedOrder w m` is the submodule of polynomials each of whose monomials has
  `w`-weight at least `m`. It contains the zero polynomial for every `m`, and every polynomial
  when `m = 0`.
* `filterSupport p` keeps exactly the monomials whose exponents satisfy `p`, and
  `weightedTruncation w m` is the special case keeping the monomials of weight below `m`.

The main result, `weightedTruncation_bind₁_weightedTruncation`, says that truncation commutes
with a substitution that does not lower weights: if every generator image `f i` has all of its
monomials of `v`-weight at least `w i`, then truncating the input below `w`-weight `m` does not
change the output truncated below `v`-weight `m`. No hypothesis on the coefficient ring is
needed.

## Main statements

* `bind₁_mem_restrictWeightedOrder`: substitution preserves weighted-order lower bounds.
* `pow_dvd_eval₂Hom_of_mem_restrictWeightedOrder`: evaluating a polynomial of weighted order at
  least `m` at values `g i` divisible by `t ^ (w i)` gives a value divisible by `t ^ m`.
* `weightedTruncation_eq_zero_iff`: a truncation vanishes exactly on the corresponding
  weighted-order submodule.
* `weightedTruncation_bind₁_weightedTruncation`: truncation commutes with weight-nondecreasing
  substitution.

## References

The truncation argument generalizes the private support lemmas behind
`ReedSolomon.HiddenDerivative.enlargedLocalConstraintMap_truncateLocalT` in
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/ConstraintMap.lean` at
ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d, which were adapted from Kai Zhe
Zheng's `rs-ld-mca` formalization. The source proved the special case of one change of local
variables using integer-valued negated weights; here the statement is for arbitrary variable
types, arbitrary natural weights, and an arbitrary commutative semiring. The source's
`filterLocalMonomials` is `filterSupport` for local polynomials.

`pow_dvd_eval₂Hom_of_mem_restrictWeightedOrder` generalizes the source's
`pow_dvd_eval₂Hom_of_lowContact_coeff_zero` and its private helper
`localContactOrder_pow_dvd_monomialSpecialization` in
`.../HiddenDerivative/Interpolation/Local/Contact.lean` at the same revision from the local
contact weight to an arbitrary weight, and from commutative rings to commutative semirings.
-/

@[expose] public section

noncomputable section

open Finsupp
open scoped Pointwise

namespace MvPolynomial

variable {σ τ R : Type*} [CommSemiring R]

/-! ### Weighted-order submodules -/

/-- The polynomials all of whose monomials have `w`-weight at least `m`. -/
def restrictWeightedOrder (w : σ → ℕ) (m : ℕ) : Submodule R (MvPolynomial σ R) :=
  restrictSupport R {e | m ≤ e.weight w}

/-- Membership in `restrictWeightedOrder` is the pointwise lower bound on the support. -/
theorem mem_restrictWeightedOrder {w : σ → ℕ} {m : ℕ} {p : MvPolynomial σ R} :
    p ∈ restrictWeightedOrder (R := R) w m ↔ ∀ e ∈ p.support, m ≤ e.weight w :=
  Iff.rfl

/-- Weakening the lower bound enlarges the submodule. -/
theorem restrictWeightedOrder_anti (w : σ → ℕ) {m n : ℕ} (hmn : m ≤ n) :
    restrictWeightedOrder (R := R) w n ≤ restrictWeightedOrder (R := R) w m :=
  restrictSupport_mono R fun _ he => Nat.le_trans hmn he

/-- Every polynomial satisfies the lower bound zero. -/
@[simp]
theorem restrictWeightedOrder_zero (w : σ → ℕ) :
    restrictWeightedOrder (R := R) w 0 = ⊤ := by
  ext p
  simp [mem_restrictWeightedOrder]

/-- A monomial satisfies the lower bound exactly when its exponent does, unless its coefficient
is zero. -/
@[simp]
theorem monomial_mem_restrictWeightedOrder (w : σ → ℕ) (m : ℕ) (e : σ →₀ ℕ) (r : R) :
    monomial e r ∈ restrictWeightedOrder (R := R) w m ↔ m ≤ e.weight w ∨ r = 0 :=
  monomial_mem_restrictSupport (R := R) (s := {e | m ≤ e.weight w})

/-- The variable `X i` satisfies every lower bound at most its weight. -/
theorem X_mem_restrictWeightedOrder (w : σ → ℕ) {m : ℕ} (i : σ) (hi : m ≤ w i) :
    X i ∈ restrictWeightedOrder (R := R) w m := by
  rw [X, monomial_mem_restrictWeightedOrder]
  simp [weight_single, hi]

/-- Weighted-order lower bounds add under multiplication. -/
theorem mul_mem_restrictWeightedOrder {w : σ → ℕ} {a b : ℕ} {p q : MvPolynomial σ R}
    (hp : p ∈ restrictWeightedOrder (R := R) w a)
    (hq : q ∈ restrictWeightedOrder (R := R) w b) :
    p * q ∈ restrictWeightedOrder (R := R) w (a + b) := by
  have hpq : p * q ∈ restrictSupport R
      ({e : σ →₀ ℕ | a ≤ e.weight w} + {e : σ →₀ ℕ | b ≤ e.weight w}) := by
    rw [restrictSupport_add]
    exact Submodule.mul_mem_mul hp hq
  refine restrictSupport_mono R ?_ hpq
  rintro _ ⟨e, he, e', he', rfl⟩
  simp only [Set.mem_ofPred_eq, map_add] at he he' ⊢
  omega

/-- The `n`th power of a polynomial of weighted order at least `a` has weighted order at least
`n * a`. -/
theorem pow_mem_restrictWeightedOrder {w : σ → ℕ} {a : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ restrictWeightedOrder (R := R) w a) (n : ℕ) :
    p ^ n ∈ restrictWeightedOrder (R := R) w (n * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Nat.succ_mul]
      exact mul_mem_restrictWeightedOrder ih hp

/-- A finite product satisfies the sum of the factors' lower bounds. -/
theorem prod_mem_restrictWeightedOrder {ι : Type*} {w : σ → ℕ} (s : Finset ι)
    {a : ι → ℕ} {p : ι → MvPolynomial σ R}
    (hp : ∀ i ∈ s, p i ∈ restrictWeightedOrder (R := R) w (a i)) :
    ∏ i ∈ s, p i ∈ restrictWeightedOrder (R := R) w (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      exact mul_mem_restrictWeightedOrder (hp i (Finset.mem_insert_self i s))
        (ih fun j hj => hp j (Finset.mem_insert_of_mem hj))

/-- Substitution preserves weighted-order lower bounds: if the image of each source variable `i`
has all of its monomials of `v`-weight at least `w i`, then a polynomial of `w`-order at least
`m` is sent to a polynomial of `v`-order at least `m`. -/
theorem bind₁_mem_restrictWeightedOrder {w : σ → ℕ} {v : τ → ℕ} {m : ℕ}
    {f : σ → MvPolynomial τ R} {p : MvPolynomial σ R}
    (hf : ∀ i, f i ∈ restrictWeightedOrder (R := R) v (w i))
    (hp : p ∈ restrictWeightedOrder (R := R) w m) :
    bind₁ f p ∈ restrictWeightedOrder (R := R) v m := by
  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun e he => ?_
  rw [bind₁_monomial, ← smul_eq_C_mul]
  refine Submodule.smul_mem _ _
    (restrictWeightedOrder_anti v (mem_restrictWeightedOrder.mp hp e he) ?_)
  have hprod := prod_mem_restrictWeightedOrder (R := R) (w := v) e.support
    (a := fun i => e i * w i) (p := fun i => f i ^ e i)
    fun i _ => pow_mem_restrictWeightedOrder (hf i) (e i)
  simpa only [weight_apply, Finsupp.sum, smul_eq_mul] using hprod

/-- Evaluation of a polynomial of weighted order at least `m`. If `t ^ (w i)` divides the value
`g i` of every variable `i`, then `t ^ m` divides `p(g)`: each monomial `x^e` of `p` has
`w`-weight at least `m`, and its value is divisible by `t` to the power of that weight. Variables
of weight zero impose no condition. -/
theorem pow_dvd_eval₂Hom_of_mem_restrictWeightedOrder {S : Type*} [CommSemiring S]
    (f : R →+* S) {g : σ → S} {t : S} {w : σ → ℕ} {m : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ restrictWeightedOrder (R := R) w m) (hg : ∀ i, t ^ w i ∣ g i) :
    t ^ m ∣ eval₂Hom f g p := by
  rw [p.as_sum, map_sum]
  refine Finset.dvd_sum fun e he => ?_
  rw [eval₂Hom_monomial]
  refine (pow_dvd_pow t (mem_restrictWeightedOrder.mp hp e he)).trans (Dvd.dvd.mul_left ?_ _)
  rw [weight_apply, Finsupp.sum, Finsupp.prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun i _ => ?_
  rw [smul_eq_mul, mul_comm, pow_mul]
  exact pow_dvd_pow_of_dvd (hg i) _

/-! ### Support filters and weighted truncation -/

/-- Coefficientwise projection onto the monomials whose exponents satisfy `p`. -/
def filterSupport (p : (σ →₀ ℕ) → Prop) [DecidablePred p] :
    MvPolynomial σ R →ₗ[R] MvPolynomial σ R where
  toFun F := AddMonoidAlgebra.ofCoeff (Finsupp.filter p (AddMonoidAlgebra.coeff F))
  map_add' F G := by
    apply AddMonoidAlgebra.coeff_injective
    exact Finsupp.filter_add
  map_smul' a F := by
    apply AddMonoidAlgebra.coeff_injective
    exact Finsupp.filter_smul

@[simp]
theorem coeff_filterSupport (p : (σ →₀ ℕ) → Prop) [DecidablePred p]
    (F : MvPolynomial σ R) (e : σ →₀ ℕ) :
    (filterSupport (R := R) p F).coeff e = if p e then F.coeff e else 0 :=
  Finsupp.filter_apply _ _ _

/-- A filtered polynomial vanishes exactly when every retained coefficient vanishes. -/
theorem filterSupport_eq_zero_iff (p : (σ →₀ ℕ) → Prop) [DecidablePred p]
    (F : MvPolynomial σ R) :
    filterSupport (R := R) p F = 0 ↔ ∀ e, p e → F.coeff e = 0 := by
  constructor
  · intro h e he
    simpa [he] using congrArg (fun G : MvPolynomial σ R => G.coeff e) h
  · intro h
    ext e
    by_cases he : p e <;> simp [he, h]

/-- A polynomial is the sum of its retained and discarded parts. -/
theorem filterSupport_add_filterSupport_not (p : (σ →₀ ℕ) → Prop) [DecidablePred p]
    (F : MvPolynomial σ R) :
    filterSupport (R := R) p F + filterSupport (R := R) (fun e => ¬p e) F = F := by
  ext e
  by_cases he : p e <;> simp [he]

/-- The retained part is supported on the exponents satisfying `p`. -/
theorem filterSupport_mem_restrictSupport (p : (σ →₀ ℕ) → Prop) [DecidablePred p]
    (F : MvPolynomial σ R) :
    filterSupport (R := R) p F ∈ restrictSupport R {e | p e} := by
  rw [mem_restrictSupport_iff]
  intro e he
  by_contra hp
  rw [Finset.mem_coe, mem_support_iff, coeff_filterSupport] at he
  exact he (by simp [show ¬p e from hp])

/-- Truncation below `w`-weight `m`: keep exactly the monomials of weight less than `m`. -/
def weightedTruncation (w : σ → ℕ) (m : ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  filterSupport fun e => e.weight w < m

@[simp]
theorem coeff_weightedTruncation (w : σ → ℕ) (m : ℕ) (F : MvPolynomial σ R)
    (e : σ →₀ ℕ) :
    (weightedTruncation (R := R) w m F).coeff e =
      if e.weight w < m then F.coeff e else 0 :=
  coeff_filterSupport _ F e

/-- The truncation below `m` vanishes exactly on polynomials of weighted order at least `m`. -/
theorem weightedTruncation_eq_zero_iff (w : σ → ℕ) (m : ℕ) (F : MvPolynomial σ R) :
    weightedTruncation (R := R) w m F = 0 ↔ F ∈ restrictWeightedOrder (R := R) w m := by
  rw [weightedTruncation, filterSupport_eq_zero_iff, mem_restrictWeightedOrder]
  constructor
  · intro h e he
    by_contra hlt
    exact mem_support_iff.mp he (h e (Nat.lt_of_not_le hlt))
  · intro h e hlt
    by_contra hne
    exact Nat.not_le_of_lt hlt (h e (mem_support_iff.mpr hne))

/-- Truncation commutes with a weight-nondecreasing substitution. If the image of each source
variable `i` has `v`-order at least `w i`, then the monomials of `w`-weight at least `m` in the
input contribute only monomials of `v`-weight at least `m` to the output, so they may be
discarded before substituting. -/
theorem weightedTruncation_bind₁_weightedTruncation {w : σ → ℕ} {v : τ → ℕ}
    {f : σ → MvPolynomial τ R}
    (hf : ∀ i, f i ∈ restrictWeightedOrder (R := R) v (w i)) (m : ℕ)
    (F : MvPolynomial σ R) :
    weightedTruncation (R := R) v m (bind₁ f (weightedTruncation (R := R) w m F)) =
      weightedTruncation (R := R) v m (bind₁ f F) := by
  obtain ⟨H, hH, hsplit⟩ : ∃ H ∈ restrictWeightedOrder (R := R) w m,
      weightedTruncation (R := R) w m F + H = F := by
    refine ⟨_, mem_restrictWeightedOrder.mpr fun e he => ?_,
      filterSupport_add_filterSupport_not _ F⟩
    by_contra hlt
    rw [mem_support_iff, coeff_filterSupport] at he
    exact he (by simp [Nat.lt_of_not_le hlt])
  conv_rhs => rw [← hsplit]
  rw [map_add, map_add, (weightedTruncation_eq_zero_iff v m _).mpr
    (bind₁_mem_restrictWeightedOrder hf hH), add_zero]

end MvPolynomial
