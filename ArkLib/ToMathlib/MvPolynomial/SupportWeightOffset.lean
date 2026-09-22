/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.MvPolynomial.SupportWeight

/-!
# Support weights with an additive allowance

Fix two additive weights `a b : (σ →₀ ℕ) →+ ℕ` on exponent vectors and an allowance `d : ℕ`.
`SupportWeightOffset a b d p` says that every monomial `m` of `p` satisfies `a m ≤ b m + d`. With
`d = 0` this is membership in `supportWeightLE a b`. Unlike the case `d = 0`, the polynomials with
a fixed positive allowance are not closed under multiplication; instead the allowances add. As a
consequence, substituting polynomials with allowances `w i` into `p` gives allowance
`p.weightedTotalDegree w`.

The intended use is Taylor substitution: the substitution preserves the difference between
coefficient index and Taylor order, and the allowance records the source jet index.

## Main statements

* `MvPolynomial.SupportWeightOffset` and its closure lemmas `mono`, `monomial`, `C`, `add`, `mul`,
  `pow`, `sum`, and `prod`.
* `MvPolynomial.supportWeightOffset_zero_iff`: allowance zero is membership in `supportWeightLE`.
* `MvPolynomial.supportWeightOffset_aeval`: substitution charges each monomial its weighted degree.

## References

Ported from `ArkLib/ToMathlib/MvPolynomial/SupportWeightOffset.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`. `SupportWeightOffset`, its namespace lemmas, and
`supportWeightOffset_aeval` keep the source statements. `supportWeightOffset_zero_iff` is new and
connects the definition to `supportWeightLE`; with it, `supportWeightOffset_aeval` at the zero
weight recovers `aeval_mem_supportWeightLE`, as the acceptance tests check. The source import of
`ArkLib.Data.MvPolynomial.WeightedDegree` is dropped because only Mathlib's
`weightedTotalDegree` is used.
-/

@[expose] public section

namespace MvPolynomial

noncomputable section

variable {R σ τ : Type*} [CommSemiring R]

/-- Every monomial `m` of `p` has first weight at most its second weight plus the allowance `d`:
`a m ≤ b m + d`. -/
def SupportWeightOffset (a b : (σ →₀ ℕ) →+ ℕ) (d : ℕ)
    (p : MvPolynomial σ R) : Prop := ∀ m ∈ p.support, a m ≤ b m + d

/-- With allowance zero, `SupportWeightOffset a b 0 p` is membership in `supportWeightLE a b`. -/
theorem supportWeightOffset_zero_iff {a b : (σ →₀ ℕ) →+ ℕ} {p : MvPolynomial σ R} :
    SupportWeightOffset a b 0 p ↔ p ∈ supportWeightLE a b := by
  rw [mem_supportWeightLE]
  rfl

namespace SupportWeightOffset

variable {a b : (σ →₀ ℕ) →+ ℕ} {d e : ℕ} {p q : MvPolynomial σ R}

/-- The allowance can be increased. -/
theorem mono (hp : SupportWeightOffset a b d p) (h : d ≤ e) :
    SupportWeightOffset a b e p := fun m hm ↦ (hp m hm).trans (Nat.add_le_add_left h _)

/-- A monomial has allowance `d` when its exponent does. The coefficient is arbitrary; a zero
coefficient gives the zero polynomial. -/
theorem monomial (m : σ →₀ ℕ) (r : R) (h : a m ≤ b m + d) :
    SupportWeightOffset a b d (MvPolynomial.monomial m r) := by
  intro n hn
  have : n = m := by simpa using support_monomial_subset hn
  simpa [this] using h

/-- A constant has every allowance, since both weights vanish on the zero exponent. -/
theorem C (r : R) : SupportWeightOffset a b d (MvPolynomial.C r) :=
  monomial 0 r (by simp)

/-- Sums keep a common allowance. -/
theorem add (hp : SupportWeightOffset a b d p) (hq : SupportWeightOffset a b d q) :
    SupportWeightOffset a b d (p + q) := by
  classical
  intro m hm
  rcases Finset.mem_union.mp (support_add hm) with hm | hm
  · exact hp m hm
  · exact hq m hm

/-- Allowances add under multiplication, because both weights are additive and every monomial of
`p * q` is a sum of a monomial of `p` and a monomial of `q`. -/
theorem mul (hp : SupportWeightOffset a b d p) (hq : SupportWeightOffset a b e q) :
    SupportWeightOffset a b (d + e) (p * q) := by
  classical
  intro m hm
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp (support_mul p q hm)
  simpa only [map_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    Nat.add_le_add (hp u hu) (hq v hv)

/-- The `n`-th power multiplies the allowance by `n`. -/
theorem pow (hp : SupportWeightOffset a b d p) (n : ℕ) :
    SupportWeightOffset a b (n * d) (p ^ n) := by
  induction n with
  | zero => simpa using (C (a := a) (b := b) (d := 0) (1 : R))
  | succ n ih => simpa [pow_succ, Nat.succ_mul] using ih.mul hp

/-- Finite sums keep a common allowance. -/
theorem sum {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ R)
    (hp : ∀ i ∈ s, SupportWeightOffset a b d (p i)) :
    SupportWeightOffset a b d (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SupportWeightOffset]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hp i (Finset.mem_insert_self _ _)).add
      (ih fun j hj ↦ hp j (Finset.mem_insert_of_mem hj))

/-- A finite product has the sum of the allowances of its factors. -/
theorem prod {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ R) (d : ι → ℕ)
    (hp : ∀ i ∈ s, SupportWeightOffset a b (d i) (p i)) :
    SupportWeightOffset a b (∑ i ∈ s, d i) (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (C (a := a) (b := b) (d := 0) (1 : R))
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact (hp i (Finset.mem_insert_self _ _)).mul
      (ih fun j hj ↦ hp j (Finset.mem_insert_of_mem hj))

end SupportWeightOffset

/-- If each substituted polynomial `v i` has allowance `w i`, then `aeval v p` has allowance
`p.weightedTotalDegree w`: a monomial `m` of `p` becomes `∏ i, v i ^ m i`, whose allowance is
`∑ i, m i * w i`, the `w`-weight of `m`. The polynomial `p` itself is unconstrained. -/
theorem supportWeightOffset_aeval
    (a b : (τ →₀ ℕ) →+ ℕ) (w : σ → ℕ) (v : σ → MvPolynomial τ R)
    (hv : ∀ i, SupportWeightOffset a b (w i) (v i)) (p : MvPolynomial σ R) :
    SupportWeightOffset a b (p.weightedTotalDegree w) (aeval v p) := by
  classical
  conv_rhs => rw [p.as_sum, map_sum]
  apply SupportWeightOffset.sum
  intro m hm
  rw [aeval_monomial]
  have hp := SupportWeightOffset.prod (a := a) (b := b) m.support
    (fun i ↦ v i ^ m i) (fun i ↦ m i * w i) (fun i _ ↦ (hv i).pow (m i))
  have hmul := (SupportWeightOffset.C (a := a) (b := b) (d := 0) (p.coeff m)).mul hp
  simp only [zero_add] at hmul
  apply hmul.mono
  simpa [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul] using
    (le_weightedTotalDegree w hm)

end

end MvPolynomial
