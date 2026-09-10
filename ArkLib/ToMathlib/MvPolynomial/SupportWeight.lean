/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Polynomial support satisfying a weight inequality

A comparison of two additive monomial weights is closed under addition and multiplication.
The resulting subalgebra tracks Taylor order: give later coefficient variables their first
possible Taylor order, and compare their total weight with the exponent of the Taylor variable.
-/

@[expose] public section

namespace MvPolynomial

noncomputable section

variable {R σ τ : Type*} [CommSemiring R]

/-- Polynomials all of whose monomials satisfy an additive weight inequality. -/
def supportWeightLE (a b : (σ →₀ ℕ) →+ ℕ) : Subalgebra R (MvPolynomial σ R) where
  carrier := {p | ∀ m ∈ p.support, a m ≤ b m}
  zero_mem' := by simp
  one_mem' := by
    classical
    intro m hm
    have hm0 : m = 0 := by
      simpa only [Finset.mem_singleton] using
        (support_monomial_subset (show m ∈ (monomial 0 (1 : R)).support from hm))
    simp [hm0]
  add_mem' := by
    classical
    intro p q hp hq m hm
    rcases Finset.mem_union.mp (support_add hm) with hm | hm
    · exact hp m hm
    · exact hq m hm
  mul_mem' := by
    classical
    intro p q hp hq m hm
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp (support_mul p q hm)
    simpa using Nat.add_le_add (hp u hu) (hq v hv)
  algebraMap_mem' := by
    intro r m hm
    have hm0 : m = 0 := by
      simpa only [Finset.mem_singleton] using
        (support_monomial_subset (show m ∈ (monomial 0 r).support from hm))
    simp [hm0]

/-- A monomial satisfies the support inequality whenever its exponent does. -/
theorem monomial_mem_supportWeightLE (a b : (σ →₀ ℕ) →+ ℕ)
    (m : σ →₀ ℕ) (r : R) (h : a m ≤ b m) :
    monomial m r ∈ supportWeightLE a b := by
  change ∀ n ∈ (monomial m r).support, a n ≤ b n
  intro n hn
  have hnm : n = m := by simpa using support_monomial_subset hn
  simpa [hnm] using h

/-- Substitution preserves a support-weight inequality satisfied by every substituted variable. -/
theorem aeval_mem_supportWeightLE (a b : (τ →₀ ℕ) →+ ℕ)
    (v : σ → MvPolynomial τ R) (hv : ∀ i, v i ∈ supportWeightLE a b)
    (p : MvPolynomial σ R) : aeval v p ∈ supportWeightLE a b := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using (supportWeightLE a b).algebraMap_mem c
  | add p q hp hq => simpa using (supportWeightLE a b).add_mem hp hq
  | mul_X p i hp =>
    simpa using (supportWeightLE a b).mul_mem hp (hv i)

/-- In a Taylor polynomial, support weight at most the Taylor-variable exponent bounds
all monomials of its coefficient of order `h`. -/
theorem weight_le_of_mem_coeff_optionEquivLeft
    (w : σ → ℕ) (p : MvPolynomial (Option σ) R)
    (hp : p ∈ supportWeightLE
      (Finsupp.weight (fun i ↦ i.elim 0 w)) (Finsupp.applyAddHom none))
    (h : ℕ) (m : σ →₀ ℕ)
    (hm : m ∈ ((optionEquivLeft R σ p).coeff h).support) :
    Finsupp.weight w m ≤ h := by
  have hbound := hp (m.optionElim h) ((mem_support_coeff_optionEquivLeft R).mp hm)
  rw [Finsupp.weight_apply, Finsupp.sum_option_index] at hbound
  · simpa [Finsupp.weight_apply] using hbound
  · intro i
    simp
  · intro i c d
    exact add_smul c d _

/-- Extracting a coefficient in the distinguished variable preserves the weighted degree
in all remaining variables. -/
theorem weightedTotalDegree_coeff_optionEquivLeft_le (w : σ → ℕ)
    (p : MvPolynomial (Option σ) R) (h : ℕ) :
    ((optionEquivLeft R σ p).coeff h).weightedTotalDegree w ≤
      p.weightedTotalDegree (fun i ↦ i.elim 0 w) := by
  apply Finset.sup_le_iff.mpr
  intro m hm
  have hbound := le_weightedTotalDegree (fun i ↦ i.elim 0 w)
    ((mem_support_coeff_optionEquivLeft R).mp hm)
  rw [Finsupp.weight_apply, Finsupp.sum_option_index] at hbound
  · simpa [Finsupp.weight_apply] using hbound
  · intro i
    simp
  · intro i c d
    exact add_smul c d _

end

end MvPolynomial
