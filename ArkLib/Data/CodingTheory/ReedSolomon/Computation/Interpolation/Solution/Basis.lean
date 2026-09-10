/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Matrix.Semantics
public import Mathlib.Algebra.MvPolynomial.Coeff
/-!
# Ordered interpolation-support coefficient basis

These proof-only maps relate the materialized support vectors to genuine source exponents. The
strict total-jet and differential-weight caps are unchanged. Coefficients of an existing supported
polynomial provide a kernel witness; they are not an oracle used by the executable solver.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.NonzeroInterpolationMachine

noncomputable section

open PolynomialDifferential
open MvPolynomial
open scoped BigOperators

variable {F : Type*} [CommRing F] {d : ℕ}

/-- Fixed dense coordinates [X,Y0,...,Yd] of a genuine source exponent. -/
def vector (e : JetVariable d →₀ ℕ) : List ℕ :=
  e none :: List.ofFn (fun j => e (some j))

/-- Source exponent denoted by a materialized vector. -/
def exponent (d : ℕ) (v : List ℕ) : JetVariable d →₀ ℕ :=
  Finsupp.single none (v.getD 0 0) +
    ∑ j : Fin (d + 1), Finsupp.single (some j) (v.getD (j.val + 1) 0)

theorem exponent_none (v : List ℕ) : exponent d v none = v.getD 0 0 := by
  simp [exponent]

theorem exponent_some (v : List ℕ) (j : Fin (d + 1)) :
    exponent d v (some j) = v.getD (j.val + 1) 0 := by
  simp [exponent, Finsupp.single_apply]

theorem exponent_vector (e : JetVariable d →₀ ℕ) : exponent d (vector e) = e := by
  ext j
  cases j with
  | none => simp [exponent_none, vector]
  | some j =>
    rw [exponent_some]
    change (List.ofFn (fun j => e (some j))).getD j.val 0 = e (some j)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos j.isLt,
      Option.getD_some]

theorem vector_exponent (v : List ℕ) (hv : v.length = d + 2) : vector (exponent d v) = v := by
  cases v with
  | nil => simp at hv
  | cons x xs =>
    simp only [vector, exponent_none, exponent_some]
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some] using congrArg (List.cons x)
      (InterpolationPointBlockMachine.ofFn_getD xs (by simpa using hv))

theorem exponent_injective (v u : List ℕ) (hv : v.length = d + 2) (hu : u.length = d + 2)
    (h : exponent d v = exponent d u) : v = u := by
  simpa [vector_exponent v hv, vector_exponent u hu] using congrArg vector h

/-- Exact source monomial interpretation, including all higher jets. -/
theorem sourceValue_eq_monomial (v : List ℕ) (hv : v.length = d + 2) :
    InterpolationPointBlockMachine.sourceValue (F := F) d v = monomial (exponent d v) 1 := by
  obtain ⟨x, b, xs, rfl⟩ : ∃ x b xs, v = x :: b :: xs := by
    cases v with
    | nil => simp at hv
    | cons x v => cases v with
      | nil => simp at hv
      | cons b xs => exact ⟨x, b, xs, rfl⟩
  simp only [InterpolationPointBlockMachine.sourceValue, sourceMonomial]
  rw [exponent, Fin.sum_univ_succ]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some,
    Fin.val_zero, Nat.zero_add, List.getElem?_cons_succ, Fin.val_succ]
  rw [show Finsupp.single none x + (Finsupp.single (some 0) b +
      ∑ j : Fin d, Finsupp.single (some j.succ) (xs[j.val]?.getD 0)) =
      (Finsupp.single none x + Finsupp.single (some 0) b) +
        ∑ j : Fin d, Finsupp.single (some j.succ) (xs[j.val]?.getD 0) by abel]
  simp only [X_pow_eq_monomial, ← monomial_sum_one, monomial_mul, mul_one]

/-- The materialized support maps to distinct genuine source monomials. -/
theorem support_exponents_nodup (D m A : ℕ) :
    ((ReceivedInterpolationMatrixMachine.support D d m A).map (exponent d)).Nodup := by
  apply List.Nodup.map_on _ (InterpolationSupportMachine.supportSpec_nodup _)
  intro v hv u hu he
  apply exponent_injective v u _ _ he
  · simpa [InterpolationSupportMachine.parameters,
      InterpolationSupportMachine.parametersWithBudget] using
      InterpolationSupportMachine.supportSpec_width _ hv
  · simpa [InterpolationSupportMachine.parameters,
      InterpolationSupportMachine.parametersWithBudget] using
      InterpolationSupportMachine.supportSpec_width _ hu

/-- Monomial linear combination in a supplied distinct order. -/
def monomialCombination (es : List (JetVariable d →₀ ℕ)) (w : ℕ → F) : DifferentialPolynomial F d :=
  InterpolationPointBlockMachine.combine (es.map (fun e => monomial e 1)) w

theorem coeff_combination_absent (e : JetVariable d →₀ ℕ) (es : List (JetVariable d →₀ ℕ))
    (he : e ∉ es) (w : ℕ → F) : coeff e (monomialCombination es w) = 0 := by
  induction es generalizing w with
  | nil => simp [monomialCombination, InterpolationPointBlockMachine.combine]
  | cons a es ih =>
    have ha : a ≠ e := by intro h; subst a; simp at he
    have ht := ih (by simp_all) (fun i => w (i + 1))
    simpa [monomialCombination, InterpolationPointBlockMachine.combine, ha] using ht

/-- Coefficient-to-source injectivity in the actual distinct support order. -/
theorem coeff_combination_index (es : List (JetVariable d →₀ ℕ)) (hd : es.Nodup)
    (j : ℕ) (hj : j < es.length) (w : ℕ → F) :
    coeff es[j] (monomialCombination es w) = w j := by
  induction es generalizing j w with
  | nil => simp at hj
  | cons e es ih =>
    have hn := List.nodup_cons.mp hd
    cases j with
    | zero =>
      have ht := coeff_combination_absent e es hn.1 (fun i => w (i + 1))
      simpa [monomialCombination, InterpolationPointBlockMachine.combine] using ht
    | succ j =>
      have hj' : j < es.length := by simpa using hj
      have hne : e ≠ es[j] := by intro he; exact hn.1 (he ▸ List.getElem_mem hj')
      have ht := ih hn.2 j hj' (fun i => w (i + 1))
      simpa [monomialCombination, InterpolationPointBlockMachine.combine, hne] using ht

/-- Every combination has support in the enumerated exponent list. -/
theorem combination_support (es : List (JetVariable d →₀ ℕ)) (w : ℕ → F)
    (e : JetVariable d →₀ ℕ) (he : e ∈ (monomialCombination es w).support) : e ∈ es := by
  by_contra hn
  exact (mem_support_iff.mp he) (coeff_combination_absent e es hn w)

/-- Existing supported polynomials reconstruct from their genuine coefficients. -/
theorem combination_reconstruct (es : List (JetVariable d →₀ ℕ)) (hd : es.Nodup)
    (Q : DifferentialPolynomial F d) (hQ : ∀ e ∈ Q.support, e ∈ es) :
    monomialCombination es (fun i => coeff (es.getD i 0) Q) = Q := by
  ext e
  by_cases he : e ∈ es
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    rw [coeff_combination_index es hd i hi]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  · rw [coeff_combination_absent e es he]
    symm
    by_contra hc
    exact he (hQ e (mem_support_iff.mpr hc))

/-- A distinct monomial combination is nonzero exactly when its bounded coefficient vector is. -/
theorem combination_ne_zero_iff (es : List (JetVariable d →₀ ℕ)) (hd : es.Nodup) (w : ℕ → F) :
    monomialCombination es w ≠ 0 ↔ ∃ i < es.length, w i ≠ 0 := by
  constructor
  · intro h
    by_contra hn
    apply h
    ext e
    rw [coeff_zero]
    by_cases he : e ∈ es
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      rw [coeff_combination_index es hd i hi]
      by_contra hw
      exact hn ⟨i, hi, hw⟩
    · exact coeff_combination_absent e es he w
  · rintro ⟨i, hi, hw⟩ h
    have hc := coeff_combination_index es hd i hi w
    rw [h, coeff_zero] at hc
    exact hw hc.symm

/-- The matrix source convention is this distinct-monomial combination. -/
theorem sourceCombination_eq (D m A : ℕ) (w : ℕ → F) :
    InterpolationPointBlockMachine.sourceCombination d
      (ReceivedInterpolationMatrixMachine.support D d m A) w =
    monomialCombination
      ((ReceivedInterpolationMatrixMachine.support D d m A).map (exponent d)) w := by
  unfold InterpolationPointBlockMachine.sourceCombination monomialCombination
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro v hv
  exact sourceValue_eq_monomial v (by
    simpa [InterpolationSupportMachine.parameters,
      InterpolationSupportMachine.parametersWithBudget] using
      InterpolationSupportMachine.supportSpec_width _ hv)

/-- Exact eligibility required from the existing interpolation witness. -/
def Eligible (D m A : ℕ) (Q : DifferentialPolynomial F d) : Prop :=
  ∀ e ∈ Q.support, vector e ∈ ReceivedInterpolationMatrixMachine.support D d m A

/-- This is exactly the unchanged strict jet cap and differential monomial-weight cap. -/
theorem eligible_iff (D m A : ℕ) (Q : DifferentialPolynomial F d) :
    Eligible D m A Q ↔ ∀ e ∈ Q.support,
      (∑ j : Fin (d + 1), e (some j)) < 2 * m ∧
        e none + ∑ j : Fin (d + 1), (D - j.val) * e (some j) < m * A := by
  simp only [Eligible, vector, ReceivedInterpolationMatrixMachine.support,
    ReceivedInterpolationMatrixMachine.supportWithBudget,
    InterpolationSupportMachine.mem_interpolation_columnsWithBudget]

/-- An actual eligible nonzero polynomial supplies the solver's bounded nonzero vector. -/
theorem witness_coordinates (D m A : ℕ) (Q : DifferentialPolynomial F d)
    (he : Eligible D m A Q) (hn : Q ≠ 0) :
    ∃ w : ℕ → F, InterpolationPointBlockMachine.sourceCombination d
      (ReceivedInterpolationMatrixMachine.support D d m A) w = Q ∧
      ∃ i < (ReceivedInterpolationMatrixMachine.support D d m A).length, w i ≠ 0 := by
  let es := (ReceivedInterpolationMatrixMachine.support D d m A).map (exponent d)
  let w := fun i => coeff (es.getD i 0) Q
  have hr : monomialCombination es w = Q := combination_reconstruct es
    (support_exponents_nodup D m A) Q (by
      intro e he'
      exact List.mem_map.mpr ⟨vector e, he e he', exponent_vector e⟩)
  refine ⟨w, ?_, ?_⟩
  · rw [sourceCombination_eq]
    exact hr
  · have hh := (combination_ne_zero_iff es (support_exponents_nodup D m A) w).mp
      (by simpa only [hr] using hn)
    simpa only [es, List.length_map] using hh

/-- Eligibility is expressed in the existing semantic jet degree and differential weight. -/
theorem eligible_support_caps (D m A : ℕ) (Q : DifferentialPolynomial F d)
    (h : Eligible D m A Q) (e : JetVariable d →₀ ℕ) (he : e ∈ Q.support) :
    totalJetDegree e < 2 * m ∧ Finsupp.weight (differentialWeight D) e < m * A := by
  have hh := (eligible_iff D m A Q).mp h e he
  constructor
  · simpa [totalJetDegree, Finsupp.degree_eq_sum] using hh.1
  · simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_option,
      differentialWeight, mul_comm] using hh.2

/-- The nonzero output's semantic differential weighted degree obeys the strict budget. -/
theorem eligible_weightedDegree (D m A : ℕ) (Q : DifferentialPolynomial F d)
    (h : Eligible D m A Q) (hn : Q ≠ 0) : differentialWeightedDegree D Q < m * A := by
  obtain ⟨e, he⟩ := support_nonempty.mpr hn
  have hp : 0 < m * A := Nat.zero_lt_of_lt (eligible_support_caps D m A Q h e he).2
  rw [differentialWeightedDegree, MvPolynomial.weightedTotalDegree, Finset.sup_lt_iff hp]
  intro e he
  exact (eligible_support_caps D m A Q h e he).2

/-- The support at strict jet cutoff `J` maps to distinct source monomials. -/
theorem supportWithBudget_exponents_nodup (D m J A : ℕ) :
    ((ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A).map
      (exponent d)).Nodup := by
  apply List.Nodup.map_on _ (InterpolationSupportMachine.supportSpec_nodup _)
  intro v hv u hu he
  apply exponent_injective v u _ _ he
  · simpa [InterpolationSupportMachine.parametersWithBudget] using
      InterpolationSupportMachine.supportSpec_width _ hv
  · simpa [InterpolationSupportMachine.parametersWithBudget] using
      InterpolationSupportMachine.supportSpec_width _ hu

/-- The matrix source convention at strict jet cutoff `J`. -/
theorem sourceCombinationWithBudget_eq (D m J A : ℕ) (w : ℕ → F) :
    InterpolationPointBlockMachine.sourceCombination d
      (ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A) w =
    monomialCombination
      ((ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A).map (exponent d)) w := by
  unfold InterpolationPointBlockMachine.sourceCombination monomialCombination
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro v hv
  exact sourceValue_eq_monomial v (by
    simpa [InterpolationSupportMachine.parametersWithBudget] using
      InterpolationSupportMachine.supportSpec_width _ hv)

/-- Eligibility for the explicitly budgeted executable support. -/
def EligibleWithBudget (D m J A : ℕ) (Q : DifferentialPolynomial F d) : Prop :=
  ∀ e ∈ Q.support, vector e ∈ ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A

/-- Budgeted eligibility is exactly the strict jet and differential-weight caps. -/
theorem eligibleWithBudget_iff (D m J A : ℕ) (Q : DifferentialPolynomial F d) :
    EligibleWithBudget D m J A Q ↔ ∀ e ∈ Q.support,
      (∑ j : Fin (d + 1), e (some j)) < J ∧
        e none + ∑ j : Fin (d + 1), (D - j.val) * e (some j) < m * A := by
  simp only [EligibleWithBudget, vector, ReceivedInterpolationMatrixMachine.supportWithBudget,
    InterpolationSupportMachine.mem_interpolation_columnsWithBudget]

/-- A budget-eligible nonzero polynomial supplies a bounded nonzero solver vector. -/
theorem witnessWithBudget_coordinates (D m J A : ℕ) (Q : DifferentialPolynomial F d)
    (he : EligibleWithBudget D m J A Q) (hn : Q ≠ 0) :
    ∃ w : ℕ → F, InterpolationPointBlockMachine.sourceCombination d
      (ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A) w = Q ∧
      ∃ i < (ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A).length,
        w i ≠ 0 := by
  let es := (ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A).map (exponent d)
  let w := fun i => coeff (es.getD i 0) Q
  have hr : monomialCombination es w = Q := combination_reconstruct es
    (supportWithBudget_exponents_nodup D m J A) Q (by
      intro e he'
      exact List.mem_map.mpr ⟨vector e, he e he', exponent_vector e⟩)
  refine ⟨w, ?_, ?_⟩
  · rw [sourceCombinationWithBudget_eq]
    exact hr
  · have hh :=
      (combination_ne_zero_iff es (supportWithBudget_exponents_nodup D m J A) w).mp
        (by simpa only [hr] using hn)
    simpa only [es, List.length_map] using hh

/-- Semantic caps for a monomial in the explicitly budgeted support. -/
theorem eligibleWithBudget_support_caps (D m J A : ℕ) (Q : DifferentialPolynomial F d)
    (h : EligibleWithBudget D m J A Q) (e : JetVariable d →₀ ℕ) (he : e ∈ Q.support) :
    totalJetDegree e < J ∧ Finsupp.weight (differentialWeight D) e < m * A := by
  have hh := (eligibleWithBudget_iff D m J A Q).mp h e he
  constructor
  · simpa [totalJetDegree, Finsupp.degree_eq_sum] using hh.1
  · simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_option,
      differentialWeight, mul_comm] using hh.2

/-- The source polynomial's differential weighted degree obeys its explicit budget. -/
theorem eligibleWithBudget_weightedDegree (D m J A : ℕ) (Q : DifferentialPolynomial F d)
    (h : EligibleWithBudget D m J A Q) (hn : Q ≠ 0) :
    differentialWeightedDegree D Q < m * A := by
  obtain ⟨e, he⟩ := support_nonempty.mpr hn
  have hp : 0 < m * A := Nat.zero_lt_of_lt
    (eligibleWithBudget_support_caps D m J A Q h e he).2
  rw [differentialWeightedDegree, MvPolynomial.weightedTotalDegree, Finset.sup_lt_iff hp]
  intro e he
  exact (eligibleWithBudget_support_caps D m J A Q h e he).2

end
end ReedSolomon.HiddenDerivative.NonzeroInterpolationMachine
