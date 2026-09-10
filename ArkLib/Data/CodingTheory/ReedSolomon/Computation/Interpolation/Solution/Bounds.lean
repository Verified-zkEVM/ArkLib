/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Solution.Attempts
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Counting.TotalJetDegreeRootCount
public import ArkLib.Data.MvPolynomial.PartialDerivativeRefinement
public import ArkLib.Data.MvPolynomial.QuadraticInputMachine
/-!
# Numerical bounds for actual sparse interpolation outputs

Factor mass is bounded using the physical emitted support columns, so cancellation cannot hide
large exponents or factor lists. The generic bound is quadratic in `m*A`, with coefficients
controlled only by the derivative order and multiplicity. Its order-zero specialization remains
polynomial when multiplicity grows. Scalar embedding shares factors and preserves these measures.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.NonzeroInterpolationMachine

open MvPolynomial PartialDerivativeMachine PolynomialDifferential

variable {F : Type*} [Field F] [DecidableEq F]

/-- Successful execution supplies the complete certificate without a witness callback. -/
theorem run_certified (D d m A : ℕ) (rows : List (F × F)) (out : Output F)
    (hr : (run D d m A rows).1 = some out) : Certified (d := d) D m A rows out := by
  obtain ⟨result, c, he, _hc, hs⟩ := attempt_complete (d := d) D m A rows
  have he' := congrArg Prod.fst he
  rw [hr] at he'
  exact hs out he'.symm

/-- Successful explicitly budgeted execution supplies its complete certificate. -/
theorem runWithBudget_certified (D d m J A : ℕ) (rows : List (F × F)) (out : Output F)
    (hr : (runWithBudget D d m J A rows).1 = some out) :
    CertifiedWithBudget (d := d) D m J A rows out := by
  obtain ⟨result, c, he, _hc, hs⟩ := attemptWithBudget_complete (d := d) D m J A rows
  have he' := congrArg Prod.fst he
  rw [hr] at he'
  exact hs out he'.symm

/-- The terms returned at strict cutoff `J` are the actual emitter result. -/
theorem runWithBudget_emit (D d m J A : ℕ) (rows : List (F × F)) (out : Output F)
    (hr : (runWithBudget D d m J A rows).1 = some out) :
    (emit (ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A)
      out.coefficients).1 = some out.terms := by
  obtain ⟨c, hs, _hc⟩ := InterpolationSupportMachine.enumerateWithBudget_correct D d m J A
  simp only [runWithBudget, hs] at hr
  split at hr
  · cases hr
  · split at hr
    · rename_i mat hm j cs hsol
      generalize he : (emit (InterpolationSupportMachine.supportSpec
        (InterpolationSupportMachine.parametersWithBudget D d m J A)) cs).1 = result at hr
      cases result with
      | none => cases hr
      | some ts => cases hr; exact he
    · cases hr

/-- The returned terms are the actual emitter result for the returned coefficient vector. -/
theorem run_emit (D d m A : ℕ) (rows : List (F × F)) (out : Output F)
    (hr : (run D d m A rows).1 = some out) :
    (emit (ReceivedInterpolationMatrixMachine.support D d m A) out.coefficients).1 =
      some out.terms := by
  simpa [run, ReceivedInterpolationMatrixMachine.support] using
    runWithBudget_emit D d m (2 * m) A rows out hr

/-- Each actual returned term has a physical key from the enumerated interpolation columns. -/
theorem run_term_origin (D d m A : ℕ) (rows : List (F × F)) (out : Output F)
    (hr : (run D d m A rows).1 = some out) :
    ∀ t ∈ out.terms, ∃ v ∈ ReceivedInterpolationMatrixMachine.support D d m A,
      t.2 = (factors 0 v).1 ∧ t.1 ≠ 0 := by
  have hc := run_certified D d m A rows out hr
  obtain ⟨c, he, _hl, _hc⟩ := emit_correct (d + 2)
    (ReceivedInterpolationMatrixMachine.support D d m A) out.coefficients hc.1 (by
      intro v hv
      exact (InterpolationSupportMachine.supportSpec_width _ hv).le)
  have he' := congrArg Prod.fst he
  rw [run_emit D d m A rows out hr] at he'
  have ht := Option.some.inj he'
  rw [ht]
  exact emitSpec_keys _ _

private theorem column_mass (D d m A : ℕ) (v : List ℕ)
    (hv : v ∈ ReceivedInterpolationMatrixMachine.support D d m A) :
    factorMass (factors 0 v).1 ≤ 2 * (d + 2) + m * A + 2 * m + 1 := by
  have hw : v.length = d + 2 :=
    InterpolationSupportMachine.supportSpec_width _ hv
  have hsum : v.sum ≤ m * A + 2 * m := by
    cases v with
    | nil => simp
    | cons x bs =>
        have hb := (InterpolationSupportMachine.mem_supportSpec
          (InterpolationSupportMachine.parameters D d m A) x bs).mp hv
        have hx : x < m * A := hb.2.1
        have hj : bs.sum < 2 * m := hb.2.2.2.1
        simp only [List.sum_cons]
        omega
  have hl : (factors 0 v).1.length = v.length := by simp [factors_correct]
  simp only [factorMass, hl, factors_values, hw]
  omega

omit [Field F] [DecidableEq F] in
private theorem mass_le (ts : List (Term F)) (B : ℕ)
    (hb : ∀ t ∈ ts, factorMass t.2 ≤ B) : inputMass ts ≤ ts.length * B := by
  induction ts with
  | nil => simp [inputMass]
  | cons t ts ih =>
      have hh := hb t (by simp)
      have ht := ih (fun u hu ↦ hb u (by simp [hu]))
      simp only [inputMass, List.map_cons, List.sum_cons, List.length_cons] at *
      nlinarith

omit [DecidableEq F] in
/-- Nonzero eligible equations obey the strict total jet cap, not only individual caps. -/
theorem eligible_jetTotalDegree {d : ℕ} (D m A : ℕ) (Q : DifferentialPolynomial F d)
    (he : Eligible D m A Q) (hne : Q ≠ 0) : jetTotalDegree Q < 2 * m := by
  obtain ⟨e, hee⟩ := MvPolynomial.support_nonempty.mpr hne
  have hpos : 0 < 2 * m := Nat.zero_lt_of_lt ((eligible_iff D m A Q).mp he e hee).1
  have hb : jetTotalDegree Q ≤ 2 * m - 1 := (jetTotalDegree_le_iff Q _).mpr (by
    intro u hu
    have := ((eligible_iff D m A Q).mp he u hu).1
    omega)
  omega

/-- Uniform numerical measures for the actual returned terms and reconstructed source equation. -/
theorem run_output_bounds (D d m A : ℕ) (rows : List (F × F)) (out : Output F)
    (hr : (run D d m A rows).1 = some out) :
    out.terms.length ≤ maximumColumns d m A ∧
      inputMass out.terms ≤ maximumColumns d m A * (2 * (d + 2) + m * A + 2 * m + 1) ∧
      jetTotalDegree (sourceOutput (d := d) D m A out) < 2 * m := by
  have hc := run_certified D d m A rows out hr
  have hlen : out.terms.length ≤ maximumColumns d m A :=
    (hc.2.2.2.1.trans_eq hc.1).trans (support_length_le D d m A)
  have hm := mass_le out.terms (2 * (d + 2) + m * A + 2 * m + 1) (by
    intro t ht
    obtain ⟨v, hv, hkey, _hne⟩ := run_term_origin D d m A rows out hr t ht
    rw [hkey]
    exact column_mass D d m A v hv)
  have hne : sourceOutput (d := d) D m A out ≠ 0 := by
    intro hz
    have hrep := hc.2.2.2.2.2.2.1
    rw [hz, map_zero] at hrep
    exact hc.2.2.2.2.2.2.2.1 hrep
  exact ⟨hlen, hm.trans (Nat.mul_le_mul_right _ hlen),
    eligible_jetTotalDegree D m A _ hc.2.2.2.2.2.2.2.2.1 hne⟩

/-- Each term returned at strict cutoff `J` comes from its materialized support. -/
theorem runWithBudget_term_origin (D d m J A : ℕ) (rows : List (F × F)) (out : Output F)
    (hr : (runWithBudget D d m J A rows).1 = some out) :
    ∀ t ∈ out.terms, ∃ v ∈ ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A,
      t.2 = (factors 0 v).1 ∧ t.1 ≠ 0 := by
  have hc := runWithBudget_certified D d m J A rows out hr
  obtain ⟨c, he, _hl, _hc⟩ := emit_correct (d + 2)
    (ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A) out.coefficients hc.1 (by
      intro v hv
      exact (InterpolationSupportMachine.supportSpec_width _ hv).le)
  have he' := congrArg Prod.fst he
  rw [runWithBudget_emit D d m J A rows out hr] at he'
  have ht := Option.some.inj he'
  rw [ht]
  exact emitSpec_keys _ _

private theorem columnWithBudget_mass (D d m J A : ℕ) (v : List ℕ)
    (hv : v ∈ ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A) :
    factorMass (factors 0 v).1 ≤ 2 * (d + 2) + m * A + J + 1 := by
  have hw : v.length = d + 2 := InterpolationSupportMachine.supportSpec_width _ hv
  have hsum : v.sum ≤ m * A + J := by
    cases v with
    | nil => simp
    | cons x bs =>
        have hb := (InterpolationSupportMachine.mem_supportSpec
          (InterpolationSupportMachine.parametersWithBudget D d m J A) x bs).mp hv
        have hx : x < m * A := hb.2.1
        have hj : bs.sum < J := hb.2.2.2.1
        simp only [List.sum_cons]
        omega
  have hl : (factors 0 v).1.length = v.length := by simp [factors_correct]
  simp only [factorMass, hl, factors_values, hw]
  omega

omit [DecidableEq F] in
/-- A nonzero equation supported at strict cutoff `J` has total jet degree below `J`. -/
theorem eligibleWithBudget_jetTotalDegree {d : ℕ} (D m J A : ℕ)
    (Q : DifferentialPolynomial F d) (he : EligibleWithBudget D m J A Q) (hne : Q ≠ 0) :
    jetTotalDegree Q < J := by
  obtain ⟨e, hee⟩ := MvPolynomial.support_nonempty.mpr hne
  have hpos : 0 < J := Nat.zero_lt_of_lt ((eligibleWithBudget_iff D m J A Q).mp he e hee).1
  have hb : jetTotalDegree Q ≤ J - 1 := (jetTotalDegree_le_iff Q _).mpr (by
    intro u hu
    have := ((eligibleWithBudget_iff D m J A Q).mp he u hu).1
    omega)
  omega

/-- Numerical measures of output from the explicitly budgeted interpolation run. -/
theorem runWithBudget_output_bounds (D d m J A : ℕ) (rows : List (F × F)) (out : Output F)
    (hr : (runWithBudget D d m J A rows).1 = some out) :
    out.terms.length ≤ maximumColumnsWithBudget d m J A ∧
      inputMass out.terms ≤
        maximumColumnsWithBudget d m J A * (2 * (d + 2) + m * A + J + 1) ∧
      jetTotalDegree (sourceOutputWithBudget (d := d) D m J A out) < J := by
  have hc := runWithBudget_certified D d m J A rows out hr
  have hlen : out.terms.length ≤ maximumColumnsWithBudget d m J A :=
    (hc.2.2.2.1.trans_eq hc.1).trans (supportWithBudget_length_le D d m J A)
  have hm := mass_le out.terms (2 * (d + 2) + m * A + J + 1) (by
    intro t ht
    obtain ⟨v, hv, hkey, _hne⟩ := runWithBudget_term_origin D d m J A rows out hr t ht
    rw [hkey]
    exact columnWithBudget_mass D d m J A v hv)
  have hne : sourceOutputWithBudget (d := d) D m J A out ≠ 0 := by
    intro hz
    have hrep := hc.2.2.2.2.2.2.1
    rw [hz, map_zero] at hrep
    exact hc.2.2.2.2.2.2.2.1 hrep
  exact ⟨hlen, hm.trans (Nat.mul_le_mul_right _ hlen),
    eligibleWithBudget_jetTotalDegree D m J A _ hc.2.2.2.2.2.2.2.2.1 hne⟩

/-- Order zero retains a polynomial mass bound even when multiplicity grows with block length. -/
theorem run_zero_output_bounds (D m A : ℕ) (rows : List (F × F)) (out : Output F)
    (hr : (run D 0 m A rows).1 = some out) :
    out.terms.length ≤ m * A * (2 * m) ∧
      inputMass out.terms ≤ (2 * m) * (m * A) * (m * A + 2 * m + 5) ∧
      jetTotalDegree (sourceOutput (d := 0) D m A out) < 2 * m := by
  have h := run_output_bounds D 0 m A rows out hr
  refine ⟨by simpa [maximumColumns] using h.1, ?_, h.2.2⟩
  convert h.2.1 using 1
  unfold maximumColumns
  ring

omit [DecidableEq F] in
/-- Scalar conversion preserves physical term count and factor mass exactly. -/
theorem embedded_measures (a : F) (ts : List (Term F)) :
    (QuadraticInputMachine.embedded (a := a) ts).length = ts.length ∧
      inputMass (QuadraticInputMachine.embedded (a := a) ts) = inputMass ts := by
  simp [QuadraticInputMachine.embedded, inputMass, List.map_map, Function.comp_def]

end ReedSolomon.HiddenDerivative.NonzeroInterpolationMachine
