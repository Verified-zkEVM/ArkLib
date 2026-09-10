/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.SeparantChainMachine
public import ArkLib.Data.MvPolynomial.HighestJetRefinement

/-!
# Separant-chain representation and execution bounds

Differentiation preserves the dense layout and cannot increase either the number of terms or
the full numerical exponent mass. Nested traces retain exact wrapper charges at each level.
-/

@[expose] public section

namespace MvPolynomial.SeparantChainMachine

open DenseNormalizeMachine (DenseLayout)
open PartialDerivativeMachine (derivativeTerm derivativeTerms factorMass inputMass)

abbrev totalCost := PartialDerivativeMachine.totalCost

private theorem total_add (a b : Cost) : totalCost (a + b) = totalCost a + totalCost b :=
  PartialDerivativeMachine.total_add a b

private theorem total_charge (a d n e o : ℕ) :
    totalCost (charge a d n e o) = a + 1 + d + n + e + o :=
  PartialDerivativeMachine.total_charge a d n e o

variable {F : Type*} [CommSemiring F] [DecidableEq F]

/-- Every surviving term's numerical exponent mass is no greater than its source term's. -/
theorem derivativeTerm_mass (i : ℕ) (c : F) (fs : List (ℕ × ℕ))
    (t : Term F) (h : derivativeTerm i c fs = some t) : factorMass t.2 ≤ factorMass fs := by
  induction fs generalizing t with
  | nil => simp [derivativeTerm] at h
  | cons p fs ih =>
      rcases p with ⟨j, e⟩
      by_cases he : j = i
      · simp only [derivativeTerm, if_pos he] at h
        split_ifs at h with hz hc
        cases h
        simp only [factorMass, List.length_cons, List.map_cons, List.sum_cons]
        omega
      · simp only [derivativeTerm, if_neg he] at h
        cases hd : derivativeTerm i c fs with
        | none => simp [hd] at h
        | some u =>
            simp only [hd, Option.map_some, Option.some.injEq] at h
            subst t
            have hm := ih u hd
            simp only [factorMass, List.length_cons, List.map_cons, List.sum_cons] at hm ⊢
            omega

/-- The derivative emits at most one term per input term. -/
theorem derivativeTerms_count (i : ℕ) (ts : List (Term F)) :
    (derivativeTerms i ts).length ≤ ts.length := by
  induction ts with
  | nil => simp [derivativeTerms]
  | cons t ts ih =>
      rcases t with ⟨c, fs⟩
      have h : (derivativeTerm i c fs).toList.length ≤ 1 := by
        cases derivativeTerm i c fs <;> simp
      simp only [derivativeTerms, List.length_append, List.length_cons]
      omega

/-- Total materialized numerical mass does not grow through a derivative stage. -/
theorem derivativeTerms_mass (i : ℕ) (ts : List (Term F)) :
    inputMass (derivativeTerms i ts) ≤ inputMass ts := by
  induction ts with
  | nil => simp [derivativeTerms, inputMass]
  | cons t ts ih =>
      rcases t with ⟨c, fs⟩
      cases hd : derivativeTerm i c fs with
      | none =>
          simpa [derivativeTerms, hd, inputMass] using ih.trans (Nat.le_add_left _ _)
      | some u =>
          have hm := derivativeTerm_mass i c fs u hd
          simp only [derivativeTerms, hd, Option.toList_some, List.singleton_append,
            inputMass, List.map_cons, List.sum_cons]
          unfold inputMass at ih
          omega

/-- Differentiation retains the same fixed ordered variable list in every surviving term. -/
theorem derivativeTerms_layout (vars : List ℕ) (i : ℕ) (ts : List (Term F))
    (hl : DenseLayout vars ts) : DenseLayout vars (derivativeTerms i ts) := by
  refine ⟨hl.1, ?_⟩
  induction ts with
  | nil => simp [derivativeTerms]
  | cons t ts ih =>
      rcases t with ⟨c, fs⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · have hd : derivativeTerm i c fs = some u := by simpa using hu
        rw [PartialDerivativeMachine.derivativeTerm_variables i c fs hd]
        exact hl.2 (c, fs) (by simp)
      · exact ih ⟨hl.1, fun v hv => hl.2 v (by simp [hv])⟩ u hu

/-- Exact wrapper charges for a child trace of length `k`; used only in proofs. -/
def wrappers (k : ℕ) : Cost := ⟨⟨0, 0, k, 2 * k, 0, 0⟩, 0⟩

private theorem wrappers_succ (k : ℕ) (c e : Cost) :
    wrappers (k + 1) + (c + e) = (charge 0 2 0 0 0 + c) + (wrappers k + e) := by
  ext <;> simp [wrappers, charge, PartialDerivativeMachine.charge, Nat.mul_add,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem wrappers_total (k : ℕ) : totalCost (wrappers k) = 3 * k := by
  simp [wrappers, totalCost, PartialDerivativeMachine.totalCost]
  omega

/-- Lift an actual selector run, retaining every instruction's parent-wrapper charge. -/
theorem selector_trace (fuel : ℕ) (eqs : List (Term F)) (pre : List (Stage F))
    (s : HighestJetMachine.Configuration F) :
    ∃ k ≤ fuel, Trace k (.selecting eqs pre s)
      (wrappers k + (HighestJetMachine.runFuel fuel s).2)
      (.selecting eqs pre (HighestJetMachine.runFuel fuel s).1) := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, by simpa [wrappers, HighestJetMachine.runFuel] using Trace.nil _⟩
  | succ fuel ih =>
      cases hs : HighestJetMachine.step s with
      | none =>
          exact ⟨0, Nat.zero_le _, by
            simpa [wrappers, HighestJetMachine.runFuel, hs] using Trace.nil (.selecting eqs pre s)⟩
      | some z =>
          obtain ⟨k, hk, ht⟩ := ih z.1
          refine ⟨k + 1, Nat.succ_le_succ hk, ?_⟩
          simpa only [HighestJetMachine.runFuel, hs, wrappers_succ] using
            Trace.cons (Step.selector hs) ht

/-- Lift an actual derivative run, retaining every instruction's parent-wrapper charge. -/
theorem derivative_trace (i fuel : ℕ) (pre : List (Stage F))
    (s : PartialDerivativeMachine.Configuration F) :
    ∃ k ≤ fuel, Trace k (.derivingAt i pre s)
      (wrappers k + (PartialDerivativeMachine.runFuel i fuel s).2)
      (.derivingAt i pre (PartialDerivativeMachine.runFuel i fuel s).1) := by
  induction fuel generalizing s with
  | zero =>
      exact ⟨0, le_rfl, by simpa [wrappers, PartialDerivativeMachine.runFuel] using Trace.nil _⟩
  | succ fuel ih =>
      cases hs : PartialDerivativeMachine.step i s with
      | none =>
          exact ⟨0, Nat.zero_le _, by
            simpa [wrappers, PartialDerivativeMachine.runFuel, hs] using
              Trace.nil (.derivingAt i pre s)⟩
      | some z =>
          obtain ⟨k, hk, ht⟩ := ih z.1
          refine ⟨k + 1, Nat.succ_le_succ hk, ?_⟩
          simpa only [PartialDerivativeMachine.runFuel, hs, wrappers_succ] using
            Trace.cons (Step.derivative hs) ht

/-- A uniform stage budget in initial term count, factor count and numerical exponent mass. -/
def stageBudget (m L M : ℕ) : ℕ :=
  5 * HighestJetMachine.budget m L + 5 * (40 * M + 10) + 40

/-- Selector execution including its outer wrapper has a uniform original-input bound. -/
theorem selected_trace (vars : List ℕ) (eqs : List (Term F)) (pre : List (Stage F))
    (hl : DenseLayout vars eqs) (m : ℕ) (hm : eqs.length ≤ m) :
    ∃ k c, Trace k (initial eqs pre) c
      (.record eqs (HighestJetMachine.select (DenseNormalizeMachine.normalize eqs []) none) pre) ∧
      k + totalCost c ≤ 5 * HighestJetMachine.budget m vars.length + 4 := by
  obtain ⟨c, hr, hc⟩ := HighestJetMachine.evaluation_runFuel vars eqs hl
  obtain ⟨k, hk, ht⟩ := selector_trace (HighestJetMachine.budget eqs.length vars.length)
    eqs pre (.normalizing (.terms eqs []))
  rw [hr] at ht
  refine ⟨k + 1, (wrappers k + c) + charge 0 2 0 0 0, ?_, ?_⟩
  · exact ht.trans (Trace.cons Step.selected (Trace.nil _))
  · simp only [total_add, wrappers_total, total_charge]
    have hb : HighestJetMachine.budget eqs.length vars.length ≤
        HighestJetMachine.budget m vars.length := by
      unfold HighestJetMachine.budget DenseNormalizeMachine.budget
      gcongr
    change totalCost c ≤ _ at hc
    omega

/-- Derivative execution including its outer wrapper preserves the original mass bound. -/
theorem derived_trace (i : ℕ) (eqs : List (Term F)) (pre : List (Stage F))
    (M : ℕ) (hm : inputMass eqs ≤ M) :
    ∃ k c, Trace k (.derivingAt i pre (.terms eqs [])) c (initial (derivativeTerms i eqs) pre) ∧
      k + totalCost c ≤ 5 * (40 * M + 10) + 7 := by
  obtain ⟨c, hr, hc⟩ := PartialDerivativeMachine.evaluation_runFuel i eqs
  obtain ⟨k, hk, ht⟩ := derivative_trace i (PartialDerivativeMachine.budget eqs) pre (.terms eqs [])
  rw [hr] at ht
  refine ⟨k + 1, (wrappers k + c) + charge 0 5 0 0 0, ?_, ?_⟩
  · exact ht.trans (Trace.cons Step.derived (Trace.nil _))
  · simp only [total_add, wrappers_total, total_charge]
    unfold PartialDerivativeMachine.budget at hk hc
    change totalCost c ≤ _ at hc
    omega

/-- Ordered output is produced by explicit reversal, charging each stage cell. -/
theorem reverse_trace (pre out : List (Stage F)) :
    ∃ k c, Trace k (.reverse pre out) c (.done (pre.reverse ++ out)) ∧
      k + totalCost c ≤ 8 * pre.length + 5 := by
  induction pre generalizing out with
  | nil =>
      refine ⟨1, charge 0 2 0 0 1, Trace.cons Step.emit (Trace.nil _), ?_⟩
      simp [total_charge]
  | cons r pre ih =>
      obtain ⟨k, c, ht, hc⟩ := ih (r :: out)
      refine ⟨k + 1, charge 0 5 0 0 1 + c, ?_, ?_⟩
      · simpa [List.reverse_cons, List.append_assoc] using Trace.cons Step.reverse ht
      · simp only [total_add, total_charge, List.length_cons]
        omega

end MvPolynomial.SeparantChainMachine
