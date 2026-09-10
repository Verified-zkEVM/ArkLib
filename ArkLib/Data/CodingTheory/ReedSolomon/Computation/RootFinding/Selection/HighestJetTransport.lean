/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.HighestJetRefinement
public import ArkLib.Data.Polynomial.Differential.Basic
/-!
# Highest-jet machine transport to finite differential variables

The representation equality uses the injective encoding `X ↦ 0`, `Y_j ↦ j+1`. Combined with
the fixed dense layout, it transports the charged selector to the existing `highestActiveJet`
and `jetDegree`, including cancellation and the no-active-jet case.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.HighestJetTransport

open PolynomialDifferential
open MvPolynomial
open MvPolynomial.DenseNormalizeMachine (DenseLayout normalize)

variable {F : Type*} [CommSemiring F] [DecidableEq F] {d : ℕ}

/-- Natural indices of finite differential variables, preserving the distinguished variable. -/
def encodeJet : JetVariable d → ℕ
  | none => 0
  | some j => j.val + 1

/-- The finite differential-variable encoding loses no variables. -/
theorem encodeJet_injective : Function.Injective (encodeJet (d := d)) := by
  intro a b he
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some b => simp only [encodeJet] at he; omega
  | some a =>
      cases b with
      | none => simp only [encodeJet] at he; omega
      | some b =>
          apply congrArg some
          apply Fin.ext
          simp only [encodeJet] at he
          omega

omit [DecidableEq F] in
/-- Injective renaming preserves each formal jet's individual degree exactly. -/
theorem encoded_degree (Q : DifferentialPolynomial F d) (j : Fin (d + 1)) :
    (rename encodeJet Q).degreeOf (j.val + 1) = jetDegree Q j :=
  degreeOf_rename_of_injective encodeJet_injective (some j)

omit [DecidableEq F] in
private theorem highest_eq_some (Q : DifferentialPolynomial F d) (j : Fin (d + 1))
    (hj : IsHighestActiveJet Q j) : highestActiveJet Q = some j := by
  have hne : (activeJets Q).Nonempty := ⟨j, mem_activeJets.mpr hj.1⟩
  rw [highestActiveJet_eq_some_max Q hne]
  congr 1
  apply le_antisymm
  · by_contra h
    have hm := mem_activeJets.mp (Finset.max'_mem (activeJets Q) hne)
    exact hj.2 _ (lt_of_not_ge h) hm
  · exact Finset.le_max' _ _ (mem_activeJets.mpr hj.1)

/-- A dense sparse representation selects exactly the highest active formal jet and its degree.
The equality premise is a polynomial representation bridge, with no degree or selector oracle. -/
theorem select_eq (ts : List (HighestJetMachine.Term F)) (Q : DifferentialPolynomial F d)
    (hl : DenseLayout (List.range (d + 2)) ts)
    (hQ : EvaluationMachine.sparsePolynomial ts = rename encodeJet Q) :
    HighestJetMachine.select (normalize ts []) none =
      (highestActiveJet Q).map (fun j => (j.val + 1, jetDegree Q j)) := by
  cases hs : HighestJetMachine.select (normalize ts []) none with
  | none =>
      have hnone : highestActiveJet Q = none := by
        apply (highestActiveJet_eq_none_iff Q).mpr
        intro j hj
        have hz := (HighestJetMachine.select_none_iff _ ts hl).mp hs (j.val + 1) (by omega)
        rw [hQ, encoded_degree] at hz
        exact (Nat.ne_of_gt hj) hz
      simp [hnone]
  | some p =>
      rcases p with ⟨i, e⟩
      obtain ⟨hi, he, hdeg, hmax, hmem⟩ := HighestJetMachine.select_some_correct _ ts hl i e hs
      have hbound : i < d + 2 := List.mem_range.mp hmem
      let j : Fin (d + 1) := ⟨i - 1, by omega⟩
      have hij : j.val + 1 = i := by dsimp [j]; omega
      have hjdeg : jetDegree Q j = e := by
        rw [← encoded_degree Q j, hij, ← hQ]
        exact hdeg
      have hh : highestActiveJet Q = some j := by
        apply highest_eq_some
        refine ⟨by unfold DependsOnJet; omega, ?_⟩
        intro k hk hactive
        have hik : i < k.val + 1 := by
          have hval : j.val < k.val := hk
          omega
        have hz := hmax (k.val + 1) hik
        rw [hQ, encoded_degree] at hz
        exact (Nat.ne_of_gt hactive) hz
      simp [hh, hij, hjdeg]

/-- No selected jet is equivalent to every formal jet having individual degree zero. -/
theorem select_none_iff (ts : List (HighestJetMachine.Term F))
    (Q : DifferentialPolynomial F d) (hl : DenseLayout (List.range (d + 2)) ts)
    (hQ : EvaluationMachine.sparsePolynomial ts = rename encodeJet Q) :
    HighestJetMachine.select (normalize ts []) none = none ↔ ∀ j, jetDegree Q j = 0 := by
  rw [select_eq ts Q hl hQ, Option.map_eq_none_iff, highestActiveJet_eq_none_iff]
  simp only [DependsOnJet, Nat.not_lt, Nat.le_zero]

/-- The normalized representation is empty exactly when the differential polynomial is zero. -/
theorem normalize_empty_iff (ts : List (HighestJetMachine.Term F))
    (Q : DifferentialPolynomial F d) (hl : DenseLayout (List.range (d + 2)) ts)
    (hQ : EvaluationMachine.sparsePolynomial ts = rename encodeJet Q) :
    normalize ts [] = [] ↔ Q = 0 := by
  rw [HighestJetMachine.normalize_empty_iff _ ts hl, hQ]
  constructor
  · intro h
    apply rename_injective encodeJet encodeJet_injective
    simpa only [map_zero] using h
  · rintro rfl
    exact map_zero _

/-- The actual normalized selector returns the mathematical highest jet and exact jet degree. -/
theorem execution_correct (ts : List (HighestJetMachine.Term F)) (Q : DifferentialPolynomial F d)
    (hl : DenseLayout (List.range (d + 2)) ts)
    (hQ : EvaluationMachine.sparsePolynomial ts = rename encodeJet Q) :
    ∃ c, HighestJetMachine.runFuel (HighestJetMachine.budget ts.length (d + 2))
        (.normalizing (.terms ts [])) =
        (.done ((highestActiveJet Q).map (fun j => (j.val + 1, jetDegree Q j))), c) ∧
      HighestJetMachine.totalCost c ≤ HighestJetMachine.budget ts.length (d + 2) := by
  obtain ⟨c, hr, hc⟩ := HighestJetMachine.evaluation_runFuel _ ts hl
  simp only [List.length_range] at hr hc
  refine ⟨c, ?_, hc⟩
  exact hr.trans (congrArg (fun b => (HighestJetMachine.Configuration.done (F := F) b, c))
    (select_eq ts Q hl hQ))

end ReedSolomon.HiddenDerivative.HighestJetTransport
