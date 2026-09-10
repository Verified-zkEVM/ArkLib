/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.ActiveOrderAdapter
/-!
# Regular witnesses at actual ordered chain records

First-nonzero separant witnesses align with the exact sparse records emitted by the closed chain.
Under the specialization-degree field-size condition, every bounded root has a regular record
at some center, and solves every earlier record. No root enumeration or executable oracle is added.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.OrderedChainRegularWitness

open PolynomialDifferential
open Polynomial MvPolynomial
open MvPolynomial.SeparantChainMachine (Stage Term)
open HighestJetTransport (encodeJet)
open SeparantChainRefinement (OrderedChain)

variable {F : Type*} [Field F] [DecidableEq F] {d D : ℕ}

/-- A candidate solves the differential equation represented by a retained sparse record. -/
def SolvesRecord (P : F[X]) (record : Stage F) : Prop :=
  ∃ Q : DifferentialPolynomial F d,
    EvaluationMachine.sparsePolynomial record.equation = rename encodeJet Q ∧
      differentialSpecialization Q P = 0

/-- A retained active record is regular for the candidate at the given center. -/
def RegularRecord (P : F[X]) (a : F) (record : Stage F) : Prop :=
  ∃ Q : DifferentialPolynomial F d, ∃ s : Fin (d + 1),
    EvaluationMachine.sparsePolynomial record.equation = rename encodeJet Q ∧
      highestActiveJet Q = some s ∧ record.selected = some (s.val + 1, jetDegree Q s) ∧
      differentialSpecialization Q P = 0 ∧ IsRegularJet Q s a (polynomialJet a P) ∧ Q ≠ 0

/-- A first-nonzero chain witness occurs in the actual ordered records, after solved records. -/
theorem chainWitness_record {Q : DifferentialPolynomial F d} {P : F[X]} {a : F}
    (hw : ChainWitness Q P a) (ts : List (Term F)) (out : List (Stage F))
    (hc : OrderedChain ts Q out) :
    ∃ pre record tail, out = pre ++ record :: tail ∧
      (∀ r ∈ pre, SolvesRecord (d := d) P r) ∧ RegularRecord (d := d) P a record := by
  induction hw generalizing ts out with
  | @regular Q P a s hs hsol hreg =>
      cases hc with
      | terminal layout rep nonzero last => simp [hs] at last
      | @active Q ts tail j layout rep nonzero highest next =>
          have he : s = j := Option.some.inj (hs.symm.trans highest)
          subst j
          refine ⟨[], ⟨ts, some (s.val + 1, jetDegree Q s)⟩, tail, rfl, by simp, ?_⟩
          refine ⟨Q, s, rep, hs, rfl, hsol, ⟨?_, hreg⟩, nonzero⟩
          rw [← eval_differentialSpecialization, hsol]
          simp
  | @singular Q P a s hs hsol nextWitness ih =>
      cases hc with
      | terminal layout rep nonzero last => simp [hs] at last
      | @active Q ts tail j layout rep nonzero highest next =>
          have he : s = j := Option.some.inj (hs.symm.trans highest)
          subst j
          obtain ⟨pre, record, suffix, hout, hpre, hrecord⟩ := ih _ _ next
          refine ⟨⟨ts, some (s.val + 1, jetDegree Q s)⟩ :: pre, record, suffix,
            by simp [hout], ?_, hrecord⟩
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact ⟨Q, rep, hsol⟩
          · exact hpre r hr

/-- Every bounded root has a regular actual record at a center, with all earlier identities zero.
The field-size premise is the existing first-nonzero separant specialization-degree budget. -/
theorem bounded_root_regular_record [Finite F] (Q : DifferentialPolynomial F d)
    (hQ : Q ≠ 0) (hchar : IsBelowCharacteristic D Q) (P : BoundedSolution Q D)
    (ts : List (Term F)) (out : List (Stage F)) (hc : OrderedChain ts Q out)
    (hcard : differentialWeightedDegree D Q - (D - d) < Nat.card F) :
    ∃ a pre record tail, out = pre ++ record :: tail ∧
      (∀ r ∈ pre, SolvesRecord (d := d) P.polynomial r) ∧
      RegularRecord (d := d) P.polynomial a record := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨R, hn, hd, hw⟩ := exists_chainWitness_polynomial Q hQ hchar P
  have hlt : R.natDegree < Fintype.card F := by
    simpa only [Nat.card_eq_fintype_card] using hd.trans_lt hcard
  obtain ⟨a, ha⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card R hn
    (by simpa only [Cardinal.mk_fintype, Nat.cast_lt] using hlt)
  obtain ⟨pre, record, tail, he, hp, hr⟩ := chainWitness_record (hw a ha) ts out hc
  exact ⟨a, pre, record, tail, he, hp, hr⟩

omit [DecidableEq F] in
/-- A regular actual record has a concrete current-order presentation usable by the root solver. -/
theorem RegularRecord.presentation {P : F[X]} {a : F} {record : Stage F}
    (h : RegularRecord (d := d) P a record) :
    ∃ Q : DifferentialPolynomial F d, ∃ s : Fin (d + 1),
      ∃ A : ActiveOrderAdapter.Presentation record.equation Q s,
        s.val ≤ d ∧ highestActiveJet Q = some s ∧
        record.selected = some (s.val + 1,
          jetDegree (semanticEquation A.polynomial) (Fin.last s.val)) ∧
        semanticEquation A.polynomial ≠ 0 ∧
        IsRegularJet (semanticEquation A.polynomial) (Fin.last s.val) a (polynomialJet a P) ∧
        differentialSpecialization (semanticEquation A.polynomial) P = 0 := by
  obtain ⟨Q, s, hrep, hs, hselected, hsol, hregular, hQ⟩ := h
  obtain ⟨A⟩ := ActiveOrderAdapter.exists_presentation record.equation Q s hrep hs
  refine ⟨Q, s, A, Nat.le_of_lt_succ s.isLt, hs, ?_, A.nonzero hQ,
    A.regular_iff a P |>.mpr hregular, ?_⟩
  · rw [A.top_degree]
    exact hselected
  · rw [A.specialization]
    exact hsol

end ReedSolomon.HiddenDerivative.OrderedChainRegularWitness
