/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.SeparantChainBounds
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.HighestJetTransport
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Counting.TotalJetDegreeRootCount
/-!
# Closed ordered separant chains

The actual selector and derivative machines construct a finite ordered chain. Every active
record is followed by its precise separant equation, even when the next highest jet drops.
Total jet degree bounds the number of active records; the terminal record has no active jet.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.SeparantChainRefinement

open PolynomialDifferential
open MvPolynomial
open MvPolynomial.SeparantChainMachine
open MvPolynomial.DenseNormalizeMachine (DenseLayout)
open MvPolynomial.PartialDerivativeMachine (derivativeTerms inputMass)
open HighestJetTransport (encodeJet)

variable {F : Type*} [Field F] [DecidableEq F] {d : ℕ}

/-- A closed ordered chain retains the representation and nonzero equation at each stage.
The active constructor fixes the next equation to the current highest-jet separant. -/
inductive OrderedChain : List (Term F) → DifferentialPolynomial F d → List (Stage F) → Prop where
  | terminal {Q ts} (layout : DenseLayout (List.range (d + 2)) ts)
      (rep : EvaluationMachine.sparsePolynomial ts = rename encodeJet Q)
      (nonzero : Q ≠ 0) (last : highestActiveJet Q = none) :
      OrderedChain ts Q [⟨ts, none⟩]
  | active {Q ts tail} (j : Fin (d + 1)) (layout : DenseLayout (List.range (d + 2)) ts)
      (rep : EvaluationMachine.sparsePolynomial ts = rename encodeJet Q)
      (nonzero : Q ≠ 0) (highest : highestActiveJet Q = some j)
      (next : OrderedChain (derivativeTerms (j.val + 1) ts) (separant Q j) tail) :
      OrderedChain ts Q (⟨ts, some (j.val + 1, jetDegree Q j)⟩ :: tail)

/-- Every retained stage has at most the initial term count and initial numerical exponent mass. -/
theorem OrderedChain.sizes {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {out : List (Stage F)} (h : OrderedChain ts Q out) :
    ∀ r ∈ out, r.equation.length ≤ ts.length ∧ inputMass r.equation ≤ inputMass ts := by
  induction h with
  | terminal layout rep nonzero last =>
      intro r hr
      have he : r = _ := List.mem_singleton.mp hr
      subst r
      exact ⟨le_rfl, le_rfl⟩
  | @active Q ts tail j layout rep nonzero highest next ih =>
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨le_rfl, le_rfl⟩
      · obtain ⟨hc, hm⟩ := ih r hr
        exact ⟨hc.trans (derivativeTerms_count _ ts), hm.trans (derivativeTerms_mass _ ts)⟩

/-- Every retained stage has the same fixed dense variable layout. -/
theorem OrderedChain.layouts {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {out : List (Stage F)} (h : OrderedChain ts Q out) :
    ∀ r ∈ out, DenseLayout (List.range (d + 2)) r.equation := by
  induction h with
  | terminal layout rep nonzero last =>
      intro r hr
      have he : r = _ := List.mem_singleton.mp hr
      subst r
      exact layout
  | active j layout rep nonzero highest next ih =>
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact layout
      · exact ih r hr

/-- Every stage denotes a nonzero differential equation, has correct selector metadata, and
retains the initial below-characteristic contract. -/
theorem OrderedChain.record_contract {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {out : List (Stage F)} (h : OrderedChain ts Q out)
    (hchar : ∀ j, jetDegree Q j < ringChar F) :
    ∀ r ∈ out, ∃ R : DifferentialPolynomial F d,
      EvaluationMachine.sparsePolynomial r.equation = rename encodeJet R ∧ R ≠ 0 ∧
      r.selected = (highestActiveJet R).map (fun j => (j.val + 1, jetDegree R j)) ∧
      ∀ j, jetDegree R j < ringChar F := by
  induction h with
  | @terminal Q ts layout rep nonzero last =>
      intro r hr
      have he : r = _ := List.mem_singleton.mp hr
      subst r
      exact ⟨Q, rep, nonzero, by simp [last], hchar⟩
  | @active Q ts tail j layout rep nonzero highest next ih =>
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨Q, rep, nonzero, by simp [highest], hchar⟩
      · exact ih (fun k => (jetDegree_separant_le Q j k).trans_lt (hchar k)) r hr

/-- Sparse differentiation transports to the literal next differential separant equation. -/
theorem derivative_rep (ts : List (Term F)) (Q : DifferentialPolynomial F d)
    (hl : DenseLayout (List.range (d + 2)) ts)
    (hQ : EvaluationMachine.sparsePolynomial ts = rename encodeJet Q) (j : Fin (d + 1)) :
    EvaluationMachine.sparsePolynomial (derivativeTerms (j.val + 1) ts) =
      rename encodeJet (separant Q j) := by
  rw [PartialDerivativeMachine.sparsePolynomial_derivativeTerms]
  · rw [hQ]
    exact pderiv_rename HighestJetTransport.encodeJet_injective (some j) Q
  · exact fun t ht => hl.2 t ht ▸ hl.1

private theorem total_add (a b : Cost) : totalCost (a + b) = totalCost a + totalCost b :=
  PartialDerivativeMachine.total_add a b

private theorem total_charge (a dn n e o : ℕ) :
    totalCost (charge a dn n e o) = a + 1 + dn + n + e + o :=
  PartialDerivativeMachine.total_charge a dn n e o

private theorem terminal_trace (ts : List (Term F)) (pre : List (Stage F))
    (Q : DifferentialPolynomial F d) (hl : DenseLayout (List.range (d + 2)) ts)
    (hQ : EvaluationMachine.sparsePolynomial ts = rename encodeJet Q)
    (hs : highestActiveJet Q = none) (m M : ℕ) (hm : ts.length ≤ m) :
    ∃ k c, Trace k (initial ts pre) c (.done (pre.reverse ++ [⟨ts, none⟩])) ∧
      k + totalCost c ≤ stageBudget m (d + 2) M + 8 * pre.length + 5 := by
  obtain ⟨ks, cs, ht, hb⟩ := selected_trace _ ts pre hl m hm
  have he := HighestJetTransport.select_eq ts Q hl hQ
  rw [hs] at he
  simp only [Option.map_none] at he
  rw [he] at ht
  obtain ⟨kr, cr, hr, hc⟩ := reverse_trace (⟨ts, none⟩ :: pre) []
  refine ⟨ks + (kr + 1), cs + (charge 0 6 0 0 1 + cr), ?_, ?_⟩
  · simpa [List.reverse_cons, List.append_assoc] using ht.trans (Trace.cons Step.terminal hr)
  · simp only [total_add, total_charge]
    simp only [List.length_range] at hb
    simp only [List.length_cons] at hc
    unfold stageBudget
    omega

/-- Closed construction follows actual child machines and terminates by total jet degree.
The prefix parameter accounts for previously allocated stage records and their final reversal. -/
theorem closed_trace (Δ m M : ℕ) (ts : List (Term F)) (pre : List (Stage F))
    (Q : DifferentialPolynomial F d) (hl : DenseLayout (List.range (d + 2)) ts)
    (hQ : EvaluationMachine.sparsePolynomial ts = rename encodeJet Q) (hne : Q ≠ 0)
    (hchar : ∀ j, jetDegree Q j < ringChar F) (hdeg : jetTotalDegree Q ≤ Δ)
    (hm : ts.length ≤ m) (hM : inputMass ts ≤ M) :
    ∃ out k c, Trace k (initial ts pre) c (.done (pre.reverse ++ out)) ∧
      OrderedChain ts Q out ∧ out.length ≤ Δ + 1 ∧
      k + totalCost c ≤ (Δ + 1) * stageBudget m (d + 2) M + 8 * pre.length + 5 := by
  induction Δ using Nat.strong_induction_on generalizing ts pre Q with
  | h Δ ih =>
      cases hs : highestActiveJet Q with
      | none =>
          obtain ⟨k, c, ht, hc⟩ := terminal_trace ts pre Q hl hQ hs m M hm
          refine ⟨[⟨ts, none⟩], k, c, ht, OrderedChain.terminal hl hQ hne hs, by simp, ?_⟩
          nlinarith [Nat.zero_le (Δ * stageBudget m (d + 2) M)]
      | some j =>
          have hp : 0 < jetDegree Q j :=
            (isHighestActiveJet_of_highestActiveJet_eq_some hs).1
          have hpos := jetDegree_le_total Q j
          have hΔ : 0 < Δ := by omega
          have hn : separant Q j ≠ 0 :=
            separant_ne_zero_of_highestActiveJet_eq_some Q j hs (hchar j)
          have hc : ∀ k, jetDegree (separant Q j) k < ringChar F := fun k =>
            (jetDegree_separant_le Q j k).trans_lt (hchar k)
          have hd : jetTotalDegree (separant Q j) ≤ Δ - 1 :=
            (separant_total_le Q j).trans (Nat.sub_le_sub_right hdeg 1)
          let r : Stage F := ⟨ts, some (j.val + 1, jetDegree Q j)⟩
          obtain ⟨out, kr, cr, hr, hchain, hlen, hb⟩ := ih (Δ - 1) (by omega)
            (derivativeTerms (j.val + 1) ts) (r :: pre) (separant Q j)
            (derivativeTerms_layout _ _ ts hl) (derivative_rep ts Q hl hQ j) hn hc hd
            ((derivativeTerms_count _ ts).trans hm) ((derivativeTerms_mass _ ts).trans hM)
          obtain ⟨ks, cs, hts, hbs⟩ := selected_trace _ ts pre hl m hm
          have he := HighestJetTransport.select_eq ts Q hl hQ
          rw [hs] at he
          simp only [Option.map_some] at he
          rw [he] at hts
          obtain ⟨kd, cd, htd, hbd⟩ := derived_trace (j.val + 1) ts (r :: pre) M hM
          have ht := hts.trans (Trace.cons Step.active (htd.trans hr))
          refine ⟨r :: out, ks + (kd + kr + 1), cs + (charge 0 8 0 0 1 + (cd + cr)),
            ?_, OrderedChain.active j hl hQ hne hs hchain, ?_, ?_⟩
          · simpa [r, List.reverse_cons, List.append_assoc] using ht
          · simp only [List.length_cons]
            omega
          · simp only [total_add, total_charge]
            simp only [List.length_cons] at hb
            simp only [List.length_range] at hbs
            have heq : Δ - 1 + 1 = Δ := by omega
            rw [heq] at hb
            unfold stageBudget at hb ⊢
            nlinarith

/-- Uniform complete-chain bound. The stage count depends only on the total-jet-degree budget. -/
def budget (Δ m L M : ℕ) : ℕ := (Δ + 1) * stageBudget m L M + 5

/-- Actual bounded execution returns the complete ordered separant chain and its terminal record.
No semantic selector or derivative correctness callback is supplied by the caller. -/
theorem execution_correct (Δ : ℕ) (ts : List (Term F)) (Q : DifferentialPolynomial F d)
    (hl : DenseLayout (List.range (d + 2)) ts)
    (hQ : EvaluationMachine.sparsePolynomial ts = rename encodeJet Q) (hne : Q ≠ 0)
    (hchar : ∀ j, jetDegree Q j < ringChar F) (hdeg : jetTotalDegree Q ≤ Δ) :
    ∃ out c, runFuel (budget Δ ts.length (d + 2) (inputMass ts)) (initial ts) = (.done out, c) ∧
      OrderedChain ts Q out ∧ out.length ≤ Δ + 1 ∧
      totalCost c ≤ budget Δ ts.length (d + 2) (inputMass ts) := by
  obtain ⟨out, k, c, ht, ho, hl, hc⟩ := closed_trace Δ ts.length (inputMass ts)
    ts [] Q hl hQ hne hchar hdeg le_rfl le_rfl
  simp only [List.reverse_nil, List.nil_append] at ht
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hc
  change k + totalCost c ≤ budget Δ ts.length (d + 2) (inputMass ts) at hc
  have he := ht.runFuel_done (budget Δ ts.length (d + 2) (inputMass ts) - k)
  rw [show k + (budget Δ ts.length (d + 2) (inputMass ts) - k) =
    budget Δ ts.length (d + 2) (inputMass ts) by omega] at he
  exact ⟨out, c, he, ho, hl, by omega⟩

end ReedSolomon.HiddenDerivative.SeparantChainRefinement
