/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.StageRootsMachine
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.ActiveOrderAdapter
/-!
# Ordered stage contexts and charged collection bounds

The specification projects explicit records to global polynomials. Pair and list allocation,
callee dispatch, and final reversal are included in the same execution bound.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.StageRootsMachine

open Polynomial Matrix CompPoly List PolynomialDifferential

/-- Total work is additive across composed transitions. -/
theorem total_add (a b : Cost) : totalCost (a + b) = totalCost a + totalCost b :=
  JetRootsMachine.total_add a b

/-- A caller dispatch preserves its fixed register charge. -/
theorem total_wrapper (n : ℕ) : totalCost (wrapperCost n) = 3 * n :=
  JetRootsMachine.total_wrapper n

/-- Local operations retain control, allocation, arithmetic, and output charges. -/
theorem total_charge (d n o : ℕ) : totalCost (charge d n o) = 1 + d + n + o :=
  JetRootsMachine.total_charge d n o

variable {F : Type*} [Field F] [DecidableEq F]

/-- Attach the already allocated context root to an already materialized center/vector record. -/
def tagged (context : Context F) (candidate : CenterRootsMachine.Record F) : Record F :=
  ⟨context, candidate.1, candidate.2⟩

/-- A context has the literal preceding prefix and immediate successor from the emitted chain. -/
def HasContext (stages : List (Stage F)) (context : Context F) : Prop :=
  ∃ pre tail next, stages = pre ++ context.stage :: next :: tail ∧
    context.previous = (pre.map (fun stage ↦ stage.equation)).reverse ∧
      context.separant = next.equation

/-- Per-stage fuel includes prefix/context/record allocations and eventual output reversal. -/
def stageFuel (input : Input F) (D L n : ℕ) (stage : Stage F) : ℕ :=
  match stage.selected with
  | none => 2
  | some (i, _) => CenterRootsMachine.fuel (centerInput input stage (i - 1)) D L n +
      3 * input.alphabet.length ^ (i - 1 + 2) + 4

/-- Per-stage work retains all callee charges and caller wrappers. -/
def stageWork (input : Input F) (D L n : ℕ) (stage : Stage F) : ℕ :=
  match stage.selected with
  | none => 13
  | some (i, _) => CenterRootsMachine.workBound (centerInput input stage (i - 1)) D L n +
      3 * CenterRootsMachine.fuel (centerInput input stage (i - 1)) D L n +
      22 * input.alphabet.length ^ (i - 1 + 2) + 40

/-- Polynomial output conversion allocates each tagged record and outer cell separately. -/
theorem collect_trace (input : Input F) (D L : ℕ) (context : Context F)
    (candidates : List (CenterRootsMachine.Record F)) (stages : List (Stage F))
    (pre : List (List (Term F))) (acc : List (Record F)) (samples : List F) :
    ∃ c, Trace input D L (2 * candidates.length + 1)
      (.collect context candidates stages pre acc samples) c
      (.scan stages pre ((candidates.map (tagged context)).reverse ++ acc) samples) ∧
      totalCost c ≤ 16 * candidates.length + 4 := by
  induction candidates generalizing acc with
  | nil =>
      refine ⟨charge 3 0 0 + 0, ?_, ?_⟩
      · simpa using Trace.cons (Step.collected (input := input) (D := D) (L := L))
          (Trace.nil _)
      · change totalCost (charge 3 0 0 + 0) ≤ 4
        decide
  | cons candidate candidates ih =>
      rcases candidate with ⟨a, cs⟩
      obtain ⟨c, ht, hc⟩ := ih (tagged context (a, cs) :: acc)
      refine ⟨charge 8 0 0 + (charge 6 0 0 + c), ?_, ?_⟩
      · simpa [tagged, List.reverse_cons, List.append_assoc, Nat.mul_add, Nat.add_assoc] using
          Trace.cons Step.record (Trace.cons Step.save ht)
      · simp only [total_add, total_charge, List.length_cons]
        omega

/-- Reversal charges every outer record cell and final emission. -/
theorem reverse_trace (input : Input F) (D L : ℕ) (as out : List (Record F)) :
    ∃ c, Trace input D L (as.length + 2) (.reverse as out) c
      (.done (some (as.reverse ++ out))) ∧ totalCost c ≤ 6 * as.length + 7 := by
  induction as generalizing out with
  | nil =>
      refine ⟨charge 2 0 0 + (charge 2 0 1 + 0), ?_, ?_⟩
      · simpa using Trace.cons (Step.reversed (input := input) (D := D) (L := L))
          (Trace.cons Step.emit (Trace.nil _))
      · change totalCost (charge 2 0 0 + (charge 2 0 1 + 0)) ≤ 7
        decide
  | cons a as ih =>
      obtain ⟨c, ht, hc⟩ := ih (a :: out)
      refine ⟨charge 5 0 0 + c, ?_, ?_⟩
      · simpa [List.reverse_cons, List.append_assoc] using Trace.cons Step.reverse ht
      · rw [total_add, total_charge]
        simp only [List.length_cons]
        omega

/-- Ordered contexts and concrete callee outputs; no freely supplied output function occurs. -/
inductive Specification (input : Input F) (D L : ℕ) (samples : List F) :
    List (Stage F) → List (List (Term F)) → List (Record F) → Prop where
  | terminal (ts pre) : Specification input D L samples [⟨ts, none⟩] pre []
  | active {stage next stages pre r e candidates out c}
      (selected : stage.selected = some (r + 1, e))
      (run : CenterRootsMachine.runFuel (centerInput input stage r) D L
        (CenterRootsMachine.fuel (centerInput input stage r) D L samples.length)
        (.start samples) = (.done (some candidates), c))
      (tail : Specification input D L samples (next :: stages) (stage.equation :: pre) out) :
      Specification input D L samples (stage :: next :: stages) pre
        (candidates.map (tagged ⟨stage, pre, next.equation⟩) ++ out)

/-- Maximum output count of a single selected stage. -/
def stageCount (input : Input F) (stage : Stage F) : ℕ :=
  match stage.selected with
  | none => 0
  | some (i, _) => input.alphabet.length ^ (i - 1 + 2)

private theorem chain_head {d : ℕ} {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {stages : List (Stage F)} (h : SeparantChainRefinement.OrderedChain ts Q stages) :
    ∃ next tail, stages = next :: tail ∧ next.equation = ts := by
  cases h with
  | terminal layout rep nonzero last => exact ⟨_, [], rfl, rfl⟩
  | active j layout rep nonzero highest next => exact ⟨_, _, rfl, rfl⟩

/-- Every chain stage executes the root solver at its actual active order.
The active-order presentation is derived from the literal ordered-chain contract. -/
theorem scan_trace {d D L : ℕ} (input : Input F) (points : Fin L ↪ F) (samples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i)) (hq : 0 < input.alphabet.length)
    (hdepth : d ≤ D) {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {stages : List (Stage F)} (hchain : SeparantChainRefinement.OrderedChain ts Q stages)
    (hweight : differentialWeightedDegree D Q < L)
    (pre : List (List (Term F))) (acc : List (Record F))
    (hacc : ∀ record ∈ acc, record.coefficients.length = D + 1) :
    ∃ roots steps c, Trace input D L steps (.scan stages pre acc samples) c
      (.done (some (acc.reverse ++ roots))) ∧ Specification input D L samples stages pre roots ∧
      (∀ record ∈ roots, record.coefficients.length = D + 1) ∧
      roots.length ≤ (stages.map (stageCount input)).sum ∧
      steps ≤ (stages.map (stageFuel input D L samples.length)).sum + acc.length + 3 ∧
      totalCost c ≤ (stages.map (stageWork input D L samples.length)).sum +
        6 * acc.length + 10 := by
  induction hchain generalizing pre acc with
  | @terminal Q ts layout rep nonzero last =>
      obtain ⟨c, ht, hc⟩ := reverse_trace input D L acc []
      simp only [List.append_nil] at ht
      have ht' := Trace.cons (Step.next (pre := pre) (xs := samples))
        (Trace.cons (Step.terminal (stage := ⟨ts, none⟩) rfl)
        (Trace.cons Step.scanned ht))
      refine ⟨[], acc.length + 5, charge 8 0 0 + (charge 3 0 0 + (charge 2 0 0 + c)),
        ?_, Specification.terminal ts pre, by simp,
        by simp [stageCount], ?_, ?_⟩
      · simpa only [List.append_nil, Nat.add_assoc] using ht'
      · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, stageFuel]
        omega
      · simp only [total_add, total_charge]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, stageWork]
        omega
  | @active Q ts stages j layout rep nonzero highest next ih =>
      obtain ⟨head, tail, hstages, hhead⟩ := chain_head next
      obtain ⟨A⟩ := ActiveOrderAdapter.exists_presentation ts Q j rep highest
      have hw : differentialWeightedDegree D (semanticEquation A.polynomial) < L := by
        rwa [A.weightedDegree]
      have hr : j.val ≤ D := (Nat.le_of_lt_succ j.isLt).trans hdepth
      have hl : D - j.val < L := ActiveOrderAdapter.lookup_of_highest Q j highest D L hweight
      let stage : Stage F := ⟨ts, some (j.val + 1, jetDegree Q j)⟩
      let context : Context F := ⟨stage, pre, head.equation⟩
      obtain ⟨candidates, cr, hrun, _hspec, hwidth, hcount, hcr⟩ :=
        CenterRootsMachine.computation_runFuel_correct A.polynomial input.alphabet ts
          points samples hsamples hq A.sparse_eq hr hl hw
      obtain ⟨nr, hnr, htr⟩ := CenterRootsMachine.runFuel_refines (centerInput input stage j.val)
        D L (CenterRootsMachine.fuel (centerInput input stage j.val) D L samples.length)
        (.start samples)
      change CenterRootsMachine.runFuel (centerInput input stage j.val) D L
        (CenterRootsMachine.fuel (centerInput input stage j.val) D L samples.length)
        (.start samples) = (.done (some candidates), cr) at hrun
      rw [hrun] at htr
      have hwnext : differentialWeightedDegree D (separant Q j) < L :=
        (weightedTotalDegree_pderiv_le (differentialWeight D) (some j) Q).trans_lt
          hweight
      obtain ⟨cc, htc, hcc⟩ := collect_trace input D L context candidates (head :: tail)
        (ts :: pre) acc samples
      obtain ⟨out, nt, ct, htt, hsem, houtwidth, houtcount, hnt, hct⟩ :=
        ih hwnext (ts :: pre) ((candidates.map (tagged context)).reverse ++ acc) (by
          intro record hm
          rcases List.mem_append.mp hm with hm | hm
          · obtain ⟨candidate, hcand, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hm)
            exact hwidth candidate hcand
          · exact hacc record hm)
      rw [hstages] at htt hsem
      have ht := Trace.cons Step.next (Trace.cons (Step.active (r := j.val) rfl)
        ((lift_roots input D L context j.val (head :: tail) (ts :: pre) acc samples htr).trans
          (Trace.cons Step.returned (htc.trans htt))))
      simp only [List.reverse_append, List.reverse_reverse, List.append_assoc] at ht
      rw [← hstages] at ht
      refine ⟨candidates.map (tagged context) ++ out, _, _, ht, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hstages]
        exact Specification.active rfl hrun hsem
      · intro record hm
        rcases List.mem_append.mp hm with hm | hm
        · obtain ⟨candidate, hcand, rfl⟩ := List.mem_map.mp hm
          exact hwidth candidate hcand
        · exact houtwidth record hm
      · simp only [List.length_append, List.length_map, List.map_cons, List.sum_cons,
          stageCount, Nat.add_sub_cancel]
        omega
      · simp only [List.length_append, List.length_reverse, List.length_map] at hnt
        simp only [List.map_cons, List.sum_cons, stageFuel, Nat.add_sub_cancel]
        dsimp [centerInput, stage] at hnr ⊢
        nlinarith
      · simp only [total_add, total_charge, CenterRootsMachine.total_wrapper]
        simp only [List.length_append, List.length_reverse, List.length_map] at hct
        simp only [List.map_cons, List.sum_cons, stageWork, Nat.add_sub_cancel]
        change totalCost cr ≤ CenterRootsMachine.workBound
          ⟨input.alphabet, ts, j.val⟩ D L samples.length at hcr
        dsimp [centerInput, stage] at hnr ⊢
        nlinarith

/-- Input-chain work bound and the exact finite sum of visited stage step budgets. -/
def fuelForStages (input : Input F) (D L n chainBudget : ℕ) (stages : List (Stage F)) : ℕ :=
  chainBudget + (stages.map (stageFuel input D L n)).sum + 5

/-- Complete work includes chain dispatch, selected-stage work, and final emission. -/
def workForStages (input : Input F) (D L n chainBudget : ℕ) (stages : List (Stage F)) : ℕ :=
  4 * chainBudget + (stages.map (stageWork input D L n)).sum + 20

private theorem Trace.runFuel_of_le {input : Input F} {D L n budget : ℕ}
    {s : Configuration F} {c : Cost} {out : Option (List (Record F))}
    (h : Trace input D L n s c (.done out)) (hle : n ≤ budget) :
    runFuel input D L budget s = (.done out, c) := by
  have hr := h.runFuel_done (budget - n)
  rwa [Nat.add_sub_of_le hle] at hr

/-- Chain-cost embedding preserves every primitive category. -/
theorem total_chain (c : MvPolynomial.SeparantChainMachine.Cost) :
    totalCost (chainCost c) = MvPolynomial.SeparantChainMachine.totalCost c := by
  simp [totalCost, CenterRootsMachine.totalCost, JetRootsMachine.totalCost,
    RegularRootMachine.totalCost, RegularLiftMachine.totalCost, DirectCoefficientMachine.totalCost,
    ResidualCoefficientMachine.totalCost, chainCost, MvPolynomial.SeparantChainMachine.totalCost,
    MvPolynomial.PartialDerivativeMachine.totalCost, Matrix.PivotSelectionMachine.totalCost]
  omega

/-- Closed execution constructs the actual chain, then enumerates its actual selected stages.
Its budget sums the visited polynomial stage costs; no external execution callback is assumed. -/
theorem execution_correct {D L : ℕ} (input : Input F) (points : Fin L ↪ F) (samples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i)) (hq : 0 < input.alphabet.length)
    (hdepth : input.order ≤ D) (Δ : ℕ) (Q : DifferentialPolynomial F input.order)
    (hl : MvPolynomial.DenseNormalizeMachine.DenseLayout (List.range (input.order + 2)) input.terms)
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial input.terms =
      MvPolynomial.rename HighestJetTransport.encodeJet Q) (hne : Q ≠ 0)
    (hchar : ∀ j, jetDegree Q j < ringChar F) (hdeg : jetTotalDegree Q ≤ Δ)
    (hweight : differentialWeightedDegree D Q < L) :
    let B := SeparantChainRefinement.budget Δ input.terms.length (input.order + 2)
      (MvPolynomial.PartialDerivativeMachine.inputMass input.terms)
    ∃ stages out c, SeparantChainRefinement.OrderedChain input.terms Q stages ∧
      stages.length ≤ Δ + 1 ∧
      runFuel input D L (fuelForStages input D L samples.length B stages) (.start samples) =
        (.done (some out), c) ∧ Specification input D L samples stages [] out ∧
      (∀ record ∈ out, record.coefficients.length = D + 1) ∧
      out.length ≤ (stages.map (stageCount input)).sum ∧
      totalCost c ≤ workForStages input D L samples.length B stages := by
  let B := SeparantChainRefinement.budget Δ input.terms.length (input.order + 2)
    (MvPolynomial.PartialDerivativeMachine.inputMass input.terms)
  obtain ⟨stages, nc, cc, htc, hchain, hlen, hcc⟩ := SeparantChainRefinement.closed_trace Δ
    input.terms.length (MvPolynomial.PartialDerivativeMachine.inputMass input.terms)
    input.terms [] Q hl hQ hne hchar hdeg le_rfl le_rfl
  simp only [List.reverse_nil, List.nil_append] at htc
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hcc
  change nc + MvPolynomial.SeparantChainMachine.totalCost cc ≤ B at hcc
  obtain ⟨out, ns, cs, hts, hspec, hwidth, hcount, hns, hcs⟩ :=
    scan_trace input points samples hsamples hq hdepth hchain hweight [] [] (by simp)
  simp only [List.reverse_nil, List.nil_append] at hts
  simp only [List.length_nil, Nat.add_zero, Nat.mul_zero] at hns hcs
  have ht := Trace.cons Step.start ((lift_chain input D L samples htc).trans
    (Trace.cons Step.chained hts))
  have hrun := ht.runFuel_of_le (budget := fuelForStages input D L samples.length B stages) (by
    dsimp [fuelForStages]
    omega)
  refine ⟨stages, out, _, hchain, hlen, hrun, hspec, hwidth, hcount, ?_⟩
  simp only [total_add, total_charge, total_chain, total_wrapper]
  dsimp [workForStages]
  omega

/-- Every returned record exposes its exact position, immutable prefix, and actual center run. -/
theorem Specification.member {input : Input F} {D L : ℕ} {samples : List F}
    {stages : List (Stage F)} {pre : List (List (Term F))} {out : List (Record F)}
    (h : Specification input D L samples stages pre out) (record : Record F) (hm : record ∈ out) :
    ∃ before next tail r e candidates c,
      stages = before ++ record.context.stage :: next :: tail ∧
      record.context.previous = (before.map (fun stage ↦ stage.equation)).reverse ++ pre ∧
      record.context.separant = next.equation ∧
      record.context.stage.selected = some (r + 1, e) ∧
      CenterRootsMachine.runFuel (centerInput input record.context.stage r) D L
        (CenterRootsMachine.fuel (centerInput input record.context.stage r) D L samples.length)
        (.start samples) = (.done (some candidates), c) ∧
      (record.center, record.coefficients) ∈ candidates := by
  induction h with
  | terminal ts pre => simp at hm
  | @active stage next stages pre r e candidates out c selected run tail ih =>
      rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨candidate, hcand, rfl⟩ := List.mem_map.mp hm
        exact ⟨[], next, stages, r, e, candidates, c, rfl, rfl, rfl, selected, run,
          by simpa [tagged] using hcand⟩
      · obtain ⟨before, after, rest, r', e', candidates', c', hstages, hpre, hsep,
          hselected, hrun, hcand⟩ := ih hm
        refine ⟨stage :: before, after, rest, r', e', candidates', c', ?_, ?_, hsep,
          hselected, hrun, hcand⟩
        · simp only [List.cons_append]
          rw [hstages]
        · simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
            List.singleton_append] using hpre

/-- Each output context refers to the literal earlier prefix and immediate successor. -/
theorem Specification.hasContext {input : Input F} {D L : ℕ} {samples : List F}
    {stages : List (Stage F)} {out : List (Record F)}
    (h : Specification input D L samples stages [] out) (record : Record F) (hm : record ∈ out) :
    HasContext stages record.context := by
  obtain ⟨before, next, tail, _, _, _, _, hstages, hpre, hsep, _⟩ := h.member record hm
  exact ⟨before, tail, next, hstages, by simpa using hpre, hsep⟩

end ReedSolomon.HiddenDerivative.StageRootsMachine
