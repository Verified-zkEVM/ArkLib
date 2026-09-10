/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.CollectorInputBounds
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.StageInputExecution
/-!+# Collector budgets for the actual ordered root records

The emitted context is a literal prefix and successor of the computed separant chain.
Consequently its equation masses and prefix length are bounded by the original input and
chain-length bound. Combining these facts with the actual record width and count removes
visited records from the collector's numerical fuel and work bounds. The guard grid may differ
from the recovery grid; no algebraic inference from guard-grid vanishing is used here.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.CanonicalOutputMachine

open HiddenDerivative PolynomialDifferential
open MvPolynomial.PartialDerivativeMachine (inputMass)

variable {F : Type*} [Field F] [DecidableEq F] {a b : F}
variable [Fact (∀ r : F, r ^ 2 ≠ a + b * r)]

/-- Actual contexts inherit the initial equation-mass bound and chain-length bound. -/
theorem context_input_bounds {d : ℕ}
    {ts : List (StageRootsMachine.Term (QuadraticAlgebra F a b))}
    {Q : DifferentialPolynomial (QuadraticAlgebra F a b) d}
    {stages : List (StageRootsMachine.Stage (QuadraticAlgebra F a b))}
    (hchain : SeparantChainRefinement.OrderedChain ts Q stages)
    (context : StageRootsMachine.Context (QuadraticAlgebra F a b))
    (hc : StageRootsMachine.HasContext stages context) :
    inputMass context.separant ≤ inputMass ts ∧
      (∀ q ∈ context.previous, inputMass q ≤ inputMass ts) ∧
      context.previous.length ≤ stages.length := by
  obtain ⟨pre, tail, next, he, hp, hs⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · rw [hs]
    exact (hchain.sizes next (by simp [he])).2
  · intro q hq
    rw [hp, List.mem_reverse] at hq
    obtain ⟨stage, hstage, rfl⟩ := List.mem_map.mp hq
    exact (hchain.sizes stage (by simp [he, hstage])).2
  · rw [hp, List.length_reverse, List.length_map, he, List.length_append]
    simp only [List.length_cons]
    omega

/-- Actual stage output bounds imply collector budgets with no visited-record parameter. -/
theorem generated_input_bounds {D L : ℕ}
    (input : StageRootsMachine.Input (QuadraticAlgebra F a b)) (k n Δ : ℕ)
    (samples testSamples : List (QuadraticAlgebra F a b))
    {Q : DifferentialPolynomial (QuadraticAlgebra F a b) input.order}
    {stages : List (StageRootsMachine.Stage (QuadraticAlgebra F a b))}
    {records : List (Record (QuadraticAlgebra F a b))}
    (hchain : SeparantChainRefinement.OrderedChain input.terms Q stages)
    (hlen : stages.length ≤ Δ + 1)
    (hspec : StageRootsMachine.Specification input D L samples stages [] records)
    (hw : ∀ r ∈ records, r.coefficients.length = D + 1)
    (hcount : records.length ≤ (Δ + 1) * input.alphabet.length ^ (input.order + 2)) :
    fuel input.order testSamples (D + 1) k n records ≤
        inputFuel (D + 1) input.order (inputMass input.terms) testSamples.length n
          (Δ + 1) ((Δ + 1) * input.alphabet.length ^ (input.order + 2)) ∧
      workBound input.order testSamples (D + 1) k n records ≤
        inputWork (D + 1) input.order (inputMass input.terms) testSamples.length n
          (Δ + 1) ((Δ + 1) * input.alphabet.length ^ (input.order + 2)) := by
  have hc := fun r hr ↦ context_input_bounds hchain r.context (hspec.hasContext r hr)
  exact input_bounds input.order (D + 1) k n (inputMass input.terms) (Δ + 1)
    ((Δ + 1) * input.alphabet.length ^ (input.order + 2)) testSamples records
    (fun r hr ↦ (hw r hr).le) (fun r hr ↦ (hc r hr).1)
    (fun r hr ↦ (hc r hr).2.1) (fun r hr ↦ (hc r hr).2.2.trans hlen) hcount

/-- The actual collector terminates at initial-size fuel, with the identical accepted output
and a work bound linear in the original alphabet power. This is an execution/cost theorem;
exact decoding and duplicate freedom follow from separate algebraic contracts. -/
theorem generated_runFuel {D L : ℕ}
    (input : StageRootsMachine.Input (QuadraticAlgebra F a b)) (k A Δ : ℕ)
    (samples testSamples : List (QuadraticAlgebra F a b)) (rows : List (F × F))
    {Q : DifferentialPolynomial (QuadraticAlgebra F a b) input.order}
    {stages : List (StageRootsMachine.Stage (QuadraticAlgebra F a b))}
    {records : List (Record (QuadraticAlgebra F a b))}
    (hchain : SeparantChainRefinement.OrderedChain input.terms Q stages)
    (hlen : stages.length ≤ Δ + 1)
    (hspec : StageRootsMachine.Specification input D L samples stages [] records)
    (hw : ∀ r ∈ records, r.coefficients.length = D + 1)
    (hcount : records.length ≤ (Δ + 1) * input.alphabet.length ^ (input.order + 2)) :
    let budget := inputFuel (D + 1) input.order (inputMass input.terms) testSamples.length
      rows.length (Δ + 1) ((Δ + 1) * input.alphabet.length ^ (input.order + 2))
    ∃ steps c, steps ≤ budget ∧
      Trace input.order testSamples (D + 1) k A rows steps (.start records) c
        (.done (result input.order testSamples (D + 1) k A rows records)) ∧
      runFuel input.order testSamples (D + 1) k A rows budget (.start records) =
        (.done (result input.order testSamples (D + 1) k A rows records), c) ∧
      c ≤ inputWork (D + 1) input.order (inputMass input.terms) testSamples.length
        rows.length (Δ + 1) ((Δ + 1) * input.alphabet.length ^ (input.order + 2)) := by
  obtain ⟨hf, hb⟩ := generated_input_bounds input k rows.length Δ samples testSamples
    hchain hlen hspec hw hcount
  obtain ⟨c, hr, hc⟩ := evaluation_runFuel input.order (D + 1) k A testSamples rows records hw
  obtain ⟨steps, hs, ht⟩ := runFuel_refines input.order (D + 1) k A
    (fuel input.order testSamples (D + 1) k rows.length records) testSamples rows (.start records)
  rw [hr] at ht
  refine ⟨steps, c, hs.trans hf, ht, ?_, hc.trans hb⟩
  simpa only [Nat.add_sub_of_le (hs.trans hf)] using
    ht.runFuel_done (inputFuel (D + 1) input.order (inputMass input.terms) testSamples.length
      rows.length (Δ + 1) ((Δ + 1) * input.alphabet.length ^ (input.order + 2)) - steps)

end ReedSolomon.ListDecoding.CanonicalOutputMachine
