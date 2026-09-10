/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.StageRootsSound

-- The prescribed-center witness reduces `ringEquiv.symm` to polynomial semantics.
import all CompPoly.Univariate.ToPoly.Core
import all CompPoly.Univariate.ToPoly.Equiv
/-!
# Prescribed-center completeness for a restricted enumeration alphabet

Only the desired center and its initial jets must be enumerated. Root recovery still uses the
separate supplied residual samples and the existing actual center program.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.StageRootsMachine

open Polynomial CompPoly PolynomialDifferential

variable {F : Type*} [Field F] [DecidableEq F] [Finite F]

/-- A root with enumerated center and jets occurs in the exact center output specification. -/
theorem center_complete_at_of_jet_mem {r D : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F)
    (alphabet : List F) (a : F) (ha : a ∈ alphabet) (f : F[X])
    (hjet : ∀ j : Fin (r + 1), polynomialJet a f j ∈ alphabet)
    (hd : f.natDegree ≤ D) (hr : differentialSpecialization (semanticEquation Q) f = 0)
    (hregular : IsRegularJet (semanticEquation Q) (Fin.last r) a (polynomialJet a f))
    (hchar : D < ringChar F) (out : List (CenterRootsMachine.Record F))
    (hspec : out.map CenterRootsMachine.recordPolynomial =
      alphabet.flatMap (CenterRootsMachine.centerSpec Q alphabet D)) :
    ∃ cs, (a, cs) ∈ out ∧ JetHornerMachine.coefficientPolynomial cs = f := by
  let jet : Fin (r + 1) → F := polynomialJet a f
  let js := List.ofFn jet
  have hmem : js ∈ JetRootsMachine.tuples alphabet (r + 1) :=
    JetRootsMachine.mem_tuples_of_entries alphabet js (r + 1) (by simp [js])
      (by
        intro x hx
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
        exact hjet j)
  let P : CPolynomial F := CPolynomial.ringEquiv.symm (taylor a f)
  have hp : P.toPoly = taylor a f := CPolynomial.ringEquiv.apply_symm_apply _
  have hunshift : unshift a P = f := by simp [unshift, hp, taylor_taylor]
  have hdegreeP : P.natDegree ≤ D := by
    simpa only [CPolynomial.natDegree_toPoly, hp, natDegree_taylor] using hd
  have hsolution : directRegularSolution Q a jet D = some P :=
    (directRegularSolution_eq_some_iff Q a jet hregular D hchar P).mpr
      ⟨hdegreeP, by simpa [hunshift] using hr, by simp [hunshift, jet]⟩
  have hjs : JetRootsMachine.jetSolution Q a D js = some f := by
    rw [JetRootsMachine.jetSolution,
      show JetRootsMachine.jetFunction r js = jet from JetRootsMachine.jetFunction_ofFn r jet,
      hsolution]
    simp [hunshift]
  have hfmem : (a, f) ∈ out.map CenterRootsMachine.recordPolynomial := by
    rw [hspec]
    apply List.mem_flatMap.mpr
    refine ⟨a, ha, List.mem_map.mpr ⟨f, ?_, rfl⟩⟩
    exact List.mem_filterMap.mpr ⟨js, hmem, hjs⟩
  obtain ⟨⟨b, cs⟩, hcs, heq⟩ := List.mem_map.mp hfmem
  obtain ⟨hab, hpoly⟩ := Prod.mk.inj heq
  change b = a at hab
  subst b
  exact ⟨cs, hcs, hpoly⟩

/-- A prescribed regular actual record and center yields a retained candidate at that context. -/
theorem Specification.regular_record_complete_of_jet_mem {d D L : ℕ} (input : Input F)
    (points : Fin L ↪ F) (samples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i))
    (hdepth : d ≤ D) {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {stages : List (Stage F)} (hchain : SeparantChainRefinement.OrderedChain ts Q stages)
    (hchar : IsBelowCharacteristic D Q) (hweight : differentialWeightedDegree D Q < L)
    {out : List (Record F)} (hspec : Specification input D L samples stages [] out)
    (before : List (Stage F)) (stage : Stage F) (after : List (Stage F))
    (he : stages = before ++ stage :: after) (f : F[X]) (hd : f.natDegree ≤ D)
    (a : F) (ha : a ∈ input.alphabet)
    (hjet : ∀ j : Fin (d + 1), polynomialJet a f j ∈ input.alphabet)
    (hregular : OrderedChainRegularWitness.RegularRecord (d := d) f a stage) :
    ∃ record ∈ out, record.context.stage = stage ∧
      record.context.previous = (before.map (fun stage ↦ stage.equation)).reverse ∧
      record.center = a ∧ JetHornerMachine.coefficientPolynomial record.coefficients = f := by
  have hmem : stage ∈ stages := by simp [he]
  obtain ⟨R, s, A, hs, hhigh, hselected, _hne, hreg, hroot⟩ := hregular.presentation
  obtain ⟨hr, hl, hw, hc⟩ := ActiveOrderAdapter.root_bounds hchain D L hdepth hchar hweight
    stage hmem R s A hhigh
  obtain ⟨next, tail, candidates, c, _hafter, hrun, hretain⟩ :=
    hspec.atStage before stage after he s.val _ hselected
  obtain ⟨actual, ca, hactual, hpoly, _hwidth, _hcount, _hcost⟩ :=
    CenterRootsMachine.computation_runFuel_correct A.polynomial input.alphabet stage.equation
      points samples hsamples (List.length_pos_of_mem ha) A.sparse_eq hr hl hw
  change CenterRootsMachine.runFuel (centerInput input stage s.val) D L
    (CenterRootsMachine.fuel (centerInput input stage s.val) D L samples.length)
    (.start samples) = (.done (some actual), ca) at hactual
  have heq := hrun.symm.trans hactual
  cases heq
  obtain ⟨cs, hcs, hf⟩ := center_complete_at_of_jet_mem A.polynomial input.alphabet a ha f
    (fun j ↦ hjet ⟨j.val, by omega⟩) hd hroot hreg hc.1 candidates hpoly
  refine ⟨tagged ⟨stage, (before.map (fun stage ↦ stage.equation)).reverse, next.equation⟩
    (a, cs), ?_, rfl, rfl, rfl, hf⟩
  simpa using hretain (a, cs) hcs

end ReedSolomon.HiddenDerivative.StageRootsMachine
