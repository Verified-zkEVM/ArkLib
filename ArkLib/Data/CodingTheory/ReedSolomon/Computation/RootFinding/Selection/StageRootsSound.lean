/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.StageRootsSemantics
public import
  ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.OrderedChainRegularWitness

-- The completeness witness reduces `ringEquiv.symm` back to its polynomial semantics.
import all CompPoly.Univariate.ToPoly.Core
import all CompPoly.Univariate.ToPoly.Equiv
/-!
# Semantic certificates for context-tagged stage roots

Every returned candidate solves its actual current stage equation at its recorded center.
Completeness is attached to concrete center executions at actual chain positions.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.StageRootsMachine

open Polynomial CompPoly PolynomialDifferential

variable {F : Type*} [Field F] [DecidableEq F]

/-- Every actual active-stage callee output is retained at its exact context and chain position. -/
theorem Specification.atStage {input : Input F} {D L : ℕ} {samples : List F}
    {stages : List (Stage F)} {pre : List (List (Term F))} {out : List (Record F)}
    (h : Specification input D L samples stages pre out) (before : List (Stage F))
    (stage : Stage F) (after : List (Stage F)) (he : stages = before ++ stage :: after)
    (r e : ℕ) (hs : stage.selected = some (r + 1, e)) :
    ∃ next tail candidates c, after = next :: tail ∧
      CenterRootsMachine.runFuel (centerInput input stage r) D L
        (CenterRootsMachine.fuel (centerInput input stage r) D L samples.length)
        (.start samples) = (.done (some candidates), c) ∧
      ∀ candidate ∈ candidates,
        tagged ⟨stage, (before.map (fun stage ↦ stage.equation)).reverse ++ pre, next.equation⟩
          candidate ∈ out := by
  induction before generalizing stages pre out with
  | nil =>
      simp only [List.nil_append] at he
      subst stages
      cases h with
      | terminal ts pre => cases hs
      | @active stage next stages pre r' e' candidates out c selected run tail =>
          have heq : (r + 1, e) = (r' + 1, e') := Option.some.inj (hs.symm.trans selected)
          have hh := (Prod.mk.inj heq).1
          have hr : r = r' := by omega
          subst r'
          refine ⟨next, stages, candidates, c, rfl, run, ?_⟩
          intro candidate hcand
          apply List.mem_append_left
          exact List.mem_map.mpr ⟨candidate, hcand, rfl⟩
  | cons first before ih =>
      simp only [List.cons_append] at he
      cases h with
      | terminal ts pre =>
          have hn := congrArg List.length he
          simp only [List.length_cons, List.length_nil, List.length_append] at hn
          omega
      | @active current next stages pre r' e' candidates out c selected run tail =>
          obtain ⟨hfirst, htail⟩ := List.cons.inj he
          subst current
          obtain ⟨next', tail', candidates', c', ha, hr, hm⟩ := ih tail htail
          refine ⟨next', tail', candidates', c', ha, hr, ?_⟩
          intro candidate hcand
          apply List.mem_append_right
          simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
            List.singleton_append] using hm candidate hcand

/-- The actual stage output solves its represented ambient equation and preserves an initial jet. -/
theorem Specification.output_sound {d D L : ℕ} (input : Input F)
    (points : Fin L ↪ F) (samples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i)) (hq : 0 < input.alphabet.length)
    (hdepth : d ≤ D) {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {stages : List (Stage F)} (hchain : SeparantChainRefinement.OrderedChain ts Q stages)
    (hchar : ∀ j, jetDegree Q j < ringChar F) (hweight : differentialWeightedDegree D Q < L)
    {out : List (Record F)} (hspec : Specification input D L samples stages [] out)
    (record : Record F) (hm : record ∈ out) :
    HasContext stages record.context ∧ record.coefficients.length = D + 1 ∧
      record.center ∈ input.alphabet ∧
      ∃ R : DifferentialPolynomial F d, ∃ s : Fin (d + 1),
        ∃ _A : ActiveOrderAdapter.Presentation record.context.stage.equation R s,
          differentialSpecialization R
            (JetHornerMachine.coefficientPolynomial record.coefficients) = 0 ∧
          ∃ js ∈ JetRootsMachine.tuples input.alphabet (s.val + 1), polynomialJet record.center
            (JetHornerMachine.coefficientPolynomial record.coefficients) =
              JetRootsMachine.jetFunction s.val js := by
  obtain ⟨before, next, tail, r, e, candidates, c, hstages, _hpre, _hsep, hselected,
    hrun, hcand⟩ := hspec.member record hm
  have hmem : record.context.stage ∈ stages := by simp [hstages]
  obtain ⟨R, s, A, hi, _he, hs, _hne, hhigh, hw, _hc⟩ :=
    ActiveOrderAdapter.of_chain_record hchain hchar record.context.stage hmem (r + 1) e hselected
  have hr : r = s.val := by omega
  subst r
  have hcurrent : differentialWeightedDegree D (semanticEquation A.polynomial) < L :=
    (hw D).trans_lt hweight
  have hl := ActiveOrderAdapter.lookup_of_highest (semanticEquation A.polynomial)
    (Fin.last s.val) hhigh D L hcurrent
  obtain ⟨actual, ca, hactual, hpoly, hwidth, _hcount, _hcost⟩ :=
    CenterRootsMachine.computation_runFuel_correct A.polynomial input.alphabet
      record.context.stage.equation points samples hsamples hq A.sparse_eq
      (hs.trans hdepth) hl hcurrent
  change CenterRootsMachine.runFuel (centerInput input record.context.stage s.val) D L
    (CenterRootsMachine.fuel (centerInput input record.context.stage s.val) D L samples.length)
    (.start samples) = (.done (some actual), ca) at hactual
  have heq := hrun.symm.trans hactual
  cases heq
  obtain ⟨hcenter, hroot, hjet⟩ := CenterRootsMachine.output_sound A.polynomial D input.alphabet
    candidates hpoly (record.center, record.coefficients) hcand
  refine ⟨hspec.hasContext record hm, hwidth _ hcand, hcenter, R, s, A, ?_, hjet⟩
  rwa [A.specialization] at hroot

/-- The exact center specification retains a bounded root at each prescribed regular center. -/
theorem center_complete_at {r D : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F)
    (alphabet : List F) (hall : ∀ x : F, x ∈ alphabet) (a : F) (f : F[X])
    (hd : f.natDegree ≤ D) (hr : differentialSpecialization (semanticEquation Q) f = 0)
    (hregular : IsRegularJet (semanticEquation Q) (Fin.last r) a (polynomialJet a f))
    (hchar : D < ringChar F) (out : List (CenterRootsMachine.Record F))
    (hspec : out.map CenterRootsMachine.recordPolynomial =
      alphabet.flatMap (CenterRootsMachine.centerSpec Q alphabet D)) :
    ∃ cs, (a, cs) ∈ out ∧ JetHornerMachine.coefficientPolynomial cs = f := by
  let : Fintype F := Fintype.ofList alphabet hall
  let jet : Fin (r + 1) → F := polynomialJet a f
  let js := List.ofFn jet
  have hmem : js ∈ JetRootsMachine.tuples alphabet (r + 1) :=
    JetRootsMachine.mem_tuples_of_entries alphabet js (r + 1) (by simp [js])
      (fun x _ ↦ hall x)
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
    refine ⟨a, hall a, List.mem_map.mpr ⟨f, ?_, rfl⟩⟩
    exact List.mem_filterMap.mpr ⟨js, hmem, hjs⟩
  obtain ⟨⟨b, cs⟩, hcs, heq⟩ := List.mem_map.mp hfmem
  obtain ⟨hab, hpoly⟩ := Prod.mk.inj heq
  change b = a at hab
  subst b
  exact ⟨cs, hcs, hpoly⟩

/-- A prescribed regular actual record and center yields a retained candidate at that context. -/
theorem Specification.regular_record_complete {d D L : ℕ} (input : Input F)
    (points : Fin L ↪ F) (samples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i)) (hall : ∀ x : F, x ∈ input.alphabet)
    (hdepth : d ≤ D) {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {stages : List (Stage F)} (hchain : SeparantChainRefinement.OrderedChain ts Q stages)
    (hchar : IsBelowCharacteristic D Q) (hweight : differentialWeightedDegree D Q < L)
    {out : List (Record F)} (hspec : Specification input D L samples stages [] out)
    (before : List (Stage F)) (stage : Stage F) (after : List (Stage F))
    (he : stages = before ++ stage :: after) (f : F[X]) (hd : f.natDegree ≤ D) (a : F)
    (hregular : OrderedChainRegularWitness.RegularRecord (d := d) f a stage) :
    ∃ record ∈ out, record.context.stage = stage ∧
      record.context.previous = (before.map (fun stage ↦ stage.equation)).reverse ∧
      record.center = a ∧ JetHornerMachine.coefficientPolynomial record.coefficients = f := by
  have hmem : stage ∈ stages := by simp [he]
  obtain ⟨R, s, A, _hs, hhigh, hselected, _hne, hreg, hroot⟩ := hregular.presentation
  obtain ⟨hr, hl, hw, hc⟩ := ActiveOrderAdapter.root_bounds hchain D L hdepth hchar hweight
    stage hmem R s A hhigh
  obtain ⟨next, tail, candidates, c, _hafter, hrun, hretain⟩ :=
    hspec.atStage before stage after he s.val _ hselected
  obtain ⟨actual, ca, hactual, hpoly, _hwidth, _hcount, _hcost⟩ :=
    CenterRootsMachine.computation_runFuel_correct A.polynomial input.alphabet stage.equation
      points samples hsamples (List.length_pos_of_mem (hall 0)) A.sparse_eq hr hl hw
  change CenterRootsMachine.runFuel (centerInput input stage s.val) D L
    (CenterRootsMachine.fuel (centerInput input stage s.val) D L samples.length)
    (.start samples) = (.done (some actual), ca) at hactual
  have heq := hrun.symm.trans hactual
  cases heq
  obtain ⟨cs, hcs, hf⟩ := center_complete_at A.polynomial input.alphabet hall a f hd hroot hreg
    hc.1 candidates hpoly
  refine ⟨tagged ⟨stage, (before.map (fun stage ↦ stage.equation)).reverse, next.equation⟩
    (a, cs), ?_, rfl, rfl, rfl, hf⟩
  simpa using hretain (a, cs) hcs

/-- Every bounded initial root has a retained regular stage record after an entirely solved prefix.
The regular-record existence premise is derived from the actual chain and field-size hypothesis. -/
theorem Specification.bounded_root_complete {d D L : ℕ} (input : Input F)
    (points : Fin L ↪ F) (samples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i)) (hall : ∀ x : F, x ∈ input.alphabet)
    (hdepth : d ≤ D) {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {stages : List (Stage F)} (hchain : SeparantChainRefinement.OrderedChain ts Q stages)
    (hne : Q ≠ 0) (hchar : IsBelowCharacteristic D Q)
    (hweight : differentialWeightedDegree D Q < L)
    (hcard : differentialWeightedDegree D Q - (D - d) < Nat.card F)
    {out : List (Record F)} (hspec : Specification input D L samples stages [] out)
    (P : BoundedSolution Q D) :
    ∃ record ∈ out, JetHornerMachine.coefficientPolynomial record.coefficients = P.polynomial ∧
      OrderedChainRegularWitness.RegularRecord (d := d) P.polynomial record.center
        record.context.stage ∧
      ∀ eqs ∈ record.context.previous, ∃ R : DifferentialPolynomial F d,
        MvPolynomial.EvaluationMachine.sparsePolynomial eqs =
          MvPolynomial.rename HighestJetTransport.encodeJet R ∧
        differentialSpecialization R P.polynomial = 0 := by
  let : Fintype F := Fintype.ofList input.alphabet hall
  obtain ⟨a, before, stage, after, he, hbefore, hreg⟩ :=
    OrderedChainRegularWitness.bounded_root_regular_record Q hne hchar P ts stages hchain hcard
  obtain ⟨record, hm, hstage, hpre, hcenter, hpoly⟩ := hspec.regular_record_complete input
    points samples hsamples hall hdepth hchain hchar hweight before stage after he
    P.polynomial (Polynomial.natDegree_le_of_degree_le P.degree_le) a hreg
  refine ⟨record, hm, hpoly, by simpa [hcenter, hstage] using hreg, ?_⟩
  intro eqs heqs
  rw [hpre, List.mem_reverse] at heqs
  obtain ⟨earlier, hearler, rfl⟩ := List.mem_map.mp heqs
  exact hbefore earlier hearler

end ReedSolomon.HiddenDerivative.StageRootsMachine
