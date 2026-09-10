/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Selection.Canonical
/-!
# Sound and complete canonical root selection

Completeness first fixes a globally first nonzero separant stage. It then chooses the first
nonzero supplied sample at that stage, and uses prescribed-center retention in the actual driver.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.CanonicalRootSelection

open Polynomial CompPoly PolynomialDifferential
open StageRootsMachine (Record Stage Term Context)

variable {F : Type*} [Field F] [DecidableEq F]

/-- A selected record denotes a bounded root of the initial equation. -/
theorem selected_sound {d D L : ℕ} (input : StageRootsMachine.Input F)
    (points : Fin L ↪ F) (samples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i)) (hq : 0 < input.alphabet.length)
    (hdepth : d ≤ D) {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial ts =
      MvPolynomial.rename HighestJetTransport.encodeJet Q)
    {stages : List (Stage F)} (hchain : SeparantChainRefinement.OrderedChain ts Q stages)
    (hchar : ∀ j, jetDegree Q j < ringChar F) (hweight : differentialWeightedDegree D Q < L)
    {out : List (Record F)}
    (hspec : StageRootsMachine.Specification input D L samples stages [] out)
    (record : Record F) (hm : record ∈ selected d samples out) :
    (JetHornerMachine.coefficientPolynomial record.coefficients).natDegree ≤ D ∧
      differentialSpecialization Q
        (JetHornerMachine.coefficientPolynomial record.coefficients) = 0 := by
  obtain ⟨hm, ha⟩ := List.mem_filter.mp hm
  obtain ⟨hc, hwidth, _hcenter, R, s, A, hroot, _hjet⟩ := hspec.output_sound input points samples
    hsamples hq hdepth hchain hchar hweight record hm
  have hd : (JetHornerMachine.coefficientPolynomial record.coefficients).natDegree ≤ D := by
    have h := JetHornerMachine.degree_coefficientPolynomial_lt_length record.coefficients
    rw [hwidth] at h
    by_cases hz : JetHornerMachine.coefficientPolynomial record.coefficients = 0
    · simp [hz]
    · have hlt := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr h
      omega
  refine ⟨hd, ?_⟩
  rcases initial_or_previous hchain record.context hc with hcurrent | hprevious
  · have heq : R = Q := MvPolynomial.rename_injective HighestJetTransport.encodeJet
      HighestJetTransport.encodeJet_injective (by
        have hr := A.natural_eq
        rw [hcurrent] at hr
        exact hr.symm.trans hQ)
    simpa only [heq] using hroot
  · have hz := ((CanonicalGuardMachine.result_eq_true_iff _ _).mp ha).1 ts hprevious
    exact (zero_iff Q ts hQ record.coefficients _ rfl hd points samples hsamples hweight).mp hz

omit [DecidableEq F] in
/-- A globally nonzero represented equation has a first nonzero supplied sample under the budget. -/
theorem first_nonzero_sample {d D L : ℕ} (R : DifferentialPolynomial F d)
    (ts : List (Term F)) (hR : MvPolynomial.EvaluationMachine.sparsePolynomial ts =
      MvPolynomial.rename HighestJetTransport.encodeJet R)
    (f : F[X]) (cs : List F) (hcs : JetHornerMachine.coefficientPolynomial cs = f)
    (hd : f.natDegree ≤ D) (hne : differentialSpecialization R f ≠ 0)
    (points : Fin L ↪ F) (samples : List F) (hsamples : samples = List.ofFn (fun i ↦ points i))
    (hweight : differentialWeightedDegree D R < L) :
    ∃ a before after, samples = before ++ a :: after ∧
      (∀ x ∈ before, (differentialSpecialization R f).eval x = 0) ∧
      (differentialSpecialization R f).eval a ≠ 0 := by
  classical
  have hw : ResidualWitnessMachine.result ⟨cs, ts, 0, d⟩ samples ≠ none := by
    intro hn
    have hz := (ResidualZeroMachine.result_eq_true_iff _ _).mpr
      ((ResidualWitnessMachine.result_eq_none_iff _ _).mp hn)
    exact hne ((zero_iff R ts hR cs f hcs hd points samples hsamples hweight).mp hz)
  cases hr : ResidualWitnessMachine.result ⟨cs, ts, 0, d⟩ samples with
  | none => exact False.elim (hw hr)
  | some a =>
      obtain ⟨before, after, he, hb, ha⟩ := (witness_iff R ts hR cs f hcs samples a).mp hr
      exact ⟨a, before, after, he, hb, ha⟩

/-- Each bounded root is selected at its canonical stage's first nonzero supplied sample. -/
theorem selected_complete {d D L : ℕ} (input : StageRootsMachine.Input F)
    (points : Fin L ↪ F) (samples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i)) (hall : ∀ x : F, x ∈ input.alphabet)
    (hdepth : d ≤ D) {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {stages : List (Stage F)} (hchain : SeparantChainRefinement.OrderedChain ts Q stages)
    (hne : Q ≠ 0) (hchar : IsBelowCharacteristic D Q)
    (hweight : differentialWeightedDegree D Q < L)
    {out : List (Record F)}
    (hspec : StageRootsMachine.Specification input D L samples stages [] out)
    (P : BoundedSolution Q D) :
    ∃ record ∈ selected d samples out,
      JetHornerMachine.coefficientPolynomial record.coefficients = P.polynomial := by
  let : Fintype F := Fintype.ofList input.alphabet hall
  have hcard : differentialWeightedDegree D Q - (D - d) < Nat.card F := by
    have hL : L ≤ Fintype.card F := by
      simpa using Fintype.card_le_of_injective points points.injective
    rw [Nat.card_eq_fintype_card]
    omega
  obtain ⟨oldCenter, before, stage, after, he, hbefore, hregular⟩ :=
    OrderedChainRegularWitness.bounded_root_regular_record Q hne hchar P ts stages hchain hcard
  obtain ⟨R, j, hR, hj, hselected, hroot, hreg, hneR⟩ := hregular
  obtain ⟨next, tail, hafter, hsep⟩ := chain_successor hchain before stage after he R hR j hj
  have hmem : stage ∈ stages := by simp [he]
  have hwR := (ActiveOrderAdapter.record_weight hchain D stage hmem R hR).trans_lt hweight
  have hwSep : differentialWeightedDegree D (separant R j) < L :=
    (weightedTotalDegree_pderiv_le (differentialWeight D) (some j) R).trans_lt hwR
  have hnSep : differentialSpecialization (separant R j) P.polynomial ≠ 0 := by
    intro hz
    have hev := congrArg (fun f : F[X] ↦ f.eval oldCenter) hz
    have hg := hreg.2
    rw [← eval_differentialSpecialization] at hg
    exact hg (by simpa using hev)
  obtain ⟨oldRecord, _holdmem, _hstage, _hpre, _hcenter, hpoly⟩ :=
    hspec.regular_record_complete input points samples hsamples hall hdepth hchain hchar hweight
      before stage after he P.polynomial (natDegree_le_of_degree_le P.degree_le) oldCenter
      ⟨R, j, hR, hj, hselected, hroot, hreg, hneR⟩
  obtain ⟨a, samplePre, samplePost, hs, hp, ha⟩ := first_nonzero_sample (separant R j)
    next.equation hsep P.polynomial oldRecord.coefficients hpoly
    (natDegree_le_of_degree_le P.degree_le) hnSep points samples hsamples hwSep
  have hnew : OrderedChainRegularWitness.RegularRecord (d := d) P.polynomial a stage := by
    refine ⟨R, j, hR, hj, hselected, hroot, ⟨?_, ?_⟩, hneR⟩
    · rw [← eval_differentialSpecialization, hroot]
      simp
    · rwa [← eval_differentialSpecialization]
  obtain ⟨record, hm, hstage, hpre, hcenter, hpoly'⟩ := hspec.regular_record_complete input
    points samples hsamples hall hdepth hchain hchar hweight before stage after he
    P.polynomial (natDegree_le_of_degree_le P.degree_le) a hnew
  have hcontext := hspec.hasContext record hm
  obtain ⟨recordPre, recordTail, recordNext, hrecordStages, hrecordPre, hrecordSep⟩ := hcontext
  have hprelen : recordPre.length = before.length := by
    have hh := congrArg List.length (hrecordPre.symm.trans hpre)
    simpa using hh
  have hsplit := List.append_inj (he.symm.trans hrecordStages) hprelen.symm
  have hrest := List.cons.inj hsplit.2
  have hnext : recordNext = next := by
    rw [hafter] at hrest
    exact (List.cons.inj hrest.2).1.symm
  have hsepRecord : record.context.separant = next.equation := hrecordSep.trans (congrArg _ hnext)
  refine ⟨record, List.mem_filter.mpr ⟨hm, ?_⟩, hpoly'⟩
  apply (CanonicalGuardMachine.result_eq_true_iff _ _).mpr
  constructor
  · intro eqs heqs
    change ResidualZeroMachine.result ⟨record.coefficients, eqs, 0, d⟩ samples = true
    rw [hpre, List.mem_reverse] at heqs
    obtain ⟨earlier, hearler, rfl⟩ := List.mem_map.mp heqs
    obtain ⟨S, hS, hz⟩ := hbefore earlier hearler
    exact zero_of_identity S earlier.equation hS record.coefficients P.polynomial hpoly' hz samples
  · change ResidualWitnessMachine.result
      ⟨record.coefficients, record.context.separant, 0, d⟩ samples = some record.center
    rw [hsepRecord, hcenter]
    exact (witness_iff (separant R j) next.equation hsep record.coefficients P.polynomial hpoly'
      samples a).mpr ⟨samplePre, samplePost, hs, hp, ha⟩

end ReedSolomon.HiddenDerivative.CanonicalRootSelection
