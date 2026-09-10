/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Selection.RestrictedStageRoots
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Selection.SeparateSampleSelection
/-!
# Canonical restricted-alphabet witnesses for actual stage roots

A reduced separant degree bound finds regular centers within the enumeration alphabet.
Recovery still uses its independent full interpolation samples. Guard-grid vanishing is never
used to infer a global identity; the actual solution supplies the globally solved prefix.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.CanonicalRootSelection

open Polynomial CompPoly PolynomialDifferential
open StageRootsMachine (Record Stage Term)

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- A nonzero polynomial has a nonzero value on any longer list of distinct points. -/
theorem exists_eval_nonzero_on (p : F[X]) (hp : p ≠ 0) (xs : List F) (hn : xs.Nodup)
    (hd : p.natDegree < xs.length) : ∃ a ∈ xs, p.eval a ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply hp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p xs.toFinset
    (fun a ha ↦ h a (List.mem_toFinset.mp ha))
  simpa only [List.toFinset_card_of_nodup hn] using hd

omit [DecidableEq F] in
/-- The existing witness program chooses the first nonzero point on the restricted guard grid. -/
theorem first_nonzero_sample_on {d : ℕ} (R : DifferentialPolynomial F d)
    (ts : List (Term F)) (hR : MvPolynomial.EvaluationMachine.sparsePolynomial ts =
      MvPolynomial.rename HighestJetTransport.encodeJet R)
    (f : F[X]) (cs : List F) (hcs : JetHornerMachine.coefficientPolynomial cs = f)
    (hne : differentialSpecialization R f ≠ 0) (xs : List F) (hn : xs.Nodup)
    (hd : (differentialSpecialization R f).natDegree < xs.length) :
    ∃ a before after, xs = before ++ a :: after ∧
      (∀ x ∈ before, (differentialSpecialization R f).eval x = 0) ∧
      (differentialSpecialization R f).eval a ≠ 0 := by
  classical
  obtain ⟨a, ha, hev⟩ := exists_eval_nonzero_on _ hne xs hn hd
  have hw : ResidualWitnessMachine.result ⟨cs, ts, 0, d⟩ xs ≠ none := by
    intro h
    have hz := (ResidualWitnessMachine.result_eq_none_iff _ _).mp h a ha
    rw [sample_eq R ts hR cs f hcs a] at hz
    exact hev hz
  cases hr : ResidualWitnessMachine.result ⟨cs, ts, 0, d⟩ xs with
  | none => exact False.elim (hw hr)
  | some a =>
      obtain ⟨before, after, he, hb, ha⟩ := (witness_iff R ts hR cs f hcs xs a).mp hr
      exact ⟨a, before, after, he, hb, ha⟩

variable [Finite F]

/-- A bounded root with enumerated jets is selected at its first regular alphabet center. -/
theorem selected_complete_of_jet_mem {d D L : ℕ} (input : StageRootsMachine.Input F)
    (points : Fin L ↪ F) (samples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i)) (hn : input.alphabet.Nodup)
    (hdepth : d ≤ D) {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {stages : List (Stage F)} (hchain : SeparantChainRefinement.OrderedChain ts Q stages)
    (hne : Q ≠ 0) (hchar : IsBelowCharacteristic D Q)
    (hweight : differentialWeightedDegree D Q < L)
    {out : List (Record F)}
    (hspec : StageRootsMachine.Specification input D L samples stages [] out)
    (P : BoundedSolution Q D)
    (hcard : differentialWeightedDegree D Q - (D - d) < input.alphabet.length)
    (hjets : ∀ a ∈ input.alphabet, ∀ j : Fin (d + 1),
      polynomialJet a P.polynomial j ∈ input.alphabet) :
    ∃ record ∈ selected d input.alphabet out,
      JetHornerMachine.coefficientPolynomial record.coefficients = P.polynomial := by
  obtain ⟨witness, hwne, hwdegree, hwcover⟩ := exists_chainWitness_polynomial Q hne hchar P
  obtain ⟨oldCenter, holdCenter, hwitness⟩ := exists_eval_nonzero_on witness hwne
    input.alphabet hn (hwdegree.trans_lt hcard)
  obtain ⟨before, stage, after, he, hbefore, hregular⟩ :=
    OrderedChainRegularWitness.chainWitness_record (hwcover oldCenter hwitness) ts stages hchain
  obtain ⟨R, j, hR, hj, hselected, hroot, hreg, hneR⟩ := hregular
  obtain ⟨next, tail, hafter, hsep⟩ := chain_successor hchain before stage after he R hR j hj
  have hmem : stage ∈ stages := by simp [he]
  have hnSep : differentialSpecialization (separant R j) P.polynomial ≠ 0 := by
    intro hz
    have hev := congrArg (fun f : F[X] ↦ f.eval oldCenter) hz
    have hg := hreg.2
    rw [← eval_differentialSpecialization] at hg
    exact hg (by simpa using hev)
  obtain ⟨oldRecord, _holdmem, _hstage, _hpre, _hcenter, hpoly⟩ :=
    hspec.regular_record_complete_of_jet_mem input points samples hsamples hdepth hchain
      hchar hweight
      before stage after he P.polynomial (natDegree_le_of_degree_le P.degree_le) oldCenter
      holdCenter (hjets oldCenter holdCenter) ⟨R, j, hR, hj, hselected, hroot, hreg, hneR⟩
  have hsepDegree : (differentialSpecialization (separant R j) P.polynomial).natDegree <
      input.alphabet.length := by
    have hb := natDegree_differentialSpecialization_separant_le_sub R j P.polynomial
      (natDegree_le_of_degree_le P.degree_le)
    have hw := ActiveOrderAdapter.record_weight hchain D stage hmem R hR
    have hj : j.val ≤ d := Nat.le_of_lt_succ j.isLt
    omega
  obtain ⟨a, samplePre, samplePost, hs, hp, ha⟩ := first_nonzero_sample_on (separant R j)
    next.equation hsep P.polynomial oldRecord.coefficients hpoly hnSep input.alphabet hn hsepDegree
  have hacenter : a ∈ input.alphabet := by simp [hs]
  have hnew : OrderedChainRegularWitness.RegularRecord (d := d) P.polynomial a stage := by
    refine ⟨R, j, hR, hj, hselected, hroot, ⟨?_, ?_⟩, hneR⟩
    · rw [← eval_differentialSpecialization, hroot]
      simp
    · rwa [← eval_differentialSpecialization]
  obtain ⟨record, hm, hstage, hpre, hcenter, hpoly'⟩ :=
    hspec.regular_record_complete_of_jet_mem input
    points samples hsamples hdepth hchain hchar hweight
    before stage after he
    P.polynomial (natDegree_le_of_degree_le P.degree_le) a hacenter
    (hjets a hacenter) hnew
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
    change ResidualZeroMachine.result ⟨record.coefficients, eqs, 0, d⟩ input.alphabet = true
    rw [hpre, List.mem_reverse] at heqs
    obtain ⟨earlier, hearler, rfl⟩ := List.mem_map.mp heqs
    obtain ⟨S, hS, hz⟩ := hbefore earlier hearler
    exact zero_of_identity S earlier.equation hS record.coefficients P.polynomial hpoly' hz
      input.alphabet
  · change ResidualWitnessMachine.result
      ⟨record.coefficients, record.context.separant, 0, d⟩ input.alphabet = some record.center
    rw [hsepRecord, hcenter]
    exact (witness_iff (separant R j) next.equation hsep record.coefficients P.polynomial hpoly'
      input.alphabet a).mpr ⟨samplePre, samplePost, hs, hp, ha⟩

end ReedSolomon.HiddenDerivative.CanonicalRootSelection
