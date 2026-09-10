/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Selection.CanonicalProof
/-!
# Canonical uniqueness with separate recovery and guard samples

Actual recovery uses its distinct sample grid and strict degree bound. Guard tests may use any
other list, including a restricted base alphabet. Global current identities imply these tests;
vanishing on the guard grid is never used to infer a global polynomial identity.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.CanonicalRootSelection

open Polynomial CompPoly PolynomialDifferential
open StageRootsMachine (Record Stage Term Context)

variable {F : Type*} [Field F] [DecidableEq F]

/-- Actual recovery certifies the global identity of each record's own current equation. -/
theorem current_identity {d D L : ℕ} (input : StageRootsMachine.Input F)
    (points : Fin L ↪ F) (samples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i)) (hq : 0 < input.alphabet.length)
    (hdepth : d ≤ D) {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {stages : List (Stage F)} (hchain : SeparantChainRefinement.OrderedChain ts Q stages)
    (hchar : ∀ j, jetDegree Q j < ringChar F) (hweight : differentialWeightedDegree D Q < L)
    {out : List (Record F)} {previous : List (List (Term F))}
    (hspec : StageRootsMachine.Specification input D L samples stages previous out)
    (record : Record F) (hm : record ∈ out) :
    record.coefficients.length = D + 1 ∧
      OrderedChainRegularWitness.SolvesRecord (d := d)
        (JetHornerMachine.coefficientPolynomial record.coefficients) record.context.stage := by
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
  change CenterRootsMachine.runFuel
    (StageRootsMachine.centerInput input record.context.stage s.val)
    D L (CenterRootsMachine.fuel (StageRootsMachine.centerInput input record.context.stage s.val)
      D L samples.length) (.start samples) = (.done (some actual), ca) at hactual
  have heq := hrun.symm.trans hactual
  cases heq
  obtain ⟨_hcenter, hroot, _hjet⟩ := CenterRootsMachine.output_sound A.polynomial D input.alphabet
    candidates hpoly (record.center, record.coefficients) hcand
  have hz : differentialSpecialization R
      (JetHornerMachine.coefficientPolynomial record.coefficients) = 0 := by
    rwa [A.specialization] at hroot
  exact ⟨hwidth _ hcand, R, A.natural_eq, hz⟩

/-- A globally solved actual current equation vanishes on any chosen guard samples. -/
theorem current_zero_on {d D L : ℕ} (input : StageRootsMachine.Input F)
    (points : Fin L ↪ F) (samples testSamples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i)) (hq : 0 < input.alphabet.length)
    (hdepth : d ≤ D) {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {stages : List (Stage F)} (hchain : SeparantChainRefinement.OrderedChain ts Q stages)
    (hchar : ∀ j, jetDegree Q j < ringChar F) (hweight : differentialWeightedDegree D Q < L)
    {out : List (Record F)} {previous : List (List (Term F))}
    (hspec : StageRootsMachine.Specification input D L samples stages previous out)
    (record : Record F) (hm : record ∈ out) :
    record.coefficients.length = D + 1 ∧
      ResidualZeroMachine.result ⟨record.coefficients, record.context.stage.equation, 0, d⟩
        testSamples = true := by
  obtain ⟨hw, R, hrep, hz⟩ := current_identity input points samples hsamples hq hdepth hchain
    hchar hweight hspec record hm
  exact ⟨hw, zero_of_identity R record.context.stage.equation hrep record.coefficients _ rfl
    hz testSamples⟩

/-- Earlier witness and later current or prefix tests conflict on the same arbitrary guard grid. -/
theorem excludes_later_on {d D L : ℕ} {input : StageRootsMachine.Input F} {samples : List F}
    {first : Stage F} {stages : List (Stage F)} {pre : List (List (Term F))}
    {out : List (Record F)} (testSamples : List F)
    (h : StageRootsMachine.Specification input D L samples (first :: stages) pre out)
    (earlier later : Record F) (hm : later ∈ out)
    (hsep : earlier.context.separant = first.equation)
    (hcs : earlier.coefficients = later.coefficients)
    (ha : accepted d testSamples earlier = true) (hb : accepted d testSamples later = true)
    (hz : ResidualZeroMachine.result
      ⟨later.coefficients, later.context.stage.equation, 0, d⟩ testSamples = true) : False := by
  have hf := CanonicalGuardMachine.separant_zero_test_false (guardInput d testSamples earlier)
    earlier.context.previous ha
  change ResidualZeroMachine.result
    ⟨earlier.coefficients, earlier.context.separant, 0, d⟩ testSamples = false at hf
  rw [hsep, hcs] at hf
  rcases first_or_previous h later hm with hcurrent | hprevious
  · rw [hcurrent, hf] at hz
    contradiction
  · have ht := ((CanonicalGuardMachine.result_eq_true_iff _ _).mp hb).1
      first.equation hprevious
    change ResidualZeroMachine.result
      ⟨later.coefficients, first.equation, 0, d⟩ testSamples = true at ht
    rw [hf] at ht
    contradiction

/-- Guard-selected polynomials remain unique with a separate arbitrary guard sample list. -/
theorem polynomials_nodup_on {d D L : ℕ} (input : StageRootsMachine.Input F)
    (points : Fin L ↪ F) (samples testSamples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i)) (hq : 0 < input.alphabet.length)
    (hn : input.alphabet.Nodup) (hdepth : d ≤ D)
    {ts : List (Term F)} {Q : DifferentialPolynomial F d} {stages : List (Stage F)}
    (hchain : SeparantChainRefinement.OrderedChain ts Q stages)
    (hchar : ∀ j, jetDegree Q j < ringChar F) (hweight : differentialWeightedDegree D Q < L)
    {out : List (Record F)} {pre : List (List (Term F))}
    (hspec : StageRootsMachine.Specification input D L samples stages pre out) :
    (polynomials d testSamples out).Nodup := by
  induction hspec generalizing ts Q with
  | terminal ts pre => simp [polynomials, selected]
  | @active stage next stages pre r e candidates out c selected run tail ih =>
      cases hchain with
      | @active Q ts tailStages j layout rep nonzero highest nextChain =>
          have hs := Option.some.inj selected
          have hr : r = j.val := by have hi := (Prod.mk.inj hs).1; omega
          subst r
          obtain ⟨A⟩ := ActiveOrderAdapter.exists_presentation ts Q j rep highest
          have hw : differentialWeightedDegree D (semanticEquation A.polynomial) < L := by
            rwa [A.weightedDegree]
          have hl := ActiveOrderAdapter.lookup_of_highest Q j highest D L hweight
          obtain ⟨actual, ca, hactual, hpoly, hwidth, _hcount, _hcost⟩ :=
            CenterRootsMachine.computation_runFuel_correct A.polynomial input.alphabet ts
              points samples hsamples hq A.sparse_eq
              ((Nat.le_of_lt_succ j.isLt).trans hdepth) hl hw
          change CenterRootsMachine.runFuel
            (StageRootsMachine.centerInput input ⟨ts, some (j.val + 1, jetDegree Q j)⟩ j.val) D L
            (CenterRootsMachine.fuel
              (StageRootsMachine.centerInput input ⟨ts, some (j.val + 1, jetDegree Q j)⟩ j.val)
              D L samples.length) (.start samples) = (.done (some actual), ca) at hactual
          have heq := run.symm.trans hactual
          cases heq
          have hpairs : (candidates.map CenterRootsMachine.recordPolynomial).Nodup := by
            rw [hpoly]
            exact center_pairs_nodup A.polynomial input.alphabet hn
          have hctail : ∀ k, jetDegree (separant Q j) k < ringChar F := fun k ↦
            (jetDegree_separant_le Q j k).trans_lt (hchar k)
          have hwtail : differentialWeightedDegree D (separant Q j) < L :=
            (weightedTotalDegree_pderiv_le (differentialWeight D) (some j) Q).trans_lt hweight
          have hntail := ih nextChain hctail hwtail
          let context : Context F :=
            ⟨⟨ts, some (j.val + 1, jetDegree Q j)⟩, pre, next.equation⟩
          have hnhead := center_selection_nodup d D testSamples context candidates hwidth hpairs
          change List.Nodup
            (polynomials d testSamples (candidates.map (StageRootsMachine.tagged context) ++ out))
          simp only [polynomials, CanonicalRootSelection.selected, List.filter_append,
            List.map_append, List.nodup_append]
          refine ⟨hnhead, hntail, ?_⟩
          intro f hf g hg hefg
          obtain ⟨earlier, hearlier, hef⟩ := List.mem_map.mp hf
          obtain ⟨hearlier, ha⟩ := List.mem_filter.mp hearlier
          obtain ⟨candidate, hcand, rfl⟩ := List.mem_map.mp hearlier
          obtain ⟨later, hlater, hlg⟩ := List.mem_map.mp hg
          obtain ⟨hlater, hb⟩ := List.mem_filter.mp hlater
          obtain ⟨hlwidth, hlzero⟩ :=
            current_zero_on input points samples testSamples hsamples hq hdepth
            nextChain hctail hwtail tail later hlater
          have hepoly : JetHornerMachine.coefficientPolynomial candidate.2 =
              JetHornerMachine.coefficientPolynomial later.coefficients :=
            hef.trans (hefg.trans hlg.symm)
          have hcoeff := coefficients_unique candidate.2 later.coefficients
            ((hwidth candidate hcand).trans hlwidth.symm) hepoly
          exact excludes_later_on testSamples tail
            (StageRootsMachine.tagged context candidate) later hlater
            rfl hcoeff ha hb hlzero

end ReedSolomon.HiddenDerivative.CanonicalRootSelection
