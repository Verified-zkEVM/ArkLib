/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.CanonicalGuardUnique
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.StageRootsSound
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.JetRootsUnique

-- The canonical witnesses reduce `ringEquiv.symm` to polynomial semantics.
import all CompPoly.Univariate.ToPoly.Core
import all CompPoly.Univariate.ToPoly.Equiv
/-!
# Canonical selection from actual stage records

These proof-only subsequences use the concrete, execution-proved guard predicate. The guard always
uses the original maximum derivative order. No new executable filtering instruction is introduced.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.CanonicalRootSelection

open Polynomial CompPoly PolynomialDifferential
open StageRootsMachine (Record Stage Term Context)

/-- Guard inputs retain the original order and literal context pointers from the stage driver. -/
def guardInput {F : Type*} (d : ℕ) (samples : List F) (record : Record F) :
    CanonicalGuardMachine.Input F :=
  ⟨record.coefficients, samples, d, record.center, record.context.separant⟩

variable {F : Type*} [Field F] [DecidableEq F]

/-- The actual guard's execution-proved acceptance predicate. -/
def accepted (d : ℕ) (samples : List F) (record : Record F) : Bool :=
  CanonicalGuardMachine.result (guardInput d samples record) record.context.previous

/-- Proof-only accepted subsequence, preserving the original enumeration order. -/
def selected (d : ℕ) (samples : List F) (records : List (Record F)) : List (Record F) :=
  records.filter (accepted d samples)

/-- Global polynomial values of the accepted subsequence. -/
noncomputable def polynomials (d : ℕ) (samples : List F) (records : List (Record F)) : List F[X] :=
  (selected d samples records).map (fun r ↦ JetHornerMachine.coefficientPolynomial r.coefficients)

omit [DecidableEq F] in
/-- Physical width and global polynomial determine the entire descending coefficient vector. -/
theorem coefficients_unique (xs ys : List F) (hlen : xs.length = ys.length)
    (hp : JetHornerMachine.coefficientPolynomial xs = JetHornerMachine.coefficientPolynomial ys) :
    xs = ys := by
  induction xs generalizing ys with
  | nil => simpa using hlen.symm
  | cons a xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons b ys =>
          have hl : xs.length = ys.length := by simpa using hlen
          have he := congrArg (fun p : F[X] ↦ p.coeff xs.length) hp
          rw [JetHornerMachine.coeff_coefficientPolynomial_cons_length, hl,
            JetHornerMachine.coeff_coefficientPolynomial_cons_length] at he
          subst b
          rw [JetHornerMachine.coefficientPolynomial_cons,
            JetHornerMachine.coefficientPolynomial_cons, hl] at hp
          exact congrArg (a :: ·) (ih ys hl (add_left_cancel hp))

omit [DecidableEq F] in
/-- An ambient-order sparse equation evaluates the represented global polynomial exactly. -/
theorem sample_eq {d : ℕ} (Q : DifferentialPolynomial F d) (ts : List (Term F))
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial ts =
      MvPolynomial.rename HighestJetTransport.encodeJet Q) (cs : List F) (f : F[X])
    (hcs : JetHornerMachine.coefficientPolynomial cs = f) (a : F) :
    ResidualBatchMachine.sampleValue ⟨cs, ts, 0, d⟩ a =
      (differentialSpecialization Q f).eval a := by
  classical
  let P : CPolynomial F := CPolynomial.ringEquiv.symm f
  have hp : P.toPoly = f := CPolynomial.ringEquiv.apply_symm_apply _
  have hrep : MvPolynomial.EvaluationMachine.sparsePolynomial ts = MvPolynomial.rename Fin.val
      (CPoly.fromCMvPolynomial (ActiveOrderAdapter.concrete Q)) :=
    hQ.trans (ActiveOrderAdapter.natural_concrete Q).symm
  have hs := ResidualBatchMachine.sampleValue_eq_effectiveResidual
    (ActiveOrderAdapter.concrete Q) 0 a P cs ts (hcs.trans hp.symm) hrep
  simpa only [eval_effectiveResidual_eq_jet, zero_add, ← eval_differentialSpecialization,
    ActiveOrderAdapter.semantic_concrete, hp] using hs

/-- Sample identity tests coincide with global identities under the strict interpolation budget. -/
theorem zero_iff {d D L : ℕ} (Q : DifferentialPolynomial F d) (ts : List (Term F))
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial ts =
      MvPolynomial.rename HighestJetTransport.encodeJet Q) (cs : List F) (f : F[X])
    (hcs : JetHornerMachine.coefficientPolynomial cs = f) (hd : f.natDegree ≤ D)
    (points : Fin L ↪ F) (samples : List F) (hsamples : samples = List.ofFn (fun i ↦ points i))
    (hweight : differentialWeightedDegree D Q < L) :
    ResidualZeroMachine.result ⟨cs, ts, 0, d⟩ samples = true ↔
      differentialSpecialization Q f = 0 := by
  let P : CPolynomial F := CPolynomial.ringEquiv.symm f
  have hp : P.toPoly = f := CPolynomial.ringEquiv.apply_symm_apply _
  have hrep : MvPolynomial.EvaluationMachine.sparsePolynomial ts = MvPolynomial.rename Fin.val
      (CPoly.fromCMvPolynomial (ActiveOrderAdapter.concrete Q)) :=
    hQ.trans (ActiveOrderAdapter.natural_concrete Q).symm
  have hdeg : P.natDegree ≤ D := by simpa only [CPolynomial.natDegree_toPoly, hp] using hd
  have hw : differentialWeightedDegree D
      (semanticEquation (ActiveOrderAdapter.concrete Q)) < L := by
    simpa only [ActiveOrderAdapter.semantic_concrete] using hweight
  have h := CanonicalGuardMachine.zero_result_iff (ActiveOrderAdapter.concrete Q) P cs ts samples
    (hcs.trans hp.symm) hrep points hsamples hdeg hw
  simpa only [ActiveOrderAdapter.semantic_concrete, hp] using h

/-- A global identity always passes its concrete sample checks, without a degree premise. -/
theorem zero_of_identity {d : ℕ} (Q : DifferentialPolynomial F d) (ts : List (Term F))
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial ts =
      MvPolynomial.rename HighestJetTransport.encodeJet Q) (cs : List F) (f : F[X])
    (hcs : JetHornerMachine.coefficientPolynomial cs = f)
    (hz : differentialSpecialization Q f = 0) (samples : List F) :
    ResidualZeroMachine.result ⟨cs, ts, 0, d⟩ samples = true := by
  rw [ResidualZeroMachine.result_eq_true_iff]
  intro a _ha
  rw [sample_eq Q ts hQ cs f hcs a, hz]
  simp

/-- The concrete witness is precisely the first nonzero supplied sample of the global identity. -/
theorem witness_iff {d : ℕ} (Q : DifferentialPolynomial F d) (ts : List (Term F))
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial ts =
      MvPolynomial.rename HighestJetTransport.encodeJet Q) (cs : List F) (f : F[X])
    (hcs : JetHornerMachine.coefficientPolynomial cs = f) (samples : List F) (a : F) :
    ResidualWitnessMachine.result ⟨cs, ts, 0, d⟩ samples = some a ↔
      ∃ before after, samples = before ++ a :: after ∧
        (∀ x ∈ before, (differentialSpecialization Q f).eval x = 0) ∧
        (differentialSpecialization Q f).eval a ≠ 0 := by
  rw [ResidualWitnessMachine.result_eq_some_iff]
  simp only [sample_eq Q ts hQ cs f hcs]

/-- A literal suffix of the emitted chain remains an ordered chain at the original ambient order. -/
theorem chain_suffix {d : ℕ} {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {stages : List (Stage F)} (h : SeparantChainRefinement.OrderedChain ts Q stages)
    (before : List (Stage F)) (stage : Stage F) (after : List (Stage F))
    (he : stages = before ++ stage :: after) :
    ∃ R : DifferentialPolynomial F d,
      SeparantChainRefinement.OrderedChain stage.equation R (stage :: after) := by
  induction h generalizing before with
  | @terminal Q ts layout rep nonzero last =>
      cases before with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact ⟨Q, .terminal layout rep nonzero last⟩
      | cons first before =>
          have hl := congrArg List.length he
          simp only [List.length_cons, List.length_nil, List.length_append] at hl
          omega
  | @active Q ts tail j layout rep nonzero highest next ih =>
      cases before with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact ⟨Q, .active j layout rep nonzero highest next⟩
      | cons first before =>
          simp only [List.cons_append, List.cons.injEq] at he
          exact ih before he.2

/-- The initial equation is either current or belongs to the immutable earlier prefix. -/
theorem initial_or_previous {d : ℕ} {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {stages : List (Stage F)} (h : SeparantChainRefinement.OrderedChain ts Q stages)
    (context : Context F) (hc : StageRootsMachine.HasContext stages context) :
    context.stage.equation = ts ∨ ts ∈ context.previous := by
  obtain ⟨before, tail, next, he, hp, _hs⟩ := hc
  have hhead : ∃ head rest, stages = head :: rest ∧ head.equation = ts := by
    cases h with
    | terminal layout rep nonzero last => exact ⟨_, [], rfl, rfl⟩
    | active j layout rep nonzero highest next => exact ⟨_, _, rfl, rfl⟩
  obtain ⟨head, rest, hst, hts⟩ := hhead
  rw [hst] at he
  cases before with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at he
      exact Or.inl (he.1 ▸ hts)
  | cons first before =>
      simp only [List.cons_append, List.cons.injEq] at he
      right
      rw [hp, List.mem_reverse]
      exact List.mem_map.mpr ⟨first, by simp, by simpa [he.1] using hts⟩

/-- The immediate successor of an active record represents its literal highest-jet separant. -/
theorem chain_successor {d : ℕ} {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {stages : List (Stage F)} (h : SeparantChainRefinement.OrderedChain ts Q stages)
    (before : List (Stage F)) (stage : Stage F) (after : List (Stage F))
    (he : stages = before ++ stage :: after) (R : DifferentialPolynomial F d)
    (hR : MvPolynomial.EvaluationMachine.sparsePolynomial stage.equation =
      MvPolynomial.rename HighestJetTransport.encodeJet R)
    (j : Fin (d + 1)) (hj : highestActiveJet R = some j) :
    ∃ next tail, after = next :: tail ∧
      MvPolynomial.EvaluationMachine.sparsePolynomial next.equation =
        MvPolynomial.rename HighestJetTransport.encodeJet (separant R j) := by
  obtain ⟨R', hsuffix⟩ := chain_suffix h before stage after he
  rcases stage with ⟨stageTerms, selection⟩
  cases hsuffix with
  | terminal layout rep nonzero last =>
      have heq : R' = R := MvPolynomial.rename_injective HighestJetTransport.encodeJet
        HighestJetTransport.encodeJet_injective (rep.symm.trans hR)
      subst R'
      rw [hj] at last
      contradiction
  | @active R' ts tail j' layout rep nonzero highest next =>
      have heq : R' = R := MvPolynomial.rename_injective HighestJetTransport.encodeJet
        HighestJetTransport.encodeJet_injective (rep.symm.trans hR)
      subst R'
      have hjs : j' = j := Option.some.inj (highest.symm.trans hj)
      subst j'
      have hhead : ∃ first rest, after = first :: rest ∧
          first.equation =
            MvPolynomial.PartialDerivativeMachine.derivativeTerms (j.val + 1) stageTerms := by
        cases next with
        | terminal layout rep nonzero last => exact ⟨_, [], rfl, rfl⟩
        | active k layout rep nonzero highest next => exact ⟨_, _, rfl, rfl⟩
      obtain ⟨first, rest, ht, hf⟩ := hhead
      exact ⟨first, rest, ht, by
        rw [hf]
        exact SeparantChainRefinement.derivative_rep stageTerms R layout rep j⟩

/-- Any actual stage output passes the ambient-order zero test for its own current equation. -/
theorem current_zero {d D L : ℕ} (input : StageRootsMachine.Input F)
    (points : Fin L ↪ F) (samples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i)) (hq : 0 < input.alphabet.length)
    (hdepth : d ≤ D) {ts : List (Term F)} {Q : DifferentialPolynomial F d}
    {stages : List (Stage F)} (hchain : SeparantChainRefinement.OrderedChain ts Q stages)
    (hchar : ∀ j, jetDegree Q j < ringChar F) (hweight : differentialWeightedDegree D Q < L)
    {out : List (Record F)} {previous : List (List (Term F))}
    (hspec : StageRootsMachine.Specification input D L samples stages previous out)
    (record : Record F) (hm : record ∈ out) :
    record.coefficients.length = D + 1 ∧
      ResidualZeroMachine.result ⟨record.coefficients, record.context.stage.equation, 0, d⟩
        samples = true := by
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
  exact ⟨hwidth _ hcand, zero_of_identity R record.context.stage.equation A.natural_eq
    record.coefficients _ rfl hz samples⟩

/-- A later record solves the first equation or stores it among earlier equations. -/
theorem first_or_previous {D L : ℕ} {input : StageRootsMachine.Input F} {samples : List F}
    {first : Stage F} {stages : List (Stage F)} {pre : List (List (Term F))}
    {out : List (Record F)}
    (h : StageRootsMachine.Specification input D L samples (first :: stages) pre out)
    (record : Record F) (hm : record ∈ out) :
    record.context.stage.equation = first.equation ∨ first.equation ∈ record.context.previous := by
  obtain ⟨before, next, tail, _, _, _, _, he, hp, _⟩ := h.member record hm
  cases before with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at he
      exact Or.inl (congrArg (fun stage ↦ stage.equation) he.1.symm)
  | cons head before =>
      simp only [List.cons_append, List.cons.injEq] at he
      right
      rw [hp]
      apply List.mem_append_left
      rw [List.mem_reverse]
      exact List.mem_map.mpr ⟨head, by simp, congrArg (fun stage ↦ stage.equation) he.1.symm⟩

/-- Adjacent-stage exclusion uses the current root's zero test; further stages use their prefix. -/
theorem excludes_later {d D L : ℕ} {input : StageRootsMachine.Input F} {samples : List F}
    {first : Stage F} {stages : List (Stage F)} {pre : List (List (Term F))}
    {out : List (Record F)}
    (h : StageRootsMachine.Specification input D L samples (first :: stages) pre out)
    (earlier later : Record F) (hm : later ∈ out)
    (hsep : earlier.context.separant = first.equation)
    (hcs : earlier.coefficients = later.coefficients)
    (ha : accepted d samples earlier = true) (hb : accepted d samples later = true)
    (hz : ResidualZeroMachine.result
      ⟨later.coefficients, later.context.stage.equation, 0, d⟩ samples = true) : False := by
  have hf := CanonicalGuardMachine.separant_zero_test_false (guardInput d samples earlier)
    earlier.context.previous ha
  change ResidualZeroMachine.result
    ⟨earlier.coefficients, earlier.context.separant, 0, d⟩ samples = false at hf
  rw [hsep, hcs] at hf
  rcases first_or_previous h later hm with hcurrent | hprevious
  · rw [hcurrent, hf] at hz
    contradiction
  · have ht := ((CanonicalGuardMachine.result_eq_true_iff _ _).mp hb).1
      first.equation hprevious
    change ResidualZeroMachine.result
      ⟨later.coefficients, first.equation, 0, d⟩ samples = true at ht
    rw [hf] at ht
    contradiction

end ReedSolomon.HiddenDerivative.CanonicalRootSelection
